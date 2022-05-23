Require Import Qreals.
Require Import Lra Lia Reals RealAdd RandomVariableL2 Coquelicot.Coquelicot.
Require Import Morphisms Finite List ListAdd Permutation infprod Almost NumberIso.
Require Import Sums SimpleExpectation PushNeg.
Require Import EquivDec.
Require Import Classical.
Require Import ClassicalChoice.
Require Import IndefiniteDescription ClassicalDescription.
Require QArith.
Require Import BorelSigmaAlgebra.
Require Import utils.Utils.
Require Import ConditionalExpectation.
Require Import Independence.
Require Import sumtest.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Import ListNotations.

Section slln.

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
Lemma ash_6_1_3 {b x : nat -> R} (hb0: b (0%nat) = 0) (hb1 : forall n, 0 < b (S n) <= b (S (S n))) (hb2 : is_lim_seq b p_infty)
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
   }
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
        induction n.
        -- simpl.
           specialize (hb1 0%nat).
           lra.
        -- rewrite sum_f_R0_peel.
           eapply Rlt_le_trans.
           ++ apply IHn.
           ++ assert (b (S (S n)) - b (S n) >= 0).
              ** specialize (hb1 n); lra.
              ** lra.
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

Lemma sum_n_zeroval (f : nat -> R)  (n:nat) :
  f 0%nat = 0 ->
  sum_n_m f 0%nat n = sum_n_m f 1%nat n.
Proof.
  intros.
  induction n.
  - rewrite sum_n_n.
    rewrite H.
    rewrite sum_n_m_zero; try lia.
    reflexivity.
  - rewrite sum_n_Sm; try lia.
    rewrite sum_n_Sm; try lia.
    unfold plus; simpl.
    now rewrite IHn.
Qed.

Lemma ash_6_1_3_strong1 {b x : nat -> R} (hb1 : forall n, 0 < b n <= b (S n)) (hb2 : is_lim_seq b p_infty)
      (hx : ex_series x):
  is_lim_seq (fun n => (sum_n_m (fun j => b j * x j) 1 n)/(b n)) 0.
Proof.
  pose (bb  := fun n => if (lt_dec 0 n) then (b n) else 0).
  generalize (@ash_6_1_3 bb x); intros.
  cut_to H; trivial.
  - apply is_lim_seq_ext with (v := fun n => sum_n_m (fun j => b j * x j) 1 (S n) / (b (S n))) in H.
    + apply is_lim_seq_incr_1.
      apply H.
    + intros.
      rewrite <- sum_n_Reals.
      unfold sum_n.
      replace (bb (S n)) with (b (S n)).
      * f_equal.
        rewrite sum_n_zeroval.
        -- rewrite sum_n_m_ext_loc with (b0 :=  (fun j : nat => b j * x j)); [easy | ].
           intros.
           unfold bb.
           match_destr.
           lia.
        -- unfold bb.
           simpl.
           lra.
      * unfold bb.
        match_destr.
        lia.
  - unfold bb.
    now simpl.
  - unfold bb.
    apply is_lim_seq_incr_1.
    apply is_lim_seq_ext with (u := (fun n => b (S n))).
    + intros.
      match_destr.
      lia.
    + now apply is_lim_seq_incr_1 in hb2.
Qed.

Lemma ash_6_1_3_strong {b x : nat -> R} (hb1 : forall n, 0 < b n <= b (S n)) (hb2 : is_lim_seq b p_infty)
      (hx : ex_series x):
  is_lim_seq (fun n => (sum_n (fun j => b j * x j) n)/(b n)) 0.
Proof.
  apply is_lim_seq_incr_1.
  apply is_lim_seq_ext with (u := fun n => ((b 0%nat)*(x 0%nat) + sum_n_m (fun j : nat => b j * x j) 1 (S n))/(b (S n))).
  - intros.
    f_equal.
  - apply is_lim_seq_ext with (u := fun n => (b 0%nat)*(x 0%nat)/(b (S n)) + (sum_n_m (fun j : nat => b j * x j) 1 (S n))/(b (S n))).
    + intros.
      field.
      apply Rgt_not_eq.
      apply (hb1 (S n)).
    + apply is_lim_seq_plus with (l1 := 0) (l2 := 0).
      * unfold Rdiv.
        replace (Rbar.Finite 0) with (Rbar_mult (Rmult (b 0%nat) (x 0%nat)) 0).
        -- apply is_lim_seq_scal_l.
           replace (Rbar.Finite 0) with (Rbar_inv p_infty).
           ++ apply is_lim_seq_inv.
              ** now apply is_lim_seq_incr_1 in hb2.
              ** discriminate.
           ++ now simpl.
        -- now rewrite Rbar_mult_0_r.
      * generalize (ash_6_1_3_strong1 hb1 hb2 hx); intros.
        now apply is_lim_seq_incr_1 in H.
      * red; simpl.
        f_equal.
        now rewrite Rplus_0_r.
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
Defined.

Global Instance frfite (X Y : Ts -> R){p : Prop}(dec : {p} + {~ p})
       {rv_X : FiniteRangeFunction X} {rv_Y : FiniteRangeFunction Y} :
  FiniteRangeFunction (if dec then X else Y).
Proof.
  match_destr.
Qed.

Definition rvmaxlist (X : nat -> Ts -> R) (N : nat) : Ts -> R :=
  fun (omega : Ts) => Rmax_list_map (List.seq 0 (S N)) (fun n => X n omega).

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
  unfold Rmax_list_map.
  rewrite Rmax_list_app.
  + apply Rmax_l.
  + apply seq_not_nil; lia.
Qed.

Global Instance frfrvmaxlist (X : nat -> Ts -> R)
       {rv : forall n, FiniteRangeFunction (X n)} (N : nat):
  FiniteRangeFunction (rvmaxlist X N).
Proof.
  unfold rvmaxlist, Rmax_list_map.
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

Fixpoint filtration_history (n : nat) (X : nat -> Ts -> R)
         {frf : forall n, FiniteRangeFunction (X n)}
         {rv : forall n, RandomVariable dom borel_sa (X n)}
  : list dec_sa_event :=
  match n with
  | 0%nat => [dsa_Ω]
  | S k => refine_dec_sa_partitions (induced_sigma_generators (frf k)) (filtration_history k X)
  end.

Lemma rvmult_zero (f : Ts -> R) :
  rv_eq (rvmult f (const 0)) (const 0).
Proof.
  intro x.
  unfold rvmult, const.
  lra.
Qed.

Lemma part_list_history (n : nat) (X : nat -> Ts -> R)
         {frf : forall n, FiniteRangeFunction (X n)}
         {rv : forall n, RandomVariable dom borel_sa (X n)} :
  is_partition_list (map dsa_event (filtration_history n X)).
Proof.
  induction n.
  - simpl.
    unfold is_partition_list.
    split.
    + apply FOP_cons.
      * apply Forall_nil.
      * apply FOP_nil.
    + apply list_union_singleton.
  - simpl.
    apply is_partition_refine.
    + apply induced_gen_ispart.
    + apply IHn.
 Qed.

Lemma part_meas_induced (f : Ts -> R) 
      {frf : FiniteRangeFunction f}
      {rv : RandomVariable dom borel_sa f} :
  partition_measurable f (map dsa_event (induced_sigma_generators frf)).
Proof.
  unfold partition_measurable, induced_sigma_generators.
  intros.
  rewrite in_map_iff in H0.  
  destruct H0 as [? [? ?]].
  rewrite in_map_iff in H1.
  destruct H1 as [? [? ?]].
  rewrite <- H1 in H0; simpl in H0.
  destruct frf.
  exists x0.
  rewrite H0.
  easy.
Qed.

Global Instance partition_measurable_perm (f : Ts -> R)
   {frf : FiniteRangeFunction f}
   {rvf : RandomVariable dom borel_sa f} :
  Proper (@Permutation _ ==> iff) (partition_measurable f).
Proof.
  cut (Proper (Permutation (A:=event dom) ==> impl) (partition_measurable f)).
  {
    unfold Proper, respectful, impl; intros HH x y perm.
    split; intros.
    - eauto.
    - symmetry in perm.
      eauto.
  }
  unfold partition_measurable.
  unfold Proper, respectful, impl; intros x y perm HH isp e ein.
  rewrite <- perm in isp.
  rewrite <- perm in ein.
  now apply HH.
Qed.

Instance partition_measurable_event_equiv (f : Ts -> R)
   {frf : FiniteRangeFunction f}
   {rvf : RandomVariable dom borel_sa f} :
  Proper (Forall2 event_equiv ==> iff) (partition_measurable f).
Proof.
  cut (Proper (Forall2 event_equiv ==> impl) (partition_measurable f)).
  {
    unfold Proper, respectful, impl; intros HH x y perm.
    split; intros.
    - eauto.
    - symmetry in perm.
      eauto.
  }
  unfold partition_measurable, impl.
  intros x y F2 HH isp p inp.
  rewrite <- F2 in isp.
  destruct (Forall2_In_r F2 inp) as [p' [??]].
  destruct (HH isp p') as [c csub]; trivial.
  exists c.
  now rewrite <- H0.
Qed.  

Lemma part_meas_refine_commute
      (f : Ts -> R) 
      (l1 l2 : list dec_sa_event)
      {frf : FiniteRangeFunction f}
      {rvf : RandomVariable dom borel_sa f} :
  partition_measurable f (map dsa_event
                              (refine_dec_sa_partitions l1 l2)) <->
  partition_measurable f (map dsa_event
                              (refine_dec_sa_partitions l2 l1)).
Proof.
  destruct (refine_dec_sa_partitions_symm l1 l2) as [l' [perm F2]].
  transitivity (partition_measurable f (map dsa_event l')).
  - apply partition_measurable_perm.
    now apply Permutation_map.
  - apply partition_measurable_event_equiv.
    apply Forall2_map_f.
    apply F2.
Qed.

Lemma part_meas_refine_l (f : Ts -> R) 
      (l1 l2 : list dec_sa_event)
      {frf : FiniteRangeFunction f}
      {rvf : RandomVariable dom borel_sa f} :
  (is_partition_list (map dsa_event l1)) ->
  (is_partition_list (map dsa_event l2)) ->  
  (partition_measurable f (map dsa_event l1)) ->
  partition_measurable f (map dsa_event
                              (refine_dec_sa_partitions l1 l2)).
Proof.
  intros ispartl1 ispartl2; intros.
  unfold partition_measurable, refine_dec_sa_partitions.
  intros.
  rewrite in_map_iff in H1.
  destruct H1 as [? [? ?]].
  rewrite flat_map_concat_map in H2.
  rewrite concat_In in H2.
  destruct H2 as [? [? ?]].
  rewrite in_map_iff in H2.
  destruct H2 as [? [? ?]].
  unfold partition_measurable in H.    
  destruct frf.
  rewrite <- H2 in H3.
  cut_to H; trivial.
  specialize (H (dsa_event x1)).
  cut_to H.
  - destruct H as [? ?].
    exists x2.
    unfold refine_dec_sa_event in H3.
    rewrite in_map_iff in H3.
    destruct H3 as [? [? ?]].
    rewrite <- H1.
    transitivity (dsa_event x1); trivial.
    rewrite <- H3.
    simpl.
    apply Event.event_inter_sub_l.
  - now apply in_map.
Qed.

Lemma part_meas_refine (f : Ts -> R) 
      (l1 l2 : list dec_sa_event)
      {frf : FiniteRangeFunction f}
      {rvf : RandomVariable dom borel_sa f} :
  (is_partition_list (map dsa_event l1)) ->
  (is_partition_list (map dsa_event l2)) ->  
  (partition_measurable f (map dsa_event l1)) \/ 
  (partition_measurable f (map dsa_event l2)) ->  
  partition_measurable f (map dsa_event
                              (refine_dec_sa_partitions l1 l2)).
Proof.
  intros.
  destruct H1.
  - now apply part_meas_refine_l.
  - rewrite part_meas_refine_commute.
    now apply part_meas_refine_l.
Qed.

Lemma part_meas_hist  (j k : nat) (X : nat -> Ts -> R)
         {frf : forall n, FiniteRangeFunction (X n)}
         {rv : forall n, RandomVariable dom borel_sa (X n)} :
  partition_measurable (X j) (map dsa_event (filtration_history ((S j) + k)%nat X)).
Proof.
  induction k.
  - replace (S j + 0)%nat with (S j) by lia.
    simpl.
    apply part_meas_refine.
    + apply induced_gen_ispart.
    + apply part_list_history.
    + left.
      apply part_meas_induced.
  - replace (S j + S k)%nat with (S (S j + k))%nat by lia.
    simpl.
    apply part_meas_refine.
    + apply induced_gen_ispart.
    + apply is_partition_refine.
      * apply induced_gen_ispart.
      * apply part_list_history.
    + right.
      apply IHk.
 Qed.

Instance filtration_sa_le_rv {Td:Type} {cod : SigmaAlgebra Td}
         {F : nat -> SigmaAlgebra Ts} (X : nat -> Ts -> Td)
           (isfilt: IsFiltration F)
           {rv : forall (n:nat), RandomVariable (F n) cod (X n)}
        (n : nat) (j:nat) (jlt: (j <= n)%nat) :
    RandomVariable (F n) cod (X j).
  Proof.
    eapply (RandomVariable_proper_le (F j))
    ; try reflexivity; trivial.
    unfold filtration_history_sa.
    apply is_filtration_le; trivial.
  Qed.

Existing Instance isfe_l2_prod.
Existing Instance isfe_sqr_seq.

Lemma expec_cross_zero_filter (X : nat -> Ts -> R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {frf2 : forall (k:nat), IsFiniteExpectation Prts (rvsqr (X k))} 
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
  forall (j k : nat), 
    (j < k)%nat ->
    FiniteExpectation Prts (rvmult (X j) (X k)) = 0.
Proof.
  intros j k jltk.
  destruct k; try lia.
  eapply FiniteCondexp_factor_out_zero_swapped with (sub := filt_sub k).
  - apply filtration_sa_le_rv; trivial.
    lia.
  - specialize (HC k).
    erewrite (FiniteCondexp_eq _ ) in HC.
    apply (almost_f_equal _ real) in HC.
    apply HC.
    Unshelve.
    now apply IsFiniteExpectation_rvsqr_lower.
 Qed.

Lemma SimpleExpectation_rvsum {n}  
      (X : nat -> Ts -> R)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {frf : forall (n:nat), FiniteRangeFunction (X n)} :
  SimpleExpectation (rvsum X n) =
  sum_n (fun m => SimpleExpectation (X m)) n.
Proof.
  induction n.
  - rewrite sum_O.
    assert (rv_eq (rvsum X 0%nat) (X 0%nat)).
    {
      unfold rvsum.
      intro x.
      now rewrite sum_O.
    }
    now erewrite SimpleExpectation_ext; [|apply H].
  - replace (SimpleExpectation (rvsum X (S n))) with
        (SimpleExpectation (rvplus (rvsum X n) (X (S n)))).
    + rewrite <- sumSimpleExpectation.
      rewrite IHn.
      rewrite sum_Sn.
      now unfold plus; simpl.
    + apply SimpleExpectation_ext.
      intro x.
      unfold rvplus, rvsum.
      now rewrite sum_Sn.
Qed.

Lemma expec_cross_zero_sum_shift_filter (X : nat -> Ts -> R) (m:nat)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt: IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {frf2 : forall (k:nat), IsFiniteExpectation Prts (rvsqr (X k))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
  forall (j k : nat), 
    (j < k)%nat ->
    FiniteExpectation Prts (rvsum (fun n => rvmult (X (n+m)%nat) (X (k+m)%nat)) j) = 0.
Proof.
  intros.
  rewrite <- sum_expectation.
  rewrite sum_n_ext_loc with (b := fun _ => 0).
  - rewrite sum_n_const.
    lra.
  - intros.
    apply expec_cross_zero_filter with (filt_sub := filt_sub) (rv := rv); trivial.
    lia.
 Qed.

Lemma rvsum_distr_r {n} (X : nat -> Ts -> R) (f : Ts -> R) :
  rv_eq (rvsum (fun j => rvmult (X j) f) n) (rvmult (rvsum X n) f).
Proof.
  intro x; unfold rvsum, rvmult.
  induction n.
  - rewrite sum_O.
    now rewrite sum_O.
  - rewrite sum_Sn.
    rewrite sum_Sn.
    unfold plus; simpl.
    rewrite IHn.
    lra.
 Qed.

Lemma expec_cross_zero_sum2_shift_filter (X : nat -> Ts -> R) (m : nat)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt: IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {isfe2 : forall (k:nat), IsFiniteExpectation Prts (rvsqr (X k))}
      {isfe_mult_sum: forall (k j:nat),
                             IsFiniteExpectation Prts (rvmult (rvsum (fun n : nat => X (n + m)%nat) j) 
                                                              (X (k + m)%nat))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
  forall (j k : nat), 
    (j < k)%nat ->
    FiniteExpectation Prts (rvmult (rvsum (fun n => X (n + m)%nat) j) (X (k+m)%nat)) = 0.
Proof.
  intros.
  generalize (expec_cross_zero_sum_shift_filter X m _ filt_sub HC j k H); intros.
  rewrite <- H0.
  apply FiniteExpectation_ext.
  symmetry.
  rewrite <- rvsum_distr_r.
  intros ?.
  unfold rvsum.
  apply sum_n_ext.
  intros.
  now rewrite rvmult_comm.
Qed.

(* Few properties about cutoff sequences. Move to RealAdd. *)
Fixpoint cutoff_eps (n : nat) (eps : R) (X : nat -> R) :=
  match n with
  | 0%nat => X 0%nat
  | S k => if (Rlt_dec (Rmax_list_map (seq 0 (S k)) (fun n => Rabs(X n))) eps) then X (S k)
                    else (cutoff_eps k eps X)
  end.

Lemma cutoff_eps_lt_eps eps n (X : nat -> R) :
   (forall k, (k <= n)%nat -> Rabs (X k) < eps) -> (cutoff_eps n eps X = X n).
Proof.
  intros H.
  induction n.
  + now simpl.
  + simpl.
    match_destr.
    assert (H1 : Rmax_list_map (seq 0 (S n)) (fun n => Rabs(X n)) < eps).
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
   (forall k:nat, eps <= Rabs(X k)) -> (forall n, cutoff_eps n eps X = X 0%nat).
Proof.
  intros H n.
  simpl.
  induction n.
  ++ now simpl in H.
  ++ simpl. match_destr.
     assert (Rabs(X n) <= Rmax_list_map (0%nat :: seq 1 n) (fun n => Rabs(X n))).
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


Lemma cutoff_ge_eps_exists  (n : nat) (eps : R) ( X : nat -> R ):
  (eps <= Rabs(cutoff_eps n eps X)) -> exists k, (k <= n)%nat /\ eps <= Rabs(X k).
Proof.
  intros Hn.
  induction n.
  -- simpl in Hn. exists 0%nat.
     split; trivial.
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
   (Rabs(cutoff_eps n eps X) < eps) -> (forall k, (k <= n)%nat -> Rabs(X k) < eps).
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
       rewrite (Rmax_list_map_seq_ge eps (fun n => Rabs (X n)) H0) in n0.
       destruct n0 as [k1 [Hk1 Heps1]].
       assert (k1 <= n)%nat by lia.
       specialize (IHn k1 H1).
       exfalso; lra.
Qed.

Lemma cutoff_ge_eps_exists_iff (n : nat) (eps : R) (X : nat -> R):
  (eps <= Rabs(cutoff_eps n eps X)) <-> exists k, (k <= n)%nat /\ eps <= Rabs(X k).
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
  (eps <= Rabs(cutoff_eps n eps X)) <-> eps <= Rmax_list_map (seq 0 (S n)) (fun n => Rabs (X n)).
Proof.
  assert (Hn : (0 < S n)%nat) by lia.
  rewrite (Rmax_list_map_seq_ge eps (fun n => Rabs (X n)) Hn).
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
   (forall k, Rabs(X k omega) < eps) -> (forall n, cutoff_eps_rv n eps X omega = X n omega).
Proof.
  intros omega H n.
  unfold cutoff_eps_rv.
  now apply cutoff_eps_lt_eps.
Qed.

Lemma cutoff_eps_rv_ge_eps eps (X : nat -> Ts -> R) : forall omega,
   (forall k:nat, eps <= Rabs(X k omega)) -> (forall n, cutoff_eps_rv n eps X omega = X 0%nat omega).
Proof.
  intros omega H n.
  unfold cutoff_eps_rv.
  now apply cutoff_eps_ge_eps.
Qed.

Lemma cutoff_ge_eps_rv_rvmaxlist_iff (n : nat) (eps : R) (X : nat -> Ts -> R): forall omega,
    eps <= Rabs(cutoff_eps_rv n eps X omega) <->
    eps <= rvmaxlist (fun k => fun omega => Rabs (X k omega)) n omega.
Proof.
  intros omega.
  unfold rvmaxlist, cutoff_eps_rv.
  now rewrite cutoff_ge_eps_Rmax_list_iff.
Qed.

Lemma Rle_Rmax : forall r1 r2 r : R, Rmax r1 r2 <= r <-> r1 <= r /\ r2 <= r.
Proof.
  split; intros.
  + split.
    -- eapply Rle_trans; try (apply H); apply Rmax_l.
    -- eapply Rle_trans; try (apply H); apply Rmax_r.
  + destruct H; apply Rmax_lub; trivial.
Qed.

Instance max_list_measurable (k : nat) (X : nat -> Ts -> R)
  {rm: forall n, (n <= k)%nat -> RealMeasurable dom (X n)} :
    RealMeasurable dom (fun omega => Rmax_list_map (seq 0 (S k)) (fun n => X n omega)).
Proof.
  unfold Rmax_list_map.
  induction k.
  - simpl.
    apply rm; lia.
  - unfold RealMeasurable in *; intros.
    assert (pre_event_equiv
               (fun omega : Ts =>
                  Rmax_list (map (fun n : nat => X n omega) (seq 0 (S (S k)))) <= r)
               (pre_event_inter
                  (fun omega : Ts =>
                     Rmax_list (map (fun n : nat => X n omega) (seq 0 (S k))) <= r)
                  (fun omega => X (S k) omega <= r))).
    {
      intro x; unfold pre_event_inter.
      replace (seq 0 (S(S k))) with (seq 0 (S k) ++ [S k]) by
          (do 3 rewrite seq_S; f_equal; lra).
      rewrite Rmax_list_app; try (apply seq_not_nil; lia).
      apply Rle_Rmax.
    }
    rewrite H.
    apply sa_inter.
    + apply IHk.
      intros.
      apply rm.
      lia.
    + apply rm.
      lia.
 Qed.

(*
Global Instance rvmaxlist_rv (X : nat -> Ts -> R) (N : nat)
       {rv : forall n, RandomVariable dom borel_sa (X n)} :
  RandomVariable dom borel_sa (rvmaxlist X N).
Proof.
  intros.
  apply measurable_rv.
  apply max_list_measurable; intros.
  apply rv_measurable.
  apply rv.
Qed.
*)
Global Instance rvmaxlist_rv  (X : nat -> Ts -> R) (N : nat)
       {rv : forall n, (n <= N)%nat -> RandomVariable dom borel_sa (X n)} :
  RandomVariable dom borel_sa (rvmaxlist X N).
Proof.
  intros.
  apply measurable_rv.
  apply max_list_measurable; intros.
  apply rv_measurable.
  apply rv; lia.
Qed.

Global Instance rv_cutoff_eps_rv (n : nat) (eps : R) (X : nat -> Ts -> R) 
         {rv: forall k, (k <= n)%nat -> RandomVariable dom borel_sa (X k)} :
  RandomVariable dom borel_sa (cutoff_eps_rv n eps X).
Proof.
  unfold cutoff_eps_rv.
  apply measurable_rv.
  assert (mrv : forall k, (k <= n)%nat -> RealMeasurable dom (X k)).
  {
    intros.
    apply rv_measurable.
    apply rv; lia.
  }
  unfold RealMeasurable in *.
  intros.
  induction n.
  - simpl; apply mrv; lia.
  - simpl.
    assert (pre_event_equiv
               (fun omega : Ts =>
                  (if Rlt_dec (Rmax_list_map (0%nat :: seq 1 n) 
                                             (fun k : nat => Rabs (X k omega))) eps
                   then X (S n) omega
                   else cutoff_eps n eps (fun k : nat => X k omega)) <= r)
               (pre_event_union
                  (pre_event_inter
                     (fun omega => Rmax_list_map (0%nat :: seq 1 n) (fun k : nat => Rabs (X k omega)) < eps)
                     (fun omega => X (S n) omega <= r))
                  (pre_event_inter
                     (pre_event_complement
                        (fun omega => Rmax_list_map (0%nat :: seq 1 n) (fun k : nat => Rabs (X k omega)) < eps))
                     (fun omega => cutoff_eps n eps (fun k : nat => X k omega) <= r)))).
    {
      intro x; unfold pre_event_union, pre_event_inter, pre_event_complement.
      match_destr; lra.
    }
    rewrite H.
    apply sa_union.
    + apply sa_inter.
      * apply sa_le_lt.
        apply max_list_measurable.
        intros.
        apply Rabs_measurable.
        unfold RealMeasurable.
        apply mrv; lia.
      * apply mrv; lia.
    + apply sa_inter.
      * apply sa_complement.
        apply sa_le_lt.
        apply max_list_measurable.        
        intros.
        apply Rabs_measurable.        
        unfold RealMeasurable.
        apply mrv; lia.
      * apply IHn.
        -- intros.
           apply rv; lia.
        -- intros.
           apply mrv; lia.
  Qed. 

Global Instance nnf_cutoff_eps_rv (n : nat) (eps : R) (X : nat -> Ts -> R) 
         {nnf: forall n, NonnegativeFunction (X n)} :
  NonnegativeFunction (cutoff_eps_rv n eps X).
Proof.
  unfold cutoff_eps_rv.
  induction n.
  - now simpl.
  - simpl.
    intro x.
    specialize (IHn x).
    simpl in IHn.
    match_destr.
    apply nnf.
Qed.

Lemma cutoff_eps_values (n : nat) (eps : R) (X : nat -> Ts -> R) :
  forall (x:Ts),
  exists (k : nat), 
    (k <= n)%nat /\
    cutoff_eps_rv n eps X x = X k x.
Proof.
  intros.
  unfold cutoff_eps_rv.
  induction n.
  - exists (0%nat); simpl.
    now split; try lia.
  - simpl.
    match_destr.
    + exists (S n).
      now split; try lia.
    + destruct IHn as [k [? ?]].
      exists k.
      now split; try lia.
Qed.

Local Obligation Tactic := idtac.

Global Program Instance frf_cutoff_eps_rv (n : nat) (eps : R) (X : nat -> Ts -> R) 
         {frf: forall n, FiniteRangeFunction (X n)} :
  FiniteRangeFunction (cutoff_eps_rv n eps X) := {
  frf_vals := flat_map (fun k => frf_vals (FiniteRangeFunction := frf k)) (seq 0 (S n))
  }.
Next Obligation.
  intros.
  apply in_flat_map.
  destruct (cutoff_eps_values n eps X x) as [k [kle ck]].
  exists k.
  split.
  - apply in_seq; lia.
  - rewrite ck.
    apply frf.
Qed.

Local Obligation Tactic := unfold complement, equiv; Tactics.program_simpl.

Lemma cutoff_eps_succ_minus eps (X : nat -> R) :
  forall n, cutoff_eps (S n) eps X - cutoff_eps n eps X =
       if (Rlt_dec (Rmax_list_map (seq 0 (S n)) (fun n => Rabs (X n))) eps) then
         (X (S n) - X n) else 0.
Proof.
  intros n.
  simpl.
  match_destr; intuition; try lra.
  f_equal.
  replace (0%nat :: seq 1 n) with (seq 0 (S n)) in r by (now simpl).
  induction n; try (now simpl).
  assert (0 < S n)%nat by lia.
  generalize (Rmax_list_map_succ eps (fun n => Rabs (X n)) (S n) H r); intros.
  specialize (IHn H0).
  simpl. match_destr; intuition; try lra.
Qed.

Definition pre_cutoff_event (n : nat) (eps : R) (X : nat -> Ts -> R) : pre_event Ts :=
  fun x => Rmax_list_map (seq 0 n) (fun n => Rabs (X n x)) < eps.

Program Definition cutoff_indicator (n : nat) (eps : R) (X : nat -> Ts -> R) :=
  EventIndicator (P := pre_cutoff_event n eps X) _.
Next Obligation.
  apply ClassicalDescription.excluded_middle_informative.
Defined.

Global Instance cutoff_ind_rv (j:nat) (eps:R) (X: nat -> Ts -> R) 
      {rv : forall n, (n<=j)%nat -> RandomVariable dom borel_sa (X n)} :
  RandomVariable dom borel_sa
                 (cutoff_indicator (S j) eps (rvsum X)).
Proof.
  unfold cutoff_indicator.
  apply EventIndicator_pre_rv.
  unfold pre_cutoff_event.
  apply sa_le_lt.
  intros.
  apply max_list_measurable.        
  intros.
  apply Rabs_measurable.
  apply rvsum_measurable_loc.
  intros.
  apply rv_measurable.
  apply rv; lia.
Qed.

  Lemma partition_measurable_rvplus (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2}         
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable  rv_X1 l ->
    partition_measurable  rv_X2 l ->     
    partition_measurable  (rvplus rv_X1 rv_X2) l.
  Proof.
     unfold partition_measurable. intros.
     specialize (H0 H p H3).
     specialize (H1 H p H3).
     destruct H0 as [c1 ?].
     destruct H1 as [c2 ?].     
     exists (Rplus c1 c2).
     intros ?.
     simpl.
     unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
     unfold rvplus; simpl; intros.
     now rewrite (H0 x), (H1 x).
  Qed.

  Lemma partition_measurable_rvsum (j : nat) (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)}
        (l : list (event dom)) :
    is_partition_list l ->
    (forall k, (k <= j)%nat -> partition_measurable (X k) l) ->
    partition_measurable (rvsum X j) l.
  Proof.
     unfold partition_measurable; intros.
     induction j.
     - specialize (H0 0%nat).
       cut_to H0; try lia; trivial.
       destruct (H0 p H2) as [c ?].
       exists c.
       unfold rvsum.
       rewrite H3.
       intros ?; simpl.
       unfold pre_event_preimage; simpl.
       now rewrite sum_O.
     - unfold rvsum.
       generalize H0; intros HH0.
       specialize (H0 (S j)).
       cut_to H0; try lia; trivial.
       cut_to IHj.
       + specialize (H0 p H2).
         destruct IHj as [c0 ?].
         destruct H0 as [c1 ?].
         exists (c1 + c0).
         intros x; simpl.
         repeat red in H0, H3.
         unfold pre_event_preimage, pre_event_singleton in *; simpl in *; intros px.
         rewrite sum_Sn.
         unfold plus; simpl.
         rewrite (Rplus_comm c1 c0).
         unfold rvsum in *.
         f_equal; auto.
       + intros.
         apply HH0; trivial.
         lia.
  Qed.

  Lemma partition_measurable_rvmult (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2}         
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable  rv_X1 l ->
    partition_measurable  rv_X2 l ->     
    partition_measurable  (rvmult rv_X1 rv_X2) l.
  Proof.
     unfold partition_measurable. intros.
     specialize (H0 H p H3).
     specialize (H1 H p H3).
     destruct H0 as [c1 ?].
     destruct H1 as [c2 ?].     
     exists (Rmult c1 c2).
     intros ?.
     simpl.
     unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
     unfold rvmult; simpl; intros.
     now rewrite (H0 x), (H1 x).
  Qed.

  Lemma partition_measurable_indicator 
        {P : event dom} 
        (dec:forall x, {P x} + {~ P x}) 
        (l : list (event dom)) :
    (forall (Q : event dom), 
        In Q l ->
        (event_sub Q P) \/ (event_sub Q (event_complement P))) ->
    partition_measurable (EventIndicator dec) l.
  Proof.
    intros.
    unfold partition_measurable; intros.
    unfold frf_vals, EventIndicator_frf, IndicatorRandomVariableSimpl.
    unfold preimage_singleton, EventIndicator, event_sub.
    unfold pre_event_sub, pre_event_preimage, pre_event_singleton.
    destruct (H p H1).
    - exists 1.
      simpl; intros.
      match_destr.
      now specialize (H2 x H3).
   - exists 0.
     simpl; intros.
     match_destr.
     now specialize (H2 x H3).
  Qed.    

  Lemma partition_measurable_indicator_pre
        {P : pre_event Ts} 
        (dec:forall x, {P x} + {~ P x}) 
        {rv : RandomVariable dom borel_sa (EventIndicator dec)}
        (l : list (event dom)) :
    (forall (Q : event dom), 
        In Q l ->
        (pre_event_sub Q P) \/ (pre_event_sub Q (pre_event_complement P))) ->
    partition_measurable (EventIndicator dec) l.
  Proof.
    intros.
    unfold partition_measurable; intros.
    unfold frf_vals, EventIndicator_frf, IndicatorRandomVariableSimpl.
    unfold preimage_singleton, EventIndicator, event_sub.
    unfold pre_event_sub, pre_event_preimage, pre_event_singleton.
    destruct (H p H1).
    - exists 1.
      simpl; intros.
      match_destr.
      now specialize (H2 x H3).
   - exists 0.
     simpl; intros.
     match_destr.
     now specialize (H2 x H3).
  Qed.

  Lemma filtration_history_var_const (X : nat -> Ts -> R) (eps : R) (j:nat) 
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
  forall (Q : event dom),
      In Q (map dsa_event (filtration_history (S j) X)) ->
      forall (k:nat), 
        (k <= j)%nat ->
        exists (c:R),
        forall x, Q x -> X k x = c.
  Proof.
    intros.
    generalize (part_meas_hist k (j - k)%nat X); intros.
    unfold partition_measurable in H1.
    generalize (part_list_history (S j) X); intros.
    replace (S k + (j - k))%nat with (S j) in H1 by lia.
    cut_to H1; trivial.
    specialize (H1 Q).
    cut_to H1; trivial.
  Qed.

Lemma filtration_history_rvsum_var_const_shift (X : nat -> Ts -> R) (eps : R) (m j:nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
  forall (Q : event dom),
      In Q (map dsa_event (filtration_history (S j + m)%nat X)) ->
      forall (k:nat),
        (k <= j)%nat ->
        exists (c:R),
        forall x, Q x -> rvsum (fun n => X(n+m)%nat) k x = c.
  Proof.
    intros.
    generalize (partition_measurable_rvsum k (fun n => X (n+m)%nat)
                                           (map dsa_event (filtration_history (S j + m)%nat X))); intros.
    generalize (part_list_history (S j + m)%nat X); intros.
    cut_to H1; trivial.
    - unfold partition_measurable in H1.
      cut_to H1; trivial.
      specialize (H1 Q).
      cut_to H1; trivial.
  - intros.
    generalize (part_meas_hist (k0+m) (j - k0)%nat X); intros.
    now replace (S (k0 + m) + (j - k0))%nat with (S j + m)%nat in H4 by lia.
 Qed.

  Lemma filtration_history_rvsum_var_const_ex_shift (X : nat -> Ts -> R) (eps : R) (m j:nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
  forall (Q : event dom),
      In Q (map dsa_event (filtration_history (S j + m)%nat X)) ->
      forall (k:nat),
        (k <= j)%nat ->
        {c:R |
            forall x, Q x -> rvsum (fun n => X (n+m)%nat) k x = c}.
     Proof.
       intros.
       generalize (filtration_history_rvsum_var_const_shift X eps m j Q H k H0); intros.
       now apply constructive_indefinite_description in H1.
   Qed.

  Lemma filtration_history_rvsum_var_const_fun_shift (X : nat -> Ts -> R) (eps : R) (m j:nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
  forall (Q : event dom),
    In Q (map dsa_event (filtration_history (S j + m)%nat X)) ->
    exists (f :  {n':nat | n' <= j}%nat -> R),
      forall (k:  {n':nat | n' <= j}%nat),
        forall x, Q x -> rvsum (fun n => X(n+m)%nat) (proj1_sig k) x = f k.
  Proof.
    intros.
    generalize (filtration_history_rvsum_var_const_ex_shift X eps m j Q H); intros.
    exists (fun k => (proj1_sig (H0 (proj1_sig k) (proj2_sig k)))).
    intros.
    destruct k; simpl.
    generalize (H0 x0 l); intros.
    destruct s.
    simpl.
    now apply e.
  Qed.

  Lemma pre_cutoff_event_const_history_shift (X : nat -> Ts -> R) (eps : R) (j m:nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom),
      In Q (map dsa_event (filtration_history (S j + m)%nat X)) ->
      exists (c:R),
      forall x, Q x -> Rmax_list_map (seq 0 (S j)) 
                                     (fun n : nat => Rabs (rvsum (fun k => X (k + m)%nat) n x)) = c.
  Proof.
    intros.
    generalize (filtration_history_rvsum_var_const_fun_shift X eps m j Q H); intros.
    destruct H0 as [f ?].
    setoid_rewrite Rmax_list_seq_bounded_nat.
    exists (Rmax_list_map (bounded_nat_finite_list (S j))
                     (fun x0 => Rabs (f (bounded_nat_lt_succ_le j x0)))).
    intros.
    apply Rmax_list_map_ext_in; intros.
    f_equal. specialize (H0 (bounded_nat_lt_succ_le j x0) x H1).
    rewrite <-H0. f_equal.
  Qed.

  Lemma partition_measurable_cutoff_ind_shift (X : nat -> Ts -> R) (eps : R) (m:nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall j, partition_measurable (cutoff_indicator (S j) eps (rvsum (fun n => X (n + m)%nat))) (map dsa_event (filtration_history (S j + m)%nat X)).
  Proof.
    intros.
    apply partition_measurable_indicator_pre; intros.
    - generalize (pre_cutoff_event_const_history_shift X eps j m Q H); intros.
      unfold pre_event_sub, pre_cutoff_event, pre_event_complement.
      destruct H0 as [c ?].
      destruct (Rlt_dec c eps).
      + left.
        intros.
        now rewrite H0.
      + apply Rnot_lt_ge in n.
        right; intros.
        apply Rge_not_lt.
        rewrite H0; trivial.
  Qed.

  Lemma partition_measurable_rvabs (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable  rv_X l ->
    partition_measurable  (rvabs rv_X) l.
  Proof.
     unfold partition_measurable. intros.
     specialize (H0 H p H2).
     destruct H0 as [c1 ?].
     exists (Rabs c1).
     intros ?.
     simpl.
     unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
     unfold rvabs; simpl; intros.
     now rewrite (H0 x).
  Qed.


  Lemma partition_measurable_Rmax_list_map (j : nat) (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)}
        (l : list (event dom)) :
    is_partition_list l ->
    (forall k, (k <= j)%nat -> partition_measurable (X k) l) ->
    partition_measurable (fun x =>
                            (Rmax_list_map (seq 0 (S j))
                                           (fun n : nat => Rabs (X n x)))) l.
  Proof.
    unfold partition_measurable; intros.
   assert (Hr : forall k, (k <= j)%nat -> is_partition_list l -> partition_measurable (rvabs (X k)) l).
    {
      intros. apply partition_measurable_rvabs; eauto.
      unfold partition_measurable; eauto.
    }
    induction j.
    - assert (Hz : (0 <= 0)%nat) by lia.
      specialize (Hr 0%nat Hz). clear Hz.
      cut_to Hr; try lia; trivial.
      destruct (Hr H p H2) as [c ?].
      unfold frf_vals in H3.
      exists c.
      rewrite H3.
      intros ?; simpl.
      unfold pre_event_preimage; simpl.
      unfold Rmax_list_map. simpl.
      unfold rvabs. trivial.
    - generalize (Hr); intros HHr.
      specialize (Hr (S j)).
      cut_to Hr; try lia; trivial.
      cut_to IHj.
      + specialize (Hr H p H2).
        destruct IHj as [c0 ?].
        destruct Hr as [c1 ?].
        exists (Rmax (c0) (c1)).
        intros x; simpl.
        repeat red in H4, H6.
        unfold pre_event_preimage, pre_event_singleton in *; simpl in *; intros px.
        replace (0%nat :: 1%nat :: seq 2%nat j) with (seq 0%nat (S j) ++ [S j]).
        -- unfold Rmax_list_map.
           rewrite Rmax_list_app; try (apply seq_not_nil; lia).
           unfold Rmax_list_map in H3.
           rewrite H3; trivial. f_equal.
           apply H4; trivial.
        -- rewrite <-seq_S.
           now simpl.
      + intros.
        unfold partition_measurable in H0.
        apply H0; trivial.
        lia.
      + intros; apply HHr; trivial; try lia.
  Qed.

  Lemma partition_measurable_Rmax_list_map_rvsum (j : nat) (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)}
        (l : list (event dom)) :
    is_partition_list l ->
    (forall k, (k <= j)%nat -> partition_measurable (X k) l) ->
    partition_measurable (fun x => 
                            (Rmax_list_map (seq 0 (S j)) 
                                           (fun n : nat => Rabs (rvsum X n x)))) l.
  Proof.
    intros.
    assert (forall n, FiniteRangeFunction (rvsum X n)).
    {
      intros.
      typeclasses eauto.
    }
    generalize (partition_measurable_Rmax_list_map j (rvsum X) l H); intros.
    apply H1.
    intros.
    apply (partition_measurable_rvsum k X l H).
    intros.
    apply H0.
    lia.
   Qed.

   Lemma cutoff_eps_const_history_shift (X : nat -> Ts -> R) (eps : R) (j m:nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom), 
      In Q (map dsa_event (filtration_history (S j + m)%nat X)) ->
      exists (c:R),
      forall x, Q x -> (cutoff_eps_rv j eps (rvsum (fun n => X (n + m)%nat))) x = c.
   Proof.
     unfold cutoff_eps_rv.
     induction j; intros.
     - simpl.
       unfold rvsum.
       setoid_rewrite sum_O.
       replace (1 + m)%nat with (S m) in H by lia.
       generalize (filtration_history_var_const X eps m Q H m); intros.
       cut_to H0; try lia.
       destruct H0 as [c ?].
       exists c.
       now apply H0.
     - assert (exists (QQ: event dom), (event_sub Q QQ) /\
                                      (In QQ (map dsa_event (filtration_history (S j + m)%nat X)))).
       {
         replace (S j) with (j+1)%nat in H by lia.
         simpl in H.
         replace (j+1)%nat with (S j) in H by lia.
         unfold refine_dec_sa_partitions in H.
         rewrite in_map_iff in H.
         destruct H as [? [? ?]].
         unfold refine_dec_sa_event in H0.
         rewrite in_flat_map in H0.
         destruct H0 as [? [? ?]].
         rewrite in_map_iff in H1.
         destruct H1 as [? [? ?]].
         exists (dsa_event x1).
         split; [|now apply in_map].
         unfold dec_sa_event_inter in H1.
         assert (event_inter (dsa_event x0) (dsa_event x1) = dsa_event x).
         - rewrite <- H1.
           now simpl.
         - rewrite H in H3.
           rewrite <- H3.
           apply event_inter_sub_r.
       }
       destruct H0 as [QQ [? ?]].
       generalize (filtration_history_rvsum_var_const_fun_shift X eps m (S j)%nat Q H); intros.
       simpl.
       generalize (pre_cutoff_event_const_history_shift X eps j m QQ H1); intros.
       destruct H3 as [c1 ?].
       specialize (IHj QQ H1).
       destruct IHj as [c2 ?].
       destruct H2 as [f ?].
       assert (S j <= S j)%nat by lia.
       exists (if Rlt_dec c1 eps then (f (exist _ _ H5)) else c2).
       intros.
       specialize (H0 x H6).
       specialize (H4 x H0).
       rewrite H4.
       specialize (H3 x H0).
       replace (0%nat :: seq 1 j) with (seq 0%nat (S j)) by now simpl.
       rewrite H3.
       rewrite <- (H2 (exist _ _ H5) x H6).
       now unfold proj1_sig; simpl.
Qed.

   Lemma event_sub_preimage_singleton (f : Ts -> R) c
         (rv : RandomVariable dom borel_sa f):
     forall (p : event dom), event_sub p (preimage_singleton f c) <->
                             (forall x, p x -> f x = c).
   Proof.
     intros; split; intros.
     + repeat red in H.
       apply H. unfold proj1_sig.
       apply H0.
     + repeat red.
       apply H.
   Qed.
   
   Lemma partition_constant_measurable 
         (f : Ts -> R)
         (rv : RandomVariable dom borel_sa f)
         (frf : FiniteRangeFunction f)
         (l : list (event dom)) :
     is_partition_list l ->
     (forall (p : event dom),
       In p l ->
       exists c, forall x, p x -> f x = c) <->
     partition_measurable f l.
   Proof.
     unfold partition_measurable.
     intros.
     split; intros.
     - destruct (H0 p H2) as [c ?].
       exists c.
       now repeat red.
     - now apply H0.
   Qed.

   Lemma partition_measurable_cutoff_eps_shift (X : nat -> Ts -> R) (eps : R) (m:nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall j, partition_measurable (cutoff_eps_rv j eps (rvsum (fun n => X (n+m)%nat)))
                              (map dsa_event (filtration_history ((S j)+m)%nat X)).
  Proof.
    intros.
    apply partition_constant_measurable.
    - apply part_list_history.
    - intros.
      apply (cutoff_eps_const_history_shift X eps j m p H).
  Qed.

End slln.

Section slln_extra.

  Context {Ts:Type} {dom: SigmaAlgebra Ts}{Prts: ProbSpace dom}.

  Lemma cutoff_eps_in j eps X :
    exists k, (k < S j)%nat /\ cutoff_eps j eps X = X k.
  Proof.
    induction j; simpl.
    - exists 0%nat.
      split; trivial; lia.
    - destruct IHj as [k [??]].
      match_destr.
      + exists (S j).
        split; trivial; lia.
      + exists k.
        split; trivial; lia.
  Qed.
  
  Lemma cutoff_eps_in_seq j eps X :
    In (cutoff_eps j eps X) (map X (seq 0 (S j))).
  Proof.
    apply in_map_iff.
    destruct (cutoff_eps_in j eps X) as [k [??]].
    exists k.
    split; [auto |].
    apply in_seq; lia.
  Qed.

  Lemma pre_cutoff_event_lt_eps j eps Xm (a:Ts) :
    (pre_cutoff_event (S j) eps (rvsum Xm) a) ->
    Rabs (cutoff_eps j eps (fun k : nat => rvsum Xm k a)) < eps.
  Proof.
    unfold rvsum.
    unfold pre_cutoff_event, Rmax_list_map.
    intros HH.
    assert (Hnnil:(nil <> map (fun n : nat => Rabs (sum_n (fun n0 : nat => Xm n0 a) n)) (seq 0 (S j))))
      by now simpl.
    destruct (Rmax_list_lt_iff Hnnil eps) as [HH1 _].
    specialize (HH1 HH).
    assert (HHin:forall x,
               In x (map (fun n : nat => (sum_n (fun n0 : nat => Xm n0 a) n)) (seq 0 (S j))) -> Rabs x < eps).
    {
      intros.
      apply HH1.
      rewrite <- map_map.
      now apply in_map.
    }
    apply HHin.
    apply cutoff_eps_in_seq.
  Qed.
  
  Lemma indicator_prod_cross_shift_filter (j m:nat) (eps:R) (X: nat -> Ts -> R) 
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall n, RandomVariable dom borel_sa (X n)}
      {isfe : forall n, IsFiniteExpectation _ (X n)} 
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
    let Xm := fun n => X (n + m)%nat in
  Expectation (Prts:=Prts)
    (rvmult (rvmult (cutoff_eps_rv j eps (rvsum Xm))
                    (cutoff_indicator (S j) eps (rvsum Xm)))
            (X (S (j + m)))) = Some (Rbar.Finite 0).
  Proof.
    intros.
    assert (isfe2:IsFiniteExpectation _
                                      (rvmult (rvmult (cutoff_eps_rv j eps (rvsum Xm))
                    (cutoff_indicator (S j) eps (rvsum Xm)))
            (X (S (j + m))))).
    {
      apply IsFiniteExpectation_abs_id
      ; [typeclasses eauto |].
      generalize (fun n => IsFiniteExpectation_abs _ _ (isfe n)); intros isfe'.
      apply (IsFiniteExpectation_bounded _ (const 0) _ (rvscale (Rabs eps) (rvabs (X (S j + m)%nat)))).
      - intros ?; rv_unfold.
        apply Rabs_pos.
      - intros ?.
        rv_unfold.
        unfold cutoff_indicator, EventIndicator.
        match_destr.
        + rewrite Rmult_1_r.
          rewrite Rabs_mult; simpl.
          apply Rmult_le_compat; trivial
          ; try apply Rabs_pos
          ; try reflexivity.
          rewrite (pre_cutoff_event_lt_eps _ _ _ _ p).
          apply RRle_abs.
        + rewrite Rmult_0_r, Rmult_0_l, Rabs_R0, <- Rabs_mult.
          apply Rabs_pos.
    } 
    rewrite (FiniteExpectation_Expectation _ _).
    do 2 f_equal.
    
    eapply FiniteCondexp_factor_out_zero_swapped with (sub := filt_sub (j + m)%nat); trivial.
    - apply rvmult_rv.
      + unfold Xm.
        apply rv_cutoff_eps_rv; intros.
        apply rvsum_rv_loc; intros.
        apply filtration_sa_le_rv; trivial.
        lia.
      + unfold Xm.
        apply cutoff_ind_rv; auto; intros.
        apply filtration_sa_le_rv; trivial.
        lia.
    - specialize (HC (j+m)%nat).
      rewrite (FiniteCondexp_eq _ _ _) in HC.
      revert HC.
      apply almost_impl; apply all_almost; intros ??.
      now invcs H.
Qed.

  Instance IsFiniteExpectation_mult_sqr X
           {isfemult : forall k j : nat, IsFiniteExpectation Prts (rvmult (X k) (X j))} :
    forall n, IsFiniteExpectation _ ((rvsqr (X n))).
  Proof.
    intros.
    apply isfemult.
  Qed.

  Lemma IsFiniteExpectation_rvmult_rvmaxlist1 F G k
        {rvF:forall n, RandomVariable dom borel_sa (F n)}
        {rvG:RandomVariable dom borel_sa G}
    :
    (forall a, (a <= k)%nat ->
            IsFiniteExpectation Prts (rvmult (F a) G)) ->
    IsFiniteExpectation Prts
                        (rvmult (rvmaxlist F k) G).
  Proof.
    intros.
    unfold rvmaxlist, Rmax_list_map.
    induction k; [simpl; auto |].
    rewrite seq_Sn.
    apply (IsFiniteExpectation_proper
             _
             (rvchoice
                (fun a =>
                   if Rle_dec (Rmax_list (map (fun n : nat => F n a) (seq 0 (S k))))
                              (F (S k) a)
                   then true else false
                )
                (rvmult
                   (fun a : Ts =>
                      ((fun n : nat => F n a) (S k)%nat)) G)
                (rvmult
                   (fun a : Ts =>
                      (Rmax_list (map (fun n : nat => F n a) (seq 0 (S k))))) G))).
    {
      intros ?.
      rv_unfold.
      rewrite  Rmax_list_app by now simpl.
      unfold Rmax.
      rewrite plus_0_l.
      destruct (Rle_dec (Rmax_list (map (fun n : nat => F n a) (seq 0 (S k)))) (F (S k) a)); trivial.
    } 
    apply IsFiniteExpectation_case.
    - apply rvmult_rv; auto.
    - apply rvmult_rv; auto 3.
      apply rvmaxlist_rv; auto.
    - apply H; lia.
    - apply IHk; intros.
      apply H; lia.
  Qed.
  
  Lemma IsFiniteExpectation_rvmult_rvmaxlist F G k j
        {rvF:forall n, RandomVariable dom borel_sa (F n)}
        {rvG:forall n, RandomVariable dom borel_sa (G n)}
    :
    (forall a b, (a <= k -> b <= j)%nat ->
            IsFiniteExpectation Prts (rvmult (F a) (G b))) ->
    IsFiniteExpectation Prts
                        (rvmult (rvmaxlist F k) (rvmaxlist G j)).
  Proof.
    intros.
    apply IsFiniteExpectation_rvmult_rvmaxlist1; try typeclasses eauto; intros.
    rewrite rvmult_comm.
    apply IsFiniteExpectation_rvmult_rvmaxlist1; try typeclasses eauto; intros.
    rewrite rvmult_comm.
    now apply H.
  Qed.

  Lemma rvsqr_minus_foil (x y:Ts -> R) :
    rv_eq (rvsqr (rvminus x y)) (rvplus (rvminus (rvsqr x) (rvscale 2 (rvmult x y))) (rvsqr y)).
  Proof.
    intros ?.
    rv_unfold.
    unfold Rsqr.
    lra.
  Qed.

  Lemma rvmult_rvminus_distr (a b c:Ts->R) :
    rv_eq (rvmult a (rvminus b c)) (rvminus (rvmult a b) (rvmult a c)).
  Proof.
    intros ?.
    rv_unfold.
    lra.
  Qed.

  Instance isfe_Sum1_r_from_crossmult X m
        {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
        {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))} :
    let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
    forall a b, IsFiniteExpectation Prts (rvmult (Sum b) (X a)).
  Proof.
    intros.
    unfold Sum.
    rewrite <- rvsum_distr_r.
    apply IsFiniteExpectation_sum; try typeclasses eauto; intros.
    now apply isfe_sqr_seq.
  Qed.

  Instance isfe_Sum1_from_crossmult X m
        {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
        {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))} :
    let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
    forall a b, IsFiniteExpectation Prts (rvmult (X a) (Sum b)).
  Proof.
    intros.
    rewrite rvmult_comm.
    now apply isfe_Sum1_r_from_crossmult.
  Qed.

  Instance isfe_Sum_from_crossmult X m
           {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
           {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))} :
    let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
    forall a b, IsFiniteExpectation Prts (rvmult (Sum a) (Sum b)).
  Proof.
    intros.
    rewrite rvmult_comm.
    unfold Sum.
    rewrite <- rvsum_distr_r.
    apply IsFiniteExpectation_sum; try typeclasses eauto; intros.
  Qed.

  Instance isfe_sqr_Sum X m
           {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
           {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))} :
    forall a,
      IsFiniteExpectation Prts (rvsqr (rvsum (fun n => X (n + m)%nat) a)).
  Proof.
    intros.
    now apply isfe_Sum_from_crossmult.
  Qed.

  Lemma ash_6_1_4_filter (X: nat -> Ts -> R) {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      (eps:posreal) (m:nat)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      (isfesqr : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k)))
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                   (const 0))  :

  let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
  (* Note that this is derivable from isfemult *)
  forall (isfe2: forall n, IsFiniteExpectation _ ((rvsqr (Sum n)))), 
  forall (n:nat), ps_P (event_ge dom (rvmaxlist (fun k => rvabs(Sum k)) n) eps) <=
             FiniteExpectation _ (rvsqr (Sum n))/eps^2.
Proof.
  intros.
  assert (H1 : event_equiv (event_ge dom (rvmaxlist (fun k => rvabs(Sum k)) n) eps)
                           (event_ge dom (rvabs(cutoff_eps_rv n eps Sum)) eps)).
  {
    intro omega.
    unfold proj1_sig, rvabs; simpl.
    split; intros H; try (apply Rle_ge; apply Rge_le in H).
    + now rewrite cutoff_ge_eps_rv_rvmaxlist_iff.
    + now rewrite <-cutoff_ge_eps_rv_rvmaxlist_iff.
  }
  rewrite H1.
  generalize (Chebyshev_ineq_div_mean0 (cutoff_eps_rv n eps Sum) _ eps); intros H3.

  assert (isfemult':forall k j, IsFiniteExpectation Prts
                                     (rvmult (cutoff_eps_rv k eps Sum) (cutoff_eps_rv j eps Sum))).
  {
    intros k j.
    apply IsFiniteExpectation_abs_id; try typeclasses eauto.
    eapply (IsFiniteExpectation_bounded _ (const 0) _ (rvmult (rvmaxlist (fun k => (rvabs (Sum k))) k) (rvmaxlist (fun k => (rvabs (Sum k))) j))).
    Unshelve.
    - intros ?; rv_unfold.
      apply Rabs_pos.
    - intros ?.
      rv_unfold.
      rewrite Rabs_mult.
      apply Rmult_le_compat; try apply Rabs_pos.
      + destruct (cutoff_eps_values k eps Sum a) as [k' [??]].
        rewrite H0.
        apply Rmax_spec.
        apply in_map_iff.
        exists k'.
        split; trivial.
        apply in_seq.
        lia.
      + destruct (cutoff_eps_values j eps Sum a) as [j' [??]].
        rewrite H0.
        apply Rmax_spec.
        apply in_map_iff.
        exists j'.
        split; trivial.
        apply in_seq.
        lia.
    - apply IsFiniteExpectation_rvmult_rvmaxlist; try typeclasses eauto; intros.
      rewrite <- rvmult_abs.
      apply IsFiniteExpectation_abs; try typeclasses eauto.
  } 

  
  assert (isfes:forall n, IsFiniteExpectation Prts (rvsqr (cutoff_eps_rv n eps Sum))).
  {
    intros j.
    rewrite rvsqr_eq.
    apply isfemult'.
  } 

  rewrite <- (FiniteNonnegExpectation_alt _ _) in H3.
  simpl in H3.
  rewrite <- Rsqr_pow2.
  unfold rvabs in H3.
  eapply Rle_trans; [apply H3 |].
  unfold Rdiv.
  apply Rmult_le_compat_r; 
    [left; apply Rinv_0_lt_compat, Rlt_0_sqr, Rgt_not_eq, cond_pos |].
  assert (Srel:forall j, FiniteExpectation _ (rvsqr (Sum (S j))) =
                    FiniteExpectation _ (rvsqr (Sum j)) + 
                    FiniteExpectation _ (rvsqr (X ((S j)+m)%nat))).
  {
    intros.
    assert (rv_eq (rvsqr (Sum (S j)))
                  (rvplus (rvsqr (Sum j))
                          (rvplus 
                             (rvscale 2
                                      (rvmult (Sum j) (X ((S j)+m)%nat)))
                             (rvsqr (rvminus (Sum (S j)) (Sum j)))))).
    - intro x.
      unfold rvsqr, rvminus, rvopp, rvscale, rvplus, rvmult.
      unfold Rsqr.
      replace (Sum (S j) x) with ((Sum j x) + (X ((S j)+m)%nat x)).
      + now ring_simplify.
      + unfold Sum, rvsum.
        rewrite sum_Sn.
        unfold plus; simpl.
        now unfold plus; simpl.
    - assert (isfep:IsFiniteExpectation Prts
                                       (rvplus (rvsqr (Sum j))
                                               (rvplus (rvscale 2 (rvmult (Sum j) (X (S j + m)%nat))) (rvsqr (rvminus (Sum (S j)) (Sum j)))))).
      {
        eapply IsFiniteExpectation_proper; [symmetry; apply H | ].
        typeclasses eauto.
      } 
      rewrite (FiniteExpectation_ext _ _ _ H).
      erewrite (FiniteExpectation_plus' _ _ _ ).
      erewrite (FiniteExpectation_plus' _ _ _ ).
      rewrite <- Rplus_assoc.
      erewrite (FiniteExpectation_scale' _ _ _).

      {
        Unshelve.
        - shelve.
        - apply (IsFiniteExpectation_proper _ (rvminus (rvplus (rvsqr (Sum j))
                                                                (rvplus (rvscale 2 (rvmult (Sum j) (X (S j + m)%nat))) (rvsqr (rvminus (Sum (S j)) (Sum j)))))
                                                       ((rvsqr (Sum j))))).
          + intros ?; rv_unfold; lra.
          + apply IsFiniteExpectation_minus; typeclasses eauto.
        - rewrite rvsqr_minus_foil.
          typeclasses eauto.
      }
      Unshelve.

     assert (isfe_mult_sum : forall k j : nat,
                  IsFiniteExpectation Prts
                    (rvmult (rvsum (fun n : nat => X (n + m)%nat) j) (X (k + m)%nat))).
     {
       intros.
       rewrite <- rvsum_distr_r.
       apply IsFiniteExpectation_sum
       ; try typeclasses eauto.
       intros.
       now apply isfe_sqr_seq.
     } 
     generalize (expec_cross_zero_sum2_shift_filter X m isfilt filt_sub HC); intros.
     replace (FiniteExpectation Prts (rvmult (Sum j) (X (S j + m)%nat))) with 0.
     + ring_simplify.
       f_equal.
       assert (rv_eq (rvsqr (rvminus (Sum (S j)) (Sum j)))
                     (rvsqr (X ((S j)+m)%nat))).
       * intro x.
         unfold Sum, rvsqr.
         rewrite rvminus_unfold.
         unfold rvsum.
         rewrite sum_Sn.
         unfold plus; simpl.
         unfold Rsqr; ring.
       * apply FiniteExpectation_ext.
         apply H2.
     + specialize (H0 j (S j)).
       rewrite <- H0; try lia.
       unfold Sum.
       apply FiniteExpectation_pf_irrel.
  }

  assert (isfee:forall j, IsFiniteExpectation Prts (rvsqr (rvminus (cutoff_eps_rv (S j) eps Sum) 
                                                              (cutoff_eps_rv j eps Sum)))).
  {
    intros.
    rewrite rvsqr_minus_foil.
    typeclasses eauto.
  } 
                                                                     
  assert (Zrel:forall j, FiniteExpectation Prts (rvsqr (cutoff_eps_rv (S j) eps Sum)) =
                    FiniteExpectation Prts (rvsqr (cutoff_eps_rv j eps Sum)) + 
                    FiniteExpectation Prts (rvsqr (rvminus (cutoff_eps_rv (S j) eps Sum) 
                                                     (cutoff_eps_rv j eps Sum)))).
  {
    intros.
    assert (rv_eq (rvsqr (cutoff_eps_rv (S j) eps Sum)) 
                  (rvplus (rvsqr (cutoff_eps_rv j eps Sum))
                          (rvplus
                             (rvscale 2
                                      (rvmult (cutoff_eps_rv j eps Sum)
                                              (rvminus (cutoff_eps_rv (S j) eps Sum) 
                                                     (cutoff_eps_rv j eps Sum))))
                             (rvsqr (rvminus (cutoff_eps_rv (S j) eps Sum) 
                                             (cutoff_eps_rv j eps Sum)))))).
    - intro x.
      unfold rvsqr, rvminus, rvopp, rvscale, rvplus, rvmult.
      unfold Rsqr.
      replace (Sum (S j) x) with ((Sum j x) + (X ((S j)+m)%nat x)).
      + now ring_simplify.
      + unfold Sum, rvsum.
        rewrite sum_Sn.
        now unfold plus; simpl.
    - rewrite (FiniteExpectation_ext_alt _ _ _ H).
      erewrite (FiniteExpectation_plus' _ _ _ ).
      erewrite (FiniteExpectation_plus' _ _ _ ).
      rewrite <- Rplus_assoc.
      f_equal.
      erewrite (FiniteExpectation_scale' _ _ _).
      {
        Unshelve.
        - shelve.
        - apply IsFiniteExpectation_plus; [typeclasses eauto | typeclasses eauto | | typeclasses eauto].
          apply IsFiniteExpectation_scale.
          rewrite rvmult_rvminus_distr.
          apply IsFiniteExpectation_minus; typeclasses eauto.
        - apply IsFiniteExpectation_scale.
          rewrite rvmult_rvminus_distr.
          apply IsFiniteExpectation_minus; typeclasses eauto.
        - rewrite rvmult_rvminus_distr.
          apply IsFiniteExpectation_minus; typeclasses eauto.
      }
      Unshelve.
     assert (Expectation (rvmult (cutoff_eps_rv j eps Sum) (rvminus (cutoff_eps_rv (S j) eps Sum) (cutoff_eps_rv j eps Sum))) = Some (Rbar.Finite 0)).
     + assert (Heq :rv_eq
                      (rvmult (cutoff_eps_rv j eps Sum) 
                              (rvmult 
                                 (cutoff_indicator (S j) eps Sum)
                                 (X ((S j)+m)%nat)))
                      (rvmult 
                         (cutoff_eps_rv j eps Sum) 
                         (rvminus (cutoff_eps_rv (S j) eps Sum) 
                                  (cutoff_eps_rv j eps Sum)))).
        {
         intros w.
         rv_unfold. f_equal. ring_simplify.
         unfold cutoff_eps_rv, cutoff_indicator, EventIndicator.
         rewrite (cutoff_eps_succ_minus eps (fun k => Sum k w) j).
         unfold Sum, rvsum. rewrite sum_Sn. unfold plus. simpl.
         rewrite Rplus_comm.
         unfold Rminus; rewrite Rplus_assoc.
         replace  (sum_n (fun n0 : nat => X (n0+m)%nat w) j + - sum_n (fun n0 : nat => X (n0+m)%nat w) j) with 0 by lra.
         rewrite Rplus_0_r.
         match_destr.
         - match_destr.
           + lra.
           + tauto.
         - match_destr.
           + tauto.
           + lra.
        }
        erewrite <-(Expectation_ext Heq).
        assert (rv_eq
                  (rvmult (cutoff_eps_rv j eps Sum)
                          (rvmult (cutoff_indicator (S j) eps Sum) (X ((S j)+m)%nat)))
                  (rvmult 
                     (rvmult (cutoff_eps_rv j eps Sum)
                             (cutoff_indicator (S j) eps Sum))
                     (X ((S j)+m)%nat))) by now rewrite rvmult_assoc.
        erewrite (Expectation_ext H0).
        eapply indicator_prod_cross_shift_filter; trivial.
        intros; now apply IsFiniteExpectation_rvsqr_lower.
     + generalize (Expectation_IsFiniteExpectation _ _ _ H0); intros isfee2.
       rewrite (FiniteExpectation_Expectation _ _) in H0.
       invcs H0.
       erewrite (FiniteExpectation_pf_irrel) in H4.
       rewrite H4.
       lra.
 }
 clear H1 H3.
 induction n.
 - simpl.
   right.
   apply FiniteExpectation_ext.
   intro x.
   now unfold rvsqr, Sum.
 - specialize (Srel n).
   rewrite Srel.
   specialize (Zrel n).
   rewrite (FiniteExpectation_pf_irrel _ (rvsqr (cutoff_eps_rv (S n) eps Sum))).
   rewrite Zrel.
   apply Rplus_le_compat; trivial.
   {
     rewrite (FiniteExpectation_pf_irrel _ (rvsqr (cutoff_eps_rv n eps Sum))) in IHn.
     rewrite (FiniteExpectation_pf_irrel _  (rvsqr (Sum n))) in IHn.
     trivial.
   } 
   apply FiniteExpectation_le.
   intro x.
   unfold rvsqr.
   rewrite rvminus_unfold.
   unfold cutoff_eps_rv.
   simpl.
   match_destr; try (do 2 rewrite Rsqr_pow2; rewrite Rminus_eq_0).
   + generalize (cutoff_eps_succ_minus eps (fun j => Sum j x) n); intros Hcut.
     simpl in Hcut. match_destr_in Hcut; intuition; try (lra).
     rewrite Hcut. unfold Sum. right.
     f_equal. unfold rvsum. rewrite sum_Sn. unfold plus.
     simpl. now ring_simplify.
   + rewrite <-Rsqr_pow2. unfold Rsqr. eapply Rle_trans; try (apply pow2_ge_0).
     lra.
Qed.

Lemma ash_6_1_4 (X: nat -> Ts -> R) (eps:posreal) (m:nat)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      (isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k)))
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filtration_history_sa_sub X n) (X (S n)))
                (const 0))  :
  let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
  forall (isfe2: forall n, IsFiniteExpectation _ ((rvsqr (Sum n)))), 

  forall (n:nat), ps_P (event_ge dom (rvmaxlist (fun k => rvabs(Sum k)) n) eps) <=
                  (FiniteExpectation Prts (rvsqr (Sum n)))/eps^2.
Proof.
  apply ash_6_1_4_filter with (filt_sub := filtration_history_sa_sub X); trivial.
  - apply filtration_history_sa_is_filtration.
  - apply filtration_history_sa_is_adapted.
Qed.

Lemma var_sum_cross_0_offset_filter (X : nat -> Ts -> R) (m : nat)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      (isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k)))
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
  let Xm := fun n => X (n + m)%nat in
  let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
  forall j (isfej:IsFiniteExpectation Prts (rvsqr (rvsum Xm j))),
          FiniteExpectation Prts (rvsqr (rvsum Xm j)) =
            sum_n (fun n => FiniteExpectation Prts (rvsqr (X (n + m)%nat))) j.
Proof.
  intros.
  induction j.
  - assert (rv_eq (rvsqr (rvsum Xm 0%nat)) (rvsqr (X m))). 
    + intro x.
      unfold Xm, rvsqr, rvsum; simpl.
      now rewrite sum_O.
    + rewrite (FiniteExpectation_ext _ _ _ H).
      now rewrite sum_O.
  - rewrite sum_Sn.
    unfold plus; simpl.
    assert (rv_eq (rvsqr (rvsum Xm (S j)))
                  (rvplus (rvsqr (rvsum Xm j))
                          (rvplus
                             (rvscale 2
                                      (rvmult (rvsum Xm j) (X ((S j)+m)%nat)))
                             (rvsqr (X ((S j)+m)%nat))))).
    + intro x.
      unfold Xm, rvsqr, rvplus, rvsum.
      rewrite sum_Sn.
      unfold plus; simpl.
      unfold Rsqr, rvscale, rvmult.
      ring.
    + rewrite (FiniteExpectation_ext_alt _ _ _ H).
      erewrite (FiniteExpectation_plus' _ _ _ ).
      erewrite (FiniteExpectation_plus' _ _ _ ).
      erewrite (FiniteExpectation_scale' _ _ _).
      generalize (expec_cross_zero_sum2_shift_filter X m _ _ HC); intros; try lia.
      unfold Xm.
      specialize (H0 j (S j)).
      cut_to H0; try lia.
      rewrite H0.
      ring_simplify.
      f_equal.
      rewrite IHj.
      reflexivity.
Qed.

    Lemma sa_sigma_is_ELimInf_seq (f : nat -> Ts -> Rbar) (c:Rbar)
          {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} :
      sa_sigma _ (fun omega => is_ELimInf_seq (fun n => f n omega) c).
    Proof.
      assert (pre_event_equiv
                (fun omega => is_ELimInf_seq (fun n => f n omega) c)
                (fun omega => ELimInf_seq (fun n => f n omega) = c)).
      {
        intros ?.
        unfold ELimInf_seq, proj1_sig.
        match_destr.
        split; intros.
        - apply is_ELimInf_seq_unique in i.
          apply is_ELimInf_seq_unique in H.
          now rewrite <- i, <- H.
        - now rewrite <- H.
      }
      rewrite H.
      apply Rbar_sa_le_pt.
      intros.
      apply Rbar_lim_inf_measurable.
      typeclasses eauto.
   Qed.

    Lemma sa_sigma_is_ELimSup_seq (f : nat -> Ts -> Rbar) (c:Rbar)
          {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} :
      sa_sigma _ (fun omega => is_ELimSup_seq (fun n => f n omega) c).
    Proof.
      assert (pre_event_equiv
                (fun omega => is_ELimSup_seq (fun n => f n omega) c)
                (fun omega => ELimSup_seq (fun n => f n omega) = c)).
      {
        intros ?.
        unfold ELimSup_seq, proj1_sig.
        match_destr.
        split; intros.
        - apply is_ELimSup_seq_unique in i.
          apply is_ELimSup_seq_unique in H.
          now rewrite <- i, <- H.
        - now rewrite <- H.
      }
      rewrite H.
      apply Rbar_sa_le_pt.
      intros.
      apply Rbar_lim_sup_measurable.
      typeclasses eauto.
   Qed.

    Lemma sa_sigma_is_Elim_seq (f : nat -> Ts -> Rbar) (c:Rbar)
          {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} :
      sa_sigma _ (fun omega => is_Elim_seq (fun n => f n omega) c).
    Proof.
      assert (pre_event_equiv
                (fun omega : Ts => is_Elim_seq (fun n : nat => f n omega) c)
                (pre_event_inter
                   (fun omega : Ts => is_ELimInf_seq (fun n : nat => f n omega) c)
                   (fun omega : Ts => is_ELimSup_seq (fun n : nat => f n omega) c))).
      {
        intros ?.
        unfold pre_event_inter.
        split; intros.
        - split.
          + now apply is_Elim_LimInf_seq.
          + now apply is_Elim_LimSup_seq.
        - destruct H.
          now apply is_ELimSup_LimInf_lim_seq .
      }
      rewrite H.
      apply sa_inter.
      - now apply sa_sigma_is_ELimInf_seq.
      - now apply sa_sigma_is_ELimSup_seq.
   Qed.

   Lemma sa_sigma_is_lim_seq (f : nat -> Ts -> R) (c:Rbar)
         {rv : forall n, RandomVariable dom borel_sa (f n)} :
     sa_sigma _ (fun omega => is_lim_seq (fun n => f n omega) c).
   Proof.
     assert (pre_event_equiv
               (fun omega => is_lim_seq (fun n => f n omega) c)
               (fun omega => is_Elim_seq (fun n => f n omega) c)).
     {
       intros ?.
       now rewrite is_Elim_seq_fin.
     }
     rewrite H.
     apply sa_sigma_is_Elim_seq.
     intros.
     now apply Real_Rbar_rv.
  Qed.

Lemma sa_sigma_not_convergent (X : nat -> Ts -> R) (X0 : Ts -> R) (eps : posreal) (N : nat)
      {rv : forall n, RandomVariable dom borel_sa (X n)}
      {rv0 : RandomVariable dom borel_sa X0} :
  sa_sigma _ (fun omega => exists n : nat, (n >= N)%nat /\ Rabs (X n omega - X0 omega) >= eps).
Proof.
  apply sa_countable_union; intros n.
  apply sa_inter; try apply sa_sigma_const_classic.
  apply sa_le_ge; intros r.
  apply Rabs_measurable.
  generalize (minus_measurable dom (X n) (X0)); intros.
  rewrite rvminus_unfold in H.
  apply H.
  -- apply rv_measurable; try apply rv.
  -- apply rv_measurable; try apply rv0.
Qed.


Lemma sa_sigma_not_cauchy (X : nat -> Ts -> R) (eps:posreal) (N : nat)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)} :
  sa_sigma _ (fun omega =>
              exists (n m : nat),
                (n >= N)%nat /\ (m >= N)%nat /\
                Rabs ((X n omega) - (X m omega)) >= eps) .
Proof.
  apply sa_countable_union; intros n.
  apply sa_countable_union; intros m.
  apply sa_inter.
  - apply sa_sigma_const_classic.
  - apply sa_inter.
    + apply sa_sigma_const_classic.
    + apply sa_le_ge; intros.
      apply Rabs_measurable.
      generalize (minus_measurable dom (X n) (X m)); intros.
      rewrite rvminus_unfold in H.
      apply H; now apply rv_measurable.
Qed.

Lemma sa_sigma_not_full_convergent (X : nat -> Ts -> R) X0
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
  {rv0 : RandomVariable dom borel_sa X0}:
  sa_sigma _ (fun omega => exists (eps : posreal), forall N:nat,
                  exists (n : nat),
                    (n >= N)%nat /\
                    Rabs ((X n omega) - (X0 omega)) >= eps).
Proof.
   assert (eqq1:pre_event_equiv
                 (fun omega => exists (eps : posreal), forall N:nat,
                        exists (n : nat),
                          (n >= N)%nat /\
                          Rabs ((X n omega) - (X0 omega)) >= eps)
                 (fun omega => exists (eps : QArith_base.Q),
                      (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} eps) /\
                      forall N:nat,
                      exists (n : nat),
                        (n >= N)%nat /\
                        Rabs ((X n omega) - (X0 omega)) >= Q2R eps)).
  {
    intros x.
    split.
    - intros [eps HH].
      destruct (Q_dense 0 eps) as [q [ql qr]].
      + apply cond_pos.
      + exists q.
        split.
        * apply Qreals.Rlt_Qlt.
          unfold QArith_base.inject_Z.
          unfold Q2R.
          simpl.
          rewrite Rmult_0_l.
          apply ql.
        * intros N.
          destruct (HH N) as [n [Hn1 Hn2]].
          exists n.
          intuition lra.
    - intros [eps [epos HH]].
      assert (qepspos: 0 < Q2R eps).
      {
        apply Qreals.Qlt_Rlt in epos.
        now rewrite RMicromega.Q2R_0 in epos.
      }
      exists (mkposreal (Q2R eps) qepspos).
      intros N.
      destruct (HH N) as [n [Hn1 Hn2]].
      exists n. intuition lra.
  }
  rewrite eqq1.
  apply sa_countable_union_iso; try typeclasses eauto.
  intros.
  destruct (Rlt_dec 0 (Q2R i)).
  - assert (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
    {
      apply Qreals.Rlt_Qlt.
      now rewrite RMicromega.Q2R_0.
    }
    eapply (sa_proper _  (fun omega => (forall N : nat,
      exists n : nat,
        (n >= N)%nat /\ Rabs (X n omega - X0 omega) >= Q2R i))).
    + firstorder.
    + apply sa_pre_countable_inter; intros N.
      now apply (sa_sigma_not_convergent X X0 (mkposreal _ r)).
  - eapply sa_proper; try apply sa_none.
    assert (~ QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
    {
      intros qlt.
      apply Qreals.Qlt_Rlt in qlt.
      now rewrite RMicromega.Q2R_0 in qlt.
    }
    firstorder.
Qed.

Lemma sa_sigma_not_full_cauchy (X : nat -> Ts -> R)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)} :
  sa_sigma _ (fun omega => exists (eps : posreal), forall N:nat,
                  exists (n m : nat),
                    (n >= N)%nat /\ (m >= N)%nat /\
                    Rabs ((X n omega) - (X m omega)) >= eps).
Proof.
  assert (eqq1:pre_event_equiv
                 (fun omega => exists (eps : posreal), forall N:nat,
                        exists (n m : nat),
                          (n >= N)%nat /\ (m >= N)%nat /\
                          Rabs ((X n omega) - (X m omega)) >= eps)
                 (fun omega => exists (eps : QArith_base.Q),
                      (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} eps) /\
                      forall N:nat,
                      exists (n m : nat),
                        (n >= N)%nat /\ (m >= N)%nat /\
                        Rabs ((X n omega) - (X m omega)) >= Q2R eps)).
  {
    intros x.
    split.
    - intros [eps HH].
      destruct (Q_dense 0 eps) as [q [ql qr]].
      + apply cond_pos.
      + exists q.
        split.
        * apply Qreals.Rlt_Qlt.
          unfold QArith_base.inject_Z.
          unfold Q2R.
          simpl.
          rewrite Rmult_0_l.
          apply ql.
        * intros N.
          destruct (HH N) as [n [m [? [? HH3]]]].
          exists n; exists m.
          intuition lra.
    - intros [eps [epos HH]].
      assert (qepspos: 0 < Q2R eps).
      {
        apply Qreals.Qlt_Rlt in epos.
        now rewrite RMicromega.Q2R_0 in epos.
      }
      exists (mkposreal (Q2R eps) qepspos).
      intros N.
      destruct (HH N) as [n [m [? [HH3]]]].
      exists n; exists m.
      intuition lra.
  }
  rewrite eqq1.
  apply sa_countable_union_iso; try typeclasses eauto.
  intros.
  destruct (Rlt_dec 0 (Q2R i)).
  - assert (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
    {
      apply Qreals.Rlt_Qlt.
      now rewrite RMicromega.Q2R_0.
    } 
    eapply (sa_proper _  (fun omega => (forall N : nat,
      exists n m : nat,
        (n >= N)%nat /\ (m >= N)%nat /\ Rabs (X n omega - X m omega) >= Q2R i))).
    + firstorder.
    + apply sa_pre_countable_inter; intros N.
      now apply (sa_sigma_not_cauchy X (mkposreal _ r)).
  - eapply sa_proper; try apply sa_none.
    assert (~ QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
    {
      intros qlt.
      apply Qreals.Qlt_Rlt in qlt.
      now rewrite RMicromega.Q2R_0 in qlt.
    } 
    firstorder.
Qed.

Definition cauchy_seq_at {A : Type}(omega : A) (X : nat -> A -> R) := forall (eps:posreal),
    exists (N:nat), forall (n m : nat),  (n >= N)%nat -> (m >= N)%nat -> Rabs ((X n omega) - (X m omega)) < eps.

Lemma sa_sigma_cauchy_descending (X : nat -> Ts -> R)(eps : posreal)
      {rv : forall n, RandomVariable dom borel_sa (X n)}:
  forall n, let E := fun n => exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps n) in
    event_sub (E (S n)) (E n).
Proof.
  intros n E.
  repeat red. intros omega H.
  red in H. destruct H as [n0 [m0 [H1 [H2 H3]]]].
  exists n0; exists m0.
  repeat split; try lia; trivial.
Qed.

Lemma sa_sigma_cauchy_inter_event_sub (X : nat -> Ts -> R) {eps1 eps2 : posreal}
      {rv : forall n, RandomVariable dom borel_sa (X n)} (Heps : eps2 < eps1) (n : nat):
  event_sub (inter_of_collection (fun n => exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps1 n)))
            (inter_of_collection (fun n => exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps2 n))).
Proof.
  repeat red. intros omega H.
  repeat red in H. intros m.
  specialize (H m).
  destruct H as [n0 [m0 [H1 [H2 H3]]]].
  exists n0; exists m0.
  repeat split; try lia; try lra.
Qed.

(* Move to ProbSpace.v *)
Lemma ps_union_countable_union_iff (coll : nat -> event dom):
  (forall n, ps_P (coll n) = 0) <-> (ps_P (union_of_collection coll) = 0).
  Proof.
    split; intros H.
    + now apply ps_zero_countable_union.
    + intros n.
      assert (H1 : 0 <= ps_P (coll n)) by (apply ps_pos).
      assert (H2 : ps_P (coll n) <= ps_P (union_of_collection coll)).
      {
        apply ps_sub.
        apply union_of_collection_sup.
      }
      rewrite H in H2.
      lra.
  Qed.

  Lemma recip_pos (m : nat) : 0 < /(1 + INR m).
  Proof.
    apply Rinv_pos.
    generalize (pos_INR m). generalize (INR m) as x; intros.
    lra.
  Qed.

 Lemma almost_convergent_iff (X : nat -> Ts -> R) X0
       {rv : forall n, RandomVariable dom borel_sa (X n)}
   {rv0 : RandomVariable dom borel_sa X0}:
   event_equiv ((exist (sa_sigma _) _ (sa_sigma_not_full_convergent X X0)))
               (union_of_collection
                  (fun m => inter_of_collection
                           (fun k => exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 (mkposreal (/(1 + INR m)) (recip_pos _)) k)))).
 Proof.
    simpl.
   intros omega. simpl.
   split; intros.
   + destruct H as [eps Heps].
     generalize (archimed_cor1 eps (cond_pos eps)); intros.
     destruct H as [N [HN1 HN2]].
     assert (/(1 + INR N) < eps).
     {
       eapply Rlt_trans; eauto.
       apply Rinv_lt_contravar; try lra.
       apply Rmult_lt_0_compat; try (now apply lt_0_INR).
       generalize (pos_INR N). generalize (INR N) as x; intros.
       lra.
     }
     exists N.
     intros n1.
     specialize (Heps n1).
     destruct Heps as [n0 [Hn1 Hn2]].
     exists n0.
     repeat split; try trivial.
     eapply Rge_trans; eauto.
     lra.
   + destruct H as [N HN].
     exists (mkposreal (/(1 + INR N)) (recip_pos _)).
     simpl. intros N0.
     specialize (HN N0).
     assumption.
 Qed.

 Lemma almost_cauchy_iff (X : nat -> Ts -> R)
    {rv : forall n, RandomVariable dom borel_sa (X n)}:
   event_equiv ((exist (sa_sigma _) _ (sa_sigma_not_full_cauchy X)))
               (union_of_collection
                  (fun m => inter_of_collection
                           (fun k => exist (sa_sigma _) _ (sa_sigma_not_cauchy X (mkposreal (/(1 + INR m)) (recip_pos _)) k)))).
 Proof.
   simpl.
   intros omega. simpl.
   split; intros.
   + destruct H as [eps Heps].
     generalize (archimed_cor1 eps (cond_pos eps)); intros.
     destruct H as [N [HN1 HN2]].
     assert (/(1 + INR N) < eps).
     {
       eapply Rlt_trans; eauto.
       apply Rinv_lt_contravar; try lra.
       apply Rmult_lt_0_compat; try (now apply lt_0_INR).
       generalize (pos_INR N). generalize (INR N) as x; intros.
       lra.
     }
     exists N.
     intros n1.
     specialize (Heps n1).
     destruct Heps as [n0 [m0 [Hn0 [Hm0 Hnm]]]].
     exists n0. exists m0.
     repeat split; try trivial.
     eapply Rge_trans; eauto.
     lra.
   + destruct H as [N HN].
     exists (mkposreal (/(1 + INR N)) (recip_pos _)).
     simpl. intros N0.
     specialize (HN N0).
     assumption.
 Qed.

 Lemma ps_P_sub_zero (E1 E2 : event dom) :
   event_sub E1 E2 -> ps_P E2 = 0 -> ps_P E1 = 0.
 Proof.
   intros.
   generalize (ps_sub _ E1 E2 H); intros.
   rewrite H0 in H1.
   generalize (ps_pos E1); intros.
   lra.
 Qed.

  (* ash prob 2.5.4 *)
Lemma almost_cauchy_seq_at_iff (X : nat -> Ts -> R)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)} :
  almost _ (fun omega => cauchy_seq_at omega X) <->
  (forall (eps:posreal),
      Lim_seq (fun N =>
                 ps_P (exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps N))) = 0).
Proof.
  assert (H1 : forall (eps: posreal),let E := fun n => exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps n) in
                                is_lim_seq (fun k => ps_P (E k)) (ps_P (inter_of_collection E))).
  {
    intros eps E.
    apply is_lim_descending.
    apply sa_sigma_cauchy_descending.
  }
  unfold cauchy_seq_at.
  split; intros.
  + rewrite almost_alt_eq in H.
    unfold almost_alt in H.
    destruct H as [E [HE Heps]].
    specialize (H1 eps). simpl in H1.
    apply is_lim_seq_unique in H1. rewrite H1.
    rewrite Rbar_finite_eq.
    apply ps_P_sub_zero with E; trivial.
    intros omega.
    simpl; specialize (Heps omega).
    intros. apply Heps. push_neg.
    push_neg_in Heps.
    now exists eps.
  + (* forall 0<δ, P(B_δ) = 0*)
    assert (Hinter : forall eps:posreal, let E :=
         fun n : nat => exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps n) in
                                    (ps_P (inter_of_collection E)) = 0).
    {
      intros eps E.
      rewrite <-Rbar_finite_eq.
      rewrite <-H with eps. symmetry.
      apply is_lim_seq_unique. apply H1.
    }
    clear H.
    rewrite almost_alt_eq.
    unfold almost_alt.
    exists (exist (sa_sigma _) _ (sa_sigma_not_full_cauchy X)).
    split.
    ++ rewrite almost_cauchy_iff.
       rewrite <-ps_union_countable_union_iff.
       intros n; apply (Hinter ({| pos := /(1 + INR n); cond_pos := recip_pos n|})).
    ++ intros omega Hnot.
       simpl. now push_neg_in Hnot.
Qed.


(*TODO(Kody): Simplify this proof using the above.*)
Lemma almost_cauchy_is_lim_seq_iff (X : nat -> Ts -> R)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)} :
  almost _ (fun omega => cauchy_seq_at omega X) <->
  (forall (eps:posreal),
      is_lim_seq (fun N =>
                 ps_P (exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps N))) 0).
Proof.
  assert (H1 : forall (eps: posreal),let E := fun n => exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps n) in
                                is_lim_seq (fun k => ps_P (E k)) (ps_P (inter_of_collection E))).
  {
    intros eps E.
    apply is_lim_descending.
    apply sa_sigma_cauchy_descending.
  }
  unfold cauchy_seq_at.
  split; intros.
  + rewrite almost_alt_eq in H.
    unfold almost_alt in H.
    destruct H as [E [HE Heps]].
    specialize (H1 eps). simpl in H1.
    enough (Hpsp : ps_P (
                    inter_of_collection(
                        fun n => (exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps n)))) = 0).
    - now rewrite <-Hpsp.
    - apply ps_P_sub_zero with E; trivial.
      intros omega.
      simpl; specialize (Heps omega).
      intros. apply Heps. push_neg.
      push_neg_in Heps.
      now exists eps.
  + (* forall 0<δ, P(B_δ) = 0*)
    assert (Hinter : forall eps:posreal, let E :=
         fun n : nat => exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps n) in
                                    (ps_P (inter_of_collection E)) = 0).
    {
      intros eps E.
      rewrite <-Rbar_finite_eq.
      rewrite <-(is_lim_seq_unique _ _ (H eps)). symmetry.
      apply is_lim_seq_unique. apply H1.
    }
    clear H.
    rewrite almost_alt_eq.
    unfold almost_alt.
    exists (exist (sa_sigma _) _ (sa_sigma_not_full_cauchy X)).
    split.
    ++ rewrite almost_cauchy_iff.
       rewrite <-ps_union_countable_union_iff.
       intros n; apply (Hinter ({| pos := /(1 + INR n); cond_pos := recip_pos n|})).
    ++ intros omega Hnot.
       simpl. now push_neg_in Hnot.
Qed.

Lemma almost_is_lim_seq_iff (X : nat -> Ts -> R) X0
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
  {rv0 : RandomVariable dom borel_sa X0}:
  almost _ (fun omega => is_lim_seq (fun n => X n omega) (X0 omega)) <->
  (forall (eps:posreal),
      is_lim_seq (fun N =>
                    ps_P (exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 eps N))) 0).
Proof.
  assert (H1 : forall (eps: posreal),let E := fun n => exist (sa_sigma _) _
                                                     (sa_sigma_not_convergent X X0 eps n) in
                                is_lim_seq (fun k => ps_P (E k)) (ps_P (inter_of_collection E))).
  {
    intros eps E.
    apply is_lim_descending.
    intros n. repeat red. intros omega H.
    red in H. destruct H as [n0 [m0 H]].
    exists n0. repeat split; try lia; trivial.
  }
  split; intros.
  + rewrite almost_alt_eq in H.
    unfold almost_alt in H.
    destruct H as [E [HE Heps]].
    specialize (H1 eps). simpl in H1.
    enough (Hpsp : ps_P (
                    inter_of_collection(
                        fun n => (exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 eps n)))) = 0).
    - now rewrite <-Hpsp.
    - apply ps_P_sub_zero with E; trivial.
      intros omega.
      simpl; specialize (Heps omega).
      intros. apply Heps. push_neg.
      setoid_rewrite is_lim_seq_Reals.
      unfold Un_cv. push_neg. exists eps.
      split; try apply cond_pos.
      now unfold R_dist.
  + (* forall 0<δ, P(B_δ) = 0*)
    assert (Hinter : forall eps:posreal, let E :=
         fun n : nat => exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 eps n) in
                                    (ps_P (inter_of_collection E)) = 0).
    {
      intros eps E.
      rewrite <-Rbar_finite_eq.
      rewrite <-(is_lim_seq_unique _ _ (H eps)). symmetry.
      apply is_lim_seq_unique. apply H1.
    }
    clear H.
    rewrite almost_alt_eq.
    unfold almost_alt.
    exists (exist (sa_sigma _) _ (sa_sigma_not_full_convergent X X0)).
    split.
    ++ rewrite almost_convergent_iff.
       rewrite <-ps_union_countable_union_iff.
       intros n; apply (Hinter ({| pos := /(1 + INR n); cond_pos := recip_pos n|})).
    ++ intros omega Hnot.
       simpl. setoid_rewrite is_lim_seq_Reals in Hnot.
       unfold Un_cv in Hnot. push_neg_in Hnot.
       destruct Hnot as [eps [Heps Hx]].
       now exists (mkposreal eps Heps).
Qed.

Global Instance rv_max_sum_shift (X : nat -> Ts -> R) (m n : nat)
         {rv : forall (k:nat), (k <= m+n)%nat -> RandomVariable dom borel_sa (X k)} :
  let Sum := fun j => (rvsum (fun k w => X (k+m)%nat w) j) in
  RandomVariable dom borel_sa (rvmaxlist (fun k : nat => rvabs (Sum k)) n).
Proof.
  apply rvmaxlist_rv; intros.
  apply rvabs_rv.
  apply rvsum_rv_loc; intros.
  apply rv; lia.
Defined.

Transparent rv_max_sum_shift.

Lemma Lim_seq_le (u v : nat -> R):
  (forall n, u n <= v n) -> Rbar_le (Lim_seq u) (Lim_seq v).
Proof.
  intros.
  apply Lim_seq_le_loc.
  exists (0%nat); intros.
  apply H.
Qed.

  Lemma event_ge_pf_irrel {x}
        {rv_X : Ts -> R}
        {rv1 : RandomVariable dom borel_sa rv_X}
        {rv2 : RandomVariable dom borel_sa rv_X} :
    event_equiv (event_ge dom rv_X (rv:=rv1) x)
                (event_ge dom rv_X (rv:=rv2) x).
  Proof.
    repeat red; intros.
    split; intros; trivial.
  Qed.

    Lemma sqr_pos (eps : posreal) :
      0 < Rsqr eps.
    Proof.
      apply Rsqr_pos_lt.
      apply Rgt_not_eq.
      apply cond_pos.
    Qed.

(*ash 6.2.1 *)

Lemma Ash_6_2_1_filter_helper (X : nat -> Ts -> R) (eps : posreal) (m : nat)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      (isfesqr : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k)))
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
  let Sum := fun j => rvsum (fun k => X (k+m)%nat) j in
  Rbar_le (Lim_seq (fun n => ps_P (event_ge dom (rvmaxlist (fun k => rvabs (Sum k)) n) eps)))
          (Rbar_div_pos (LimSup_seq (sum_n (fun n => FiniteExpectation Prts (rvsqr (X (n + m)%nat))))) (mkposreal _ (sqr_pos eps))).
Proof.
  intros.
  generalize (ash_6_1_4_filter X isfilt filt_sub); intros.
  specialize (H eps m _ _ HC (isfe_sqr_Sum X m)).
  simpl in H.
  generalize (Lim_seq_le _ _ H); intros.
  unfold Sum.
  eapply Rbar_le_trans.
  - apply H0.
  - replace (eps * (eps * 1)) with (Rsqr eps) by (unfold Rsqr; lra).
    unfold Rdiv.
    rewrite Lim_seq_scal_r.
    replace (Rbar.Finite (/ (Rsqr (pos eps)))) with (Rbar.Finite (/ (pos (mkposreal _ (sqr_pos eps))))) by now simpl.
    rewrite Rbar_mult_div_pos.
    apply Rbar_div_pos_le.
    generalize (var_sum_cross_0_offset_filter X m _ filt_sub _ HC); intros.
    simpl in H1.
    rewrite Lim_seq_ext with (v := sum_n (fun n : nat => FiniteExpectation Prts (rvsqr (X (n + m)%nat)))).
    + apply Lim_seq_sup_le.
    + intros.
      apply H1.
Qed.

 Lemma Ash_6_2_1_helper2 (X : nat -> Ts -> R) (eps : posreal)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))}
      (isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))) :
    ex_series (fun n => FiniteExpectation Prts (rvsqr (X n))) ->
    is_lim_seq (fun m =>
                  (Rbar_div_pos (LimSup_seq (sum_n (fun n => FiniteExpectation Prts (rvsqr (X (n + (S m))%nat))))) 
                                (mkposreal _ (sqr_pos eps)))) 0.
  Proof.
    intros.
    apply is_lim_seq_ext with
        (u := fun m => (Rbar_div_pos (Series (fun n => FiniteExpectation Prts (rvsqr (X (n + (S m))%nat))))
                                     (mkposreal _ (sqr_pos eps)))).
    {
      intros.
      generalize (LimSup_seq_series H); intros.
      now rewrite H0.
    }
    simpl.
    unfold Rdiv.
    replace (Rbar.Finite 0) with (Rbar_mult 0 (/ (mkposreal _ (sqr_pos eps)))).
    - apply is_lim_seq_scal_r.
      generalize (zerotails _ H); intros.
      apply is_lim_seq_ext with
          (u :=  (fun n : nat =>
          Series (fun k : nat => FiniteExpectation Prts (rvsqr (X (S (n + k))))))).
      + intros.
        apply Series_ext.
        intros.
        apply FiniteExpectation_ext.
        intro x.
        now replace (n0 + S n)%nat with (S (n + n0))%nat by lia.
      + apply H0.
    - simpl.
      now rewrite Rmult_0_l.
  Qed.

  Lemma list_union_rvmaxlist (f : nat -> Ts -> R) (eps : posreal) (n : nat) 
        (rv: forall n, RandomVariable dom borel_sa (f n)) :
    event_equiv
      (list_union
         (collection_take (fun k => event_ge dom (f k) eps) (S n)))
      (event_ge dom (rvmaxlist f n) eps).
  Proof.
    split.
    - intros [a [inn ax]].
      apply In_collection_take in inn.
      destruct inn as [m [mlt ?]]; subst.
      simpl in ax.
      simpl.
      unfold rvmaxlist.
      apply Rle_ge.
      apply Rge_le in ax.
      eapply Rmax_list_ge; eauto.
      apply in_map_iff.
      eexists; split; eauto.
      apply in_seq.
      lia.
    - intros rvm.
      simpl in rvm.
      unfold rvmaxlist, Rmax_list_map in rvm.
      generalize (Rmax_list_In (map (fun n : nat => f n x) (seq 0 (S n))))
      ; intros HH.
      cut_to HH; [| simpl; congruence].
      apply in_map_iff in HH.
      destruct HH as [m [fm mini]].
      exists (event_ge dom (f m) eps).
      split.
      + unfold collection_take.
        apply in_map_iff.
        eexists; split; eauto.
      + simpl.
        congruence.
  Qed.

 Lemma Ash_6_2_1_helper3 (X : nat -> Ts -> R) (eps : posreal) (m : nat) 
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))} :
   let Sum := fun j => rvsum X j in
    Rbar.Finite (ps_P (union_of_collection (fun k =>  event_ge dom (rvabs (rvminus (Sum (k+(S m))%nat) (Sum m))) eps))) =
    Lim_seq (fun n => ps_P (event_ge dom (rvmaxlist (fun k => rvabs (rvminus (Sum (k + (S m))%nat) (Sum m))) n) eps)).
   Proof.
     intros.
     assert (Rbar.Finite (ps_P
               (union_of_collection (fun k : nat => event_ge dom (rvabs (rvminus (Sum (k + (S m))%nat) (Sum m))) eps))) =
             Lim_seq (fun n => ps_P (list_union (collection_take (fun k : nat => event_ge dom (rvabs (rvminus (Sum (k + (S m))%nat) (Sum m))) eps) (S n))))).
     {
       rewrite lim_ascending.
       - now rewrite event_union_list_union.
       - unfold ascending_collection.
         intros.
         replace (S n) with (n+1)%nat by lia.
         rewrite collection_take_Sn.
         rewrite list_union_app.
         apply event_sub_union_l.
     }
     rewrite H.
     apply Lim_seq_ext.
     intros.
     apply ps_proper.
     apply list_union_rvmaxlist.
  Qed.

   Lemma sum_shift_diff (X : nat -> R) (m a : nat) :
     sum_n X (a + S m) - sum_n X m =
     sum_n (fun n0 : nat => X (n0 + S m)%nat) a.
   Proof.
     rewrite <- sum_n_m_shift.
     unfold sum_n.
     rewrite sum_split with (m0 := m); try lia.
     unfold plus; simpl.
     lra.
   Qed.

  Lemma Ash_6_2_1_filter_helper4 (X : nat -> Ts -> R) (eps : posreal) (m : nat) 
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
   let Sum := fun j => rvsum X j in
    Rbar_le (ps_P (union_of_collection (fun k =>  event_ge dom (rvabs (rvminus (Sum (k + (S m))%nat) (Sum m))) eps)))
            (Rbar_div_pos (LimSup_seq (sum_n (fun n => FiniteExpectation Prts (rvsqr (X (n + (S m))%nat))))) (mkposreal _ (sqr_pos eps))).
    Proof.
      intros.
      unfold Sum.
      rewrite Ash_6_2_1_helper3; trivial.
      generalize (Ash_6_2_1_filter_helper X eps (S m) _ _ _ HC); intros.
      simpl in H.
      rewrite Lim_seq_ext with
          (v :=  fun n : nat =>
            ps_P
              (event_ge dom
                 (rvmaxlist
                    (fun k : nat => rvabs (rvsum (fun k0 : nat => X (k0 + (S m))%nat) k))
                    n) eps)).
      - apply H.
      - intros.
        apply ps_proper.
        assert (rv_eq
                  (rvmaxlist
                     (fun k : nat =>
                        rvabs
                          (rvminus (rvsum (fun k0 : nat => X k0) (k + (S m)))
                                   (rvsum (fun k0 : nat => X k0) m))) n)
                   (rvmaxlist (fun k : nat => rvabs (rvsum (fun k0 : nat => X (k0 + (S m))%nat) k))
          n)).
        + intro x.
          unfold rvmaxlist.
          apply Rmax_list_Proper, refl_refl, map_ext.
          intros.
          unfold rvabs, rvsum.
          rewrite rvminus_unfold.
          f_equal.
          now rewrite sum_shift_diff.
        + intro x.
          simpl.
          now rewrite H0.
    Qed.

  Lemma Ash_6_2_1_filter_helper5 (X : nat -> Ts -> R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
    ex_series (fun n => FiniteExpectation Prts (rvsqr (X n))) ->
   let Sum := fun j => rvsum X j in
   forall (eps : posreal),
     is_lim_seq (fun m => ps_P (union_of_collection (fun k => event_ge dom (rvabs (rvminus (Sum (k + (S m))%nat) (Sum m))) eps))) 0. 
    Proof.
      intros.
      generalize (Ash_6_2_1_helper2 X eps _ H); intros.
      assert (forall m, 
                 0 <= (fun m : nat =>
                                ps_P
                                  (union_of_collection
                                     (fun k : nat =>
                                        event_ge dom (rvabs (rvminus (Sum (k + S m)%nat) (Sum m))) eps))) m <=
                 (fun m : nat =>
          Rbar_div_pos
            (LimSup_seq
               (sum_n (fun n : nat => FiniteExpectation Prts (rvsqr (X (n + (S m))%nat)))))
            {| pos := eps²; cond_pos := sqr_pos eps |}) m).
      {
        intros.
        split.
        - apply ps_pos.
        - generalize (Ash_6_2_1_filter_helper4 X eps m _ _ HC); intros.
          unfold Sum in H1.
          generalize (LimSup_seq_series H); intros.
          rewrite H2 in H1.
          simpl in H1.
          rewrite H2.
          simpl.
          unfold Sum.
          apply H1.
      }
      apply (is_lim_seq_le_le _ _ _ 0 H1); trivial.
      apply is_lim_seq_const.
   Qed.

    Lemma Ash_6_2_1_helper6a (X : nat -> Ts -> R) (eps : posreal) (N : nat) 
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))} :
      event_sub
        (exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps N))
        (union_of_collection (fun k => event_ge dom (rvabs (rvminus (X (k + (S N))%nat) (X N))) (eps/2))).
      Proof.
        unfold rvabs.
        intro x; simpl; intros.
        destruct H as [n [m [? [? ?]]]].
        destruct (Rge_dec (Rabs (X n x - X N x)) (eps/2)).
        - destruct (n == N).
          ++ rewrite e in r.
             rewrite Rminus_eq_0 in r.
             rewrite Rabs_R0 in r.
             generalize (is_pos_div_2 eps); intros; lra.
          ++ assert (n > N)%nat by (destruct H; try lia;firstorder).
             exists (n - (S N))%nat.
             rewrite rvminus_unfold.
             now replace (n - S N + S N)%nat with (n) by lia.
        - generalize (Rabs_triang (X n x - X N x) (X N x - X m x));intros.
          replace  (X n x - X N x + (X N x - X m x)) with (X n x - X m x) in H2 by lra.
          assert (Rabs (X N x - X m x) >= eps/2) by lra.
          destruct (m == N).
          ++ rewrite e in H3.
             rewrite Rminus_eq_0 in H3.
             rewrite Rabs_R0 in H3.
             generalize (is_pos_div_2 eps); intros; lra.
          ++ assert (m > N)%nat by (destruct H0; try lia; firstorder).
             exists (m - (S N))%nat.
             rewrite rvminus_unfold.
             replace (m - S N + S N)%nat with (m) by lia.
             now rewrite Rabs_minus_sym.
      Qed.

    Lemma Ash_6_2_1_helper6b (X : nat -> Ts -> R) (eps : posreal) (N : nat) 
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))} :
      event_sub
        (union_of_collection (fun k => event_ge dom (rvabs (rvminus (X (k + (S N))%nat) (X N))) eps))
        (exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps N)).
      Proof.
        unfold rvabs.
        intro x; simpl; intros.
        destruct H.
        exists (x0 + S N)%nat.
        exists N.
        rewrite rvminus_unfold in H.
        split; try lia.
        split; try lia; trivial.
    Qed.

  Lemma Ash_6_2_1_helper6  (X : nat -> Ts -> R) 
        {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))} :
    (forall (eps:posreal), 
        is_lim_seq (fun m => ps_P (union_of_collection (fun k => event_ge dom (rvabs (rvminus (X (k + (S m))%nat) (X m))) eps))) 0) <->
    (forall (eps:posreal), 
        is_lim_seq (fun N => ps_P (exist (sa_sigma _) _ (sa_sigma_not_cauchy X eps N))) 0).
    Proof.
      split; intros.
      - generalize (is_pos_div_2 eps); intros.
        specialize (H (mkposreal _ H0)).
        apply is_lim_seq_le_le with 
            (u := const 0) 
            (w :=  (fun m : nat =>
                      ps_P
                        (union_of_collection
                           (fun k : nat =>
                              event_ge dom (rvabs (rvminus (X (k + S m)%nat) (X m)))
                                       {| pos := eps / 2; cond_pos := H0 |})))).
        + intros; split.
          * apply ps_pos.
          * apply ps_sub.
            apply Ash_6_2_1_helper6a.
        + apply is_lim_seq_const.
        + apply H.
     - specialize (H eps).
       apply is_lim_seq_le_le with
           (u := const 0)
           (w :=  (fun N : nat =>
         ps_P
           (exist (sa_sigma _)
              (fun omega : Ts =>
               exists n m : nat,
                 (n >= N)%nat /\ (m >= N)%nat /\ Rabs (X n omega - X m omega) >= eps)
              (sa_sigma_not_cauchy X eps N)))).
       + intros; split.
         * apply ps_pos.
         * apply ps_sub.
           apply Ash_6_2_1_helper6b.
       + apply is_lim_seq_const.
       + apply H.
   Qed.            

  Lemma cauchy_seq_at_ex_series {A : Type} (X : nat -> A -> R)
      : forall x:A,
        cauchy_seq_at x (fun (n : nat) (omega : A) => sum_n (fun n0 : nat => X n0 omega) n)
        -> ex_series (fun n => X n x).
    Proof.
      intros x Hx.
      generalize (ex_series_Cauchy (fun n => X n x)); intros.
      apply H. clear H. unfold cauchy_seq_at in Hx.
      rewrite Cauchy_series_Reals.
      unfold Cauchy_crit_series.
      unfold Cauchy_crit.
      setoid_rewrite sum_n_Reals in Hx.
      intros. unfold R_dist.
      specialize (Hx (mkposreal eps H)); eauto.
    Qed.
    
    Lemma Ash_6_2_1_filter (X : nat -> Ts -> R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {isfesqr : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
    ex_series (fun n => FiniteExpectation Prts (rvsqr (X n))) ->
    almost Prts (fun (x : Ts) => ex_series (fun n => X n x)).
  Proof.
    intros.
    generalize (almost_cauchy_is_lim_seq_iff (rvsum X)); intros.
    generalize (Ash_6_2_1_helper6 (rvsum X)); intros.
    rewrite <- H1 in H0.
    clear H1.
    generalize (Ash_6_2_1_filter_helper5 X _ _ HC H); intros.
    simpl in H1.
    rewrite <- H0 in H1.
    unfold almost.
    destruct H1 as [E HE].
    exists E. destruct HE. split; trivial.
    intros.  specialize (H2 x H3).
    apply cauchy_seq_at_ex_series.
    apply H2.
  Qed.
  
  Lemma Ash_6_2_1 (X : nat -> Ts -> R)
        {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))}
        {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filtration_history_sa_sub X n) (X (S n)))
                (const 0))  :
    ex_series (fun n => FiniteExpectation Prts (rvsqr (X n))) ->
    almost Prts (fun (x : Ts) => ex_series (fun n => X n x)).
  Proof.
    intros.
    apply Ash_6_2_1_filter with (filt_sub := filtration_history_sa_sub X) 
                                (rv := rv) (isfesqr:=isfe2); trivial.
    - apply filtration_history_sa_is_filtration.
    - apply filtration_history_sa_is_adapted.
  Qed.

  Lemma induced_sigma_scale (X : nat -> Ts -> R) (b : nat -> R)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))}
      {frf : forall (n:nat), FiniteRangeFunction (X (n))} :
    (forall n, b n <> 0) ->
    forall n, Forall2 dsa_equiv (induced_sigma_generators (frf n)) (induced_sigma_generators (frfscale (/ b n) (X n))).
  Proof.
    intros.
    unfold induced_sigma_generators, SimpleExpectation.induced_sigma_generators_obligation_1.
    simpl.
    assert (forall n, / b n <> 0) by (intros; now apply Rinv_neq_0_compat).
    rewrite <- nodup_scaled, map_map; trivial.
    unfold rvscale, preimage_singleton.
    unfold pre_event_preimage, pre_event_singleton.
    rewrite <- Forall2_map.
    apply Forall2_refl.
    intros ??; simpl.
    split; intros.
    - subst; lra.
    - apply Rmult_eq_reg_l in H1; trivial.
  Qed.

  Lemma filtration_history_scale (X : nat -> Ts -> R) (b : nat -> R)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))}
      {frf : forall (n:nat), FiniteRangeFunction (X (n))} :
    (forall n, b n <> 0) ->
    forall n, Forall2 dsa_equiv (filtration_history n X) (filtration_history n (fun n0 : nat => rvscale (/ b n0) (X n0))).
  Proof.
    induction n.
    - now simpl.
    - simpl.
      apply refine_dec_sa_partitions_proper.
      + now apply induced_sigma_scale.
      + apply IHn.
  Qed.

  Lemma SCESA_scale (X : nat -> Ts -> R) (b : nat -> R)
        {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))}
        {isfe : forall k : nat, IsFiniteExpectation Prts (X k)}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filtration_history_sa_sub X n) (X (S n)))
                (const 0))  :
    (forall n, b n <> 0) ->
    forall n, almostR2 Prts eq
           (ConditionalExpectation Prts
                                   (filtration_history_sa_sub 
                                      (fun n0 : nat => rvscale (/ b n0) (X n0)) n)
                                   (rvscale (/ (b (S n))) (X (S n))))
           
              (const 0).
  Proof.
    intros.
    assert (forall n,
               sa_equiv (filtration_history_sa X n)
                        (filtration_history_sa (fun n0 => (rvscale (/ b n0) (X n0))) n)).
    {
      intros.
      apply filtrate_sa_proper.
      intros ??.
      apply pullback_sa_rvscale_equiv.
      now apply Rinv_neq_0_compat.
    }
    generalize (Condexp_scale Prts (filtration_history_sa_sub (fun n0 => (rvscale (/ b n0) (X n0))) n)
                              (/ b (S n)) (X (S n))); intros.
    specialize (HC n).
    specialize (H0 n).
    apply almostR2_prob_space_sa_sub_lift in H1.
    revert HC; apply almost_impl.
    revert H1; apply almost_impl.

    generalize (Condexp_sa_proper Prts
                                  (filtration_history_sa_sub X n)
                                  (filtration_history_sa_sub (fun n0 : nat => rvscale (/ b n0) (X n0)) n)
                                  H0 (X (S n)))
    ; intros HH.
    apply almostR2_prob_space_sa_sub_lift in HH.
    revert HH; apply almost_impl.
    apply all_almost; intros ????.
    rewrite H2.
    unfold Rbar_rvmult.
    rewrite <- H1.
    rewrite H3.
    unfold const.
    now rewrite Rbar_mult_0_r.
  Qed.

  Lemma Ash_6_2_2 (X : nat -> Ts -> R) (b : nat -> R)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))}
      {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))}
      {isfes:forall n, IsFiniteExpectation Prts (rvsqr (rvscale (/ b n) (X n)))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filtration_history_sa_sub X n) (X (S n)))
                (const 0))  :
    (forall n, 0 < b n <= b (S n)) ->
    is_lim_seq b p_infty ->
    ex_series (fun n => FiniteExpectation Prts (rvsqr (rvscale (/ (b n)) (X n)))) ->
    almost Prts (fun (x : Ts) => is_lim_seq (fun n => (rvscale (/ (b n)) (rvsum X n)) x) 0). 
  Proof.
    intros.
    assert (bneq0:forall n, b n <> 0).
    {
      intros.
      apply Rgt_not_eq.
      apply H.
    }
    assert (isfe:forall k : nat, IsFiniteExpectation Prts (X k))
      by (intros; now apply IsFiniteExpectation_rvsqr_lower).

    generalize (SCESA_scale X b HC bneq0); intros.
    assert (isfemult' : forall k j : nat,
             IsFiniteExpectation Prts
                                 (rvmult ((fun n : nat => rvscale (/ b n) (X n)) k) ((fun n : nat => rvscale (/ b n) (X n)) j))). 
    {
      intros.
      rewrite rvmult_rvscale.
      apply IsFiniteExpectation_scale.
      rewrite rvmult_comm, rvmult_rvscale.
      apply IsFiniteExpectation_scale.
      now apply isfe_sqr_seq.
    } 

    generalize (Ash_6_2_1 (fun n => rvscale (/ (b n)) (X n))); intros.
    specialize (H3 H2).
    destruct H3 as [? [? ?]].
    - revert H1.
      apply ex_series_ext; intros.
      apply FiniteExpectation_pf_irrel.
    - exists x.
      split; trivial.
      intros.
      generalize (ash_6_1_3_strong H H0 (H4 x0 H5)); intros.
      eapply is_lim_seq_ext; try (apply H6).
      intros; simpl.
      unfold rvsum, rvscale, Rdiv.
      rewrite Rmult_comm.
      f_equal.
      apply sum_n_ext.
      intros.
      simpl; field.
      apply Rgt_not_eq.
      apply H.
Qed.

  Lemma Ash_6_2_2_filter (X : nat -> Ts -> R) (b : nat -> R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X (n))}
      {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))}
      {isfes:forall n, IsFiniteExpectation Prts (rvsqr (rvscale (/ b n) (X n)))}
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
    (forall n, 0 < b n <= b (S n)) ->
    is_lim_seq b p_infty ->
    ex_series (fun n => FiniteExpectation Prts (rvsqr (rvscale (/ (b n)) (X n)))) ->
    almost Prts (fun (x : Ts) => is_lim_seq (fun n => (rvscale (/ (b n)) (rvsum X n)) x) 0). 
  Proof.
    intros.
    assert (bneq0:forall n, b n <> 0).
    {
      intros.
      apply Rgt_not_eq.
      apply H.
    }
    generalize (Ash_6_2_1_filter (fun n => rvscale (/ (b n)) (X n)) isfilt); intros.
    specialize (H2 filt_sub).
    assert (isad2: IsAdapted borel_sa (fun n : nat => rvscale (/ b n) (X n)) F).
    {
      intros.
      unfold IsAdapted.
      intros.
      apply rvscale_rv.
      apply adapt.
    }
    specialize (H2 isad2 (fun n => @rvscale_rv Ts dom (Rinv (b n)) (X n) (rv n))).
    specialize (H2 isfes).
    cut_to H2; trivial.
    - destruct H2 as [? [? ?]].
      exists x.
      split; trivial.
      intros.
      generalize (ash_6_1_3_strong H H0 (H3 x0 H4)); intros.
      eapply is_lim_seq_ext; try (apply H5).
      intros; simpl.
      unfold rvsum, rvscale, Rdiv.
      rewrite Rmult_comm.
      f_equal.
      apply sum_n_ext.
      intros.
      simpl; field.
      apply Rgt_not_eq.
      apply H.
    - intros n.
      specialize (HC n).
      assert (isfe:IsFiniteExpectation Prts (X (S n)))
        by now apply IsFiniteExpectation_rvsqr_lower.
      generalize (Condexp_scale Prts (filt_sub n) (/ b (S n)) (X (S n))); intros.
      apply almostR2_prob_space_sa_sub_lift in H3.
      revert HC; apply almost_impl.
      revert H3; apply almost_impl.
      apply all_almost.
      intros x ??.
      rewrite H3.
      unfold Rbar_rvmult.
      rewrite H4.
      now rewrite Rbar_mult_0_r.
  Qed.

  Lemma independent_expectation_prod_nneg (X Y : Ts -> R)
        {rvx : RandomVariable dom borel_sa X}
        {rvy : RandomVariable dom borel_sa Y}        
        {nnx : NonnegativeFunction X}
        {nny : NonnegativeFunction Y} :
    independent_rvs Prts borel_sa borel_sa X Y ->
    ex_Rbar_mult (NonnegExpectation X) (NonnegExpectation Y) ->
    NonnegExpectation (rvmult X Y) = Rbar_mult (NonnegExpectation X) (NonnegExpectation Y).
  Proof.
    intros.
    assert (forall n, RandomVariable dom borel_sa (simple_approx X n)).
    {
      intros.
      apply simple_approx_rv; trivial.
      now apply Real_Rbar_rv.
    }
    assert (forall n, RandomVariable dom borel_sa (simple_approx Y n)).
    {
      intros.
      apply simple_approx_rv; trivial.
      now apply Real_Rbar_rv.
    }
    assert (forall n, FiniteRangeFunction (simple_approx X n)).
    {
      intros.
      apply simple_approx_frf.
    }
    assert (forall n, FiniteRangeFunction (simple_approx Y n)).
    {
      intros.
      apply simple_approx_frf.
    }
    assert (forall n, NonnegativeFunction (simple_approx X n)) by (intros n x; apply simple_approx_pos).
    assert (forall n, NonnegativeFunction (simple_approx Y n)) by (intros n x; apply simple_approx_pos).    
    assert (forall n, NonnegativeFunction (rvmult (simple_approx X n) (simple_approx Y n))).
    {
      intros.
      apply NonNegMult; intro x; apply simple_approx_pos.
   }
    assert (forall n,
               real (NonnegExpectation (rvmult (simple_approx X n) (simple_approx Y n))) =
               real (NonnegExpectation (simple_approx X n)) *
               real (NonnegExpectation (simple_approx Y n))).
    {
      intros.
      do 3 erewrite frf_NonnegExpectation.
      simpl.
      apply SimpleExpectation_indep.
      now apply (simple_approx_independent' _ _ _ _).
    }
    generalize (monotone_convergence X (simple_approx X) _ _ _ (fun n => simple_approx_pos _ n)); intros.
    generalize (monotone_convergence Y (simple_approx Y) _ _ _ (fun n => simple_approx_pos _ n)); intros.    
    generalize (monotone_convergence (rvmult X Y) (fun n => rvmult (simple_approx X n) (simple_approx Y n)) _ _ _ H5); intros.
    rewrite <- H7, <- H8, <- H9.
    - rewrite Lim_seq_ext with
          (v := fun n =>
               NonnegExpectation (simple_approx X n) *
               NonnegExpectation (simple_approx Y n)); trivial.
      rewrite Lim_seq_mult; trivial.
      + apply ex_lim_seq_incr.
        intros.
        generalize (NonnegExpectation_le (simple_approx X n) (simple_approx X (S n))); intros.
        erewrite <- (simple_expectation_real (simple_approx X n)) in H10.
        erewrite <- (simple_expectation_real (simple_approx X (S n))) in H10.
        simpl in H10.
        apply H10.
        intro x.
        now apply simple_approx_increasing.
      + apply ex_lim_seq_incr.
        intros.
        generalize (NonnegExpectation_le (simple_approx Y n) (simple_approx Y (S n))); intros.
        erewrite <- (simple_expectation_real (simple_approx Y n)) in H10.
        erewrite <- (simple_expectation_real (simple_approx Y (S n))) in H10.
        simpl in H10.
        apply H10.
        intro x.
        now apply simple_approx_increasing.
      + replace  (Lim_seq
                    (fun n : nat => NonnegExpectation (simple_approx (fun x : Ts => X x) n)))
          with
            (NonnegExpectation X).
        * replace  (Lim_seq
                      (fun n : nat => NonnegExpectation (simple_approx (fun x : Ts => Y x) n)))
            with
              (NonnegExpectation Y); trivial.
          rewrite <- NonnegExpectation_simple_approx; trivial.
        * rewrite <- NonnegExpectation_simple_approx; trivial.
    - intros n x.
      unfold rvmult.
      apply Rmult_le_compat; try apply simple_approx_pos.
      + now apply (simple_approx_le X).
      + now apply (simple_approx_le Y).
    - intros n x.
      unfold rvmult.
      apply Rmult_le_compat; try apply simple_approx_pos.
      + now apply simple_approx_increasing.
      + now apply simple_approx_increasing.
    - intros.
      apply simple_expectation_real; typeclasses eauto.
    - intros.
      unfold rvmult.
      apply is_lim_seq_mult'.
      + now apply (simple_approx_lim_seq X).
      + now apply (simple_approx_lim_seq Y).
    - intros n x.
      now apply (simple_approx_le Y).
    - intros n x.
      now apply simple_approx_increasing.
    - intros.
      apply simple_expectation_real; typeclasses eauto.
    - intro.
      now apply (simple_approx_lim_seq Y).
    - intros n x.
      now apply (simple_approx_le X).
    - intros n x.
      now apply simple_approx_increasing.
    - intros.
      apply simple_expectation_real; typeclasses eauto.
    - intro.
      now apply (simple_approx_lim_seq X).
  Qed.

   Lemma pos_parts_mult (X Y : Ts -> R) :
     rv_eq (fun x => nonneg (pos_fun_part (rvmult X Y) x))
           (rvplus (rvmult (pos_fun_part X) (pos_fun_part Y))
                   (rvmult (neg_fun_part X) (neg_fun_part Y))).
     Proof.
       intro x.
       rv_unfold.
       generalize (rv_pos_neg_id X); intros.
       generalize (rv_pos_neg_id Y); intros.       
       simpl.
       rewrite H at 1.
       rewrite Rmult_comm.
       rewrite H0 at 1.
       rv_unfold.
       simpl.
       unfold Rmax.
       match_destr; match_destr; match_destr; match_destr; match_destr; try lra.
       - assert (0 < - X x) by lra.
         assert (0 < - Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
       - assert (0 < X x) by lra.
         assert (0 < Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
       - assert (0 < X x) by lra.
         assert (0 < - Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
       - assert (0 < - X x) by lra.
         assert (0 < Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
    Qed.

   Lemma neg_parts_mult (X Y : Ts -> R) :
     rv_eq (fun x => nonneg (neg_fun_part (rvmult X Y) x))
           (rvplus (rvmult (pos_fun_part X) (neg_fun_part Y))
                   (rvmult (neg_fun_part X) (pos_fun_part Y))).
     Proof.
       intro x.
       rv_unfold.
       generalize (rv_pos_neg_id X); intros.
       generalize (rv_pos_neg_id Y); intros.       
       simpl.
       rewrite H at 1.
       rewrite Rmult_comm.
       rewrite H0 at 1.
       rv_unfold.
       simpl.
       unfold Rmax.
       match_destr; match_destr; match_destr; match_destr; match_destr; try lra.
       - assert (0 < - X x) by lra.
         assert (0 < Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
       - assert (0 < X x) by lra.
         assert (0 < - Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
       - assert (0 < - X x) by lra.
         assert (0 < - Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
       - assert (0 < X x) by lra.
         assert (0 < Y x) by lra.
         generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
         lra.
    Qed.

   Lemma Finite_expectation_pos_neg_parts (X : Ts -> R) 
         {rvx : RandomVariable dom borel_sa X}
         {isfe : IsFiniteExpectation Prts X} :
     FiniteExpectation Prts X = NonnegExpectation(pos_fun_part X) -
                                NonnegExpectation(neg_fun_part X).
   Proof.
     unfold FiniteExpectation, proj1_sig.
     match_destr.
     unfold Expectation in e.
     rewrite <- (Expectation_pos_part_finite _ X) in e.
     rewrite <- (Expectation_neg_part_finite _ X) in e.     
     simpl in e.
     invcs e.
     simpl.
     ring.
  Qed.

  Lemma independent_expectation_prod (X Y : Ts -> R)
        {rvx : RandomVariable dom borel_sa X}
        {rvy : RandomVariable dom borel_sa Y}        
        {isfex : IsFiniteExpectation Prts X}
        {isfey : IsFiniteExpectation Prts Y}
        {isfexy : IsFiniteExpectation Prts (rvmult X Y)}:    
    independent_rvs Prts borel_sa borel_sa X Y ->
    FiniteExpectation Prts (rvmult X Y) = FiniteExpectation Prts X * FiniteExpectation Prts Y.
  Proof.
    intros.
    generalize (independent_expectation_prod_nneg (pos_fun_part X) (pos_fun_part Y)
                                                  (indep_pos_part X Y H)); intros.
    generalize (independent_expectation_prod_nneg (neg_fun_part X) (neg_fun_part Y)
                                                  (indep_neg_part X Y H)); intros.
    generalize (independent_expectation_prod_nneg (pos_fun_part X) (neg_fun_part Y)
                                                  (indep_pos_neg_part X Y H)); intros.
    generalize (independent_expectation_prod_nneg (neg_fun_part X) (pos_fun_part Y)
                                                  (indep_neg_pos_part X Y H)); intros.
    rewrite  Finite_expectation_pos_neg_parts; try typeclasses eauto.
    rewrite  Finite_expectation_pos_neg_parts; try typeclasses eauto.
    rewrite  Finite_expectation_pos_neg_parts; try typeclasses eauto.
    generalize (pos_parts_mult X Y); intros.
    generalize (neg_parts_mult X Y); intros.    
    rewrite (NonnegExpectation_ext _ _ H4).
    rewrite (NonnegExpectation_ext _ _ H5).
    rewrite NonnegExpectation_sum; try typeclasses eauto.
    rewrite NonnegExpectation_sum; try typeclasses eauto.
    rewrite H0, H1, H2, H3.
    - rewrite <- (Expectation_pos_part_finite _ X); trivial.
      rewrite <- (Expectation_pos_part_finite _ Y); trivial.
      rewrite <- (Expectation_neg_part_finite _ X); trivial.
      rewrite <- (Expectation_neg_part_finite _ Y); trivial.
      simpl.
      ring.
    - rewrite <- (Expectation_neg_part_finite _ X); trivial.
      rewrite <- (Expectation_pos_part_finite _ Y); trivial.
      now simpl.
    - rewrite <- (Expectation_pos_part_finite _ X); trivial.
      rewrite <- (Expectation_neg_part_finite _ Y); trivial.             
      now simpl.
    - rewrite <- (Expectation_neg_part_finite _ X); trivial.
      rewrite <- (Expectation_neg_part_finite _ Y); trivial.
      now simpl.
    - rewrite <- (Expectation_pos_part_finite _ X); trivial.
      rewrite <- (Expectation_pos_part_finite _ Y); trivial.             
      now simpl.
   Qed.

    Lemma ident_distr_finite_exp_eq (X Y:Ts->R)
          {isfex : IsFiniteExpectation Prts X}
          {isfey : IsFiniteExpectation Prts Y}          
          {rvx  : RandomVariable dom borel_sa X}
          {rvy  : RandomVariable dom borel_sa Y} :
    identically_distributed_rvs Prts borel_sa X Y ->
    FiniteExpectation Prts X = FiniteExpectation Prts Y.
   Proof.
     intros.
     rewrite Finite_expectation_pos_neg_parts; trivial.
     rewrite Finite_expectation_pos_neg_parts; trivial.
     rewrite (ident_distr_nnexp_eq Prts (pos_fun_part X) (pos_fun_part Y)
                                   (identially_distributed_pos_part X Y H)).
     now rewrite (ident_distr_nnexp_eq Prts (neg_fun_part X) (neg_fun_part Y)
                                   (identially_distributed_neg_part X Y H)).
   Qed.

  Instance rv_collection (X : nat -> Ts -> R)
           {rv : forall n, RandomVariable dom borel_sa (X n)} :
    forall (n:nat), RandomVariable dom (const borel_sa n) (X n).
  Proof.
    intros.
    now unfold const.
  Qed.
  
  Lemma independent_sas_split1 (sas : nat -> SigmaAlgebra Ts) 
        {sub:IsSubAlgebras dom sas}
        (fsub: forall n, sa_sub (filtrate_sa sas n) dom) :
    independent_sa_collection Prts sas ->
    forall n,
      independent_sas Prts (fsub n) (is_sub_algebras (S n)).
  Proof.
    
    Admitted.

  Lemma event_sa_sub_pf_irrel (dom2 : SigmaAlgebra Ts) (sub1 sub2 : sa_sub dom2 dom) (x : event dom2) :
    event_equiv (event_sa_sub sub1 x) (event_sa_sub sub2 x).
  Proof.
    intros ?; reflexivity.
  Qed.
        
  Lemma filtration_history_pullback_independent (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)} :
    independent_rv_collection Prts (const borel_sa) X ->
    forall n, independent_sas Prts (filtration_history_sa_sub X n) (pullback_rv_sub dom borel_sa (X (S n)) _ ).
  Proof.
    intros.
    assert (independent_sa_collection Prts (fun n : nat => pullback_sa borel_sa (X n))).
    {
      apply independent_rv_collection_sas.
      unfold const in H.
      revert H.
      now apply independent_rv_collection_proper.
    }
    generalize (filtration_history_sa_sub X); intros fsub.
    generalize (independent_sas_split1 _ fsub H0 n); intros.
    unfold is_sub_algebras in H1.
    unfold independent_sas in *.
    intros.
    generalize (H1 A B).
    apply independent_events_proper; try reflexivity.
    apply event_sa_sub_pf_irrel.
  Qed.

  Lemma independent_sum (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)} :
    independent_rv_collection Prts (const borel_sa) X ->
    forall n,
      independent_rvs Prts borel_sa borel_sa (rvsum X n) (X (S n)).
  Proof.
    intros.
    apply independent_rv_sas.
    generalize (filtration_history_pullback_independent X H); intros.
    assert (RandomVariable (filtration_history_sa X n) borel_sa (rvsum X n)).
    {
      apply rvsum_rv_loc.
      intros.
      now apply filtration_history_sa_le_rv.
    }
    generalize (pullback_rv_sub _ _ _ H1); intros.
    specialize (H0 n).
    revert H0.
    apply independent_sas_sub_proper; trivial.
    apply sa_equiv_sub.
    apply sa_equiv_equiv.
  Qed.

  Lemma independent_sum_prod (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)} 
        {isl2 : forall n, IsLp Prts 2 (X n)} 
        {isfe : forall n j, IsFiniteExpectation Prts (rvmult (rvsum X n) (X (n + S j)%nat))} :
    pairwise_independent_rv_collection Prts (const borel_sa) X ->
    forall n j,
        FiniteExpectation Prts (rvmult (rvsum X n) (X (n + S j)%nat)) =
        FiniteExpectation Prts (rvsum X n) * FiniteExpectation Prts (X (n + S j)%nat).
  Proof.
    unfold pairwise_independent_rv_collection.
    intro H.
    unfold const in H.

    induction n.
    - intros.
      assert (rv_eq (rvsum X 0%nat) (X 0%nat)).
      {
        intro x.
        unfold rvsum.
        now rewrite sum_O.
      }
      rewrite (FiniteExpectation_ext _ _ _ H0).
      assert (rv_eq (rvmult (rvsum X 0%nat) (X (0 + S j)%nat))
                    (rvmult (X 0%nat) (X (0 + S j)%nat))).
      {
        intro x.
        unfold rvmult, rvsum.
        now rewrite sum_O.
      }
      rewrite (FiniteExpectation_ext _ _ _ H1).
      apply independent_expectation_prod with (rvx := rv 0%nat) (rvy := rv (0 + S j)%nat).
      specialize (H (0%nat) (0 + S j)%nat).
      cut_to H; try lia.
      revert H.
      now apply independent_rvs_proper.
    - intro j.
      assert (rv_eq (rvsum X (S n))
                    (rvplus (rvsum X n) (X (S n)))).
      {
        intro x.
        unfold rvsum, rvplus.
        now rewrite sum_Sn.
      }
      rewrite (FiniteExpectation_ext _ _ _ H0).
      assert (rv_eq (rvmult (rvsum X (S n)) (X (S n + S j)%nat))
                    (rvplus
                       (rvmult (rvsum X n) (X (S n + S j)%nat))
                       (rvmult (X (S n)) (X (S n + S j)%nat)))).
      {
        intro x.
        unfold rvmult, rvsum, rvplus.
        rewrite sum_Sn.
        unfold plus; simpl.
        ring.
      }
      assert (IsFiniteExpectation Prts
            (rvplus (rvmult (rvsum X n) (X (S n + S j)%nat))
                    (rvmult (X (S n)) (X (S n + S j)%nat)))).
      {
        apply IsFiniteExpectation_plus; try typeclasses eauto.
        generalize (isfe n (S j)); intros.
        revert H2.
        apply IsFiniteExpectation_proper.
        intro x.
        f_equal.
        f_equal.
        lia.
      }        
      rewrite (FiniteExpectation_ext _ _ _ H1).      
      rewrite FiniteExpectation_plus.
      erewrite FiniteExpectation_plus'; try typeclasses eauto.
      ring_simplify.
      specialize (IHn (S j)).
      assert (rv_eq (X (n + S (S j))%nat)
                    (X (S n + S j)%nat)).
      {
        intro x.
        f_equal.
        lia.
      }
      rewrite (FiniteExpectation_ext _ _ _ H3) in IHn.
      assert (rv_eq (rvmult (rvsum X n) (X (n + S (S j))%nat))
                    (rvmult (rvsum X n) (X (S n + S j))%nat)).
      {
        intro x.
        f_equal.
        f_equal.
        lia.
      }
      erewrite (FiniteExpectation_ext _ _ _ H4) in IHn.      
      rewrite IHn.
      assert (forall n, IsFiniteExpectation Prts (X n)) by typeclasses eauto.
      rewrite independent_expectation_prod with (rvx := rv (S n)) (rvy := rv (S n + S j)%nat) (isfex := H5 (S n)) (isfey := (H5 (S n + S j)%nat)).
      + f_equal; f_equal; apply FiniteExpectation_pf_irrel.
      + specialize (H (S n) (S n + S j)%nat).
        cut_to H; try lia.
        revert H.
        now apply independent_rvs_proper.
        Unshelve.
        specialize (isfe n (S j)).
        revert isfe.
        apply IsFiniteExpectation_proper.
        intro x.
        f_equal.
        f_equal.
        lia.
  Qed.
      
  Lemma independent_sum_variance (X : nat -> Ts -> R) (n:nat)
        {rv: forall n, RandomVariable dom borel_sa (X n)}
        {isl2 : forall n, IsLp Prts 2 (X n)} 
        {isfe : forall n, IsFiniteExpectation Prts (rvsqr (rvsum X n))}:
    pairwise_independent_rv_collection Prts (const borel_sa) X ->
    FiniteExpectation Prts (rvsqr (rvsum X n)) -
    Rsqr (FiniteExpectation Prts (rvsum X n)) =
    sum_n (fun n => FiniteExpectation Prts (rvsqr (X n))
                    - Rsqr (FiniteExpectation Prts (X n))) n.
  Proof.
    intros.
    induction n.
    - rewrite sum_O.
      assert (rv_eq (rvsum X 0%nat) (X 0%nat)).
      {
        intro x.
        unfold rvsum.
        now rewrite sum_O.
      }
      assert (rv_eq (rvsqr (rvsum X 0)) (rvsqr (X 0%nat))).
      {
        intro x.
        unfold rvsqr, rvsum.
        now rewrite sum_O.
      }
      rewrite (FiniteExpectation_ext _ _ _ H1).
      now rewrite (FiniteExpectation_ext _ _ _ H0).
    - assert (rv_eq (rvsum X (S n))
                    (rvplus (rvsum X n) (X (S n)))).
      {
        intro x.
        unfold rvsum, rvplus.
        rewrite sum_Sn.
        now unfold plus; simpl.
      }
      assert (rv_eq (rvsqr (rvsum X (S n)))
                    (rvplus (rvsqr (rvsum X n))
                            (rvplus (rvscale 2 (rvmult (rvsum X n) (X (S n))))
                                    (rvsqr (X (S n)))))).
      {
        intro x.
        unfold rvsum, rvsqr, rvmult, rvplus, rvscale.
        rewrite sum_Sn.
        unfold plus; simpl.
        unfold Rsqr.
        ring.
      }
      rewrite sum_Sn.
      unfold plus; simpl.
      rewrite <- IHn.
      rewrite (FiniteExpectation_ext _ _ _ H0).
      rewrite FiniteExpectation_plus.
      rewrite (FiniteExpectation_ext_alt _ _ _ H1).
      symmetry.
      assert (RandomVariable dom borel_sa (rvsum X n)) by typeclasses eauto.
      assert (IsFiniteExpectation Prts (rvmult (rvsum X n) (X (S n)))).
      {
        apply is_L2_mult_finite; try typeclasses eauto.
        apply IsLp_sum; trivial.
        lra.
      }
      erewrite FiniteExpectation_plus'; try typeclasses eauto.
      + rewrite FiniteExpectation_plus.
        * rewrite FiniteExpectation_scale.
          replace (FiniteExpectation Prts (rvmult (rvsum X n) (X (S n)))) with
              (FiniteExpectation Prts (rvsum X n) *
               FiniteExpectation Prts (X (S n))).
          -- unfold Rsqr; ring.
          -- assert (forall n j : nat,
                        IsFiniteExpectation Prts (rvmult (rvsum X n) (X (n + S j)%nat))).
             {
               intros.
               generalize (isfe_Sum1_r_from_crossmult X (0%nat)); intros.
               specialize (H4 (n0 + S j)%nat n0).
               revert H4.
               apply IsFiniteExpectation_proper.
               intro x.
               unfold rvmult.
               f_equal.
               unfold rvsum.
               apply sum_n_ext.
               intros.
               f_equal; lia.
             }
             generalize (independent_sum_prod X); intros.
             cut_to H5; trivial.
             specialize (H5 n 0%nat).
             assert (rv_eq (X (n + 1)%nat) (X (S n))).
             {
               intro x.
               f_equal; lia.
             }
             rewrite (FiniteExpectation_ext _ _ _ H6) in H5.
             assert (rv_eq  (rvmult (rvsum X n) (X (n + 1)%nat))
                            (rvmult (rvsum X n) (X (S n)))).
             {
               intro x.
               f_equal; f_equal; lia.
             }
             rewrite (FiniteExpectation_ext _ _ _ H7) in H5.                
             now rewrite H5.
  Qed.

  Lemma filtration_history_indep (X : nat -> Ts -> R) (n : nat) (P : pre_event Ts) (dec : dec_pre_event P)
        {rv : forall n, RandomVariable dom borel_sa (X n)} 
        {rvdec : RandomVariable dom borel_sa (EventIndicator dec)} :
    independent_rv_collection Prts (const borel_sa) X ->    
    sa_sigma (filtration_history_sa X n) P ->
    independent_rvs Prts borel_sa borel_sa (X (S n)) (EventIndicator dec).
  Proof.
    intros.
    apply independent_rvs_symm.
    apply independent_rv_sas.
    generalize (filtration_history_pullback_independent X H n); intros.
    assert (RandomVariable (filtration_history_sa X n) borel_sa (EventIndicator dec)) by
        now apply EventIndicator_pre_rv.
    generalize (pullback_rv_sub _ _ _ H2); intros.
    revert H1.
    apply independent_sas_sub_proper; trivial.
    apply sa_equiv_sub.
    apply sa_equiv_equiv.
  Qed.

  Existing Instance IsFiniteExpectation_simple.

  Lemma is_condexp_indep (X : nat -> Ts -> R) (n : nat)
        {rv : forall n, RandomVariable dom borel_sa (X n)} 
        (isfe : IsFiniteExpectation Prts (X (S n))) :
    independent_rv_collection Prts (const borel_sa) X ->
    almostR2 Prts eq
             (ConditionalExpectation Prts (filtration_history_sa_sub X n) (X (S n)))
             (const (FiniteExpectation Prts (X (S n)))).
    Proof.
      intros.
      apply almost_prob_space_sa_sub_lift with (sub := (filtration_history_sa_sub X n)).
      apply (is_conditional_expectation_unique 
               Prts
               (filtration_history_sa_sub X n)
               (X (S n))
               (ConditionalExpectation Prts (filtration_history_sa_sub X n) (X (S n)))
               (const (FiniteExpectation Prts (X (S n))))).
      - now apply Condexp_cond_exp.
      - unfold is_conditional_expectation; intros.
        assert (rv_eq
                  (Rbar_rvmult (fun x : Ts => const (FiniteExpectation Prts (X (S n))) x)
                               (fun x : Ts => EventIndicator dec x))
                  (fun x => Rbar.Finite 
                              ((rvmult (const (FiniteExpectation Prts (X (S n))))
                                       (EventIndicator dec)) x))).
        + intros x.
          now unfold Rbar_rvmult, rvmult; simpl.
        + rewrite H1.
          rewrite <- RbarExpectation.Expectation_Rbar_Expectation.
          assert (RandomVariable dom borel_sa (EventIndicator dec)).
          {
            apply (RandomVariable_sa_sub (filtration_history_sa_sub X n)).
            now apply EventIndicator_pre_rv.
          }
          assert (IsFiniteExpectation Prts (rvmult (X (S n)) (EventIndicator dec))).
          {
            apply IsFiniteExpectation_indicator; trivial.
            eapply (@filtration_history_is_sub_algebra _ _ _ X dom _).
            eauto.
          }
          assert (IsFiniteExpectation Prts (rvmult (const (FiniteExpectation Prts (X (S n)))) (EventIndicator dec))).
          {
            apply IsFiniteExpectation_indicator; trivial; try typeclasses eauto.
            eapply (@filtration_history_is_sub_algebra _ _ _ X dom _).
            eauto.
          }
          rewrite FiniteExpectation_Expectation with (isfe0 := H3).
          rewrite FiniteExpectation_Expectation with (isfe0 := H4).
          f_equal.
          erewrite independent_expectation_prod.
          * erewrite independent_expectation_prod.
            -- apply Rbar_finite_eq.
               f_equal.
               now rewrite FiniteExpectation_const.
            -- apply independent_rvs_const_l.
          * now apply filtration_history_indep.
     Qed.

  Lemma Ash_6_2_2_indep_0 (X : nat -> Ts -> R)
        {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
        {isfe : forall k, IsFiniteExpectation Prts (X k)}
        {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))}
        {isfes:forall n, IsFiniteExpectation Prts (rvsqr (rvscale (/ (INR (S n))) (X n)))} :
    (forall i, FiniteExpectation Prts (X i) = 0) ->
    independent_rv_collection Prts (const borel_sa) X ->
    ex_series (fun n => FiniteExpectation Prts (rvsqr (rvscale (/ INR (S n)) (X n)))) ->
    almost Prts (fun (x : Ts) => is_lim_seq (fun n => (rvscale (/ INR (S n)) (rvsum X n)) x) 0). 
  Proof.
    intros.
    apply (Ash_6_2_2 X (fun n => INR (S n))); trivial.
    - intros.
      generalize (is_condexp_indep X n (isfe (S n)) H0); intros.
      assert (rv_eq (fun x:Ts => (const 0 x))
                    (const (FiniteExpectation Prts (X (S n))))).
      {
        intro x.
        unfold const.
        now rewrite H.
      }
      revert H2.
      unfold almostR2.
      apply almost_impl, all_almost; intros.
      unfold impl.
      now rewrite H3.
    - intros.
      split.
      + apply lt_0_INR; lia.
      + apply le_INR; lia.
    - apply is_lim_seq_spec.
      unfold is_lim_seq'.
      intros.
      exists (Z.to_nat(up M)).
      intros.
      destruct (archimed M).
      apply le_INR in H2.
      destruct (Rge_dec M 0).
      + rewrite INR_up_pos in H2; trivial.
        assert (n < S n)%nat by lia.
        apply lt_INR in H5.
        lra.
      + generalize (pos_INR (S n)); intros.
        lra.
   Qed.
      
  Lemma NonnegExpectation_EventIndicator
        {P : event dom}
        (dec : forall x : Ts, {P x} + {~ P x}): 
      NonnegExpectation (EventIndicator dec) = ps_P P.
  Proof.
    generalize (Expectation_EventIndicator dec); intros.
    rewrite Expectation_pos_pofrf with (nnf := EventIndicator_pos dec) in H.
    now inversion H.
  Qed.

  Lemma sum_Rbar_n_le (f g : nat -> Rbar) (n : nat) :
    (forall n, Rbar_le 0 (f n)) ->
    (forall n, Rbar_le 0 (g n)) ->    
    (forall n, Rbar_le (f n) (g n)) ->
    Rbar_le (sum_Rbar_n f n) (sum_Rbar_n g n).
  Proof.
    intros.
    induction n.
    - simpl.
      lra.
    - rewrite sum_Rbar_n_Sn; trivial.
      rewrite sum_Rbar_n_Sn; trivial.
      now apply Rbar_plus_le_compat.
   Qed.

  Lemma sum_Rbar_n_pos (f : nat -> Rbar) :
    (forall n, Rbar_le 0 (f n)) ->
    forall n, Rbar_le 0 (sum_Rbar_n f n).
  Proof.
    intros.
    induction n.
    - simpl.
      lra.
    - rewrite sum_Rbar_n_Sn; trivial.
      replace (Rbar.Finite 0) with (Rbar_plus (Rbar.Finite 0) (Rbar.Finite 0)).
      + now apply Rbar_plus_le_compat.
      + now rewrite Rbar_plus_0_r.
   Qed.

  Lemma sum_disj_event_ind (Y : Ts -> R) 
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    forall x n,
      sum_n
        (fun x0 : nat =>
           EventIndicator
             (classic_dec (event_inter (event_ge dom Y (INR x0)) (event_lt dom Y (INR x0 + 1)) )) x) n =
      EventIndicator (classic_dec (event_lt dom Y (INR n + 1))) x.
  Proof.
    induction n.
    - rewrite sum_O.
      unfold EventIndicator, event_inter, pre_event_inter.
      match_destr; match_destr; simpl in *.
      + lra.
      + unfold NonnegativeFunction in nny.
        intuition.
    - rewrite sum_Sn.
      rewrite IHn.
      unfold EventIndicator, event_inter, pre_event_inter.
      replace (S n) with (n+1)%nat by lia.
      match_destr; match_destr; match_destr; unfold plus; simpl in *; try lra.
      + replace (INR n + 1) with (INR (n+1)) in e; try lra.
        replace (n+1)%nat with (S n) by lia.
        now rewrite S_INR.
      + replace (INR n + 1) with (INR (n+1)) in e; try lra.
        replace (n+1)%nat with (S n) by lia.
        now rewrite S_INR.
      + replace (INR n + 1) with (INR (n+1)) in n0; try lra.
        replace (n+1)%nat with (S n) by lia.
        now rewrite S_INR.
   Qed.

  Lemma sum_disj_event_ind_mult (Y : Ts -> R) 
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    forall x n,
      sum_n
        (fun x0 : nat =>
           (Y x) *
           (EventIndicator
             (classic_dec (event_inter (event_ge dom Y (INR x0)) (event_lt dom Y (INR x0 + 1)) )) x))
             n =
      (Y x)* (EventIndicator (classic_dec (event_lt dom Y (INR n + 1))) x).
   Proof.
     induction n.
     - rewrite sum_O.
       unfold EventIndicator, event_inter, pre_event_inter.
       match_destr; match_destr; simpl in *.
       + lra.
       + unfold NonnegativeFunction in nny.
         intuition.
     - rewrite sum_Sn.
       rewrite IHn.
         unfold EventIndicator, event_inter, pre_event_inter.
      replace (S n) with (n+1)%nat by lia.
      match_destr; match_destr; match_destr; unfold plus; simpl in *; try lra.
      + replace (INR n + 1) with (INR (n+1)) in e; try lra.
        replace (n+1)%nat with (S n) by lia.
        now rewrite S_INR.
      + replace (INR n + 1) with (INR (n+1)) in e; try lra.
        replace (n+1)%nat with (S n) by lia.
        now rewrite S_INR.
      + replace (INR n + 1) with (INR (n+1)) in n0; try lra.
        replace (n+1)%nat with (S n) by lia.
        now rewrite S_INR.
   Qed.

  (* move this *)
  Lemma ForallOrdPairs_app_inv {A} {P} (l1 l2:list A) :
    ForallOrdPairs P (l1 ++ l2) ->
    ForallOrdPairs P l1 /\
      ForallOrdPairs P l2 /\
      Forall (fun a1 => (Forall (fun b1 => P a1 b1) l2)) l1.
  Proof.
    induction l1; simpl; intros.
    - repeat split; trivial.
      constructor.
    - invcs H.
      destruct (IHl1 H3) as [? [??]].
      repeat split; trivial.
      + constructor; trivial.
        apply Forall_app_inv in H2; tauto.
      + constructor; trivial.
        apply Forall_app_inv in H2; tauto.
  Qed.        
    
  Lemma ps_disjoint_collection_take_union {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (E : nat -> event σ) (n : nat) :
    ForallOrdPairs event_disjoint (collection_take E (S n)) ->
    sum_n (fun k => ps_P (E k)) n = ps_P (list_union (collection_take E (S n))).
  Proof.
    induction n; unfold collection_take; intros disj.
    - simpl; now rewrite sum_O, list_union_singleton.
    - rewrite seq_Sn in *.
      rewrite sum_Sn, IHn.
      + rewrite map_app.
        rewrite list_union_app.
        unfold plus; simpl.
        rewrite list_union_singleton.
        rewrite ps_disjoint_union; trivial.
        intros ? [? [??]] inn2; simpl in *.
        destruct H; subst.
        * invcs disj.
          rewrite Forall_forall in H2.
          eelim H2; eauto.
          apply in_map.
          apply in_app_iff; simpl; tauto.
        * apply in_map_iff in H.
          destruct H as [? [??]]; subst.
          invcs disj.
          rewrite map_app in H4.
          generalize (ForallOrdPairs_app_in H4)
          ; intros HH.
          eapply (HH (E x1) (E (S n))); simpl; eauto.
          now apply in_map.
      + rewrite map_app in disj.
        apply ForallOrdPairs_app_inv in disj.
        tauto.
  Qed.

  Lemma ps_partition_intervals (Y : Ts -> R)
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    forall n : nat,
      ps_P (list_union (collection_take (fun k : nat => event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1))) (S n))) =
      ps_P (event_lt dom Y (INR n + 1)).
   Proof.
        intros.
        rewrite <- S_INR.
        generalize (S n); clear n; intros n.
        apply ps_proper
        ; intros ?; simpl; split.
        * intros [? [??]].
          apply in_map_iff in H.
          destruct H as [? [??]]; subst.
          destruct H0; simpl in *.
          apply in_seq in H1.
          eapply Rlt_le_trans; try apply H0.
          rewrite <- S_INR.
          apply le_INR.
          lia.
        * intros.
          eexists; split.
          -- apply in_map.
             apply in_seq.
             assert (Z.to_nat (up (Y x))-1 < n)%nat.
             {
               destruct (archimed (Y x)).
               apply INR_lt.
               specialize (nny x).
               rewrite minus_INR.
               - simpl.
                 rewrite INR_up_pos by lra.
                 lra.
               - cut (0 < Z.to_nat (up (Y x)))%nat; try lia.
                 apply INR_lt.
                 rewrite INR_up_pos by lra.
                 simpl.
                 lra.
             }
             simpl.
             split; try apply H0.
             lia.
          -- { destruct (archimed (Y x)).
               split; simpl.
               - specialize (nny x).
                 rewrite minus_INR.
                 + simpl.
                   rewrite INR_up_pos by lra.
                   lra.
                 + cut (0 < Z.to_nat (up (Y x)))%nat; try lia.
                   apply INR_lt.
                   rewrite INR_up_pos by lra.
                   simpl.
                   lra.
               - specialize (nny x).
                 rewrite minus_INR.
                 + simpl.
                   rewrite INR_up_pos by lra.
                   lra.
                 + cut (0 < Z.to_nat (up (Y x)))%nat; try lia.
                   apply INR_lt.
                   rewrite INR_up_pos by lra.
                   simpl.
                   lra.
             }
     Qed.

  Lemma Ash_6_2_4_partitioN (Y : Ts -> R)
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    Lim_seq (fun n => sum_n
                        (fun k => (ps_P (event_inter (event_ge dom Y (INR k))
                                                     (event_lt dom Y (INR k + 1)))))
                        n) = 1.
  Proof.
    erewrite Lim_seq_ext
    ; [| intros; rewrite ps_disjoint_collection_take_union; [reflexivity |]].
    - rewrite (Lim_seq_ext _
                           (fun n => ps_P (event_lt dom Y (INR n + 1)))).
      + rewrite lim_ascending.
        * rewrite (ps_proper _ Ω).
          -- now rewrite ps_all.
          -- split; intros; simpl; [now red |].
             destruct (archimed (Y x)).
             exists (Z.to_nat (up (Y x))).
             rewrite INR_up_pos; try lra.
             specialize (nny x).
             lra.
        * intros ??.
          rewrite S_INR; simpl; lra.
      + now apply ps_partition_intervals.
    - apply collection_take_preserves_disjoint.
      intros ????[??][??]; simpl in *.
      apply H.
      apply le_antisym.
      + assert (INR n1 < INR (S n2)) by (rewrite S_INR; lra).
        apply INR_lt in H4.
        lia.
      + assert (INR n2 < INR (S n1)) by (rewrite S_INR; lra).
        apply INR_lt in H4.
        lia.
  Qed.        
    
 Lemma partition_expectation0 (Y : Ts -> R)
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
   NonnegExpectation Y =
   ELim_seq
     (fun n : nat =>
        NonnegExpectation
          (rvmult Y 
                  (EventIndicator
                     (classic_dec (event_lt dom Y (INR n + 1)) )))).
   Proof.
     generalize (RbarExpectation.Rbar_monotone_convergence 
                   Y 
                   (fun n => rvmult Y
                                    (EventIndicator
                                       (classic_dec (event_lt dom Y (INR n + 1)) )))); intros.
     assert (RandomVariable dom Rbar_borel_sa (fun x : Ts => Y x)) by typeclasses eauto.
     assert (Rbar_NonnegativeFunction Y) by apply nny.
     specialize (H H0 H1).
     rewrite RbarExpectation.NNExpectation_Rbar_NNExpectation.
     rewrite ELim_seq_ext with
         (v := (fun n : nat =>
         RbarExpectation.Rbar_NonnegExpectation
           (fun omega : Ts =>
            rvmult Y (EventIndicator (classic_dec (event_lt dom Y (INR n + 1)))) omega))).
     - rewrite H.
       + apply  RbarExpectation.Rbar_NonnegExpectation_ext.
         reflexivity.
       + intros.
         typeclasses eauto.
       + intros n x.
         specialize (nny x).
         unfold rvmult, EventIndicator; simpl.
         match_destr; lra.
       + intros n x.
         unfold rvmult, EventIndicator.
         match_destr; match_destr; simpl; try lra.
         * unfold event_lt in e; simpl in e.
           replace (INR (S n)) with (INR n + 1) in n0.
           -- unfold event_lt in n0; simpl in n0.
              lra.
           -- simpl.
              match_destr; simpl; lra.
         * specialize (nny x).
           lra.
       + intros.
         apply is_Elim_seq_fin.
         pose (n:=Z.to_nat(up (Y omega))).
         apply is_lim_seq_spec.
         unfold is_lim_seq'.
         intros.
         exists n.
         intros.
         unfold rvmult, EventIndicator.
         match_destr.
         * rewrite Rmult_1_r.
           rewrite Rminus_eq_0.
           rewrite Rabs_R0.
           apply cond_pos.
         * simpl in n1.
           destruct (archimed (Y omega)).
           assert (INR n0 > Y omega).
           {
             apply le_INR in H2.
             subst n.
             specialize (nny omega).
             rewrite INR_up_pos in H2; lra.
           }
           lra.
     - intros.
       now rewrite RbarExpectation.NNExpectation_Rbar_NNExpectation.       
   Qed.

   Lemma sum_Rbar_n_NNexp (Y : nat -> Ts -> R) 
        (rv : forall n, RandomVariable dom borel_sa (Y n))
        (nny: forall n, NonnegativeFunction (Y n)) :
     forall n,
       sum_Rbar_n (fun k =>  NonnegExpectation (Y k)) (S n) =
       NonnegExpectation (rvsum Y n).
   Proof.
     unfold sum_Rbar_n, rvsum.
     induction n.
     - simpl; rewrite Rbar_plus_0_r.
       apply NonnegExpectation_ext; intros ?.
       now rewrite sum_O.
     - rewrite seq_Sn.
       rewrite map_app.
       rewrite list_Rbar_sum_nneg_plus.
       + rewrite IHn.
         simpl.
         rewrite Rbar_plus_0_r.
         rewrite <- NonnegExpectation_sum by typeclasses eauto.
         apply NonnegExpectation_ext.
         unfold rvplus.
         intros ?.
         rewrite sum_Sn.
         reflexivity.
       + apply Forall_forall; intros.
         apply in_map_iff in H.
         destruct H as [? [??]]; subst.
         apply NonnegExpectation_pos.
       + apply Forall_forall; intros.
         apply in_map_iff in H.
         destruct H as [? [??]]; subst.
         apply NonnegExpectation_pos.
   Qed.

 Lemma partition_expectation (Y : Ts -> R)
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
   NonnegExpectation Y =
   ELim_seq
     (fun n : nat =>
        sum_Rbar_n
          (fun k : nat =>
             NonnegExpectation
               (rvmult Y 
                       (EventIndicator
                          (classic_dec (event_inter (event_ge dom Y (INR k))
                                                    (event_lt dom Y (INR k + 1)) ))))) 
          (S n)).
 Proof.
   rewrite partition_expectation0 with (rv := rv).
   apply ELim_seq_ext.
   intros.
   rewrite sum_Rbar_n_NNexp.
   - apply NonnegExpectation_ext.
     intro x.
     unfold rvmult, rvsum.
     rewrite  <- sum_disj_event_ind_mult; trivial.
   - intros.
     typeclasses eauto.
  Qed.
   
  Lemma Ash_6_2_4_helper1 (Y : Ts -> R) 
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    Rbar_le
      (ELim_seq (fun n => sum_Rbar_n (fun k => (INR k) * (ps_P (event_inter (event_ge dom Y (INR k))
                                                                            (event_lt dom Y (INR k + 1))
                                                                        ))) 
                                    (S n)))
      (NonnegExpectation Y).
  Proof.
    rewrite ELim_seq_ext  with
        (v := fun n => sum_Rbar_n (fun k => Rbar_mult (INR k)
                                                      (NonnegExpectation
                                                         (EventIndicator
                                                            (classic_dec
                                                               (event_inter (event_ge dom Y (INR k))
                                                                            (event_lt dom Y (INR k + 1))
                                                                            )))))
                                  (S n)).
    - rewrite partition_expectation with (rv := rv).
      apply ELim_seq_le; intros.
      apply sum_Rbar_n_le; intros.
      + replace (Rbar.Finite 0) with (Rbar_mult (INR n0) (Rbar.Finite 0)).
        * apply Rbar_mult_le_compat_l.
          -- apply pos_INR.
          -- apply NonnegExpectation_pos.
        * now rewrite Rbar_mult_0_r.
      + apply NonnegExpectation_pos.
      + destruct n0.
        * unfold INR.
          rewrite Rbar_mult_0_l.
          apply NonnegExpectation_pos.
          * assert (0 < INR (S n0)).
            {
              replace 0 with (INR (0%nat)).
              - apply lt_INR.
                lia.
              - now simpl.
            }
            replace (INR (S n0)) with (pos (mkposreal _ H)) by now simpl.
            rewrite <- NonnegExpectation_scale.
            apply NonnegExpectation_le.
            intro x.
            unfold rvscale, rvmult.
            unfold EventIndicator.
            match_case; intros.
            -- destruct e.
               unfold proj1_sig, event_ge in p.
               lra.
            -- lra.
     - intros.
       apply sum_Rbar_n_proper; trivial.
       intro x.
       rewrite NonnegExpectation_EventIndicator.
       now simpl.
  Qed.
    
 Lemma Ash_6_2_4_helper2 (Y : Ts -> R) 
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    Rbar_le
      (NonnegExpectation Y)
      (ELim_seq (fun n => sum_Rbar_n (fun k => (INR k + 1) * (ps_P (event_inter (event_ge dom Y (INR k))
                                                                                (event_lt dom Y (INR k + 1))
                                                                        ))) 
                                    (S n))).
  Proof.
    rewrite ELim_seq_ext  with
        (v := fun n => sum_Rbar_n (fun k => Rbar_mult (INR k + 1)
                                                      (NonnegExpectation
                                                         (EventIndicator
                                                            (classic_dec
                                                               (event_inter (event_ge dom Y (INR k))
                                                                            (event_lt dom Y (INR k + 1))
                                                                            )))))
                                  (S n)).
    - rewrite partition_expectation with (rv := rv).
      apply ELim_seq_le; intros.
      apply sum_Rbar_n_le; intros.
      + apply NonnegExpectation_pos.
      + replace (Rbar.Finite 0) with (Rbar_mult (INR n0 + 1) (Rbar.Finite 0)).
        * apply Rbar_mult_le_compat_l.
          -- rewrite <- S_INR.
             apply pos_INR.
          -- apply NonnegExpectation_pos.
        * now rewrite Rbar_mult_0_r.
      + rewrite <- S_INR.
        assert (0 < INR (S n0)).
        {
          replace 0 with (INR (0%nat)).
          - apply lt_INR.
            lia.
          - now simpl.
        }
        replace (INR (S n0)) with (pos (mkposreal _ H)) by now simpl.
        rewrite <- NonnegExpectation_scale.
        apply NonnegExpectation_le.
        intro x.
        unfold rvscale, rvmult.
        unfold EventIndicator.
        match_case; intros.
        * destruct e.
          unfold proj1_sig, event_lt in p0.
          left; lra.
        * lra.
    - intros.
      apply sum_Rbar_n_proper; trivial.
      intro x.
      rewrite NonnegExpectation_EventIndicator.
      now simpl.
  Qed.

  Lemma Rbar_plus_fin (a b : Rbar) (c : R) :
    Rbar_plus a c = Rbar_plus b c -> a = b.
  Proof.
    intros.
    destruct a; destruct b; simpl; try easy.
    simpl in H.
    apply Rbar_finite_eq in H.
    apply Rbar_finite_eq.
    lra.
  Qed.
  
  Lemma Ash_6_2_4_helper3a (Y : Ts -> R) 
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    forall n,
      Rbar.Finite (ps_P (event_ge dom Y (INR n))) =
      Lim_seq (fun m => sum_n
                          (fun  k => (EventIndicator (classic_dec (fun k0 => k0 >= n)%nat)) k *
                                      (ps_P (event_inter (event_ge dom Y (INR k))
                                                         (event_lt dom Y (INR k + 1)))))

                          m).
   Proof.
     generalize (Ash_6_2_4_partitioN Y rv nny); intros.
     destruct n.
     - rewrite Lim_seq_ext with
           (v := fun m =>
                    sum_n
                      (fun k : nat =>
                         ps_P (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1)))) m).
       + rewrite H.
         assert (event_equiv
                   (event_ge dom Y (INR 0))
                   Ω).
         * intro x.
           simpl.
           unfold pre_Ω.
           specialize (nny x).
           lra.
         * rewrite H0.
           apply Rbar_finite_eq.
           apply ps_all.
       + intros.
         apply sum_n_ext; intros.
         unfold EventIndicator.
         match_destr; try lra.
         lia.
     - intros.
       assert (ps_P (event_lt dom Y (INR (S n))) =
               sum_n
                 (fun  k => ps_P (event_inter (event_ge dom Y (INR k))
                                              (event_lt dom Y (INR k + 1))))
                 n).
       {
         rewrite ps_disjoint_collection_take_union.
         - rewrite ps_partition_intervals; trivial.
           now rewrite S_INR.
         - apply collection_take_preserves_disjoint.
           intros ????[??][??]; simpl in *.
           assert (INR n1 < INR n2 + 1) by lra.
           assert (INR n2 < INR n1 + 1) by lra.           
           rewrite <- S_INR in H5.
           rewrite <- S_INR in H6.
           apply INR_lt in H5.
           apply INR_lt in H6.
           lia.
       }
       rewrite <- Lim_seq_incr_n with (N := S n) in H.
       rewrite Lim_seq_ext with
           (v := fun n0 =>
                   plus
                     (sum_n_m
                        (fun k : nat =>
                           ps_P
                             (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1))))
                        0 n)
                     (sum_n_m
                        (fun k : nat =>
                           ps_P
                             (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1))))
                        (S n) (n0 + S n)) ) in H.
       + rewrite Lim_seq_plus in H.
         * rewrite Lim_seq_const in H.
           unfold sum_n in H0.
           rewrite <- H0 in H.
           apply Rbar_plus_fin with (c := ps_P (event_lt dom Y (INR (S n)))).
           rewrite Rbar_plus_comm in H.
           unfold sum_n.
           rewrite <- Lim_seq_incr_n with (N := S n).
           rewrite Lim_seq_ext with
               (v := (fun n0 : nat =>
            sum_n_m
              (fun k : nat =>
               ps_P
                 (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1))))
              (S n) (n0 + S n))).
           -- rewrite H.
              replace (S n) with (n + 1)%nat by lia.
              simpl.
              assert (event_equiv
                        (event_ge dom Y (INR (n + 1)))
                        (event_complement (event_lt dom Y (INR (n + 1))))).
              {
                intro x.
                simpl.
                unfold pre_event_complement.
                lra.
              }
              rewrite H1.
              rewrite ps_complement.
              apply Rbar_finite_eq.
              lra.
           -- intros.
              rewrite sum_split with (m := n); try lia.
              rewrite sum_n_m_ext_loc with (b := fun _ => zero).
              ++ rewrite sum_n_m_const_zero.
                 rewrite plus_zero_l.
                 apply sum_n_m_ext_loc; intros.
                 unfold EventIndicator.
                 match_destr; try lra.
                 lia.
              ++ intros.
                 unfold zero; simpl.
                 unfold EventIndicator.
                 match_destr; try lra.
                 lia.
         * apply ex_lim_seq_const.
         * apply ex_lim_seq_incr.
           intros.
           replace (S n0 + S n)%nat with (S (n0 + S n)) by lia.
           rewrite sum_n_Sm; try lia.
           replace (S n) with (n + 1)%nat by lia.
           replace (S (n0 + (n + 1))) with (n0 + (n+1) + 1)%nat by lia.
           unfold plus; simpl.
           apply Rplus_le_pos_l.
           apply ps_pos.
         * apply ex_Rbar_plus_pos.
           -- rewrite Lim_seq_const; simpl.
              apply sum_n_m_pos; intros.
              apply ps_pos.
           -- apply Lim_seq_pos; intros.
              apply sum_n_m_pos; intros.
              apply ps_pos.
       + intros.
         unfold sum_n.
         rewrite sum_split with (m := n); try lia.
         reflexivity.
    Qed.

  Lemma Ash_6_2_4_helper3 (Y : Ts -> R) 
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    Lim_seq (fun n => sum_n
                        (fun k => ps_P (event_ge dom Y (INR k + 1)))
                        n) =
    Lim_seq (fun n => sum_n
                        (fun k => (INR k) * (ps_P (event_inter (event_ge dom Y (INR k))
                                                               (event_lt dom Y (INR k + 1))
                                                               )))
                        n).
  Proof.
    rewrite <- Elim_seq_fin.
    rewrite ELim_seq_ext with
        (v := (fun m0 => sum_Rbar_n
           (fun nn => 
              ELim_seq (fun m1 => sum_Rbar_n
                          (fun  k => (EventIndicator (classic_dec (fun k0 => k0 >= S nn)%nat)) k *
                                     (ps_P (event_inter (event_ge dom Y (INR k))
                                                        (event_lt dom Y (INR k + 1))))) (S m1))) (S m0))).
    - rewrite ELim_seq_incr_1.
      erewrite ELim_seq_ext.
      2: {
        intros; apply sum_Rbar_n_proper; [intros ?| reflexivity].
        rewrite ELim_seq_incr_1; reflexivity.
      } 
      rewrite ELim_seq_sum_nneg_nested_swap.
      + rewrite <- Elim_seq_fin.
        rewrite <- ELim_seq_incr_1.
        apply ELim_seq_ext.
        intros.
        rewrite <- sum_Rbar_n_finite_sum_n.
        apply sum_Rbar_n_proper; trivial.
        unfold pointwise_relation.
        intros.
        rewrite <- ELim_seq_incr_n with (N := S a).
        rewrite ELim_seq_ext with
            (v := fun _ =>
                     INR a * ps_P (event_inter (event_ge dom Y (INR a)) (event_lt dom Y (INR a + 1)))).
        * now rewrite ELim_seq_const.
        * intros.
          destruct a.
          -- simpl.
             rewrite Rmult_0_l.
             replace (n0 + 1)%nat with (S n0) by lia.
             rewrite sum_Rbar_n_finite_sum_n.
             rewrite sum_n_ext_loc with
                 (b := fun _ => @zero R_AbelianGroup).
             ++ unfold sum_n.
                rewrite sum_n_m_const_zero.
                reflexivity.
             ++ intros.
                unfold EventIndicator.
                match_destr; try lia.
                rewrite Rmult_0_l.
                reflexivity.
          -- replace (n0 + S (S a))%nat with (S (n0 + S a)) by lia.
             rewrite sum_Rbar_n_finite_sum_n.
             unfold sum_n.
             rewrite sum_split with (m := a); try lia.
             rewrite plus_comm.
             rewrite sum_n_m_ext_loc with (b := (fun _ => @zero R_AbelianGroup)).
             ++ rewrite sum_n_m_const_zero.
                rewrite plus_zero_l.
                rewrite sum_n_m_ext_loc with
                    (b := fun x =>   ps_P
       (event_inter (event_ge dom Y (INR (S a))) (event_lt dom Y (INR (S a) + 1)))).
                ** rewrite sum_n_m_const.
                   now replace (S a - 0)%nat with (S a) by lia.
                ** intros.
                   unfold EventIndicator.
                   match_destr; try lra.
                   lia.
             ++ intros.
                unfold EventIndicator.
                match_destr; try lia.
                rewrite Rmult_0_l.
                reflexivity.
      + intros.
        simpl.
        apply Rmult_le_pos.
        * apply EventIndicator_pos.
        * apply ps_pos.
    - intros.
      rewrite <- sum_Rbar_n_finite_sum_n.
      apply sum_Rbar_n_proper; trivial.
      intros ?.
      generalize (Ash_6_2_4_helper3a Y rv nny (S a)); intros.
      rewrite <- Elim_seq_fin in H.
      rewrite ELim_seq_ext with
          (v :=  
             (fun x : nat => 
                (Rbar.Finite (
         sum_n
           (fun k : nat =>
            EventIndicator (classic_dec (fun k0 : nat => (k0 >= S a)%nat)) k *
            ps_P (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1))))
           x)))).
      + rewrite <- H.
        now rewrite S_INR.
      + intros.
        now rewrite <- sum_Rbar_n_finite_sum_n.
  Qed.

  Lemma Ash_6_2_4  (Y : Ts -> R) 
        (rv : RandomVariable dom borel_sa Y)
        (nny: NonnegativeFunction Y) :
    (Rbar_le (Lim_seq (fun n => sum_n
                                 (fun k => ps_P (event_ge dom Y (INR k + 1)))
                                 n) )
             (NonnegExpectation Y)) /\
    
    (Rbar_le (NonnegExpectation Y)
             (Rbar_plus 1 
                        (Lim_seq (fun n => sum_n
                                             (fun k => ps_P (event_ge dom Y (INR k + 1)))
                                             n) ))).
  Proof.
    rewrite Ash_6_2_4_helper3; trivial.
    rewrite <- Elim_seq_fin.
    split.
    - rewrite ELim_seq_ext with
          (v :=  (fun n : nat =>
                    sum_Rbar_n
                      (fun k : nat =>
                         INR k * ps_P (event_inter (event_ge dom Y (INR k))
                                                   (event_lt dom Y (INR k + 1)) 
                                                   )) 
                      (S n))).
      + apply Ash_6_2_4_helper1.
      + intros.
        now rewrite sum_Rbar_n_finite_sum_n.
    - rewrite ELim_seq_ext with
          (v :=  (fun n : nat =>
                    sum_Rbar_n
                      (fun k : nat =>
                         INR k * ps_P (event_inter (event_ge dom Y (INR k))
                                                   (event_lt dom Y (INR k + 1)) 
                                                   )) 
                      (S n))).
      + rewrite <- (Ash_6_2_4_partitioN Y rv nny).
        generalize (Ash_6_2_4_helper2 Y rv nny); intros.
        replace  (Rbar_plus
       (Lim_seq
          (fun n : nat =>
           sum_n
             (fun k : nat => ps_P (event_inter (event_ge dom Y (INR k) ) (event_lt dom Y (INR k + 1) )))
             n))
       (ELim_seq
          (fun n : nat =>
           sum_Rbar_n
             (fun k : nat =>
              INR k * ps_P (event_inter (event_ge dom Y (INR k) ) (event_lt dom Y (INR k + 1)))) 
             (S n))))
          with
             (ELim_seq
           (fun n : nat =>
            sum_Rbar_n
              (fun k : nat =>
               (INR k + 1) * ps_P (event_inter (event_ge dom Y (INR k) ) (event_lt dom Y (INR k + 1) )))
              (S n))).
        * apply H.
        * rewrite ELim_seq_ext with
             (v := fun n =>
                     Rbar_plus 
                      (sum_Rbar_n
                         (fun k : nat =>
                            ps_P (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1)))) 
                         (S n))
                      (sum_Rbar_n
                         (fun k : nat =>
                            (INR k) * ps_P (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1)))) 
                         (S n))).                      
          -- rewrite <- Elim_seq_fin.
             rewrite <- ELim_seq_plus.
             ++ apply ELim_seq_ext.
                intros.
                now rewrite sum_Rbar_n_finite_sum_n.                
             ++ rewrite ex_Elim_seq_fin.
                apply ex_lim_seq_incr.
                intros.
                rewrite sum_Sn.
                generalize (ps_pos  (event_inter (event_ge dom Y (INR (S n))) (event_lt dom Y (INR (S n) + 1)))); intros.
                unfold plus; simpl.
                simpl in H0; lra.
             ++ apply ex_Elim_seq_incr.
                intros.
                replace (S n) with (n + 1)%nat by lia.
                rewrite sum_Rbar_n_Sn.
                ** replace (sum_Rbar_n
                              (fun k : nat =>
                                 INR k * ps_P (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1)))) 
                              (n + 1)) with
                       (Rbar_plus
                          (sum_Rbar_n
                             (fun k : nat =>
                                INR k * ps_P (event_inter (event_ge dom Y (INR k)) (event_lt dom Y (INR k + 1)))) 
                             (n + 1))
                          0) at 1.
                   --- apply Rbar_plus_le_compat.
                       +++ apply Rbar_le_refl.
                       +++ apply Rmult_le_pos.
                           *** apply pos_INR.
                           *** apply ps_pos.
                   --- now rewrite Rbar_plus_0_r.
                ** intros.
                   simpl.
                   apply Rmult_le_pos.
                   --- apply pos_INR.
                   --- apply ps_pos.
             ++ apply ex_Rbar_plus_pos.
                ** apply ELim_seq_nneg.
                   intros.
                   apply sum_n_nneg.
                   intros.
                   apply ps_pos.
                ** apply ELim_seq_nneg.
                   intros.
                   rewrite sum_Rbar_n_finite_sum_n.                
                   apply sum_n_nneg.
                   intros.
                   apply Rmult_le_pos.
                   --- apply pos_INR.
                   --- apply ps_pos.
          -- intros.
             do 3 rewrite sum_Rbar_n_finite_sum_n.          
             simpl.
             rewrite sum_n_ext with
                 (b := (fun x : nat => 
                          plus
                           ( ps_P (event_inter (event_ge dom Y (INR x)) (event_lt dom Y (INR x + 1))))
                           (INR x * ps_P (event_inter (event_ge dom Y (INR x)) (event_lt dom Y (INR x + 1)))))).
             ++ rewrite sum_n_plus.
                unfold plus; simpl.
                apply Rbar_finite_eq.
                lra.
             ++ intros.
                unfold plus; simpl.
                lra.
        + intros.
          now rewrite sum_Rbar_n_finite_sum_n.          
    Qed.
            
  Lemma sum_inv_sq_lim :
    forall m,
      Rbar_le
        (Lim_seq (fun n => sum_n_m (fun k => / Rsqr (INR k)) (S m) (S m + n)%nat))
        (2 / (INR (S m))).
    Proof.
      intros.
      generalize (ub_lim_sum_inv_sq_alt (S m)); intros.
      cut_to H; try lia.
      rewrite Lim_seq_ext with
          (v := (fun n : nat => sum_n_m (fun k : nat => / (INR k)²) (S m) (S m + n))) in H.
      - eapply Rbar_le_trans.
        + apply H.
        + replace  (Rbar.Finite (2 / INR (S m))) with (Rbar_plus (/ INR (S m)) (/ INR (S m)))
            by (simpl; apply Rbar_finite_eq; lra).
          apply Rbar_plus_le_compat.
          * apply Rbar_le_refl.
          * rewrite Rbar_le_Rle.
            assert (1 <= INR (S m)).
            {
              replace (1) with (INR 1%nat) by now simpl.
              apply le_INR; lia.
            }
            apply Rinv_le_contravar; try lra.
            replace (INR (S m)) with (1 * (INR (S m))) at 1 by lra.
            unfold Rsqr.
            apply Rmult_le_compat_r; try lra.
      - intros.
        now rewrite sum_n_m_Reals; try lia.
   Qed.

    Lemma eq_Rbar_le (x y : Rbar) :
      x = y -> Rbar_le x y.
    Proof.
      intros.
      rewrite H.
      apply Rbar_le_refl.
   Qed.

  Lemma sum_n_ge_m (f : nat -> R) :
    forall n m,
      sum_n_m f m (m + n)%nat =
      sum_n (fun k =>
               (if (le_dec m k) then 1 else 0) * (f k))
            (m + n)%nat.
   Proof.
     intros.
     destruct m.
     - unfold sum_n.
       apply sum_n_m_ext.
       intros.
       match_case; intros.
       lra.
     - induction n.
       + replace (S m + 0)%nat with (S m) by lia.
         rewrite sum_n_n.
         rewrite sum_Sn.
         unfold plus; simpl.
         match_case; intros; try lia.
         rewrite sum_n_ext_loc with (b := fun _ => 0).
         * rewrite sum_n_zero; lra.
         * intros.
           match_case; intros; try lia.
           lra.
       + replace (S m + S n)%nat with (S (S m + n)) by lia.
         rewrite sum_n_Sm; try lia.
         rewrite sum_Sn; try lia.
         rewrite IHn.
         f_equal.
         match_case; intros; try lia.
         lra.
    Qed.

  Lemma sum_Rbar_n_ge_m (f : nat -> R) :
    forall n m,
      Rbar.Finite(sum_n_m f m (m + n)%nat) = 
      sum_Rbar_n (fun k =>
               (if (le_dec m k) then 1 else 0) * (f k))
            (S (m + n)).
   Proof.
     intros.
     rewrite sum_n_ge_m.
     now rewrite sum_Rbar_n_finite_sum_n.
    Qed.

    Lemma sum_inv_sq_Elim :
      forall m,
        Rbar_le
          (ELim_seq (sum_Rbar_n (fun j : nat => (if le_dec m j then 1 else 0) / (INR (S j))²)))
          (2 / (INR (S m))).
    Proof.
      intros.
      rewrite <- ELim_seq_incr_n with (N := (S m)).
      rewrite ELim_seq_ext with
          (v := (fun n => Rbar.Finite (sum_n_m (fun k => / Rsqr (INR k)) (S m) ((S m) + n)%nat))).
      - rewrite Elim_seq_fin.
        apply sum_inv_sq_lim.
      - intros.
        replace (n + (S m))%nat with (S (m + n)) by lia.
        unfold Rdiv.
        rewrite <- sum_Rbar_n_ge_m.
        replace (m + n)%nat with (n + m)%nat by lia.
        rewrite sum_n_m_shift.
        replace (S m + n)% nat with (n + S m)%nat by lia.
        rewrite sum_n_m_shift.
        apply Rbar_finite_eq.
        apply sum_n_ext.
        intros.
        f_equal; f_equal; f_equal; lia.
   Qed.

  Lemma ident_distrib_event_ge_abs
        {Idx} (X : forall (i:Idx), Ts -> R)
        {rv : forall (i:Idx), RandomVariable dom borel_sa (X i)} :
    identically_distributed_rv_collection Prts borel_sa X ->
    forall (r : R),
    forall (i j : Idx),
      ps_P (event_ge dom (rvabs (X i)) r) = ps_P (event_ge dom (rvabs (X j)) r).
   Proof.
     intros.
     specialize (H i j).
     generalize (identically_distributed_rv_compose Prts borel_sa borel_sa (X i) (X j) Rabs H); intros.
     unfold identically_distributed_rvs in H0.
     assert (sa_sigma borel_sa (fun (x : R) => x >= r)).
     {
       apply sa_le_ge; intros.
       simpl; intros.
       apply H1.
       now exists r0.
     }
     specialize (H0 (exist _ _ H1)).
     assert (event_equiv
               (event_ge dom (rvabs (X i)) r)
               (rv_preimage (Rabs ∘ X i) (exist (sa_sigma _) (fun x : R => x >= r) H1))) by (now simpl).
     assert (event_equiv
               (event_ge dom (rvabs (X j)) r)
               (rv_preimage (Rabs ∘ X j) (exist (sa_sigma _) (fun x : R => x >= r) H1))) by (now simpl).
     now rewrite H2, H3.
   Qed.

   Lemma lim_sum_0 (f : nat -> R) :
     is_lim_seq f 0 ->
     is_lim_seq (fun n => (sum_n f n)/(INR (S n))) 0.
   Proof.
     intros.
     apply is_lim_seq_ext with (u := fun n => (sum_f_R0 f n)/(INR (S n))).
     - intros.
       now rewrite sum_n_Reals.
     - apply is_lim_seq_Reals in H.
       generalize (Cesaro_1 f 0 H); intros.
       apply is_lim_seq_Reals in H0.
       apply is_lim_seq_incr_1 in H0.
       revert H0.
       apply is_lim_seq_ext.
       reflexivity.
   Qed.

   Lemma sum_n_Rplus (u v : nat -> R) (n : nat):
     sum_n (fun k : nat => u k + v k) n = (sum_n u n) + (sum_n v n).
   Proof.
     generalize (sum_n_plus u v n); intros.
     unfold plus in H; now simpl in H.
   Qed.

   Lemma sum_n_Rscal_r (f : nat -> R) (c:R)  (n : nat):
     (sum_n f n) * c  = (sum_n (fun k => (f k) * c) n).
   Proof.
     induction n.
     - now do 2 rewrite sum_O.
     - do 2 rewrite sum_Sn.
       rewrite <- IHn.
       unfold plus; simpl.
       now ring.
   Qed.

   Lemma sqr_scale_comm (X : Ts -> R) (c: R) :
     rv_eq (rvsqr (rvscale c X))
           (rvscale (Rsqr c) (rvsqr X)).
   Proof.
      intro x.
      rv_unfold.
      now rewrite Rsqr_mult.
   Qed.
   
   Instance is_finexp_sqr_scale (X : Ts -> R) (c: R) 
            {isfe : IsFiniteExpectation Prts (rvsqr X)} :
     IsFiniteExpectation Prts (rvsqr (rvscale c X)).
  Proof.
    generalize (sqr_scale_comm X c); intros.
    apply (IsFiniteExpectation_proper _ _ _ H).
    now apply IsFiniteExpectation_scale.
  Qed.

   Lemma finexp_sqr_scale (X : Ts -> R) (c: R) 
         {isfe : IsFiniteExpectation Prts (rvsqr X)} :
     FiniteExpectation Prts (rvsqr (rvscale c X)) = 
     Rsqr c * FiniteExpectation Prts (rvsqr X).
   Proof.
     erewrite FiniteExpectation_ext with (rv_X2 := (rvscale (Rsqr c) (rvsqr X))).
     - now rewrite FiniteExpectation_scale.
     - apply sqr_scale_comm.
  Qed.
     
  Lemma identically_distributed_sqr
             (X Y : Ts -> R)
             {rv_X : RandomVariable dom borel_sa X}
             {rv_Y : RandomVariable dom borel_sa Y} :
    identically_distributed_rvs Prts borel_sa X Y -> 
    identically_distributed_rvs Prts borel_sa 
                    (Rsqr ∘ X) 
                    (Rsqr ∘ Y).
  Proof.
    apply identically_distributed_rv_compose.
  Qed.

  Lemma identically_distributed_rvsqr
             (X Y : Ts -> R)
             {rv_X : RandomVariable dom borel_sa X}
             {rv_Y : RandomVariable dom borel_sa Y} :
    identically_distributed_rvs Prts borel_sa X Y -> 
    identically_distributed_rvs Prts borel_sa 
                    (rvsqr X) 
                    (rvsqr Y).
  Proof.
    intros.
    generalize (identically_distributed_sqr X Y H).
    now apply identically_distributed_rvs_proper.
  Qed.

  Lemma event_lt_indicator_sum (X : Ts -> R) (n : nat) 
        {rv: RandomVariable dom borel_sa X} :
    rv_eq
      (EventIndicator (classic_dec (event_lt dom (rvabs X) (INR n + 1))))
      (rvsum (fun k => EventIndicator (classic_dec 
                                         (event_inter
                                            (event_lt dom (rvabs X) (INR k + 1))
                                            (event_ge dom (rvabs X) (INR k)))))
             n).
  Proof.
    intro x.
    unfold rvsum, rvabs, EventIndicator, event_lt, event_ge, event_inter, pre_event_inter.
    assert (0 <= Rabs (X x)) by apply Rabs_pos.
    induction n.
    - rewrite sum_O.
      simpl.
      match_case; intros; match_case; intros; lra.
    - rewrite sum_Sn.
      rewrite S_INR.
      simpl in *.
      rewrite <- IHn.
      unfold plus; simpl.
      match_case; intros; match_case; intros; match_case; intros; lra.
  Qed.

  Lemma event_lt_indicator_sum_mult (X Y : Ts -> R) (n : nat) 
        {rv: RandomVariable dom borel_sa X} :
    rv_eq
      (rvmult Y (EventIndicator (classic_dec (event_lt dom (rvabs X) (INR n + 1)))))
      (rvsum (fun k => rvmult Y (EventIndicator (classic_dec 
                                         (event_inter
                                            (event_lt dom (rvabs X) (INR k + 1))
                                            (event_ge dom (rvabs X) (INR k))))))
             n).
   Proof.
     rewrite event_lt_indicator_sum.
     intro x.
     unfold rvmult, rvsum.
     symmetry.
     do 2 rewrite sum_n_Reals.
     rewrite scal_sum.
     apply sum_f_R0_ext.
     intros.
     lra.
   Qed.

   Lemma sum_n_pos_incr (f : nat -> R) :
     (forall n, 0 <= f n) ->
     forall n, sum_n f n <= sum_n f (S n).
   Proof.
     intros.
     replace (sum_n f n) with (sum_n f n + 0) by lra.
     rewrite sum_Sn.
     now apply Rplus_le_compat_l.
   Qed.

   Lemma ELim_seq_ind_le (f : nat -> R) (x : nat) :
     ELim_seq
       (sum_Rbar_n
          (fun n0 : nat =>
             (if le_dec n0 x then 1 else 0) *
             (f n0))) =
     (sum_n f x).
   Proof.
     rewrite <- ELim_seq_incr_n with (N := (S x)).
     rewrite ELim_seq_ext with
         (v := fun n => Rbar.Finite(sum_n f  x)).
     - apply ELim_seq_const.
     - intros.
       replace (n + S x)%nat with (S (n + x)) by lia.
       rewrite sum_Rbar_n_finite_sum_n.
       apply Rbar_finite_eq.
       induction n.
       + replace (0 + x)%nat with x by lia.
         apply sum_n_ext_loc.
         intros.
         match_case; intros; try lra; try lia.
       + replace (S n + x)%nat with (S (n + x)) by lia.
         rewrite sum_Sn.
         replace (sum_n f x) with (sum_n f x + 0) by lra.
         rewrite IHn.
         unfold plus; simpl.
         f_equal.
         match_case; intros; try lra; try lia.
    Qed.

   Lemma Rbar_mult_le_nneg (f g : Rbar) :
     Rbar_le 0 f -> Rbar_le 0 g ->
     Rbar_le 0 (Rbar_mult f g).
   Proof.
     intros.
     replace (Rbar.Finite 0) with (Rbar_mult 0 g) by now rewrite Rbar_mult_0_l.
     now apply Rbar_mult_le_compat_r.
   Qed.

   Lemma scale_pos_sum_Rbar_n (f : nat -> Rbar) (c : R) :
     (0 < c) ->
     (forall n, Rbar_le 0 (f n)) ->
     forall n,
       Rbar_mult c (sum_Rbar_n f n) = sum_Rbar_n (fun k => Rbar_mult c (f k)) n.
   Proof.
     induction n.
     - unfold sum_Rbar_n; simpl.
       now rewrite Rmult_0_r.
     - rewrite sum_Rbar_n_Sn; trivial.
       rewrite sum_Rbar_n_Sn.
       + rewrite <- IHn.
         now rewrite Rbar_mult_r_plus_distr.
       + intros.
         apply Rbar_mult_le_nneg; trivial.
         simpl; lra.
   Qed.

   Existing Instance Rbar_le_pre.

   Lemma indicator_lim_seq (X : Ts -> R)
         {rv : RandomVariable dom borel_sa (rvabs X)}
         {isfe : forall x, IsFiniteExpectation Prts
           (rvmult (rvabs X)
              (EventIndicator (classic_dec (event_lt dom (rvabs X) (INR x + 1)))))} 
         {isfe0 : IsFiniteExpectation Prts (rvabs X)} :
     Lim_seq
       (fun x : nat =>
          FiniteExpectation Prts
                            (rvmult (rvabs X)
                                    (EventIndicator
                                       (classic_dec (event_lt dom (rvabs X) (INR x + 1)))))) =
     FiniteExpectation Prts (rvabs X).
   Proof.
     apply monotone_convergence_FiniteExpectation; trivial.
     - typeclasses eauto.
     - intros; typeclasses eauto.
     - intros; typeclasses eauto.
     - intros n x.
       rv_unfold.
       match_destr; try lra.
       rewrite Rmult_0_r.
       apply Rabs_pos.
     - intros n x.
       rv_unfold.
       unfold event_lt.
       match_case; intros.
       + match_case; intros; try lra.
         simpl in *.
         generalize n0; intros.
         generalize e; intros.
         match_case_in n0; intros.
         * rewrite H1 in n1.
           rewrite H1 in e0.
           simpl in e0.
           lra.
         * rewrite H1 in n1.
           rewrite H1 in e0.
           lra.
       + match_case; intros; try lra.
         rewrite Rmult_0_r, Rmult_1_r.
         apply Rabs_pos.
     - intros.
       apply is_lim_seq_spec.
       unfold is_lim_seq'.
       intros.
       unfold rvabs.
       exists (Z.to_nat (up (Rabs (X omega)))).
       intros.
       unfold event_lt.
       unfold rvmult, EventIndicator.
       match_destr.
       * rewrite Rmult_1_r.
         rewrite Rminus_eq_0.
         rewrite Rabs_R0.
         apply cond_pos.
       * simpl in n0.
         destruct (archimed (Rabs (X omega))).
         assert (INR n > Rabs (X omega)).
         {
           apply le_INR in H.
           rewrite INR_up_pos in H.
           - lra.
           - apply Rle_ge.
             apply Rabs_pos.
         }
         lra.
   Qed.

   
 Lemma BC_exist_N_not_ge (Y : nat -> Ts -> R) (α : nat -> R)
       (rv: forall n k, RandomVariable dom borel_sa (rvabs (Y (n + k)%nat))) :
   ps_P
     (inter_of_collection
        (fun k : nat =>
           union_of_collection
             (fun n : nat => event_ge dom (rvabs (Y (n + k)%nat)) (α (n + k)%nat)))) =
   0 ->
  almost Prts
    (fun omega : Ts =>
     exists N : nat,
       forall n : nat, (N <= n)%nat -> rvabs (Y n) omega < (α n)).
   Proof.
     intros.
     rewrite almost_alt_eq.
     unfold almost_alt. push_neg.
     simpl in H. eexists.
     split; [apply H|intros omega ?H].
     simpl. intros n. specialize (H0 n).
     destruct H0 as [n0 [Hn0 HZ]]. exists (n0-n)%nat.
     now replace ((n0 - n + n)%nat) with n0 by lia.
   Qed.

   Lemma lim_avg_tails0 (X : nat -> R) (N:nat):
     is_lim_seq (fun n : nat => sum_n_m X 0 N / INR (S (n + S N))) 0.
   Proof.
     unfold Rdiv.
     replace (Rbar.Finite 0) with (Rbar_mult (sum_n_m X 0 N) 0) by now rewrite Rbar_mult_0_r.
     apply is_lim_seq_scal_l.
     replace (Rbar.Finite 0) with (Rbar_inv p_infty) by now simpl.
     apply is_lim_seq_inv; try discriminate.
     rewrite <- is_lim_seq_incr_n with (N := S N) (u := fun n => INR (S n)).
     rewrite <- is_lim_seq_incr_1.
     apply is_lim_seq_INR.
   Qed.

  

   Lemma lim_avg_tails (X : nat -> R) (l:R) (N:nat):
     is_lim_seq (fun n => sum_n_m X 0 n / INR (S n)) l <->
     is_lim_seq (fun n => sum_n_m X N n / INR (S n)) l.
   Proof.
     destruct N; try easy.
     split; intros.
     - apply is_lim_seq_incr_n with (N := S N) in H.
       apply is_lim_seq_incr_n with (N := S N).
       apply is_lim_seq_ext   with 
           (u := fun n => minus
                            (sum_n_m X 0 (n + S N) / INR (S (n + S N)))
                            ((sum_n_m X 0 N) / INR (S (n + S N)))).
       + intros.
         rewrite sum_n_m_Chasles with (m := N); try lia.
         unfold minus, plus, opp.
         simpl.
         field.
         match_destr.
         rewrite <- S_INR.
         apply INR_nzero; lia.
       + apply is_lim_seq_minus with (l1 := l) (l2 := 0); trivial.
         * apply lim_avg_tails0.
         * unfold is_Rbar_minus, is_Rbar_plus; simpl.
           f_equal.
           apply Rbar_finite_eq; lra.
   -  apply is_lim_seq_incr_n with (N := S N) in H.
      apply is_lim_seq_incr_n with (N := S N).
      apply is_lim_seq_ext with
          (u := fun n => plus
                           (sum_n_m X 0 N / INR (S (n + S N)))
                           (sum_n_m X (S N) (n + S N) / INR (S (n + S N)))).
      + intros.
        symmetry.
        rewrite sum_n_m_Chasles with (m := N); try lia.
        unfold plus; simpl; field.
        match_destr.
        rewrite <- S_INR.
        apply INR_nzero; lia.
      + apply is_lim_seq_plus with (l1 := 0) (l2 := l); trivial.
        * apply lim_avg_tails0.
        * unfold is_Rbar_plus; simpl.
          f_equal.
          apply Rbar_finite_eq; lra.          
  Qed.

  Lemma Ash_6_2_5_0 (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)} 
        {isfe : forall n, IsFiniteExpectation Prts (X n)} :
    (forall n, FiniteExpectation Prts (X n) = 0) ->
    iid_rv_collection Prts borel_sa X ->
    almost Prts (fun omega => is_lim_seq (fun n => ((rvsum X n) omega)/(INR (S n))) 0).
  Proof.
    intros fe0 iid.
    assert (Rbar_le (Lim_seq (fun n => sum_n
                                         (fun k => ps_P (event_ge dom (rvabs (X k)) (INR k + 1)))
                                         n) )
                    (NonnegExpectation (rvabs (X 0%nat)))).
    {
      rewrite Lim_seq_ext with
          (v :=  (fun n => sum_n
                             (fun k => ps_P (event_ge dom (rvabs (X 0%nat)) (INR k + 1)))
                             n) ).
      - apply Ash_6_2_4.
      - intros.
        apply sum_n_ext.
        intros.
        apply ident_distrib_event_ge_abs.
        now unfold iid_rv_collection in iid.
    }
    assert (isfe0: IsFiniteExpectation Prts (rvabs (X 0%nat))).
    {
      now apply IsFiniteExpectation_abs.
    }
    pose (Y := fun n => rvmult (X n) (EventIndicator (classic_dec (event_lt _ (rvabs (X n)) (INR n + 1))))).
    assert (isfey: forall n, IsFiniteExpectation Prts (Y n)).
    {
      intros.
      apply IsFiniteExpectation_indicator; trivial.
      apply sa_le_lt.
      intros.
      apply borel_sa_preimage2.
      assert (RandomVariable dom borel_sa (rvabs (X n))).
      - now apply rvabs_rv.
      - apply H0.
    }
    assert (isfey0: forall (n:nat), IsFiniteExpectation Prts (rvmult (X 0%nat) (EventIndicator (classic_dec (event_lt _ (rvabs (X 0%nat)) (INR n + 1)))))).
    {
      intros.
      apply IsFiniteExpectation_indicator; trivial.
      apply sa_le_lt.
      intros.
      apply borel_sa_preimage2.
      assert (RandomVariable dom borel_sa (rvabs (X 0%nat))).
      - now apply rvabs_rv.
      - apply H0.
    }
    assert (iidy0: forall n, identically_distributed_rvs Prts borel_sa (Y n) (rvmult (X 0%nat)
                                                                                          (EventIndicator (classic_dec (event_lt _ (rvabs (X 0%nat)) (INR n + 1)))))).
    {
      intros.
      pose (f := fun x => x * (EventIndicator (classic_dec (event_lt borel_sa (rvabs id) (INR n + 1)))) x).
      assert (RandomVariable borel_sa borel_sa f).
      {
        unfold f.
        apply rvmult_rv.
        -  red; intros.
           apply borel_sa_preimage; trivial; intros.
           simpl; intros.
           apply H0.
           now exists r.
        -  apply EventIndicator_rv.
        }
      destruct iid.
      generalize (identically_distributed_rv_compose Prts borel_sa borel_sa (X n) (X 0%nat) f (H2 n 0%nat)); intros.
      revert H3.
      apply identically_distributed_rvs_proper.
      - now simpl.
      - intro x.
        unfold Y, f.
        unfold rvmult, rvabs, EventIndicator, compose.
        f_equal.
      - intro x.
        unfold Y, f.
        unfold rvmult, rvabs, EventIndicator, compose.
        f_equal.
    }
    assert (fey0: forall n, FiniteExpectation Prts (Y n) = FiniteExpectation Prts (rvmult (X 0%nat)
                                                                                          (EventIndicator (classic_dec (event_lt _ (rvabs (X 0%nat)) (INR n + 1)))))).
    {
      intros.
      eapply ident_distr_finite_exp_eq.
      apply iidy0.
    }
    assert (limexpy: is_lim_seq (fun n =>  FiniteExpectation Prts (Y n)) (FiniteExpectation Prts (X 0%nat))).
    {
      eapply is_lim_seq_ext.
      - intros; symmetry; apply fey0.
      - eapply is_lim_seq_ext with
            (u := (fun n : nat =>
                     RbarExpectation.Rbar_FiniteExpectation 
                       Prts
                       (rvmult (X 0%nat) (EventIndicator (classic_dec (event_lt dom (rvabs (X 0%nat)) (INR n + 1))))))).
        + intros.
          rewrite RbarExpectation.FinExp_Rbar_FinExp.
          * reflexivity.
          * typeclasses eauto.
        + rewrite <- RbarExpectation.FinExp_Rbar_FinExp; trivial.
          apply RbarExpectation.Dominated_convergence with (g := rvabs (X 0%nat)).
          * intros; typeclasses eauto.
          * typeclasses eauto.
          * typeclasses eauto.
          * now apply RbarExpectation.IsFiniteExpectation_Rbar.
          * intros n x.
            simpl.
            unfold rvmult, rvabs, EventIndicator.
            match_destr.
            -- now rewrite Rmult_1_r.
            -- rewrite Rmult_0_r, Rabs_R0.
               apply Rabs_pos.
          * intros.
            rewrite is_Elim_seq_fin.
            apply is_lim_seq_spec.
            unfold is_lim_seq'.
            intros.
            exists (Z.to_nat(up (Rabs (X 0%nat x)))).
            intros.
            unfold rvmult, EventIndicator.
            match_destr.
            -- rewrite Rmult_1_r.
               rewrite RIneq.Rminus_eq_0.
               rewrite Rabs_R0.
               apply cond_pos.
            -- unfold event_lt,rvabs in n0.
               simpl in n0.
               destruct (archimed (Rabs (X 0%nat x))).
               apply le_INR in H0.
               rewrite INR_up_pos in H0.
               ++ lra.
               ++ apply Rle_ge, Rabs_pos.
    }
    assert (Rbar.Finite (FiniteExpectation Prts (X 0%nat)) = 0).
    {
      now apply Rbar_finite_eq.
    }
    rewrite H0 in limexpy; clear H0.

    assert (limsumyexp:almost Prts (fun omega : Ts => 
                                      is_lim_seq (fun n : nat => sum_n (fun k => (Y k omega - (FiniteExpectation Prts (Y k)))) n / INR (S n)) 0)).
    {

      assert (almost Prts (fun omega => ex_series (fun k => (Y k omega - (FiniteExpectation Prts (Y k)))/(INR (S k))) )).
      {
        assert (forall k, RandomVariable 
                            dom borel_sa
                            (rvscale (/ INR (S k)) 
                                     (rvminus (Y k)
                                              (const (FiniteExpectation Prts (Y k))))))
          by (intros; typeclasses eauto).
         assert (forall k, rv_le (rvabs (Y k)) (const (INR k + 1))).
          {
            intros k x.
            subst Y.
            unfold rvmult, EventIndicator, rvabs, const; simpl.
            match_destr.
            - rewrite Rmult_1_r; lra.
            - rewrite Rmult_0_r, Rabs_R0, <- S_INR.
              left; apply lt_0_INR; lia.
          }
          assert (forall k, IsFiniteExpectation 
                              Prts
                              (rvsqr 
                                 (rvminus (Y k)
                                          (const (FiniteExpectation Prts (Y k)))))).
          {
            intros.
            apply IsFiniteExpectation_bounded with (rv_X1 := const 0) 
                                                   (rv_X3 := const (Rsqr ((INR k + 1) + (Rabs (FiniteExpectation Prts (Y k)))))); try apply IsFiniteExpectation_const.
            - intro x.
              unfold const, rvsqr.
              apply Rle_0_sqr.
            - intro x.
              unfold const, rvsqr.
              rewrite rvminus_unfold.
              specialize (H1 k x).
              unfold rvabs, const in H1.
              apply Rsqr_le_abs_1.
              unfold Rminus.
              eapply Rle_trans.
              + apply Rabs_triang.
              + rewrite Rabs_Ropp.
                rewrite (Rabs_right (INR k + 1 + Rabs (FiniteExpectation Prts (Y k)))); try lra.
                rewrite <- S_INR.
                apply Rle_ge.
                apply Rplus_le_le_0_compat.
                * left; apply lt_0_INR; lia.
                * apply Rabs_pos.
          }
          eapply Ash_6_2_1.
        - assert (independent_rv_collection Prts (const borel_sa) Y).
          {
            pose (YY :=
              (fun n x => x * (EventIndicator (classic_dec (event_lt borel_sa (rvabs id) (INR n + 1))) x))).
            assert (forall n, RandomVariable (const borel_sa n) (const borel_sa n) (YY n)).
            {
              intros.
              unfold const.
              unfold YY.
              typeclasses eauto.
            }
            unfold iid_rv_collection in iid.
            destruct iid.
            generalize (independent_rv_collection_compose Prts
                     (const borel_sa) X
                     (const borel_sa) YY H4).
            apply independent_rv_collection_proper; try easy.
          }
          assert (independent_rv_collection 
                    Prts (const borel_sa)
                    (fun k => (rvscale (/ INR (S k)) (rvminus (Y k) (const (FiniteExpectation Prts (Y k))))))).
          {
            pose (YY :=
                    (fun (k:nat)(x:R) => rvscale (/ INR (S k)) (rvminus id (const (FiniteExpectation Prts (Y k)))) x)).
            assert (forall n, RandomVariable (const borel_sa n) (const borel_sa n) (YY n)).
            {
              intros.
              unfold YY, const.
              apply rvscale_rv.
              apply rvminus_rv.
              - apply id_rv.
              - apply rvconst.
            }
            generalize (independent_rv_collection_compose Prts
                     (const borel_sa) Y
                     (const borel_sa) YY H3).
            apply independent_rv_collection_proper; try easy.            
          }
          intros.
          assert (forall n1,
                     (rv_eq (fun x : Ts => (Y n1 x - FiniteExpectation Prts (Y n1)) / INR (S n1))
                            (rvscale (/ (INR (S n1))) (rvminus (Y n1) (const (FiniteExpectation Prts (Y n1))))))).
          {
            intros ? ?.
            rv_unfold.
            unfold Rdiv.
            ring.
          }
          assert (rv00:forall n1, RandomVariable dom borel_sa
                                       (rvscale (/ (INR (S n1))) (rvminus (Y n1) (const (FiniteExpectation Prts (Y n1)))))).
          {
            intros.
            typeclasses eauto.
          }
          assert  (rv0 : forall n1 : nat,
            RandomVariable dom borel_sa (fun x : Ts => (Y n1 x - FiniteExpectation Prts (Y n1)) / INR (S n1))).
          {
            intros.
            generalize (rv00 n1).
            now apply RandomVariable_proper.
          }
          assert (isfe2 : forall n1,
              IsFiniteExpectation Prts (fun x : Ts => (Y n1 x - FiniteExpectation Prts (Y n1)) / INR (S n1))).
          {
            intros.
            assert (IsFiniteExpectation Prts 
                                        (rvscale (/ (INR (S n1))) (rvminus (Y n1) (const (FiniteExpectation Prts (Y n1)))))) 
                   by typeclasses eauto.
            revert H6.
            now apply IsFiniteExpectation_proper.
          }
          { Unshelve.
              - shelve.
              - intros.
                generalize (H0 n); apply RandomVariable_proper; try reflexivity.
                rv_unfold; intros ?.
                unfold Rdiv; ring.
              - intros.
                apply IsFiniteExpectation_proper with
                    (x := rvscale (Rsqr (/ (INR (S k))))
                                  (rvsqr (rvminus (Y k) (const (FiniteExpectation Prts (Y k)))))).
                + intros ?.
                  rv_unfold.
                  unfold Rdiv, Rsqr.
                  ring.
                + now apply IsFiniteExpectation_scale.
            }
            Unshelve.
          generalize (is_condexp_indep  (fun (n0 : nat) (x : Ts) => (Y n0 x - FiniteExpectation Prts (Y n0)) / INR (S n0)) n (isfe2 (S n))); intros.
          cut_to H6.
          + etransitivity; [| etransitivity]; [| apply H6 |].
            * apply Condexp_all_proper'; reflexivity.
            * apply all_almost; intros.
              rv_unfold.
              erewrite FiniteExpectation_ext with (rv_X2 := rvscale (/ (INR (S (S n)))) (rvminus (Y (S n)) (const (FiniteExpectation Prts (Y (S n)))))).
              -- rewrite FiniteExpectation_scale.
                 rewrite FiniteExpectation_minus.
                 rewrite FiniteExpectation_const.
                 f_equal.
                 ring.
              -- apply H5.
          + revert H4.
            now apply independent_rv_collection_proper.
        - assert (forall n, IsFiniteExpectation Prts (rvsqr (Y n))).
          {
            intros.
            apply IsFiniteExpectation_bounded with (rv_X1 := const 0) 
                                                   (rv_X3 := const (Rsqr (INR n + 1))); try apply IsFiniteExpectation_const.
            - intro x.
              apply Rle_0_sqr.
            - intro x.
              apply Rsqr_le_abs_1.
              rewrite (Rabs_right (INR n + 1)).
              + apply H1.
              + rewrite <- S_INR.
                apply Rle_ge.
                left; apply lt_0_INR; lia.
          }
          apply ex_series_ext with
              (a := fun k => 
                      FiniteExpectation Prts
                        (rvscale (/ INR (S k))²
                                 (rvsqr (rvminus 
                                           (Y k) 
                                           (const (FiniteExpectation Prts (Y k))))))).
          + intro.
            apply FiniteExpectation_ext.
            rewrite <- sqr_scale_comm.
            intro x.
            rv_unfold.
            f_equal.
            field.
            apply INR_nzero; lia.
          + assert (forall k,
                     FiniteExpectation 
                       Prts
                        (rvscale (/ INR (S k))²
                                 (rvsqr (rvminus (Y k) (const (FiniteExpectation Prts (Y k))))))
                     <= 
                 FiniteExpectation Prts (rvsqr (Y k))/(Rsqr (INR (S k)))).
          {
            intros.
            erewrite FiniteExpectation_scale.
            unfold Rdiv.
            rewrite Rmult_comm.
            rewrite <- Rsqr_inv.
            - apply Rmult_le_compat_r.
              + apply Rle_0_sqr.
              + assert (rv_eq (rvsqr (rvminus (Y k) (const (FiniteExpectation Prts (Y k)))))
                              (rvplus (rvplus (rvsqr (Y k))
                                              (rvscale (- 2 * FiniteExpectation Prts (Y k))
                                                       (Y k)))
                                      (const (Rsqr (FiniteExpectation Prts (Y k)))))).
                {
                  intro x.
                  rv_unfold.
                  unfold Rsqr.
                  ring.
                }
                rewrite (FiniteExpectation_ext Prts _ _ H4).
                do 2 rewrite FiniteExpectation_plus.
                rewrite FiniteExpectation_scale.
                rewrite FiniteExpectation_const.
                unfold Rsqr.
                ring_simplify.
                apply Rplus_le_reg_r with
                    (r := (FiniteExpectation Prts (Y k)) ^2 ).
                ring_simplify.
                replace (FiniteExpectation Prts (rvsqr (Y k))) with
                    (FiniteExpectation Prts (rvsqr (Y k)) + 0) at 1 by lra.
                apply Rplus_le_compat_l.
                apply pow2_ge_0.
            - apply INR_nzero; lia.
          }
          apply ex_series_nneg_bounded with
              (g := (fun k =>  FiniteExpectation Prts (rvsqr (Y k)) / (INR (S k))²)); trivial.
          * intros.
            apply FiniteExpectation_pos.
            intro x.
            rv_unfold.
            rewrite <- Rsqr_mult.
            apply Rle_0_sqr.
          * clear H4.
            assert (forall k, IsFiniteExpectation Prts
                      (rvsqr (rvmult (X 0%nat)
                                     (EventIndicator
                                        (classic_dec (event_lt dom (rvabs (X 0%nat)) (INR k + 1))))))).
            {
              intros.
              apply IsFiniteExpectation_bounded with (rv_X1 := const 0) 
                                                   (rv_X3 := const (Rsqr (INR k + 1))); try apply IsFiniteExpectation_const.
              - intro x.
                unfold const, rvsqr, rvmult, rvabs, EventIndicator.
                match_destr; apply Rle_0_sqr.
              - intro x.
                unfold const, rvsqr, rvmult, rvabs, EventIndicator.
                match_case; intros.
                + rewrite Rmult_1_r.
                  apply Rsqr_le_abs_1.
                  rewrite (Rabs_right (INR k + 1)).
                  * unfold event_lt in e.
                    simpl in e; lra.
                  * rewrite <- S_INR.
                    apply Rle_ge.
                    left; apply lt_0_INR; lia.
                + rewrite Rmult_0_r, Rsqr_0.
                  apply Rle_0_sqr.
            }
            assert (forall k,
                       FiniteExpectation Prts (rvsqr (Y k)) =
                       FiniteExpectation 
                         Prts (rvsqr (rvmult (X 0%nat)
               (EventIndicator
                  (classic_dec (event_lt dom (rvabs (X 0%nat)) (INR k + 1))))))).
            {
              intros.
              eapply ident_distr_finite_exp_eq.
              now apply identically_distributed_rvsqr.
            }
            assert (forall k,
                       (FiniteExpectation Prts
                                          (rvsqr
                                             (rvmult (X 0%nat)
                                                     (EventIndicator
                                                        (classic_dec (event_lt dom (rvabs (X 0%nat)) (INR k + 1)))))))/(Rsqr (INR (S k))) =
                       (FiniteExpectation Prts (rvsqr (Y k))/(Rsqr (INR (S k))))).
            {
              intros.
              f_equal.
              symmetry.
              apply H5.
            }
            apply (ex_series_ext _ _ H6).
            clear H5 H6.
            assert (forall k,
                       rv_eq
                         (rvsqr
                            (rvmult (X 0%nat)
                                    (EventIndicator
                                       (classic_dec (event_lt dom (rvabs (X 0%nat)) (INR k + 1))))))
                         (rvmult (rvsqr (X 0%nat))
                                 (EventIndicator
                                       (classic_dec (event_lt dom (rvabs (X 0%nat)) (INR k + 1)))))).
            {
              intros k x.
              rv_unfold.
              rewrite Rsqr_mult.
              f_equal.
              match_destr; unfold Rsqr; lra.

            }
            generalize (fun k => event_lt_indicator_sum_mult (X 0%nat)
                                                             (rvsqr (X 0%nat))
                                                             k); intros.
            assert (forall k,
                       rv_eq
                          (rvsqr
                             (rvmult (X 0%nat)
                                     (EventIndicator
                                        (classic_dec (event_lt dom (rvabs (X 0%nat)) (INR k + 1))))))
                             (rvsum
            (fun k0 : nat =>
             rvmult (rvsqr (X 0%nat))
               (EventIndicator
                  (classic_dec
                     (event_inter (event_lt dom (rvabs (X 0%nat)) (INR k0 + 1))
                        (event_ge dom (rvabs (X 0%nat)) (INR k0)))))) k)).
            {
              intros.
              rewrite H5.
              now rewrite H6.
            }
            generalize (fun k => FiniteExpectation_ext_alt _ _ _ (H7 k)); intros.
            generalize (fun (k:nat) => Rmult_eq_compat_r (/ (Rsqr (INR (S k)))) _ _ (H8 k)); intros.
            assert
              (isfe' : forall n : nat,
                  IsFiniteExpectation Prts
                    (rvmult (rvsqr (X 0%nat))
                       (EventIndicator
                          (classic_dec
                             (event_inter
                                (event_lt dom (rvabs (X 0%nat)) (INR n + 1))
                                (event_ge dom (rvabs (X 0%nat)) (INR n))))))).
            {
              intros.
              apply IsFiniteExpectation_bounded with (rv_X1 := const 0) 
                                                   (rv_X3 := const (Rsqr (INR n + 1))); try apply IsFiniteExpectation_const.
              - intro x.
                unfold const, rvmult, rvsqr, EventIndicator.
                match_destr.
                + rewrite Rmult_1_r.
                  apply Rle_0_sqr.
                + rewrite Rmult_0_r; lra.
              - intro x.
                unfold const, rvmult, rvsqr, EventIndicator, rvabs.
                unfold event_inter, event_lt, event_ge, pre_event_inter.
                simpl.
                match_case; intros.
                + rewrite Rmult_1_r.
                  apply Rsqr_le_abs_1.
                  rewrite (Rabs_right (INR n + 1)).
                  * lra.
                  * rewrite <- S_INR.
                    apply Rle_ge.
                    apply pos_INR.
               + rewrite Rmult_0_r.
                 apply Rle_0_sqr.
            }
            generalize (sum_expectation Prts
             (fun k0 : nat =>
             rvmult (rvsqr (X 0%nat))
               (EventIndicator
                  (classic_dec
                     (event_inter (event_lt dom (rvabs (X 0%nat)) (INR k0 + 1))
                                  (event_ge dom (rvabs (X 0%nat)) (INR k0)))))) _ _); intros.
            symmetry in H9.
            unfold Rdiv.
            apply (ex_series_ext _ _ H9).
            generalize (fun (k:nat) => Rmult_eq_compat_r (/ (Rsqr (INR (S k)))) _ _ (H10 k)); intros.
            assert (ex_series 
                      (fun k =>  
                         sum_n
                           (fun n0 : nat =>
                              FiniteExpectation 
                                Prts
                                (rvmult 
                                   (rvsqr (X 0%nat))
                                   (EventIndicator
                                      (classic_dec
                                         (event_inter (event_lt dom (rvabs (X 0%nat)) (INR n0 + 1))
                                                      (event_ge dom (rvabs (X 0%nat)) (INR n0))))))) k *
                         / (INR (S k))²)).
            {
              rewrite <- ex_finite_lim_series.
              rewrite ex_finite_lim_seq_correct.
              split.
              - apply ex_lim_seq_incr; intros.
                apply sum_n_pos_incr.
                intros.
                apply Rmult_le_pos.
                + apply sum_n_nneg; intros.
                  apply FiniteExpectation_pos.
                  typeclasses eauto.
                + left.
                  apply Rinv_0_lt_compat.
                  apply Rsqr_pos_lt.
                  apply INR_nzero; lia.
              - rewrite Lim_seq_sum_Elim.
                rewrite ELim_seq_ext with
                    (v := sum_Rbar_n
                             (fun x : nat =>
                                (ELim_seq
                                   (sum_Rbar_n
                                      (fun n0 : nat =>
              (if (le_dec n0 x) then 1 else 0) *
              FiniteExpectation Prts
                (rvmult (rvsqr (X 0%nat))
                   (EventIndicator
                      (classic_dec
                         (event_inter
                            (event_lt dom (rvabs (X 0%nat)) (INR n0 + 1))
                            (event_ge dom (rvabs (X 0%nat)) (INR n0))))))
                                / (INR (S x))²))))).
                * rewrite ELim_seq_sum_nneg_nested_swap.
                  -- rewrite ELim_seq_ext with
                         (v := sum_Rbar_n (fun i => Rbar_mult
                  (FiniteExpectation Prts
                   (rvmult (rvsqr (X 0%nat))
                      (EventIndicator
                         (classic_dec
                            (event_inter
                               (event_lt dom (rvabs (X 0%nat)) (INR i + 1))
                               (event_ge dom (rvabs (X 0%nat)) (INR i)))))))
                  (ELim_seq (sum_Rbar_n (fun j => (if (le_dec i j) then 1 else 0)/ (INR (S j))²))))).
                     ++ apply bounded_is_finite with (a := 0) (b := 2 * FiniteExpectation Prts (rvabs (X 0%nat))).
                        --- apply ELim_seq_nneg; intros.
                            apply sum_Rbar_n_pos; intros.
                            apply Rbar_mult_le_nneg.
                            +++ apply FiniteExpectation_pos.        
                                typeclasses eauto.
                            +++ apply ELim_seq_nneg; intros.
                                apply sum_Rbar_n_pos; intros.
                                unfold Rdiv.
                                apply Rmult_le_pos.
                                *** match_destr; lra.
                                *** left; apply Rinv_0_lt_compat.
                                    apply Rlt_0_sqr, INR_nzero; lia.
                        --- apply Rbar_le_trans with
                                (y := ELim_seq
                                        (sum_Rbar_n
                                           (fun i : nat =>
                                              Rbar_mult
                                                (FiniteExpectation 
                                                   Prts
                                                   (rvmult (rvsqr (X 0%nat))
                                                           (EventIndicator
                                                              (classic_dec
                                                                 (event_inter (event_lt dom (rvabs (X 0%nat)) (INR i + 1)) 
                                                                              (event_ge dom (rvabs (X 0%nat)) (INR i)))))))
                                                (2 / (INR (S i)))))).
                            +++ apply ELim_seq_le; intros.
                                apply sum_Rbar_n_le; intros.
                                *** apply Rbar_mult_le_nneg.
                                    ---- apply FiniteExpectation_pos.
                                         typeclasses eauto.
                                    ---- apply ELim_seq_nneg; intros.
                                         apply sum_Rbar_n_pos; intros.
                                         unfold Rdiv.
                                         apply Rmult_le_pos.
                                         **** match_destr; lra.
                                         **** left; apply Rinv_0_lt_compat.
                                              apply Rlt_0_sqr, INR_nzero; lia.
                                *** apply Rbar_mult_le_nneg.
                                    ---- apply FiniteExpectation_pos.
                                         typeclasses eauto.
                                    ---- unfold Rdiv.
                                         apply Rmult_le_pos; try lra.
                                         left; apply Rinv_0_lt_compat.
                                         apply lt_0_INR; lia.
                                *** apply Rbar_mult_le_compat_l.
                                    ---- apply FiniteExpectation_pos.
                                         typeclasses eauto.
                                    ---- apply sum_inv_sq_Elim.
                            +++ assert (forall i,
                                           (rv_le
                                              (rvmult (rvsqr (X 0%nat))
                                                      (EventIndicator
                                                         (classic_dec
                                                            (event_inter (event_lt dom (rvabs (X 0%nat)) (INR i + 1)) 
                                                                         (event_ge dom (rvabs (X 0%nat)) (INR i)))))) 
                                              (rvscale 
                                                 (INR i + 1)
                                                 (rvmult (rvabs (X 0%nat))
                                                         (EventIndicator
                                                            (classic_dec
                                                               (event_inter (event_lt dom (rvabs (X 0%nat)) (INR i + 1)) 
                                                                            (event_ge dom (rvabs (X 0%nat)) (INR i))))))))).
                                {
                                  intros i x.
                                  rv_unfold.
                                  unfold event_inter, event_lt, event_ge, pre_event_inter.
                                  simpl.
                                  match_case; intros; try lra.
                                  destruct a.
                                  do 2 rewrite Rmult_1_r.
                                  rewrite Rsqr_abs.
                                  unfold Rsqr.
                                  apply Rmult_le_compat_r; try lra.
                                  apply Rabs_pos.
                                }
                                assert (forall i,
                                           IsFiniteExpectation 
                                             Prts
                                             (rvmult (rvabs (X 0%nat))
                                                     (EventIndicator
                                                        (classic_dec
                                                           (event_inter (event_lt dom (rvabs (X 0%nat)) (INR i + 1))
                                                                        (event_ge dom (rvabs (X 0%nat)) (INR i))))))).
                                {
                                  intros.
                                  apply IsFiniteExpectation_indicator; trivial.
                                  - typeclasses eauto.
                                  - apply sa_inter.
                                    + simpl.
                                      apply sa_le_lt.
                                      apply rv_measurable.
                                      typeclasses eauto.
                                    + simpl.
                                      apply sa_le_ge.
                                      apply rv_measurable.
                                      typeclasses eauto.
                                }
                                generalize (fun i => FiniteExpectation_le _ _ _ (H12 i)); intros.
                                apply Rbar_le_trans with
                                    (y :=  (ELim_seq
                                              (sum_Rbar_n
                                                 (fun i : nat =>
                                                    2 * 
                                                      (FiniteExpectation 
                                                         Prts
                                                         (rvmult (rvabs (X 0%nat))
                                                                 (EventIndicator
                                                                    (classic_dec
                                                                       (event_inter (event_lt dom (rvabs (X 0%nat)) (INR i + 1)) 
                                                                                    (event_ge dom (rvabs (X 0%nat)) (INR i))))))))))).
                                *** apply ELim_seq_le; intros.
                                    apply sum_Rbar_n_le; intros.
                                    ---- apply Rbar_mult_le_nneg.
                                         ++++ apply FiniteExpectation_pos.
                                              typeclasses eauto.
                                         ++++ unfold Rdiv.
                                              apply Rmult_le_pos; try lra.
                                              left; apply Rinv_0_lt_compat.
                                              apply lt_0_INR; lia.
                                    ---- apply Rmult_le_pos; try lra.
                                         apply FiniteExpectation_pos.
                                         typeclasses eauto.                                         
                                    ---- rewrite S_INR.
                                         apply Rbar_le_trans with
                                             (y := Rbar_mult (FiniteExpectation Prts
          (rvscale (INR n0 + 1)
             (rvmult (rvabs (X 0%nat))
                (EventIndicator
                   (classic_dec
                      (event_inter (event_lt dom (rvabs (X 0%nat)) (INR n0 + 1)) (event_ge dom (rvabs (X 0%nat)) (INR n0))))))))
                                                            (2 / (INR n0 + 1))).
                                         ++++ apply Rbar_mult_le_compat_r.
                                              **** apply Rdiv_le_0_compat; try lra.
                                                   rewrite <- S_INR.
                                                   apply lt_0_INR; lia.
                                              **** apply H14.
                                         ++++ rewrite FiniteExpectation_scale.
                                              right.
                                              field.
                                              rewrite <- S_INR.
                                              apply INR_nzero; lia.
                                *** replace (ELim_seq
       (sum_Rbar_n
          (fun i : nat =>
           2 *
           FiniteExpectation Prts
             (rvmult (rvabs (X 0%nat))
                (EventIndicator
                   (classic_dec
                      (event_inter (event_lt dom (rvabs (X 0%nat)) (INR i + 1)) (event_ge dom (rvabs (X 0%nat)) (INR i)))))))))
                                      with
                                        (Rbar_mult 2 
                                                   (ELim_seq
                                                      (sum_Rbar_n
                                                         (fun i : nat =>
                                                            FiniteExpectation 
                                                              Prts
                                                              (rvmult (rvabs (X 0%nat))
                                                                      (EventIndicator
                                                                         (classic_dec
                                                                            (event_inter (event_lt dom (rvabs (X 0%nat)) (INR i + 1)) (event_ge dom (rvabs (X 0%nat)) (INR i)))))))))).
                                    ---- replace  (Rbar.Finite (2 * FiniteExpectation Prts (rvabs (X 0%nat)))) with
                                             (Rbar_mult 2 (FiniteExpectation Prts (rvabs (X 0%nat)))); [| now simpl].
                                         apply Rbar_mult_le_compat_l; try (simpl; lra).
                                         apply refl_refl.
                                         rewrite <- ELim_seq_incr_1.
                                         erewrite ELim_seq_ext with
                                             (v := fun n => FiniteExpectation 
                                                     Prts
                                                     (rvmult (rvabs (X 0%nat))
                                                             (EventIndicator
                                                                (classic_dec
                                                                   (event_lt dom (rvabs (X 0%nat)) (INR n + 1)))))).
                                         ++++ rewrite Elim_seq_fin.
                                              erewrite <- indicator_lim_seq.
                                              reflexivity.
                                         ++++ intros.
                                              generalize (event_lt_indicator_sum_mult (X 0%nat) (rvabs (X 0%nat)) n); intros.
                                              erewrite (FiniteExpectation_ext_alt _ _ _ H15).
                                              rewrite sum_Rbar_n_finite_sum_n.
                                              apply Rbar_finite_eq.
                                              generalize sum_expectation; intros.
                                              assert (forall n,
                                                         RandomVariable dom borel_sa (rvmult (rvabs (X 0%nat))
          (EventIndicator
             (classic_dec
                (event_inter (event_lt dom (rvabs (X 0%nat)) (INR n + 1))
                             (event_ge dom (rvabs (X 0%nat)) (INR n))))))).
                                              {
                                                intros.
                                                typeclasses eauto.
                                              }  
                                              erewrite sum_expectation.
                                              apply FiniteExpectation_ext.
                                              reflexivity.
                                    ---- rewrite <- ELim_seq_scal_l.
                                         ++++ apply ELim_seq_ext; intros.
                                              rewrite scale_pos_sum_Rbar_n; try lra.
                                              **** apply sum_Rbar_n_proper; trivial.
                                                   intro x.
                                                   now simpl.
                                              **** intros.
                                                   apply FiniteExpectation_pos.
                                                   typeclasses eauto.
                                         ++++ unfold ex_Rbar_mult.
                                              match_destr.
                     ++ intros.
                        apply sum_Rbar_n_proper; trivial.
                        intro x.
                        rewrite ELim_seq_ext with
                            (v := fun n =>
                                    (Rbar_mult
                                       (FiniteExpectation 
                                          Prts
                                          (rvmult (rvsqr (X 0%nat))
                                                  (EventIndicator
                                                     (classic_dec 
                                                        (event_inter (event_lt dom (rvabs (X 0%nat)) (INR x + 1))
                                                                     (event_ge dom (rvabs (X 0%nat)) (INR x)))))))
                                       ((sum_Rbar_n (fun j : nat => (if le_dec x j then 1 else 0) / (INR (S j))²)) n))).
                        ** rewrite ELim_seq_scal_l; trivial.
                           unfold Rdiv.
                           assert (is_finite  (ELim_seq (sum_Rbar_n (fun j : nat => (if le_dec x j then 1 else 0) * / (INR (S j))²)))).
                           {
                             apply bounded_is_finite with (a := 0) (b :=  2 / INR (S x)).
                             - apply ELim_seq_nneg; intros.
                               apply sum_Rbar_n_pos; intros.
                               apply Rmult_le_pos.
                               + match_destr; lra.
                               + left.
                                 apply Rinv_0_lt_compat.
                                 apply Rlt_0_sqr.
                                 apply INR_nzero; lia.
                             - generalize (sum_inv_sq_Elim x); intros.
                               unfold Rdiv in H12.
                               apply H12.
                           }
                           now rewrite <- H12.
                        ** intros.
                           assert (forall j,
                                      Rbar.Finite ((if le_dec x j then 1 else 0) *
                                                   (FiniteExpectation Prts
                                                        (rvmult (rvsqr (X 0%nat))
                                                                (EventIndicator
                                                                   (classic_dec (event_inter (event_lt dom (rvabs (X 0%nat)) (INR x + 1)) (event_ge dom (rvabs (X 0%nat)) (INR x))))))) /
                                                                                                                                                                                        (INR (S j))²) =
                                      Rbar.Finite ((FiniteExpectation Prts
                                                         (rvmult (rvsqr (X 0%nat))
                                                                 (EventIndicator
                                                                    (classic_dec (event_inter (event_lt dom (rvabs (X 0%nat)) (INR x + 1)) (event_ge dom (rvabs (X 0%nat)) (INR x))))))) *
                                      ((if le_dec x j then 1 else 0) / (INR (S j))²))).
                           {
                             intros.
                             apply Rbar_finite_eq.
                             unfold Rdiv.
                             ring.
                           }
                           rewrite (sum_Rbar_n_proper _ _ H12) with (y := n0); trivial.
                           destruct n0.
                           --- unfold sum_Rbar_n.
                               simpl.
                               rewrite Rmult_0_r.
                               reflexivity.
                           --- do 2 rewrite sum_Rbar_n_finite_sum_n.
                               rewrite sum_n_ext with
                                   (b :=  fun x0 : nat =>
                                            scal
                                              (FiniteExpectation 
                                                 Prts
                                                 (rvmult (rvsqr (X 0%nat))
                                                         (EventIndicator
                                                            (classic_dec (event_inter (event_lt dom (rvabs (X 0%nat)) (INR x + 1))
                                                                                      (event_ge dom (rvabs (X 0%nat)) (INR x)))))))
                                              ((if le_dec x x0 then 1 else 0) / (INR (S x0))²)).
                               +++ rewrite sum_n_scal_l.
                                   reflexivity.
                               +++ intros.
                                   now simpl.
                  -- intros.
                     apply Rmult_le_pos.
                     ++ apply Rmult_le_pos.
                        ** match_destr;lra.
                        ** apply FiniteExpectation_pos.
                           typeclasses eauto.
                     ++ left; apply Rinv_0_lt_compat.
                        apply Rlt_0_sqr.
                        apply INR_nzero; lia.
                * intros.
                  apply sum_Rbar_n_proper; trivial.
                  intro x.
                  generalize (ELim_seq_ind_le (fun n0 : nat =>
                                                 FiniteExpectation Prts
                                                                   (rvmult (rvsqr (X 0%nat))
                                                                           (EventIndicator
                                                                              (classic_dec
                                                                                 (event_inter (event_lt dom (rvabs (X 0%nat)) (INR n0 + 1)) (event_ge dom (rvabs (X 0%nat)) (INR n0)))))) /
                                                                   (INR (S x))²) x); intros.
                  rewrite ELim_seq_ext with
                      (v :=  (sum_Rbar_n
             (fun n0 : nat =>
              (if le_dec n0 x then 1 else 0) *
              (FiniteExpectation Prts
                 (rvmult (rvsqr (X 0%nat))
                    (EventIndicator
                       (classic_dec
                          (event_inter (event_lt dom (rvabs (X 0%nat)) (INR n0 + 1)) (event_ge dom (rvabs (X 0%nat)) (INR n0)))))) /
               (INR (S x))²)))).
                  -- rewrite H12.
                     unfold Rdiv.
                     rewrite sum_n_Rscal_r.
                     now unfold Rdiv.
                  -- intros; apply sum_Rbar_n_proper; trivial.
                     intro z.
                     apply Rbar_finite_eq.
                     unfold Rdiv.
                     ring.
            }
            revert H12.
            apply ex_series_ext.
            intros.
            rewrite H11.
            f_equal.
            apply FiniteExpectation_ext; intro x.
            f_equal.
      }
      revert H0.
      apply almost_impl, all_almost.      
      unfold impl; intros.
      generalize (ash_6_1_3_strong (x := (fun k => (Y k x - (FiniteExpectation Prts (Y k)))/(INR (S k)))) (b := (fun k => INR (S k)))); intros.
      cut_to H1; trivial.
      - revert H1.
        apply is_lim_seq_ext.
        intros.
        f_equal.
        apply sum_n_ext.
        intros.
        rewrite Rmult_comm.
        unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite Rinv_l; try lra.
        apply INR_nzero; lia.
      - intros.
        split.
        + apply lt_0_INR; lia.
        + apply le_INR; lia.
      - apply is_lim_seq_ext with (u := fun k => INR k + 1).
        + intro; now rewrite S_INR.
        + apply is_lim_seq_plus with (l1 := p_infty) (l2 := 1).
          * apply is_lim_seq_INR.
          * apply is_lim_seq_const.
          * unfold is_Rbar_plus; now simpl.
    }

    assert (limsumy:almost Prts (fun omega : Ts => is_lim_seq (fun n : nat => rvsum Y n omega / INR (S n)) 0)).
    {
      assert (limexpysum: is_lim_seq (fun n => (sum_n (fun k => FiniteExpectation Prts (Y k)) n)/(INR (S n))) 0) by now apply lim_sum_0.
      revert limsumyexp.
      apply almost_impl, all_almost.
      unfold impl; intros.
      generalize (is_lim_seq_plus _ _ _ _ 0 H0 limexpysum); intros.
      cut_to H1.
      - revert H1.
        apply is_lim_seq_ext.
        intros.
        unfold rvsum.
        rewrite <- Rdiv_plus_distr.
        f_equal.
        rewrite <- sum_n_Rplus.
        apply sum_n_ext.
        intros.
        lra.
      - unfold is_Rbar_plus.
        simpl.
        now rewrite Rplus_0_r.
    }
    generalize (Borel_Cantelli Prts (fun n => event_ge dom (rvabs (X n)) (INR n + 1))); intros.
    cut_to H0.
    - 
      assert (almost Prts (fun omega =>
                             exists N, forall n, (N <= n)%nat ->
                                                 X n omega = Y n omega)).
      {
        generalize (BC_exist_N_not_ge X (fun k => INR k + 1) _ H0).
        apply almost_impl, all_almost.
        unfold impl; intros.
        destruct H1.
        exists x0; intros.
        specialize (H1 n H2).
        subst Y; simpl.
        unfold rvmult, EventIndicator, rvabs.
        match_destr; try lra.
        unfold rvabs in H1; lra.
      }
      revert H1.
      apply almost_impl.
      revert limsumy.
      apply almost_impl.
      apply all_almost.
      unfold impl; intros.
      destruct H2.
      unfold rvsum, sum_n.
      unfold rvsum, sum_n in H1.
      rewrite lim_avg_tails with (N := x0).
      rewrite lim_avg_tails with (N := x0) in H1.
      apply is_lim_seq_ext_loc with
          (u := (fun n : nat => sum_n_m (fun n0 : nat => Y n0 x) x0 n / INR (S n)) ); trivial.
      exists x0; intros.
      f_equal.
      apply sum_n_m_ext_loc.
      intros.
      now rewrite H2.
    - generalize (RandomVariableFinite.IsFiniteExpectation_abs Prts (X 0%nat) (isfe 0%nat)); intros.
      generalize (IsFiniteNonnegExpectation Prts (rvabs (X 0%nat))); intros.
      rewrite <- H2 in H.
      rewrite <- FiniteNonnegExpectation with (isfeX := H1) in H.
      rewrite <- ex_finite_lim_series.
      apply lim_sum_abs_bounded.
      rewrite Lim_seq_ext with (v := (sum_n (fun n : nat => (ps_P (event_ge dom (rvabs (X n)) (INR n + 1)))))).
      + apply bounded_is_finite with (a := 0) (b := (@FiniteExpectation _ _ Prts (rvabs (X 0%nat)) H1)); trivial.
        apply Lim_seq_pos; intros.
        apply sum_n_nneg; intros.
        apply ps_pos.
      + intros.
        apply sum_n_ext; intros.
        rewrite Rabs_right; trivial.
        apply Rle_ge.
        apply ps_pos.
        Unshelve.
        intros.
        apply IsFiniteExpectation_indicator; trivial.
        * typeclasses eauto.
        * apply sa_le_lt.
          intros.
          apply rv_measurable.
          typeclasses eauto.
  Qed.

End slln_extra.
