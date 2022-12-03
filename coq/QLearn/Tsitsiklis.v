Require Import List.
Require Import mdp qvalues fixed_point.
Require Import RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import infprod Dvoretzky Expectation RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import RandomVariableL2.
Require Import ConditionalExpectation VectorConditionalExpectation.
Require Import IndefiniteDescription ClassicalDescription.
Require Import RelationClasses.
Require Import qlearn qlearn_redux Dvoretzky infprod.
Require Import Martingale MartingaleStopped.

Set Bullet Behavior "Strict Subproofs".

Context {Ts : Type} (β γ : R) (w α : Ts -> nat -> R) 
        {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

Lemma isfe_condexp_sqr_bounded (dom2 : SigmaAlgebra Ts) (sub2: sa_sub dom2 dom) (B : R) 
      (w : Ts -> R)
      {rv : RandomVariable dom borel_sa w} :
  Rbar_rv_le
    (ConditionalExpectation _ sub2 (rvsqr w))
    (const (Rsqr B)) ->
  IsFiniteExpectation prts (rvsqr w).
Proof.
  intros.
  assert (Rbar_IsFiniteExpectation prts (ConditionalExpectation _ sub2 (rvsqr w))).
  {
    apply Rbar_IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const (Rsqr B)); trivial.
    - apply Rbar_IsFiniteExpectation_const.
    - apply Rbar_IsFiniteExpectation_const.
    - intros ?.
      apply Condexp_nneg.
      typeclasses eauto.
  }
  generalize (Condexp_cond_exp_nneg prts sub2 (rvsqr w)); intros.
  apply is_conditional_expectation_FiniteExpectation in H1.
  now apply H1.
Qed.

Lemma isfe_rsqr (w : Ts -> R) 
      {rv : RandomVariable dom borel_sa w} :
  IsFiniteExpectation prts (rvsqr w) ->
  IsFiniteExpectation prts w.
Proof.
  now apply IsFiniteExpectation_rvsqr_lower.
Qed.

Lemma condexp_sqr_bounded (dom2 : SigmaAlgebra Ts) (sub2: sa_sub dom2 dom) (B : R) 
      (w : Ts -> R)
      {rv : RandomVariable dom borel_sa w} :
  Rbar_rv_le
    (ConditionalExpectation _ sub2 (rvsqr w))
    (const (Rsqr B)) ->
  Rbar_le
    (NonnegExpectation (rvsqr w))
    (Rsqr B).
  Proof.
    generalize (Condexp_cond_exp_nneg prts sub2 (rvsqr w)); intros.
    apply is_conditional_expectation_Expectation in H.
    erewrite Expectation_pos_pofrf in H.
    erewrite Rbar_Expectation_pos_pofrf in H.
    invcs H.
    rewrite H2.
    erewrite <- (Rbar_NonnegExpectation_const' prts (Rsqr B)).
    - now apply Rbar_NonnegExpectation_le.
    - apply Rle_0_sqr.
      Unshelve.
      + apply Condexp_nneg.
        typeclasses eauto.
      + intros ?.
        apply Rle_0_sqr.
  Qed.

Lemma lemma1_bounded (α w W : nat -> Ts -> R) (C B : R) 
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} :  
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rle (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (const B)) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) ->
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almostR2 prts Rle (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const C)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (α n ω) * (w n ω)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  Admitted.

 Definition process_swap (Y Z : nat -> Ts -> R) (T:Ts -> option nat) (n:nat) (x : Ts) : R
   := match (T x) with
      | None => Y n x
      | Some b =>
        if (lt_dec n b)%nat then Y n x else Z n x
      end.

Lemma lemma1 (α w B W : nat -> Ts -> R) (W0 C : R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {adaptB : IsAdapted borel_sa B F}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} :  
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rle (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (B n)) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) ->
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almostR2 prts Rle (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const C)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (α n ω) * (w n ω)) ->
  (almost prts (fun ω => exists (b:R), forall n, B n ω <= b)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  intros.
  unfold IsAdapted in adaptB.
  assert (forall j t,
             (j <= t)%nat ->
             RandomVariable (F t) borel_sa (B j)).
  {
    intros.
    assert (sa_sub (F j) (F t)).
    {
      now apply is_filtration_le.
    }
    now apply (RandomVariable_sa_sub H8).
  }
(*  pose (tau_coll k t j :=
          if le_dec j t then event_lt (F t) (B j) (INR k) else Ω). *)
  pose (tau_coll k t j :=
          if le_dec j t then event_lt (F t) (B t) (INR k) else Ω).
  pose (tau_int k t := inter_of_collection (tau_coll k t)).

  pose (IB k t := EventIndicator (classic_dec (tau_int k t))).
  assert (forall k t,
             RandomVariable dom borel_sa (rvmult (rvsqr (w t)) (IB k t))).
  {
    intros.
    apply rvmult_rv.
    - typeclasses eauto.
    - apply (RandomVariable_sa_sub (filt_sub t)).
      apply EventIndicator_rv with (dom := F t).
  }
  assert (forall k t,
             almostR2 prts Rle
                      (ConditionalExpectation 
                         prts (filt_sub t) 
                         (rvmult (rvsqr (w t)) (IB k t)))
                      (const (INR k))).
  {
    intros.
    apply almost_forall in H0.
    red in H0.
    assert (RandomVariable (F t) borel_sa (IB k t)).
    {
      unfold IB.
      generalize (@EventIndicator_rv Ts (F t) (tau_int k t)); intros.
      apply EventIndicator_rv with (dom := F t).
    }
    assert (isfef: IsFiniteExpectation prts (rvsqr (w t))) by admit.
    assert (isfefg : IsFiniteExpectation prts
             (rvmult (rvsqr (w t)) (IB k t))).
    {
      apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := (rvsqr (w t))); trivial.
      - apply IsFiniteExpectation_const.
      - intros ?.
        unfold const, rvmult, rvsqr, IB.
        apply Rmult_le_pos.
        + apply Rle_0_sqr.
        + apply EventIndicator_pos.
      - intros ?.
        rv_unfold.
        unfold IB, EventIndicator.
        match_destr; try lra.
        rewrite Rmult_0_r.
        apply Rle_0_sqr.
    }
    generalize (Condexp_factor_out prts (filt_sub t) 
                                   (rvsqr (w t)) (IB k t)); intros.
    apply almostR2_prob_space_sa_sub_lift in H10.
    revert H10.
    apply almost_impl.
    revert H0.
    apply almost_impl, all_almost.
    unfold impl; intros.
    rewrite H10.
    unfold IB, tau_int, Rbar_rvmult, tau_coll, EventIndicator.
    match_destr.
    - rewrite Rbar_mult_1_l.
      simpl in e.
      specialize (e t).
      unfold proj1_sig in e.
      destruct (le_dec t t); try lia.
      simpl in e.
      red in H0.
      specialize (H0 t).
      unfold const.
      eapply Rle_trans.
      apply H0.
      now left.
    - rewrite Rbar_mult_0_l.
      unfold const.
      apply pos_INR.
  }

  assert (almost prts (fun ω => exists k, forall t,
                             IB k t ω = 1)).
  {
    revert H6.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H6.
    exists (Z.to_nat (up x0)).
    intros.
    unfold IB, tau_int, tau_coll, EventIndicator.
    match_destr.
    red in n.
    
  Admitted.


Lemma lemma2_part1 (W : Ts -> nat -> nat -> R) (ω : Ts) :
  (forall t0, W ω 0%nat t0 = 0) ->
  (forall t0 t,
      W ω (S t) t0 =
      (1 - α ω (t + t0)%nat) * (W ω t t0) +
      (α ω (t + t0)%nat) * (w ω (t + t0)%nat)) ->
  forall t0 t,
    W ω ((S t) + t0)%nat 0%nat = (prod_f_R0 (fun k => 1 - α ω (k + t0)%nat)
                                                t) * (W ω t0 0%nat)  + (W ω (S t) t0).
  Proof.
    intros.
    revert t0.
    induction t.
    - intros.
      rewrite H0, H0, H.
      rewrite Nat.add_0_r.
      simpl; lra.
    - intros.
      replace (S (S t) + t0)%nat with (S (S t + t0)) by lia.
      rewrite H0, H0, IHt.
      rewrite Nat.add_0_r.
      simpl; lra.
  Qed.

   Lemma prod_f_R0_le_1 {f : nat -> R} :
     (forall n, 0 <= f n <= 1) ->
     forall k, prod_f_R0 f k <= 1.
    Proof.
      intros Hf k.
      induction k; simpl.
      - apply Hf.
      - replace 1 with (1 * 1) by lra.
        apply Rmult_le_compat; trivial; try apply Hf.
        apply prod_f_R0_nonneg.
        intros.
        apply Hf.
   Qed.

Lemma lemma2_part2 (W : Ts -> nat -> nat -> R) (ω : Ts) :
  (forall t0, W ω 0%nat t0 = 0) ->
  (forall t, 0 <= α ω t <= 1) ->
  (forall t0 t,
      W ω (S t) t0 =
      (1 - α ω (t + t0)%nat) * (W ω t t0) +
      (α ω (t + t0)%nat) * (w ω (t + t0)%nat)) ->
  forall t0 t,
    Rabs (W ω t t0) <= Rabs (W ω (t + t0)%nat 0%nat) +
                           Rabs (W ω t0 0%nat).
Proof.
  intros.
  destruct t.
  - rewrite H, Rabs_R0.
    apply Rplus_le_le_0_compat; apply Rabs_pos.
  - generalize (lemma2_part1 W ω H H1 t0 t); intros.
    assert (W ω (S t) t0 =
            W ω (S t + t0)%nat 0%nat -
            prod_f_R0 (fun k : nat => 1 - α ω (k + t0)) t * W ω t0 0%nat).
    {
      rewrite H2.
      lra.
    }
    rewrite H3.
    unfold Rminus at 1.
    eapply Rle_trans.
    + apply Rabs_triang.
    + apply Rplus_le_compat_l.
      rewrite Rabs_Ropp.
      rewrite <- Rmult_1_l.
      rewrite Rabs_mult.
      apply Rmult_le_compat_r.
      * apply Rabs_pos.
      * rewrite Rabs_right.
        -- apply prod_f_R0_le_1.
           intros.
           specialize (H0 (n + t0)%nat).
           lra.
        -- apply Rle_ge.
           apply prod_f_R0_nonneg.
           intros.
           specialize (H0 (n + t0)%nat).
           lra.
  Qed.

Lemma lemma2 (W : Ts -> nat -> nat -> R) (ω : Ts) :
  (forall t0, W ω 0%nat t0 = 0) ->
  (forall t , 0 <= α ω t <= 1) ->
  (forall t0 t,
      W ω (S t) t0 =
      (1 - α ω (t + t0)%nat) * (W ω t t0) +
      (α ω (t + t0)%nat) * (w ω (t + t0)%nat)) ->
  is_lim_seq (fun n => W ω n 0%nat) 0 ->
  forall (delta : posreal),
  exists (T : nat),
  forall t0 t,
    (t0 >= T)%nat ->
    Rabs (W ω t t0) <= delta.
 Proof.
   intros.
   generalize (lemma2_part2 W ω H H0 H1 ); intros.
   apply is_lim_seq_spec in H2.
   assert (0 < delta/2).
   {
     generalize (cond_pos delta); intros.
     lra.
   }
   specialize (H2 (mkposreal _ H4)).
   unfold eventually in H2.
   destruct H2 as [T ?].
   exists T.
   intros.
   specialize (H3 t0 t).
   eapply Rle_trans.
   - apply H3.
   - replace (pos delta) with ((delta/2) + (delta/2)) by lra.
     apply Rplus_le_compat.
     + simpl in H2.
       specialize (H2 (t + t0)%nat).
       rewrite Rminus_0_r in H2.
       left.
       apply H2.
       lia.
     + simpl in H2.
       specialize (H2 t0).
       rewrite Rminus_0_r in H2.
       left.
       apply H2.
       lia.
 Qed.

 Lemma lemma8_part1 (x Y W : Ts -> nat -> R) (D : posreal) (ω : Ts) :
   (Y ω 0%nat = D) ->
   (W ω 0%nat = 0) ->   
   (forall t, 0 <= α ω t <= 1) ->
   (forall t,
       W ω (S t) =
       (1 - α ω t) * (W ω t) +
       (α ω t) * (w ω t)) ->
   (forall t,
       Y ω (S t) =
       (1 - α ω t) * (Y ω t) +
       (α ω t) * β * D) ->
   (forall t,
     x ω (S t) <= 
     (1 - α ω t) * (x ω t) + 
     (α ω t) * (β * D + w ω t)) ->
   (forall t,
       Rabs (x ω t) <= D) ->
   forall t,
     x ω t <= (Y ω t) + (W ω t).
 Proof.
   intros.
   induction t; intros.
   - rewrite H, H0.
     rewrite Rplus_0_r.
     specialize (H5 0%nat).
     rewrite Rabs_le_between in H5.
     lra.
   - rewrite H2, H3.
     eapply Rle_trans.
     apply H4.
     apply Rmult_le_compat_l with (r := 1 - α ω t) in IHt.
     apply Rplus_le_compat_r with (r := α ω t * (β * D + w ω t)) in IHt.
     + eapply Rle_trans.
       * apply IHt.
       * lra.
     + specialize (H1 t).
       lra.
  Qed.
     
 Lemma lemma8_almost_part1  (x Y W : Ts -> nat  -> R) (D : posreal) :
   (forall ω, Y ω 0%nat = D) ->
   (forall ω, W ω 0%nat = 0) ->   
   (forall ω t, 0 <= α ω t <= 1) ->
   (forall ω t,
       W ω (S t) =
       (1 - α ω t) * (W ω t) +
       (α ω t) * (w ω t)) ->
   (forall ω t,
       Y ω (S t) =
       (1 - α ω t) * (Y ω t) +
       (α ω t) * β * D) ->
   (almost prts
           (fun ω =>
              forall t,
                 Rabs (x ω t) <=  D)) ->

   (almost prts
           (fun ω =>
              forall t,
                 (x ω (S t)) <=
                 ((1 - α ω t) * (x ω t) + 
                  (α ω t) * (β * D + w ω t)))) ->
   almost prts
          (fun ω =>
             forall t,
               (x ω t) <= (Y ω t) + (W ω t)).
 Proof.
   intros.
   revert H5.
   apply almost_impl.
   revert H4.
   apply almost_impl; red.
   apply all_almost.
   unfold impl.
   intros.
   apply (lemma8_part1 x Y W D x0); trivial.
 Qed.

 Lemma lemma8_part2 (x Y W : Ts -> nat -> R) (D : posreal) (ω : Ts):
   (Y ω 0%nat = D) ->
   (W ω 0%nat = 0) ->   
   (forall t, 0 <= α ω t <= 1) ->
   (forall t,
       W ω (S t) =
       (1 - α ω t) * (W ω t) +
       (α ω t) * (w ω t)) ->
   (forall t,
       Y ω (S t) =
       (1 - α ω t) * (Y ω t) +
       (α ω t) * β * D) ->
   (forall t,
       Rabs (x ω t) <= D) ->
   (forall t,
      x ω (S t) >= 
       (1 - α ω t) * (x ω t) + 
       (α ω t) * (-β * D + w ω t)) ->
   forall t,
      (- Y ω t) + (W ω t) <= x ω t.
 Proof.
   intros.
   induction t; intros.
   - rewrite H, H0.
     specialize (H4 0%nat).
     rewrite Rplus_0_r.
     rewrite Rabs_le_between in H4.
     lra.
   - rewrite H2, H3.
     eapply Rle_trans.
     shelve.
     apply Rge_le.
     apply H5.
     Unshelve.
     apply Rmult_le_compat_l with (r := 1 - α ω t) in IHt.
     apply Rplus_le_compat_r with (r := α ω t * (-β * D + w ω t)) in IHt.
     + eapply Rle_trans.
       shelve.
       apply IHt.
       Unshelve.
       lra.
     + specialize (H1 t).
       lra.
  Qed.
     
 Lemma lemma8_almost_part2  (x Y W : Ts -> nat  -> R) (D : posreal) :
   (forall ω, Y ω 0%nat = D) ->
   (forall ω, W ω 0%nat = 0) ->   
   (forall ω t, 0 <= α ω t <= 1) ->
   (forall ω t,
       W ω (S t) =
       (1 - α ω t) * (W ω t) +
       (α ω t) * (w ω t)) ->
   (forall ω t,
       Y ω (S t) =
       (1 - α ω t) * (Y ω t) +
       (α ω t) * β * D) ->
   (almost prts
           (fun ω =>
              forall t,
                 Rabs (x ω t) <=  D)) ->

   (almost prts
           (fun ω =>
              forall t,
                x ω (S t) >= 
                (1 - α ω t) * (x ω t) + 
                (α ω t) * (-β * D + w ω t))) ->
   almost prts
          (fun ω =>
             forall t,
               (- Y ω t) + (W ω t) <= x ω t).
 Proof.
   intros.
   revert H5.
   apply almost_impl.
   revert H4.
   apply almost_impl; red.
   apply all_almost.
   unfold impl.
   intros.
   apply (lemma8_part2 x Y W D x0); trivial.
 Qed.

 Lemma lemm8_abs  (x Y W : Ts -> nat -> R) (D : posreal) (ω : Ts) :
   (Y ω 0%nat = D) ->
   (W ω 0%nat = 0) ->   
   (forall t, 0 <= α ω t <= 1) ->
   (forall t,
       W ω (S t) =
       (1 - α ω t) * (W ω t) +
       (α ω t) * (w ω t)) ->
   (forall t,
       Y ω (S t) =
       (1 - α ω t) * (Y ω t) +
       (α ω t) * β * D) ->
   (forall t,
     x ω (S t) <= 
     (1 - α ω t) * (x ω t) + 
     (α ω t) * (β * D + w ω t)) ->
   (forall t,
     x ω (S t) >= 
     (1 - α ω t) * (x ω t) + 
     (α ω t) * (-β * D + w ω t)) ->
   (forall t,
       Rabs (x ω t) <= D) ->
   forall t,
     Rabs (x ω t) <= Rabs (W ω t) + (Y ω t).
 Proof.
   intros.
   assert (Rabs (x ω t - W ω t) <=  Y ω t).
   {
     apply Rabs_le_between.
     split.
     - apply Rplus_le_reg_r with (r := (W ω t)).
       ring_simplify.
       now apply lemma8_part2 with (D := D).
     - apply Rplus_le_reg_r with (r := (W ω t)).
       ring_simplify.
       rewrite Rplus_comm.
       now apply lemma8_part1 with (D := D).
   }
   apply Rplus_le_reg_r with (r := - Rabs (W ω t)).
   ring_simplify.
   apply Rle_trans with (r2 := Rabs (x ω t - W ω t) ); trivial.
   apply Rabs_triang_inv.
  Qed.

 Lemma lemm8_abs_part2  (x Y W : Ts -> nat -> R) (eps D : posreal) (ω : Ts) :
   (forall t, 0 <= α ω t <= 1) ->
   (W ω 0%nat = 0) ->
   (forall t,
       W ω (S t) =
       (1 - α ω t) * (W ω t) +
       (α ω (t)%nat) * (w ω (t)%nat)) ->
   (forall t,
       Rabs (x ω t) <= Rabs (W ω t) + (Y ω t)) ->
   is_lim_seq (Y ω) (β * D) ->
   is_lim_seq (W ω) 0 ->   
   (exists (T : nat),
       forall t,
         (t >= T)%nat ->
         Rabs (W ω t) <= β * eps * D) ->
   Rbar_le (LimSup_seq (fun t => Rabs (x ω t))) (β * (1 + eps) * D).
 Proof.
   intros.
   eapply Rbar_le_trans.
   - apply LimSup_le.
     exists 0%nat.
     intros.
     apply H2.
   - eapply Rbar_le_trans.
     + apply LimSup_le with (v := fun t => β * eps * D + (Y ω t)).
       destruct H5.
       exists x0.
       intros.
       apply Rplus_le_compat_r.
       apply H5.
       lia.
     + assert (is_LimSup_seq  (fun t : nat => β * eps * D + Y ω t) (β * eps * D + β * D)).
       {
         apply is_lim_LimSup_seq.
         apply is_lim_seq_plus with (l1 := β * eps * D) (l2 := β * D); trivial.
         - apply is_lim_seq_const.
         - red.
           simpl.
           f_equal.
       }
       apply is_LimSup_seq_unique in H6.
       rewrite H6.
       simpl.
       lra.
  Qed.

 Lemma Y_prod (Y : Ts -> nat -> R) (D β : nonnegreal) :
   β < 1 ->
   (forall ω, Y ω 0%nat = D) ->
   (forall ω t, 0 <= α ω t <= 1) ->
   (forall ω t,
       Y ω (S t) =
       (1 - α ω t) * (Y ω t) +
       (α ω t) * β * D) ->
   forall ω t,
     Y ω (S t) = prod_f_R0 (fun k => 1 - α ω k) t * ((1 - β) * D) + β * D.
  Proof.
    intros.
    induction t.
    - rewrite H2, H0.
      simpl.
      lra.
    - rewrite H2, IHt.
      simpl.
      lra.
  Qed.

  Lemma sum_inf_prod_0_lt1 (a : nat -> R) :
    (forall n, 0 <= a n < 1) ->
    is_lim_seq (sum_n a) p_infty ->
    is_lim_seq (prod_f_R0 (fun k => 1 - a k)) 0.
  Proof.
    intros.
    generalize (Fprod_0 a H H0); intros.
    apply is_lim_seq_ext with (v :=  (prod_f_R0 (fun k : nat => 1 - a k))) in H1; trivial.
    intros.
    induction n.
    - unfold part_prod, part_prod_n, g_alpha.
      simpl; lra.
    - simpl.
      unfold part_prod.
      rewrite part_prod_n_S; [|lia].
      unfold part_prod in IHn.
      rewrite IHn.
      reflexivity.
  Qed.
    
  Lemma exp_sum_prod_f_R0 (a : nat -> R) (n : nat) :
    exp(sum_n a n) = prod_f_R0 (fun j => exp (a j)) n.
  Proof.
    induction n.
    - simpl.
      now rewrite sum_O.
    - simpl.
      rewrite sum_Sn.
      unfold plus; simpl.
      rewrite exp_plus.
      now rewrite IHn.
  Qed.

  Lemma series_sq_finite_lim_0 (a : nat -> R) :
    ex_series (fun n => Rsqr (a n)) ->
    is_lim_seq a 0.
  Proof.
    intros.
    apply ex_series_lim_0 in H.
    apply is_lim_seq_spec in H.
    apply is_lim_seq_spec.
    unfold is_lim_seq' in *.
    intros.
    assert (0 < Rsqr eps).
    {
      unfold Rsqr.
      generalize (cond_pos eps); intros.
      now apply Rmult_lt_0_compat.
    }
    specialize (H (mkposreal _ H0)).
    destruct H.
    exists x.
    intros.
    rewrite Rminus_0_r.
    specialize (H n H1).
    rewrite Rminus_0_r in H.
    simpl in H.
    rewrite Rabs_right in H.
    - apply Rsqr_lt_abs_0 in H.
      rewrite (Rabs_right eps) in H; trivial.
      generalize (cond_pos eps); lra.
    - apply Rle_ge, Rle_0_sqr.
  Qed.

  Lemma sum_inf_prod_0 (a : nat -> R) :
    (forall n, 0 <= a n <= 1) ->
    is_lim_seq (sum_n a) p_infty ->
    is_lim_seq (prod_f_R0 (fun k => 1 - a k)) 0.
  Proof.
    intros.
    assert (forall n, 0 <= 1 - a n).
    {
      intros.
      specialize (H n); lra.
    }
    assert (forall n, 1 - a n <= exp(- a n)).
    {
      intros.
      apply exp_ineq.
    }
    generalize (prod_f_R0_nonneg H1); intros.
    apply is_lim_seq_le_le with (u := fun _ => 0) (w := prod_f_R0 (fun n => exp (- a n))).
    - intros.
      split; trivial.
      apply prod_SO_Rle.
      intros.
      split; [apply H1 | apply H2].
    - apply is_lim_seq_const.
    - apply is_lim_seq_ext with (u := fun n => exp (- sum_n a n)).
      + intros.
        rewrite Ropp_sum_Ropp.
        rewrite Ropp_involutive.
        apply exp_sum_prod_f_R0.
      + apply is_lim_seq_spec; unfold is_lim_seq'.
        intros; unfold eventually.
        assert (is_lim_seq (fun n => - sum_n a n) m_infty).
        {
          apply is_lim_seq_opp.
          apply (is_lim_seq_ext (sum_n a)).
          - intros.
            now rewrite Ropp_involutive.
          - now simpl.
        }
        apply is_lim_seq_spec in H4; unfold is_lim_seq' in H4.
        unfold eventually in H4.
        specialize (H4 (ln eps)); destruct H4.
        exists x; intros.
        specialize (H4 n H5).
        rewrite Rminus_0_r, Rabs_right by (left; apply exp_pos).
        replace (pos eps) with (exp (ln eps)); [| apply exp_ln, cond_pos].
        now apply exp_increasing.
   Qed.

  Lemma Y_lim (Y : Ts -> nat -> R) (D β : nonnegreal) :
    β < 1 ->
    (forall ω, Y ω 0%nat = D) ->
    (forall ω t, 0 <= α ω t <= 1) ->
    (forall ω, is_lim_seq (sum_n (α ω)) p_infty) ->
    (forall ω t,
        Y ω (S t) =
        (1 - α ω t) * (Y ω t) +
        (α ω t) * β * D) ->
    forall ω,
      is_lim_seq (Y ω) (β * D).
  Proof.
    intros.
    apply is_lim_seq_incr_1.
    apply is_lim_seq_ext with (u := fun t =>  prod_f_R0 (fun k : nat => 1 - α ω k) t * ((1 - β) * D) + β * D).
    - intros.
      rewrite Y_prod with (D := D) (β := β); trivial; lra.
    - apply is_lim_seq_plus with (l1 := 0) (l2 := β * D).
      + apply is_lim_seq_mult with (l1 := 0) (l2 := (1 - β) * D).
        * apply sum_inf_prod_0; trivial.
        * apply is_lim_seq_const.
        * red.
          unfold Rbar_mult'.
          f_equal.
          now rewrite Rmult_0_l.
      + apply is_lim_seq_const.
      + red.
        unfold Rbar_plus'.
        f_equal.
        now rewrite Rplus_0_l.
 Qed.


  Lemma W_lim (W w : Ts -> nat -> R) 
        {F : nat -> SigmaAlgebra Ts} 
        (isfilt : IsFiltration F) 
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptZ : IsAdapted borel_sa (fun n ω => W ω n) F}
        (adapt_alpha : IsAdapted borel_sa (fun n ω => α ω n) F) 
        {rvBB : forall n, RandomVariable dom borel_sa (fun ω => w ω n)}
        {rvalpha : forall n, RandomVariable dom borel_sa (fun ω => α ω n)}  :
    β < 1 ->
    (forall n : nat,
        almost (prob_space_sa_sub prts (filt_sub n))
          (fun x : Ts =>
           ConditionalExpectation prts (filt_sub n) (fun ω : Ts => w ω n) x =
           const 0 x)) ->
   (forall ω, W ω 0%nat = 0) ->   
   (forall ω t, 0 <= α ω t <= 1) ->
   (forall ω t,
       W ω (S t) =
       (1 - α ω t) * (W ω t) +
       (α ω t) * (w ω t)) ->
   almost prts (fun ω => is_lim_seq (sum_n (α ω)) p_infty) ->
   (exists C : R,
     almost prts
            (fun ω : Ts =>
               Rbar_lt (Lim_seq (sum_n (fun n : nat => Rsqr (α ω n))))
                       C)) ->
   almost prts (fun ω => is_lim_seq (W ω) 0).
  Proof.
    intros.
    generalize (Dvoretzky_converge_Z prts (fun n ω => W ω n) (fun n ω => w ω n)
                                     (fun n ω => α ω n) isfilt filt_sub
                                     adapt_alpha); intros.
    apply H6; trivial.
    - intros.
      specialize (H2 x n); lra.
    - intros.
      specialize (H2 x n); lra.
    - admit.
    - intros ??.
      rewrite H3.
      rv_unfold.
      lra.
Admitted.

