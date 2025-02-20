Require Import List EquivDec Morphisms.
Require Import mdp qvalues fixed_point pmf_monad.
Require Import RealAdd CoquelicotAdd EquivDec.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import infprod Dvoretzky Expectation RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace ProductSpace.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import RandomVariableL2.
Require Import ConditionalExpectation VectorConditionalExpectation DiscreteProbSpace.
Require Import IndefiniteDescription ClassicalDescription.
Require Import RelationClasses.
Require Import Dvoretzky infprod uniform_converge.
Require Import Martingale MartingaleStopped.
Require Import FiniteTypeVector.
Require Import ProductSpaceDep.

Set Bullet Behavior "Strict Subproofs".

Section Stochastic_convergence.
  
Context {Ts : Type} {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

Lemma lemma1_bounded_alpha_beta (α β w W : nat -> Ts -> R) (Ca Cb B : R) 
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F} :    
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (const (Rsqr B))) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
(*  (forall n x, 0 <= α n x) -> *)
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) -> 
(*  (forall n x, 0 <= 1 - α n x )  -> *)
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->  
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  intros.
  assert (IsAdapted borel_sa W F).
  {
    intros ?.
    induction n.
    - trivial.
    - specialize (H8 n).
      assert (RandomVariable (F (S n)) borel_sa
                    (rvplus (rvmult (rvminus (const 1) (α n)) (W n))
                       (rvmult (β n) (w n)))).
      {
        apply rvplus_rv.
        - apply rvmult_rv.
          + apply rvminus_rv.
            * apply rvconst.
            * apply (RandomVariable_sa_sub (isfilt n)).
              apply adapta.
          + now apply (RandomVariable_sa_sub (isfilt n)).
        - apply rvmult_rv; trivial.
          now apply (RandomVariable_sa_sub (isfilt n)).
      }
      revert H9.
      apply RandomVariable_proper; try easy.
      intros ?.
      rewrite H8.
      rv_unfold.
      lra.
  }
  generalize (Dvoretzky_converge_W_alpha_beta W w α β isfilt filt_sub); intros dvor.
  eapply dvor; trivial.
  - intros.
    now apply (RandomVariable_sa_sub (filt_sub n)).
  - intros.
    now apply (RandomVariable_sa_sub (filt_sub n)).
  - exists B.
    apply H0.
  - exists (Cb + 1).
    revert H7.
    apply almost_impl, all_almost.
    unfold impl; intros.
    eapply Rbar_le_lt_trans.
    apply H7.
    unfold const; simpl.
    lra.
  - intros ??.
    specialize (H8 n a).
    rv_unfold.
    lra.
 Qed.

Lemma lemma1_bounded_alpha_beta_uniform (α β w W : nat -> Ts -> R) (B : R) 
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F} :    
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (const (Rsqr B))) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) -> 
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->  
  almost prts (fun ω => ex_series (fun n => Rsqr (β n ω))) ->
  (exists epsilon : posreal, eventually (fun n => almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (β (nn+n)%nat) ω))) (const epsilon))) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  intros.
  assert (IsAdapted borel_sa W F).
  {
    intros ?.
    induction n.
    - trivial.
    - specialize (H9 n).
      assert (RandomVariable (F (S n)) borel_sa
                    (rvplus (rvmult (rvminus (const 1) (α n)) (W n))
                       (rvmult (β n) (w n)))).
      {
        apply rvplus_rv.
        - apply rvmult_rv.
          + apply rvminus_rv.
            * apply rvconst.
            * apply (RandomVariable_sa_sub (isfilt n)).
              apply adapta.
          + now apply (RandomVariable_sa_sub (isfilt n)).
        - apply rvmult_rv; trivial.
          now apply (RandomVariable_sa_sub (isfilt n)).
      }
      revert H10.
      apply RandomVariable_proper; try easy.
      intros ?.
      rewrite H9.
      rv_unfold.
      lra.
  }
  generalize (Dvoretzky_converge_W_alpha_beta_uniform W w α β isfilt filt_sub); intros dvor.
  eapply dvor; trivial.
  - intros.
    now apply (RandomVariable_sa_sub (filt_sub n)).
  - intros.
    now apply (RandomVariable_sa_sub (filt_sub n)).
  - exists B.
    apply H0.
  - intros ??.
    specialize (H9 n a).
    rv_unfold.
    lra.
 Qed.

Lemma lemma1_alpha_beta (α β w B W : nat -> Ts -> R) (Ca Cb : R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptB : IsAdapted borel_sa B F}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F}
      (is_cond : forall n, is_conditional_expectation prts (F n) (w n) (ConditionalExpectation prts (filt_sub n) (w n))) :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (B n)) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
(*  (forall n x, 0 <= α n x) -> *)
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) -> 
(*  (forall n x, 0 <= 1 - α n x )  -> *)
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  (exists (b : Ts -> R),
      almost prts (fun ω => forall n, B n ω <= Rabs (b ω))) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0). 
Proof.
  assert (H7 : True) by trivial. (* fix auto naming from history. sigh. *)
  intros.
  unfold IsAdapted in adaptB.
  assert (rvB: forall j t,
             (j <= t)%nat ->
             RandomVariable (F t) borel_sa (B j)).
  {
    intros.
    assert (sa_sub (F j) (F t)).
    {
      now apply is_filtration_le.
    }
    now apply (RandomVariable_sa_sub H12).
  }

  pose (tau_coll k t j :=
          match (le_dec j t) with
          | left pf =>  event_lt (rv := rvB j t pf) (F t) (B j) (INR k)
          | _ =>  Ω
          end).
  
  pose (tau_int k t := inter_of_collection (tau_coll k t)).

  pose (IB k t := EventIndicator (classic_dec (tau_int k t))).
  assert (forall k t,
             RandomVariable dom borel_sa (rvmult (rvsqr (w t)) (IB k t))).
  {
    intros.
    apply rvmult_rv.
    - typeclasses eauto.
    - apply (RandomVariable_sa_sub (filt_sub t)).
      apply EventIndicator_rv.
  }
  assert (forall k t,
             almostR2 prts Rbar_le
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
      apply EventIndicator_rv.
    }
    generalize (Condexp_nneg_simpl prts (filt_sub t) (rvmult (rvsqr (w t)) (IB k t))); intros.
    generalize (NonNegCondexp_factor_out prts (filt_sub t) 
                                         (rvsqr (w t)) (IB k t)); intros.
    apply almostR2_prob_space_sa_sub_lift in H14.
    revert H14.
    apply almost_impl.
    revert H0.
    apply almost_impl, all_almost.
    unfold impl; intros.
    rewrite H13.

    rewrite_condexp H14.
    unfold IB, tau_int, Rbar_rvmult, tau_coll, EventIndicator.
    match_destr.
    generalize (e t); intros.
    match_destr_in H15.
    unfold event_lt in H15.
    simpl in H15.
    - specialize (H0 t).
      simpl in H0.
      rewrite Condexp_nneg_simpl with (nnf := (nnfsqr (w t)))  in H0.
      rewrite Rbar_mult_1_l.
      unfold const.
      eapply Rbar_le_trans.
      apply H0.
      simpl; lra.
    - lia.
    - rewrite Rbar_mult_0_l.
      unfold const.
      apply pos_INR.
  }

  assert (almost prts (fun ω => exists k, forall t,
                             IB k t ω = 1)).
  {
    generalize (@almost_exists_iff 
                  Ts dom prts R
                  (fun b ω => forall n : nat, B n ω <= Rabs b)); intros.
    rewrite H13 in H10.
    revert H10.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H10.
    pose (b := Rabs x0).
    exists (Z.to_nat (up b)).
    intros.
    unfold IB, tau_int, tau_coll, EventIndicator.
    match_destr.
    red in n.
    cut_to n; try easy.
    simpl.
    intros.
    match_destr.
    - simpl.
      eapply Rle_lt_trans.
      apply H10.
      rewrite INR_up_pos.
      + apply Rle_lt_trans with (r2 := b).
        * unfold b.
          lra.
        * apply archimed.
      + unfold b.
        apply Rle_ge.
        apply Rabs_pos.
  }
  pose (wk k n := rvmult (w n) (IB k n)).
  pose (Wk := fix Wk k n ω :=
                match n with
                | 0%nat => W 0%nat ω
                | S n' =>
                  (1 - α n' ω) * (Wk k n' ω) + (β n' ω) * (wk k n' ω)
                end).
  assert (almost prts (fun ω => exists k, forall t,
                             Wk k t ω = W t ω)).
  {
    revert H13.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H13.
    exists x0.
    intros.
    unfold Wk.
    induction t; trivial.
    rewrite IHt.
    rewrite H9.
    unfold wk.
    unfold rvmult.
    rewrite H13.
    ring.
  }
  assert (forall k, IsAdapted borel_sa (IB k) F).
  {
    intros ??.
    apply EventIndicator_pre_rv.
    unfold tau_int, tau_coll.
    apply sa_pre_countable_inter.
    intros.
    match_destr.
    - unfold proj1_sig.
      match_destr.
    - apply sa_all.
  }
    
  assert (forall k n, RandomVariable (F (S n)) borel_sa (wk k n)).
  {
    intros.
    apply rvmult_rv; trivial.
    apply EventIndicator_pre_rv.
    unfold tau_int, tau_coll.
    apply sa_pre_countable_inter.
    intros.
    match_destr.
    - unfold proj1_sig.
      match_destr.
      apply isfilt in s.
      apply s.
    - apply sa_all.
  }
  assert (forall k, IsAdapted borel_sa (wk k) (fun n : nat => F (S n))).
  {
    intros ? ?.
    apply H16.
  }
  assert (forall k n, RandomVariable dom borel_sa (wk k n)).  
  {
    intros.
    specialize (H16 k n).
    now apply RandomVariable_sa_sub in H16.
  }
  
  assert (isfewk2: forall k n : nat, IsFiniteExpectation prts (rvsqr (wk k n) )).
  {
    intros.
    generalize isfe_almost_condexp_sqr_bounded; intros.
    assert (RandomVariable dom borel_sa (wk k n)).
    {
      apply rvmult_rv; trivial.
      apply (RandomVariable_sa_sub (filt_sub n)).
      apply EventIndicator_rv.
    }
    apply (isfe_almost_condexp_sqr_bounded _ (filt_sub n) (sqrt (INR k))) with (rv := H20).
    specialize (H12 k n).
    revert H12.
    apply almost_impl, all_almost.
    unfold impl; intros.
    unfold const.
    unfold const in H12.
    replace (Rsqr (sqrt (INR k))) with (INR k).
    - rewrite ConditionalExpectation_ext with (f2 := (rvmult (rvsqr (w n)) (IB k n)))
                                              (rv2 := H11 k n); trivial.
      intros ?.
      rv_unfold.
      unfold wk.
      rewrite Rsqr_mult.
      f_equal.
      unfold Rsqr, IB.
      match_destr; lra.
    - rewrite Rsqr_sqrt; trivial.
      apply pos_INR.
  }

  assert (isfewk : forall k n, IsFiniteExpectation prts (wk k  n)).
  {
    intros.
    now apply isfe_rsqr.
  }
  assert (isfe : forall n, IsFiniteExpectation prts (w n)).
  {
    intros.
    apply (isfe_almost_condexp_const _ (filt_sub n) 0 (w n) (H n) (is_cond n)).
  }
  assert (forall k,
             almost prts (fun ω : Ts => is_lim_seq (fun n : nat => Wk k n ω) 0)).
  {
    intros.
    generalize (lemma1_bounded_alpha_beta α β (wk k) (Wk k) Ca Cb (INR k) isfilt filt_sub); intros.
    apply H19; trivial.
    - intros.
      generalize (Condexp_factor_out prts (filt_sub n) (w n) (IB k n)); intros.
      apply almost_prob_space_sa_sub_lift with (sub := filt_sub n) in H20.
      revert H20.
      apply almost_impl.
      specialize (H n).
      revert H.
      apply almost_impl, all_almost.
      unfold impl; intros.
      unfold wk.
      rewrite H20.
      unfold Rbar_rvmult.
      rewrite H.
      unfold const.
      apply Rbar_mult_0_r.
    - intros.
      specialize (H12 k n).
      revert H12.
      apply almost_impl, all_almost.
      unfold impl; intros.
      assert (rv_eq (rvmult (rvsqr (w n)) (IB k n ))
                    (rvsqr (wk k n))).
      {
        intros ?.
        rv_unfold.
        unfold wk.
        rewrite Rsqr_mult.
        f_equal.
        unfold Rsqr.
        unfold IB.
        match_destr; lra.
     }
      rewrite (ConditionalExpectation_ext prts (filt_sub n) _ _ H20) in H12.
      eapply Rbar_le_trans.
      apply H12.
      unfold const; simpl.
      unfold Rsqr.
      destruct k.
      + simpl.
        lra.
      + rewrite <- Rmult_1_l at 1.
        apply Rmult_le_compat_r.
        * apply pos_INR.
        * rewrite S_INR.
          generalize (pos_INR k); intros.
          lra.
  }
  apply almost_forall in H19.
  revert H19.
  apply almost_impl.
  revert H14.
  apply almost_impl, all_almost.
  unfold impl; intros.
  destruct H14.
  specialize (H19 x0).
  simpl in H19.
  revert H19.
  now apply is_lim_seq_ext.
Qed.


Lemma lemma1_alpha_beta_uniform (α β w B W : nat -> Ts -> R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptB : IsAdapted borel_sa B F}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F}
      (is_cond : forall n, is_conditional_expectation prts (F n) (w n) (ConditionalExpectation prts (filt_sub n) (w n))) :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (B n)) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
(*  (forall n x, 0 <= α n x) -> *)
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) -> 
(*  (forall n x, 0 <= 1 - α n x )  -> *)
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->
  almost prts (fun ω => ex_series (fun n => Rsqr (β n ω))) ->
  (exists epsilon : posreal, eventually (fun n => almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (β (nn+n)%nat) ω))) (const epsilon))) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  (exists (b : Ts -> R),
      almost prts (fun ω => forall n, B n ω <= Rabs (b ω))) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0). 
Proof.
  intros.
  unfold IsAdapted in adaptB.
  assert (rvB: forall j t,
             (j <= t)%nat ->
             RandomVariable (F t) borel_sa (B j)).
  {
    intros.
    assert (sa_sub (F j) (F t)).
    {
      now apply is_filtration_le.
    }
    now apply (RandomVariable_sa_sub H12).
  }

  pose (tau_coll k t j :=
          match (le_dec j t) with
          | left pf =>  event_lt (rv := rvB j t pf) (F t) (B j) (INR k)
          | _ =>  Ω
          end).
  
  pose (tau_int k t := inter_of_collection (tau_coll k t)).

  pose (IB k t := EventIndicator (classic_dec (tau_int k t))).
  assert (forall k t,
             RandomVariable dom borel_sa (rvmult (rvsqr (w t)) (IB k t))).
  {
    intros.
    apply rvmult_rv.
    - typeclasses eauto.
    - apply (RandomVariable_sa_sub (filt_sub t)).
      apply EventIndicator_rv.
  }
  assert (forall k t,
             almostR2 prts Rbar_le
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
      apply EventIndicator_rv.
    }
    generalize (Condexp_nneg_simpl prts (filt_sub t) (rvmult (rvsqr (w t)) (IB k t))); intros.
    generalize (NonNegCondexp_factor_out prts (filt_sub t) 
                                         (rvsqr (w t)) (IB k t)); intros.
    apply almostR2_prob_space_sa_sub_lift in H14.
    revert H14.
    apply almost_impl.
    revert H0.
    apply almost_impl, all_almost.
    unfold impl; intros.
    rewrite H13.

    rewrite_condexp H14.
    unfold IB, tau_int, Rbar_rvmult, tau_coll, EventIndicator.
    match_destr.
    generalize (e t); intros.
    match_destr_in H15.
    unfold event_lt in H15.
    simpl in H15.
    - specialize (H0 t).
      simpl in H0.
      rewrite Condexp_nneg_simpl with (nnf := (nnfsqr (w t)))  in H0.
      rewrite Rbar_mult_1_l.
      unfold const.
      eapply Rbar_le_trans.
      apply H0.
      simpl; lra.
    - lia.
    - rewrite Rbar_mult_0_l.
      unfold const.
      apply pos_INR.
  }

  assert (almost prts (fun ω => exists k, forall t,
                             IB k t ω = 1)).
  {
    generalize (@almost_exists_iff 
                  Ts dom prts R
                  (fun b ω => forall n : nat, B n ω <= Rabs b)); intros.
    rewrite H13 in H10.
    revert H10.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H10.
    pose (b := Rabs x0).
    exists (Z.to_nat (up b)).
    intros.
    unfold IB, tau_int, tau_coll, EventIndicator.
    match_destr.
    red in n.
    cut_to n; try easy.
    simpl.
    intros.
    match_destr.
    - simpl.
      eapply Rle_lt_trans.
      apply H10.
      rewrite INR_up_pos.
      + apply Rle_lt_trans with (r2 := b).
        * unfold b.
          lra.
        * apply archimed.
      + unfold b.
        apply Rle_ge.
        apply Rabs_pos.
    - easy.
  }
  pose (wk k n := rvmult (w n) (IB k n)).
  pose (Wk := fix Wk k n ω :=
                match n with
                | 0%nat => W 0%nat ω
                | S n' =>
                  (1 - α n' ω) * (Wk k n' ω) + (β n' ω) * (wk k n' ω)
                end).
  assert (almost prts (fun ω => exists k, forall t,
                             Wk k t ω = W t ω)).
  {
    revert H13.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H13.
    exists x0.
    intros.
    unfold Wk.
    induction t; trivial.
    rewrite IHt.
    rewrite H9.
    unfold wk.
    unfold rvmult.
    rewrite H13.
    ring.
  }
  assert (forall k, IsAdapted borel_sa (IB k) F).
  {
    intros ??.
    apply EventIndicator_pre_rv.
    unfold tau_int, tau_coll.
    apply sa_pre_countable_inter.
    intros.
    match_destr.
    - unfold proj1_sig.
      match_destr.
    - apply sa_all.
  }
    
  assert (forall k n, RandomVariable (F (S n)) borel_sa (wk k n)).
  {
    intros.
    apply rvmult_rv; trivial.
    apply EventIndicator_pre_rv.
    unfold tau_int, tau_coll.
    apply sa_pre_countable_inter.
    intros.
    match_destr.
    - unfold proj1_sig.
      match_destr.
      apply isfilt in s.
      apply s.
    - apply sa_all.
  }
  assert (forall k, IsAdapted borel_sa (wk k) (fun n : nat => F (S n))).
  {
    intros ? ?.
    apply H16.
  }
  assert (forall k n, RandomVariable dom borel_sa (wk k n)).  
  {
    intros.
    specialize (H16 k n).
    now apply RandomVariable_sa_sub in H16.
  }
  
  assert (isfewk2: forall k n : nat, IsFiniteExpectation prts (rvsqr (wk k n) )).
  {
    intros.
    generalize isfe_almost_condexp_sqr_bounded; intros.
    assert (RandomVariable dom borel_sa (wk k n)).
    {
      apply rvmult_rv; trivial.
      apply (RandomVariable_sa_sub (filt_sub n)).
      apply EventIndicator_rv.
    }
    apply (isfe_almost_condexp_sqr_bounded _ (filt_sub n) (sqrt (INR k))) with (rv := H20).
    specialize (H12 k n).
    revert H12.
    apply almost_impl, all_almost.
    unfold impl; intros.
    unfold const.
    unfold const in H12.
    replace (Rsqr (sqrt (INR k))) with (INR k).
    - rewrite ConditionalExpectation_ext with (f2 := (rvmult (rvsqr (w n)) (IB k n)))
                                              (rv2 := H11 k n); trivial.
      intros ?.
      rv_unfold.
      unfold wk.
      rewrite Rsqr_mult.
      f_equal.
      unfold Rsqr, IB.
      match_destr; lra.
    - rewrite Rsqr_sqrt; trivial.
      apply pos_INR.
  }

  assert (isfewk : forall k n, IsFiniteExpectation prts (wk k  n)).
  {
    intros.
    now apply isfe_rsqr.
  }
  assert (isfe : forall n, IsFiniteExpectation prts (w n)).
  {
    intros.
    apply (isfe_almost_condexp_const _ (filt_sub n) 0 (w n) (H n) (is_cond n)).
  }
  assert (forall k,
             almost prts (fun ω : Ts => is_lim_seq (fun n : nat => Wk k n ω) 0)).
  {
    intros.
    generalize (lemma1_bounded_alpha_beta_uniform α β (wk k) (Wk k) (INR k) isfilt filt_sub); intros.
    apply H19; trivial.
    - intros.
      generalize (Condexp_factor_out prts (filt_sub n) (w n) (IB k n)); intros.
      apply almost_prob_space_sa_sub_lift with (sub := filt_sub n) in H20.
      revert H20.
      apply almost_impl.
      specialize (H n).
      revert H.
      apply almost_impl, all_almost.
      unfold impl; intros.
      unfold wk.
      rewrite H20.
      unfold Rbar_rvmult.
      rewrite H.
      unfold const.
      apply Rbar_mult_0_r.
    - intros.
      specialize (H12 k n).
      revert H12.
      apply almost_impl, all_almost.
      unfold impl; intros.
      assert (rv_eq (rvmult (rvsqr (w n)) (IB k n ))
                    (rvsqr (wk k n))).
      {
        intros ?.
        rv_unfold.
        unfold wk.
        rewrite Rsqr_mult.
        f_equal.
        unfold Rsqr.
        unfold IB.
        match_destr; lra.
     }
      rewrite (ConditionalExpectation_ext prts (filt_sub n) _ _ H20) in H12.
      eapply Rbar_le_trans.
      apply H12.
      unfold const; simpl.
      unfold Rsqr.
      destruct k.
      + simpl.
        lra.
      + rewrite <- Rmult_1_l at 1.
        apply Rmult_le_compat_r.
        * apply pos_INR.
        * rewrite S_INR.
          generalize (pos_INR k); intros.
          lra.
  }
  apply almost_forall in H19.
  revert H19.
  apply almost_impl.
  revert H14.
  apply almost_impl, all_almost.
  unfold impl; intros.
  destruct H14.
  specialize (H19 x0).
  simpl in H19.
  revert H19.
  now apply is_lim_seq_ext.
Qed.

Lemma lemma1_alpha_beta_alt (α β w W : nat -> Ts -> R) (Ca Cb : R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F}
      (is_cond : forall n, is_conditional_expectation prts (F n) (w n) (ConditionalExpectation prts (filt_sub n) (w n))) :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
(*  (forall n x, 0 <= α n x) -> *)
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) -> 
(*  (forall n x, 0 <= 1 - α n x )  -> *)
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  (exists (b : Ts -> R),
      almost prts (fun ω => forall n,
                       Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n)) ω) (b ω))) ->  
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0). 
Proof.
  assert (H6 : True) by trivial. (* fix auto naming from history. sigh. *)
  intros.
  pose (B := fun n ω => real (ConditionalExpectation _ (filt_sub n) (rvsqr (w n)) ω)).
  generalize (lemma1_alpha_beta α β w B W Ca Cb isfilt); intros.
  specialize (H10 filt_sub rv _).
  apply H10; trivial.
  - unfold IsAdapted, B.
    intros.
    apply Rbar_real_rv.
    apply Condexp_rv.
  - intros.
    destruct H9 as [b ?].
    revert H9.
    apply almost_impl.
    apply all_almost; intros ??.
    specialize (H9 n).
    unfold B.
    assert (is_finite
               (ConditionalExpectation prts (filt_sub n) (rvsqr (w n)) x)).
    {
      apply bounded_is_finite with (a := 0) (b := b x); trivial.
      apply Condexp_nneg.
      apply nnfsqr.
    }
    rewrite <- H11.
    simpl.
    now right.
  - destruct H9 as [b ?].
    exists b.
    revert H9.
    apply almost_impl.
    apply all_almost; intros ???.
    unfold B.
    specialize (H9 n).
    assert (is_finite
               (ConditionalExpectation prts (filt_sub n) (rvsqr (w n)) x)).
    {
      apply bounded_is_finite with (a := 0) (b := b x); trivial.
      apply Condexp_nneg.
      apply nnfsqr.
    }
    rewrite <- H11 in H9.
    simpl in H9.
    eapply Rle_trans.
    apply H9.
    apply Rle_abs.
 Qed.

Lemma lemma1_alpha_beta_alt_uniform (α β w W : nat -> Ts -> R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F}
      (is_cond : forall n, is_conditional_expectation prts (F n) (w n) (ConditionalExpectation prts (filt_sub n) (w n))) :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
(*  (forall n x, 0 <= α n x) -> *)
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) -> 
(*  (forall n x, 0 <= 1 - α n x )  -> *)
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->
  almost prts (fun ω => ex_series (fun n => Rsqr (β n ω))) ->
  (exists epsilon : posreal, eventually (fun n => almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (β (nn+n)%nat) ω))) (const epsilon))) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  (exists (b : Ts -> R),
      almost prts (fun ω => forall n,
                       Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n)) ω) (b ω))) ->  
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0). 
Proof.
  intros.
  pose (B := fun n ω => real (ConditionalExpectation _ (filt_sub n) (rvsqr (w n)) ω)).
  generalize (lemma1_alpha_beta_uniform α β w B W isfilt); intros.
  specialize (H10 filt_sub rv _).
  apply H10; trivial.
  - unfold IsAdapted, B.
    intros.
    apply Rbar_real_rv.
    apply Condexp_rv.
  - intros.
    destruct H9 as [b ?].
    revert H9.
    apply almost_impl.
    apply all_almost; intros ??.
    specialize (H9 n).
    unfold B.
    assert (is_finite
               (ConditionalExpectation prts (filt_sub n) (rvsqr (w n)) x)).
    {
      apply bounded_is_finite with (a := 0) (b := b x); trivial.
      apply Condexp_nneg.
      apply nnfsqr.
    }
    rewrite <- H11.
    simpl.
    now right.
  - destruct H9 as [b ?].
    exists b.
    revert H9.
    apply almost_impl.
    apply all_almost; intros ???.
    unfold B.
    specialize (H9 n).
    assert (is_finite
               (ConditionalExpectation prts (filt_sub n) (rvsqr (w n)) x)).
    {
      apply bounded_is_finite with (a := 0) (b := b x); trivial.
      apply Condexp_nneg.
      apply nnfsqr.
    }
    rewrite <- H11 in H9.
    simpl in H9.
    eapply Rle_trans.
    apply H9.
    apply Rle_abs.
 Qed.

Lemma lemma1_alpha_alpha (α w B W : nat -> Ts -> R) (Ca : R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptB : IsAdapted borel_sa B F}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      (is_cond : forall n, is_conditional_expectation prts (F n) (w n) (ConditionalExpectation prts (filt_sub n) (w n))) :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (B n)) ->  
  (forall n x, 0 <= α n x) ->
  (forall n x, 0 <= 1 - α n x )  ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const Ca)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (α n ω) * (w n ω)) ->
  (exists (b : Ts -> R),
      almost prts (fun ω => forall n, B n ω <= Rabs (b ω))) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  intros.
  apply (lemma1_alpha_beta α α w B W Ca Ca isfilt filt_sub); trivial.
  - intros.
    apply all_almost.
    now intros.
  - intros.
    apply all_almost.
    unfold const.
    intros.
    apply H1.
  - intros.
    apply all_almost.
    unfold const.
    intros.
    specialize (H2 n x).
    lra.
  - intros.
    apply all_almost.
    unfold const.
    intros.
    specialize (H2 n x).
    lra.
 Qed.


Lemma lemma1_alpha_beta_shift (α β w B W : nat -> Ts -> R) (Ca Cb : R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {rvW0 : RandomVariable (F 0%nat) borel_sa (W 0%nat)}
      {adaptB : IsAdapted borel_sa B F}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F}
      (is_cond : forall n, is_conditional_expectation prts (F n) (w n) (ConditionalExpectation prts (filt_sub n) (w n))) :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rbar_le (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (B n)) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) ->
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->  
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  is_lim_seq'_uniform_almost (fun n => fun ω => sum_n (fun k => rvsqr (α k) ω) n) 
                             (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) ->
  is_lim_seq'_uniform_almost (fun n => fun ω => sum_n (fun k => rvsqr (β k) ω) n) 
                             (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) ->
  (exists (b : Ts -> R),
      almost prts (fun ω => forall n, B n ω <= Rabs (b ω))) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  assert (H5 : True) by trivial. (* fix auto naming from history. sigh. *)
  intros.
  
  destruct ( uniform_converge_sq _ H1 ( uniform_converge_sum_sq _ H8)).
  destruct ( uniform_converge_sq _ H2 ( uniform_converge_sum_sq _ H9)).
  pose (N := max x x0).
  assert (almost prts (fun ω : Ts => is_lim_seq (fun n : nat => W (n + N)%nat ω) 0)).
  {
    assert (isfilt' : IsFiltration (fun n => F (n + N)%nat)).
    {
      intros ?.
      now replace (S n + N)%nat with (S (n + N)) by lia.
    }
    eapply (lemma1_alpha_beta (fun n => α (n + N)%nat) (fun n => β (n + N)%nat) 
                             (fun n => w (n + N)%nat) (fun n => B (n + N)%nat)
                             (fun n => W (n + N)%nat) Ca Cb isfilt' (fun n => filt_sub (n + N)%nat)); try easy.
    - intros.
      apply H11.
      lia.
    - intros.
      apply H12.
      lia.
    - revert H3.
      apply almost_impl, all_almost; intros ??.
      rewrite is_lim_seq_sum_shift_inf in H3.
      apply H3.
    - revert H4.
      apply almost_impl, all_almost; intros ??.
      rewrite is_lim_seq_sum_shift_inf in H4.
      apply H4.
    - revert H6; apply almost_impl.
      apply all_almost; intros ??.
      destruct N.
      + rewrite Lim_seq_ext with
            (v := (sum_n (fun k : nat => rvsqr (β k) x1))); trivial.
        intros.
        apply sum_n_ext; intros.
        now replace (n0 + 0)%nat with n0 by lia.
      + rewrite Lim_seq_ext with
            (v :=  fun n => sum_n (fun k : nat => rvsqr (β k) x1) (n + S N) -
                            sum_n (fun k : nat => rvsqr (β k) x1) N).
        * apply Rbar_le_trans with
              (y := Lim_seq (fun n : nat => sum_n (fun k : nat => rvsqr (β k) x1) (n + S N))).
          -- apply Lim_seq_le_loc.
             exists (0%nat); intros.
             assert (0 <= sum_n (fun k : nat => rvsqr (β k) x1) N).
             {
               apply sum_n_nneg.
               intros.
               apply nnfsqr.
             }
             lra.
          -- now rewrite <- Lim_seq_incr_n with (N := S N) in H6.
        * intros.
          now rewrite sum_shift_diff.
    - intros.
      now replace (S n + N)%nat with (S (n + N)) by lia.
      Unshelve.
      + simpl.
        induction N; trivial.
        specialize (H7 N).
        assert (RandomVariable (F (S N)) borel_sa
                      (rvplus
                         (rvmult (rvminus (const 1) (α N)) (W N))
                         (rvmult (β N) (w N)))).
        {
          apply rvplus_rv.
          - apply rvmult_rv.
            + apply rvminus_rv.
              * typeclasses eauto.
              * now apply (RandomVariable_sa_sub (isfilt N)).
            + apply (RandomVariable_sa_sub (isfilt N)).
              apply IHN.
              intros ?.
              now replace (S n + N)%nat with (S (n + N)) by lia.
         - apply rvmult_rv.
           + now apply (RandomVariable_sa_sub (isfilt N)).
           + easy.
        }
        revert H13; apply RandomVariable_proper; try reflexivity.
        intros ?.
        now rv_unfold'.
      + easy.
      + intros ?.
        now replace (S n + N)%nat with (S (n + N)) by lia.
      + easy.
      + easy.
    - destruct H10.
      exists x1.
      revert H10.
      apply almost_impl, all_almost; intros ???.
      apply H10.
  }
  revert H13.
  apply almost_impl, all_almost; intros ??.
  eapply is_lim_seq_incr_n.
  apply H13.
Qed.
  
Lemma lemma2_part1 (W : nat -> nat -> Ts -> R) (ω : Ts) 
      (α w : nat -> Ts -> R) :
  (forall t0, W 0%nat t0 ω = 0) ->
  (forall t0 t,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (α (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  forall t0 t,
    W ((S t) + t0)%nat 0%nat ω = (prod_f_R0 (fun k => 1 - α (k + t0)%nat ω)
                                                t) * (W t0 0%nat ω)  + (W (S t) t0 ω).
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

Lemma lemma2_part1_beta (W : nat -> nat -> Ts -> R) (ω : Ts) 
      (α β w : nat -> Ts -> R) :
  (forall t0, W 0%nat t0 ω = 0) ->
  (forall t0 t,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (β (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  forall t0 t,
    W ((S t) + t0)%nat 0%nat ω = (prod_f_R0 (fun k => 1 - α (k + t0)%nat ω)
                                                t) * (W t0 0%nat ω)  + (W (S t) t0 ω).
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

Lemma lemma2_part2 (W :  nat -> nat -> Ts -> R) (ω : Ts) 
      (α w : nat -> Ts -> R) :
  (forall t0, W 0%nat t0 ω = 0) ->
  (forall t, 0 <= α t ω <= 1) -> 
  (forall t0 t,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (α (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  forall t0 t,
    Rabs (W t t0 ω) <= Rabs (W (t + t0)%nat 0%nat ω) +
                           Rabs (W t0 0%nat ω).
Proof.
  intros.
  destruct t.
  - rewrite H, Rabs_R0.
    apply Rplus_le_le_0_compat; apply Rabs_pos.
  - generalize (lemma2_part1 W ω α w H H1 t0 t); intros.
    assert (W (S t) t0 ω =
            W (S t + t0)%nat 0%nat ω -
            prod_f_R0 (fun k : nat => 1 - α (k + t0)%nat ω) t * W t0 0%nat ω).
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

Lemma lemma2_part2_beta (W :  nat -> nat -> Ts -> R) (ω : Ts) 
      (α β w : nat -> Ts -> R) :
  (forall t0, W 0%nat t0 ω = 0) ->
  (forall t, 0 <= α t ω <= 1) ->
  (forall t, 0 <= β t ω <= 1) ->  
  (forall t0 t,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (β (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  forall t0 t,
    Rabs (W t t0 ω) <= Rabs (W (t + t0)%nat 0%nat ω) +
                           Rabs (W t0 0%nat ω).
Proof.
  intros.
  destruct t.
  - rewrite H, Rabs_R0.
    apply Rplus_le_le_0_compat; apply Rabs_pos.
  - generalize (lemma2_part1_beta W ω α β w H H2 t0 t); intros.
    assert (W (S t) t0 ω =
            W (S t + t0)%nat 0%nat ω -
            prod_f_R0 (fun k : nat => 1 - α (k + t0)%nat ω) t * W t0 0%nat ω).
    {
      rewrite H3.
      lra.
    }
    rewrite H4.
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

Lemma lemma2 (W : nat -> nat -> Ts -> R) (ω : Ts) 
      (α w : nat -> Ts -> R) :
  (forall t0, W 0%nat t0 ω = 0) ->
  (forall t , 0 <= α t ω <= 1) ->
  (forall t0 t,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (α (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  is_lim_seq (fun n => W n 0%nat ω) 0 ->
  forall (delta : posreal),
  exists (T : nat),
  forall t0 t,
    (t0 >= T)%nat ->
    Rabs (W t t0 ω) <= delta.
 Proof.
   intros.
   generalize (lemma2_part2 W ω α w H H0 H1 ); intros.
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

 Lemma lemma2_alpha_pos (W : nat -> nat -> Ts -> R) (ω : Ts) 
      (α w : nat -> Ts -> R) :
  (forall t0, W 0%nat t0 ω = 0) ->
  (forall t , 0 <= α t ω ) ->
  is_lim_seq (fun t => α t ω) 0 ->
  (forall t0 t,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (α (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  (forall x, is_lim_seq (fun n => W n x ω) 0) ->
  forall (delta : posreal),
  exists (T : nat),
  forall t0 t,
    (t0 >= T)%nat ->
    Rabs (W t t0 ω) <= delta.
 Proof.
   intros.
   apply is_lim_seq_spec in H1.
   assert (0 < 1) by lra.
   specialize (H1 (mkposreal 1 H4)).
   destruct H1.
   pose (W' := fun (t t0:nat) (ω : Ts) =>
                 W t (t0 + x)%nat ω).
   pose (α' := fun (t : nat) (ω : Ts) => α (t + x)%nat ω).
   pose (w' := fun (t : nat) (ω : Ts) => w (t + x)%nat ω).   
   generalize (lemma2 W' ω α' w'); intros.
   cut_to H5.
   - specialize (H5 delta).
     destruct H5.
     exists (x + x0)%nat.
     intros.
     specialize (H5 (t0 - x)%nat t).
     cut_to H5; try lia.
     unfold W' in H5.
     replace (t0 - x + x)%nat with t0 in H5 by lia.
     apply H5.
   - intros.
     apply H.
   - intros.
     split.
     + apply H0.
     + unfold α'.
       specialize (H1 (t + x)%nat).
       cut_to H1; try lia.
       simpl in H1.
       rewrite Rminus_0_r in H1.
       rewrite Rabs_right in H1; try lra.
       apply Rle_ge.
       apply H0.
   - intros.
     unfold W'.
     rewrite H2.
     unfold α', w'.
     f_equal.
     + f_equal.
       f_equal.
       f_equal.
       lia.
     + f_equal.
       * f_equal; lia.
       * f_equal; lia.
   - apply H3.
Qed.
   
   
Lemma lemma2_beta (W : nat -> nat -> Ts -> R) (ω : Ts) 
      (α β w : nat -> Ts -> R) :
  (forall t0, W 0%nat t0 ω = 0) ->
  (forall t , 0 <= α t ω <= 1) ->
  (forall t , 0 <= β t ω <= 1) ->  
  (forall t0 t,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (β (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  is_lim_seq (fun n => W n 0%nat ω) 0 ->
  forall (delta : posreal),
  exists (T : nat),
  forall t0 t,
    (t0 >= T)%nat ->
    Rabs (W t t0 ω) <= delta.
 Proof.
   intros.
   generalize (lemma2_part2_beta W ω α β w H H0 H1 H2); intros.
   apply is_lim_seq_spec in H3.
   assert (0 < delta/2).
   {
     generalize (cond_pos delta); intros.
     lra.
   }
   specialize (H3 (mkposreal _ H5)).
   unfold eventually in H3.
   destruct H3 as [T ?].
   exists T.
   intros.
   specialize (H4 t0 t).
   eapply Rle_trans.
   - apply H4.
   - replace (pos delta) with ((delta/2) + (delta/2)) by lra.
     apply Rplus_le_compat.
     + simpl in H3.
       specialize (H3 (t + t0)%nat).
       rewrite Rminus_0_r in H3.
       left.
       apply H3.
       lia.
     + simpl in H3.
       specialize (H3 t0).
       rewrite Rminus_0_r in H3.
       left.
       apply H3.
       lia.
 Qed.

 Lemma lemma2_almost (W : nat -> nat -> Ts -> R) 
      (α w : nat -> Ts -> R) :
  (forall t0 ω, W 0%nat t0 ω = 0) ->
  (forall t ω, 0 <= α t ω <= 1) ->
  (forall t0 t ω,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (α (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n 0%nat ω) 0) ->
  forall (delta : Ts -> posreal),
  exists (T : Ts -> nat),
    almost prts (fun ω =>
                   forall t0 t,
                   (t0 >= T ω)%nat ->
                   (rvabs (W t t0) ω) <= delta ω).
 Proof.
   intros.
   apply (@exists_almost Ts dom prts _ (fun (T : nat) =>
                     (fun ω : Ts => forall t0 t : nat, (t0 >= T)%nat -> rvabs (W t t0) ω <= delta ω))).
   revert H2.
   apply almost_impl, all_almost; intros ??.
   now apply lemma2 with (α := α) (w := w).
 Qed.

 Lemma lemma2_almost_alpha_pos  (W : nat -> nat -> Ts -> R) 
      (α w : nat -> Ts -> R) :
  (forall t0 ω, W 0%nat t0 ω = 0) ->
  almost prts (fun ω => forall t, 0 <= α t ω) ->
  almost prts (fun ω => is_lim_seq (fun t => α t ω) 0) ->
  (forall t0 t ω,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (α (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  (forall x, almost prts (fun ω => is_lim_seq (fun n => W n x ω) 0)) ->
  forall (delta : Ts -> posreal),
  exists (T : Ts -> nat),
    almost prts (fun ω =>
                   forall t0 t,
                   (t0 >= T ω)%nat ->
                   (rvabs (W t t0) ω) <= delta ω).
 Proof.
   intros.
   apply (@exists_almost Ts dom prts _ (fun (T : nat) =>
                                          (fun ω : Ts => forall t0 t : nat, (t0 >= T)%nat -> rvabs (W t t0) ω <= delta ω))).
   apply almost_forall in H3.
   revert H0; apply almost_impl.
   revert H1; apply almost_impl.
   revert H3; apply almost_impl.
   apply all_almost; intros ????.
   now apply lemma2_alpha_pos with (α := α) (w := w).
 Qed.
 
 Lemma lemma2_almost_beta (W : nat -> nat -> Ts -> R) 
      (α β w : nat -> Ts -> R) :
  (forall t0 ω, W 0%nat t0 ω = 0) ->
  almost prts (fun ω  => forall t, 0 <= α t ω <= 1) ->
  almost prts (fun ω  => forall t, 0 <= β t ω <= 1) ->  
  (forall t0 t ω,
      W (S t) t0 ω =
      (1 - α (t + t0)%nat ω) * (W t t0 ω) +
      (β (t + t0)%nat ω) * (w (t + t0)%nat ω)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n 0%nat ω) 0) ->
  forall (delta : Ts -> posreal),
  exists (T : Ts -> nat),
    almost prts (fun ω =>
                   forall t0 t,
                   (t0 >= T ω)%nat ->
                   (rvabs (W t t0) ω) <= delta ω).
 Proof.
   intros.
   apply (@exists_almost Ts dom prts _ (fun (T : nat) =>
                     (fun ω : Ts => forall t0 t : nat, (t0 >= T)%nat -> rvabs (W t t0) ω <= delta ω))).
   revert H0; apply almost_impl.
   revert H1; apply almost_impl.
   revert H3; apply almost_impl.
   apply all_almost; intros ????.
   now apply lemma2_beta with (α := α) (β := β) (w := w).
 Qed.

 Lemma lemma8_part1 (x Y W : nat -> Ts -> R) (β : R) (D : posreal) (ω : Ts) 
      (α w : nat -> Ts -> R) :
   (Y 0%nat ω = D) ->
   (W 0%nat ω = 0) ->   
   (forall t, 0 <= α t ω <= 1) ->
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (α t ω) * β * D) ->
   (forall t,
     x (S t) ω <= 
     (1 - α t ω) * (x t ω) + 
     (α t ω) * (β * D + w t ω)) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   forall t,
     x t ω <= (Y t ω) + (W t ω).
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
     apply Rmult_le_compat_l with (r := 1 - α t ω) in IHt.
     apply Rplus_le_compat_r with (r := α t ω * (β * D + w t ω)) in IHt.
     + eapply Rle_trans.
       * apply IHt.
       * lra.
     + specialize (H1 t).
       lra.
 Qed.
     
 Lemma lemma8_part1_beta (x Y W : nat -> Ts -> R) (b : R) (D : posreal) (ω : Ts) 
      (α β w : nat -> Ts -> R) :
   (Y 0%nat ω = D) ->
   (W 0%nat ω = 0) ->   
   (forall t, 0 <= α t ω <= 1) ->
   (forall t, 0 <= β t ω <= 1) ->   
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (β t ω) * b * D) ->
   (forall t,
     x (S t) ω <= 
     (1 - α t ω) * (x t ω) + 
     (β t ω) * (b * D + w t ω)) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   forall t,
     x t ω <= (Y t ω) + (W t ω).
 Proof.
   intros.
   induction t; intros.
   - rewrite H, H0.
     rewrite Rplus_0_r.
     specialize (H6 0%nat).
     rewrite Rabs_le_between in H6.
     lra.
   - rewrite H3, H4.
     eapply Rle_trans.
     apply H5.
     apply Rmult_le_compat_l with (r := 1 - α t ω) in IHt.
     apply Rplus_le_compat_r with (r := β t ω * (b * D + w t ω)) in IHt.
     + eapply Rle_trans.
       * apply IHt.
       * lra.
     + specialize (H1 t).
       lra.
 Qed.

 Lemma lemma8_almost_part1  (x Y W : nat -> Ts -> R) (β : R) (D : posreal) 
      (α w : nat -> Ts -> R) :
   (forall ω, Y 0%nat ω = D) ->
   (forall ω, W 0%nat ω = 0) ->   
   (forall t ω, 0 <= α t ω <= 1) ->
   (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t ω,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (α t ω) * β * D) ->
   (almost prts
           (fun ω =>
              forall t,
                 Rabs (x t ω) <=  D)) ->

   (almost prts
           (fun ω =>
              forall t,
                 (x (S t) ω) <=
                 ((1 - α t ω) * (x t ω) + 
                  (α t ω) * (β * D + w t ω)))) ->
   almost prts
          (fun ω =>
             forall t,
               (x t ω) <= (Y t ω) + (W t ω)).
 Proof.
   intros.
   revert H5.
   apply almost_impl.
   revert H4.
   apply almost_impl; red.
   apply all_almost.
   unfold impl.
   intros.
   apply lemma8_part1 with (β := β) (D := D) (α := α) (w := w); trivial.
 Qed.

 Lemma lemma8_almost_part1_beta  (x Y W : nat -> Ts -> R) (b : R) (D : posreal) 
      (α β w : nat -> Ts -> R) :
   (forall ω, Y 0%nat ω = D) ->
   (forall ω, W 0%nat ω = 0) ->   
   (forall t ω, 0 <= α t ω <= 1) ->
   (forall t ω, 0 <= β t ω <= 1) ->   
   (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t ω,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (β t ω) * b * D) ->
   (almost prts
           (fun ω =>
              forall t,
                 Rabs (x t ω) <=  D)) ->

   (almost prts
           (fun ω =>
              forall t,
                 (x (S t) ω) <=
                 ((1 - α t ω) * (x t ω) + 
                  (β t ω) * (b * D + w t ω)))) ->
   almost prts
          (fun ω =>
             forall t,
               (x t ω) <= (Y t ω) + (W t ω)).
 Proof.
   intros.
   revert H6.
   apply almost_impl.
   revert H5.
   apply almost_impl; red.
   apply all_almost.
   unfold impl.
   intros.
   apply lemma8_part1_beta with (b := b) (β := β) (D := D) (α := α) (w := w); trivial.
 Qed.

 Lemma lemma8_part2 (x Y W : nat -> Ts -> R) (β : R) (D : posreal) (ω : Ts)
      (α w : nat -> Ts -> R) :
   (Y 0%nat ω = D) ->
   (W 0%nat ω = 0) ->   
   (forall t, 0 <= α t ω <= 1) ->
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (α t ω) * β * D) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   (forall t,
      x (S t) ω >= 
       (1 - α t ω) * (x t ω) + 
       (α t ω) * (-β * D + w t ω)) ->
   forall t,
      (- Y t ω) + (W t ω) <= x t ω.
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
     apply Rmult_le_compat_l with (r := 1 - α t ω) in IHt.
     apply Rplus_le_compat_r with (r := α t ω * (-β * D + w t ω)) in IHt.
     + eapply Rle_trans.
       shelve.
       apply IHt.
       Unshelve.
       lra.
     + specialize (H1 t).
       lra.
  Qed.
     
 Lemma lemma8_part2_beta (x Y W : nat -> Ts -> R) (b : R) (D : posreal) (ω : Ts)
      (α β w : nat -> Ts -> R) :
   (Y 0%nat ω = D) ->
   (W 0%nat ω = 0) ->   
   (forall t, 0 <= α t ω <= 1) ->
   (forall t, 0 <= β t ω <= 1) ->   
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (β t ω) * b * D) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   (forall t,
      x (S t) ω >= 
       (1 - α t ω) * (x t ω) + 
       (β t ω) * (-b * D + w t ω)) ->
   forall t,
      (- Y t ω) + (W t ω) <= x t ω.
 Proof.
   intros.
   induction t; intros.
   - rewrite H, H0.
     specialize (H5 0%nat).
     rewrite Rplus_0_r.
     rewrite Rabs_le_between in H5.
     lra.
   - rewrite H3, H4.
     eapply Rle_trans.
     shelve.
     apply Rge_le.
     apply H6.
     Unshelve.
     apply Rmult_le_compat_l with (r := 1 - α t ω) in IHt.
     apply Rplus_le_compat_r with (r := β t ω * (-b * D + w t ω)) in IHt.
     + eapply Rle_trans.
       shelve.
       apply IHt.
       Unshelve.
       lra.
     + specialize (H1 t).
       lra.
  Qed.

 Lemma lemma8_almost_part2  (x Y W : nat -> Ts -> R) (β : R) (D : posreal) 
      (α w : nat -> Ts -> R) :
   (forall ω, Y 0%nat ω = D) ->
   (forall ω, W 0%nat ω = 0) ->   
   (forall t ω, 0 <= α t ω <= 1) ->
   (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t ω,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (α t ω) * β * D) ->
   (almost prts
           (fun ω =>
              forall t,
                 Rabs (x t ω) <=  D)) ->
   (almost prts
           (fun ω =>
              forall t,
                x (S t) ω >= 
                (1 - α t ω) * (x t ω) + 
                (α t ω) * (-β * D + w t ω))) ->
   almost prts
          (fun ω =>
             forall t,
               (- Y t ω) + (W t ω) <= x t ω).
 Proof.
   intros.
   revert H5.
   apply almost_impl.
   revert H4.
   apply almost_impl; red.
   apply all_almost.
   unfold impl.
   intros.
   apply lemma8_part2 with (β := β) (D := D) (α := α) (w := w); trivial.
 Qed.

 Lemma lemma8_almost_part2_beta  (x Y W : nat -> Ts -> R) (b : R) (D : posreal) 
      (α β w : nat -> Ts -> R) :
   (forall ω, Y 0%nat ω = D) ->
   (forall ω, W 0%nat ω = 0) ->   
   (forall t ω, 0 <= α t ω <= 1) ->
   (forall t ω, 0 <= β t ω <= 1) ->   
   (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t ω,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (β t ω) * b * D) ->
   (almost prts
           (fun ω =>
              forall t,
                 Rabs (x t ω) <=  D)) ->
   (almost prts
           (fun ω =>
              forall t,
                x (S t) ω >= 
                (1 - α t ω) * (x t ω) + 
                (β t ω) * (-b * D + w t ω))) ->
   almost prts
          (fun ω =>
             forall t,
               (- Y t ω) + (W t ω) <= x t ω).
 Proof.
   intros.
   revert H6.
   apply almost_impl.
   revert H5.
   apply almost_impl; red.
   apply all_almost.
   unfold impl.
   intros.
   apply lemma8_part2_beta with (b := b) (β := β) (D := D) (α := α) (w := w); trivial.
 Qed.

 Lemma lemma8_abs  (x Y W : nat -> Ts -> R) (ω : Ts) (β : R) (D : posreal) 
      (α w : nat -> Ts -> R) :
   (Y 0%nat ω = D) ->
   (W 0%nat ω = 0) ->   
   (forall t, 0 <= α t ω <= 1) ->
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (α t ω) * β * D) ->
   (forall t,
     x (S t) ω <= 
     (1 - α t ω) * (x t ω) + 
     (α t ω) * (β * D + w t ω)) ->
   (forall t,
     x (S t) ω >= 
     (1 - α t ω) * (x t ω) + 
     (α t ω) * (-β * D + w t ω)) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   forall t,
     Rabs (x t ω) <= Rabs (W t ω) + (Y t ω).
 Proof.
   intros.
   assert (Rabs (x t ω - W t ω) <=  Y t ω).
   {
     apply Rabs_le_between.
     split.
     - apply Rplus_le_reg_r with (r := (W t ω)).
       ring_simplify.
       now apply lemma8_part2 with (β := β) (D := D) (α := α) (w := w).
     - apply Rplus_le_reg_r with (r := (W t ω)).
       ring_simplify.
       rewrite Rplus_comm.
       now apply lemma8_part1 with (β := β) (D := D) (α := α) (w := w).
   }
   apply Rplus_le_reg_r with (r := - Rabs (W t ω)).
   ring_simplify.
   apply Rle_trans with (r2 := Rabs (x t ω - W t ω) ); trivial.
   apply Rabs_triang_inv.
  Qed.

 Lemma lemma8_abs_beta  (x Y W : nat -> Ts -> R) (ω : Ts) (b : R) (D : posreal) 
      (α β w : nat -> Ts -> R) :
   (Y 0%nat ω = D) ->
   (W 0%nat ω = 0) ->   
   (forall t, 0 <= α t ω <= 1) ->
   (forall t, 0 <= β t ω <= 1) ->   
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (β t ω) * b * D) ->
   (forall t,
     x (S t) ω <= 
     (1 - α t ω) * (x t ω) + 
     (β t ω) * (b * D + w t ω)) ->
   (forall t,
     x (S t) ω >= 
     (1 - α t ω) * (x t ω) + 
     (β t ω) * (-b * D + w t ω)) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   forall t,
     Rabs (x t ω) <= Rabs (W t ω) + (Y t ω).
 Proof.
   intros.
   assert (Rabs (x t ω - W t ω) <=  Y t ω).
   {
     apply Rabs_le_between.
     split.
     - apply Rplus_le_reg_r with (r := (W t ω)).
       ring_simplify.
       now apply lemma8_part2_beta with (b := b) (β := β) (D := D) (α := α) (w := w).
     - apply Rplus_le_reg_r with (r := (W t ω)).
       ring_simplify.
       rewrite Rplus_comm.
       now apply lemma8_part1_beta with (b := b) (β := β) (D := D) (α := α) (w := w).
   }
   apply Rplus_le_reg_r with (r := - Rabs (W t ω)).
   ring_simplify.
   apply Rle_trans with (r2 := Rabs (x t ω - W t ω) ); trivial.
   apply Rabs_triang_inv.
  Qed.

 Lemma lemma8_abs_part2  (x Y W : nat -> Ts -> R) 
      (α w : nat -> Ts -> R) (ω : Ts) (β : R) (eps D : posreal) :
   (forall t, 0 <= α t ω <= 1) ->
   (W 0%nat ω = 0) ->
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t,
       Rabs (x t ω) <= Rabs (W t ω) + (Y t ω)) ->
   is_lim_seq (fun t => Y t ω) (β * D) ->
   eventually (fun t => Rabs (W t ω) <= β * eps * D) ->
   Rbar_le (LimSup_seq (fun t => Rabs (x t ω))) (β * (1 + eps) * D).
 Proof.
   intros.
   eapply Rbar_le_trans.
   - apply LimSup_le.
     exists 0%nat.
     intros.
     apply H2.
   - eapply Rbar_le_trans.
     + apply LimSup_le with (v := fun t => β * eps * D + (Y t ω)).
       destruct H4.
       exists x0.
       intros.
       apply Rplus_le_compat_r.
       apply H4.
       lia.
     + assert (is_LimSup_seq  (fun t : nat => β * eps * D + Y t ω) (β * eps * D + β * D)).
       {
         apply is_lim_LimSup_seq.
         apply is_lim_seq_plus with (l1 := β * eps * D) (l2 := β * D); trivial.
         - apply is_lim_seq_const.
         - red.
           simpl.
           f_equal.
       }
       apply is_LimSup_seq_unique in H5.
       rewrite H5.
       simpl.
       lra.
 Qed.

 Lemma lemma8_abs_part2_beta  (x Y W : nat -> Ts -> R) 
      (α β w : nat -> Ts -> R) (ω : Ts) (b : R) (eps D : posreal) :
   (forall t, 0 <= α t ω <= 1) ->
   (forall t, 0 <= β t ω <= 1) ->   
   (W 0%nat ω = 0) ->
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t,
       Rabs (x t ω) <= Rabs (W t ω) + (Y t ω)) ->
   (forall C, Rbar_le (LimSup_seq (fun t => C + Y t ω)) (C + (b * D))) ->
   eventually (fun t => Rabs (W t ω) <= b * eps * D) ->
   Rbar_le (LimSup_seq (fun t => Rabs (x t ω))) (b * (1 + eps) * D).
 Proof.
   intros.
   eapply Rbar_le_trans.
   - apply LimSup_le.
     exists 0%nat.
     intros.
     apply H3.
   - eapply Rbar_le_trans.
     + apply LimSup_le with (v := fun t => b * eps * D + (Y t ω)).
       destruct H5.
       exists x0.
       intros.
       apply Rplus_le_compat_r.
       apply H5.
       lia.
     + eapply Rbar_le_trans.
       apply H4.
       replace (b * eps * D + b * D) with  (b * (1 + eps) * D) by lra.
       apply Rbar_le_refl.
 Qed.

  Lemma lemma8_abs_combined  (x Y W : nat -> Ts -> R) 
        (α w : nat -> Ts -> R) (ω : Ts) (β : R) (eps D : posreal) :
    (0 < β) ->
    (Y 0%nat ω = D) ->
    (W 0%nat ω = 0) ->   
   (forall t, 0 <= α t ω <= 1) ->
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (α t ω) * β * D) ->
   (forall t,
     x (S t) ω <= 
     (1 - α t ω) * (x t ω) + 
     (α t ω) * (β * D + w t ω)) ->
   (forall t,
     x (S t) ω >= 
     (1 - α t ω) * (x t ω) + 
     (α t ω) * (-β * D + w t ω)) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   is_lim_seq (fun t => Y t ω) (β * D) ->
   eventually (fun t => Rabs (W t ω) <= β * eps * D) ->
   eventually (fun t => Rabs (x t ω) <=  (β * (1 + 2 * eps) * D)).
  Proof.
    intros.
    apply LimSup_lt_le.
    apply Rbar_le_lt_trans with (y:= β * (1 + eps) * D).
    + apply lemma8_abs_part2 with (Y := Y) (W :=W) (α := α) (w := w); trivial.
      intros.
      apply lemma8_abs with (β := β) (D := D) (α := α) (w := w); trivial.
    + simpl.
      apply Rmult_lt_compat_r; [apply cond_pos |].
      apply Rmult_lt_compat_l; trivial.
      generalize (cond_pos eps); intros.
      lra.
   Qed.

  Lemma lemma8_abs_combined_beta  (x Y W : nat -> Ts -> R) 
        (α β w : nat -> Ts -> R) (ω : Ts) (b : R) (eps D : posreal) :
    (0 < b) ->
    (Y 0%nat ω = D) ->
    (W 0%nat ω = 0) ->   
    (forall t, 0 <= α t ω <= 1) ->
    (forall t, 0 <= β t ω <= 1) ->    
    (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t,
       Y (S t) ω =
       (1 - α t ω) * (Y t ω) +
       (β t ω) * b * D) ->
   (forall t,
     x (S t) ω <= 
     (1 - α t ω) * (x t ω) + 
     (β t ω) * (b * D + w t ω)) ->
   (forall t,
     x (S t) ω >= 
     (1 - α t ω) * (x t ω) + 
     (β t ω) * (-b * D + w t ω)) ->
   (forall t,
       Rabs (x t ω) <= D) ->
   (forall C, Rbar_le (LimSup_seq (fun t => C + Y t ω)) (C + (b * D))) ->
   eventually (fun t => Rabs (W t ω) <= b * eps * D) ->
   eventually (fun t => Rabs (x t ω) <=  (b * (1 + 2 * eps) * D)).
  Proof.
    intros.
    apply LimSup_lt_le.
    apply Rbar_le_lt_trans with (y:= b * (1 + eps) * D).
    - apply lemma8_abs_part2_beta with (Y := Y) (W :=W) (α := α) (β := β) (w := w); trivial.
      intros.
      apply lemma8_abs_beta with (b := b) (β := β) (D := D) (α := α) (w := w); trivial.
    - simpl.
      apply Rmult_lt_compat_r; [apply cond_pos |].
      apply Rmult_lt_compat_l; trivial.
      generalize (cond_pos eps); intros.
      lra.
  Qed.

  Lemma lemma8_abs_combined_almost  (x Y W : nat -> Ts -> R) 
        (α w : nat -> Ts -> R) (eps : posreal) (β : R) (D : Ts -> posreal) :
    (0 < β) ->
    (forall ω, Y 0%nat ω = D ω) ->
    (forall ω, W 0%nat ω = 0) ->   
    (forall t ω, 0 <= α t ω <= 1) ->
    (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
    (forall t ω,
        Y (S t) ω =
        (1 - α t ω) * (Y t ω) +
        (α t ω) * β * D ω) ->
    (forall t,
        almost prts (fun ω =>
                       x (S t) ω <= 
                       (1 - α t ω) * (x t ω) + 
                       (α t ω) * (β * D ω + w t ω))) ->
   (forall t,
       almost prts (fun ω =>
                      x (S t) ω >= 
                      (1 - α t ω) * (x t ω) + 
                      (α t ω) * (-β * D ω + w t ω))) ->
   (almost prts (fun ω => forall t,
                     Rabs (x t ω) <= D ω)) ->
   (forall ω, is_lim_seq (fun t => Y t ω) (β * D ω)) ->
   almost prts (fun ω =>
                  eventually (fun t => Rabs (W t ω) <= β * eps * D ω)) ->
   exists (N : Ts -> nat),
     almost prts (fun ω =>
                    forall (t : nat), 
                      (N ω <= t)%nat ->
                      (rvabs (x t) ω) <= (rvscale (β * (1 + 2 * eps)) D ω)).
 Proof.
   intros.
   assert (almost prts (fun ω =>
                           exists N : nat,
                             forall t : nat,
                               (N <= t)%nat ->
                               (rvabs (x t) ω) <=
                               (rvscale (β * (1 + 2 * eps)) (fun x0 : Ts => D x0) ω))).
   {
     revert H7; apply almost_impl.
     apply almost_forall in H5.
     apply almost_forall in H6.
     revert H5; apply almost_impl.
     revert H6; apply almost_impl.     
     revert H9;apply almost_impl, all_almost; intros ?????.
     apply lemma8_abs_combined with  (Y := Y) (W := W) (α := α) (w := w); trivial.
   }
   now apply exists_almost in H10.
 Qed.
    
  Lemma lemma8_abs_combined_almost_beta  (x Y W : nat -> Ts -> R) 
        (α β w : nat -> Ts -> R) (eps : posreal) (b : R) (D : Ts -> posreal) :
    (0 < b) ->
    (forall ω, Y 0%nat ω = D ω) ->
    (forall ω, W 0%nat ω = 0) ->   
    almost prts (fun ω => forall t, 0 <= α t ω <= 1) ->
    almost prts (fun ω => forall t, 0 <= β t ω <= 1) ->    
    (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
    (forall t ω,
        Y (S t) ω =
        (1 - α t ω) * (Y t ω) +
        (β t ω) * b * D ω) ->
    (forall t,
        almost prts (fun ω =>
                       x (S t) ω <= 
                       (1 - α t ω) * (x t ω) + 
                       (β t ω) * (b * D ω + w t ω))) ->
   (forall t,
       almost prts (fun ω =>
                      x (S t) ω >= 
                      (1 - α t ω) * (x t ω) + 
                      (β t ω) * (-b * D ω + w t ω))) ->
   (almost prts (fun ω => forall t,
                     Rabs (x t ω) <= D ω)) ->
   almost prts (fun ω => forall C, 
                    Rbar_le (LimSup_seq (fun t => C + Y t ω)) (C + (b * D ω))) ->
   almost prts (fun ω =>
                  eventually (fun t => 
                                Rabs (W t ω) <= b * eps * D ω)) ->
   exists (N : Ts -> nat),
     almost prts (fun ω =>
                    forall (t : nat), 
                      (N ω <= t)%nat ->
                      (rvabs (x t) ω) <= (rvscale (b * (1 + 2 * eps)) D ω)).
 Proof.
   intros.
   assert (almost prts (fun ω =>
                           exists N : nat,
                             forall t : nat,
                               (N <= t)%nat ->
                               (rvabs (x t) ω) <=
                               (rvscale (b * (1 + 2 * eps)) (fun x0 : Ts => D x0) ω))).
   {
     revert H2; apply almost_impl.
     revert H3; apply almost_impl.
     revert H8; apply almost_impl.
     apply almost_forall in H6.
     apply almost_forall in H7.
     revert H6; apply almost_impl.
     revert H7; apply almost_impl.     
     revert H9; apply almost_impl.
     revert H10;apply almost_impl, all_almost; intros ????????.
     apply lemma8_abs_combined_beta with  (Y := Y) (W := W) (α := α) (β := β) (w := w); trivial.
   }
   now apply exists_almost in H11.
 Qed.

 Lemma lemma8_abs_part2_almost  (x Y W : nat -> Ts -> R) 
      (α w : nat -> Ts -> R) (eps : posreal) (β : R) (D : Ts -> posreal) :
   (forall t ω, 0 <= α t ω <= 1) ->
   (forall ω, W 0%nat ω = 0) ->
   (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t ω,
       Rabs (x t ω) <= Rabs (W t ω) + (Y t ω)) ->
   (forall ω, is_lim_seq (fun t => Y t ω) (β * (D ω))) ->
   almost prts (fun ω => is_lim_seq (fun t => W t ω) 0) ->   
   (exists (T : Ts -> nat),
       (almost prts
               (fun ω =>
                  eventually (fun t => Rabs (W t ω) <= β * eps * D ω)))) ->
   almost prts (fun ω => 
                  Rbar_le (LimSup_seq (fun t => Rabs (x t ω))) (β * (1 + eps) * D ω)).
 Proof.
   intros.
   destruct H5.
   revert H4; apply almost_impl.
   revert H5; apply almost_impl.
   apply all_almost; intros ???.
   now apply lemma8_abs_part2 with (Y := Y) (W := W) (α := α) (w := w).
 Qed.

 Lemma lemma8_abs_part2_almost_beta  (x Y W : nat -> Ts -> R) 
      (α β w : nat -> Ts -> R) (eps : posreal) (b : R) (D : Ts -> posreal) :
   (forall t ω, 0 <= α t ω <= 1) ->
   (forall t ω, 0 <= β t ω <= 1) ->   
   (forall ω, W 0%nat ω = 0) ->
   (forall t ω,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (β t ω) * (w t ω)) ->
   (forall t ω,
       Rabs (x t ω) <= Rabs (W t ω) + (Y t ω)) ->
   (forall C ω, Rbar_le (LimSup_seq (fun t => C + Y t ω)) (C + (b * D ω))) ->
   almost prts (fun ω => is_lim_seq (fun t => W t ω) 0) ->   
   (exists (T : Ts -> nat),
       (almost prts
               (fun ω =>
                  eventually (fun t => 
                                Rabs (W t ω) <= b * eps * D ω)))) ->
   almost prts (fun ω => 
                  Rbar_le (LimSup_seq (fun t => Rabs (x t ω))) (b * (1 + eps) * D ω)).
 Proof.
   intros.
   destruct H6.
   revert H5; apply almost_impl.
   revert H6; apply almost_impl.
   apply all_almost; intros ???.
   now apply lemma8_abs_part2_beta with (Y := Y) (W := W) (α := α) (β := β) (w := w).
 Qed.

 Lemma Y_prod (Y : nat -> Ts -> R) (D : Ts -> R) (β : R) 
      (α : nat -> Ts -> R) :
   (rv_eq (Y 0%nat) D) ->
   (forall t,
       rv_eq (Y (S t))
             (rvplus 
                (rvmult (rvminus (const 1) (α t)) (Y t))
                (rvmult (α t) (rvscale β D)))) ->
   forall t ω,
     Y (S t) ω = prod_f_R0 (fun k => 1 - α k ω) t * ((1 - β) * D ω) + β * D ω.
  Proof.
    intros.
    induction t.
    - rewrite H0.
      rv_unfold'.
      rewrite H.
      simpl.
      lra.
    - rewrite H0.
      rv_unfold'.
      rewrite IHt.
      simpl.
      lra.
  Qed.

 Lemma Y_prod_beta (Y : nat -> Ts -> R) (D : Ts -> R) (β : R) 
      (α beta : nat -> Ts -> R) :
   (forall t ω, 0 <= α t ω <= 1) ->
   (forall t ω, beta t ω <= α t ω) ->   
   (forall ω,  β *  D ω >= 0) ->
   (rv_eq (Y 0%nat) D) ->
   (forall t,
       rv_eq (Y (S t))
             (rvplus 
                (rvmult (rvminus (const 1) (α t)) (Y t))
                (rvmult (beta t) (rvscale β D)))) ->
   forall t ω,
     Y (S t) ω <= prod_f_R0 (fun k => 1 - α k ω) t * ((1 - β) * D ω) + β * D ω.
 Proof.
   intros.
   pose (Y' := fix Y' t :=
           match t with
           | 0 => D
           | S t' => 
               (rvplus 
                  (rvmult (rvminus (const 1) (α t')) (Y' t'))
                  (rvmult (α t') (rvscale β D))) 
           end).
   assert (forall t ω, Y t ω <= Y' t ω).
   {
     intros.
     induction t0.
     - simpl.
       rewrite H2.
       now right.
     - simpl.
       rewrite H3.
       unfold rvmult, rvminus, rvopp, rvplus, rvscale, const.
       apply Rplus_le_compat.
       + apply Rmult_le_compat_l.
         * specialize (H t0 ω0).
           lra.
         * apply IHt0.
       + apply Rmult_le_compat_r.
         * apply Rge_le.
           apply H1.
         * apply H0.
   }
   eapply Rle_trans.
   apply H4.
   rewrite (Y_prod Y' D β α).
   - now right.
   - now simpl.
   - intros.
     now simpl.
 Qed.

  Lemma Y_lim (Y : nat -> Ts -> R) (β : R) (D : Ts -> R)
      (α : nat -> Ts -> R) (ω : Ts):
    β < 1 ->
    (rv_eq (Y 0%nat) D) ->
    (forall t, 0 <= α t ω <= 1) ->
    is_lim_seq (sum_n (fun t => α t ω)) p_infty ->
    (forall t,
        rv_eq (Y (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y t))
                 (rvmult (α t) (rvscale β D)))) ->
    is_lim_seq (fun t => Y t ω) (β * D ω).
  Proof.
    intros.
    apply is_lim_seq_incr_1.
    apply is_lim_seq_ext with (u := fun t =>  prod_f_R0 (fun k : nat => 1 - α k ω) t * ((1 - β) * D ω) + β * D ω).
    - intros.
      rewrite Y_prod with (D := D) (β := β) (α := α); trivial; lra.
    - apply is_lim_seq_plus with (l1 := 0) (l2 := β * D ω).
      + apply is_lim_seq_mult with (l1 := 0) (l2 := (1 - β) * D ω).
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

  Lemma Y_lim_almost (Y : nat -> Ts -> R) (β : R) (D : Ts -> R)
      (α : nat -> Ts -> R) :
    β < 1 ->
    (rv_eq (Y 0%nat) D) ->
    almost prts (fun ω => forall t, 0 <= α t ω <= 1) ->
    almost prts (fun ω => is_lim_seq (sum_n (fun t => α t ω)) p_infty) ->
    (forall t,
        rv_eq (Y (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y t))
                 (rvmult (α t) (rvscale β D)))) ->
    almost prts (fun ω =>
      is_lim_seq (fun t => Y t ω) (β * D ω)).
  Proof.
    intros.
    revert H1; apply almost_impl.
    revert H2; apply almost_impl.
    apply all_almost; intros ???.
    now apply Y_lim with (α := α).
 Qed.

  Lemma Y_alpha_beta_le (Y1 Y2 α beta : nat -> Ts -> R) (β : R) (D : Ts -> R) (ω : Ts):
    β * D ω >= 0 ->
    (rv_eq (Y1 0%nat) D) ->
    (rv_eq (Y2 0%nat) D) ->    
    (forall t, 0 <= α t ω <= 1) ->
    (forall t, beta t ω <= α t ω) ->
    (forall t,
        rv_eq (Y1 (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y1 t))
                 (rvmult (beta t) (rvscale β D)))) ->
    (forall t,
        rv_eq (Y2 (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y2 t))
                 (rvmult (α t) (rvscale β D)))) ->
    forall t,
        Y1 t ω <=  Y2 t ω.
  Proof.
    intros.
    induction t.
    - rewrite H0, H1.
      lra.
    - rewrite H4, H5.
      unfold rvminus, rvplus, rvmult, const, rvopp, rvscale.
      apply Rplus_le_compat.
      + apply Rmult_le_compat_l; trivial.
        specialize (H2 t).
        lra.
      + apply Rmult_le_compat_r; trivial.
        now apply Rge_le.
   Qed.

  Lemma Y_alpha_beta_le_almost  (Y1 Y2 α beta : nat -> Ts -> R) (β : R) (D : Ts -> R) :
    (forall ω,  β * D ω >= 0) ->
    (rv_eq (Y1 0%nat) D) ->
    (rv_eq (Y2 0%nat) D) ->    
    almost prts (fun ω => forall t, 0 <= α t ω <= 1) ->
    almost prts (fun ω => forall t, beta t ω <= α t ω) ->
    (forall t,
        rv_eq (Y1 (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y1 t))
                 (rvmult (beta t) (rvscale β D)))) ->
    (forall t,
        rv_eq (Y2 (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y2 t))
                 (rvmult (α t) (rvscale β D)))) ->
    almost prts (fun ω => forall t,
                     Y1 t ω <=  Y2 t ω).
  Proof.
    intros.
    revert H2; apply almost_impl.
    revert H3; apply almost_impl.
    apply all_almost; intros ????.
    apply Y_alpha_beta_le with (α := α) (β := β) (D := D) (beta := beta); trivial.
   Qed.

  Lemma Y_lim_beta (Y : nat -> Ts -> R) (β : R) (D : Ts -> R)
      (α beta : nat -> Ts -> R)  (ω : Ts) :
    β < 1 ->
    β * D ω >= 0 ->
    (rv_eq (Y 0%nat) D) ->
    (forall t, 0 <= α t ω <= 1) ->
    (forall t, 0 <= beta t ω <= 1) ->
    (forall t, beta t ω <= α t ω) ->
    is_lim_seq (sum_n (fun t => α t ω)) p_infty ->
    (forall t,
        rv_eq (Y (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y t))
                 (rvmult (beta t) (rvscale β D)))) ->
    forall eps : posreal, 
      eventually (fun n =>  Y n ω - β * D ω < eps).
  Proof.
    intros.
    pose (Y' := fix Y' t :=
           match t with
           | 0 => D
           | S t' => 
               (rvplus 
                  (rvmult (rvminus (const 1) (α t')) (Y' t'))
                  (rvmult (α t') (rvscale β D))) 
           end).
   generalize (Y_alpha_beta_le Y Y' α beta β D ω); intros.
   cut_to H7; trivial.
   - generalize (Y_lim Y' β D α ω H); intros.
     cut_to H8; trivial.
     + apply is_lim_seq_spec in H8.
       specialize (H8 eps).
       destruct H8.
       exists x.
       intros.
       specialize (H8 n H9).
       apply Rabs_def2 in H8.
       destruct H8.
       eapply Rle_lt_trans; cycle 1.
       apply H8.
       specialize (H7 n).
       lra.
     + now simpl.
     + intros.
       now simpl.
    - now unfold Y'.
    - intros.
      now simpl.
  Qed.

  Lemma Y_limsup_beta_const (Y : nat -> Ts -> R) (β : R) (D : Ts -> R)
      (α beta : nat -> Ts -> R) (ω : Ts):
    β < 1 ->
    β * D ω >= 0 ->
    (rv_eq (Y 0%nat) D) ->
    (forall t, 0 <= α t ω <= 1) ->
    (forall t, 0 <= beta t ω <= 1) ->
    (forall t, beta t ω <= α t ω) ->
    is_lim_seq (sum_n (fun t => α t ω)) p_infty ->
    (forall t,
        rv_eq (Y (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y t))
                 (rvmult (beta t) (rvscale β D)))) ->
    forall C,
      Rbar_le (LimSup_seq (fun n => C + Y n  ω)) (C + β * D ω). 
  Proof.
    intros.
    pose (Y' := fix Y' t :=
           match t with
           | 0 => D
           | S t' => 
               (rvplus 
                  (rvmult (rvminus (const 1) (α t')) (Y' t'))
                  (rvmult (α t') (rvscale β D))) 
           end).
   generalize (Y_alpha_beta_le Y Y' α beta β D ω); intros.
   cut_to H7; trivial.
   - generalize (Y_lim Y' β D α ω H); intros.
     cut_to H8; trivial.
     + assert (is_lim_seq (fun t : nat => C + Y' t ω) (C + β * D ω)).
       {
         apply is_lim_seq_plus'; trivial.
         apply is_lim_seq_const.
       }
       assert (LimSup_seq (fun t : nat => C + Y' t ω) = C + (β * D ω)).
       {
         apply is_lim_LimSup_seq in H9.
         apply is_LimSup_seq_unique in H9.
         now rewrite H9.
       }
       rewrite <- H10.
       apply LimSup_le.
       exists (0%nat).
       intros.
       specialize (H7 n).
       lra.
     + now simpl.
     + intros.
       now simpl.
   - now simpl.
   - intros.
     now simpl.
 Qed.

  Lemma Y_limsup_beta_const_almost (Y : nat -> Ts -> R) (β : R) (D : Ts -> R)
      (α beta : nat -> Ts -> R) :
    β < 1 ->
    (forall ω,  β * D ω >= 0) ->
    (rv_eq (Y 0%nat) D) ->
    almost prts (fun ω => forall t, 0 <= α t ω <= 1) ->
    almost prts (fun ω => forall t, 0 <= beta t ω <= 1) ->
    almost prts (fun ω => forall t, beta t ω <= α t ω) ->        
    almost prts (fun ω => is_lim_seq (sum_n (fun t => α t ω)) p_infty) ->
    (forall t,
        rv_eq (Y (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y t))
                 (rvmult (beta t) (rvscale β D)))) ->
    almost prts (fun ω => forall C,
                     Rbar_le (LimSup_seq (fun n => C + Y n  ω)) (C + β * D ω)). 
  Proof.
    intros.
    pose (Y' := fix Y' t :=
           match t with
           | 0 => D
           | S t' => 
               (rvplus 
                  (rvmult (rvminus (const 1) (α t')) (Y' t'))
                  (rvmult (α t') (rvscale β D))) 
           end).
   generalize (Y_alpha_beta_le_almost Y Y' α beta β D); intros.
   cut_to H7; trivial.
   generalize (Y_lim_almost Y' β D α H); intros.
   cut_to H8; trivial.
   - revert H7; apply almost_impl.
     revert H8; apply almost_impl.
     apply all_almost; intros ????.
     assert (is_lim_seq (fun t : nat => C + Y' t x) (C + β * D x)).
     {
       apply is_lim_seq_plus'; trivial.
       apply is_lim_seq_const.
     }
     assert (LimSup_seq (fun t : nat => C + Y' t x) = C + (β * D x)).
     {
       apply is_lim_LimSup_seq in H9.
       apply is_LimSup_seq_unique in H9.
       now rewrite H9.
     }
     rewrite <- H10.
     apply LimSup_le.
     exists (0%nat).
     intros.
     specialize (H8 n).
     lra.
   - now simpl.
   - intros.
     now simpl.
   - now simpl.
   - intros.
     now simpl.
Qed.     

(*
  Lemma vecrvminus_unfold {n} (x y : Ts -> vector R n) :
    rv_eq (vecrvminus x y) (fun ω => Rvector_minus (x ω) (y ω)).
  Proof.
    intros ?.
    now unfold vecrvminus, Rvector_minus, vecrvplus.
  Qed.
*)

  Lemma lemma3_pre0  (ω : Ts) (ε : posreal)
        (G M : nat -> Ts -> R) :
    is_lim_seq (fun k => M k ω) p_infty ->
    (forall t, (M t ω) <= (rvscale (1 + ε) (G t)) ω) ->
    (forall t, (G t ω) <= (G (S t) ω)) ->
    (forall t,
        (G t ω < G (S t) ω) ->
        (M (S t) ω <= G (S t) ω)) ->
    forall (t : nat),
       exists (t0 : nat),
         (t0 >= t)%nat /\
         M t0 ω <= G t0 ω .
  Proof.
    intros.
    assert (is_lim_seq (fun k => G k ω) p_infty).
    {
      assert (is_lim_seq (fun k => (rvscale (1 + ε) (G k)) ω) p_infty).
      {
        apply is_lim_seq_le_p_loc with (u := (fun k => M k ω)); trivial.
        exists 0%nat.
        intros.
        apply H0.
      }
      generalize (is_lim_seq_scal_l (fun k : nat => rvscale (1 + ε) (G k) ω)
                                    (/ (1 + ε)) _ H3); intros.
      replace (Rbar_mult (/ (1 + ε)) p_infty) with p_infty in H4.
      - revert H4.
        apply is_lim_seq_ext.
        intros.
        unfold rvscale.
        rewrite <- Rmult_assoc.
        rewrite Rinv_l; try lra.
        generalize (cond_pos ε); lra.
      - rewrite Rbar_mult_comm.
        symmetry; apply Rbar_mult_p_infty_pos.
        apply Rinv_0_lt_compat.
        generalize (cond_pos ε); lra.        
    }
    assert (exists t0, (t0 >= t)%nat /\ M t0 ω <= G t0 ω).
    {
      assert (exists t0, (t0 >= t)%nat /\ G t0 ω  < G (S t0) ω).
      {
        rewrite is_lim_seq_incr_n with (N := S t) in H3.
        apply is_lim_seq_spec in H3.
        unfold is_lim_seq' in H3.
        specialize (H3 (G t ω)).
        destruct H3.
        revert H3.
        contrapose.
        intros.
        push_neg.
        push_neg_in H3.
        assert (forall x0, (x0 >= t)%nat -> G x0 ω = G t ω).
        {
          intros.
          pose (h := (x0 - t)%nat).
          replace x0 with (h + t)%nat by lia.
          induction h.
          - now simpl.
          - rewrite <- IHh.
            replace (S h + t)%nat with (S (h + t)) by lia.
            specialize (H3 (h + t)%nat).
            cut_to H3; try lia.
            specialize (H1 (h + t)%nat).
            lra.
        }
        specialize (H4 (x + S t)%nat).
        exists x.
        split; try lia.
        cut_to H4; try lia; try lra.
      }
      destruct H4 as [? [? ?]].
      exists (S x).
      split; try lia.
      now apply H2.
    }
    destruct H4 as [? [? ?]].
    exists x.
    now split.
  Qed.

  Lemma lemma3_pre1 {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R)
        (ω : Ts) (ε : posreal)
        (α ww : nat -> Ts -> vector R (S n)) :
    (forall i pf t0, W i pf 0%nat t0 ω = 0) ->
    
    (forall i pf t, 0 <= vecrvnth i pf (α t) ω <= 1) ->
    (forall i pf t0 t,
        W i pf (S t) t0 ω =
        (1 - vecrvnth i pf (α (t + t0)%nat) ω) * (W i pf t t0 ω) +
        (vecrvnth i pf (α (t + t0)%nat) ω) * (vecrvnth i pf (ww (t + t0)%nat) ω)) ->

    (forall i pf, is_lim_seq (fun n : nat => W i pf n 0%nat ω) 0) ->

    exists (T : nat),
      forall i pf t0 t,
        (t0 >= T)%nat ->
        Rabs (W i pf t t0 ω) <= ε.
  Proof.
    intros.
    assert (forall i pf,
               exists T,
                 forall t0 t,
                   (t0 >= T)%nat ->
                   Rabs (W i pf t t0 ω) <= ε).
    {
      intros.
      generalize (lemma2 (W i pf) ω 
                         (fun t => vecrvnth i pf (α t)) 
                         (fun t => vecrvnth i pf (ww t)) 
                         (H i pf) (H0 i pf) (H1 i pf) (H2 i pf) ε); intros.
      destruct H3.
      exists x.
      intros.
      now apply H3.
    }
    assert (forall (i : nat) (pf : (i < S n)%nat),
               exists T : nat, forall t0: nat, (t0 >= T)%nat ->
                                               forall t, Rabs (W i pf t t0 ω) <= ε).
    {
      intros.
      destruct (H3 i pf).
      exists x.
      intros.
      now apply H4.
    }
    generalize (bounded_nat_ex_choice_vector 
                  (A := nat) (n := S n)
                  (fun i pf N =>
                     forall t0, (t0>=N)%nat -> 
                                forall t,
                                  Rabs (W i pf t t0 ω) <= ε)); intros.
    cut_to H5.
    - destruct H5.
      exists (list_max (proj1_sig x)).
      intros.
      apply H5.
      apply list_max_le in H6.
      rewrite Forall_forall in H6.
      specialize (H6 (vector_nth i pf x)).
      apply H6.
      apply vector_nth_In.
    - intros.
      apply H4.
   Qed.

  Lemma lemma3_pre1_beta {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R)
        (ω : Ts) (ε : posreal)
        (α β ww : nat -> Ts -> vector R (S n)) :
    (forall i pf t0, W i pf 0%nat t0 ω = 0) ->
    
    (forall i pf t, 0 <= vecrvnth i pf (α t) ω <= 1) ->
    (forall i pf t, 0 <= vecrvnth i pf (β t) ω <= 1) ->    
    (forall i pf t0 t,
        W i pf (S t) t0 ω =
        (1 - vecrvnth i pf (α (t + t0)%nat) ω) * (W i pf t t0 ω) +
        (vecrvnth i pf (β (t + t0)%nat) ω) * (vecrvnth i pf (ww (t + t0)%nat) ω)) ->

    (forall i pf, is_lim_seq (fun n : nat => W i pf n 0%nat ω) 0) ->

    exists (T : nat),
      forall i pf t0 t,
        (t0 >= T)%nat ->
        Rabs (W i pf t t0 ω) <= ε.
  Proof.
    intros.
    assert (forall i pf,
               exists T,
                 forall t0 t,
                   (t0 >= T)%nat ->
                   Rabs (W i pf t t0 ω) <= ε).
    {
      intros.
      generalize (lemma2_beta (W i pf) ω 
                    (fun t => vecrvnth i pf (α t))
                    (fun t => vecrvnth i pf (β t))                     
                    (fun t => vecrvnth i pf (ww t)) 
                    (H i pf) (H0 i pf) (H1 i pf) (H2 i pf) (H3 i pf) ε); intros.
      destruct H4.
      exists x.
      intros.
      now apply H4.
    }
    assert (forall (i : nat) (pf : (i < S n)%nat),
               exists T : nat, forall t0: nat, (t0 >= T)%nat ->
                                               forall t, Rabs (W i pf t t0 ω) <= ε).
    {
      intros.
      destruct (H4 i pf).
      exists x.
      intros.
      now apply H5.
    }
    generalize (bounded_nat_ex_choice_vector 
                  (A := nat) (n := S n)
                  (fun i pf N =>
                     forall t0, (t0>=N)%nat -> 
                                forall t,
                                  Rabs (W i pf t t0 ω) <= ε)); intros.
    cut_to H6.
    - destruct H6.
      exists (list_max (proj1_sig x)).
      intros.
      apply H6.
      apply list_max_le in H7.
      rewrite Forall_forall in H7.
      specialize (H7 (vector_nth i pf x)).
      apply H7.
      apply vector_nth_In.
    - intros.
      apply H5.
   Qed.

  Lemma lemma3 {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R) (ω : Ts) (ε G0 :R)
        (t0 : nat) (α x ww : nat -> Ts -> vector R (S n)) (M G : nat -> Ts -> R) 
        (XF : nat -> vector R (S n) -> vector R (S n)) :
    (forall i pf, W i pf 0%nat t0 ω = 0) ->
    M t0 ω <= G t0 ω ->
    (forall t, M (S t) ω <= (1 + ε) * G t ω -> G (S t) ω = G t ω) ->
    (forall t, M t ω <= (1 + ε) * G t ω) ->
    (forall t, M (S t) ω = Rmax (M t ω) (rvmaxabs (x (S t)) ω)) ->
    (forall t i pf, Rabs (vecrvnth i pf (x t) ω) <= M t ω) -> 
    (forall t i pf, 0 <= vecrvnth i pf (α t) ω <= 1) ->
    (forall t i pf,
        W i pf (S t) t0 ω =
        (1 - vecrvnth i pf (α (t + t0)%nat) ω) * (W i pf t t0 ω) +
        (vecrvnth i pf (α (t + t0)%nat) ω) * (vecrvnth i pf (ww (t + t0)%nat) ω)) ->
    (forall k, rv_eq (x (S k)) 
                     (vecrvplus (x k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (x k ω)) (x k) ) (vecrvscalerv (G k) (ww k)))))) ->
    (forall k i pf, rv_le (rvabs (vecrvnth i pf (fun ω => XF k (x k ω)))) (G k)) ->
    (forall t i pf, Rabs (W i pf t t0 ω) <= ε) -> 
    forall t i pf,
      (-1 + (W i pf t t0 ω)) * (G t0 ω) <= vecrvnth i pf (x (t + t0)%nat) ω <= (1 + (W i pf t t0 ω)) * (G t0 ω) /\
      G (t + t0)%nat ω = G t0 ω.
  Proof.
    intros W0 MleGt0 MGprop MGprop2 Mxprop Mprop alphaprop Wprop xdef XFle (* xbounds *) Weps.
    induction t.
    - intros; simpl; split; trivial.
      rewrite W0.
      do 2 rewrite Rplus_0_r.
      rewrite Rmult_1_l.
      split.
      + specialize (Mprop t0 i pf).
        assert (Rabs (vecrvnth i pf (x t0) ω) <= G t0 ω) by lra.
        rewrite Rabs_le_between in H.
        lra.
      + apply Rle_trans with (r2 := Rabs (vecrvnth i pf (x t0) ω)).
        * apply Rle_abs.
        * now eapply Rle_trans.
    - replace (S t + t0)%nat with (S (t + t0)) by lia.
      assert (xbounds1 : (forall t i pf,
        (1 - vecrvnth i pf (α t) ω) * (vecrvnth i pf (x t) ω) + 
        (vecrvnth i pf (α t) ω) * ((-G t ω) + (vecrvnth i pf (ww t) ω) * (G t ω)) <= 
        vecrvnth i pf (x (S t)) ω <= 
        (1 - vecrvnth i pf (α t) ω) * (vecrvnth i pf (x t) ω) + 
        (vecrvnth i pf (α t) ω) * (G t ω + (vecrvnth i pf (ww t) ω) * (G t ω)))).
      {
        intros.
        unfold vecrvnth.
        rewrite xdef.
        specialize (XFle t1 i pf ω).
        unfold rvabs in XFle.
        rewrite Rabs_le_between in XFle.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscalerv, vecrvscale.
        rewrite Rvector_nth_plus, Rvector_nth_mult.
        rewrite Rvector_nth_plus, Rvector_nth_plus, Rvector_nth_scale.
        rewrite Rvector_nth_scale.
        split.
        - ring_simplify.
          unfold Rminus.
          do 4 rewrite Rplus_assoc.
          do 2 apply Rplus_le_compat_l.
          apply Rplus_le_compat_r.
          rewrite Ropp_mult_distr_r.
          apply Rmult_le_compat_l.
          + apply alphaprop.
          + apply XFle.
        - ring_simplify.
          unfold Rminus.
          do 4 rewrite Rplus_assoc.
          do 2 apply Rplus_le_compat_l.
          rewrite Rplus_comm.
          apply Rplus_le_compat_l.
          apply Rmult_le_compat_l.
          + apply alphaprop.
          + apply XFle.
      }
                
      assert (forall i pf, (-1 + (W i pf(S t) t0 ω)) * G t0 ω <= vecrvnth i pf (x (S (t + t0))) ω <= (1 + (W i pf (S t) t0 ω)) * G t0 ω).
      {
        intros.
        split.
        - eapply Rle_trans.
          shelve.
          apply xbounds1.
          Unshelve.
          specialize (alphaprop (t + t0)%nat i pf).
          destruct (IHt i pf).
          destruct H.
          apply Rmult_le_compat_l with (r := (1 - vecrvnth i pf (α (t + t0)%nat) ω)) in H; try lra.
          apply Rplus_le_compat_r with (r :=  vecrvnth i pf (α (t + t0)%nat) ω * (-G (t + t0)%nat ω + vecrvnth i pf (ww (t + t0)%nat) ω * G t0 ω)) in H.
          eapply Rle_trans.
          shelve.
          rewrite H0 at 2.
          apply H.
          Unshelve.
          rewrite Wprop, H0.
          ring_simplify.
          lra.
        - eapply Rle_trans.
          apply xbounds1.
          specialize (alphaprop (t + t0)%nat i pf).
          destruct (IHt i pf).
          destruct H.
          apply Rmult_le_compat_l with (r := (1 - vecrvnth i pf (α (t + t0)%nat) ω)) in H1; try lra.
          rewrite H0.
          apply Rplus_le_compat_r with (r :=  vecrvnth i pf (α (t + t0)%nat) ω * (G t0 ω + (vecrvnth i pf (ww (t + t0)%nat) ω) * (G t0 ω))) in H1.
          eapply Rle_trans.
          apply H1.
          rewrite Wprop.
          ring_simplify.
          lra.
      }
      intros.
      split;trivial.
      assert (forall i pf,
                 Rabs (vecrvnth i pf (x (S (t + t0))) ω) <= (G t0 ω) * (1 + ε)).
      {
        intros.
        rewrite Rabs_le_between.
        destruct (H i0 pf0).
        specialize (Weps (S t) i0 pf0).
        apply Rabs_le_between in Weps.
        split.
        - eapply Rle_trans.
          shelve.
          apply H0.
          Unshelve.
          replace (- (G t0 ω * (1 + ε))) with ((- (1 + ε)) * (G t0 ω)) by lra.
          apply Rmult_le_compat_r; try lra.          
        - eapply Rle_trans.
          apply H1.
          rewrite Rmult_comm.
          apply Rmult_le_compat_l; try lra.
      }
      destruct (IHt i pf).
      rewrite <- H2.
      apply MGprop.
      rewrite H2.
      specialize (MGprop2 (t + t0)%nat).
      rewrite H2 in MGprop2.
      rewrite Mxprop.
      apply Rmax_lub; trivial.
      rewrite Rmult_comm.
      unfold rvmaxabs.
      apply Rvector_max_abs_nth_Rabs_le.
      intros.
      apply H0.
   Qed.

  Lemma lemma3_Jaakkola_beta {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R) (ω : Ts) (ε G0 :R)
    (t0 : nat) (α β x ww : nat -> Ts -> vector R (S n)) (M G : nat -> Ts -> R) (XF : nat -> Ts -> vector R (S n)) :
    (forall i pf, W i pf 0%nat t0 ω = 0) ->
    M t0 ω <= G t0 ω ->
    (forall t, M (S t) ω <= (1 + ε) * G t ω -> G (S t) ω = G t ω) ->
    (forall t, M t ω <= (1 + ε) * G t ω) ->
    (forall t, M (S t) ω = Rmax (M t ω) (rvmaxabs (x (S t)) ω)) ->
    (forall t i pf, Rabs (vecrvnth i pf (x t) ω) <= M t ω) -> 
    (forall t i pf, 0 <= vecrvnth i pf (α t) ω <= 1) ->
    (forall t i pf, 0 <= vecrvnth i pf (β t) ω <= 1) ->
    (forall t i pf, vecrvnth i pf (β t) ω <= vecrvnth i pf (α t) ω) ->    
    (forall t i pf,
        W i pf (S t) t0 ω =
        (1 - vecrvnth i pf (α (t + t0)%nat) ω) * (W i pf t t0 ω) +
        (vecrvnth i pf (β (t + t0)%nat) ω) * (vecrvnth i pf (ww (t + t0)%nat) ω)) ->
    (forall k, rv_eq (x (S k)) 
                     (vecrvplus (vecrvminus (x k) (vecrvmult (α k) (x k))) (vecrvmult (β k) (vecrvplus (XF k) (vecrvscalerv (G k) (ww k)))))) ->
    (forall k i pf, Rabs (vecrvnth i pf (XF k) ω) <= G k ω) ->
    (forall t i pf, Rabs (W i pf t t0 ω) <= ε) -> 
    forall t i pf,
      (-1 + (W i pf t t0 ω)) * (G t0 ω) <= vecrvnth i pf (x (t + t0)%nat) ω <= (1 + (W i pf t t0 ω)) * (G t0 ω) /\
      G (t + t0)%nat ω = G t0 ω.
  Proof.
    intros W0 MleGt0 MGprop MGprop2 Mxprop Mprop alphaprop betaprop alpha_beta_prop Wprop xdef XFle (* xbounds *) Weps.
    induction t.
    - intros; simpl; split; trivial.
      rewrite W0.
      do 2 rewrite Rplus_0_r.
      rewrite Rmult_1_l.
      split.
      + specialize (Mprop t0 i pf).
        assert (Rabs (vecrvnth i pf (x t0) ω) <= G t0 ω) by lra.
        rewrite Rabs_le_between in H.
        lra.
      + apply Rle_trans with (r2 := Rabs (vecrvnth i pf (x t0) ω)).
        * apply Rle_abs.
        * now eapply Rle_trans.
    - replace (S t + t0)%nat with (S (t + t0)) by lia.
      assert (xbounds1 : (forall t i pf,
        (1 - vecrvnth i pf (α t) ω) * (vecrvnth i pf (x t) ω) + 
        (vecrvnth i pf (β t) ω) * ((-G t ω) + (vecrvnth i pf (ww t) ω) * (G t ω)) <= 
        vecrvnth i pf (x (S t)) ω <= 
        (1 - vecrvnth i pf (α t) ω) * (vecrvnth i pf (x t) ω) + 
        (vecrvnth i pf (β t) ω) * (G t ω + (vecrvnth i pf (ww t) ω) * (G t ω)))).
      {
        intros.
        unfold vecrvnth.
        rewrite xdef.
        specialize (XFle t1 i pf).
        unfold rvabs in XFle.
        rewrite Rabs_le_between in XFle.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscalerv, vecrvscale.
        rewrite Rvector_nth_plus, Rvector_nth_mult.
        rewrite Rvector_nth_plus, Rvector_nth_plus, Rvector_nth_scale.
        rewrite Rvector_nth_mult, Rvector_nth_scale.
        split.
        - rewrite Rmult_minus_distr_r, Rmult_1_l.
          apply Rplus_le_reg_l with (r := vector_nth i pf (α t1 ω) * vector_nth i pf (x t1 ω)).
          ring_simplify.
          apply Rplus_le_compat_l.
          rewrite Ropp_mult_distr_r.
          apply Rmult_le_compat_l.
          + apply betaprop.
          + apply XFle.
        - ring_simplify.
          unfold Rminus.
          do 4 rewrite Rplus_assoc.
          do 2 apply Rplus_le_compat_l.
          rewrite Rplus_comm.
          apply Rplus_le_compat_l.
          apply Rmult_le_compat_l.
          + apply betaprop.
          + apply XFle.
      }
                
      assert (forall i pf, (-1 + (W i pf(S t) t0 ω)) * G t0 ω <= vecrvnth i pf (x (S (t + t0))) ω <= (1 + (W i pf (S t) t0 ω)) * G t0 ω).
      {
        intros.
        assert (Gb_small: (- (G t0 ω * vecrvnth i pf (β (t + t0)%nat) ω) + G t0 ω * vecrvnth i pf (α (t + t0)%nat) ω >= 0)).
        {
          specialize (alpha_beta_prop (t + t0)%nat i pf).
          assert  (0 <= G t0 ω).
          {
            assert (0 < S n)%nat by lia.
            specialize (XFle t0 0%nat H).
            unfold rvabs in XFle.
            eapply Rle_trans; cycle 1.
            apply XFle.
            apply Rabs_pos.
          }
          replace  (- (G t0 ω * vecrvnth i pf (β (t + t0)%nat) ω) + G t0 ω * vecrvnth i pf (α (t + t0)%nat) ω) with
             (G t0 ω * ( vecrvnth i pf (α (t + t0)%nat) ω - vecrvnth i pf (β (t + t0)%nat) ω)) by ring.
          apply Rle_ge.
          apply Rmult_le_pos; lra.
        }
        split.
        - eapply Rle_trans; cycle 1.
          apply xbounds1.
          specialize (alphaprop (t + t0)%nat i pf).
          destruct (IHt i pf).
          destruct H.
          apply Rmult_le_compat_l with (r := (1 - vecrvnth i pf (α (t + t0)%nat) ω)) in H; try lra.
          apply Rplus_le_compat_r with (r :=  vecrvnth i pf (β (t + t0)%nat) ω * (-G (t + t0)%nat ω + vecrvnth i pf (ww (t + t0)%nat) ω * G t0 ω)) in H.
          eapply Rle_trans.
          shelve.
          rewrite H0 at 2.
          apply H.
          Unshelve.
          rewrite Wprop, H0.
          lra.
        - eapply Rle_trans.
          apply xbounds1.
          specialize (alphaprop (t + t0)%nat i pf).
          specialize (betaprop (t + t0)%nat i pf).          
          destruct (IHt i pf).
          destruct H.
          apply Rmult_le_compat_l with (r := (1 - vecrvnth i pf (α (t + t0)%nat) ω)) in H1; try lra.
          rewrite H0.
          apply Rplus_le_compat_r with (r :=  vecrvnth i pf (β (t + t0)%nat) ω * (G t0 ω + (vecrvnth i pf (ww (t + t0)%nat) ω) * (G t0 ω))) in H1.
          eapply Rle_trans.
          apply H1.
          rewrite Wprop.
          ring_simplify.
          lra.
      }
      intros.
      split;trivial.
      assert (forall i pf,
                 Rabs (vecrvnth i pf (x (S (t + t0))) ω) <= (G t0 ω) * (1 + ε)).
      {
        intros.
        rewrite Rabs_le_between.
        destruct (H i0 pf0).
        specialize (Weps (S t) i0 pf0).
        apply Rabs_le_between in Weps.
        split.
        - eapply Rle_trans.
          shelve.
          apply H0.
          Unshelve.
          replace (- (G t0 ω * (1 + ε))) with ((- (1 + ε)) * (G t0 ω)) by lra.
          apply Rmult_le_compat_r; try lra.          
        - eapply Rle_trans.
          apply H1.
          rewrite Rmult_comm.
          apply Rmult_le_compat_l; try lra.
      }
      destruct (IHt i pf).
      rewrite <- H2.
      apply MGprop.
      rewrite H2.
      specialize (MGprop2 (t + t0)%nat).
      rewrite H2 in MGprop2.
      rewrite Mxprop.
      apply Rmax_lub; trivial.
      rewrite Rmult_comm.
      unfold rvmaxabs.
      apply Rvector_max_abs_nth_Rabs_le.
      intros.
      apply H0.
  Qed.
  
   Lemma lemma3_almost {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R) (ε G0 :R)
         (α x ww : nat -> Ts -> vector R (S n)) (M G : nat -> Ts -> R) 
        (XF : nat -> vector R (S n) -> vector R (S n)) :
(*    (forall ω, M t0 ω <= G t0 ω) -> *)
    (forall ω t, M (S t) ω <= (1 + ε) * G t ω -> G (S t) ω = G t ω) ->
    (forall ω t, M t ω <= (1 + ε) * G t ω) ->
    (forall ω t, M (S t) ω = Rmax (M t ω) (rvmaxabs (x (S t)) ω)) ->
    (forall ω t i pf, Rabs (vecrvnth i pf (x t) ω) <= M t ω) -> 
    (forall ω t i pf, 0 <= vecrvnth i pf (α t) ω <= 1) ->
    (forall ω t t0 i pf,
        W i pf (S t) t0 ω =
        (1 - vecrvnth i pf (α (t + t0)%nat) ω) * (W i pf t t0 ω) +
        (vecrvnth i pf (α (t + t0)%nat) ω) * (vecrvnth i pf (ww (t + t0)%nat) ω)) ->
    (forall ω i pf t0, W i pf 0%nat t0 ω = 0) ->
    (forall k, rv_eq (x (S k)) 
                     (vecrvplus (x k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (x k ω)) (x k) ) (vecrvscalerv (G k) (ww k)))))) ->
    (forall k i pf, rv_le (rvabs (vecrvnth i pf (fun ω => XF k (x k ω)))) (G k)) ->
    almost prts
          (fun ω : Ts =>
           is_lim_seq (fun k : nat => M k ω) p_infty ->
           exists t0 : nat,
             M t0 ω <= G t0 ω /\
             (forall (t i : nat) (pf : (i < (S n))%nat), Rabs (W i pf t t0 ω) <= ε)) ->
(*    (almost prts (fun ω => forall t i pf, Rabs (W i pf t t0 ω) <= ε)) ->  *)
    almost prts (fun ω => 
           is_lim_seq (fun k : nat => M k ω) p_infty ->                   
           exists t0, forall t, G (t + t0)%nat ω = G t0 ω).
   Proof.
     intros.
     revert H8.
     apply almost_impl, all_almost; intros ???.
     specialize (H8 H9).
     destruct H8 as [t0 [? ?]].
     assert (forall t (i: nat) (pf : (i < S n)%nat), G (t + t0)%nat x0 = G t0 x0).
     {
       intros.
       generalize (lemma3 W x0 ε G0 t0 α x ww M G XF); intros.
       cut_to H11; try easy.
       - now specialize (H11 t i pf).
       - apply H.
     }
     intros.
     assert (0 < S n)%nat by lia.
     exists t0.
     intros.
     now specialize (H11 t _ H12).
   Qed.
    

   Lemma lemma3_almost_Jaakkola_beta {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R) (ε G0 :R)
         (α β x ww : nat -> Ts -> vector R (S n)) (M G : nat -> Ts -> R) 
        (XF : nat -> Ts -> vector R (S n)) :
(*    (forall ω, M t0 ω <= G t0 ω) -> *)
    (forall ω t, M (S t) ω <= (1 + ε) * G t ω -> G (S t) ω = G t ω) ->
    (forall ω t, M t ω <= (1 + ε) * G t ω) ->
    (forall ω t, M (S t) ω = Rmax (M t ω) (rvmaxabs (x (S t)) ω)) ->
    (forall ω t i pf, Rabs (vecrvnth i pf (x t) ω) <= M t ω) -> 
    almost prts (fun ω => forall t i pf, 0 <= vecrvnth i pf (α t) ω <= 1) ->
    almost prts (fun ω => forall t i pf, 0 <= vecrvnth i pf (β t) ω <= 1) ->
    almost prts (fun ω => forall t i pf, vecrvnth i pf (β t) ω <= vecrvnth i pf (α t) ω) ->        
    (forall ω t t0 i pf,
        W i pf (S t) t0 ω =
        (1 - vecrvnth i pf (α (t + t0)%nat) ω) * (W i pf t t0 ω) +
        (vecrvnth i pf (β (t + t0)%nat) ω) * (vecrvnth i pf (ww (t + t0)%nat) ω)) ->
    (forall ω i pf t0, W i pf 0%nat t0 ω = 0) ->
    (forall k, rv_eq (x (S k)) 
                     (vecrvplus (vecrvminus (x k) (vecrvmult (α k) (x k))) (vecrvmult (β k) (vecrvplus (XF k) (vecrvscalerv (G k) (ww k)))))) ->
    almost prts 
      (fun ω =>
         forall k i pf, (rvabs (vecrvnth i pf (XF k ))) ω <= G k ω) ->
    almost prts
      (fun ω : Ts =>
           is_lim_seq (fun k : nat => M k ω) p_infty ->
           exists t0 : nat,
             M t0 ω <= G t0 ω /\
             (forall (t i : nat) (pf : (i < (S n))%nat), Rabs (W i pf t t0 ω) <= ε)) ->
(*    (almost prts (fun ω => forall t i pf, Rabs (W i pf t t0 ω) <= ε)) ->  *)
    almost prts (fun ω => 
           is_lim_seq (fun k : nat => M k ω) p_infty ->                   
           exists t0, forall t, G (t + t0)%nat ω = G t0 ω).
   Proof.
     intros.
     revert H10; apply almost_impl.
     revert H9; apply almost_impl.
     revert H3; apply almost_impl.
     revert H4; apply almost_impl.
     revert H5; apply almost_impl.     
     apply all_almost; intros ???????.
     specialize (H10 H11).
     destruct H10 as [t0 [? ?]].
     assert (forall t (i: nat) (pf : (i < S n)%nat), G (t + t0)%nat x0 = G t0 x0).
     {
       intros.
       generalize (lemma3_Jaakkola_beta W x0 ε G0 t0 α β x ww M G XF); intros.
       cut_to H13; try easy.
       - now specialize (H13 H9 H12 t i pf).
       - apply H.
     }
     intros.
     assert (0 < S n)%nat by lia.
     exists t0.
     intros.
     now specialize (H13 t _ H14).
   Qed.

  Theorem Tsitsiklis1 {n} (β : R) (X w α : nat -> Ts -> vector R (S n)) 
        (XF : nat -> vector R (S n) -> vector R (S n))
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa (S n)) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S n)) (X 0%nat)}
        (adapt_w : IsAdapted  (Rvector_borel_sa (S n)) w (fun k => F (S k)))
        {rvXF : forall k, RandomVariable (Rvector_borel_sa (S n)) (Rvector_borel_sa (S n)) (XF k)}
        {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
        {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A)
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (exists (D : nonnegreal),
        forall k ω, Rvector_max_abs (XF k (X k ω)) <= β * Rvector_max_abs (X k ω) + D) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    exists (D0 : Ts -> R),  forall k, almostR2 prts Rle (rvmaxabs (X k)) D0.
  Proof.
    intros.
    assert (exists γ,β < γ < 1).
    {
      exists (β + (1 - β)/2).
      lra.
    }
    destruct H5 as [D ?].
    destruct H7 as [γ ?].
    assert (exists G0,
               1 < G0 /\
               β * G0 + D <= γ * G0).
    {
      exists ((D + 1) / (γ - β)).
      split.
      - generalize (cond_nonneg D); intros.
        rewrite <- Rlt_div_r; lra.
      - field_simplify; try lra.
        unfold Rdiv.
        apply Rmult_le_compat_r; try lra.
        left.
        apply Rinv_0_lt_compat.
        lra.
    }
    destruct H8 as [G0 [? ?]].
    assert (forall k ω i pf,
               Rabs (vector_nth i pf (XF k (X k ω))) <=
               γ * Rmax (Rvector_max_abs (X k ω)) G0).
    {
      intros.
      eapply Rle_trans.
      - apply Rvector_max_abs_nth_le.
      - eapply Rle_trans.
        apply H5.
        unfold Rmax.
        match_destr.
        + apply Rle_trans with (r2 := β * G0 + D); try lra.
          apply Rplus_le_compat_r.
          apply Rmult_le_compat_l; try lra.
        + assert (Rvector_max_abs (X k ω) > G0) by lra.
          pose (G1 := Rvector_max_abs (X k ω) - G0).
          replace (Rvector_max_abs (X k ω)) with (G0 + G1).
          * assert (β * G1 <= γ * G1).
            {
              apply Rmult_le_compat_r; try lra.
              unfold G1; lra.
            }
            lra.
          * unfold G1; lra.
    }
    assert (exists ε,
               0 < ε /\
               γ * (1 + ε) = 1).
    {
      exists (1/γ - 1).
      split.
      - field_simplify; try lra.
        apply Rdiv_lt_0_compat; lra.
      - field_simplify; lra.
   }
    destruct H11 as [ε [? ?]].
    pose (M := fun t ω => Rmax_list_map (seq 0 (S t)) 
                                        (fun n0 : nat => rvmaxabs (X n0) ω)).
    pose (G := fix G t :=
                 match t with
                 | 0%nat => rvmax (M 0%nat) (const G0)
                 | S t' => rvchoice
                             (fun ω =>
                                if Rle_dec (M t ω) ((1+ε)*(G t' ω)) then true else false)
                             (G t')
                             (rvscale G0 (fun ω => powerRZ_ge_fun (1 + ε) ((M t ω)/G0)))
                 end).
    assert (forall t, rv_le (M t) (rvscale (1 + ε) (G t))).
    {
      intros ??.
      destruct t.
      - simpl.
        unfold rvscale, rvmax, const.
        apply Rle_trans with (r2 := 1 * Rmax (M 0%nat a) G0).
        + rewrite Rmult_1_l.
          apply Rmax_l.
        + apply Rmult_le_compat_r.
          * apply Rle_trans with (r2 := G0); try lra.
            apply Rmax_r.
          * lra.
      - simpl.
        unfold rvscale, rvchoice.
        match_case; intros.
        + match_destr_in H13.
        + apply Rle_trans with (r2 := (1 + ε) * (M (S t) a)).
          * rewrite <- (Rmult_1_l (M (S t) a)) at 1.
            apply Rmult_le_compat_r; try lra.
            unfold M.
            apply Rmax_list_map_seq_ge; try lia.
            exists (0%nat).
            split; try lia.
            apply rvmaxabs_pos.
          * generalize (powerRZ_ge_scale (1 + ε) (M (S t) a) G0); intros.
            cut_to H14; try lra.
            apply Rmult_le_compat_l; try lra.
    }
    assert (forall t ω,
               (G t ω < G (S t) ω) ->
               (M (S t) ω <= G (S t) ω)).
    {
      intros ???.
      simpl in H14; simpl.
      unfold rvmax, const, rvchoice, rvscale in H14.
      unfold rvmax, const, rvchoice, rvscale.
      match_destr_in H14; try lra.
      apply powerRZ_ge_scale; try lra.
   }
    assert (adaptX : IsAdapted (Rvector_borel_sa (S n)) X F).
    {
      intros ?.
      induction n0.
      - easy.
      - assert (RandomVariable (F (S n0)) (Rvector_borel_sa (S n))
                               (vecrvplus (X n0) (vecrvmult (α n0) (vecrvplus (vecrvminus (fun ω : Ts => XF n0 (X n0 ω)) (X n0)) (w n0))))).
        {
          apply Rvector_plus_rv.
          - now apply (RandomVariable_sa_sub (isfilt n0)).
          - apply Rvector_mult_rv.
            + now apply (RandomVariable_sa_sub (isfilt n0)).
            + apply Rvector_plus_rv; try easy.
              apply Rvector_minus_rv.
              * apply (compose_rv (dom2 := Rvector_borel_sa (S n))); try easy.
                now apply (RandomVariable_sa_sub (isfilt n0)).
              * now apply (RandomVariable_sa_sub (isfilt n0)).
        }
        revert H15.
        apply RandomVariable_proper; try easy.
    }

    assert (adaptM : IsAdapted borel_sa M F).
    {
      intros ?.
      unfold M.
      induction n0.
      - unfold Rmax_list_map; simpl.
        now apply Rvector_max_abs_rv.
      - unfold Rmax_list_map.
        assert (rv_eq
                   (fun ω : Ts => Max_{ seq 0 (S (S n0))}(fun n1 : nat => rvmaxabs (X n1) ω))
                   (fun ω : Ts => Rmax (Max_{ seq 0 (S n0)}(fun n1 : nat => rvmaxabs (X n1) ω))
                                       (rvmaxabs (X (S n0)) ω))).
        {
          intros ?.
          rewrite Rmax_list_Sn; try lia.
          now replace (0 + S n0)%nat with (S n0) by lia.
        }
        assert (RandomVariable (F (S n0)) borel_sa
                   (fun ω : Ts => Rmax (Max_{ seq 0 (S n0)}(fun n1 : nat => rvmaxabs (X n1) ω))
                                       (rvmaxabs (X (S n0)) ω))).
        {
          apply rvmax_rv.
          - now apply (RandomVariable_sa_sub (isfilt n0)).
          - now apply Rvector_max_abs_rv.
        }
        revert H16.
        apply RandomVariable_proper; try easy.
    }

    assert (Mnneg:forall t ω, 0 <= M t ω).
    {
      intros.
      unfold M.
      apply Rmax_list_map_seq_ge; try lia.
      exists (0%nat).
      split; try lia.
      apply rvmaxabs_pos.
    }

    assert (Gnneg:forall t ω, 0 <= G t ω).
    {
      intros.
      induction t.
      - simpl.
        unfold rvmax, const.
        apply Rle_trans with (r2 :=  G0); try lra.
        apply Rmax_r.
      - simpl.
        unfold rvchoice, rvscale.
        match_destr.
        generalize (powerRZ_ge_scale (1 + ε) (M (S t) ω) G0); intros.      
        cut_to H15; try lra.
        specialize (Mnneg (S t) ω).
        lra.
    }

    assert (Gincr: forall t, rv_le (G t) (G (S t))).
    {
      intros ??.
      simpl.
      unfold rvchoice, rvscale.
      match_case; intros; try lra.
      match_destr_in H15.
      assert (M (S t) a > (1 + ε) * G t a) by lra.
      generalize (powerRZ_ge_scale (1 + ε) (M (S t) a) G0); intros.      
      cut_to H17; try lra.
      apply Rle_trans with (r2 := (M (S t) a)); try lra.
      apply Rle_trans with (r2 := (1 + ε) * G t a); try lra.
      rewrite <- Rmult_1_l at 1.
      apply Rmult_le_compat_r; try lra.
      apply Gnneg.
    }

    assert (Gpos1:forall t ω, 1 < G t ω).
    {
      intros.
      induction t.
      - simpl.
        unfold rvmax, const.
        apply Rlt_le_trans with (r2 := G0); try lra.
        apply Rmax_r.
      - specialize (Gincr t ω).
        lra.
   }
    assert (Gpos:forall t ω, 0 < G t ω).
    {
      intros.
      specialize (Gpos1 t ω);lra.
   }
    assert (adaptG : IsAdapted borel_sa G F).
    {
      intros ?.
      induction n0.
      - simpl.
        typeclasses eauto.
      - simpl.
        assert (rvc:RandomVariable (F (S n0)) (discrete_sa bool)
                  (fun x : Ts => if Rle_dec (M (S n0) x) ((1 + ε) * G n0 x) then true else false)).
        { 
          Existing Instance FiniteRange_FiniteRangeFunction.
          apply (frf_singleton_rv _ _).
          intros [|] _; unfold pre_event_singleton, pre_event_singleton, pre_event_preimage; simpl.
          * apply sa_proper with
                (x := (fun ω => (rvminus (M (S n0)) 
                                         (rvscale (1 + ε) (G n0)) ω) <= 0)). 
            -- intros ?.
               rv_unfold'.
               match_destr.
               ++ assert (M (S n0) x - (1 + ε) * G n0 x <= 0) by lra.
                  try easy.
               ++ assert (~(M (S n0) x - (1 + ε) * G n0 x <= 0)) by lra.
                  try easy.
            -- apply sa_le_le_rv.
               apply rvminus_rv; try easy.
               apply (RandomVariable_sa_sub (isfilt n0)).
               now apply rvscale_rv.
          * apply sa_proper with
                (x := (fun ω => (rvminus (M (S n0)) 
                                         (rvscale (1 + ε) (G n0)) ω) > 0)). 
            -- intros ?.
               rv_unfold'.
               match_destr.
               ++ assert (~ (M (S n0) x - (1 + ε) * G n0 x > 0)) by lra.
                  try easy.
               ++ assert ((M (S n0) x - (1 + ε) * G n0 x > 0)) by lra.
                  try easy.
            -- apply sa_le_gt_rv.
               apply rvminus_rv; try easy.
               apply (RandomVariable_sa_sub (isfilt n0)).
               now apply rvscale_rv.
        }
        apply rvchoiceb_rv; try easy.
        + now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply rvscale_rv.
          apply (@compose_rv Ts R R (F (S n0)) borel_sa borel_sa
                             (fun ω => M (S n0) ω / G0)
                             (fun z => powerRZ_ge_fun (1 + ε) z)).
          * assert (RandomVariable (F (S n0)) borel_sa
                                   (rvscale (/ G0) (M (S n0)))).
            {
              apply rvscale_rv.
              apply adaptM.
            }
            revert H15.
            apply RandomVariable_proper; try easy.
            intros ?.
            unfold rvscale; lra.
          * apply powerRZ_ge_fun_rv.
    }
    
    pose (ww := fun t => vecrvscalerv (rvinv (G t)) (w t)).

    assert (rvww :  forall (k i : nat) (pf : (i < (S n))%nat), RandomVariable dom borel_sa (vecrvnth i pf (ww k))).
    {
      intros.
      unfold ww.
      apply vecrvnth_rv.
      apply Rvector_scale_rv_rv.
      - apply rvinv_rv.
        now apply (RandomVariable_sa_sub (filt_sub k)).
      - apply rv_vecrvnth.
        apply rvw.
   }

    assert (expw0 : forall k i pf, Expectation (vecrvnth i pf (w k)) = Some (Finite 0)).
      {
        intros.
        specialize (H2 k i pf).
        specialize (iscond k i pf).
        generalize (@is_conditional_expectation_Expectation Ts dom prts (F k) (vecrvnth i pf (w k))); intros.
        specialize (H15 _ _ _ iscond).
        assert (RandomVariable dom Rbar_borel_sa
                               (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))).
        {
          apply (RandomVariable_sa_sub (filt_sub k)).
          apply Condexp_rv.
        }
        generalize (Rbar_Expectation_almostR2_proper prts (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k))) (fun x : Ts => const 0 x) H2); intros.
        rewrite H17 in H15.
        now rewrite Rbar_Expectation_finite_const in H15.
      }
      assert (isfef : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (w k))).
      {
        intros.
        unfold IsFiniteExpectation.
        now rewrite expw0.
      }
      assert (isfefg: forall k i pf, IsFiniteExpectation prts (rvmult (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        intros.
        destruct (IsFiniteExpectation_parts prts _ (isfef k i pf)).
        assert (forall t ω, 0 < rvinv (G t) ω < 1).
        {
          intros.
          specialize (Gpos1 t ω).
          rewrite rvinv_Rinv; try lra.
          split.
          - apply Rinv_0_lt_compat; lra.
          - replace 1 with (/ 1) by lra.
            apply Rinv_lt_contravar; lra.
        }
        apply IsFiniteExpectation_from_parts.
        - apply IsFiniteExpectation_bounded with
              (rv_X1 := const 0) (rv_X3 := pos_fun_part (vecrvnth i pf (w k))); trivial.
          + apply IsFiniteExpectation_const.
          + apply positive_part_nnf.
          + assert (rv_eq  (fun x : Ts => nonneg (pos_fun_part (rvmult (vecrvnth i pf (w k)) (rvinv (G k))) x))
                           (rvmult (fun x : Ts => nonneg (pos_fun_part (vecrvnth i pf (w k)) x))
                                   (rvinv (G k)))).
            {
              intros ?.
              unfold rvmult.
              unfold pos_fun_part.
              simpl.
              rewrite Rmax_mult.
              - now rewrite Rmult_0_l.
              - specialize (H17 k a); lra.
            }
            rewrite H18.
            intros ?.
            unfold rvmult.
            rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l.
            * apply positive_part_nnf.
            * specialize (H17 k a); lra.
      - apply IsFiniteExpectation_bounded with
              (rv_X1 := const 0) (rv_X3 := neg_fun_part (vecrvnth i pf (w k))); trivial.
        + apply IsFiniteExpectation_const.
        + apply negative_part_nnf.
        + assert (rv_eq  (fun x : Ts => nonneg (neg_fun_part (rvmult (vecrvnth i pf (w k)) (rvinv (G k))) x))
                           (rvmult (fun x : Ts => nonneg (neg_fun_part (vecrvnth i pf (w k)) x))
                                   (rvinv (G k)))).
            {
              intros ?.
              unfold rvmult.
              unfold neg_fun_part.
              simpl.
              rewrite Rmax_mult.
              - rewrite Rmult_0_l.
                f_equal.
                lra.
              - specialize (H17 k a); lra.
            }
            rewrite H18.
            intros ?.
            unfold rvmult.
            rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l.
            * apply negative_part_nnf.
            * specialize (H17 k a); lra.
      }
    assert (forall k i pf,
                 almostR2 prts eq (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (ww k)))
                          (fun x : Ts => const 0 x)).
    {
      intros.
      assert (RandomVariable (F k) borel_sa (rvinv (G k))).
      {
        now apply rvinv_rv.
      }
      assert (RandomVariable dom borel_sa (rvmult (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        apply rvmult_rv.
        - apply rvw.
        - apply rvinv_rv.
          now apply (RandomVariable_sa_sub (filt_sub k)).          
      }
      generalize (Condexp_factor_out prts (filt_sub k) (vecrvnth i pf (w k)) (rvinv (G k))); intros.
      apply almost_prob_space_sa_sub_lift in H17.
      revert H17; apply almost_impl.
      specialize (H2 k i pf).
      revert H2.
      apply almost_impl, all_almost; intros ???.
      unfold ww.
      assert (rv_eq
                (vecrvnth i pf (vecrvscalerv (rvinv (G k)) (w k)))
                (rvmult  (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        intros ?.
        unfold vecrvnth, vecrvscalerv.
        unfold rvmult.
        rewrite Rvector_nth_scale.
        lra.
      }
      erewrite (ConditionalExpectation_ext _ (filt_sub k) _ _ H18).
      rewrite H17.
      unfold Rbar_rvmult.
      rewrite H2.
      unfold const.
      apply Rbar_mult_0_r.
    }

    assert (exists (K : R),
               forall k i pf,
                 almostR2 prts Rbar_le
                          (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (ww k))))
                          (const K)).
    {
      destruct H3 as [A [B [? [? ?]]]].
      assert (exists (K : R),
                 forall t ω,
                   (A + B * Rsqr (M t ω))/(Rsqr (G t ω)) <= K).
      {
        exists ((A / Rsqr G0) + B * (Rsqr (1 + ε))).
        intros.
        assert (0 < (Rsqr (G t ω))).
        {
          unfold Rsqr.
          now apply Rmult_lt_0_compat.
        }

        assert (0 < Rsqr G0).
        {
          unfold Rsqr.
          apply Rmult_lt_0_compat; lra.
        }

        assert (A / (Rsqr (G t ω)) <= A / Rsqr G0).
        {
          unfold Rdiv.
          apply Rmult_le_compat_l; try lra.
          apply Rle_Rinv; try lra.
          apply Rsqr_incr_1; try lra.
          induction t.
          - simpl.
            unfold rvmax, const.
            apply Rmax_r.
          - cut_to IHt.
            + eapply Rle_trans.
              apply IHt.
              apply Gincr.
            + unfold Rsqr.
              now apply Rmult_lt_0_compat.
          - now left.
        }
        assert (0 <> (Rsqr (G t ω))).
        {
          now apply Rlt_not_eq.
        }
        assert ((B * Rsqr (M t ω))/(Rsqr (G t ω)) <= B * Rsqr (1 + ε)).
        {
          specialize (H13 t ω).
          unfold rvscale in H13.
          apply Rmult_le_reg_r with (r := Rsqr (G t ω)); try lra.
          field_simplify; try lra.
          rewrite Rmult_assoc.
          apply Rmult_le_compat_l; try lra.
          apply Rsqr_incr_1 in H13.
          - rewrite Rsqr_mult in H13; try lra.
          - apply Mnneg.
          - apply Rle_trans with (r2 := (G t ω)).
            + now left.
            + rewrite <- Rmult_1_l at 1.
              apply Rmult_le_compat_r; try lra.
              now left.
        }
        generalize (Rplus_le_compat _ _ _ _ H20 H22); intros.
        assert (0 <> Rsqr G0).
        {
          now apply Rlt_not_eq.
        }
        field_simplify in H23; try lra.
      }
      destruct H18 as [K ?].
      exists K.
      intros.
      specialize (H15 k i pf).
      unfold ww.
      generalize (is_conditional_expectation_factor_out_nneg_both_Rbar prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k)))); intros.
      specialize (H19 (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))))).
      assert (RandomVariable dom borel_sa (rvsqr (rvinv (G k)))).
      {
        apply rvsqr_rv, rvinv_rv.
        now apply (RandomVariable_sa_sub (filt_sub k)).
      }
      generalize (NonNegCondexp_cond_exp prts (filt_sub k) (rvmult (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k))))); intros.
      assert (Rbar_NonnegativeFunction (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k)))) ).
      {
        apply Condexp_nneg.
        typeclasses eauto.
      }
      assert (RandomVariable (F k) borel_sa (rvsqr (rvinv (G k)))).
      {
        now apply rvsqr_rv, rvinv_rv.
      }
      specialize (H19 _ _ _ _ _ _ _ ).
      assert (rvgce : RandomVariable (F k) Rbar_borel_sa
                                      (Rbar_rvmult (fun x : Ts => rvsqr (rvinv (G k)) x)
                        (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k)))))).
      {
        apply Rbar_rvmult_rv.
        - apply Real_Rbar_rv.
          typeclasses eauto.
        - apply Condexp_rv.
      }
      specialize (H19 _).
      cut_to H19.
      - revert H15; apply almost_impl.
        generalize (is_conditional_expectation_nneg_unique prts (filt_sub k) _ _ _ H19 H21); intros.
        apply almost_prob_space_sa_sub_lift in H15. 
        revert H15; apply almost_impl.
        specialize (H17 k i pf).
        revert H17; apply almost_impl.
        apply all_almost; intros ????.
        erewrite Condexp_nneg_simpl.
        assert (rv_eq
                  (rvsqr (vecrvnth i pf (vecrvscalerv (rvinv (G k)) (w k))))
                  (rvmult (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k))))).
        {
          intros ?.
          rv_unfold.
          unfold vecrvscalerv, vecrvnth.
          rewrite Rvector_nth_scale.
          rewrite Rsqr_mult.
          now apply Rmult_comm.
        }
        erewrite (NonNegCondexp_ext prts (filt_sub k) _ _ H25).
        rewrite <- H17.
        assert  (rvmaxlist (fun (j : nat) (ω : Ts) => rvsqr (rvmaxabs (X j)) ω) k x <= Rsqr (M k x)).
        {
          unfold M, rvmaxlist, rvsqr.
          unfold Rmax_list_map.
          apply Rmax_list_le_iff.
          - apply map_not_nil, seq_not_nil; lia.
          - intros.
            apply in_map_iff in H26.
            destruct H26 as [? [? ?]].
            rewrite <- H26.
            apply Rsqr_le_abs_1.
            rewrite Rabs_pos_eq.
            + rewrite Rabs_pos_eq.
              apply (Rmax_spec_map (seq 0 (S k)) (fun n0 : nat => rvmaxabs (X n0) x) x1 H27).
              apply Rmax_list_ge with (x := rvmaxabs (X x1) x).
              * apply in_map_iff.
                exists x1; split; trivial.
              * apply rvmaxabs_pos.
            + apply rvmaxabs_pos.
        }
        assert (Rbar_le (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))) x)
                        (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr (M k))) x)).
        {
           eapply Rbar_le_trans.
           apply H15.
           rv_unfold.
           simpl.
           rewrite Rabs_right; try lra.
           rewrite Rabs_right; try lra.           
           apply Rplus_le_compat_l.
           apply Rmult_le_compat_l.
           - lra.
           - apply H26.
        }
        unfold Rbar_rvmult, const.
        assert (0 < rvsqr (rvinv (G k)) x).
        {
          unfold rvsqr.
          apply Rsqr_pos_lt.
          apply Rgt_not_eq.
          unfold rvinv, rvpower, const.
          apply power_pos.
          apply Gpos.
        }
        rewrite Rbar_mult_comm.
        rewrite Rbar_mult_pos_le with (z := mkposreal _ H28) in H27.
        simpl in H27.
        rewrite Rbar_mult_mult_pos in H27.
        eapply Rbar_le_trans.
        apply H27.
        rv_unfold.
        simpl.
        rewrite Rabs_right; try lra.
        rewrite Rabs_right; try lra.
        specialize (H18 k x).
        unfold Rdiv in H18.
        replace (Rsqr (rvinv (G k) x)) with (/ Rsqr (G k x)); trivial.
        assert (G k x <> 0).
        {
          apply Rgt_not_eq, Gpos.
        }
        rewrite rvinv_Rinv; trivial.
        rewrite Rsqr_inv; trivial.
      - apply Condexp_cond_exp_nneg.
        typeclasses eauto.
    }
    destruct
    (classic
       (exists D0 : Ts -> R, forall k : nat, almostR2 prts Rle (rvmaxabs (X k)) D0)); trivial.
    push_neg_in H17.
    assert (forall x : Ts -> R, exists x0 : nat, exists pt : Ts, Rgt (rvmaxabs (X x0) pt) (x pt)).
    {
      intros x.
      specialize (H17 x).
      destruct H17 as [x0 HH].
      exists x0.
      unfold almostR2,almost in HH.
      push_neg_in HH.
      specialize (HH Ω ps_one).
      destruct HH as [pt [_ HH]].
      exists pt.
      lra.
    }
    pose (WW := fix WW i pf t' t0 :=
                  match t' with
                  | 0%nat => const 0
                  | (S t) => 
                    rvplus 
                      (rvmult 
                         (rvminus (const 1) (vecrvnth i pf (α (t + t0)%nat)))
                         (WW i pf t t0))
                      (rvmult (vecrvnth i pf (α (t + t0)%nat))
                              (vecrvnth i pf (ww (t + t0)%nat)))
                  end).
    assert (forall i pf,
               almost prts (fun ω => is_lim_seq (fun k => WW i pf k 0%nat ω) 0)).
    {
      intros.

      destruct H1 as [Ca ?].
      destruct H16 as [K ?].
      
      apply lemma1_alpha_alpha with
          (α := fun k => vecrvnth i pf (α k))
          (w := fun k => vecrvnth i pf (ww k))
          (filt_sub := filt_sub) (Ca := Ca)
          (rv := fun k => rvww k i pf)
          (B := fun _ => const K); try easy.

      - simpl.
        apply rvconst.
      - unfold IsAdapted; intros.
        apply rvconst.
      - unfold IsAdapted; intros.
        unfold ww.
        apply vecrvnth_rv.
        apply Rvector_scale_rv_rv.
        + apply rvinv_rv.
          now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply adapt_w.
      - unfold IsAdapted.
        intros.
        now apply vecrvnth_rv.
      - intros.
        apply Condexp_cond_exp.
        unfold ww.
        specialize (isfefg n0 i pf).
        revert isfefg.
        apply IsFiniteExpectation_proper.
        intros ?.
        unfold vecrvnth, vecrvscalerv, rvmult, Rvector_scale.
        rewrite vector_nth_map.
        apply Rmult_comm.
      - intros.
        apply H.
      - intros.
        specialize (H n0 x i pf).
        unfold vecrvnth.
        lra.
      - apply all_almost.
        intros.
        specialize (H0 i pf x).
        now unfold vecrvnth.
      - unfold const.
        specialize (H1 i pf).
        revert H1.
        apply almost_impl, all_almost.
        intros ??.
        now unfold rvsqr, vecrvnth.
      - intros.
        simpl.
        rv_unfold.
        replace (n0 + 0)%nat with n0 by lia.
        lra.
      - exists (const K).
        apply all_almost.
        intros.
        apply Rle_abs.
    }

    assert (almost prts (fun ω =>
                          forall i pf,
                            is_lim_seq (fun k => WW i pf k 0%nat ω) 0)).
    {
      apply almost_bounded_forall.
      intros.
      - apply lt_dec.
      - intros.
        apply is_lim_seq_ext with (u := (fun k : nat => WW i pf1 k 0%nat x)); trivial.
        intros.
        now rewrite (digit_pf_irrel _ _ pf2 pf1).   
      - apply H19.
    }
    
    assert (almost prts (fun ω =>
                           is_lim_seq (fun k : nat => M k ω) p_infty ->
                           exists t0 : nat, 
                             forall t,
                               (G t0 ω = G (t + t0)%nat ω))).
    {
      generalize (lemma3_almost WW ε G0 α X ww M G XF); intros.
      cut_to H21; try easy.
      - revert H21.
        apply almost_impl, all_almost; intros ???.
        destruct (H21 H22).
        exists x0.
        intros.
        symmetry.
        apply H23.
      - intros.
        simpl.
        unfold rvchoice.
        match_case; intros.
        now match_destr_in H23.
      - intros.
        apply H13.
      - intros.
        unfold M.
        unfold Rmax_list_map.
        rewrite Rmax_list_Sn; try lia.
        now simpl.
      - intros.
        unfold M.
        apply Rle_trans with (r2 := rvmaxabs (X t) ω).
        + apply Rvector_max_abs_nth_le.
        + unfold Rmax_list_map.
          apply Rmax_spec.
          apply in_map_iff.
          exists t.
          split; trivial.
          apply in_seq.
          lia.
      - intros.
        apply H.
      - intros.
        simpl.
        rv_unfold.
        lra.
      - intros.
        rewrite H6.
        intros ?.
        unfold ww, vecrvscalerv.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale.
        do 3 f_equal.
        rewrite Rvector_scale_scale.
        specialize (Gpos k a).
        rewrite rvinv_Rinv; trivial.
        rewrite <- Rinv_r_sym; try lra.
        now rewrite Rvector_scale1.
      - intros ????.
        eapply Rle_trans.
        apply H10.
        assert (Rvector_max_abs (X k a) <= (1 + ε) * G k a).
        {
          apply Rle_trans with (r2 := M k a).
          - unfold M.
            unfold Rmax_list_map, rvmaxabs.
            apply Rmax_spec.
            apply in_map_iff.
            exists k.
            split; trivial.
            apply in_seq.
            lia.
          - apply H13.
        }
        replace (G k a) with (γ * ((1 + ε) * G k a)).
        + apply Rmult_le_compat_l; try lra.
          apply Rle_Rmax.
          split; trivial.
          apply Rle_trans with (r2 := G k a).
          * clear H22.
            induction k.
            -- simpl.
               unfold rvmax, const.
               apply Rmax_r.
            -- eapply Rle_trans.
               apply IHk.
               apply Gincr.
          * rewrite <- Rmult_1_l at 1.
            apply Rmult_le_compat_r; try lra.
            left; apply Gpos.
        + rewrite <- Rmult_assoc.
          rewrite H12.
          lra.
      - revert H20.
        apply almost_impl, all_almost; intros ???.
        generalize (lemma3_pre0 x (mkposreal _ H11) G M H22); intros.
        cut_to H23; try easy.
        + generalize (lemma3_pre1 WW x (mkposreal _ H11) α ww ); intros.
          cut_to H24; try easy.
          * destruct H24.
            specialize (H23 x0).
            destruct H23 as [? [? ?]].
            exists x1.
            split; trivial.
            intros.
            specialize (H24 i pf x1 t H23).
            apply H24.
          * intros.
            apply H.
          * intros.
            simpl.
            rv_unfold.
            lra.
        + intros.
          simpl.
          apply H13.
        + intros.
          apply Gincr.
        + intros.
          now apply H14.
    }
    assert (almost prts (fun ω =>
                           is_lim_seq (fun k : nat => M k ω) p_infty ->
                           exists D0 : R,
                             forall t,
                               M t ω <= D0)).
    {
      revert H21.
      apply almost_impl, all_almost; intros ???.
      destruct (H21 H22).
      exists ((1 + ε) * (G x0 x)).
      intros.
      destruct (le_dec t x0).
      - apply Rle_trans with (r2 := M x0 x).
        + unfold M.
          apply Rmax_seq_map_monotone.
          lia.
        + apply H13.
      - specialize (H23 (t - x0)%nat).
        replace (t - x0 + x0)%nat with t in H23 by lia.
        rewrite H23.
        apply H13.
   }
    assert (almost prts
                   (fun ω => exists D0 : R,
                        forall t,
                          M t ω <= D0)).
    {
      revert H22.
      apply almost_impl, all_almost; intros ??.
      destruct (classic (is_lim_seq (fun k : nat => M k x) p_infty)).
      - specialize (H22 H23).
        destruct H22.
        exists x0.
        intros.
        apply H22.
      - assert (ex_finite_lim_seq (fun k => M k x)).
        {
          assert (forall k, M k x <= M (S k) x).
          {
            intros.
            unfold M.
            apply Rmax_seq_map_monotone.
            lia.
          }
          generalize (ex_lim_seq_incr _ H24); intros.
          apply ex_finite_lim_seq_correct.
          split; trivial.
          case_eq (Lim_seq (fun k : nat => M k x)); intros.
          - now simpl.
          - apply Lim_seq_correct in H25.
            now rewrite H26 in H25.
          - generalize (Lim_seq_pos (fun k => M k x)); intros.
            cut_to H27.
            + now rewrite H26 in H27.
            + intros.
              apply Mnneg.
        }
        destruct H24.
        apply is_lim_seq_bounded in H24.
        destruct H24.
        exists x1.
        intros.
        specialize (H24 t).
        eapply Rle_trans.
        shelve.
        apply H24.
        Unshelve.
        apply Rle_abs.
    }
    assert (exists D0 : Ts -> R,
               forall k, almostR2 prts Rle (M k) D0).
    {
      apply exists_almost in H23.
      destruct H23 as [??].
      exists x.
      now apply forall_almost.
    }
    destruct H24.
    exists x.
    intros.
    specialize (H24 k).
    revert H24.
    apply almost_impl, all_almost; intros ??.
    unfold M in H24.
    unfold Rmax_list_map in H24.
    eapply Rle_trans.
    shelve.
    apply H24.
    Unshelve.
    apply Rmax_spec.
    apply in_map_iff.
    exists k.
    split; trivial.
    apply in_seq.
    lia.
  Qed.


  Theorem Tsitsiklis1_Jaakkola_beta {n} (β : R) (X w α beta : nat -> Ts -> vector R (S n)) 
        (XF : nat -> Ts -> vector R (S n))
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa (S n)) α F)
        (adapt_beta : IsAdapted (Rvector_borel_sa (S n)) beta F)        
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S n)) (X 0%nat)}
        (adapt_w : IsAdapted  (Rvector_borel_sa (S n)) w (fun k => F (S k)))
        {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S n)) (XF k)}
        {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
        {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf (α k ω)) ->        
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A)
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (exists (D : nonnegreal),
        almost prts (fun ω =>
                       forall k, 
                         Rvector_max_abs (XF k ω) <= β * Rvector_max_abs (X k ω) + D)) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    exists (D0 : Ts -> R),  forall k, almostR2 prts Rle (rvmaxabs (X k)) D0.
  Proof.
    intros H beta_prop alpha_beta_prop beta_inf beta_fin.
    intros.
    assert (exists γ,β < γ < 1).
    {
      exists (β + (1 - β)/2).
      lra.
    }
    destruct H5 as [D ?].
    destruct H7 as [γ ?].
    assert (exists G0,
               1 < G0 /\
               β * G0 + D <= γ * G0).
    {
      exists ((D + 1) / (γ - β)).
      split.
      - generalize (cond_nonneg D); intros.
        rewrite <- Rlt_div_r; lra.
      - field_simplify; try lra.
        unfold Rdiv.
        apply Rmult_le_compat_r; try lra.
        left.
        apply Rinv_0_lt_compat.
        lra.
    }
    destruct H8 as [G0 [? ?]].
    assert (almost prts (fun ω => forall k i pf,
               Rabs (vector_nth i pf (XF k ω)) <=
               γ * Rmax (Rvector_max_abs (X k ω)) G0)).
    {
      revert H5; apply almost_impl.
      apply all_almost; intros ω?.
      intros.
      eapply Rle_trans.
      - apply Rvector_max_abs_nth_le.
      - eapply Rle_trans.
        apply H5.
        unfold Rmax.
        match_destr.
        + apply Rle_trans with (r2 := β * G0 + D); try lra.
          apply Rplus_le_compat_r.
          apply Rmult_le_compat_l; try lra.
        + assert (Rvector_max_abs (X k ω) > G0) by lra.
          pose (G1 := Rvector_max_abs (X k ω) - G0).
          replace (Rvector_max_abs (X k ω)) with (G0 + G1).
          * assert (β * G1 <= γ * G1).
            {
              apply Rmult_le_compat_r; try lra.
              unfold G1; lra.
            }
            lra.
          * unfold G1; lra.
    }
    assert (exists ε,
               0 < ε /\
               γ * (1 + ε) = 1).
    {
      exists (1/γ - 1).
      split.
      - field_simplify; try lra.
        apply Rdiv_lt_0_compat; lra.
      - field_simplify; lra.
   }
    destruct H11 as [ε [? ?]].
    pose (M := fun t ω => Rmax_list_map (seq 0 (S t)) 
                                        (fun n0 : nat => rvmaxabs (X n0) ω)).
    pose (G := fix G t :=
                 match t with
                 | 0%nat => rvmax (M 0%nat) (const G0)
                 | S t' => rvchoice
                             (fun ω =>
                                if Rle_dec (M t ω) ((1+ε)*(G t' ω)) then true else false)
                             (G t')
                             (rvscale G0 (fun ω => powerRZ_ge_fun (1 + ε) ((M t ω)/G0)))
                 end).
    assert (forall t, rv_le (M t) (rvscale (1 + ε) (G t))).
    {
      intros ??.
      destruct t.
      - simpl.
        unfold rvscale, rvmax, const.
        apply Rle_trans with (r2 := 1 * Rmax (M 0%nat a) G0).
        + rewrite Rmult_1_l.
          apply Rmax_l.
        + apply Rmult_le_compat_r.
          * apply Rle_trans with (r2 := G0); try lra.
            apply Rmax_r.
          * lra.
      - simpl.
        unfold rvscale, rvchoice.
        match_case; intros.
        + match_destr_in H13.
        + apply Rle_trans with (r2 := (1 + ε) * (M (S t) a)).
          * rewrite <- (Rmult_1_l (M (S t) a)) at 1.
            apply Rmult_le_compat_r; try lra.
            unfold M.
            apply Rmax_list_map_seq_ge; try lia.
            exists (0%nat).
            split; try lia.
            apply rvmaxabs_pos.
          * generalize (powerRZ_ge_scale (1 + ε) (M (S t) a) G0); intros.
            cut_to H14; try lra.
            apply Rmult_le_compat_l; try lra.
    }
    assert (forall t ω,
               (G t ω < G (S t) ω) ->
               (M (S t) ω <= G (S t) ω)).
    {
      intros ???.
      simpl in H14; simpl.
      unfold rvmax, const, rvchoice, rvscale in H14.
      unfold rvmax, const, rvchoice, rvscale.
      match_destr_in H14; try lra.
      apply powerRZ_ge_scale; try lra.
   }
    assert (adaptX : IsAdapted (Rvector_borel_sa (S n)) X F).
    {
      intros ?.
      induction n0.
      - easy.
      - rewrite H6.
        apply Rvector_plus_rv.
        + apply Rvector_minus_rv.
          * now apply (RandomVariable_sa_sub (isfilt n0)).
          * apply Rvector_mult_rv.
            -- now apply (RandomVariable_sa_sub (isfilt n0)).
            -- now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply Rvector_mult_rv.
          * now apply (RandomVariable_sa_sub (isfilt n0)).
          * apply Rvector_plus_rv; try easy.
    }            
    assert (adaptM : IsAdapted borel_sa M F).
    {
      intros ?.
      unfold M.
      induction n0.
      - unfold Rmax_list_map; simpl.
        now apply Rvector_max_abs_rv.
      - unfold Rmax_list_map.
        assert (rv_eq
                   (fun ω : Ts => Max_{ seq 0 (S (S n0))}(fun n1 : nat => rvmaxabs (X n1) ω))
                   (fun ω : Ts => Rmax (Max_{ seq 0 (S n0)}(fun n1 : nat => rvmaxabs (X n1) ω))
                                       (rvmaxabs (X (S n0)) ω))).
        {
          intros ?.
          rewrite Rmax_list_Sn; try lia.
          now replace (0 + S n0)%nat with (S n0) by lia.
        }
        assert (RandomVariable (F (S n0)) borel_sa
                   (fun ω : Ts => Rmax (Max_{ seq 0 (S n0)}(fun n1 : nat => rvmaxabs (X n1) ω))
                                       (rvmaxabs (X (S n0)) ω))).
        {
          apply rvmax_rv.
          - now apply (RandomVariable_sa_sub (isfilt n0)).
          - now apply Rvector_max_abs_rv.
        }
        revert H16.
        apply RandomVariable_proper; try easy.
    }

    assert (Mnneg:forall t ω, 0 <= M t ω).
    {
      intros.
      unfold M.
      apply Rmax_list_map_seq_ge; try lia.
      exists (0%nat).
      split; try lia.
      apply rvmaxabs_pos.
    }

    assert (Gnneg:forall t ω, 0 <= G t ω).
    {
      intros.
      induction t.
      - simpl.
        unfold rvmax, const.
        apply Rle_trans with (r2 :=  G0); try lra.
        apply Rmax_r.
      - simpl.
        unfold rvchoice, rvscale.
        match_destr.
        generalize (powerRZ_ge_scale (1 + ε) (M (S t) ω) G0); intros.      
        cut_to H15; try lra.
        specialize (Mnneg (S t) ω).
        lra.
    }

    assert (Gincr: forall t, rv_le (G t) (G (S t))).
    {
      intros ??.
      simpl.
      unfold rvchoice, rvscale.
      match_case; intros; try lra.
      match_destr_in H15.
      assert (M (S t) a > (1 + ε) * G t a) by lra.
      generalize (powerRZ_ge_scale (1 + ε) (M (S t) a) G0); intros.      
      cut_to H17; try lra.
      apply Rle_trans with (r2 := (M (S t) a)); try lra.
      apply Rle_trans with (r2 := (1 + ε) * G t a); try lra.
      rewrite <- Rmult_1_l at 1.
      apply Rmult_le_compat_r; try lra.
      apply Gnneg.
    }

    assert (Gpos1:forall t ω, 1 < G t ω).
    {
      intros.
      induction t.
      - simpl.
        unfold rvmax, const.
        apply Rlt_le_trans with (r2 := G0); try lra.
        apply Rmax_r.
      - specialize (Gincr t ω).
        lra.
   }
    assert (Gpos:forall t ω, 0 < G t ω).
    {
      intros.
      specialize (Gpos1 t ω);lra.
   }
    assert (adaptG : IsAdapted borel_sa G F).
    {
      intros ?.
      induction n0.
      - simpl.
        typeclasses eauto.
      - simpl.
        assert (rvc:RandomVariable (F (S n0)) (discrete_sa bool)
                  (fun x : Ts => if Rle_dec (M (S n0) x) ((1 + ε) * G n0 x) then true else false)).
        { 
          Existing Instance FiniteRange_FiniteRangeFunction.
          apply (frf_singleton_rv _ _).
          intros [|] _; unfold pre_event_singleton, pre_event_singleton, pre_event_preimage; simpl.
          * apply sa_proper with
                (x := (fun ω => (rvminus (M (S n0)) 
                                         (rvscale (1 + ε) (G n0)) ω) <= 0)). 
            -- intros ?.
               rv_unfold'.
               match_destr.
               ++ assert (M (S n0) x - (1 + ε) * G n0 x <= 0) by lra.
                  try easy.
               ++ assert (~(M (S n0) x - (1 + ε) * G n0 x <= 0)) by lra.
                  try easy.
            -- apply sa_le_le_rv.
               apply rvminus_rv; try easy.
               apply (RandomVariable_sa_sub (isfilt n0)).
               now apply rvscale_rv.
          * apply sa_proper with
                (x := (fun ω => (rvminus (M (S n0)) 
                                         (rvscale (1 + ε) (G n0)) ω) > 0)). 
            -- intros ?.
               rv_unfold'.
               match_destr.
               ++ assert (~ (M (S n0) x - (1 + ε) * G n0 x > 0)) by lra.
                  try easy.
               ++ assert ((M (S n0) x - (1 + ε) * G n0 x > 0)) by lra.
                  try easy.
            -- apply sa_le_gt_rv.
               apply rvminus_rv; try easy.
               apply (RandomVariable_sa_sub (isfilt n0)).
               now apply rvscale_rv.
        }
        apply rvchoiceb_rv; try easy.
        + now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply rvscale_rv.
          apply (@compose_rv Ts R R (F (S n0)) borel_sa borel_sa
                             (fun ω => M (S n0) ω / G0)
                             (fun z => powerRZ_ge_fun (1 + ε) z)).
          * assert (RandomVariable (F (S n0)) borel_sa
                                   (rvscale (/ G0) (M (S n0)))).
            {
              apply rvscale_rv.
              apply adaptM.
            }
            revert H15.
            apply RandomVariable_proper; try easy.
            intros ?.
            unfold rvscale; lra.
          * apply powerRZ_ge_fun_rv.
    }
    
    pose (ww := fun t => vecrvscalerv (rvinv (G t)) (w t)).

    assert (rvww :  forall (k i : nat) (pf : (i < (S n))%nat), RandomVariable dom borel_sa (vecrvnth i pf (ww k))).
    {
      intros.
      unfold ww.
      apply vecrvnth_rv.
      apply Rvector_scale_rv_rv.
      - apply rvinv_rv.
        now apply (RandomVariable_sa_sub (filt_sub k)).
      - apply rv_vecrvnth.
        apply rvw.
   }

    assert (expw0 : forall k i pf, Expectation (vecrvnth i pf (w k)) = Some (Finite 0)).
      {
        intros.
        specialize (H2 k i pf).
        specialize (iscond k i pf).
        generalize (@is_conditional_expectation_Expectation Ts dom prts (F k) (vecrvnth i pf (w k))); intros.
        specialize (H15 _ _ _ iscond).
        assert (RandomVariable dom Rbar_borel_sa
                               (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))).
        {
          apply (RandomVariable_sa_sub (filt_sub k)).
          apply Condexp_rv.
        }
        generalize (Rbar_Expectation_almostR2_proper prts (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k))) (fun x : Ts => const 0 x) H2); intros.
        rewrite H17 in H15.
        now rewrite Rbar_Expectation_finite_const in H15.
      }
      assert (isfef : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (w k))).
      {
        intros.
        unfold IsFiniteExpectation.
        now rewrite expw0.
      }
      assert (isfefg: forall k i pf, IsFiniteExpectation prts (rvmult (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        intros.
        destruct (IsFiniteExpectation_parts prts _ (isfef k i pf)).
        assert (forall t ω, 0 < rvinv (G t) ω < 1).
        {
          intros.
          specialize (Gpos1 t ω).
          rewrite rvinv_Rinv; try lra.
          split.
          - apply Rinv_0_lt_compat; lra.
          - replace 1 with (/ 1) by lra.
            apply Rinv_lt_contravar; lra.
        }
        apply IsFiniteExpectation_from_parts.
        - apply IsFiniteExpectation_bounded with
              (rv_X1 := const 0) (rv_X3 := pos_fun_part (vecrvnth i pf (w k))); trivial.
          + apply IsFiniteExpectation_const.
          + apply positive_part_nnf.
          + assert (rv_eq  (fun x : Ts => nonneg (pos_fun_part (rvmult (vecrvnth i pf (w k)) (rvinv (G k))) x))
                           (rvmult (fun x : Ts => nonneg (pos_fun_part (vecrvnth i pf (w k)) x))
                                   (rvinv (G k)))).
            {
              intros ?.
              unfold rvmult.
              unfold pos_fun_part.
              simpl.
              rewrite Rmax_mult.
              - now rewrite Rmult_0_l.
              - specialize (H17 k a); lra.
            }
            rewrite H18.
            intros ?.
            unfold rvmult.
            rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l.
            * apply positive_part_nnf.
            * specialize (H17 k a); lra.
      - apply IsFiniteExpectation_bounded with
              (rv_X1 := const 0) (rv_X3 := neg_fun_part (vecrvnth i pf (w k))); trivial.
        + apply IsFiniteExpectation_const.
        + apply negative_part_nnf.
        + assert (rv_eq  (fun x : Ts => nonneg (neg_fun_part (rvmult (vecrvnth i pf (w k)) (rvinv (G k))) x))
                           (rvmult (fun x : Ts => nonneg (neg_fun_part (vecrvnth i pf (w k)) x))
                                   (rvinv (G k)))).
            {
              intros ?.
              unfold rvmult.
              unfold neg_fun_part.
              simpl.
              rewrite Rmax_mult.
              - rewrite Rmult_0_l.
                f_equal.
                lra.
              - specialize (H17 k a); lra.
            }
            rewrite H18.
            intros ?.
            unfold rvmult.
            rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l.
            * apply negative_part_nnf.
            * specialize (H17 k a); lra.
      }
    assert (forall k i pf,
                 almostR2 prts eq (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (ww k)))
                          (fun x : Ts => const 0 x)).
    {
      intros.
      assert (RandomVariable (F k) borel_sa (rvinv (G k))).
      {
        now apply rvinv_rv.
      }
      assert (RandomVariable dom borel_sa (rvmult (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        apply rvmult_rv.
        - apply rvw.
        - apply rvinv_rv.
          now apply (RandomVariable_sa_sub (filt_sub k)).          
      }
      generalize (Condexp_factor_out prts (filt_sub k) (vecrvnth i pf (w k)) (rvinv (G k))); intros.
      apply almost_prob_space_sa_sub_lift in H17.
      revert H17; apply almost_impl.
      specialize (H2 k i pf).
      revert H2.
      apply almost_impl, all_almost; intros ???.
      unfold ww.
      assert (rv_eq
                (vecrvnth i pf (vecrvscalerv (rvinv (G k)) (w k)))
                (rvmult  (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        intros ?.
        unfold vecrvnth, vecrvscalerv.
        unfold rvmult.
        rewrite Rvector_nth_scale.
        lra.
      }
      erewrite (ConditionalExpectation_ext _ (filt_sub k) _ _ H18).
      rewrite H17.
      unfold Rbar_rvmult.
      rewrite H2.
      unfold const.
      apply Rbar_mult_0_r.
    }

    assert (exists (K : R),
               forall k i pf,
                 almostR2 prts Rbar_le
                          (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (ww k))))
                          (const K)).
    {
      destruct H3 as [A [B [? [? ?]]]].
      assert (exists (K : R),
                 forall t ω,
                   (A + B * Rsqr (M t ω))/(Rsqr (G t ω)) <= K).
      {
        exists ((A / Rsqr G0) + B * (Rsqr (1 + ε))).
        intros.
        assert (0 < (Rsqr (G t ω))).
        {
          unfold Rsqr.
          now apply Rmult_lt_0_compat.
        }

        assert (0 < Rsqr G0).
        {
          unfold Rsqr.
          apply Rmult_lt_0_compat; lra.
        }

        assert (A / (Rsqr (G t ω)) <= A / Rsqr G0).
        {
          unfold Rdiv.
          apply Rmult_le_compat_l; try lra.
          apply Rle_Rinv; try lra.
          apply Rsqr_incr_1; try lra.
          induction t.
          - simpl.
            unfold rvmax, const.
            apply Rmax_r.
          - cut_to IHt.
            + eapply Rle_trans.
              apply IHt.
              apply Gincr.
            + unfold Rsqr.
              now apply Rmult_lt_0_compat.
          - now left.
        }
        assert (0 <> (Rsqr (G t ω))).
        {
          now apply Rlt_not_eq.
        }
        assert ((B * Rsqr (M t ω))/(Rsqr (G t ω)) <= B * Rsqr (1 + ε)).
        {
          specialize (H13 t ω).
          unfold rvscale in H13.
          apply Rmult_le_reg_r with (r := Rsqr (G t ω)); try lra.
          field_simplify; try lra.
          rewrite Rmult_assoc.
          apply Rmult_le_compat_l; try lra.
          apply Rsqr_incr_1 in H13.
          - rewrite Rsqr_mult in H13; try lra.
          - apply Mnneg.
          - apply Rle_trans with (r2 := (G t ω)).
            + now left.
            + rewrite <- Rmult_1_l at 1.
              apply Rmult_le_compat_r; try lra.
              now left.
        }
        generalize (Rplus_le_compat _ _ _ _ H20 H22); intros.
        assert (0 <> Rsqr G0).
        {
          now apply Rlt_not_eq.
        }
        field_simplify in H23; try lra.
      }
      destruct H18 as [K ?].
      exists K.
      intros.
      specialize (H15 k i pf).
      unfold ww.
      generalize (is_conditional_expectation_factor_out_nneg_both_Rbar prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k)))); intros.
      specialize (H19 (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))))).
      assert (RandomVariable dom borel_sa (rvsqr (rvinv (G k)))).
      {
        apply rvsqr_rv, rvinv_rv.
        now apply (RandomVariable_sa_sub (filt_sub k)).
      }
      generalize (NonNegCondexp_cond_exp prts (filt_sub k) (rvmult (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k))))); intros.
      assert (Rbar_NonnegativeFunction (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k)))) ).
      {
        apply Condexp_nneg.
        typeclasses eauto.
      }
      assert (RandomVariable (F k) borel_sa (rvsqr (rvinv (G k)))).
      {
        now apply rvsqr_rv, rvinv_rv.
      }
      specialize (H19 _ _ _ _ _ _ _ ).
      assert (rvgce : RandomVariable (F k) Rbar_borel_sa
                                      (Rbar_rvmult (fun x : Ts => rvsqr (rvinv (G k)) x)
                        (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k)))))).
      {
        apply Rbar_rvmult_rv.
        - apply Real_Rbar_rv.
          typeclasses eauto.
        - apply Condexp_rv.
      }
      specialize (H19 _).
      cut_to H19.
      - revert H15; apply almost_impl.
        generalize (is_conditional_expectation_nneg_unique prts (filt_sub k) _ _ _ H19 H21); intros.
        apply almost_prob_space_sa_sub_lift in H15. 
        revert H15; apply almost_impl.
        specialize (H17 k i pf).
        revert H17; apply almost_impl.
        apply all_almost; intros ????.
        erewrite Condexp_nneg_simpl.
        assert (rv_eq
                  (rvsqr (vecrvnth i pf (vecrvscalerv (rvinv (G k)) (w k))))
                  (rvmult (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k))))).
        {
          intros ?.
          rv_unfold.
          unfold vecrvscalerv, vecrvnth.
          rewrite Rvector_nth_scale.
          rewrite Rsqr_mult.
          now apply Rmult_comm.
        }
        erewrite (NonNegCondexp_ext prts (filt_sub k) _ _ H25).
        rewrite <- H17.
        assert  (rvmaxlist (fun (j : nat) (ω : Ts) => rvsqr (rvmaxabs (X j)) ω) k x <= Rsqr (M k x)).
        {
          unfold M, rvmaxlist, rvsqr.
          unfold Rmax_list_map.
          apply Rmax_list_le_iff.
          - apply map_not_nil, seq_not_nil; lia.
          - intros.
            apply in_map_iff in H26.
            destruct H26 as [? [? ?]].
            rewrite <- H26.
            apply Rsqr_le_abs_1.
            rewrite Rabs_pos_eq.
            + rewrite Rabs_pos_eq.
              apply (Rmax_spec_map (seq 0 (S k)) (fun n0 : nat => rvmaxabs (X n0) x) x1 H27).
              apply Rmax_list_ge with (x := rvmaxabs (X x1) x).
              * apply in_map_iff.
                exists x1; split; trivial.
              * apply rvmaxabs_pos.
            + apply rvmaxabs_pos.
        }
        assert (Rbar_le (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))) x)
                        (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr (M k))) x)).
        {
           eapply Rbar_le_trans.
           apply H15.
           rv_unfold.
           simpl.
           rewrite Rabs_right; try lra.
           rewrite Rabs_right; try lra.           
           apply Rplus_le_compat_l.
           apply Rmult_le_compat_l.
           - lra.
           - apply H26.
        }
        unfold Rbar_rvmult, const.
        assert (0 < rvsqr (rvinv (G k)) x).
        {
          unfold rvsqr.
          apply Rsqr_pos_lt.
          apply Rgt_not_eq.
          unfold rvinv, rvpower, const.
          apply power_pos.
          apply Gpos.
        }
        rewrite Rbar_mult_comm.
        rewrite Rbar_mult_pos_le with (z := mkposreal _ H28) in H27.
        simpl in H27.
        rewrite Rbar_mult_mult_pos in H27.
        eapply Rbar_le_trans.
        apply H27.
        rv_unfold.
        simpl.
        rewrite Rabs_right; try lra.
        rewrite Rabs_right; try lra.
        specialize (H18 k x).
        unfold Rdiv in H18.
        replace (Rsqr (rvinv (G k) x)) with (/ Rsqr (G k x)); trivial.
        assert (G k x <> 0).
        {
          apply Rgt_not_eq, Gpos.
        }
        rewrite rvinv_Rinv; trivial.
        rewrite Rsqr_inv; trivial.
      - apply Condexp_cond_exp_nneg.
        typeclasses eauto.
    }
    destruct
    (classic
       (exists D0 : Ts -> R, forall k : nat, almostR2 prts Rle (rvmaxabs (X k)) D0)); trivial.
    push_neg_in H17.
    assert (forall x : Ts -> R, exists x0 : nat, exists pt : Ts, Rgt (rvmaxabs (X x0) pt) (x pt)).
    {
      intros x.
      specialize (H17 x).
      destruct H17 as [x0 HH].
      exists x0.
      unfold almostR2,almost in HH.
      push_neg_in HH.
      specialize (HH Ω ps_one).
      destruct HH as [pt [_ HH]].
      exists pt.
      lra.
    }
    pose (WW := fix WW i pf t' t0 :=
                  match t' with
                  | 0%nat => const 0
                  | (S t) => 
                    rvplus 
                      (rvmult 
                         (rvminus (const 1) (vecrvnth i pf (α (t + t0)%nat)))
                         (WW i pf t t0))
                      (rvmult (vecrvnth i pf (beta (t + t0)%nat))
                              (vecrvnth i pf (ww (t + t0)%nat)))
                  end).
    assert (forall i pf,
               almost prts (fun ω => is_lim_seq (fun k => WW i pf k 0%nat ω) 0)).
    {
      intros.
      destruct H1 as [Ca ?].
      destruct beta_fin as [Cb ?].
      destruct H16 as [K ?].
      
      apply lemma1_alpha_beta with
          (α := fun k => vecrvnth i pf (α k))
          (β := fun k => vecrvnth i pf (beta k))
          (w := fun k => vecrvnth i pf (ww k))
          (filt_sub := filt_sub) (Cb := Cb)
          (rv := fun k => rvww k i pf)
          (B := fun _ => const K); try easy.

      - simpl.
        apply rvconst.
      - unfold IsAdapted; intros.
        apply rvconst.
      - unfold IsAdapted; intros.
        unfold ww.
        apply vecrvnth_rv.
        apply Rvector_scale_rv_rv.
        + apply rvinv_rv.
          now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply adapt_w.
      - unfold IsAdapted.
        intros.
        now apply vecrvnth_rv.
      - unfold IsAdapted.
        intros.
        now apply vecrvnth_rv.
      - intros.
        apply Condexp_cond_exp.
        unfold ww.
        specialize (isfefg n0 i pf).
        revert isfefg.
        apply IsFiniteExpectation_proper.
        intros ?.
        unfold vecrvnth, vecrvscalerv, rvmult, Rvector_scale.
        rewrite vector_nth_map.
        apply Rmult_comm.
      - intros.
        revert H.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H.
      - intros.
        revert beta_prop.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H20.
      - intros.
        revert H.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H.
      - intros.
        revert beta_prop.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H20.
      - revert H0; apply almost_impl.
        apply all_almost; intros ??.
        specialize (H0 i pf).
        now unfold vecrvnth.
      - revert beta_inf; apply almost_impl.
        apply all_almost; intros ??.
        apply H20.
      - unfold const.
        specialize (H19 i pf).
        revert H19.
        apply almost_impl, all_almost.
        intros ??.
        now unfold rvsqr, vecrvnth.
      - intros.
        simpl.
        rv_unfold.
        replace (n0 + 0)%nat with n0 by lia.
        lra.
      - exists (const K).
        apply all_almost.
        intros.
        apply Rle_abs.
    }

    assert (almost prts (fun ω =>
                          forall i pf,
                            is_lim_seq (fun k => WW i pf k 0%nat ω) 0)).
    {
      apply almost_bounded_forall.
      intros.
      - apply lt_dec.
      - intros.
        apply is_lim_seq_ext with (u := (fun k : nat => WW i pf1 k 0%nat x)); trivial.
        intros.
        now rewrite (digit_pf_irrel _ _ pf2 pf1).   
      - apply H19.
    }
    
    assert (almost prts (fun ω =>
                           is_lim_seq (fun k : nat => M k ω) p_infty ->
                           exists t0 : nat, 
                             forall t,
                               (G t0 ω = G (t + t0)%nat ω))).
    {
      generalize (lemma3_almost_Jaakkola_beta WW ε G0 α beta X ww M G XF); intros.
      cut_to H21; try easy.
      - assert (almost prts (fun ω : Ts => is_lim_seq (fun k : nat => M k ω) p_infty -> exists t0 : nat, M t0 ω <= G t0 ω /\ (forall (t i : nat) (pf : (i < S n)%nat), Rabs (WW i pf t t0 ω) <= ε))).
        {
          revert H; apply almost_impl.
          revert beta_prop; apply almost_impl.
          revert H20; apply almost_impl, all_almost; intros ?????.
          generalize (lemma3_pre0 x (mkposreal _ H11) G M H23); intros.
          cut_to H24; try easy.
          - generalize (lemma3_pre1_beta WW x (mkposreal _ H11) α beta ww ); intros.
            cut_to H25; try easy.
            + destruct H25.
              specialize (H24 x0).
              destruct H24 as [? [? ?]].
              exists x1.
              split; trivial.
              intros.
              specialize (H25 i pf x1 t H24).
              apply H25.
            + intros.
              apply H22.
            + intros.
              apply H20.
            + intros.
              simpl.
              rv_unfold.
              lra.
        - intros.
          simpl.
          apply H13.
        - intros.
          apply Gincr.
        - intros.
          now apply H14.
        }
        specialize (H21 H22).
        revert H21.
        apply almost_impl, all_almost; intros ???.
        destruct (H21 H23).
        exists x0.
        intros.
        symmetry.
        apply H24.
      - intros.
        simpl.
        unfold rvchoice.
        match_case; intros.
        now match_destr_in H23.
      - intros.
        apply H13.
      - intros.
        unfold M.
        unfold Rmax_list_map.
        rewrite Rmax_list_Sn; try lia.
        now simpl.
      - intros.
        unfold M.
        apply Rle_trans with (r2 := rvmaxabs (X t) ω).
        + apply Rvector_max_abs_nth_le.
        + unfold Rmax_list_map.
          apply Rmax_spec.
          apply in_map_iff.
          exists t.
          split; trivial.
          apply in_seq.
          lia.
      - intros.
        simpl.
        rv_unfold.
        lra.
      - intros.
        rewrite H6.
        intros ?.
        unfold ww, vecrvscalerv.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale.
        do 3 f_equal.
        rewrite Rvector_scale_scale.
        specialize (Gpos k a).
        rewrite rvinv_Rinv; trivial.
        rewrite <- Rinv_r_sym; try lra.
        now rewrite Rvector_scale1.
      - revert H10; apply almost_impl.
        apply all_almost; intros a?.
        intros.
        eapply Rle_trans.
        apply H10.
        assert (Rvector_max_abs (X k a) <= (1 + ε) * G k a).
        {
          apply Rle_trans with (r2 := M k a).
          - unfold M.
            unfold Rmax_list_map, rvmaxabs.
            apply Rmax_spec.
            apply in_map_iff.
            exists k.
            split; trivial.
            apply in_seq.
            lia.
          - apply H13.
        }
        replace (G k a) with (γ * ((1 + ε) * G k a)).
        + apply Rmult_le_compat_l; try lra.
          apply Rle_Rmax.
          split; trivial.
          apply Rle_trans with (r2 := G k a).
          * clear H22.
            induction k.
            -- simpl.
               unfold rvmax, const.
               apply Rmax_r.
            -- eapply Rle_trans.
               apply IHk.
               apply Gincr.
          * rewrite <- Rmult_1_l at 1.
            apply Rmult_le_compat_r; try lra.
            left; apply Gpos.
        + rewrite <- Rmult_assoc.
          rewrite H12.
          lra.
    }
    assert (almost prts (fun ω =>
                           is_lim_seq (fun k : nat => M k ω) p_infty ->
                           exists D0 : R,
                             forall t,
                               M t ω <= D0)).
    {
      revert H21.
      apply almost_impl, all_almost; intros ???.
      destruct (H21 H22).
      exists ((1 + ε) * (G x0 x)).
      intros.
      destruct (le_dec t x0).
      - apply Rle_trans with (r2 := M x0 x).
        + unfold M.
          apply Rmax_seq_map_monotone.
          lia.
        + apply H13.
      - specialize (H23 (t - x0)%nat).
        replace (t - x0 + x0)%nat with t in H23 by lia.
        rewrite H23.
        apply H13.
   }
    assert (almost prts
                   (fun ω => exists D0 : R,
                        forall t,
                          M t ω <= D0)).
    {
      revert H22.
      apply almost_impl, all_almost; intros ??.
      destruct (classic (is_lim_seq (fun k : nat => M k x) p_infty)).
      - specialize (H22 H23).
        destruct H22.
        exists x0.
        intros.
        apply H22.
      - assert (ex_finite_lim_seq (fun k => M k x)).
        {
          assert (forall k, M k x <= M (S k) x).
          {
            intros.
            unfold M.
            apply Rmax_seq_map_monotone.
            lia.
          }
          generalize (ex_lim_seq_incr _ H24); intros.
          apply ex_finite_lim_seq_correct.
          split; trivial.
          case_eq (Lim_seq (fun k : nat => M k x)); intros.
          - now simpl.
          - apply Lim_seq_correct in H25.
            now rewrite H26 in H25.
          - generalize (Lim_seq_pos (fun k => M k x)); intros.
            cut_to H27.
            + now rewrite H26 in H27.
            + intros.
              apply Mnneg.
        }
        destruct H24.
        apply is_lim_seq_bounded in H24.
        destruct H24.
        exists x1.
        intros.
        specialize (H24 t).
        eapply Rle_trans.
        shelve.
        apply H24.
        Unshelve.
        apply Rle_abs.
    }
    assert (exists D0 : Ts -> R,
               forall k, almostR2 prts Rle (M k) D0).
    {
      apply exists_almost in H23.
      destruct H23 as [??].
      exists x.
      now apply forall_almost.
    }
    destruct H24.
    exists x.
    intros.
    specialize (H24 k).
    revert H24.
    apply almost_impl, all_almost; intros ??.
    unfold M in H24.
    unfold Rmax_list_map in H24.
    eapply Rle_trans.
    shelve.
    apply H24.
    Unshelve.
    apply Rmax_spec.
    apply in_map_iff.
    exists k.
    split; trivial.
    apply in_seq.
    lia.
 Qed.

  Theorem Tsitsiklis1_Jaakkola_beta_uniform {n} (β : R) (X w α beta : nat -> Ts -> vector R (S n)) 
        (XF : nat -> Ts -> vector R (S n))
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa (S n)) α F)
        (adapt_beta : IsAdapted (Rvector_borel_sa (S n)) beta F)        
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S n)) (X 0%nat)}
        (adapt_w : IsAdapted  (Rvector_borel_sa (S n)) w (fun k => F (S k)))
        {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S n)) (XF k)}
        {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
        {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf (α k ω)) ->        
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (beta n ω))))) ->
    (exists epsilon : posreal,
        eventually (fun n => forall i pf,
                        almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (vecrvnth i pf (beta (nn+n)%nat)) ω))) (const epsilon))) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (α n ω))))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A)
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (exists (D : nonnegreal),
        almost prts (fun ω =>
                       forall k, 
                         Rvector_max_abs (XF k ω) <= β * Rvector_max_abs (X k ω) + D)) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    
    exists (D0 : Ts -> R),  forall k, almostR2 prts Rle (rvmaxabs (X k)) D0.
  Proof.
    intros H beta_prop alpha_beta_prop beta_inf beta_fin beta_eps.
    intros.
    assert (exists γ,β < γ < 1).
    {
      exists (β + (1 - β)/2).
      lra.
    }
    destruct H5 as [D ?].
    destruct H7 as [γ ?].
    assert (exists G0,
               1 < G0 /\
               β * G0 + D <= γ * G0).
    {
      exists ((D + 1) / (γ - β)).
      split.
      - generalize (cond_nonneg D); intros.
        rewrite <- Rlt_div_r; lra.
      - field_simplify; try lra.
        unfold Rdiv.
        apply Rmult_le_compat_r; try lra.
        left.
        apply Rinv_0_lt_compat.
        lra.
    }
    destruct H8 as [G0 [? ?]].
    assert (almost prts (fun ω => forall k i pf,
               Rabs (vector_nth i pf (XF k ω)) <=
               γ * Rmax (Rvector_max_abs (X k ω)) G0)).
    {
      revert H5; apply almost_impl.
      apply all_almost; intros ω?.
      intros.
      eapply Rle_trans.
      - apply Rvector_max_abs_nth_le.
      - eapply Rle_trans.
        apply H5.
        unfold Rmax.
        match_destr.
        + apply Rle_trans with (r2 := β * G0 + D); try lra.
          apply Rplus_le_compat_r.
          apply Rmult_le_compat_l; try lra.
        + assert (Rvector_max_abs (X k ω) > G0) by lra.
          pose (G1 := Rvector_max_abs (X k ω) - G0).
          replace (Rvector_max_abs (X k ω)) with (G0 + G1).
          * assert (β * G1 <= γ * G1).
            {
              apply Rmult_le_compat_r; try lra.
              unfold G1; lra.
            }
            lra.
          * unfold G1; lra.
    }
    assert (exists ε,
               0 < ε /\
               γ * (1 + ε) = 1).
    {
      exists (1/γ - 1).
      split.
      - field_simplify; try lra.
        apply Rdiv_lt_0_compat; lra.
      - field_simplify; lra.
   }
    destruct H11 as [ε [? ?]].
    pose (M := fun t ω => Rmax_list_map (seq 0 (S t)) 
                                        (fun n0 : nat => rvmaxabs (X n0) ω)).
    pose (G := fix G t :=
                 match t with
                 | 0%nat => rvmax (M 0%nat) (const G0)
                 | S t' => rvchoice
                             (fun ω =>
                                if Rle_dec (M t ω) ((1+ε)*(G t' ω)) then true else false)
                             (G t')
                             (rvscale G0 (fun ω => powerRZ_ge_fun (1 + ε) ((M t ω)/G0)))
                 end).
    assert (forall t, rv_le (M t) (rvscale (1 + ε) (G t))).
    {
      intros ??.
      destruct t.
      - simpl.
        unfold rvscale, rvmax, const.
        apply Rle_trans with (r2 := 1 * Rmax (M 0%nat a) G0).
        + rewrite Rmult_1_l.
          apply Rmax_l.
        + apply Rmult_le_compat_r.
          * apply Rle_trans with (r2 := G0); try lra.
            apply Rmax_r.
          * lra.
      - simpl.
        unfold rvscale, rvchoice.
        match_case; intros.
        + match_destr_in H13.
        + apply Rle_trans with (r2 := (1 + ε) * (M (S t) a)).
          * rewrite <- (Rmult_1_l (M (S t) a)) at 1.
            apply Rmult_le_compat_r; try lra.
            unfold M.
            apply Rmax_list_map_seq_ge; try lia.
            exists (0%nat).
            split; try lia.
            apply rvmaxabs_pos.
          * generalize (powerRZ_ge_scale (1 + ε) (M (S t) a) G0); intros.
            cut_to H14; try lra.
            apply Rmult_le_compat_l; try lra.
    }
    assert (forall t ω,
               (G t ω < G (S t) ω) ->
               (M (S t) ω <= G (S t) ω)).
    {
      intros ???.
      simpl in H14; simpl.
      unfold rvmax, const, rvchoice, rvscale in H14.
      unfold rvmax, const, rvchoice, rvscale.
      match_destr_in H14; try lra.
      apply powerRZ_ge_scale; try lra.
   }
    assert (adaptX : IsAdapted (Rvector_borel_sa (S n)) X F).
    {
      intros ?.
      induction n0.
      - easy.
      - rewrite H6.
        apply Rvector_plus_rv.
        + apply Rvector_minus_rv.
          * now apply (RandomVariable_sa_sub (isfilt n0)).
          * apply Rvector_mult_rv.
            -- now apply (RandomVariable_sa_sub (isfilt n0)).
            -- now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply Rvector_mult_rv.
          * now apply (RandomVariable_sa_sub (isfilt n0)).
          * apply Rvector_plus_rv; try easy.
    }            
    assert (adaptM : IsAdapted borel_sa M F).
    {
      intros ?.
      unfold M.
      induction n0.
      - unfold Rmax_list_map; simpl.
        now apply Rvector_max_abs_rv.
      - unfold Rmax_list_map.
        assert (rv_eq
                   (fun ω : Ts => Max_{ seq 0 (S (S n0))}(fun n1 : nat => rvmaxabs (X n1) ω))
                   (fun ω : Ts => Rmax (Max_{ seq 0 (S n0)}(fun n1 : nat => rvmaxabs (X n1) ω))
                                       (rvmaxabs (X (S n0)) ω))).
        {
          intros ?.
          rewrite Rmax_list_Sn; try lia.
          now replace (0 + S n0)%nat with (S n0) by lia.
        }
        assert (RandomVariable (F (S n0)) borel_sa
                   (fun ω : Ts => Rmax (Max_{ seq 0 (S n0)}(fun n1 : nat => rvmaxabs (X n1) ω))
                                       (rvmaxabs (X (S n0)) ω))).
        {
          apply rvmax_rv.
          - now apply (RandomVariable_sa_sub (isfilt n0)).
          - now apply Rvector_max_abs_rv.
        }
        revert H16.
        apply RandomVariable_proper; try easy.
    }

    assert (Mnneg:forall t ω, 0 <= M t ω).
    {
      intros.
      unfold M.
      apply Rmax_list_map_seq_ge; try lia.
      exists (0%nat).
      split; try lia.
      apply rvmaxabs_pos.
    }

    assert (Gnneg:forall t ω, 0 <= G t ω).
    {
      intros.
      induction t.
      - simpl.
        unfold rvmax, const.
        apply Rle_trans with (r2 :=  G0); try lra.
        apply Rmax_r.
      - simpl.
        unfold rvchoice, rvscale.
        match_destr.
        generalize (powerRZ_ge_scale (1 + ε) (M (S t) ω) G0); intros.      
        cut_to H15; try lra.
        specialize (Mnneg (S t) ω).
        lra.
    }

    assert (Gincr: forall t, rv_le (G t) (G (S t))).
    {
      intros ??.
      simpl.
      unfold rvchoice, rvscale.
      match_case; intros; try lra.
      match_destr_in H15.
      assert (M (S t) a > (1 + ε) * G t a) by lra.
      generalize (powerRZ_ge_scale (1 + ε) (M (S t) a) G0); intros.      
      cut_to H17; try lra.
      apply Rle_trans with (r2 := (M (S t) a)); try lra.
      apply Rle_trans with (r2 := (1 + ε) * G t a); try lra.
      rewrite <- Rmult_1_l at 1.
      apply Rmult_le_compat_r; try lra.
      apply Gnneg.
    }

    assert (Gpos1:forall t ω, 1 < G t ω).
    {
      intros.
      induction t.
      - simpl.
        unfold rvmax, const.
        apply Rlt_le_trans with (r2 := G0); try lra.
        apply Rmax_r.
      - specialize (Gincr t ω).
        lra.
   }
    assert (Gpos:forall t ω, 0 < G t ω).
    {
      intros.
      specialize (Gpos1 t ω);lra.
   }
    assert (adaptG : IsAdapted borel_sa G F).
    {
      intros ?.
      induction n0.
      - simpl.
        typeclasses eauto.
      - simpl.
        assert (rvc:RandomVariable (F (S n0)) (discrete_sa bool)
                  (fun x : Ts => if Rle_dec (M (S n0) x) ((1 + ε) * G n0 x) then true else false)).
        { 
          Existing Instance FiniteRange_FiniteRangeFunction.
          apply (frf_singleton_rv _ _).
          intros [|] _; unfold pre_event_singleton, pre_event_singleton, pre_event_preimage; simpl.
          * apply sa_proper with
                (x := (fun ω => (rvminus (M (S n0)) 
                                         (rvscale (1 + ε) (G n0)) ω) <= 0)). 
            -- intros ?.
               rv_unfold'.
               match_destr.
               ++ assert (M (S n0) x - (1 + ε) * G n0 x <= 0) by lra.
                  try easy.
               ++ assert (~(M (S n0) x - (1 + ε) * G n0 x <= 0)) by lra.
                  try easy.
            -- apply sa_le_le_rv.
               apply rvminus_rv; try easy.
               apply (RandomVariable_sa_sub (isfilt n0)).
               now apply rvscale_rv.
          * apply sa_proper with
                (x := (fun ω => (rvminus (M (S n0)) 
                                         (rvscale (1 + ε) (G n0)) ω) > 0)). 
            -- intros ?.
               rv_unfold'.
               match_destr.
               ++ assert (~ (M (S n0) x - (1 + ε) * G n0 x > 0)) by lra.
                  try easy.
               ++ assert ((M (S n0) x - (1 + ε) * G n0 x > 0)) by lra.
                  try easy.
            -- apply sa_le_gt_rv.
               apply rvminus_rv; try easy.
               apply (RandomVariable_sa_sub (isfilt n0)).
               now apply rvscale_rv.
        }
        apply rvchoiceb_rv; try easy.
        + now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply rvscale_rv.
          apply (@compose_rv Ts R R (F (S n0)) borel_sa borel_sa
                             (fun ω => M (S n0) ω / G0)
                             (fun z => powerRZ_ge_fun (1 + ε) z)).
          * assert (RandomVariable (F (S n0)) borel_sa
                                   (rvscale (/ G0) (M (S n0)))).
            {
              apply rvscale_rv.
              apply adaptM.
            }
            revert H15.
            apply RandomVariable_proper; try easy.
            intros ?.
            unfold rvscale; lra.
          * apply powerRZ_ge_fun_rv.
    }
    
    pose (ww := fun t => vecrvscalerv (rvinv (G t)) (w t)).

    assert (rvww :  forall (k i : nat) (pf : (i < (S n))%nat), RandomVariable dom borel_sa (vecrvnth i pf (ww k))).
    {
      intros.
      unfold ww.
      apply vecrvnth_rv.
      apply Rvector_scale_rv_rv.
      - apply rvinv_rv.
        now apply (RandomVariable_sa_sub (filt_sub k)).
      - apply rv_vecrvnth.
        apply rvw.
   }

    assert (expw0 : forall k i pf, Expectation (vecrvnth i pf (w k)) = Some (Finite 0)).
      {
        intros.
        specialize (H2 k i pf).
        specialize (iscond k i pf).
        generalize (@is_conditional_expectation_Expectation Ts dom prts (F k) (vecrvnth i pf (w k))); intros.
        specialize (H15 _ _ _ iscond).
        assert (RandomVariable dom Rbar_borel_sa
                               (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))).
        {
          apply (RandomVariable_sa_sub (filt_sub k)).
          apply Condexp_rv.
        }
        generalize (Rbar_Expectation_almostR2_proper prts (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k))) (fun x : Ts => const 0 x) H2); intros.
        rewrite H17 in H15.
        now rewrite Rbar_Expectation_finite_const in H15.
      }
      assert (isfef : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (w k))).
      {
        intros.
        unfold IsFiniteExpectation.
        now rewrite expw0.
      }
      assert (isfefg: forall k i pf, IsFiniteExpectation prts (rvmult (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        intros.
        destruct (IsFiniteExpectation_parts prts _ (isfef k i pf)).
        assert (forall t ω, 0 < rvinv (G t) ω < 1).
        {
          intros.
          specialize (Gpos1 t ω).
          rewrite rvinv_Rinv; try lra.
          split.
          - apply Rinv_0_lt_compat; lra.
          - replace 1 with (/ 1) by lra.
            apply Rinv_lt_contravar; lra.
        }
        apply IsFiniteExpectation_from_parts.
        - apply IsFiniteExpectation_bounded with
              (rv_X1 := const 0) (rv_X3 := pos_fun_part (vecrvnth i pf (w k))); trivial.
          + apply IsFiniteExpectation_const.
          + apply positive_part_nnf.
          + assert (rv_eq  (fun x : Ts => nonneg (pos_fun_part (rvmult (vecrvnth i pf (w k)) (rvinv (G k))) x))
                           (rvmult (fun x : Ts => nonneg (pos_fun_part (vecrvnth i pf (w k)) x))
                                   (rvinv (G k)))).
            {
              intros ?.
              unfold rvmult.
              unfold pos_fun_part.
              simpl.
              rewrite Rmax_mult.
              - now rewrite Rmult_0_l.
              - specialize (H17 k a); lra.
            }
            rewrite H18.
            intros ?.
            unfold rvmult.
            rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l.
            * apply positive_part_nnf.
            * specialize (H17 k a); lra.
      - apply IsFiniteExpectation_bounded with
              (rv_X1 := const 0) (rv_X3 := neg_fun_part (vecrvnth i pf (w k))); trivial.
        + apply IsFiniteExpectation_const.
        + apply negative_part_nnf.
        + assert (rv_eq  (fun x : Ts => nonneg (neg_fun_part (rvmult (vecrvnth i pf (w k)) (rvinv (G k))) x))
                           (rvmult (fun x : Ts => nonneg (neg_fun_part (vecrvnth i pf (w k)) x))
                                   (rvinv (G k)))).
            {
              intros ?.
              unfold rvmult.
              unfold neg_fun_part.
              simpl.
              rewrite Rmax_mult.
              - rewrite Rmult_0_l.
                f_equal.
                lra.
              - specialize (H17 k a); lra.
            }
            rewrite H18.
            intros ?.
            unfold rvmult.
            rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l.
            * apply negative_part_nnf.
            * specialize (H17 k a); lra.
      }
    assert (forall k i pf,
                 almostR2 prts eq (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (ww k)))
                          (fun x : Ts => const 0 x)).
    {
      intros.
      assert (RandomVariable (F k) borel_sa (rvinv (G k))).
      {
        now apply rvinv_rv.
      }
      assert (RandomVariable dom borel_sa (rvmult (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        apply rvmult_rv.
        - apply rvw.
        - apply rvinv_rv.
          now apply (RandomVariable_sa_sub (filt_sub k)).          
      }
      generalize (Condexp_factor_out prts (filt_sub k) (vecrvnth i pf (w k)) (rvinv (G k))); intros.
      apply almost_prob_space_sa_sub_lift in H17.
      revert H17; apply almost_impl.
      specialize (H2 k i pf).
      revert H2.
      apply almost_impl, all_almost; intros ???.
      unfold ww.
      assert (rv_eq
                (vecrvnth i pf (vecrvscalerv (rvinv (G k)) (w k)))
                (rvmult  (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        intros ?.
        unfold vecrvnth, vecrvscalerv.
        unfold rvmult.
        rewrite Rvector_nth_scale.
        lra.
      }
      erewrite (ConditionalExpectation_ext _ (filt_sub k) _ _ H18).
      rewrite H17.
      unfold Rbar_rvmult.
      rewrite H2.
      unfold const.
      apply Rbar_mult_0_r.
    }

    assert (exists (K : R),
               forall k i pf,
                 almostR2 prts Rbar_le
                          (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (ww k))))
                          (const K)).
    {
      destruct H3 as [A [B [? [? ?]]]].
      assert (exists (K : R),
                 forall t ω,
                   (A + B * Rsqr (M t ω))/(Rsqr (G t ω)) <= K).
      {
        exists ((A / Rsqr G0) + B * (Rsqr (1 + ε))).
        intros.
        assert (0 < (Rsqr (G t ω))).
        {
          unfold Rsqr.
          now apply Rmult_lt_0_compat.
        }

        assert (0 < Rsqr G0).
        {
          unfold Rsqr.
          apply Rmult_lt_0_compat; lra.
        }

        assert (A / (Rsqr (G t ω)) <= A / Rsqr G0).
        {
          unfold Rdiv.
          apply Rmult_le_compat_l; try lra.
          apply Rle_Rinv; try lra.
          apply Rsqr_incr_1; try lra.
          induction t.
          - simpl.
            unfold rvmax, const.
            apply Rmax_r.
          - cut_to IHt.
            + eapply Rle_trans.
              apply IHt.
              apply Gincr.
            + unfold Rsqr.
              now apply Rmult_lt_0_compat.
          - now left.
        }
        assert (0 <> (Rsqr (G t ω))).
        {
          now apply Rlt_not_eq.
        }
        assert ((B * Rsqr (M t ω))/(Rsqr (G t ω)) <= B * Rsqr (1 + ε)).
        {
          specialize (H13 t ω).
          unfold rvscale in H13.
          apply Rmult_le_reg_r with (r := Rsqr (G t ω)); try lra.
          field_simplify; try lra.
          rewrite Rmult_assoc.
          apply Rmult_le_compat_l; try lra.
          apply Rsqr_incr_1 in H13.
          - rewrite Rsqr_mult in H13; try lra.
          - apply Mnneg.
          - apply Rle_trans with (r2 := (G t ω)).
            + now left.
            + rewrite <- Rmult_1_l at 1.
              apply Rmult_le_compat_r; try lra.
              now left.
        }
        generalize (Rplus_le_compat _ _ _ _ H20 H22); intros.
        assert (0 <> Rsqr G0).
        {
          now apply Rlt_not_eq.
        }
        field_simplify in H23; try lra.
      }
      destruct H18 as [K ?].
      exists K.
      intros.
      specialize (H15 k i pf).
      unfold ww.
      generalize (is_conditional_expectation_factor_out_nneg_both_Rbar prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k)))); intros.
      specialize (H19 (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))))).
      assert (RandomVariable dom borel_sa (rvsqr (rvinv (G k)))).
      {
        apply rvsqr_rv, rvinv_rv.
        now apply (RandomVariable_sa_sub (filt_sub k)).
      }
      generalize (NonNegCondexp_cond_exp prts (filt_sub k) (rvmult (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k))))); intros.
      assert (Rbar_NonnegativeFunction (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k)))) ).
      {
        apply Condexp_nneg.
        typeclasses eauto.
      }
      assert (RandomVariable (F k) borel_sa (rvsqr (rvinv (G k)))).
      {
        now apply rvsqr_rv, rvinv_rv.
      }
      specialize (H19 _ _ _ _ _ _ _ ).
      assert (rvgce : RandomVariable (F k) Rbar_borel_sa
                                      (Rbar_rvmult (fun x : Ts => rvsqr (rvinv (G k)) x)
                        (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k)))))).
      {
        apply Rbar_rvmult_rv.
        - apply Real_Rbar_rv.
          typeclasses eauto.
        - apply Condexp_rv.
      }
      specialize (H19 _).
      cut_to H19.
      - revert H15; apply almost_impl.
        generalize (is_conditional_expectation_nneg_unique prts (filt_sub k) _ _ _ H19 H21); intros.
        apply almost_prob_space_sa_sub_lift in H15. 
        revert H15; apply almost_impl.
        specialize (H17 k i pf).
        revert H17; apply almost_impl.
        apply all_almost; intros ????.
        erewrite Condexp_nneg_simpl.
        assert (rv_eq
                  (rvsqr (vecrvnth i pf (vecrvscalerv (rvinv (G k)) (w k))))
                  (rvmult (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k))))).
        {
          intros ?.
          rv_unfold.
          unfold vecrvscalerv, vecrvnth.
          rewrite Rvector_nth_scale.
          rewrite Rsqr_mult.
          now apply Rmult_comm.
        }
        erewrite (NonNegCondexp_ext prts (filt_sub k) _ _ H25).
        rewrite <- H17.
        assert  (rvmaxlist (fun (j : nat) (ω : Ts) => rvsqr (rvmaxabs (X j)) ω) k x <= Rsqr (M k x)).
        {
          unfold M, rvmaxlist, rvsqr.
          unfold Rmax_list_map.
          apply Rmax_list_le_iff.
          - apply map_not_nil, seq_not_nil; lia.
          - intros.
            apply in_map_iff in H26.
            destruct H26 as [? [? ?]].
            rewrite <- H26.
            apply Rsqr_le_abs_1.
            rewrite Rabs_pos_eq.
            + rewrite Rabs_pos_eq.
              apply (Rmax_spec_map (seq 0 (S k)) (fun n0 : nat => rvmaxabs (X n0) x) x1 H27).
              apply Rmax_list_ge with (x := rvmaxabs (X x1) x).
              * apply in_map_iff.
                exists x1; split; trivial.
              * apply rvmaxabs_pos.
            + apply rvmaxabs_pos.
        }
        assert (Rbar_le (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))) x)
                        (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr (M k))) x)).
        {
           eapply Rbar_le_trans.
           apply H15.
           rv_unfold.
           simpl.
           rewrite Rabs_right; try lra.
           rewrite Rabs_right; try lra.           
           apply Rplus_le_compat_l.
           apply Rmult_le_compat_l.
           - lra.
           - apply H26.
        }
        unfold Rbar_rvmult, const.
        assert (0 < rvsqr (rvinv (G k)) x).
        {
          unfold rvsqr.
          apply Rsqr_pos_lt.
          apply Rgt_not_eq.
          unfold rvinv, rvpower, const.
          apply power_pos.
          apply Gpos.
        }
        rewrite Rbar_mult_comm.
        rewrite Rbar_mult_pos_le with (z := mkposreal _ H28) in H27.
        simpl in H27.
        rewrite Rbar_mult_mult_pos in H27.
        eapply Rbar_le_trans.
        apply H27.
        rv_unfold.
        simpl.
        rewrite Rabs_right; try lra.
        rewrite Rabs_right; try lra.
        specialize (H18 k x).
        unfold Rdiv in H18.
        replace (Rsqr (rvinv (G k) x)) with (/ Rsqr (G k x)); trivial.
        assert (G k x <> 0).
        {
          apply Rgt_not_eq, Gpos.
        }
        rewrite rvinv_Rinv; trivial.
        rewrite Rsqr_inv; trivial.
      - apply Condexp_cond_exp_nneg.
        typeclasses eauto.
    }
    destruct
    (classic
       (exists D0 : Ts -> R, forall k : nat, almostR2 prts Rle (rvmaxabs (X k)) D0)); trivial.
    push_neg_in H17.
    assert (forall x : Ts -> R, exists x0 : nat, exists pt : Ts, Rgt (rvmaxabs (X x0) pt) (x pt)).
    {
      intros x.
      specialize (H17 x).
      destruct H17 as [x0 HH].
      exists x0.
      unfold almostR2,almost in HH.
      push_neg_in HH.
      specialize (HH Ω ps_one).
      destruct HH as [pt [_ HH]].
      exists pt.
      lra.
    }
    pose (WW := fix WW i pf t' t0 :=
                  match t' with
                  | 0%nat => const 0
                  | (S t) => 
                    rvplus 
                      (rvmult 
                         (rvminus (const 1) (vecrvnth i pf (α (t + t0)%nat)))
                         (WW i pf t t0))
                      (rvmult (vecrvnth i pf (beta (t + t0)%nat))
                              (vecrvnth i pf (ww (t + t0)%nat)))
                  end).
    assert (forall i pf,
               almost prts (fun ω => is_lim_seq (fun k => WW i pf k 0%nat ω) 0)).
    {
      intros.
(*
      destruct H1 as [Ca ?].
      destruct beta_fin as [Cb ?].
*)
      destruct H16 as [K ?].
      
      apply lemma1_alpha_beta_uniform with
          (α := fun k => vecrvnth i pf (α k))
          (β := fun k => vecrvnth i pf (beta k))
          (w := fun k => vecrvnth i pf (ww k))
          (filt_sub := filt_sub) 
          (rv := fun k => rvww k i pf)
          (B := fun _ => const K); try easy.
      - simpl.
        apply rvconst.
      - unfold IsAdapted; intros.
        apply rvconst.
      - unfold IsAdapted; intros.
        unfold ww.
        apply vecrvnth_rv.
        apply Rvector_scale_rv_rv.
        + apply rvinv_rv.
          now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply adapt_w.
      - unfold IsAdapted.
        intros.
        now apply vecrvnth_rv.
      - unfold IsAdapted.
        intros.
        now apply vecrvnth_rv.
      - intros.
        apply Condexp_cond_exp.
        unfold ww.
        specialize (isfefg n0 i pf).
        revert isfefg.
        apply IsFiniteExpectation_proper.
        intros ?.
        unfold vecrvnth, vecrvscalerv, rvmult, Rvector_scale.
        rewrite vector_nth_map.
        apply Rmult_comm.
      - intros.
        revert H.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H.
      - intros.
        revert beta_prop.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H19.
      - intros.
        revert H.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H.
      - intros.
        revert beta_prop.
        apply almost_impl.
        apply all_almost.
        intros ??.
        apply H19.
      - revert H0; apply almost_impl.
        apply all_almost; intros ??.
        specialize (H0 i pf).
        now unfold vecrvnth.
      - revert beta_inf; apply almost_impl.
        apply all_almost; intros ??.
        apply H19.
      - apply beta_fin.
      - destruct beta_eps as [eps ?].
        exists eps.
        revert H19.
        apply eventually_impl.
        apply all_eventually.
        intros.
        specialize (H19 i pf).
        revert H19.
        apply almost_impl, all_almost.
        intros ??.
        now unfold rvsqr, vecrvnth.
      - intros.
        simpl.
        rv_unfold.
        replace (n0 + 0)%nat with n0 by lia.
        lra.
      - exists (const K).
        apply all_almost.
        intros.
        apply Rle_abs.
    }

    assert (almost prts (fun ω =>
                          forall i pf,
                            is_lim_seq (fun k => WW i pf k 0%nat ω) 0)).
    {
      apply almost_bounded_forall.
      intros.
      - apply lt_dec.
      - intros.
        apply is_lim_seq_ext with (u := (fun k : nat => WW i pf1 k 0%nat x)); trivial.
        intros.
        now rewrite (digit_pf_irrel _ _ pf2 pf1).   
      - apply H19.
    }
    
    assert (almost prts (fun ω =>
                           is_lim_seq (fun k : nat => M k ω) p_infty ->
                           exists t0 : nat, 
                             forall t,
                               (G t0 ω = G (t + t0)%nat ω))).
    {
      generalize (lemma3_almost_Jaakkola_beta WW ε G0 α beta X ww M G XF); intros.
      cut_to H21; try easy.
      - assert (almost prts (fun ω : Ts => is_lim_seq (fun k : nat => M k ω) p_infty -> exists t0 : nat, M t0 ω <= G t0 ω /\ (forall (t i : nat) (pf : (i < S n)%nat), Rabs (WW i pf t t0 ω) <= ε))).
        {
          revert H; apply almost_impl.
          revert beta_prop; apply almost_impl.
          revert H20; apply almost_impl, all_almost; intros ?????.
          generalize (lemma3_pre0 x (mkposreal _ H11) G M H23); intros.
          cut_to H24; try easy.
          - generalize (lemma3_pre1_beta WW x (mkposreal _ H11) α beta ww ); intros.
            cut_to H25; try easy.
            + destruct H25.
              specialize (H24 x0).
              destruct H24 as [? [? ?]].
              exists x1.
              split; trivial.
              intros.
              specialize (H25 i pf x1 t H24).
              apply H25.
            + intros.
              apply H22.
            + intros.
              apply H20.
            + intros.
              simpl.
              rv_unfold.
              lra.
        - intros.
          simpl.
          apply H13.
        - intros.
          apply Gincr.
        - intros.
          now apply H14.
        }
        specialize (H21 H22).
        revert H21.
        apply almost_impl, all_almost; intros ???.
        destruct (H21 H23).
        exists x0.
        intros.
        symmetry.
        apply H24.
      - intros.
        simpl.
        unfold rvchoice.
        match_case; intros.
        now match_destr_in H23.
      - intros.
        apply H13.
      - intros.
        unfold M.
        unfold Rmax_list_map.
        rewrite Rmax_list_Sn; try lia.
        now simpl.
      - intros.
        unfold M.
        apply Rle_trans with (r2 := rvmaxabs (X t) ω).
        + apply Rvector_max_abs_nth_le.
        + unfold Rmax_list_map.
          apply Rmax_spec.
          apply in_map_iff.
          exists t.
          split; trivial.
          apply in_seq.
          lia.
      - intros.
        simpl.
        rv_unfold.
        lra.
      - intros.
        rewrite H6.
        intros ?.
        unfold ww, vecrvscalerv.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale.
        do 3 f_equal.
        rewrite Rvector_scale_scale.
        specialize (Gpos k a).
        rewrite rvinv_Rinv; trivial.
        rewrite <- Rinv_r_sym; try lra.
        now rewrite Rvector_scale1.
      - revert H10; apply almost_impl.
        apply all_almost; intros a?.
        intros.
        eapply Rle_trans.
        apply H10.
        assert (Rvector_max_abs (X k a) <= (1 + ε) * G k a).
        {
          apply Rle_trans with (r2 := M k a).
          - unfold M.
            unfold Rmax_list_map, rvmaxabs.
            apply Rmax_spec.
            apply in_map_iff.
            exists k.
            split; trivial.
            apply in_seq.
            lia.
          - apply H13.
        }
        replace (G k a) with (γ * ((1 + ε) * G k a)).
        + apply Rmult_le_compat_l; try lra.
          apply Rle_Rmax.
          split; trivial.
          apply Rle_trans with (r2 := G k a).
          * clear H22.
            induction k.
            -- simpl.
               unfold rvmax, const.
               apply Rmax_r.
            -- eapply Rle_trans.
               apply IHk.
               apply Gincr.
          * rewrite <- Rmult_1_l at 1.
            apply Rmult_le_compat_r; try lra.
            left; apply Gpos.
        + rewrite <- Rmult_assoc.
          rewrite H12.
          lra.
    }
    assert (almost prts (fun ω =>
                           is_lim_seq (fun k : nat => M k ω) p_infty ->
                           exists D0 : R,
                             forall t,
                               M t ω <= D0)).
    {
      revert H21.
      apply almost_impl, all_almost; intros ???.
      destruct (H21 H22).
      exists ((1 + ε) * (G x0 x)).
      intros.
      destruct (le_dec t x0).
      - apply Rle_trans with (r2 := M x0 x).
        + unfold M.
          apply Rmax_seq_map_monotone.
          lia.
        + apply H13.
      - specialize (H23 (t - x0)%nat).
        replace (t - x0 + x0)%nat with t in H23 by lia.
        rewrite H23.
        apply H13.
   }
    assert (almost prts
                   (fun ω => exists D0 : R,
                        forall t,
                          M t ω <= D0)).
    {
      revert H22.
      apply almost_impl, all_almost; intros ??.
      destruct (classic (is_lim_seq (fun k : nat => M k x) p_infty)).
      - specialize (H22 H23).
        destruct H22.
        exists x0.
        intros.
        apply H22.
      - assert (ex_finite_lim_seq (fun k => M k x)).
        {
          assert (forall k, M k x <= M (S k) x).
          {
            intros.
            unfold M.
            apply Rmax_seq_map_monotone.
            lia.
          }
          generalize (ex_lim_seq_incr _ H24); intros.
          apply ex_finite_lim_seq_correct.
          split; trivial.
          case_eq (Lim_seq (fun k : nat => M k x)); intros.
          - now simpl.
          - apply Lim_seq_correct in H25.
            now rewrite H26 in H25.
          - generalize (Lim_seq_pos (fun k => M k x)); intros.
            cut_to H27.
            + now rewrite H26 in H27.
            + intros.
              apply Mnneg.
        }
        destruct H24.
        apply is_lim_seq_bounded in H24.
        destruct H24.
        exists x1.
        intros.
        specialize (H24 t).
        eapply Rle_trans.
        shelve.
        apply H24.
        Unshelve.
        apply Rle_abs.
    }
    assert (exists D0 : Ts -> R,
               forall k, almostR2 prts Rle (M k) D0).
    {
      apply exists_almost in H23.
      destruct H23 as [??].
      exists x.
      now apply forall_almost.
    }
    destruct H24.
    exists x.
    intros.
    specialize (H24 k).
    revert H24.
    apply almost_impl, all_almost; intros ??.
    unfold M in H24.
    unfold Rmax_list_map in H24.
    eapply Rle_trans.
    shelve.
    apply H24.
    Unshelve.
    apply Rmax_spec.
    apply in_map_iff.
    exists k.
    split; trivial.
    apply in_seq.
    lia.
 Qed.

  Theorem Tsitsiklis3_beta_pos {n}
    (X w α : nat -> Ts -> vector R n)
    (β : R) (D0' : Ts -> R) 
    (x' : vector R n)
    (XF : nat -> vector R n -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    {rvXF : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
    {posD0' : forall ω, 0 < D0' ω}
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A)) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0') ->
    0 < β < 1 ->
    (forall k ω, Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') <=
                 β * Rvector_max_abs (Rvector_minus (X k ω) x')) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (Rvector_minus (X n ω) x')) 0).
 Proof.
   intros.
   pose (eps := (1/β-1)/3).
   pose (Xx := fun n ω => Rvector_minus (X n ω) x').
   assert (HH4: exists (D0 : Ts -> R),
              (forall k, almostR2 prts Rle (rvmaxabs (Xx k)) D0) /\
                (forall ω, 0 < D0 ω)).
   {
     exists (fun ω => (D0' ω) + Rvector_max_abs x').
     split.
     - intros.
       specialize (H4 k).
       revert H4.
       apply almost_impl, all_almost; intros ??.
       subst Xx.
       apply Rplus_le_compat_r with (r := Rvector_max_abs x') in H4.
       unfold rvmaxabs, Rvector_minus.
       eapply Rle_trans.
       apply Rvector_max_abs_triang.
       unfold rvmaxabs in H4.
       unfold Rvector_opp.
       rewrite Rvector_max_abs_scale.
       rewrite Rabs_m1.
       now rewrite Rmult_1_l.
     - intros.
       eapply Rlt_le_trans.
       apply (posD0' ω).
       rewrite <- Rplus_0_r at 1.
       apply Rplus_le_compat_l.
       apply Rvector_max_abs_nonneg.
   }
   destruct HH4 as [D0 [HH4 posD0]].
   assert (0 < eps).
   {
     unfold eps.
     assert (1 < 1 / β).
     {
       apply Rmult_lt_reg_r with (r := β); try lra.
       field_simplify; lra.
     }
     lra.
   }
   assert ((1 + 2 * eps) * β < 1).
   {
     unfold eps.
     apply Rplus_lt_reg_r with (x := -1).
     field_simplify; lra.
   }
   pose (D := fix D k :=
                match k with
                | 0%nat => D0
                | S k' => rvscale ((1 + 2 * eps) * β) (D k')
                end).
   assert (Dpos : forall k ω, 0 < D k ω).
   {
     intros.
     induction k.
     - simpl; apply posD0.
     - simpl.
       unfold rvscale.
       apply Rmult_lt_0_compat; try lra.
       apply Rmult_lt_0_compat; try lra.
   }       
   assert (forall ω, is_lim_seq (fun k => D k ω) 0).
   {
     intros.
     apply is_lim_seq_ext with
         (u := fun n => (D0 ω) *  ((1 + 2 * eps) * β)^n).
     - intros.
       induction n0.
       + unfold D.
         rewrite pow_O.
         now rewrite Rmult_1_r.
       + simpl.
         unfold rvscale.
         rewrite <- IHn0.
         ring.
     - replace (Finite 0) with (Rbar_mult (D0 ω) 0) by apply Rbar_mult_0_r.
       apply is_lim_seq_scal_l.
       apply is_lim_seq_geom.
       rewrite Rabs_right; trivial.
       apply Rle_ge.
       apply Rmult_le_pos; lra.
   }
   assert (forall (k : nat),
              exists (N : Ts -> nat),
                almost prts
                       (fun ω =>
                          forall (t : nat),
                            (N ω <= t)%nat ->
                            (rvmaxabs (Xx t) ω) <= (D k ω))).
   {
     induction k.
     - exists (const 0%nat).
       apply almost_forall in HH4.
       revert HH4.
       apply almost_impl, all_almost; intros ????.
       apply H11.
     - destruct IHk as [N ?].
       assert (forall i pf,
                  exists (N0 : Ts -> nat),
                    almost prts (fun ω =>
                                   forall t : nat, 
                                     (N0 ω <= t)%nat ->
                                     (rvabs (vecrvnth i pf (Xx t)) ω) <= (D (S k) ω))).
       {
         intros.

         pose (X1 := fun t => vecrvnth i pf (Xx t)).
         pose (α1 := fun t => vecrvnth i pf (α t)).
         pose (w1 := fun t => vecrvnth i pf (w t)).
         pose (W := fix W t' :=
                    match t' with
                    | 0%nat => const 0
                    | (S t) => 
                      rvplus 
                        (rvmult 
                           (rvminus (const 1) (α1 t))
                           (W t))
                        (rvmult (α1 t) (w1 t))
                    end).
         pose (WW := fix WW t' t0 :=
                    match t' with
                    | 0%nat => const 0
                    | (S t) => 
                      rvplus 
                        (rvmult 
                           (rvminus (const 1) (α1 (t + t0)%nat))
                           (WW t t0))
                        (rvmult (α1 (t + t0)%nat) (w1 (t + t0)%nat))
                    end).
       assert (almost prts
                      (fun ω => is_lim_seq (fun n => W n ω) 0)).
       {
         destruct H3 as [A [B ?]].
         destruct H1 as [Ca ?].
         pose (BB := fun (n : nat) =>
                       rvplus (const (Rabs A)) 
                              (rvscale (Rabs B)
                                       (rvmaxlist (fun (j : nat) => rvsqr (rvmaxabs (X j))) n))).
(*
         pose (BB := fun (n:nat) => rvplus (const A) (rvscale (Rabs B) (rvsqr D0))).
*)
         eapply lemma1_alpha_alpha with (α := α1) (w := w1) (W := W) (filt_sub := filt_sub) (B := BB) (Ca := Ca); try easy.
         - simpl.
           typeclasses eauto.
         - intros ?.
           unfold BB; simpl.
           apply rvplus_rv; try typeclasses eauto.
           apply rvscale_rv.
           apply rvmaxlist_rv.
           intros.
           apply rvsqr_rv.
           apply Rvector_max_abs_rv.
           assert (sa_sub (F n1) (F n0)) by 
               now apply is_filtration_le.
           apply (RandomVariable_sa_sub H13).
           clear H12 H13.
           induction n1; trivial.
           rewrite H7.
           apply Rvector_plus_rv.
           + now apply (RandomVariable_sa_sub (isfilt n1)).
           + apply Rvector_mult_rv.
             * now apply (RandomVariable_sa_sub (isfilt n1)).
             * apply Rvector_plus_rv; trivial.
               apply Rvector_minus_rv.
               ++ apply (RandomVariable_sa_sub (isfilt n1)).
                  now apply (compose_rv (dom2 := Rvector_borel_sa n)).
               ++ now apply (RandomVariable_sa_sub (isfilt n1)).
         - unfold w1.
           intros ?.
           now apply vecrvnth_rv.
         - unfold α1.
           intros ?.
           now apply vecrvnth_rv.
         - intros.
           unfold w1.
           apply iscond.
         - intros.
           unfold w1.
           apply H2.
         - intros.
           unfold w1.
           specialize (H3 n0 i pf).
           revert H3; apply almost_impl.
           apply almost_forall in H4.
           revert H4; apply almost_impl.
           apply all_almost; intros ???.
           unfold rvsqr, vecrvnth.
           eapply Rbar_le_trans.
           apply H4.
           unfold BB.
           rv_unfold.
           simpl.
           lra.
         - intros.
           apply H.
         - intros.
           unfold α1.
           specialize (H n0 x i pf).
           unfold vecrvnth.
           lra.
         - apply all_almost.
           intros.
           unfold α1, vecrvnth.
           apply H0.
         - unfold rvsqr, const.
           unfold α1.
           specialize (H1 i pf).
           revert H1.
           apply almost_impl, all_almost; intros ??.
           apply H1.
         - intros.
           simpl.
           now rv_unfold'.
         - exists (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr D0'))).
           apply almost_forall in H4.
           revert H4.
           apply almost_impl, all_almost; intros ???.
           unfold BB.
           rv_unfold.
           assert (Rabs B * Rsqr (D0' x) = Rabs (B * Rsqr(D0' x))).
           {
             rewrite Rabs_mult.
             f_equal.
             now rewrite <- Rabs_sqr.
           }
           rewrite H12.
           rewrite Rabs_plus.
           apply Rplus_le_compat_l.
           rewrite <- H12.
           apply Rmult_le_compat_l.
           + apply Rabs_pos.
           + unfold rvmaxlist.
             unfold Rmax_list_map.
             apply Rmax_list_le_iff.
             * apply map_not_nil.
               apply seq_not_nil.
               lia.
             * intros.
               apply in_map_iff in H13.
               destruct H13 as [? [? ?]].
               rewrite <- H13.
               specialize (H4 x1).
               simpl in H4.
               apply Rsqr_le_abs_1.
               rewrite Rabs_right.
               -- eapply Rle_trans.
                  ++ apply H4.
                  ++ apply Rle_abs.
               -- apply Rle_ge, rvmaxabs_pos.
       }
       assert (almost prts
                      (fun ω => is_lim_seq (fun n => WW n 0%nat ω) 0)).
       {
         revert H12.
         apply almost_impl, all_almost; unfold impl; intros ?.
         apply is_lim_seq_ext.
         induction n0.
         - now simpl.
         - simpl.
           rv_unfold'.
           rewrite IHn0.
           now replace (n0 + 0)%nat with n0 by lia.
       }
       generalize (lemma2_almost WW α1 w1); intros.
       cut_to H14; cycle 1; try easy.
         - unfold α1.
           intros.
           apply H.
         - intros.
           simpl.
           now rv_unfold'.
         - assert (forall ω, 0 < β * eps * (D k ω)).
           {
             intros.
             apply Rmult_lt_0_compat; try easy.
             apply Rmult_lt_0_compat; lra.
           }
           specialize (H14 (fun ω => mkposreal _ (H15 ω))).
           destruct H14 as [N2 ?].
           pose (tauk := fun ω => max (N ω) (N2 ω)) .
           pose (αtau := fun t ω => α1 (t + tauk ω)%nat ω).

           pose (Y := fix Y t' :=
                    match t' with
                    | 0%nat => (D k)
                    | (S t) =>
                      rvplus 
                        (rvmult 
                           (rvminus (const 1) (αtau t))
                           (Y t))
                        (rvmult (αtau t) (rvscale β (D k)))
                    end).
           pose (Xtau := fun t ω => X1 (t + tauk ω)%nat ω).
           pose (wtau := fun t ω => w1 (t + tauk ω)%nat ω).
           pose (Wtau := fun t ω => WW t (tauk ω) ω).
           generalize (lemma8_abs_combined_almost Xtau Y Wtau αtau wtau); intros.
           simpl.
           specialize (H16 (mkposreal _ H8) β (fun ω => mkposreal _ (Dpos k ω))).
           cut_to H16; try easy. 
           + destruct H16.
             exists (fun ω => ((tauk ω) + (x ω))%nat).
             revert H16.
             apply almost_impl, all_almost; intros ????.
             unfold Xtau, tauk, X1 in H16.
             specialize (H16 (t - tauk x0)%nat).
             cut_to H16; try lia.
             rv_unfold'_in_hyp H16.
             simpl in H16.
             rv_unfold.
             unfold tauk in H16.
             unfold tauk in H17.
             replace (t - Init.Nat.max (N x0) (N2 x0) + Init.Nat.max (N x0) (N2 x0))%nat with (t) in H16 by lia.
             lra.
           + intros.
             apply H.
           + intros.
             unfold Wtau, αtau, wtau.
             simpl.
             now rv_unfold'.
           + intros.
             simpl.
             rv_unfold.
             lra.
           + intros.
             clear H16 H13 H14 Wtau WW Y.
             revert H11.
             apply almost_impl, all_almost; intros ??.
             unfold Xtau, X1, vecrvnth, αtau, α1, wtau, w1.
             replace (S t + tauk x)%nat with (S (t + tauk x)) by lia.
             subst Xx.
             simpl.
             rewrite H7.
             unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult.
             unfold Rvector_minus.
             rewrite Rvector_nth_plus.
             rewrite Rvector_nth_plus, Rvector_nth_mult.
             repeat rewrite Rvector_nth_plus.
             rewrite Rvector_nth_scale.
             ring_simplify.
             unfold Rminus.
             repeat rewrite Rplus_assoc.
             do 2 apply Rplus_le_compat_l.
             apply Rplus_le_reg_r with
               (r := - vecrvnth i pf (α (t + tauk x)%nat) x * vecrvnth i pf (w (t + tauk x)%nat) x).
             apply Rplus_le_reg_r with (r := - vector_nth i pf (Rvector_opp x')).
             unfold Rvector_opp.
             rewrite Rvector_nth_scale.
             ring_simplify.
             rewrite <- Rmult_plus_distr_l.       
             rewrite <- Rmult_minus_distr_l.                    
             rewrite (Rmult_comm (vector_nth i pf x')).
             rewrite Rmult_assoc.
             rewrite <- Rmult_plus_distr_l.       
             apply Rmult_le_compat_l.
             apply H.
             unfold vecrvnth.
             specialize (H6 (t + tauk x)%nat x).
             apply Rplus_le_reg_r with (r := - vector_nth i pf x').
             ring_simplify.
             rewrite <- Rvector_nth_minus.
             eapply Rle_trans.
             apply Rle_abs.
             eapply Rle_trans.
             apply Rvector_max_abs_nth_le.
             eapply Rle_trans.
             apply H6.
             apply Rmult_le_compat_l; try lra.
             apply H11.
             unfold tauk; lia.
           + intros.
             clear H16 H13 H14 Wtau WW Y.
             revert H11.
             apply almost_impl, all_almost; intros ??.
             unfold Xtau, X1, vecrvnth, αtau, α1, wtau, w1.
             replace (S t + tauk x)%nat with (S (t + tauk x)) by lia.
             subst Xx.
             simpl.
             rewrite H7.
             unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult, vecrvnth.
             unfold Rvector_minus.
             rewrite Rvector_nth_plus.
             rewrite Rvector_nth_plus, Rvector_nth_mult.             
             repeat rewrite Rvector_nth_plus.
             rewrite Rvector_nth_scale.
             ring_simplify.
             apply Rplus_ge_compat_r.
             repeat rewrite Rplus_assoc.
             unfold Rminus.
             repeat rewrite Rplus_assoc.             
             do 2 apply Rplus_ge_compat_l.
             ring_simplify.
             rewrite <- Rmult_plus_distr_l.
             rewrite <- Rmult_minus_distr_l.
             rewrite Rmult_assoc.
             rewrite <- Rmult_minus_distr_l.
             apply Rmult_ge_compat_l.
             apply Rle_ge, H.
             apply Rplus_ge_reg_l with
               (r := - vector_nth i pf (w (t + tauk x)%nat x)).
             ring_simplify.
             unfold Rvector_opp.
             rewrite Rvector_nth_scale.
             apply Rplus_ge_reg_l with
               (r := - vector_nth i pf x').
             ring_simplify.
             assert (Rabs (vector_nth i pf (Rvector_minus (XF (t + tauk x)%nat (X (t + tauk x)%nat x))
                                                          x')) <=  β * D k x).
             {
               eapply Rle_trans.
               apply Rvector_max_abs_nth_le.
               eapply Rle_trans.
               apply H6.
               apply Rmult_le_compat_l; try lra.
               apply H11.
               unfold tauk; lia.
             }
             rewrite Rabs_le_between in H13.
             rewrite Rvector_nth_minus in H13.
             lra.
           + revert H11.
             apply almost_impl, all_almost; intros ???.
             simpl.
             specialize (H11 (t + tauk x)%nat).
             unfold Xtau, X1.
             cut_to H11; try lia.
             eapply Rle_trans.
             shelve.
             apply H11.
             unfold tauk.
             lia.
           + intros.
             apply Y_lim with (α := αtau); try easy.
             * intros.
               apply H.
             * intros.
               apply (seq_sum_shift (fun t => α1 t ω)).
               apply H0.
           + revert H14.
             apply almost_impl, all_almost; intros ??.
             exists (N2 x).
             intros.
             unfold Wtau.
             specialize (H14 (tauk x) n0).
             apply H14.
             unfold tauk.
             lia.
      }               
       apply bounded_nat_ex_choice_vector in H12.
       destruct H12.
       exists (fun ω => list_max (map (fun z => z ω) (proj1_sig x))).
       intros.
       assert (forall i pf ω,
                  (vector_nth i pf x ω <= 
                   list_max (map (fun z => z ω) (` x)))%nat).
       {
         intros.
         generalize (vector_nth_In x _ pf); intros HH.
         generalize (list_max_upper (map (fun z => z ω) (` x))); intros HH2.
         rewrite Forall_forall in HH2.
         apply HH2.
         apply in_map_iff.
         now exists (vector_nth i pf x).
       }
       
       assert (almost prts (fun x0 =>
                             forall i pf t,
                               (t >= vector_nth i pf x x0)%nat ->
                               (rvabs (vecrvnth i pf (Xx t)) x0) <=
                               (D (S k) x0))).
       {
         apply almost_bounded_forall.
         intros.
         - apply le_dec.
         - intros.
           rewrite (digit_pf_irrel _ _ pf2 pf1).
           apply H14.
           now rewrite (digit_pf_irrel _ _ pf2 pf1) in H15.
         - intros.
           apply H12.
       }
       revert H14.
       apply almost_impl, all_almost; intros ????.
       unfold rvmaxabs.
       unfold rvabs, vecrvnth in H15.
       destruct n.
       + assert (Rvector_max_abs (Xx t x0) = 0).
         {
           apply Rvector_max_abs_zero.
           rewrite vector0_0.
           apply (vector0_0 (Xx t x0)).
         }
         rewrite H16.
         clear H11 H12 H13 H14 H15.
         induction k.
         * unfold D.
           unfold rvscale.
           apply Rmult_le_pos; trivial.
           apply Rmult_le_pos; lra.
           now left.
         * simpl.
           simpl in IHk.
           unfold rvscale; unfold rvscale in IHk.
           apply Rmult_le_pos; trivial.
           apply Rmult_le_pos; lra.
       + rewrite Rvector_max_abs_nth_Rabs_le.
         intros.
         apply H14.
         specialize (H13 i pf x0).
         lia.
     }
       
   assert (almost prts
             (fun ω =>
                forall (k : nat),
                exists (N : Ts -> nat),
                forall (t : nat),
                  (t >= N ω)%nat ->
                  (rvmaxabs (Xx t) ω) <= (D k ω))).
   {
     apply almost_forall.
     intros.
     specialize (H11 n0).
     destruct H11.
     revert H11.
     apply almost_impl, all_almost; intros ??.
     now exists x.
   }
   revert H12.
   apply almost_impl.
   apply all_almost; intros ??.
   specialize (H10 x).
   apply is_lim_seq_spec.
   apply is_lim_seq_spec in H10.
   intros ?.
   specialize (H10 eps0).
   destruct H10.
   specialize (H12 x0).
   destruct H12.
   exists (x1 x).
   intros.
   specialize (H12 n0).
   cut_to H12; try lia.
   rewrite Rminus_0_r.
   specialize (H10 x0).
   cut_to H10; try lia.
   rewrite Rminus_0_r in H10.
   generalize (Rle_abs (D x0 x)); intros.
   unfold rvmaxabs, Xx in H12.
   rewrite Rabs_right; try lra.
   apply Rle_ge.
   apply rvmaxabs_pos.
   Unshelve.
   apply Rvector_max_abs_nth_le.
  Qed.


  Theorem Tsitsiklis3_beta_pos_Jaakkola_alpha_beta {n}
    (X w α beta : nat -> Ts -> vector R n)
    (β : R) (D0' : Ts -> R) 
(*    (x' : vector R n)  *)
    (XF : nat -> Ts -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa n) beta F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
    {posD0' : forall ω, 0 < D0' ω}
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :


    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf  (α k ω)) -> 
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->



    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A)) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0') ->
    0 < β < 1 ->
    (forall k ω, Rvector_max_abs (XF k ω) <=
                 β * Rvector_max_abs (X k ω)) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->

    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (X n ω)) 0).
 Proof.
   intros beta_prop beta_alpha_prop beta_inf beta_fin.
   intros.
   pose (eps := (1/β-1)/3).
   assert (HH4: exists (D0 : Ts -> R),
              (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0) /\
                (forall ω, 0 < D0 ω)).
   {
     exists D0'.
     split.
     - intros.
       specialize (H4 k).
       revert H4.
       apply almost_impl, all_almost; intros ??.
       apply H4.
     - intros.
       eapply Rlt_le_trans.
       apply (posD0' ω).
       rewrite <- Rplus_0_r at 1.
       lra.
   }
   destruct HH4 as [D0 [HH4 posD0]].
   assert (0 < eps).
   {
     unfold eps.
     assert (1 < 1 / β).
     {
       apply Rmult_lt_reg_r with (r := β); try lra.
       field_simplify; lra.
     }
     lra.
   }
   assert ((1 + 2 * eps) * β < 1).
   {
     unfold eps.
     apply Rplus_lt_reg_r with (x := -1).
     field_simplify; lra.
   }
   pose (D := fix D k :=
                match k with
                | 0%nat => D0
                | S k' => rvscale ((1 + 2 * eps) * β) (D k')
                end).
   assert (Dpos : forall k ω, 0 < D k ω).
   {
     intros.
     induction k.
     - simpl; apply posD0.
     - simpl.
       unfold rvscale.
       apply Rmult_lt_0_compat; try lra.
       apply Rmult_lt_0_compat; try lra.
   }       
   assert (forall ω, is_lim_seq (fun k => D k ω) 0).
   {
     intros.
     apply is_lim_seq_ext with
         (u := fun n => (D0 ω) *  ((1 + 2 * eps) * β)^n).
     - intros.
       induction n0.
       + unfold D.
         rewrite pow_O.
         now rewrite Rmult_1_r.
       + simpl.
         unfold rvscale.
         rewrite <- IHn0.
         ring.
     - replace (Finite 0) with (Rbar_mult (D0 ω) 0) by apply Rbar_mult_0_r.
       apply is_lim_seq_scal_l.
       apply is_lim_seq_geom.
       rewrite Rabs_right; trivial.
       apply Rle_ge.
       apply Rmult_le_pos; lra.
   }
   assert (forall (k : nat),
              exists (N : Ts -> nat),
                almost prts
                       (fun ω =>
                          forall (t : nat),
                            (N ω <= t)%nat ->
                            (rvmaxabs (X t) ω) <= (D k ω))).
   {
     induction k.
     - exists (const 0%nat).
       apply almost_forall in HH4.
       revert HH4.
       apply almost_impl, all_almost; intros ????.
       apply H11.
     - destruct IHk as [N ?].
       assert (forall i pf,
                  exists (N0 : Ts -> nat),
                    almost prts (fun ω =>
                                   forall t : nat, 
                                     (N0 ω <= t)%nat ->
                                     (rvabs (vecrvnth i pf (X t)) ω) <= (D (S k) ω))).
       {
         intros.

         pose (X1 := fun t => vecrvnth i pf (X t)).
         pose (α1 := fun t => vecrvnth i pf (α t)).
         pose (beta1 := fun t => vecrvnth i pf (beta t)).         
         pose (w1 := fun t => vecrvnth i pf (w t)).
         pose (W := fix W t' :=
                    match t' with
                    | 0%nat => const 0
                    | (S t) => 
                      rvplus 
                        (rvmult 
                           (rvminus (const 1) (α1 t))
                           (W t))
                        (rvmult (beta1 t) (w1 t))
                    end).
         pose (WW := fix WW t' t0 :=
                    match t' with
                    | 0%nat => const 0
                    | (S t) => 
                      rvplus 
                        (rvmult 
                           (rvminus (const 1) (α1 (t + t0)%nat))
                           (WW t t0))
                        (rvmult (beta1 (t + t0)%nat) (w1 (t + t0)%nat))
                    end).
       assert (almost prts
                      (fun ω => is_lim_seq (fun n => W n ω) 0)).
       {
         destruct H3 as [A [B ?]].
         destruct H1 as [Ca ?].
         destruct beta_fin as [Cb ?].
         pose (BB := fun (n : nat) =>
                       rvplus (const (Rabs A)) 
                              (rvscale (Rabs B)
                                       (rvmaxlist (fun (j : nat) => rvsqr (rvmaxabs (X j))) n))).
(*
         pose (BB := fun (n:nat) => rvplus (const A) (rvscale (Rabs B) (rvsqr D0))).
*)
         eapply lemma1_alpha_beta with (α := α1) (β := beta1) (w := w1) (W := W) (filt_sub := filt_sub) (B := BB) (Cb := Cb); try easy.
         - simpl.
           typeclasses eauto.
         - intros ?.
           unfold BB; simpl.
           apply rvplus_rv; try typeclasses eauto.
           apply rvscale_rv.
           apply rvmaxlist_rv.
           intros.
           apply rvsqr_rv.
           apply Rvector_max_abs_rv.
           assert (sa_sub (F n1) (F n0)) by 
               now apply is_filtration_le.
           apply (RandomVariable_sa_sub H14).
           clear H12 H13 H14.
           induction n1; trivial.
           rewrite H7.
           apply Rvector_plus_rv.
           + apply Rvector_minus_rv.
             * now apply (RandomVariable_sa_sub (isfilt n1)).
             * apply Rvector_mult_rv.
               -- now apply (RandomVariable_sa_sub (isfilt n1)).
               -- now apply (RandomVariable_sa_sub (isfilt n1)).
           + apply Rvector_mult_rv.
             -- now apply (RandomVariable_sa_sub (isfilt n1)).
             -- apply Rvector_plus_rv; trivial.
         - unfold w1.
           intros ?.
           now apply vecrvnth_rv.
         - unfold α1.
           intros ?.
           now apply vecrvnth_rv.
         - unfold beta1.
           intros ?.
           now apply vecrvnth_rv.
         - intros.
           unfold w1.
           apply iscond.
         - intros.
           unfold w1.
           apply H2.
         - intros.
           unfold w1.
           specialize (H3 n0 i pf).
           revert H3; apply almost_impl.
           apply almost_forall in H4.
           revert H4; apply almost_impl.
           apply all_almost; intros ???.
           unfold rvsqr, vecrvnth.
           eapply Rbar_le_trans.
           apply H4.
           unfold BB.
           rv_unfold.
           simpl.
           lra.
         - intros.
           revert H; apply almost_impl.
           apply all_almost; intros ??.
           apply H.
         - intros.
           revert beta_prop; apply almost_impl.
           apply all_almost; intros ??.
           apply H13.
         - intros.
           revert H; apply almost_impl.
           apply all_almost; intros ??.
           apply H.
         - intros.
           revert beta_prop; apply almost_impl.
           apply all_almost; intros ??.
           apply H13.
         - revert H0; apply almost_impl.
           apply all_almost; intros ??.
           apply H0.
         - revert beta_inf; apply almost_impl.
           apply all_almost; intros ??.
           apply H13.
         - unfold rvsqr, const.
           unfold beta1.
           specialize (H12 i pf).
           revert H12.
           apply almost_impl, all_almost; intros ??.
           apply H12.
         - intros.
           simpl.
           now rv_unfold'.
         - exists (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr D0'))).
           apply almost_forall in H4.
           revert H4.
           apply almost_impl, all_almost; intros ???.
           unfold BB.
           rv_unfold.
           assert (Rabs B * Rsqr (D0' x) = Rabs (B * Rsqr(D0' x))).
           {
             rewrite Rabs_mult.
             f_equal.
             now rewrite <- Rabs_sqr.
           }
           rewrite H13.
           rewrite Rabs_plus.
           apply Rplus_le_compat_l.
           rewrite <- H13.
           apply Rmult_le_compat_l.
           + apply Rabs_pos.
           + unfold rvmaxlist.
             unfold Rmax_list_map.
             apply Rmax_list_le_iff.
             * apply map_not_nil.
               apply seq_not_nil.
               lia.
             * intros.
               apply in_map_iff in H14.
               destruct H14 as [? [? ?]].
               rewrite <- H14.
               specialize (H4 x1).
               simpl in H4.
               apply Rsqr_le_abs_1.
               rewrite Rabs_right.
               -- eapply Rle_trans.
                  ++ apply H4.
                  ++ apply Rle_abs.
               -- apply Rle_ge, rvmaxabs_pos.
       }
       assert (almost prts
                      (fun ω => is_lim_seq (fun n => WW n 0%nat ω) 0)).
       {
         revert H12.
         apply almost_impl, all_almost; unfold impl; intros ?.
         apply is_lim_seq_ext.
         induction n0.
         - now simpl.
         - simpl.
           rv_unfold'.
           rewrite IHn0.
           now replace (n0 + 0)%nat with n0 by lia.
       }
       generalize (lemma2_almost_beta WW α1 beta1 w1); intros.
       cut_to H14; cycle 1; try easy.
         - revert H; apply almost_impl.
           apply all_almost; intros ??.
           intros.
           apply H.
         - revert beta_prop; apply almost_impl.
           apply all_almost; intros ??.
           intros.
           apply H15.
         - intros.
           simpl.
           now rv_unfold'.
         - assert (forall ω, 0 < β * eps * (D k ω)).
           {
             intros.
             apply Rmult_lt_0_compat; try easy.
             apply Rmult_lt_0_compat; lra.
           }
           specialize (H14 (fun ω => mkposreal _ (H15 ω))).
           destruct H14 as [N2 ?].
           pose (tauk := fun ω => max (N ω) (N2 ω)) .
           pose (αtau := fun t ω => α1 (t + tauk ω)%nat ω).
           pose (betatau := fun t ω => beta1 (t + tauk ω)%nat ω).           
           pose (Y := fix Y t' :=
                    match t' with
                    | 0%nat => (D k)
                    | (S t) =>
                      rvplus 
                        (rvmult 
                           (rvminus (const 1) (αtau t))
                           (Y t))
                        (rvmult (betatau t) (rvscale β (D k)))
                    end).
           pose (Xtau := fun t ω => X1 (t + tauk ω)%nat ω).
           pose (wtau := fun t ω => w1 (t + tauk ω)%nat ω).
           pose (Wtau := fun t ω => WW t (tauk ω) ω).
           generalize (lemma8_abs_combined_almost_beta Xtau Y Wtau αtau betatau wtau); intros.
           simpl.
           specialize (H16 (mkposreal _ H8) β (fun ω => mkposreal _ (Dpos k ω))).
           cut_to H16; try easy.
           cut_to H16.
           + destruct H16.
             exists (fun ω => ((tauk ω) + (x ω))%nat).
             revert H16.
             apply almost_impl, all_almost; intros ????.
             unfold Xtau, tauk, X1 in H16.
             specialize (H16 (t - tauk x0)%nat).
             cut_to H16; try lia.
             rv_unfold'_in_hyp H16.
             simpl in H16.
             rv_unfold.
             unfold tauk in H16.
             unfold tauk in H17.
             replace (t - Init.Nat.max (N x0) (N2 x0) + Init.Nat.max (N x0) (N2 x0))%nat with (t) in H16 by lia.
             lra.
           + revert H14.
             apply almost_impl, all_almost; intros ??.
             exists (N2 x).
             intros.
             unfold Wtau.
             specialize (H14 (tauk x) n0).
             apply H14.
             unfold tauk.
             lia.
           + revert H; apply almost_impl.
             apply all_almost; intros ??.
             intros.
             apply H.
           + revert beta_prop; apply almost_impl.
             apply all_almost; intros ??.
             intros.
             apply H17.
           + intros.
             unfold Wtau, αtau, wtau.
             simpl.
             now rv_unfold'.
           + intros.
             simpl.
             rv_unfold.
             lra.
           + intros.
             clear H16 H13 H14 Wtau WW Y.
             revert beta_prop; apply almost_impl.
             revert H11; apply almost_impl, all_almost; intros ???.
             unfold Xtau, X1, vecrvnth, αtau, betatau,  α1, beta1, wtau, w1.
             replace (S t + tauk x)%nat with (S (t + tauk x)) by lia.
             simpl.
             rewrite H7.
             unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult.
             rewrite Rvector_nth_plus.
             rewrite Rvector_nth_plus, Rvector_nth_mult.
             repeat rewrite Rvector_nth_plus.
             rewrite Rvector_nth_scale.
             rewrite Rvector_nth_mult.
             unfold vecrvnth.
             ring_simplify.
             repeat rewrite Rplus_assoc.
             do 2 apply Rplus_le_compat_l.
             assert (vector_nth i pf (XF (t + tauk x)%nat x) <= β * D k x ).
             {
               eapply Rle_trans.
               apply Rle_abs.
               eapply Rle_trans.
               apply Rvector_max_abs_nth_le.
               eapply Rle_trans.
               apply H6.
               apply Rmult_le_compat_l; try lra.
               apply H11.
               unfold tauk; lia.
            }
            apply Rmult_le_compat_l with (r := vector_nth i pf (beta (t + tauk x)%nat x)) in H14; try lra.
            apply H13.
           + intros.
             clear H16 H13 H14 Wtau WW Y.
             revert beta_prop; apply almost_impl.
             revert H11.
             apply almost_impl, all_almost; intros ???.
             unfold Xtau, X1, vecrvnth, αtau, betatau, α1, beta1, wtau, w1.
             replace (S t + tauk x)%nat with (S (t + tauk x)) by lia.
             simpl.
             rewrite H7.
             unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult, vecrvnth.
             rewrite Rvector_nth_plus.
             rewrite Rvector_nth_plus, Rvector_nth_mult.             
             repeat rewrite Rvector_nth_plus.
             rewrite Rvector_nth_scale.
             rewrite Rvector_nth_mult.
             ring_simplify.
             assert (Rabs (vector_nth i pf (XF (t + tauk x)%nat x)) <=  β * D k x).
             {
               eapply Rle_trans.
               apply Rvector_max_abs_nth_le.
               eapply Rle_trans.
               apply H6.
               apply Rmult_le_compat_l; try lra.
               apply H11.
               unfold tauk; lia.
             }
             rewrite Rabs_le_between in H14.
             destruct H14.
             apply Rmult_le_compat_l with (r := vector_nth i pf (beta (t + tauk x)%nat x)) in H14; try lra.               
             apply H13.
           + revert H11.
             apply almost_impl, all_almost; intros ???.
             simpl.
             specialize (H11 (t + tauk x)%nat).
             unfold Xtau, X1.
             cut_to H11; try lia.
             eapply Rle_trans.
             shelve.
             apply H11.
             unfold tauk.
             lia.
           + intros.
             apply Y_limsup_beta_const_almost with (α := αtau) (beta := betatau); try easy.
             * intros.
               apply Rle_ge.
               apply Rmult_le_pos.
               -- left.
                  apply H5.
               -- left.
                  now simpl.
             * revert H; apply almost_impl.
               apply all_almost; intros ???.
               apply H.
             * revert beta_prop; apply almost_impl.
               apply all_almost; intros ???.
               apply H17.
             * revert beta_alpha_prop; apply almost_impl.
               apply all_almost; intros ???.
               apply H17.
             * revert H0; apply almost_impl.
               apply all_almost; intros ??.
               apply (seq_sum_shift (fun t => α1 t x)).
               apply H0.
        }
       apply bounded_nat_ex_choice_vector in H12.
       destruct H12.
       exists (fun ω => list_max (map (fun z => z ω) (proj1_sig x))).
       intros.
       assert (forall i pf ω,
                  (vector_nth i pf x ω <= 
                   list_max (map (fun z => z ω) (` x)))%nat).
       {
         intros.
         generalize (vector_nth_In x _ pf); intros HH.
         generalize (list_max_upper (map (fun z => z ω) (` x))); intros HH2.
         rewrite Forall_forall in HH2.
         apply HH2.
         apply in_map_iff.
         now exists (vector_nth i pf x).
       }
       
       assert (almost prts (fun x0 =>
                             forall i pf t,
                               (t >= vector_nth i pf x x0)%nat ->
                               (rvabs (vecrvnth i pf (X t)) x0) <=
                               (D (S k) x0))).
       {
         apply almost_bounded_forall.
         intros.
         - apply le_dec.
         - intros.
           rewrite (digit_pf_irrel _ _ pf2 pf1).
           apply H14.
           now rewrite (digit_pf_irrel _ _ pf2 pf1) in H15.
         - intros.
           apply H12.
       }
       revert H14.
       apply almost_impl, all_almost; intros ????.
       unfold rvmaxabs.
       unfold rvabs, vecrvnth in H15.
       destruct n.
       + assert (Rvector_max_abs (X t x0) = 0).
         {
           apply Rvector_max_abs_zero.
           rewrite vector0_0.
           apply (vector0_0 (X t x0)).
         }
         rewrite H16.
         clear H11 H12 H13 H14 H15.
         induction k.
         * unfold D.
           unfold rvscale.
           apply Rmult_le_pos; trivial.
           apply Rmult_le_pos; lra.
           now left.
         * simpl.
           simpl in IHk.
           unfold rvscale; unfold rvscale in IHk.
           apply Rmult_le_pos; trivial.
           apply Rmult_le_pos; lra.
       + rewrite Rvector_max_abs_nth_Rabs_le.
         intros.
         apply H14.
         specialize (H13 i pf x0).
         lia.
     }
       
   assert (almost prts
             (fun ω =>
                forall (k : nat),
                exists (N : Ts -> nat),
                forall (t : nat),
                  (t >= N ω)%nat ->
                  (rvmaxabs (X t) ω) <= (D k ω))).
   {
     apply almost_forall.
     intros.
     specialize (H11 n0).
     destruct H11.
     revert H11.
     apply almost_impl, all_almost; intros ??.
     now exists x.
   }
   revert H12.
   apply almost_impl.
   apply all_almost; intros ??.
   specialize (H10 x).
   apply is_lim_seq_spec.
   apply is_lim_seq_spec in H10.
   intros ?.
   specialize (H10 eps0).
   destruct H10.
   specialize (H12 x0).
   destruct H12.
   exists (x1 x).
   intros.
   specialize (H12 n0).
   cut_to H12; try lia.
   rewrite Rminus_0_r.
   specialize (H10 x0).
   cut_to H10; try lia.
   rewrite Rminus_0_r in H10.
   generalize (Rle_abs (D x0 x)); intros.
   unfold rvmaxabs in H12.
   rewrite Rabs_right; try lra.
   apply Rle_ge.
   apply rvmaxabs_pos.
   Unshelve.
   apply Rvector_max_abs_nth_le.
 Qed.

 Theorem Tsitsiklis3_beta_0 {n}
   (X w α : nat -> Ts -> vector R n)
   (β : R) (D0' : Ts -> R)
   (x' : vector R n)
   (XF : nat -> vector R n -> vector R n)
   {F : nat -> SigmaAlgebra Ts}
   (isfilt : IsFiltration F) 
   (filt_sub : forall k, sa_sub (F k) dom) 
   (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
   {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
   {rvXF : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
   {posD0' : forall ω, 0 < D0' ω}
   (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
   {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
   {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A))
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0') ->
    β = 0 ->
    (forall k ω, Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') <=
                 β * Rvector_max_abs (Rvector_minus (X k ω) x')) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (Rvector_minus (X n ω) x')) 0).
  Proof.
    intros.
    pose (Xx := fun n ω => Rvector_minus (X n ω) x').
    assert (forall k ω, XF k (X k ω) = x').
    {
      intros.
      specialize (H6 k ω).
      rewrite H5 in H6.
      rewrite Rmult_0_l in H6.
      generalize (Rvector_max_abs_nonneg (Rvector_minus (XF k (X k ω)) x')); intros.      
      assert (Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') = 0) by lra.
      apply Rvector_max_abs_zero in H9.
      apply (f_equal (fun v => Rvector_plus v x')) in H9.
      unfold Rvector_minus in H9.
      rewrite <- Rvector_plus_assoc in H9.
      rewrite Rvector_inv_plus in H9.
      rewrite Rvector_plus_zero in H9.
      rewrite Rvector_plus_comm in H9.
      now rewrite Rvector_plus_zero in H9.
    }
    assert (forall i pf,
               almost prts (fun ω => is_lim_seq (fun n0 => vector_nth i pf (Xx n0 ω)) 0)). 

    {
      intros.
      pose (X1 := fun t => vecrvnth i pf (Xx t)).
      pose (α1 := fun t => vecrvnth i pf (α t)).
      pose (w1 := fun t => vecrvnth i pf (w t)).
      
      destruct H3 as [A [B ?]].
      destruct H1 as [Ca ?].
      pose (BB := fun (n : nat) =>
                    rvplus (const (Rabs A)) 
                           (rvscale (Rabs B)
                                    (rvmaxlist (fun (j : nat) => rvsqr (rvmaxabs (X j))) n))).
(*
      pose (BB := fun (n:nat) => rvplus (const A) (rvscale (Rabs B) (rvsqr D0))).
*)
      eapply lemma1_alpha_alpha with (α := α1) (w := w1) (W := X1) (filt_sub := filt_sub) (B := BB) (Ca := Ca); try easy.
      - simpl.
        typeclasses eauto.
      - intros ?.
        unfold BB; simpl.
        apply rvplus_rv; try typeclasses eauto.
        apply rvscale_rv.
        apply rvmaxlist_rv.
        intros.
        apply rvsqr_rv.
        apply Rvector_max_abs_rv.
        assert (sa_sub (F n1) (F n0)) by 
            now apply is_filtration_le.
        apply (RandomVariable_sa_sub H10).
        clear H9 H10.
        induction n1; trivial.
        rewrite H7.
        apply Rvector_plus_rv.
        + now apply (RandomVariable_sa_sub (isfilt n1)).
        + apply Rvector_mult_rv.
          * now apply (RandomVariable_sa_sub (isfilt n1)).
          * apply Rvector_plus_rv; trivial.
            apply Rvector_minus_rv.
            ++ apply (RandomVariable_sa_sub (isfilt n1)).
               now apply (compose_rv (dom2 := Rvector_borel_sa n)).
            ++ now apply (RandomVariable_sa_sub (isfilt n1)).
      - unfold w1.
        intros ?.
        now apply vecrvnth_rv.
      - unfold α1.
        intros ?.
        now apply vecrvnth_rv.
      - intros.
        unfold w1.
        apply iscond.
      - intros.
        unfold w1.
        apply H2.
      - intros.
        unfold w1.
        specialize (H3 n0 i pf).
        revert H3; apply almost_impl.
        apply almost_forall in H4.
        revert H4; apply almost_impl.
        apply all_almost; intros ???.
        unfold rvsqr, vecrvnth.
        eapply Rbar_le_trans.
        apply H4.
        unfold BB.
        rv_unfold.
        simpl.
        lra.
      - intros.
        apply H.
      - intros.
        unfold α1.
        specialize (H n0 x i pf).
        unfold vecrvnth.
        lra.
      - apply all_almost.
        intros.
        unfold α1, vecrvnth.
        apply H0.
      - unfold rvsqr, const.
        unfold α1.
        specialize (H1 i pf).
        revert H1.
        apply almost_impl, all_almost; intros ??.
        apply H1.
      - intros.
        unfold X1.
        unfold vecrvnth, Xx.
        rewrite H7.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale.
        unfold α1, w1.
        rewrite Rvector_nth_minus.
        rewrite Rvector_nth_plus, Rvector_nth_mult.
        do 2 rewrite Rvector_nth_plus.
        rewrite Rvector_nth_scale.
        unfold Rvector_minus, Rvector_opp.
        rewrite Rvector_nth_plus, Rvector_nth_scale.
        ring_simplify.
        unfold vecrvnth, Rminus.        
        repeat rewrite Rplus_assoc.
        do 2 f_equal.
        ring_simplify.
        rewrite H8.
        lra.
      - exists (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr D0'))).
        apply almost_forall in H4.
        revert H4.
        apply almost_impl, all_almost; intros ???.
        unfold BB.
        rv_unfold.
        assert (Rabs B * Rsqr (D0' x) = Rabs (B * Rsqr(D0' x))).
        {
          rewrite Rabs_mult.
          f_equal.
          now rewrite <- Rabs_sqr.
        }
        rewrite H9.
        rewrite Rabs_plus.
        apply Rplus_le_compat_l.
        rewrite <- H9.
        apply Rmult_le_compat_l.
        + apply Rabs_pos.
        + unfold rvmaxlist.
          unfold Rmax_list_map.
          apply Rmax_list_le_iff.
          * apply map_not_nil.
            apply seq_not_nil.
            lia.
          * intros.
            apply in_map_iff in H10.
            destruct H10 as [? [? ?]].
            rewrite <- H10.
            specialize (H4 x1).
            simpl in H4.
            apply Rsqr_le_abs_1.
            rewrite Rabs_right.
            -- eapply Rle_trans.
               ++ apply H4.
               ++ apply Rle_abs.
            -- apply Rle_ge, rvmaxabs_pos.
    }
    apply almost_bounded_forall in H9.
    - revert H9.
      apply almost_impl, all_almost; intros ??.
      unfold rvmaxabs.
      assert (forall i pf,
                 is_lim_seq' (fun n1 => vector_nth i pf (Xx n1 x)) 0).
      {
        intros.
        now apply is_lim_seq_spec.
      }
      apply is_lim_seq_spec.
      unfold is_lim_seq' in *.
      intros.
      assert (exists (N:nat),
                 forall n0,
                   (N <= n0)%nat ->
                   forall i pf,
                     Rabs (vector_nth i pf (Xx n0 x)) < eps).
      {
        unfold eventually in H10.
        setoid_rewrite Rminus_0_r in H10.
        generalize (fun i pf => H10 i pf eps); intros.
        apply bounded_nat_ex_choice_vector in H11.
        destruct H11.
        exists (list_max (proj1_sig x0)).
        intros.
        apply H11.
        rewrite <- H12.
        generalize (list_max_upper (` x0)); intros.
        rewrite Forall_forall in H13.
        apply H13.
        apply vector_nth_In.
      }
      destruct H11.
      exists x0.
      intros.
      specialize (H11 n0 H12).
      rewrite Rminus_0_r.
      rewrite Rabs_right.
      + destruct n.
        * rewrite (vector0_0 (Rvector_minus (X n0 x) x')).
          unfold Rvector_max_abs.
          rewrite (vector0_0 (Rvector_abs vector0)).
          unfold vector_fold_left.
          simpl.
          apply cond_pos.
        * destruct (Rvector_max_abs_nth_in (Xx n0 x)) as [? [? ?]].
          unfold Xx in H13.
          rewrite H13.
          apply H11.
      + apply Rle_ge, Rvector_max_abs_nonneg.
    - intros.
      apply lt_dec.
    - intros i pf1 pf2 x.
      apply is_lim_seq_ext.
      intros.
      apply vector_nth_ext.
  Qed.


 Theorem Tsitsiklis3_beta_0_Jaakkola_alpha_beta {n}
   (X w α beta : nat -> Ts -> vector R n)
   (β : R) (D0' : Ts -> R)
(*   (x' : vector R n) *)
   (XF : nat -> Ts -> vector R n)
   {F : nat -> SigmaAlgebra Ts}
   (isfilt : IsFiltration F) 
   (filt_sub : forall k, sa_sub (F k) dom) 
   (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
   (adapt_beta : IsAdapted (Rvector_borel_sa n) beta F)    
   {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
   {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
   {posD0' : forall ω, 0 < D0' ω}
   (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
   {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
   {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf  (α k ω)) -> 
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->



    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->

(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A))
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0') ->
    β = 0 ->
    (forall k ω, Rvector_max_abs (XF k ω) <=
                 β * Rvector_max_abs (X k ω)) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (X n ω)) 0).
  Proof.
    intros betaprop alpha_betaprop beta_inf beta_fin.
    intros.
    assert (forall k ω, XF k ω = @Rvector_zero n).
    {
      intros.
      specialize (H6 k ω).
      rewrite H5 in H6.
      rewrite Rmult_0_l in H6.
      generalize (Rvector_max_abs_nonneg (XF k ω)); intros.      
      assert (Rvector_max_abs (XF k ω) = 0) by lra.
      now apply Rvector_max_abs_zero in H9.
    }
    assert (forall i pf,
               almost prts (fun ω => is_lim_seq (fun n0 => vector_nth i pf (X n0 ω)) 0)). 

    {
      intros.
      pose (X1 := fun t => vecrvnth i pf (X t)).
      pose (α1 := fun t => vecrvnth i pf (α t)).
      pose (beta1 := fun t => vecrvnth i pf (beta t)).      
      pose (w1 := fun t => vecrvnth i pf (w t)).
      
      destruct H3 as [A [B ?]].
      destruct H1 as [Ca ?].
      destruct beta_fin as [Cb beta_fin].
      pose (BB := fun (n : nat) =>
                    rvplus (const (Rabs A)) 
                           (rvscale (Rabs B)
                                    (rvmaxlist (fun (j : nat) => rvsqr (rvmaxabs (X j))) n))).
(*
      pose (BB := fun (n:nat) => rvplus (const A) (rvscale (Rabs B) (rvsqr D0))).
*)
      eapply lemma1_alpha_beta with (α := α1) (β := beta1) (w := w1) (W := X1) (filt_sub := filt_sub) (B := BB) (Cb := Cb); try easy.
      - simpl.
        typeclasses eauto.
      - intros ?.
        unfold BB; simpl.
        apply rvplus_rv; try typeclasses eauto.
        apply rvscale_rv.
        apply rvmaxlist_rv.
        intros.
        apply rvsqr_rv.
        apply Rvector_max_abs_rv.
        assert (sa_sub (F n1) (F n0)) by 
            now apply is_filtration_le.
        apply (RandomVariable_sa_sub H10).
        clear H9 H10.
        induction n1; trivial.
        rewrite H7.
        apply Rvector_plus_rv.
        + apply Rvector_minus_rv.
          * now apply (RandomVariable_sa_sub (isfilt n1)).
          * apply Rvector_mult_rv.
            -- now apply (RandomVariable_sa_sub (isfilt n1)).
            -- now apply (RandomVariable_sa_sub (isfilt n1)).               
        + apply Rvector_mult_rv.
          * now apply (RandomVariable_sa_sub (isfilt n1)).
          * apply Rvector_plus_rv; trivial.
      - unfold w1.
        intros ?.
        now apply vecrvnth_rv.
      - unfold α1.
        intros ?.
        now apply vecrvnth_rv.
      - unfold beta1.
        intros ?.
        now apply vecrvnth_rv.
      - intros.
        unfold w1.
        apply iscond.
      - intros.
        unfold w1.
        apply H2.
      - intros.
        unfold w1.
        specialize (H3 n0 i pf).
        revert H3; apply almost_impl.
        apply almost_forall in H4.
        revert H4; apply almost_impl.
        apply all_almost; intros ???.
        unfold rvsqr, vecrvnth.
        eapply Rbar_le_trans.
        apply H4.
        unfold BB.
        rv_unfold.
        simpl.
        lra.
      - intros.
        revert H; apply almost_impl.
        apply all_almost; intros ??.
        apply H.
      - intros.
        revert betaprop; apply almost_impl.
        apply all_almost; intros ??.
        apply H9.
      - intros.
        revert H; apply almost_impl.
        apply all_almost; intros ??.
        apply H.
      - intros.
        revert betaprop; apply almost_impl.
        apply all_almost; intros ??.
        apply H9.
      - revert H0; apply almost_impl.
        apply all_almost; intros ??.
        apply H0.
      - revert beta_inf; apply almost_impl.
        apply all_almost; intros ??.
        apply H9.
      - unfold rvsqr, const.
        unfold beta1.
        specialize (beta_fin i pf).
        revert beta_fin.
        apply almost_impl, all_almost; intros ??.
        apply H9.
      - intros.
        unfold X1.
        unfold vecrvnth.
        rewrite H7.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale.
        unfold α1, beta1, w1.
        rewrite Rvector_nth_plus, Rvector_nth_mult.
        do 2 rewrite Rvector_nth_plus.
        rewrite Rvector_nth_scale.
        unfold Rvector_minus.
        ring_simplify.
        unfold vecrvnth, Rminus.        
        repeat rewrite Rplus_assoc.
        rewrite Rvector_nth_mult.
        ring_simplify.
        rewrite H8.
        rewrite Rvector_nth_zero.
        rewrite Rmult_0_r.
        lra.
      - exists (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr D0'))).
        apply almost_forall in H4.
        revert H4.
        apply almost_impl, all_almost; intros ???.
        unfold BB.
        rv_unfold.
        assert (Rabs B * Rsqr (D0' x) = Rabs (B * Rsqr(D0' x))).
        {
          rewrite Rabs_mult.
          f_equal.
          now rewrite <- Rabs_sqr.
        }
        rewrite H9.
        rewrite Rabs_plus.
        apply Rplus_le_compat_l.
        rewrite <- H9.
        apply Rmult_le_compat_l.
        + apply Rabs_pos.
        + unfold rvmaxlist.
          unfold Rmax_list_map.
          apply Rmax_list_le_iff.
          * apply map_not_nil.
            apply seq_not_nil.
            lia.
          * intros.
            apply in_map_iff in H10.
            destruct H10 as [? [? ?]].
            rewrite <- H10.
            specialize (H4 x1).
            simpl in H4.
            apply Rsqr_le_abs_1.
            rewrite Rabs_right.
            -- eapply Rle_trans.
               ++ apply H4.
               ++ apply Rle_abs.
            -- apply Rle_ge, rvmaxabs_pos.
    }
    apply almost_bounded_forall in H9.
    - revert H9.
      apply almost_impl, all_almost; intros ??.
      unfold rvmaxabs.
      assert (forall i pf,
                 is_lim_seq' (fun n1 => vector_nth i pf (X n1 x)) 0).
      {
        intros.
        now apply is_lim_seq_spec.
      }
      apply is_lim_seq_spec.
      unfold is_lim_seq' in *.
      intros.
      assert (exists (N:nat),
                 forall n0,
                   (N <= n0)%nat ->
                   forall i pf,
                     Rabs (vector_nth i pf (X n0 x)) < eps).
      {
        unfold eventually in H10.
        setoid_rewrite Rminus_0_r in H10.
        generalize (fun i pf => H10 i pf eps); intros.
        apply bounded_nat_ex_choice_vector in H11.
        destruct H11.
        exists (list_max (proj1_sig x0)).
        intros.
        apply H11.
        rewrite <- H12.
        generalize (list_max_upper (` x0)); intros.
        rewrite Forall_forall in H13.
        apply H13.
        apply vector_nth_In.
      }
      destruct H11.
      exists x0.
      intros.
      specialize (H11 n0 H12).
      rewrite Rminus_0_r.
      rewrite Rabs_right.
      + destruct n.
        * rewrite (vector0_0 (X n0 x)).
          unfold Rvector_max_abs.
          rewrite (vector0_0 (Rvector_abs vector0)).
          unfold vector_fold_left.
          simpl.
          apply cond_pos.
        * destruct (Rvector_max_abs_nth_in (X n0 x)) as [? [? ?]].
          rewrite H13.
          apply H11.
      + apply Rle_ge, Rvector_max_abs_nonneg.
    - intros.
      apply lt_dec.
    - intros i pf1 pf2 x.
      apply is_lim_seq_ext.
      intros.
      apply vector_nth_ext.
  Qed.

  Theorem Tsitsiklis3_max_abs {n} 
    (X w α : nat -> Ts -> vector R n) 
    (β : R) (D0 : Ts -> R)  
    (x' : vector R n)
    (XF : nat -> vector R n -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (*
      {rvD0 : RandomVariable (F 0%nat) borel_sa D0}        
     *)
    {XF_rv : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
    {posD0 : forall ω, 0 < D0 ω}
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :
    
    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
    (*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    
    (exists (C : R),
      forall i pf,
        almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A)) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') <=
                 β * Rvector_max_abs (Rvector_minus (X k ω) x')) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (Rvector_minus (X n ω) x')) 0).
  Proof.
    intros.
    destruct (Rlt_dec 0 β).
    - now apply (@Tsitsiklis3_beta_pos
                   _
                   _
                   w α β D0 _ XF _ _
                   filt_sub
                   _ _ _
                   posD0
                   _
                   rvw).
    - assert (β = 0) by lra.
      now apply (@Tsitsiklis3_beta_0 _ _
                   w α β D0 _ XF _ _
                   filt_sub
                   _ _ _
                   posD0
                   _
                   rvw).
  Qed.


  Theorem Tsitsiklis3_max_abs_Jaakkola_alpha_beta {n} 
    (X w α beta : nat -> Ts -> vector R n) 
    (β : R) (D0 : Ts -> R)  
(*    (x' : vector R n) *)
    (XF : nat -> Ts -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa n) beta F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (*
      {rvD0 : RandomVariable (F 0%nat) borel_sa D0}        
     *)
    {XF_rv : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
    {posD0 : forall ω, 0 < D0 ω}
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf  (α k ω)) -> 
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->

    (*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    
    (exists (C : R),
      forall i pf,
        almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A)) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (XF k ω) <=
                 β * Rvector_max_abs (X k ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (X n ω)) 0).
  Proof.
    intros.
    destruct (Rlt_dec 0 β).
    - now apply (@Tsitsiklis3_beta_pos_Jaakkola_alpha_beta _
                   X w α beta β D0 XF _ _ filt_sub _ _ _ _ posD0 _ rvw).
    - assert (β = 0) by lra.
      now apply (@Tsitsiklis3_beta_0_Jaakkola_alpha_beta _ X w α beta β D0 XF _ _ filt_sub
                   _ _ _ _ posD0 _ rvw).
  Qed.

  Theorem Tsitsiklis3 {n} 
    (X w α : nat -> Ts -> vector R n) 
    (β : R) (D0 : Ts -> R)  
    (x' : vector R n)
    (XF : nat -> vector R n -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (*
      {rvD0 : RandomVariable (F 0%nat) borel_sa D0}        
     *)
    {XF_rv : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
    {posD0 : forall ω, 0 < D0 ω}
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :
    
    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
    (*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    
    (exists (C : R),
      forall i pf,
        almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A)) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') <=
                 β * Rvector_max_abs (Rvector_minus (X k ω) x')) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) (vector_nth i pf x')).
  Proof.
    intros.
    generalize (Tsitsiklis3_max_abs X w α β D0 x' XF _ filt_sub); intros.
    specialize (H8 _ _ _ posD0 _ _ iscond).
    cut_to H8; try easy.
    revert H8; apply almost_impl, all_almost; intros ????.
    now apply lim_seq_maxabs.
  Qed.

  Theorem Tsitsiklis3_Jaakkola_alpha_beta {n} 
    (X w α beta : nat -> Ts -> vector R n) 
    (β : R) (D0 : Ts -> R)  
(*    (x' : vector R n) *)
    (XF : nat -> Ts -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa n) beta F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (*
      {rvD0 : RandomVariable (F 0%nat) borel_sa D0}        
     *)
    {XF_rv : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
    {posD0 : forall ω, 0 < D0 ω}
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :
    
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf  (α k ω)) -> 
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->

    (*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    
    (exists (C : R),
      forall i pf,
        almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const (Rabs A)) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (XF k ω) <=
                   β * Rvector_max_abs (X k ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
  Proof.
    intros.
    generalize (Tsitsiklis3_max_abs_Jaakkola_alpha_beta X w α beta β D0 XF _ filt_sub); intros.
    specialize (H12 _ _ _ _ posD0 _ _ iscond).
    cut_to H12; try easy.
    cut_to H12; try easy.    
    revert H12; apply almost_impl, all_almost; intros ????.
    now apply lim_seq_maxabs0.
  Qed.

  Theorem Tsitsiklis_1_3_max_abs {n} 
    (β : R) 
    (X w α : nat -> Ts -> vector R n)
    (x' : vector R n)
    (XF : nat -> vector R n -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvXF : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') <=
                 β * Rvector_max_abs (Rvector_minus (X k ω) x')) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (Rvector_minus (X n ω) x')) 0).
  Proof.
    intros.
    destruct n; try lia.
    generalize (Tsitsiklis1 β X w α XF isfilt filt_sub 
                            adapt_alpha); intros Tsit1.
    specialize (Tsit1 adapt_w _ _ iscond H H0 H1 H2 H3 H4).
    assert (exists D : nonnegreal,
          forall k ω,
          Rvector_max_abs (XF k (X k ω)) <= β * Rvector_max_abs (X k ω) + D).
    {
      assert (0 <= (β + 1)*Rvector_max_abs x').
      {
        apply Rmult_le_pos; try lra.
        apply Rvector_max_abs_nonneg.
      }
      exists (mknonnegreal _ H7).
      intros.
      generalize (Rvector_max_abs_triang_inv (XF k (X k ω)) x'); intros.
      generalize (Rle_trans _ _ _ H8 (H5 k ω)); intros.
      simpl.
      unfold Rvector_minus in H9.
      generalize (Rvector_max_abs_triang (X k ω) (Rvector_opp x')); intros.
      apply Rmult_le_compat_l with (r := β) in H10; try lra.
      rewrite Rmult_plus_distr_l, Rvector_max_abs_opp in H10.
      lra.
    }
    specialize (Tsit1 H7 H6).
    destruct Tsit1 as [D0 Tsit1].
    pose (D0' := rvplus (const 1) (rvabs D0)).
    generalize (Tsitsiklis3_max_abs X w α β D0' x' XF isfilt filt_sub); intros Tsit3.
    specialize (Tsit3 adapt_alpha _ _).
    assert  (forall ω : Ts, 0 < D0' ω).
    {
      unfold D0'.
      intros.
      rv_unfold.
      generalize (Rabs_pos (D0 ω)); intros.
      lra.
    }
    specialize (Tsit3 H8 _ _ iscond H H0 H1 H2).
    apply Tsit3; try easy.
    - destruct H3 as [A [B [? [? ?]]]].
      exists A; exists B.
      intros.
      specialize (H10 k i pf).
      revert H10.
      apply almost_impl, all_almost; intros ??.
      rewrite Rabs_right; try lra.
      rewrite Rabs_right; try lra.
      apply H10.
    - intros.
      specialize (Tsit1 k).
      revert Tsit1.
      apply almost_impl, all_almost; intros ??.
      eapply Rle_trans.
      + apply H9.
      + unfold D0'.
        rv_unfold.
        generalize (Rle_abs (D0 x)); intros.
        lra.
  Qed.


  Theorem Tsitsiklis_1_3_max_abs_Jaakkola_alpha_beta {n} 
    (β : R) 
    (X w α beta : nat -> Ts -> vector R n)
(*    (x' : vector R n) *)
    (XF : nat -> Ts -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa n) beta F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf (α k ω)) ->        
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (XF k ω) <=
                 β * Rvector_max_abs (X k ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rvector_max_abs (X n ω)) 0).
  Proof.
    intros betaprop alpha_betaprop beta_inf beta_fin.
    intros.
    destruct n; try lia.
    generalize (Tsitsiklis1_Jaakkola_beta β X w α beta XF isfilt filt_sub
                            adapt_alpha adapt_beta); intros Tsit1.
    specialize (Tsit1 adapt_w _ _ iscond H betaprop alpha_betaprop).
    specialize (Tsit1 beta_inf beta_fin H0 H1 H2 H3 H4).
    assert (exists D : nonnegreal,
          forall k ω,
          Rvector_max_abs (XF k ω) <= β * Rvector_max_abs (X k ω) + D).
    {
      assert (0 <= 0) by lra.
      exists (mknonnegreal _ H7).
      intros.
      simpl.
      rewrite Rplus_0_r.
      apply H5.
    }
    assert (HH7: exists D : nonnegreal,
             almost prts
               (fun ω : Ts =>
                forall k : nat,
                Rvector_max_abs (XF k ω) <= β * Rvector_max_abs (X k ω) + D)).
    {
      destruct H7.
      exists x.
      apply all_almost; intros ?.
      intros.
      apply H7.
    }
    specialize (Tsit1 HH7 H6).
    destruct Tsit1 as [D0 Tsit1].
    pose (D0' := rvplus (const 1) (rvabs D0)).
    generalize (Tsitsiklis3_max_abs_Jaakkola_alpha_beta X w α beta β D0' XF isfilt filt_sub); intros Tsit3.
    specialize (Tsit3 adapt_alpha adapt_beta _ _).
    assert  (forall ω : Ts, 0 < D0' ω).
    {
      unfold D0'.
      intros.
      rv_unfold.
      generalize (Rabs_pos (D0 ω)); intros.
      lra.
    }
    specialize (Tsit3 H8 _ _ iscond betaprop alpha_betaprop beta_inf beta_fin H H0 H1 H2).
    apply Tsit3; try easy.
    - destruct H3 as [A [B [? [? ?]]]].
      exists A; exists B.
      intros.
      specialize (H10 k i pf).
      revert H10.
      apply almost_impl, all_almost; intros ??.
      rewrite Rabs_right; try lra.
      rewrite Rabs_right; try lra.
      apply H10.
    - intros.
      specialize (Tsit1 k).
      revert Tsit1.
      apply almost_impl, all_almost; intros ??.
      eapply Rle_trans.
      + apply H9.
      + unfold D0'.
        rv_unfold.
        generalize (Rle_abs (D0 x)); intros.
        lra.
  Qed.

    Theorem Tsitsiklis_1_3 {n} 
    (β : R) 
    (X w α : nat -> Ts -> vector R n)
    (x' : vector R n)
    (XF : nat -> vector R n -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvXF : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') <=
                 β * Rvector_max_abs (Rvector_minus (X k ω) x')) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) (vector_nth i pf x')).
  Proof.
    intros.
    generalize (Tsitsiklis_1_3_max_abs β X w α x' XF _ filt_sub); intros.
    specialize (H7 _ _  npos _ _ _ ).
    cut_to H7; try easy.
    revert H7; apply almost_impl, all_almost; intros ????.
    now apply lim_seq_maxabs.
  Qed.
      
    Theorem Tsitsiklis_1_3_eventually {n} 
    (β : R) 
    (X w α : nat -> Ts -> vector R n)
    (x' : vector R n)
    (XF : nat -> vector R n -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvXF : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :
     
      (forall k ω i pf, 0 <= vector_nth i pf (α k ω)) ->
    (eventually (fun k => forall ω i pf, 0 <= vector_nth i pf (α k ω) <= 1)) ->      
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                           (rvscale B (rvsqr (rvmaxabs (X k)))))) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (Rvector_minus (XF k (X k ω)) x') <=
                 β * Rvector_max_abs (Rvector_minus (X k ω) x')) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) (vector_nth i pf x')).
  Proof.
    intros.
    destruct H0.
    pose (X' := fun n ω => X (n + x)%nat ω).
    pose (F' := fun n => F (n + x)%nat).
    assert (RandomVariable (F' 0%nat) (Rvector_borel_sa n) (X' 0%nat)).
    {
      unfold F', X'.
      replace (0 + x)%nat with x by lia.
      clear H0 H4 X' F'.
      induction x.
      - apply rvX0.
      - rewrite H7.
        apply Rvector_plus_rv.
        + now apply (RandomVariable_sa_sub (isfilt x)).
        + apply Rvector_mult_rv.
          * now apply (RandomVariable_sa_sub (isfilt x)).
          * apply Rvector_plus_rv.
            -- apply Rvector_minus_rv.
               ++ apply (RandomVariable_sa_sub (isfilt x)).
                  apply (@compose_rv) with (dom2 := (Rvector_borel_sa n)); trivial.
               ++ now apply (RandomVariable_sa_sub (isfilt x)).
            -- apply adapt_w.
     }
    pose (w' := fun n ω => w (n + x)%nat ω).
    pose (α' := fun n ω => α (n + x)%nat ω).    
    pose (XF' := fun n ω => XF (n + x)%nat ω).    
    assert (filt_sub': forall k, sa_sub (F' k) dom).
    {
      intros.
      apply filt_sub.
    }
    assert (isfilt': IsFiltration F').
    {
      intros ?.
      apply isfilt.
    }
    generalize (Tsitsiklis_1_3 β X' w' α' x' XF' _ filt_sub'); intros.
    assert (IsAdapted (Rvector_borel_sa n) α' F').
    {
      intros ?.
      apply adapt_alpha.
    }
    assert (IsAdapted  (Rvector_borel_sa n) w' (fun k : nat => F' (S k))).
    {
      intros ?.
      apply adapt_w.
    }
    assert (forall k : nat, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF' k)).
    {
      intros.
      apply rvXF.
    }
    specialize (H9 _ _  npos _ _ _).
    cut_to H9; try easy.
    - revert H9.
      apply almost_impl; apply all_almost.
      intros ??.
      intros.
      specialize (H9 i pf).
      unfold X' in H9.
      now rewrite is_lim_seq_incr_n with (N := x).
    - intros.
      specialize (iscond (k + x)%nat i pf).
      unfold w', F'.
      revert iscond.
      apply is_conditional_expectation_proper; try easy.
      apply (almostR2_prob_space_sa_sub_lift prts (filt_sub (k + x)%nat)).
      apply Condexp_sa_proper.
      reflexivity.
    - intros.
      unfold α'.
      apply H0.
      lia.
    - intros.
      specialize (H1 i pf ω).
      unfold α'.
      now apply (seq_sum_shift (fun k : nat => vector_nth i pf (α k ω)) x).
    - destruct H2 as [C H2].
      exists C.
      intros.
      specialize (H2 i pf).
      revert H2.
      apply almost_impl; apply all_almost.
      intros ??.
      unfold α'.
      destruct x.
      + rewrite Lim_seq_ext with (v := (sum_n (fun k : nat => (vector_nth i pf (α k x0))²))); trivial.
        intros.
        apply sum_n_ext.
        intros.
        now replace (n1 + 0)%nat with n1 by lia.
      + pose (aa := (fun k : nat => (vector_nth i pf (α k x0))²)).
        rewrite Lim_seq_ext with (v := fun a => sum_n aa (a + S x) - sum_n aa x).
        * rewrite Lim_seq_minus.
          -- rewrite Lim_seq_const.
             rewrite Lim_seq_incr_n.
             eapply Rbar_le_trans; cycle 1.
             apply H2.
             unfold Rbar_minus.
             rewrite <- Rbar_plus_0_r.
             apply Rbar_plus_le_compat.
             ++ apply Rbar_le_refl.
             ++ rewrite <- Rbar_opp_le_contravar.
                rewrite Rbar_opp_involutive.
                rewrite Rbar_opp0.
                simpl.
                apply sum_n_nneg.
                intros.
                apply Rle_0_sqr.
          -- apply ex_lim_seq_incr.
             intros.
             replace (S n0 + S x)%nat with (S (n0 + S x)) by lia.
             rewrite sum_Sn.
             unfold plus; simpl.
             assert (0 <= aa (S (n0 + S x))).
             {
               unfold aa.
               apply Rle_0_sqr.
             }
             lra.
          -- apply ex_lim_seq_const.
          -- rewrite Lim_seq_const.
             apply ex_Rbar_minus_Finite_r.
        * intros.
          now rewrite sum_shift_diff.
    - intros.
      specialize (H3 (k + x)%nat i pf).
      assert (almostR2 prts eq
                (ConditionalExpectation prts (filt_sub' k) (vecrvnth i pf (w' k)))
                (ConditionalExpectation prts (filt_sub (k + x)%nat) (vecrvnth i pf (w (k + x)%nat)))).
      {
        apply (almostR2_prob_space_sa_sub_lift prts (filt_sub' k)).
        apply Condexp_sa_proper.
        reflexivity.
      }
      revert H13; apply almost_impl.
      revert H3; apply almost_impl.
      apply all_almost; intros ???.
      rewrite H13.
      now rewrite H3.
    - destruct H4 as [A [B [? [? ?]]]].
      exists A.
      exists B.
      split; trivial.
      split; trivial.
      intros.
      specialize (H14 (k + x)%nat i pf).
      revert H14.
      assert (almostR2 prts eq
                (ConditionalExpectation prts (filt_sub' k) (rvsqr (vecrvnth i pf (w' k))))
                (ConditionalExpectation prts (filt_sub (k + x)%nat) (rvsqr (vecrvnth i pf (w (k + x)%nat))))).
      {
        apply (almostR2_prob_space_sa_sub_lift prts (filt_sub' k)).
        apply Condexp_sa_proper.
        reflexivity.
      }
      apply almost_impl.
      revert H14.
      apply almost_impl; apply all_almost.
      intros ???.
      rewrite H14.
      eapply Rbar_le_trans.
      apply H15.
      unfold rvplus, const, rvscale, rvsqr, rvmaxabs, rvmaxlist.
      simpl.
      apply Rplus_le_compat_l.
      apply Rmult_le_compat_l; try lra.
      unfold X'.
      unfold Rmax_list_map.
      apply Rmax_list_ge with (x := (Rvector_max_abs (X (k + x)%nat x0))²); try lra.
      apply in_map_iff.
      exists k.
      split; trivial.
      destruct k.
      + simpl; lia.
      + apply in_cons.
        apply in_seq.
        lia.
    - intros.
      apply H6.
    - intros.
      unfold X'.
      replace (S k + x)%nat with (S (k + x)) by lia.
      now rewrite H7.
 Qed.

    Theorem Tsitsiklis_1_3_Jaakkola_alpha_beta {n} 
    (β : R) 
    (X w α beta : nat -> Ts -> vector R n)
(*    (x' : vector R n) *)
    (XF : nat -> Ts -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa n) beta F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

   almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (beta k ω) <= vector_nth i pf (α k ω)) ->        
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->

(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (XF k ω) <=
                 β * Rvector_max_abs (X k ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
  Proof.
    intros betaprop alpha_betaprop beta_inf beta_fin.
    intros.
    generalize (Tsitsiklis_1_3_max_abs_Jaakkola_alpha_beta β X w α beta XF _ filt_sub _ _ npos); intros Tsit13.
    specialize (Tsit13 adapt_w _ _ iscond betaprop alpha_betaprop beta_inf beta_fin H H0 H1 H2).
    cut_to Tsit13; try easy.
    revert Tsit13; apply almost_impl, all_almost; intros ????.
    now apply lim_seq_maxabs0.
  Qed.

  Theorem Tsitsiklis_1_3_Jaakkola_alpha_beta_eventually_almost {n} 
    (β : R) 
    (X w α beta : nat -> Ts -> vector R n)
(*    (x' : vector R n) *)
    (XF : nat -> Ts -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa n) beta F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (beta k ω)) ->
    (eventually (fun k => almost prts (fun ω => forall i pf, vector_nth i pf (beta k ω) <= 1))) ->      
    almost prts (fun ω => forall k i pf, 
                     vector_nth i pf (beta k ω) <=  vector_nth i pf (α k ω)) ->        
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (beta k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (beta k ω))))) (Finite C))) ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    (eventually (fun k => almost prts (fun ω => forall i pf,
                                           vector_nth i pf (α k ω) <= 1 ))) ->          
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                      (rvscale B (rvsqr (rvmaxabs (X k)))))) ->
    0 <= β < 1 ->
    (forall k ω, Rvector_max_abs (XF k ω) <=
                 β * Rvector_max_abs (X k ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (beta k) (vecrvplus (XF k) (w k))))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
   Proof.
    intros betapos betaprop alpha_betaprop beta_inf beta_fin.
    intros.
    destruct betaprop.
    destruct H0.
    pose (xx := max x x0).
    pose (X' := fun n ω => X (n + xx)%nat ω).
    pose (F' := fun n => F (n + xx)%nat).
    assert (RandomVariable (F' 0%nat) (Rvector_borel_sa n) (X' 0%nat)).
    {
      unfold F', X'.
      replace (0 + xx)%nat with xx by lia.
      clear H0 H4 X' F'.
      induction xx.
      - apply rvX0.
      - rewrite H7.
        apply Rvector_plus_rv.
        + apply Rvector_minus_rv.
          * now apply (RandomVariable_sa_sub (isfilt xx)).
          * apply Rvector_mult_rv.
            -- now apply (RandomVariable_sa_sub (isfilt xx)).
            -- now apply (RandomVariable_sa_sub (isfilt xx)).
        + apply Rvector_mult_rv.
          * now apply (RandomVariable_sa_sub (isfilt xx)).
          * apply Rvector_plus_rv.
            -- apply rvXF.
            -- apply adapt_w.   
     }
    pose (w' := fun n ω => w (n + xx)%nat ω).
    pose (α' := fun n ω => α (n + xx)%nat ω).
    pose (beta' := fun n ω => beta (n + xx)%nat ω).        
    pose (XF' := fun n ω => XF (n + xx)%nat ω).    
    assert (filt_sub': forall k, sa_sub (F' k) dom).
    {
      intros.
      apply filt_sub.
    }
    assert (isfilt': IsFiltration F').
    {
      intros ?.
      apply isfilt.
    }
    generalize (Tsitsiklis_1_3_Jaakkola_alpha_beta β X' w' α' beta' XF' _ filt_sub'); intros.
    assert (IsAdapted (Rvector_borel_sa n) α' F').
    {
      intros ?.
      apply adapt_alpha.
    }
    assert (IsAdapted (Rvector_borel_sa n) beta' F').
    {
      intros ?.
      apply adapt_beta.
    }
    assert (IsAdapted  (Rvector_borel_sa n) w' (fun k : nat => F' (S k))).
    {
      intros ?.
      apply adapt_w.
    }
    specialize (H10 _ _ _ npos _ _ _ ).
    cut_to H10; try easy.
    cut_to H10; try easy.    
    - revert H10.
      apply almost_impl; apply all_almost.
      intros ??.
      intros.
      specialize (H10 i pf).
      unfold X' in H10.
      now rewrite is_lim_seq_incr_n with (N := xx).
    - intros.
      apply H6.
    - intros.
      unfold X'.
      replace (S k + xx)%nat with (S (k + xx)) by lia.
      rewrite H7.
      reflexivity.
    - intros.
      specialize (iscond (k + xx)%nat i pf).
      unfold w', F'.
      revert iscond.
      apply is_conditional_expectation_proper; try easy.
      apply (almostR2_prob_space_sa_sub_lift prts (filt_sub (k + xx)%nat)).
      apply Condexp_sa_proper.
      reflexivity.
    - intros.
      apply almost_bounded_forall in H8.
      + revert H8; apply almost_impl.
        revert betapos; apply almost_impl.
        apply all_almost; intros ??????.
        split.
        * apply H8.
        * apply H14.
          lia.
      + intros.
        apply le_dec.
      + intros.
        apply H14.
    - revert alpha_betaprop; apply almost_impl.
      apply all_almost; intros ?????.
      apply H14.
    - revert beta_inf; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      now apply (seq_sum_shift (fun k : nat => vector_nth i pf (beta k x1)) xx).
    - destruct beta_fin as [C beta_fin].
      exists C.
      intros.
      specialize (beta_fin i pf).
      revert beta_fin; apply almost_impl.
      apply all_almost; intros ??.
      unfold beta'.
      destruct xx.
      + rewrite Lim_seq_ext with (v := (sum_n (fun k : nat => (vector_nth i pf (beta k x1))²))); trivial.
        intros.
        apply sum_n_ext.
        intros.
        now replace (n1 + 0)%nat with n1 by lia.
      + pose (bb := (fun k : nat => (vector_nth i pf (beta k x1))²)).
        rewrite Lim_seq_ext with (v := fun a => sum_n bb (a + S xx) - sum_n bb xx).
        * rewrite Lim_seq_minus.
          -- rewrite Lim_seq_const.
             rewrite Lim_seq_incr_n.
             eapply Rbar_le_trans; cycle 1.
             apply H14.
             unfold Rbar_minus.
             rewrite <- Rbar_plus_0_r.
             apply Rbar_plus_le_compat.
             ++ apply Rbar_le_refl.
             ++ rewrite <- Rbar_opp_le_contravar.
                rewrite Rbar_opp_involutive.
                rewrite Rbar_opp0.
                simpl.
                apply sum_n_nneg.
                intros.
                apply Rle_0_sqr.
          -- apply ex_lim_seq_incr.
             intros.
             replace (S n0 + S xx)%nat with (S (n0 + S xx)) by lia.
             rewrite sum_Sn.
             unfold plus; simpl.
             assert (0 <= bb (S (n0 + S xx))).
             {
               apply Rle_0_sqr.
             }
             lra.
          -- apply ex_lim_seq_const.
          -- rewrite Lim_seq_const.
             apply ex_Rbar_minus_Finite_r.
        * intros.
          now rewrite sum_shift_diff.
    - intros.
      apply almost_bounded_forall in H0.
      + revert H0; apply almost_impl.
        revert H; apply almost_impl.
        apply all_almost; intros ??????.
        split.
        * apply H.
        * apply H0.
          lia.
      + intros.
        apply le_dec.
      + intros.
        apply H14.
    - revert H1; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      now apply (seq_sum_shift (fun k : nat => vector_nth i pf (α k x1)) xx).
    - destruct H2 as [C H2].
      exists C.
      intros.
      specialize (H2 i pf).
      revert H2.
      apply almost_impl; apply all_almost.
      intros ??.
      unfold α'.
      destruct xx.
      + rewrite Lim_seq_ext with (v := (sum_n (fun k : nat => (vector_nth i pf (α k x1))²))); trivial.
        intros.
        apply sum_n_ext.
        intros.
        now replace (n1 + 0)%nat with n1 by lia.
      + pose (bb := (fun k : nat => (vector_nth i pf (α k x1))²)).
        rewrite Lim_seq_ext with (v := fun a => sum_n bb (a + S xx) - sum_n bb xx).
        * rewrite Lim_seq_minus.
          -- rewrite Lim_seq_const.
             rewrite Lim_seq_incr_n.
             eapply Rbar_le_trans; cycle 1.
             apply H2.
             unfold Rbar_minus.
             rewrite <- Rbar_plus_0_r.
             apply Rbar_plus_le_compat.
             ++ apply Rbar_le_refl.
             ++ rewrite <- Rbar_opp_le_contravar.
                rewrite Rbar_opp_involutive.
                rewrite Rbar_opp0.
                simpl.
                apply sum_n_nneg.
                intros.
                apply Rle_0_sqr.
          -- apply ex_lim_seq_incr.
             intros.
             replace (S n0 + S xx)%nat with (S (n0 + S xx)) by lia.
             rewrite sum_Sn.
             unfold plus; simpl.
             assert (0 <= bb (S (n0 + S xx))).
             {
               apply Rle_0_sqr.
             }
             lra.
          -- apply ex_lim_seq_const.
          -- rewrite Lim_seq_const.
             apply ex_Rbar_minus_Finite_r.
        * intros.
          now rewrite sum_shift_diff.
    - intros.
      specialize (H3 (k + xx)%nat i pf).
      assert (almostR2 prts eq
                (ConditionalExpectation prts (filt_sub' k) (vecrvnth i pf (w' k)))
                (ConditionalExpectation prts (filt_sub (k + xx)%nat) (vecrvnth i pf (w (k + xx)%nat)))).
      {
        apply (almostR2_prob_space_sa_sub_lift prts (filt_sub' k)).
        apply Condexp_sa_proper.
        reflexivity.
      }
      revert H14; apply almost_impl.
      revert H3; apply almost_impl.
      apply all_almost; intros ???.
      rewrite H14.
      now rewrite H3.
    - destruct H4 as [A [B [? [? ?]]]].
      exists A.
      exists B.
      split; trivial.
      split; trivial.
      intros.
      specialize (H15 (k + xx)%nat i pf).
      revert H15.
      assert (almostR2 prts eq
                (ConditionalExpectation prts (filt_sub' k) (rvsqr (vecrvnth i pf (w' k))))
                (ConditionalExpectation prts (filt_sub (k + xx)%nat) (rvsqr (vecrvnth i pf (w (k + xx)%nat))))).
      {
        apply (almostR2_prob_space_sa_sub_lift prts (filt_sub' k)).
        apply Condexp_sa_proper.
        reflexivity.
      }
      apply almost_impl.
      revert H15.
      apply almost_impl; apply all_almost.
      intros ???.
      rewrite H15.
      eapply Rbar_le_trans.
      apply H16.
      unfold rvplus, const, rvscale, rvsqr, rvmaxabs, rvmaxlist.
      simpl.
      apply Rplus_le_compat_l.
      apply Rmult_le_compat_l; try lra.
      unfold X'.
      unfold Rmax_list_map.
      apply Rmax_list_ge with (x := (Rvector_max_abs (X (k + xx)%nat x1))²); try lra.
      apply in_map_iff.
      exists k.
      split; trivial.
      destruct k.
      + simpl; lia.
      + apply in_cons.
        apply in_seq.
        lia.
  Qed.     

    Theorem Tsitsiklis_1_3_orig {n} 
    (β : R) 
    (X w α : nat -> Ts -> vector R n)
    (x' : vector R n)
    (XF : nat -> vector R n -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
    {rvXF : forall k, RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) (XF k)}
    {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
    {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                           (rvscale B (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (forall k x, Rvector_max_abs (Rvector_minus (XF k x) x') <=
                 β * Rvector_max_abs (Rvector_minus x x')) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF k (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) (vector_nth i pf x')).
    Proof.
      intros.
      now apply (Tsitsiklis_1_3  β X w α x' XF isfilt filt_sub adapt_alpha) with (rvw := rvw).
    Qed.

 Program Global Instance fin_image_frf {A B} {fin:FiniteType B} (f:A->B) : FiniteRangeFunction f
   := {|
     frf_vals := fin_elms
   |}.
 Next Obligation.
   apply fin_finite.
 Qed.

End Stochastic_convergence.

  Instance rvs_Rmin_list {Ts} {dom2 : SigmaAlgebra Ts} (rvs : list (Ts -> R))
                          {rv_rvs : List.Forall (RandomVariable dom2 borel_sa) rvs} :
    RandomVariable dom2 borel_sa (fun ω : Ts => Rmin_list (map (fun x => x ω) rvs)).
  Proof.
    induction rvs.
    - apply rvconst.
    - invcs rv_rvs.
      cut_to IHrvs; trivial.
      destruct rvs; trivial.
      simpl.
      apply rvmin_rv; trivial.
  Qed.

  Instance rvs_Rmax_list {Ts} {dom2 : SigmaAlgebra Ts} (rvs : list (Ts -> R))
                          {rv_rvs : List.Forall (RandomVariable dom2 borel_sa) rvs} :
    RandomVariable dom2 borel_sa (fun ω : Ts => Rmax_list (map (fun x => x ω) rvs)).
  Proof.
    induction rvs.
    - apply rvconst.
    - invcs rv_rvs.
      cut_to IHrvs; trivial.
      destruct rvs; trivial.
      simpl.
      apply rvmax_rv; trivial.
  Qed.

  Instance rvs_Rmin_list' {A Ts} {dom2 : SigmaAlgebra Ts} (rvs : list A) g
                          {rv_rvs : List.Forall (fun x => RandomVariable dom2 borel_sa (g x)) rvs} :
    RandomVariable dom2 borel_sa (fun ω : Ts => Rmin_list (map (fun x => g x ω) rvs)).
  Proof.
    induction rvs.
    - apply rvconst.
    - invcs rv_rvs.
      cut_to IHrvs; trivial.
      destruct rvs; trivial.
      simpl.
      apply rvmin_rv; trivial.
  Qed.

  Instance rvs_Rmax_list' {A} {Ts} {dom2 : SigmaAlgebra Ts} (rvs : list A) g
                          {rv_rvs : List.Forall (fun x => RandomVariable dom2 borel_sa (g x)) rvs} :
    RandomVariable dom2 borel_sa (fun ω : Ts => Rmax_list (map (fun x => g x ω) rvs)).
  Proof.
    induction rvs.
    - apply rvconst.
    - invcs rv_rvs.
      cut_to IHrvs; trivial.
      destruct rvs; trivial.
      simpl.
      apply rvmax_rv; trivial.
  Qed.

(*
Require Bellman.
*)
Section MDP.

  Context {M : MDP}  (γ : R).
  Arguments t {_}.

  
  Definition Ts := {x : state M & act M x} .
  Definition Td := Rfct Ts.

(*
  Definition bellmanQbar_alt (ec : Rfct (sigT M.(act))) : Rfct (sigT M.(act)) -> Rfct (sigT M.(act))
  := fun W => fun (sa : sigT M.(act))  => let (s,a) := sa in
                  ec sa +
                  γ*expt_value (t s a)(fun s' => Max_{act_list s'}(fun a => W (existT _ s' a) ) ).

  Lemma bellmanQbar_alt_contraction (ec : Rfct (sigT M.(act))) :
    0 <= γ < 1 ->
    forall (X1 X2 : Rfct(sigT M.(act))),
      Hierarchy.norm (Hierarchy.minus (bellmanQbar_alt ec X1) (bellmanQbar_alt ec X2)) <=
      γ * Hierarchy.norm (Hierarchy.minus X1 X2).
  Proof.
    intros.
    assert (minus (bellmanQbar_alt ec X1) (bellmanQbar_alt ec X2)=
            (minus (bellmanQbar γ X1) (bellmanQbar γ X2))).
    {
      unfold bellmanQbar_alt, bellmanQbar, minus, plus, opp; simpl.
      unfold Rfct_plus, Rfct_opp, opp; simpl.
      apply Rfct_eq_ext; intros.
      destruct x.
      lra.
    }
    rewrite H0.
    now apply Bellman.bellmanQbar_contraction.
  Qed.

  Lemma bellmanQbar_alt_contraction_fixed (ec : Rfct (sigT M.(act))) 
                (Xstar : Rfct (sigT M.(act))) :
    0 <= γ < 1 ->
    bellmanQbar_alt ec Xstar = Xstar ->
    forall (X : Rfct(sigT M.(act))),
      Hierarchy.norm (Hierarchy.minus (bellmanQbar_alt ec X) Xstar) <=
      γ * Hierarchy.norm (Hierarchy.minus X Xstar).
  Proof.
    intros.
    rewrite <- H0 at 1.
    now apply bellmanQbar_alt_contraction.
  Qed.
 *)
  
Section FixedPoint_contract.
  Context (A : Type) {finA : FiniteType A}.

  Canonical Rfct_CompleteNormedModule :=
    CompleteNormedModule.Pack _  (Rfct A) (CompleteNormedModule.Class R_AbsRing _ (NormedModule.class _ (Rfct_NormedModule A)) (Rfct_CompleteSpace_mixin A)) (Rfct A).

  Context (X := Rfct_CompleteNormedModule).

 Lemma f_contract_fixedpoint gamma (F: X -> X) :
   0 <= gamma < 1 ->
   (forall x1 y : X, norm (minus (F x1) (F y)) <= gamma * norm (minus x1 y)) -> 
     exists (xstar : X), F xstar = xstar.
   Proof.
     intros.
     destruct (Req_dec gamma 0).
     - exists (F zero).
       rewrite H1 in H0.
       apply is_Lipschitz_le_zero_const.
       intros.
       specialize (H0 y x).
       now rewrite Rmult_0_l in H0.
     - generalize (FixedPoint R_AbsRing F (fun _ => True)); intros.
       cut_to H2; trivial.
       + destruct H2 as [x [? [? [? ?]]]].
         now exists x.
       + now exists (zero).
       + apply closed_my_complete ; apply closed_true.                
       + unfold is_contraction.
         exists gamma.
         split; [lra | ].
         unfold is_Lipschitz.
         split; [lra | ].
         intros.
         eapply Rle_lt_trans.
         apply H0.
         assert (0 < gamma) by lra.
         now apply Rmult_lt_compat_l.
  Qed.
   
End FixedPoint_contract.

  Lemma max_sqr_bound (ec : Rfct (sigT M.(act))) :
    forall (s : state M),
      Max_{act_list s} (fun a => Rsqr (ec (existT _ s a))) <= Rmax_sq_norm _ ec.
   Proof.
     intros.
     unfold Rmax_sq_norm.
     match_destr.
     apply Rmax_list_incl.
     - rewrite map_not_nil.
       apply act_list_not_nil.
     - intros ??.
       apply in_map_iff in H.
       destruct H as [? [? ?]].
       subst.
       apply in_map_iff.
       exists (existT _ s x).
       split; trivial.
   Qed.

  Lemma min_sqr_bound (ec : Rfct (sigT M.(act))) :
    forall (s : state M),
      Rmin_list (List.map (fun a => Rsqr (ec (existT _ s a))) (act_list s)) <=
                 Rmax_sq_norm _ ec.
   Proof.
     intros.
     eapply Rle_trans with
         (r2 := Max_{act_list s} (fun a => Rsqr (ec (existT _ s a)))).
     - apply Rge_le.
       apply Rmax_list_map_ge_Rmin.
     - apply max_sqr_bound.
   Qed.

  Instance finite_sigact : FiniteType( sigT M.(act)) := 
    fin_finite_dep_prod M.(fs) M.(fa).

  Context {Ts : Type}            
          {dom : SigmaAlgebra Ts}
          {prts : ProbSpace dom}
          {F : nat -> SigmaAlgebra Ts}

          (next_state : nat -> (sigT M.(act)) -> Ts -> M.(state))          
          (next_state_rv : forall t sa,
              RandomVariable (F (S t)) (discrete_sa (state M)) (next_state t sa))
          (cost : nat -> (sigT M.(act)) -> Ts -> R)          
          (cost_rv : forall t sa, RandomVariable (F (S t)) borel_sa (cost t sa))
          (islp_cost: forall t (sa : {x : state M & act M x}), IsLp prts 2 (cost t sa))          
          (Q0 : Rfct (sigT M.(act)))
          (α : nat -> Ts -> Rfct (sigT M.(act)))
          (alpha_bound : forall t ω sa, 0 <= α t ω sa <= 1)
          (rvα : forall t sa,
              RandomVariable (F t) borel_sa (fun ω => α t ω sa))
          (isfilt : IsFiltration F) 
          (filt_sub : forall k, sa_sub (F k) dom).

  Context (indep_cost: forall k sa,
              independent_sas prts (pullback_rv_sub dom borel_sa (cost k sa)
                                      (RandomVariable_sa_sub (filt_sub (S k)) _))
                (filt_sub k))
          (indep_next_state: forall k sa,
              independent_sas prts (pullback_rv_sub dom (discrete_sa (state M)) (next_state k sa) 
                                      (RandomVariable_sa_sub (filt_sub (S k)) _))
                (filt_sub k))
          (ident_distr_next_state: forall k sa,
              identically_distributed_rvs prts (discrete_sa (state M))
                (rv1 := (RandomVariable_sa_sub (filt_sub 1) _))
                (rv2 := (RandomVariable_sa_sub (filt_sub (S k)) _))
                (next_state 0%nat sa)
                (next_state k sa))
          (ident_distr_cost: forall k sa,
              identically_distributed_rvs prts borel_sa
                (rv1 := (RandomVariable_sa_sub (filt_sub 1) _))
                (rv2 := (RandomVariable_sa_sub (filt_sub (S k)) _))
                (cost 0%nat sa)
                (cost k sa))
          (β : R).

  Instance qlearn_next_state_rv2 t sa:
    RandomVariable dom (discrete_sa (state M)) (fun ω => next_state t sa ω).
  Proof.
    intros.
    now apply (RandomVariable_sa_sub (filt_sub (S t))).
  Defined.

  Instance qlearn_cost_rv2 t sa : RandomVariable dom borel_sa (cost t sa).
  Proof.
    intros.
    now apply (RandomVariable_sa_sub (filt_sub (S t))).
  Defined.

  Instance isfe_cost :
    forall t (sa : sigT M.(act)),
      IsFiniteExpectation prts (cost t sa).
  Proof.
    intros.
    apply IsLp_Finite with (n := 2); try lra; try easy.
    typeclasses eauto.
  Qed.

  Instance qlearn_rvα t sa : RandomVariable dom borel_sa (fun ω => α t ω sa).
  Proof.
    intros.
    now apply (RandomVariable_sa_sub (filt_sub t)).
  Defined.

  Instance rv_ns: forall t sa, RandomVariable dom (discrete_sa (state M)) (next_state t sa).
  Proof.
    intros.
    now apply (RandomVariable_sa_sub (filt_sub (S t))).
  Defined.

  (* Definition SA := sigT M.(act). *)

  Definition qlearn_Qmin (Q : Rfct (sigT M.(act))) (s : M.(state)) : R :=
    Min_{act_list s} (fun a => Q (existT _ s a)).

  Instance qlearn_Qmin_proper : Proper (rv_eq ==> eq ==> eq) qlearn_Qmin.
  Proof.
    intros ??????; subst.
    unfold qlearn_Qmin.
    f_equal.
    apply map_ext; intros.
    apply H.
  Qed.

  Lemma qlearn_Qmin_sa  (Q : Rfct (sigT M.(act))) (s : M.(state)) :
    exists (sa : sigT M.(act)), qlearn_Qmin Q s = Q sa.
  Proof.
    unfold qlearn_Qmin.
    generalize (Rmin_list_In (map (fun a : act M s => Q (existT (act M) s a)) (act_list s))); intros.
    cut_to H.
    - apply in_map_iff in H.
      destruct H as [? [??]].
      now exists (existT _ s x).
    - apply map_not_nil.
      apply act_list_not_nil.      
  Qed.

  Existing Instance FiniteCondexp_rv'.    

  Context {finA : FiniteType (sigT M.(act))}. 
  Definition Rmax_all : Rfct (sigT M.(act)) -> R := let (ls,_) := finA in fun (f:Rfct (sigT M.(act))) => Max_{ls}(fun s => (f s)).
  Definition Rmin_all : Rfct (sigT M.(act)) -> R := let (ls,_) := finA in fun (f:Rfct (sigT M.(act))) => Min_{ls}(fun s => (f s)).
  
  Instance isfe_qmin (Q : Rfct (sigT M.(act))) (t : nat) (sa : (sigT M.(act))) :
    IsFiniteExpectation prts (fun ω => qlearn_Qmin Q (next_state t sa ω)).
  Proof.
    apply IsFiniteExpectation_bounded with (rv_X1 := const (Rmin_all Q))
                                           (rv_X3 := const (Rmax_all Q)).
    - apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_const.
    - intros ?.
      unfold const, qlearn_Qmin, Rmin_all.
      match_destr.
      apply Rge_le.
      apply Rmin_list_incl.
      * rewrite map_not_nil.
        apply act_list_not_nil.
      * intros ??.
        apply in_map_iff in H.
        destruct H as [? [? ?]].
        subst.
        apply in_map_iff.
        exists  (existT (act M) (next_state t sa a) x).
        split; trivial.
    - intros ?.
      unfold const, qlearn_Qmin.
      unfold Rmax_all.
      match_destr.
      apply Rle_trans with (r2 := Max_{ act_list (next_state t sa a)}(fun a0 : act M (next_state t sa a) => Q (existT (act M) (next_state t sa a) a0))).
      + apply Rge_le.
        apply Rmax_list_map_ge_Rmin.
      + apply Rmax_list_incl.
        * rewrite map_not_nil.
          apply act_list_not_nil.
        * intros ??.
          apply in_map_iff in H.
          destruct H as [? [? ?]].
          subst.
          apply in_map_iff.
          exists  (existT (act M) (next_state t sa a) x).
          split; trivial.
  Qed.

  Definition qlearn_XF (Q : Rfct (sigT M.(act))) : Rfct (sigT M.(act)) :=
    fun sa => FiniteExpectation prts (cost 0%nat sa) +
                β * (FiniteExpectation prts (fun ω => qlearn_Qmin Q (next_state 0%nat sa ω))).

  Instance isfe_Rmin_list (rvs : list (Ts -> R))
                          {rv_rvs : List.Forall (RandomVariable dom borel_sa) rvs}
                          {rv_isfe : List.Forall (IsFiniteExpectation prts) rvs} :
    IsFiniteExpectation prts (fun ω : Ts => Rmin_list (map (fun x => x ω) rvs)).
  Proof.
    induction rvs.
    - apply IsFiniteExpectation_const.
    - invcs rv_rvs.
      invcs rv_isfe.
      cut_to IHrvs; trivial.
      simpl.
      destruct rvs; trivial.
      apply IsFiniteExpectation_min; trivial.
      now apply rvs_Rmin_list.
  Qed.


  Instance isfe_Rmax_list (rvs : list (Ts -> R))
                          {rv_rvs : List.Forall (RandomVariable dom borel_sa) rvs}
                          {rv_isfe : List.Forall (IsFiniteExpectation prts) rvs} :
    IsFiniteExpectation prts (fun ω : Ts => Rmax_list (map (fun x => x ω) rvs)).
  Proof.
    induction rvs.
    - apply IsFiniteExpectation_const.
    - invcs rv_rvs.
      invcs rv_isfe.
      cut_to IHrvs; trivial.
      simpl.
      destruct rvs; trivial.
      apply IsFiniteExpectation_max; trivial.
      now apply rvs_Rmax_list.
  Qed.

  Instance isfe_Rmin_all (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q ω sa)) :
    IsFiniteExpectation prts (fun ω : Ts => Rmin_all (Q ω)).
  Proof.
    unfold Rmin_all.
    match_destr.
    generalize (@isfe_Rmin_list ((map (fun (s : sigT (act M)) ω => Q ω s) fin_elms))); intros HH.
    cut_to HH.
    - revert HH.
      apply IsFiniteExpectation_proper.
      intros ?.
      now rewrite map_map.
    - apply Forall_forall; intros.
      apply in_map_iff in H.
      now destruct H as [? [??]]; subst.
    - apply Forall_forall; intros.
      apply in_map_iff in H.
      now destruct H as [? [??]]; subst.
  Qed.      

  Instance rv_Rmin_all {dom2 : SigmaAlgebra Ts} (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom2 borel_sa (fun ω => Q ω sa)) :
    RandomVariable dom2 borel_sa (fun ω : Ts => Rmin_all (Q ω)).
  Proof.
    unfold Rmin_all.
    match_destr.
    generalize (@rvs_Rmin_list Ts dom2 ((map (fun (s : sigT (act M)) ω => Q ω s) fin_elms))); intros HH.
    cut_to HH.
    - revert HH.
      apply RandomVariable_proper; try easy.
      intros ?.
      now rewrite map_map.
    - apply Forall_forall; intros.
      apply in_map_iff in H.
      now destruct H as [? [??]]; subst.
  Qed.      

  Instance rv_Rmax_all (Q : Ts -> Rfct (sigT M.(act)))
    {dom2 : SigmaAlgebra Ts}
    (isrvQ : forall sa, RandomVariable dom2 borel_sa (fun ω => Q ω sa)) :
    RandomVariable dom2 borel_sa (fun ω : Ts => Rmax_all (Q ω)).
  Proof.
    unfold Rmax_all.
    match_destr.
    generalize (@rvs_Rmax_list Ts dom2 ((map (fun (s : sigT (act M)) ω => Q ω s) fin_elms))); intros HH.
    cut_to HH.
    - revert HH.
      apply RandomVariable_proper; try easy.
      intros ?.
      now rewrite map_map.
    - apply Forall_forall; intros.
      apply in_map_iff in H.
      now destruct H as [? [??]]; subst.
  Qed.      

  Instance isfe_Rmax_all (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q ω sa)) :
    IsFiniteExpectation prts (fun ω : Ts => Rmax_all (Q ω)).
  Proof.
    unfold Rmax_all.
    match_destr.
    generalize (@isfe_Rmax_list ((map (fun (s : sigT (act M)) ω => Q ω s) fin_elms))); intros HH.
    cut_to HH.
    - revert HH.
      apply IsFiniteExpectation_proper.
      intros ?.
      now rewrite map_map.
    - apply Forall_forall; intros.
      apply in_map_iff in H.
      now destruct H as [? [??]]; subst.
    - apply Forall_forall; intros.
      apply in_map_iff in H.
      now destruct H as [? [??]]; subst.
  Qed.      

  Definition event_st_eq {dom2 : SigmaAlgebra Ts} (rvs : Ts -> M.(state)) (s0 : M.(state))
          {rv : RandomVariable dom2 (discrete_sa M.(state)) rvs} :
    event dom2 := exist _ (fun ω => (rvs ω) = s0) (rv (DiscreteProbSpace.discrete_singleton s0)).

  Lemma qlearn_Qmin_all_rv {dom2 : SigmaAlgebra Ts} (Q : Ts -> Rfct (sigT M.(act))) 
        {rv : forall sa, RandomVariable dom2 borel_sa (fun ω => Q ω sa)}:
    forall (s : M.(state)), RandomVariable dom2 borel_sa (fun ω => qlearn_Qmin (Q ω) s).
  Proof.
    intros.
    unfold qlearn_Qmin.
    generalize (@rvs_Rmin_list Ts dom2 ((map (fun a  ω => Q ω (existT _ s a)) (act_list s)))); intros HH.
    cut_to HH.
    - revert HH.
      apply RandomVariable_proper; try easy.
      intros ?.
      now rewrite map_map.
    - apply Forall_forall; intros.
      apply in_map_iff in H.
      now destruct H as [? [??]]; subst.
  Qed.

  Existing Instance st_eqdec.

  Instance rv_qmin1 (Q : Ts -> Rfct (sigT M.(act))) (f:Ts -> state M) 
           {dom2 : SigmaAlgebra Ts}
    (rvQ : forall sa, RandomVariable dom2 borel_sa (fun ω => Q ω sa))

    (rvf : RandomVariable dom2 (discrete_sa M.(state)) f) :
    RandomVariable dom2 borel_sa 
                   (fun ω : Ts => qlearn_Qmin (Q ω) (f ω)).
  Proof.
    cut (RandomVariable dom2 borel_sa
           (fun ω : Ts => finite_Rsum (fun x => (qlearn_Qmin (Q ω) x) * (EventIndicator (classic_dec (event_st_eq f x)) ω)))).
    - apply RandomVariable_proper; try reflexivity.
      intros ?.
      unfold EventIndicator.
      unfold finite_Rsum.
      rewrite list_sum_all_but_zero with (c:=f a).
      + match_destr; try lra.
        unfold event_st_eq in *; simpl in *; congruence.
      + apply NoDup_nodup.
      + apply nodup_In.
        apply fin_finite.
      + intros.
        match_destr; try lra.
        unfold event_st_eq in *; simpl in *.
        congruence.
    - apply rv_finite_Rsum; intros.
      apply rvmult_rv.
      + now apply qlearn_Qmin_all_rv.
      + apply EventIndicator_rv.
  Qed.

  Instance rv_qmin2 (Q : Ts -> Rfct (sigT M.(act))) (f:Ts -> state M) 
           {dom2 : SigmaAlgebra Ts}
    (rvQ : forall sa, RandomVariable dom2 borel_sa (fun ω => Q ω sa))

    (rvf : RandomVariable dom2 (discrete_sa M.(state)) f) :
    RandomVariable (product_sa dom2 dom2) borel_sa 
                   (fun '(ω,ω0) => qlearn_Qmin (Q ω) (f ω0)).
  Proof.
    cut (RandomVariable (product_sa dom2 dom2) borel_sa
           (fun '(ω,ω0) => finite_Rsum (fun x => (qlearn_Qmin (Q ω) x) * (EventIndicator (classic_dec (event_st_eq f x)) ω0)))).
    - apply RandomVariable_proper; try reflexivity.
      intros ?.
      unfold EventIndicator.
      unfold finite_Rsum.
      destruct a.
      rewrite list_sum_all_but_zero with (c:=f t0).
      + match_destr; try lra.
        unfold event_st_eq in *; simpl in *; congruence.
      + apply NoDup_nodup.
      + apply nodup_In.
        apply fin_finite.
      + intros.
        match_destr; try lra.
        unfold event_st_eq in *; simpl in *.
        congruence.
    -
      generalize (@rv_finite_Rsum (prod Ts Ts) (state M) _ _); intros HH.
      specialize (HH (fun ω x => qlearn_Qmin (Q (fst ω)) x * EventIndicator (classic_dec (event_st_eq f x)) (snd ω))).
      specialize (HH (product_sa dom2 dom2)).
      cut_to HH.
      + revert HH.
        apply RandomVariable_proper; try reflexivity; intros ?.
        now destruct a.
      + intros.
        apply rvmult_rv.
        * generalize qlearn_Qmin_all_rv; intros HH2.
          apply (compose_rv fst (fun ω : Ts => qlearn_Qmin (Q ω) b)).
        * apply (compose_rv snd _). 
  Qed.


  Instance isfe_qmin2 (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q ω sa)) :
    forall x, IsFiniteExpectation prts (fun ω : Ts => qlearn_Qmin (Q ω) x).
  Proof.
    intros.
    apply IsFiniteExpectation_bounded with
        (rv_X1 := fun ω => Rmin_all (Q ω)) (rv_X3 := fun ω => Rmax_all (Q ω)).
    - typeclasses eauto.
    - typeclasses eauto.      
    - intros ?.
      unfold Rmin_all, qlearn_Qmin.
      match_destr.
      apply Rge_le, Rmin_list_incl.
      + rewrite map_not_nil.
        apply act_list_not_nil.
      + intros ??.
        apply in_map_iff in H.
        destruct H as [? [? ?]].
        subst.
        apply in_map_iff.
        eexists.
        split; try reflexivity; trivial.
    - intros ?.
      unfold Rmax_all, qlearn_Qmin.
      apply Rle_trans with
        (r2:=Max_{ act_list x}(fun a0 : act M x => Q a (existT (act M) x a0))).
      + apply Rge_le, Rmax_list_map_ge_Rmin.
      + match_destr.
        apply Rmax_list_incl.
        * rewrite map_not_nil.
          apply act_list_not_nil.
        * intros ??.
          apply in_map_iff in H.
          destruct H as [? [? ?]].
          subst.
          apply in_map_iff.
          eexists; split; try reflexivity; trivial.
  Qed.

  Instance isfe_qmin1 (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q ω sa))
    (sa : (sigT M.(act))) :
    forall t,
      IsFiniteExpectation prts (fun ω : Ts => qlearn_Qmin (Q ω) (next_state t sa ω)).
  Proof.
    intros.
    apply IsFiniteExpectation_bounded with
        (rv_X1 := fun ω => Rmin_all (Q ω)) (rv_X3 := fun ω => Rmax_all (Q ω)).
    - typeclasses eauto.
    - typeclasses eauto.      
    - intros ?.
      unfold Rmin_all, qlearn_Qmin.
      match_destr.
      apply Rge_le, Rmin_list_incl.
      + rewrite map_not_nil.
        apply act_list_not_nil.
      + intros ??.
        apply in_map_iff in H.
        destruct H as [? [? ?]].
        subst.
        apply in_map_iff.
        exists  (existT (act M) (next_state t sa a) x).
        split; trivial.
    - intros ?.
      unfold Rmax_all, qlearn_Qmin.
      apply Rle_trans with
          (r2 :=  Max_{ act_list (next_state t sa a)}(fun a0 : act M (next_state t sa a) => Q a (existT (act M) (next_state t sa a) a0))).
      + apply Rge_le, Rmax_list_map_ge_Rmin.
      + match_destr.
        apply Rmax_list_incl.
        * rewrite map_not_nil.
          apply act_list_not_nil.
        * intros ??.
          apply in_map_iff in H.
          destruct H as [? [? ?]].
          subst.
          apply in_map_iff.
          exists  (existT (act M) (next_state t sa a) x).
          split; trivial.
  Qed.

  Instance isfe_qmin2' (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q ω sa))
    (sa : (sigT M.(act))) :
    forall k,
      IsFiniteExpectation (product_ps prts prts)
        (fun '(ω, ω0) => qlearn_Qmin (Q ω) (next_state k sa ω0)).
  Proof.
    intros.
    apply IsFiniteExpectation_bounded with
      (rv_X1 := fun p => Rmin_all (Q (fst p))) (rv_X3 := fun p => Rmax_all (Q (fst p))).
    - apply (isfe_prod_fst prts (fun ω => Rmin_all (Q ω))).
    - apply (isfe_prod_fst prts (fun ω => Rmax_all (Q ω))).
    - intros ?.
      unfold Rmin_all, qlearn_Qmin.
      match_destr.
      destruct a.
      apply Rge_le, Rmin_list_incl.
      + rewrite map_not_nil.
        apply act_list_not_nil.
      + intros ??.
        apply in_map_iff in H.
        destruct H as [? [? ?]].
        subst.
        apply in_map_iff.
        simpl.
        exists  (existT (act M) (next_state k sa t0) x).
        split; trivial.
    - intros ?.
      unfold Rmax_all, qlearn_Qmin.
      destruct a.
      apply Rle_trans with
          (r2 :=  Max_{ act_list (next_state k sa t0)}(fun a0 : act M (next_state k sa t0) => Q t (existT (act M) (next_state k sa t0) a0))).
      + apply Rge_le, Rmax_list_map_ge_Rmin.
      + match_destr.
        apply Rmax_list_incl.
        * rewrite map_not_nil.
          apply act_list_not_nil.
        * intros ??.
          apply in_map_iff in H.
          destruct H as [? [? ?]].
          subst.
          apply in_map_iff.
          simpl.
          exists  (existT (act M) (next_state k sa t0) x).
          split; trivial.
  Qed.

  Instance isl2_qmin1 (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsLp prts 2 (fun ω => Q ω sa))
    (sa : (sigT M.(act))) :
    forall t,
      IsLp prts 2 (fun ω : Ts => qlearn_Qmin (Q ω) (next_state t sa ω)).
  Proof.
    intros.
    unfold qlearn_Qmin.
    apply IsLp_bounded with
        (rv_X2 := fun ω => (Rmax_all (fun sa => Rsqr (Q ω sa)))).
    - intros ?.
      rewrite rvpower2; [| apply nnfabs].
      rv_unfold.
      rewrite <- Rsqr_abs.
      unfold Rmax_all, qlearn_Qmin.
      match_destr.
      assert (exists sa0,
                 Min_{ act_list (next_state t sa a)}
                     (fun a0 : act M (next_state t sa a) => Q a (existT (act M) (next_state t sa a) a0)) = Q a sa0).
      {
        generalize (Rmin_list_map_exist (fun a0 : act M (next_state t sa a) => Q a (existT (act M) (next_state t sa a) a0))  (act_list (next_state t sa a))); intros.
        cut_to H.
        - destruct H as [? [? ?]].
          exists (existT _ _ x).
          now rewrite <- H0.
        - apply act_list_not_nil.
      }
      destruct H.
      rewrite H.
      apply Rmax_spec.
      apply in_map_iff.
      exists x.
      split; trivial.
    - apply isfe_Rmax_all; try typeclasses eauto.
  Qed.

  Program Instance frf_Qmin (g : Rfct (sigT M.(act))) (f : Ts -> M.(state))
           {rvf : RandomVariable dom (discrete_sa M.(state)) f} :
    FiniteRangeFunction (fun ω0 : Ts => qlearn_Qmin g (f ω0))
    := { frf_vals := map (fun s => qlearn_Qmin g s) fin_elms }.
  Next Obligation.
    apply in_map_iff.
    exists (f x).
    split; trivial.
    destruct (M.(fs)).
    apply fin_finite.
  Qed.

  Instance isfe_small_mult (f g: Ts -> R)
    {rvf: RandomVariable dom borel_sa f}
    {rvg: RandomVariable dom borel_sa g}
    (fbounded: forall ω, 0 <= f ω <= 1) {isfeg : IsFiniteExpectation prts g} :
    IsFiniteExpectation prts (rvmult f g).
  Proof.
    eapply (IsFiniteExpectation_bounded prts (rvmin (const 0) g) _ (rvmax (const 0) g)).
    - intros ?.
      unfold rvmin, Rmin, const, rvmult.
      match_destr.
      + apply Rmult_le_pos; trivial.
        apply fbounded.
      + cut (f a * - g a <= - g a); [lra |].
        cut (f a * - g a <= 1 * - g a); [lra |].
        apply Rmult_le_compat_r; [lra |].
        apply fbounded.
    - intros ?.
      unfold rvmax, Rmax, const, rvmult.
      match_destr.
      + cut (f a * g a <= 1 * g a); [lra |].
        apply Rmult_le_compat_r; [lra |].
        apply fbounded.
      + cut (0 <= f a * - g a); [lra |].
        apply Rmult_le_pos; [| lra].
        apply fbounded.
  Qed.

  Fixpoint qlearn_Q (t : nat) : (Ts -> Rfct (sigT M.(act)))    :=
           match t with
           | 0%nat => (fun ω  => Q0)
           | S t' => let g := qlearn_Q t' in 
                     (fun ω sa => (g ω sa) + 
                                  (α t' ω sa) * ((cost t' sa ω) + β * (qlearn_Qmin (g ω) (next_state t' sa ω))
                                                                   - (g ω sa)))
           end.

  Instance qlearn_Q_rv    :
    forall t sa, RandomVariable (F t) borel_sa (fun ω => qlearn_Q t ω sa).
  Proof.
    induction t; simpl; intros.
    - apply rvconst.
    - apply rvplus_rv.
      + now apply (RandomVariable_sa_sub (isfilt t)).
      + apply rvmult_rv.
        * now apply (RandomVariable_sa_sub (isfilt t)).
        * apply rvplus_rv.
          -- apply rvplus_rv; try easy.
             apply rvscale_rv.
             apply rv_qmin1.
             ++ intros.
                apply (RandomVariable_sa_sub (isfilt t)).      
                now apply IHt.
             ++ apply next_state_rv.
          -- apply rvopp_rv'.
             now apply (RandomVariable_sa_sub (isfilt t)).                   
  Qed.

  Instance qlearn_Q_rv_dom :
    forall t sa, RandomVariable dom borel_sa (fun ω => qlearn_Q t ω sa).
  Proof.
    induction t; simpl; intros; typeclasses eauto.
  Qed.

  Instance isfe_qlearn_Q:
    forall t sa, IsFiniteExpectation prts (fun ω => qlearn_Q t ω sa).
  Proof.
    intros.
    revert sa.
    induction t.
    - intros.
      simpl.
      apply IsFiniteExpectation_const.
    - intros.
      simpl.
      apply IsFiniteExpectation_plus; try typeclasses eauto.
      apply isfe_small_mult; try typeclasses eauto.
      intros; apply alpha_bound.
  Qed.      

  Instance isl2_qlearn_Q
     (isl2_sa: forall k sa, IsLp prts 2 (cost k sa)):
    forall k sa, IsLp prts 2 (fun ω => qlearn_Q k ω sa).
  Proof.
    intros.
    revert sa.
    induction k.
    - intros.
      simpl.
      apply IsLp_const.
    - intros.
      simpl.
      assert (0 <= 2) by lra.
      generalize (IsLp_plus prts (mknonnegreal _ H)); intros.
      apply H0; try typeclasses eauto.
      apply IsLp_almost_bounded with
          (rv_X2 :=  
             (fun ω : Ts =>
                (Rsqr 
                   (cost k sa ω + 
                    β * qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω) -
                    qlearn_Q k ω sa)))); try typeclasses eauto.
      + apply all_almost; intros.
        rewrite rvpower2; [|apply nnfabs].
        rv_unfold.
        rewrite <- Rsqr_abs.        
        rewrite Rsqr_mult.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat_r; [apply Rle_0_sqr | ].
        replace 1 with (Rsqr 1).
        * specialize (alpha_bound k x sa).
          apply neg_pos_Rsqr_le; lra.
        * unfold Rsqr; lra.
      + assert (IsLp prts 2 
                     (fun ω : Ts =>
                        (cost k sa ω + 
                         β * qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω) -
                         qlearn_Q k ω sa))).
        {
          apply H0; try typeclasses eauto.
          generalize (IsLp_opp prts (mknonnegreal _ H) (fun ω => qlearn_Q k ω sa)); intros.
          revert H1.
          apply IsLp_proper; try easy.
          intros ?.
          rv_unfold'.
          lra.
        }
        unfold IsLp in H1.
        revert H1.
        apply IsFiniteExpectation_proper.
        intros ?.
        rewrite rvpower2; [|apply nnfabs].
        rv_unfold.
        now rewrite <- Rsqr_abs.
   Qed.

  Definition qlearn_w (Q : nat -> Ts -> Rfct (sigT M.(act)))
             (t : nat) (ω : Ts) (sa : (sigT M.(act)))     
             (rvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q t ω sa))
             (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q t ω sa)) : R :=
    ((cost t sa ω) - FiniteExpectation (isfe := isfe_cost t sa) prts (cost t sa)) +
                     β *(qlearn_Qmin (Q t ω) (next_state t sa ω) -
                         (FiniteExpectation 
                           prts 
                           (fun ω0 => qlearn_Qmin (Q t ω) (next_state t sa ω0)))).

  Lemma finite_fun_vector_iso_nth (x : Rfct (sigT M.(act))) (P : R -> Prop) :
    let iso_f := iso_f
                   (Isomorphism := finite_fun_vec_encoder finA EqDecsigT (B := R)) in
    (forall sa, P (x sa)) <-> (forall i pf, P (vector_nth i pf (iso_f x))).
  Proof.
    simpl.
    split; intros.
    - unfold finite_fun_to_vector; simpl.
      rewrite vector_nth_map.
      apply H.
    - specialize (H _ (fin_finite_index_bound finA (dec:=EqDecsigT) sa)).
      unfold finite_fun_to_vector in H.
      now rewrite vector_nth_finite_map in H.
  Qed.

  Lemma finite_fun_vector_iso_nth_fun {A} (x : A -> Rfct (sigT M.(act))) (P : (A -> R) -> Prop) 
    (Pext : Proper (rv_eq ==> iff) P) :
    let iso_f := iso_f
                   (Isomorphism := finite_fun_vec_encoder finA EqDecsigT (B := R)) in
    (forall sa, P (fun A => x A sa)) <-> (forall i pf, P (fun A => vector_nth i pf (iso_f (x A)))).
  Proof.
    simpl.
    split; intros.
    - unfold finite_fun_to_vector; simpl.
      eapply Pext.
      + intros ?.
        rewrite vector_nth_map.
        reflexivity.
      + apply H.
    - specialize (H _ (fin_finite_index_bound finA (dec:=EqDecsigT) sa)).
      unfold finite_fun_to_vector in H.
      eapply Pext in H.
      + apply H.
      + intros ?.
        now rewrite vector_nth_finite_map.
  Qed.

  Let our_iso_f := iso_f (Isomorphism := finite_fun_vec_encoder finA EqDecsigT (B := R)).
  Let our_iso_b := iso_b (Isomorphism := finite_fun_vec_encoder finA EqDecsigT (B := R)).

  Lemma nodup_length_le {A} (decA : forall x y : A, {x = y} + {x <> y}) (l : list A) :
    (length (nodup decA l) <= length l)%nat.
  Proof.
    induction l; simpl; trivial.
    match_destr; simpl; lia.
  Qed.

  Lemma nodup_length_nzero {A} (decA : forall x y : A, {x = y} + {x <> y}) (l : list A) :
    (0 < length (nodup decA l) <->
    0 < length l)%nat.
  Proof.
    split.
    - intros.
      generalize (nodup_length_le decA l); lia.
    - destruct l; simpl; trivial.
      intros _.
      revert a.
      induction l; simpl; trivial; [lia |]; intros.
      match_destr; simpl; lia.
  Qed.
    
  Existing Instance Rbar_le_pre.

  Instance finfun_sa : SigmaAlgebra (Rfct (sigT M.(act))) :=
    iso_sa (iso := Isomorphism_symm (finite_fun_vec_encoder finA EqDecsigT (B := R)))
      (Rvector_borel_sa _).

  Instance rv_qmin3
    {rv: forall sa, 
        RandomVariable finfun_sa borel_sa
          (fun q : Rfct {x : state M & act M x} => q sa)} :
    RandomVariable (product_sa finfun_sa (discrete_sa (state M)))
                            borel_sa (fun '(q, ns) => qlearn_Qmin q ns).
  Proof.
    cut (RandomVariable (product_sa finfun_sa (discrete_sa (state M))) borel_sa
           (fun qns => finite_Rsum 
                             (fun x => (qlearn_Qmin (fst qns) x) * 
                                         (EventIndicator (classic_dec (preimage_singleton (fun qns => snd qns) x))) qns))).
    - apply RandomVariable_proper; try reflexivity.
      intros ?.
      unfold EventIndicator.
      unfold finite_Rsum.
      destruct a.
      rewrite list_sum_all_but_zero with (c:=s).
      + unfold fst; match_destr; try lra.
        unfold preimage_singleton in n; simpl in n.
        now unfold pre_event_preimage, pre_event_singleton, snd in n.
      + apply NoDup_nodup.
      + apply nodup_In.
        apply fin_finite.
      + intros.
        match_destr; try lra.
        unfold preimage_singleton in e; simpl in e.
        unfold pre_event_preimage, pre_event_singleton, snd in e.
        congruence.
    - apply list_sum_map_rv.
      intros.
      apply rvmult_rv.
      + generalize (@compose_rv _ _ _ (product_sa finfun_sa (discrete_sa (state M)))
                      finfun_sa borel_sa fst  (fun q => qlearn_Qmin q x)); intros.
        apply H; try typeclasses eauto.
        unfold qlearn_Qmin.
        apply rvs_Rmin_list'.
        now rewrite Forall_forall; intros.
      + apply EventIndicator_rv.
  Qed.

  Theorem Tsitsiklis_1_3_fintype
    (X w  : nat -> Ts -> Rfct (sigT M.(act)))
    (x' : Rfct (sigT M.(act)))
    (XF : nat -> Rfct (sigT M.(act)) -> Rfct (sigT M.(act)))
    (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F) 
    {rvX0 : forall sa, RandomVariable (F 0%nat) borel_sa (fun ω => X 0%nat ω sa)}
    (adapt_w : forall sa, IsAdapted borel_sa (fun t ω => w t ω sa) (fun k => F (S k)))
    {rvXF : forall k, RandomVariable finfun_sa finfun_sa (XF k)}
    {rvw : forall k sa, RandomVariable dom borel_sa (fun ω : Ts => w k ω sa)}
    {iscond : forall k sa, is_conditional_expectation prts (F k) (fun ω => w k ω sa) (ConditionalExpectation prts (filt_sub k) (fun ω => w k ω sa))} :
    
    (forall sa ω, is_lim_seq (sum_n (fun k => α k ω sa)) p_infty) ->
    (exists (C : R),
        forall sa,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (α k ω sa)))) (Finite C))) ->
    (forall k sa, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => w k ω sa)) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k sa, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (fun ω => (w k ω sa))))
                   (rvplus (const A) 
                           (rvscale B (rvmaxlist 
                                         (fun j ω => Rsqr (Rmax_norm _ (X j ω)))
                                         k)))) ->
    0 <= β < 1 ->
     (forall k x, Rmax_norm _ (Rfct_minus _ (XF k x) x') <= β * Rmax_norm _ (Rfct_minus _ x x')) ->
    (forall k ω sa, X (S k) ω sa = 
                    (X k ω sa) +  ((α k ω sa) * (((XF k (X k ω) sa) - (X k ω sa) ) +  (w k ω sa)))) ->
(*    almost prts (fun ω => is_lim_seq (fun n => Rmax_norm _ (Rfct_minus _ (X n ω) x')) 0). *)
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) (x' sa)).
  Proof.
    intros.
  
    pose (Xvec := fun t ω => our_iso_f (X t ω)).
    pose (wvec := fun t ω => our_iso_f (w t ω)).
    pose (αvec := fun t ω => our_iso_f (α t ω)).    
    pose (XFvec := fun t vecrf => our_iso_f (XF t (our_iso_b vecrf))).
    pose (xvec' := our_iso_f x').
    pose (N := length (nodup EqDecsigT fin_elms)).
    generalize (Tsitsiklis_1_3_orig β Xvec wvec αvec xvec' XFvec isfilt filt_sub); intros.
    assert (IsAdapted (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) αvec F).
    {
      unfold IsAdapted.
      intros.
      apply rv_vecrvnth; intros.
      assert (forall sa, RandomVariable (F n) borel_sa (fun ω => α n ω sa)).
      {
        intros.
        apply adapt_alpha.
      }
      generalize (finite_fun_vector_iso_nth_fun (α n)); intros.
      rewrite H8 in H7.
      apply H7.
      intros.
      apply RandomVariable_proper; try reflexivity.
    }
    assert ( RandomVariable (F 0) (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) (Xvec 0%nat)).
    {
      apply rv_vecrvnth.
      rewrite finite_fun_vector_iso_nth_fun in rvX0.
      apply rvX0.
      apply RandomVariable_proper; try reflexivity.
    }
    assert (0 < length (nodup EqDecsigT fin_elms))%nat.
    {
      assert (NonEmpty (sigT M.(act))).
      {
        unfold NonEmpty.
        generalize (M.(ne)); intros.
        red in X0.
        generalize (M.(na) X0); intros.
        red in X1.
        exact (existT _ X0 X1).
      }
      red in X0.
      apply nodup_length_nzero.
      generalize (fin_finite X0).
      clear.
      destruct fin_elms; simpl; [tauto | lia].
    }
    assert (IsAdapted (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) wvec (fun k : nat => F (S k))).
    {
      unfold IsAdapted.
      intros.
      apply rv_vecrvnth; intros.
      assert (forall sa, RandomVariable (F (S n)) borel_sa (fun ω => w n ω sa)).
      {
        intros.
        apply adapt_w.
      }
      rewrite finite_fun_vector_iso_nth_fun in H10.
      apply H10.
      apply RandomVariable_proper; try reflexivity.
    }
    assert (forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (wvec k ω))).
    {
      intros k.
      generalize (rvw k); intros rvw1.
      rewrite finite_fun_vector_iso_nth_fun in rvw1.
      apply rvw1.
      apply RandomVariable_proper; try reflexivity.
    }
    assert (forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (wvec k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (wvec k)))).
    {
      intros k.
      specialize (iscond k).
      unfold vecrvnth.
      clear H0 H1 H2 H6.
      generalize (finite_fun_vector_iso_nth_fun (w k)); intros.
      unfold wvec.
      specialize (iscond (vector_nth i pf (vector_from_list (nodup EqDecsigT fin_elms)))).
      revert iscond.
      apply is_conditional_expectation_proper; trivial.
      - apply all_almost; intros.
        unfold our_iso_f, iso_f; simpl.
        unfold finite_fun_to_vector; simpl.
        now rewrite vector_nth_map.
      - apply almost_prob_space_sa_sub_lift with (sub := filt_sub k).
        apply Condexp_proper.
        apply all_almost; intros.
        unfold our_iso_f, iso_f; simpl.
        unfold finite_fun_to_vector; simpl.
        now rewrite vector_nth_map.
    }
    assert (rvXFvec: forall k, RandomVariable (Rvector_borel_sa (length (nodup EqDecsigT fin_elms)))
                           (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) (XFvec k)).
    {
      intros.
      unfold XFvec.
      apply (rv_cod_iso_sa_b (Isomorphism_symm (finite_fun_vec_encoder finA EqDecsigT (B := R)))).
      apply (RandomVariable_proper
               _ _ (reflexivity _)
               _ finfun_sa (reflexivity _) _ 
               (fun ω' => XF k (our_iso_b ω'))).
      {
        intros ?.
        apply iso_b_f.
      }
      unfold our_iso_b.
      generalize (rv_dom_iso_sa_f (finite_fun_vec_encoder finA EqDecsigT (B := R)) (rvXF k)).
      apply RandomVariable_proper; try reflexivity.
      symmetry.
      apply iso_sa_symm_id.
    }
    specialize (H6 _ _ H9 _ _ _ H12).
    cut_to H6; trivial.
    - revert H6.
      apply almost_impl, all_almost; intros ??.
      intros sa.
      specialize (H6 _ (fin_finite_index_bound _ sa)).
      unfold xvec', our_iso_f in H6.
      simpl in H6.
      generalize (finite_fun_iso_b_f finA EqDecsigT x').
      unfold vector_to_finite_fun; intros eqq1.
      apply (f_equal (fun x => x sa)) in eqq1.
      rewrite eqq1 in H6.
      revert H6.
      apply is_lim_seq_ext; intros.
      unfold Xvec, our_iso_f; simpl.
      generalize (finite_fun_iso_b_f finA EqDecsigT (X n x)).
      unfold vector_to_finite_fun; intros eqq2.
      now apply (f_equal (fun x => x sa)) in eqq2.
    - intros k ω.
      generalize  (alpha_bound k ω); intros ab.
      generalize (finite_fun_vector_iso_nth (α k ω) (fun r => 0 <= r <= 1)); intros.
      now rewrite H13 in ab.
    - assert (forall ω i pf,
                 is_lim_seq (sum_n (fun k : nat => vector_nth i pf (αvec k ω))) p_infty).
      {
        intros ω.
        assert (forall sa, is_lim_seq (sum_n (fun k : nat => α k ω sa)) p_infty).
        {
          intros.
          apply H.
        }
        generalize (finite_fun_vector_iso_nth_fun (fun k => α k ω) 
                                                  (fun afun => is_lim_seq (sum_n afun) p_infty)); intros.
        rewrite H14 in H13.
        apply H13.
        intros ???.
        apply is_lim_seq_proper; trivial.
        intros ?.
        now apply sum_n_ext.
      }
      intros.
      apply H13.
    - destruct H0 as [C ?].
      exists C.
      revert H0.
      intros HH i pf.
      generalize (HH (vector_nth i pf (vector_from_list (nodup EqDecsigT fin_elms)))).
      apply almost_impl; apply all_almost; intros ??.
      rewrite <- H0.
      apply refl_refl.
      apply Lim_seq_ext; intros ?.
      apply sum_n_ext; intros.
      unfold αvec, our_iso_f, iso_f; simpl.
      unfold finite_fun_to_vector; simpl.
      now rewrite vector_nth_map.
    - clear H6.
      intros k i pf.
      specialize (H1 k (vector_nth i pf (vector_from_list (nodup EqDecsigT fin_elms)))).
      rewrite <- H1.
      apply almost_prob_space_sa_sub_lift with (sub := filt_sub k).
      apply Condexp_proper.
      apply all_almost; intros.
      unfold vecrvnth, wvec, our_iso_f, iso_f; simpl.
      unfold finite_fun_to_vector; simpl.
      now rewrite vector_nth_map.
    - destruct H2 as [A [B [? [? ?]]]].
      exists A; exists B.
      split; trivial.
      split; trivial; clear H6.
      intros.
      specialize (H14 k (vector_nth i pf (vector_from_list (nodup EqDecsigT fin_elms)))).
      revert H14.
      apply almost_impl; apply all_almost; intros ??.
      etransitivity; [| etransitivity]; [| apply H6 |]; apply refl_refl.
      + apply ConditionalExpectation_ext.
        intros ?.
        unfold rvsqr, vecrvnth.
        f_equal.
        unfold wvec, our_iso_f; simpl.
        unfold finite_fun_to_vector.
        now rewrite vector_nth_map.
      + unfold rvplus, rvscale, rvmaxlist, const, rvsqr, rvmaxabs, Rvector_max_abs.
        do 3 f_equal.
        apply Rmax_list_map_ext; intros.
        f_equal.
        unfold Rmax_norm.
        unfold fin_elms; destruct finA.
        generalize (nodup_equiv EqDecsigT fin_elms)
        ; intros eqq1.
        rewrite <- (map_equivlist (fun s : sigT (act M) => Rabs (X x0 x s)) _ (reflexivity _) _ _ eqq1).
        rewrite <- fold_left_Rmax_abs.
        * unfold vector_fold_left; simpl.
          now rewrite map_map.
        * apply Forall_map.
          apply Forall_forall; intros.
          apply Rabs_pos.
    - intros k x.
      generalize (H4 k (our_iso_b x)); intros HH.
      unfold XFvec.
      unfold Rmax_norm in HH.
      unfold fin_elms in *.
      destruct finA.
      generalize (nodup_equiv EqDecsigT fin_elms)
      ; intros eqq1.
      repeat rewrite <- (map_equivlist (fun s : sigT (act M) => Rabs _) _ (reflexivity _) _ _ eqq1) in HH.
      unfold our_iso_f; simpl.
      etransitivity; [etransitivity |]; [| apply HH |]; right.
      + rewrite <- fold_left_Rmax_abs.
        * unfold Rvector_max_abs, vector_fold_left; simpl.
          rewrite map_map, map_map, combine_map_l, combine_map_r, combine_self, map_map, map_map, map_map.
          f_equal; apply map_ext; intros.
          f_equal.
          unfold Rfct_minus; lra.
        * apply Forall_map.
          apply Forall_forall; intros.
          apply Rabs_pos.
      + rewrite <- fold_left_Rmax_abs.
        * unfold Rvector_max_abs, vector_fold_left; simpl.
          f_equal.
          rewrite <- map_map.
          repeat rewrite (fold_left_map _ Rabs).
          f_equal.
          unfold our_iso_b; simpl.
          unfold vector_to_finite_fun; simpl in *.
          generalize (vector_map_nth_finite (Build_FiniteType _ fin_elms fin_finite) EqDecsigT (B:=R) x); intros HH2.
          apply (f_equal (@proj1_sig _ _)) in HH2.
          simpl in HH2.
          rewrite <- HH2.
          rewrite map_map, combine_map_l, combine_map_r, combine_self, map_map, map_map, map_map.
          apply map_ext; intros.
          unfold Rfct_minus; lra.
        * apply Forall_map.
          apply Forall_forall; intros.
          apply Rabs_pos.
    - revert H5.
      intros.
      intros ?.
      apply vector_nth_eq; intros.
      unfold Xvec, XFvec, αvec, wvec, our_iso_f, iso_f; simpl.
      unfold finite_fun_to_vector.
      unfold vecrvminus, vecrvopp, vecrvscale, vecrvplus, vecrvmult.
      repeat (rewrite Rvector_nth_plus || rewrite Rvector_nth_mult || rewrite Rvector_nth_scale || rewrite vector_nth_map).
      rewrite H5.
      unfold our_iso_b.
      simpl.
      generalize (finite_fun_iso_b_f finA EqDecsigT (X k a)); intros HH.
      unfold finite_fun_to_vector in HH.
      rewrite HH.
      lra.
  Qed.

  Instance rv_finfun_sa {Ts1} {dom1 : SigmaAlgebra Ts1}
           (rv_X : Ts1 -> Rfct (sigT M.(act)))
           {rv : forall sa, RandomVariable dom1 borel_sa (fun ω => rv_X ω sa)} :
    RandomVariable dom1 finfun_sa rv_X.
  Proof.
    unfold finfun_sa; simpl.
    apply (rv_cod_iso_sa_b (finite_fun_vec_encoder finA EqDecsigT (B := R))).
    cut (RandomVariable dom1 (Rvector_borel_sa (length (nodup EqDecsigT fin_elms)))
           (fun ω' : Ts1 => our_iso_f (rv_X ω'))).
    {
      apply RandomVariable_proper; try reflexivity.
      apply iso_sa_symm_id.
    }
    apply rv_vecrvnth; intros.
    unfold vecrvnth.
    eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)).
    - intros ?.
      unfold our_iso_f; simpl.
      unfold finite_fun_to_vector.
      rewrite vector_nth_map.
      reflexivity.
    - apply rv.
  Qed.

  Instance finfun_sa_rv {Ts1} {dom1 : SigmaAlgebra Ts1}
           (rv_X : Ts1 -> Rfct (sigT M.(act)))
           {rv : RandomVariable dom1 finfun_sa rv_X} :
    forall sa, RandomVariable dom1 borel_sa (fun ω => rv_X ω sa).
  Proof.

    assert (rv': RandomVariable dom1 (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) (fun x => our_iso_f (rv_X x))).
    {
      generalize (rv_cod_iso_sa_f (finite_fun_vec_encoder finA EqDecsigT (B := R)) rv).
      apply RandomVariable_proper; try reflexivity.
      unfold finfun_sa.
      now rewrite iso_sa_symm_id'.
    }
    intros sa.
    generalize (vecrvnth_rv _ (fin_finite_index_bound (dec:=EqDecsigT) _ sa) _ (rv:=rv')).
    apply RandomVariable_proper; try reflexivity.
    intros ?.
    unfold vecrvnth.
    symmetry.
    apply (vector_nth_finite_map finA EqDecsigT (rv_X a) sa).
  Qed.

  Lemma FiniteExpectation_Qmin (x : Rfct {s : state M & act M s}) sa :
    forall t,
      FiniteExpectation prts (fun ω : Ts => qlearn_Qmin x (next_state t sa ω)) =
        list_sum (map (fun v : state M => qlearn_Qmin x v * ps_P (preimage_singleton (next_state t sa) v)) 
                  (fin_elms (FiniteType := fin_finite_nodup _))).
  Proof.
    intros.
    erewrite FiniteExpectation_simple.
    now erewrite SimpleExpectation_compose.
  Qed.

   Lemma qlearn_XF_contraction0 :
    0 <= β < 1 ->
    forall x y : Rfct {x : state M & act M x},
    forall sa,
        Rabs (qlearn_XF x sa - qlearn_XF y sa) <=      
        β * Rmax_norm (sigT M.(act)) (Rfct_minus (sigT M.(act)) x y).
  Proof.
    intros.
    unfold qlearn_XF.
    replace  (FiniteExpectation prts (cost 0%nat sa) +
              β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin x (next_state 0%nat sa ω)) -
              (FiniteExpectation prts (cost 0%nat sa) +
               β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin y (next_state 0%nat sa ω))))
      with
        (β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin x (next_state 0%nat sa ω)) -
         β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin y (next_state 0%nat sa ω))) by lra.
    rewrite <- Rmult_minus_distr_l.
    rewrite Rabs_mult.
    rewrite Rabs_right; try lra.
    apply Rmult_le_compat_l; try lra.
    do 2 rewrite FiniteExpectation_Qmin.
    rewrite <- list_sum_map_sub.
    unfold Rmax_norm.
    match_destr.
    rewrite list_sum_Rabs_triangle.
    rewrite map_map.
    unfold qlearn_Qmin.
    unfold Rfct_minus.
    apply Rle_trans with
        (r2 :=  
           list_sum
             (map
                (fun x0 : state M =>
                   (Max_{ act_list x0}
                        (fun a : act M x0 => 
                           (Rabs
                             (x (existT (act M) x0 a) - 
                              y (existT (act M) x0 a))) *
                           ps_P (preimage_singleton (next_state 0%nat sa) x0))))
                (@FiniteType.fin_elms 
                   (state M)
                   (@fin_finite_nodup (state M) (st_eqdec M) (fs M))))).
    - apply list_sum_le.
      intros.
      rewrite <- Rmult_minus_distr_r.
      rewrite Rabs_mult.
      apply Rge_le.
      setoid_rewrite Rmult_comm.
      rewrite Rmax_list_map_const_mul; [| apply ps_pos].
      rewrite Rabs_right; [| apply Rle_ge, ps_pos].
      apply Rle_ge.
      apply Rmult_le_compat_l; [apply ps_pos |].
      eapply Rle_trans.
      apply Rmin_list_minus_le_max_abs.
      now simpl; right.
    - simpl.
      apply Rle_trans with
          (r2 :=
             list_sum
               (map
                  (fun x0 : state M =>
                     (Max_{ fin_elms}(fun s : {x : state M & act M x} => Rabs (x s - y s))) 

                     * ps_P (preimage_singleton (next_state 0%nat sa) x0))
                  (@FiniteType.fin_elms 
                   (state M)
                   (@fin_finite_nodup (state M) (st_eqdec M) (fs M))))). 
      + simpl.
        apply list_sum_le.
        intros.
        setoid_rewrite Rmult_comm.
        rewrite Rmax_list_map_const_mul; [|apply ps_pos].
        apply Rmult_le_compat_l; [apply ps_pos |].
        apply Rmax_list_incl.
        * unfold act_list.
          destruct (M.(fa) a).
          specialize (fin_finite0 (na M a)).
          destruct fin_elms0; simpl in *; congruence.
        * intros ? HH.
          apply in_map_iff in HH.
          apply in_map_iff.
          destruct HH as [? [??]]; subst.
          eexists.
          now split; [reflexivity |].
      + rewrite <- map_map.
        rewrite list_sum_mult_const.
        rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l.
        * apply Rmax_list_Rabs_pos.
        * right.
          now generalize (frf_vals_prob_1 _ (next_state 0%nat sa)).
  Qed.

  Lemma qlearn_XF_contraction :
    0 <= β < 1 ->
    forall x y : Rfct {x : state M & act M x},
        Rmax_norm (sigT M.(act)) (Rfct_minus (sigT M.(act)) 
                                             (qlearn_XF x) (qlearn_XF y)) <=      
        β * Rmax_norm (sigT M.(act)) (Rfct_minus (sigT M.(act)) x y).
  Proof.
    intros.
    generalize (qlearn_XF_contraction0 H x y); intros.
    unfold Rmax_norm.
    match_destr.
    rewrite Rmax_list_le_iff.
    - intros.
      apply in_map_iff in H1.
      destruct H1 as [? [? ?]].
      specialize (H0 x1).
      unfold Rfct_minus in H1.
      rewrite H1 in H0.
      apply H0.
    - rewrite map_not_nil.
      generalize (M.(ne)); intros.
      red in X.
      generalize (M.(na) X); intros.
      red in X0.
      apply not_nil_exists.
      exists (existT _ X X0).
      apply fin_finite.
   Qed.

    Theorem qlearn
      (x' : Rfct (sigT M.(act)))
      (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F)
      (fixpt: qlearn_XF x' = x') :
    0 <= β < 1 ->
    (forall sa ω, is_lim_seq (sum_n (fun k => α k ω sa)) p_infty) ->
    (exists (C : R),
      forall sa,
        almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (α k ω sa)))) (Finite C))) ->

    let X := qlearn_Q in 
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) (x' sa)).
   Proof.
     intros.
     pose (H2 := 1).
     pose (w := fun t ω sa => qlearn_w (qlearn_Q) t ω sa (qlearn_Q_rv_dom t) (isfe_qlearn_Q t)).
     assert (rvXF : RandomVariable finfun_sa finfun_sa qlearn_XF).
     {
       apply rv_finfun_sa.
       intros.
       apply rvplus_rv; try typeclasses eauto.
       apply rvscale_rv.
       assert (rv2 : forall ω, RandomVariable dom borel_sa (fun v : Ts => qlearn_Qmin ω (next_state 0%nat sa v))).
       {
         intros.
         typeclasses eauto.
       } 
       eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)).
       {
         intros ?.
         rewrite (FiniteExpectation_simple _ _).
         now erewrite SimpleExpectation_compose.
       }
       apply list_sum_rv; intros; try typeclasses eauto.
       apply rvmult_rv; [| apply rvconst].
       unfold qlearn_Qmin.
       generalize (@rvs_Rmin_list (Rfct (sigT M.(act))) finfun_sa (map (fun a omega => omega (existT _ c a)) (act_list c))); intros HH.
       cut_to HH.
       - revert HH.
         apply RandomVariable_proper; try easy.
         intros ?.
         now rewrite map_map.
       - apply Forall_forall; intros.
         apply in_map_iff in H3.
         destruct H3 as [? [??]]; subst.
         apply finfun_sa_rv.
         apply id_rv.
     }
     assert (rvfinexp : forall k sa, RandomVariable (F (S k)) borel_sa
                                       (fun ω : Ts => FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0)))).
     {
       intros.
       assert (RandomVariable (F (S k)) borel_sa
                              (fun ω => list_sum (map (fun v : state M => qlearn_Qmin (qlearn_Q k ω) v * ps_P (preimage_singleton (next_state k sa) v))  (@fin_elms (state M) (@fin_finite_nodup (state M) (st_eqdec M) (fs M)))))).
       {
         apply list_sum_rv.
         intros.
         apply rvmult_rv.
         - apply rv_qmin1.
           + intros.
             apply (RandomVariable_sa_sub (isfilt k)).
             apply qlearn_Q_rv.
           + apply rvconst.
         - apply rvconst.
       }
       revert H3.
       apply RandomVariable_proper; try easy.
       intros ?.
       now rewrite FiniteExpectation_Qmin.
     }
     assert (rvfinexp' : forall k sa, RandomVariable dom borel_sa
                                       (fun ω : Ts => FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0)))).
     {
       intros.
       now apply (RandomVariable_sa_sub (filt_sub (S k))).
     }
     assert (rvw: forall (k : nat) (sa : {x : state M & act M x}),
                RandomVariable dom borel_sa (fun ω : Ts => w k ω sa)).
     {
       unfold w.
       unfold qlearn_w.
       intros.
       apply rvplus_rv.
       - typeclasses eauto.
       - apply rvscale_rv.
         unfold Rminus.
         apply rvplus_rv.
         + typeclasses eauto.
         + now apply rvopp_rv'.
     }
     assert (isfe_finexp: forall k sa,
                IsFiniteExpectation prts
                  (fun ω : Ts => FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0)))).
     {
       intros.
         generalize (@isfe_fubini_section_fst _ _ _ _ prts prts
                       (fun '(ω, ω0) =>
                          qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0)))
         ; intros HH.
         {
           assert (rvf: RandomVariable (product_sa dom dom) Rbar_borel_sa
                          (fun '(ω, ω0) => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))).
           {
             assert (RandomVariable (product_sa dom dom) borel_sa
                       (fun '(ω, ω0) => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))).
             {
               apply rv_qmin2; try easy.
               intros.
               typeclasses eauto.
               apply qlearn_next_state_rv2.
             }
             apply borel_Rbar_borel in H3.
             revert H3.
             apply RandomVariable_proper; try easy.
             intros ?.
             now destruct a.
           }
           

           assert (IsFiniteExpectation (product_ps prts prts)
                            (fun '(ω, ω0) => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))).
          {
            apply isfe_qmin2'; typeclasses eauto.
          }
           assert (isfef: Rbar_IsFiniteExpectation (product_ps prts prts)
                            (fun '(ω, ω0) => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))).
          {
            apply IsFiniteExpectation_Rbar in H3.
            revert H3.
            apply Rbar_IsFiniteExpectation_proper.
            intros ?.
            now destruct a.
         }
          specialize (HH _ _).
           revert HH.
           apply IsFiniteExpectation_proper; intros ?.
           rewrite <- FinExp_Rbar_FinExp.
           + now rewrite (Rbar_FiniteExpectation0_finite _ _ (isfe:= (@IsFiniteExpectation_Rbar Ts dom prts
                                                                      (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k a) (next_state k sa ω0))
                                                                      (isfe_qmin (qlearn_Q k a) k sa)))).
           + typeclasses eauto.
         }
     }
     assert (forall k sa, IsFiniteExpectation prts (fun ω : Ts => w k ω sa)).
     {
       intros.
       subst w.
       unfold qlearn_w.
       apply IsFiniteExpectation_plus.
       - typeclasses eauto.
       - typeclasses eauto.
       - apply IsFiniteExpectation_minus'; try typeclasses eauto.
         apply IsFiniteExpectation_const.
       - apply IsFiniteExpectation_scale.
         apply IsFiniteExpectation_minus'; try typeclasses eauto.
      }
     assert (forall n sa, RandomVariable (F n) borel_sa (fun ω : Ts => X n ω sa)).
     {
       intros.
       typeclasses eauto.
     }
     assert (forall n sa,  RandomVariable (F (S n)) (discrete_sa (state M)) (next_state n sa)).
     {
       intros.
       easy.
     }
     apply Tsitsiklis_1_3_fintype with 
         (w := w) (XF := (fun (k : nat) => qlearn_XF)) (rvw := rvw); try easy.
     - intros.
       subst w.
       unfold IsAdapted; intros.
       apply rvplus_rv.
       + typeclasses eauto.
       + apply rvscale_rv.
         apply rvminus_rv'; trivial.
         apply rv_qmin1; trivial.
         intros.
         now apply (RandomVariable_sa_sub (isfilt n)).
     - intros.
       now apply Condexp_cond_exp.
     - intros.
       subst w.
       unfold qlearn_w.
       apply almostR2_prob_space_sa_sub_lift with (sub := filt_sub k).
       generalize (Condexp_minus' prts (filt_sub k)
                     (fun ω => cost k sa ω) (fun _ => FiniteExpectation 
                                                                   (isfe := isfe_cost k sa)
                                                                   prts (cost k sa))
                     (rv1 := qlearn_cost_rv2 k sa) 
                     (isfe1 := isfe_cost k sa) 
                     (isfe2 := IsFiniteExpectation_const prts (FiniteExpectation 
                                                                 (isfe := isfe_cost k sa)
                                                                 prts (cost k sa)))
                  ); intros.
       generalize (@Condexp_plus _ _ prts _ (filt_sub k)
                     (fun ω : Ts =>
                        cost k sa ω - FiniteExpectation
                                          prts (cost k sa))
                     (fun ω => β *
                               (qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω) -
                                (FiniteExpectation prts 

                                   (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))))) _  _); intros.
       cut_to H7.
       generalize (is_conditional_expectation_independent_sa prts (filt_sub k) (cost k sa)); intros.
       cut_to H8.

       generalize (Condexp_cond_exp prts (filt_sub k) (cost k sa)); intros.
       generalize (is_conditional_expectation_unique prts (filt_sub k) (cost k sa)); intros.
       specialize (H10 _ _ _ _ _ (isfe_cost k sa) H8 H9).
       generalize (Condexp_scale prts (filt_sub k) β
                     (fun ω : Ts =>
                         (qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω) -
                            FiniteExpectation prts
                              (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))))); intros.

       assert (almostR2 (prob_space_sa_sub prts (filt_sub k)) eq
                 (ConditionalExpectation prts (filt_sub k)
                    (fun ω : Ts =>
                       qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω) -
                         FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))))
                 (const 0)).
       {
         generalize (Condexp_minus' prts (filt_sub k)
                       (fun ω : Ts =>
                          qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω))
                       (fun ω =>
                          FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0)))); intros.
         generalize (freezing_sa_alt (filt_sub k)
                       (pullback_rv_sub dom (discrete_sa (state M))
                          (next_state k sa) (qlearn_next_state_rv2 k sa))
                       (qlearn_Q k)
                       (next_state k sa)
                    ); intros.
         specialize (H13 (fun '(q, ns) => (qlearn_Qmin q ns)) _ ).
         assert (rvy : RandomVariable
                         (pullback_sa (discrete_sa (state M)) (next_state k sa))
                         (discrete_sa (state M)) (next_state k sa)).
         {
           apply pullback_rv.
         }
         assert  (rvPsi : RandomVariable (product_sa finfun_sa (discrete_sa (state M)))
                            borel_sa (fun '(q, ns) => qlearn_Qmin q ns)).
         {
           apply rv_qmin3.
         }
         rewrite H12; clear H12.
         specialize (H13 rvy rvPsi _ _ ).
         cut_to H13; [|apply independent_sas_comm, indep_next_state].
         destruct H13 as [_ H13].
         cut (almostR2 (prob_space_sa_sub prts (filt_sub k)) eq
                (ConditionalExpectation prts (filt_sub k)
                   (fun ω : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω)))
                (ConditionalExpectation prts (filt_sub k)
                   (fun ω : Ts =>
                      FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))))).
         {
           apply almost_impl; apply all_almost; intros ??.
           unfold Rbar_rvminus, Rbar_rvopp, Rbar_rvplus, const.
           rewrite <- H12.
           apply Rbar_plus_opp_zero.
         }
         simpl in H13.
         
         assert (eqq:almostR2 (prob_space_sa_sub prts (filt_sub k)) eq
                       (ConditionalExpectation prts (filt_sub k)
                          (fun ω : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω)))
                       (ConditionalExpectation prts (filt_sub k)
                          (FiniteConditionalExpectation prts (filt_sub k)
                             (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω0) (next_state k sa ω0))))).
         {
           apply all_almost; intros ?.
           symmetry.
           rewrite Condexp_id.
           - now rewrite (FiniteCondexp_eq _ _ _).
           - apply FiniteCondexp_rv.
         }
         rewrite eqq; clear eqq.
         apply Condexp_proper.
         apply almostR2_prob_space_sa_sub_lift with (sub := filt_sub k).
         revert H13.
         apply almost_impl.
         apply all_almost; intros ??.
         rewrite (FiniteCondexp_eq _ _ _) in H12.
         apply Rbar_finite_eq in H12.
         rewrite <- H12.
         apply FiniteConditionalExpectation_ext; reflexivity.
       }
       + revert H12; apply almost_impl.
         revert H11; apply almost_impl.
         revert H10; apply almost_impl.
         revert H7; apply almost_impl.
         revert H6; apply almost_impl.
         apply all_almost; intros ??????.
         unfold rvplus in H7.
         rewrite_condexp H7.
         replace (Finite (const 0 x)) with (Rbar_plus (Finite (const 0 x)) (Finite (const 0 x))) by now rewrite Rbar_plus_0_r.
         unfold Rbar_rvplus.
         f_equal.
         * etransitivity; [| etransitivity]; [| apply H6 |]; apply refl_refl.
           -- apply ConditionalExpectation_ext.
              reflexivity.
           -- unfold const.
              unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
              generalize (Condexp_const' prts (filt_sub k) 
                            (FiniteExpectation prts (cost k sa)) x); intros.
              rewrite H13.
              unfold const.
              unfold const in H10.
              repeat change (fun x => ?h x) with h.
              rewrite <- H10.
              simpl; f_equal.
              lra.
         * unfold rvscale in H11.
           rewrite H11.
           unfold Rbar_rvmult, const.
           replace (Finite 0) with (Rbar_mult β 0) by apply Rbar_mult_0_r.
           f_equal.
           rewrite H12.
           now unfold const.
       + apply indep_cost.
       + apply IsFiniteExpectation_minus'; try typeclasses eauto.
         apply IsFiniteExpectation_const.
       + apply IsFiniteExpectation_scale.
         apply IsFiniteExpectation_minus'; try typeclasses eauto.
     - unfold w.
       assert (isl2_qmin: forall k sa,
                  IsLp prts 2 (fun ω => (qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω)))).
       {
         typeclasses eauto.
       }
       
       assert (forall k,
                  RandomVariable (F k) borel_sa
                    (fun ω => (Rmax_all (fun sa => Rsqr (qlearn_Q k ω sa))))).
       {
         intros.
         apply rv_Rmax_all.
         intros.
         apply rvsqr_rv.
         apply H4.
       }
       (pose (Xmin := fun k sa ω => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω))).
       assert (forall k sa,
                  IsFiniteExpectation 
                    prts
                    (rvsqr
                       (rvminus (Xmin k sa)
                                (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa))))).
       {
         intros.

         generalize (FiniteConditionalVariance_exp_from_L2 prts (filt_sub k) (Xmin k sa) ); intros.
         revert H7.
         apply IsFiniteExpectation_proper.
         intros ?.
         rv_unfold.
         do 3 f_equal.
         unfold Xmin.
         apply FiniteConditionalExpectation_ext; reflexivity.
       }

       assert (forall k sa,
                  almostR2 prts Rle 
                           (FiniteConditionalExpectation 
                              prts (filt_sub k)
                              (rvsqr (rvminus 
                                        (Xmin k sa)
                                        (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa)))))
                           (fun ω => Rmax_all (fun sa => Rsqr (qlearn_Q k ω sa)))).
      {
        intros.
        assert (RandomVariable dom borel_sa (Xmin k sa)) by typeclasses eauto.
        assert (IsLp prts 2 (Xmin k sa)) by typeclasses eauto.
        assert (IsFiniteExpectation 
                  prts
                  (fun ω : Ts =>
                     Rmax_all (fun sa : {x : state M & act M x} => (qlearn_Q k ω sa)²))).
        {
          apply isfe_Rmax_all; intros; typeclasses eauto.
        }
        generalize (Finite_conditional_variance_bound_L2_fun 
                      prts (filt_sub k) (Xmin k sa)
                      (fun ω => (Rmax_all (fun sa => Rsqr (qlearn_Q k ω sa))))
                      ); intros.
        cut_to H11.
        - apply almost_prob_space_sa_sub_lift in H11.
          revert H11.
          apply almost_impl, all_almost; intros ??.
          etransitivity; [| etransitivity]; [| apply H11 |]; apply refl_refl.
          + apply FiniteConditionalExpectation_ext.
            intros ?.
            rv_unfold.
            do 3 f_equal.
            apply FiniteConditionalExpectation_ext; reflexivity.
          + reflexivity.
        - rv_unfold.
          unfold Rmax_all, Xmin, qlearn_Qmin.
          apply all_almost; intros ?.
          match_destr.
          assert (exists sa0,
                     Min_{ act_list (next_state k sa x)}
                         (fun a0 : act M (next_state k sa x) => qlearn_Q k x (existT (act M) (next_state k sa x) a0)) = qlearn_Q k x sa0).
         {
           generalize (Rmin_list_map_exist (fun a0 : act M (next_state k sa x) => qlearn_Q k x (existT (act M) (next_state k sa x) a0))  (act_list (next_state k sa x))); intros.
           cut_to H12.
           - destruct H12 as [? [? ?]].
             exists (existT _ _ x0).
             now rewrite <- H13.
           - apply act_list_not_nil.
         }
         destruct H12.
         rewrite H12.
         apply Rmax_spec.
         apply in_map_iff.
         exists x0.
         split; trivial.
      }
      generalize (fun k sa =>
                    nncondexp_sqr_sum_bound_nneg
                      prts
                      (filt_sub k)
                      (fun ω : Ts =>
                         cost k sa ω - FiniteExpectation prts (cost k sa))
                      (rvscale 
                         β 
                         (fun ω => (Xmin k sa ω) -
                                   (FiniteConditionalExpectation 
                                      prts (filt_sub k)
                                      (Xmin k sa) ω)))
                 ); intros.                           
      assert (forall k sa,
                 IsFiniteExpectation 
                   prts
                   (fun ω => Rsqr
                               ((cost k sa ω) -
                                (FiniteExpectation prts (cost k sa))))).
      {
        intros.
        generalize (isfe_variance_l2 prts (cost k sa) (qlearn_cost_rv2 k sa)).
        apply IsFiniteExpectation_proper.
        intros ?.
        rv_unfold'.
        do 2 f_equal.
        now apply FiniteExpectation_ext.
      }
      assert (exists A,
                 0 < A /\
                 forall k sa, 
                   FiniteExpectation prts 
                                     (fun ω => Rsqr
                                                 ((cost k sa ω) -
                                                  (FiniteExpectation prts (cost k sa))))
                   <=   A).
      {
        assert (forall k sa,
                   exists A,
                     FiniteExpectation prts 
                                     (fun ω => Rsqr
                                                 ((cost k sa ω) -
                                                  (FiniteExpectation prts (cost k sa))))
                   <=   A).
        {
          intros.
          unfold FiniteExpectation.
          unfold proj1_sig.
          match_destr.
          exists x; lra.
        }
        assert (exists A : R,
                   0 < A /\
                     (forall (sa : {x : state M & act M x}),
                         FiniteExpectation prts
                           (fun ω : Ts => (cost 0%nat sa ω - FiniteExpectation prts (cost 0%nat sa))²) <=  A)).
        {
          specialize (H11 0%nat).
          apply (finite_ex_choice _ (decA:=EqDecsigT)) in H11.
          destruct H11 as [l F2l].
          exists (Rabs (Rmax_list l) + 1).
          split.
          - unfold Rabs; match_destr; lra.
          - intros sa.
            apply Rle_trans with (r2:=Rmax_list l); [| unfold Rabs; match_destr; lra].
            destruct (Forall2_In_l F2l (a:=sa)) as [?[??]].
            + apply nodup_In; apply fin_finite.
            + eapply Rle_trans; try apply H12.
              now apply Rmax_spec.
        }
        destruct H12 as [? [? ?]].
        exists x.
        split; trivial.
        intros.
        eapply Rle_trans.
        shelve.
        apply (H13 sa).
        Unshelve.
        right.
        eapply ident_distr_finite_exp_eq.
        generalize (identically_distributed_sqr
                      (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa)))
                      (fun ω : Ts => (cost 0 sa ω - FiniteExpectation prts (cost 0%nat sa)))); intros.
        unfold compose in H14.
        cut_to H14.
        - revert H14.
          now apply identically_distributed_rvs_proper.
        - cut (identically_distributed_rvs prts borel_sa
                 (fun ω : Ts => cost k sa ω - FiniteExpectation prts (cost 0 sa))
                 (fun ω : Ts => cost 0 sa ω - FiniteExpectation prts (cost 0 sa))).
          + apply identically_distributed_rvs_proper; try reflexivity.
            intros ?.
            f_equal.
            eapply ident_distr_finite_exp_eq.
            apply identically_distributed_rvs_comm.
            generalize (ident_distr_cost k sa).
            now apply identically_distributed_rvs_proper.
          + generalize (identically_distributed_rv_compose prts borel_sa borel_sa
                          (cost k sa) (cost 0 sa) (fun x => x - FiniteExpectation prts (cost 0 sa)))
            ; intros HH.
            cut_to HH.
            * revert HH.
              now apply identically_distributed_rvs_proper.
            * apply identically_distributed_rvs_comm.
              generalize (ident_distr_cost k sa).
              now apply identically_distributed_rvs_proper.
      }
      destruct H11 as [A [? ?]].
      exists (2 * A); exists 2.
      split; try lra.
      split; try lra.
      intros.
      assert (almostR2 prts Rle
                     (FiniteConditionalExpectation 
                        prts (filt_sub k)
                        (rvscale (Rsqr β) 
                                 (rvsqr
                           (rvminus (Xmin k sa)
                                    (FiniteConditionalExpectation prts (filt_sub k) 
                                                                  (Xmin k sa))))))
                     (FiniteConditionalExpectation 
                        prts (filt_sub k)
                        (rvsqr
                           (rvminus (Xmin k sa)
                                    (FiniteConditionalExpectation prts (filt_sub k) 
                                                                  (Xmin k sa)))))).
      {
        apply almost_prob_space_sa_sub_lift with (sub := filt_sub k).
        apply FiniteCondexp_ale.
        apply all_almost; intros ?.
        rv_unfold.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat_r.
        - apply Rle_0_sqr.
        - unfold Rsqr.
          replace 1 with (1 * 1) by lra.
          apply Rmult_le_compat; lra.
      }
      specialize (H9 k sa).
      specialize (H8 k sa).
      specialize (H12 k sa).
      assert (freezn: almostR2  prts  eq
                  (fun ω => FiniteExpectation prts
                               (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0)))
                  (FiniteConditionalExpectation prts (filt_sub k)
                     (fun ω : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω)))).
      {
         generalize (freezing_sa_alt (filt_sub k)
                       (pullback_rv_sub dom (discrete_sa (state M))
                          (next_state k sa) (qlearn_next_state_rv2 k sa))
                       (qlearn_Q k)
                       (next_state k sa)
                    ); intros.
         specialize (H14 (fun '(q, ns) => (qlearn_Qmin q ns)) _ ).
         assert (rvy : RandomVariable
                         (pullback_sa (discrete_sa (state M)) (next_state k sa))
                         (discrete_sa (state M)) (next_state k sa)).
         {
           apply pullback_rv.
         }
         assert  (rvPsi : RandomVariable (product_sa finfun_sa (discrete_sa (state M)))
                            borel_sa (fun '(q, ns) => qlearn_Qmin q ns)).
         {
           apply rv_qmin3.
         }
         specialize (H14 rvy rvPsi _ _).
         cut_to H14; [|apply independent_sas_comm, indep_next_state].
         destruct H14 as [_ H14].
         apply almost_prob_space_sa_sub_lift with (sub := filt_sub k).
         revert H14.
         apply almost_impl, all_almost; intros ??.
         rewrite (FiniteCondexp_eq _ _ _) in H14.
         apply Rbar_finite_eq in H14.
         rewrite <- H14.
         apply FiniteConditionalExpectation_ext; intros ?; reflexivity.
      }
      assert (almostR2 (prob_space_sa_sub prts (filt_sub k)) eq
          (fun _ : Ts =>
           FiniteExpectation prts
             (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa))²))
          (fun x : Ts =>
           FiniteConditionalExpectation prts (filt_sub k)
             (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa))²) x)).
      {
        generalize (is_conditional_expectation_independent_sa prts (filt_sub k)
                      (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa))²)); intros.
              cut_to H14.
        - unfold const in H14.
          generalize (FiniteCondexp_is_cond_exp prts (filt_sub k)
                        (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa))²)
                     ); intros.
          generalize (is_conditional_expectation_unique prts (filt_sub k)); intros.
          assert (IsFiniteExpectation 
                    prts
                    (fun omega : Ts => (cost k sa omega - FiniteExpectation prts (cost k sa))²)) by easy.
          specialize (H16 _ _ _ _ _ _ H17 H14 H15).
          revert H16.
          apply almost_impl, all_almost; intros ??.
          now apply Rbar_finite_eq in H16.
        - specialize (indep_cost k sa).
          revert indep_cost.
          apply independent_sas_sub_proper; try easy.
          apply pullback_rv_sub.
          apply rvsqr_rv.
          unfold Rminus.
          apply rvplus_rv; try typeclasses eauto.
          apply pullback_rv.
      }
      etransitivity; [etransitivity |]; [| apply H9 |].
       + cut (almostR2 prts eq
                (ConditionalExpectation prts (filt_sub k)
                   (rvsqr
                      (fun ω : Ts =>
                         cost k sa ω - FiniteExpectation prts (cost k sa) +
                           β *
                             (qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω) -
                                FiniteExpectation prts
                                  (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))))))
                (NonNegCondexp prts (filt_sub k)
                   (rvsqr
                      (rvplus (fun ω : Ts => cost k sa ω - FiniteExpectation prts (cost k sa))
                         (rvscale β
                            (fun ω : Ts => Xmin k sa ω - FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa) ω)))))).
         {
           
           apply almostR2_subrelation.
           intros ???; subst; reflexivity.
         }
         rewrite (Condexp_nneg_simpl _ _ _).
         apply almost_prob_space_sa_sub_lift with (sub := filt_sub k).
         apply NonNegCondexp_proper.
         apply almostR2_eq_sqr_proper.
         apply almostR2_eq_plus_proper; try reflexivity.
         apply almostR2_eq_mult_proper; try reflexivity.
         unfold Xmin, Rminus.
         apply almostR2_eq_plus_proper; try reflexivity.
         apply almostR2_eq_opp'_proper.
         apply freezn.
       + clear freezn.
         revert H8; apply almost_impl.
         revert H9; apply almost_impl.
         revert H13; apply almost_impl.
         apply almost_prob_space_sa_sub_lift with (sub := filt_sub k) in H14.
         revert H14; apply almost_impl.
         apply all_almost; intros ?????.
         unfold rvplus, const, Rbar_rvmult, Rbar_rvplus.
         do 2 rewrite <- Condexp_nneg_simpl.
         do 2 erewrite FiniteCondexp_eq.
         simpl.
         rewrite Rmult_plus_distr_l.
         apply Rplus_le_compat.
         * apply Rmult_le_compat_l; try lra.
           unfold rvsqr.
           eapply Rle_trans; [| eapply Rle_trans]; [| apply H12 |]; try lra.
         * unfold rvscale.
           apply Rmult_le_compat_l; try lra.
           apply Rle_trans with
               (r2 := FiniteConditionalExpectation 
                        prts (filt_sub k)
                        (rvsqr
                           (rvminus (Xmin k sa)
                                    (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa)))) x ).
           -- unfold rvscale in *.
              eapply Rle_trans.
              shelve.
              apply H9.
              Unshelve.
              ++ apply IsFiniteExpectation_bounded with 
                     (rv_X1 := const 0)
                     (rv_X3 := rvsqr (rvminus (Xmin k sa) (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa)))); try typeclasses eauto.
                 ** intros ?.
                    rv_unfold.
                    apply Rle_0_sqr.
                 ** intros ?.
                    rv_unfold'.
                    unfold Xmin.
                    rewrite Rsqr_mult.
                    rewrite <- Rmult_1_l.
                    apply Rmult_le_compat_r.
                    --- apply Rle_0_sqr.
                    --- rewrite <- Rmult_1_l.
                        unfold Rsqr.
                        apply Rmult_le_compat; lra.
              ++ right.
                 apply FiniteConditionalExpectation_ext.
                 intros ?.
                 rv_unfold.
                 rewrite Rsqr_mult.
                 unfold Xmin.
                 do 2 f_equal.
                 lra.
           -- eapply Rle_trans.
              ++ apply H14.
              ++ unfold Rmax_norm, Rmax_all, X, rvmaxlist, Rmax_list_map.
                 match_destr.
                 apply Rmax_spec.
                 apply in_map_iff.
                 exists k.
                 split; trivial.
                 ** rewrite <- map_map.
                    rewrite Rmax_list_abs_sqr.
                    now rewrite map_map.
                 ** apply in_seq; lia.
     - intros.
       generalize (qlearn_XF_contraction H x x'); intros.
       rewrite fixpt in H6.
       apply H6.
     - intros.
       subst w X.
       unfold qlearn_XF, qlearn_w.
       simpl.
       do 2 f_equal.
       replace (FiniteExpectation prts (cost k sa)) with
         (FiniteExpectation prts (cost 0 sa)).
       ring_simplify.
       + replace
         (FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state k sa ω0))) with
         (FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q k ω) (next_state 0 sa ω0))); try lra.
         eapply ident_distr_finite_exp_eq.
         generalize (identically_distributed_rv_compose prts
                       (discrete_sa (state M))
                       borel_sa
                       (next_state 0%nat sa) 
                       (next_state k sa)
                       (qlearn_Qmin (qlearn_Q k ω))
                       (ident_distr_next_state k sa)).
         apply identically_distributed_rvs_proper; try easy.
       + eapply ident_distr_finite_exp_eq.
         generalize (ident_distr_cost k sa).
         now apply identically_distributed_rvs_proper.
   Qed.

(*
   Definition ps_P_nneg {T} {dom : SigmaAlgebra T} (ps : ProbSpace dom) (ev : event dom) :=
     mknonnegreal (ps_P (ProbSpace := ps) ev) (ps_pos _).

   Fixpoint policy_prob_s
     (d : forall (n:nat), vector (sigT M.(act)) n -> forall (s:state M), ProbSpace (discrete_sa (M.(act) s)))
     (p1 : ProbSpace (discrete_sa (M.(state))))
     (ns : sigT M.(act) -> ProbSpace (discrete_sa (M.(state)))) 
     (N : nat) : (vector (sigT M.(act)) N) -> state M -> nonnegreal :=
     match N with
     | 0 => fun v s => ps_P_nneg p1 (discrete_singleton s)
     | (S n) => fun v s =>
         let vn := vector_last v in
         mknonnegreal ((policy_prob_s d p1 ns n (vector_removelast v) (projT1 vn) ) *
                         (mknonnegreal
                            ((ps_P_nneg (d n (vector_removelast v) (projT1 vn)) (discrete_singleton (projT2 vn))) *
                               (ps_P_nneg (ns vn) (discrete_singleton s))) (prod_nonnegreal _ _)))
                           (prod_nonnegreal _ _)
     end.

   Fixpoint policy_prob_sa
     (d : forall (n:nat), vector (sigT M.(act)) n -> forall (s:state M), ProbSpace (discrete_sa (M.(act) s)))
     (p1 : ProbSpace (discrete_sa (M.(state))))
     (ns : sigT M.(act) -> ProbSpace (discrete_sa (M.(state)))) 
     (N : nat) : (vector (sigT M.(act)) N) -> sigT M.(act) -> nonnegreal :=
     match N with
     | 0 => fun v sa => mknonnegreal ((ps_P_nneg p1 (discrete_singleton (projT1 sa))) *
                                        (ps_P_nneg (d 0%nat v (projT1 sa)) (discrete_singleton (projT2 sa))))
                                     (prod_nonnegreal _ _)
     | (S n) => fun v sa =>
         let vn := vector_last v in
         mknonnegreal
           ((policy_prob_sa d p1 ns n (vector_removelast v) vn ) *
              (mknonnegreal 
                 ((ps_P_nneg (ns vn) (discrete_singleton (projT1 sa))) *
                    (ps_P_nneg (d (S n) v (projT1 sa)) (discrete_singleton (projT2 sa))))
                 (prod_nonnegreal _ _)))
           (prod_nonnegreal _ _)
     end.
  *)

   (*
   Instance dep_ps_product_ps {X : Type} {Y : Type} (A : SigmaAlgebra X) (B : SigmaAlgebra Y)
     (psA:ProbSpace A)
     (psB : forall a : X, ProbSpace B)
     (psB_rv: forall b : forall a : X, event B, RandomVariable A borel_sa (fun a : X => ps_P (ProbSpace:=psB a) (b a))) :
     ProbSpace (product_sa A B).
   Proof.
     generalize (@dep_product_ps X (const Y) A (const B) psA psB psB_rv); intros HH.
     generalize (pullback_ps _ (product_sa A B) HH); intros HH2.
     apply (HH2 (fun '(existT a b) => (a, b))).
     generalize dep_product_sa_sa; intros.
     unfold product_sa, dep_product_sa.
     intros ?.
     
*)
(*   
   (* d assumes that the vector is reversed.  The most recent history is at the beginning *)
   Program Fixpoint ivector_dep_prod n
     (d : forall (n:nat), ivector (sigT M.(act)) n -> forall (s:state M), ProbSpace (discrete_sa (M.(act) s)))
     (p1 : ProbSpace (discrete_sa (M.(state))))
     (ns : sigT M.(act) -> ProbSpace (discrete_sa (M.(state)))) 
     (N : nat) : ProbSpace (discrete_sa (ivector (sigT M.(act)) (S n)))
     := 
     match n with
     | 0%nat => _ (* dep_product_ps p1 (fun s => d 0%nat tt s) *)
     | S n => dep_product_ps (ivector_dep_prod n)
               (fun '(hd, tl) => (dep_product_ps  (fun s => d _ x s)))
               _ 
     end.

   *)

(*   Lemma puterman_5_5_1 (s0 : state M)
     (d : forall (n:nat), vector (sigT M.(act)) n -> forall (s:state M), ProbSpace (discrete_sa (M.(act) s))) :
     exists (d' : nat -> forall (s:state M), ProbSpace (discrete_sa (M.(act) s))),
     forall (p1 : ProbSpace (discrete_sa (M.(state))))
            (ns : sigT M.(act) -> ProbSpace (discrete_sa (M.(state))))
            (N : nat)
            (v : vector (sigT M.(act)) N),
       (forall s, policy_prob_s d p1 ns N v s = policy_prob_s (fun n v s => d' n s) p1 ns N v s) /\
       (forall sa, policy_prob_sa d p1 ns N v sa = policy_prob_sa (fun n v s => d' n s) p1 ns N v sa).
   Proof.
 *)

End MDP.

Section Jaakkola.
  Context {Ts : Type}            
          {dom : SigmaAlgebra Ts}
          {prts : ProbSpace dom}
          {M : MDP}

          {F : nat -> SigmaAlgebra Ts}
          (sa_seq : nat -> Ts -> sigT M.(act))
          (sa_seq_rv : forall t,
              RandomVariable (F t) (discrete_sa (sigT M.(act))) (fun ω => sa_seq t ω))
          (cost : nat -> (sigT M.(act)) -> Ts -> R)          
          (cost_rv : forall t sa, RandomVariable (F (S t)) borel_sa (cost t sa))
          (islp_cost: forall t (sa : {x : state M & act M x}),
              IsLp prts 2 (cost t sa))          
          (Q0 : Rfct (sigT M.(act)))
          (α : nat -> Ts -> Rfct (sigT M.(act)))

          (β : R)
          (beta_bound : 0 <= β < 1)
          (rvα : forall t sa,
              RandomVariable (F t) borel_sa (fun ω => α t ω sa))

          (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F)
          (alpha_lim1: forall sa ω, is_lim_seq (sum_n (fun k => α k ω sa)) p_infty)
          (alpha_lim2 :
            exists (C : R),
            forall sa,
              almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (α k ω sa)))) (Finite C)))
          (isfilt : IsFiltration F) 
          (filt_sub : forall k, sa_sub (F k) dom)
          (indep_cost: forall k sa,
              independent_sas prts (pullback_rv_sub dom borel_sa (cost k sa) 
                                      (RandomVariable_sa_sub (filt_sub (S k)) _))
                (filt_sub k))
          (ident_distr_cost: forall k sa,
              identically_distributed_rvs prts borel_sa
                (rv1 := (RandomVariable_sa_sub (filt_sub 1%nat) _))
                (rv2 := (RandomVariable_sa_sub (filt_sub (S k)) _))
                (cost 0%nat sa)
                (cost k sa)).

  Instance sa_seq_proj_rv :
    forall t,
      RandomVariable (F t) (discrete_sa (M.(state))) (fun ω => projT1 (sa_seq t ω)).
  Proof.
    intros.
    apply (compose_rv (sa_seq t)); trivial.
    apply discrete_sa_rv.
  Qed.

  Instance sa_seq_proj_rv2 :
    forall t,
      RandomVariable dom (discrete_sa (M.(state))) (fun ω => projT1 (sa_seq t ω)).
  Proof.
    intros.
    apply (RandomVariable_sa_sub (filt_sub t)).
    typeclasses eauto.
  Qed.

  Lemma FiniteType_eq_ext {A B} {finA:FiniteType A} {decA:EqDec A eq} (f g:A->B) :
    rv_eq f g -> f = g.
  Proof.
    intros.
    rewrite <- (iso_b_f f
                 (Isomorphism := finite_fun_vec_encoder finA decA (B := B))).
    rewrite <- (iso_b_f g
                 (Isomorphism := finite_fun_vec_encoder finA decA (B := B))).
    simpl.
    f_equal.
    apply vector_nth_eq; intros.
    unfold finite_fun_to_vector.
    now repeat rewrite vector_nth_map.
  Qed.
    
  Theorem qlearn_single_path
      (x' : Rfct (sigT M.(act)))
      (alpha_bound : forall t ω sa, 0 <= α t ω sa <= 1)
      (indep_next_state:  
        forall k,
          independent_sas prts
            (pullback_rv_sub dom (discrete_sa (state M)) 
               (fun ω : Ts => projT1 (sa_seq (S k) ω)) (sa_seq_proj_rv2 (S k))) 
            (filt_sub k))
      (ident_distr_next_state: forall k,
          identically_distributed_rvs prts (discrete_sa (state M)) 
            (fun ω : Ts => projT1 (sa_seq 1%nat ω))
            (fun ω : Ts => projT1 (sa_seq (S k) ω)))     :
   
    let next_state := (fun (t : nat) (sa : {x : state M & act M x}) (ω : Ts) => projT1 (sa_seq (S t) ω)) in
    let X := (qlearn_Q next_state cost Q0 α β) in
    let XF := (qlearn_XF next_state cost cost_rv islp_cost filt_sub β) in
    XF x' = x' ->
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) (x' sa)).
  Proof.
    intros.
    generalize (qlearn (M := M) next_state _); intros.
    specialize (H0 cost _ _ Q0 α alpha_bound _ _ filt_sub).
    cut_to H0; try easy.
    apply (H0 β _ x' _ H beta_bound alpha_lim1 alpha_lim2).
    - intros.
      generalize (indep_next_state k).
      now apply independent_sas_proper.      
    - intros.
      generalize (ident_distr_next_state k).
      now apply identically_distributed_rvs_proper.
  Qed.


(*
  Theorem qlearn_single_path_uniform_conv
      (x' : Rfct (sigT M.(act)))
      (alpha_bound : forall t ω sa, 0 <= α t ω sa)
      (indep_next_state:  
        forall k,
          independent_sas prts
            (pullback_rv_sub dom (discrete_sa (state M)) 
               (fun ω : Ts => projT1 (sa_seq (S k) ω)) (sa_seq_proj_rv2 (S k))) 
            (filt_sub k))
      (ident_distr_next_state: forall k,
          identically_distributed_rvs prts (discrete_sa (state M)) 
            (fun ω : Ts => projT1 (sa_seq 1%nat ω))
            (fun ω : Ts => projT1 (sa_seq (S k) ω)))     :
    (forall sa,
        is_lim_seq'_uniform_almost (fun n => fun ω => sum_n (fun k => Rsqr (α k ω sa)) n) 
          (fun ω => Lim_seq (sum_n (fun k => Rsqr (α k ω sa))))) ->
    let next_state := (fun (t : nat) (sa : {x : state M & act M x}) (ω : Ts) => projT1 (sa_seq (S t) ω)) in
    let X := (qlearn_Q next_state cost Q0 α β) in
    let XF := (qlearn_XF next_state cost cost_rv islp_cost filt_sub β) in
    XF x' = x' ->
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) (x' sa)).
 Proof.
   intros.
   *)

  Fixpoint qlearn_Q_single_path (t : nat) : (Ts -> Rfct (sigT M.(act)))    :=
           match t with
           | 0%nat => (fun ω  => Q0)
           | S t' => let g := qlearn_Q_single_path t' in 
                     (fun ω sa =>
                        (g ω sa) +
                          if (EqDecsigT sa (sa_seq t' ω))
                          then
                            (α t' ω sa) * ((cost t' sa ω) + β * (qlearn_Qmin (g ω) (projT1 (sa_seq t ω)))
                                                                   - (g ω sa))

                          else 0)
           end.

  Lemma qlearn_q_single_path_qlearn_Q :
    let next_state := (fun (t : nat) (sa : {x : state M & act M x}) (ω : Ts) => projT1 (sa_seq (S t) ω)) in
    let X := (qlearn_Q next_state cost Q0 α β) in
    (forall t ω sa, sa_seq t ω <> sa -> α t ω sa = 0) ->
    forall t ω sa,
      qlearn_Q_single_path t ω sa =
        X t ω sa.
   Proof.
     intros.
     revert sa.
     induction t.
     - now simpl.
     - intros.
       simpl.
       rewrite <- IHt.
       f_equal.
       specialize (H t ω sa).
       match_destr.
       + do 4 f_equal.
         unfold qlearn_Qmin.
         apply Rmin_list_Proper, refl_refl, map_ext.
         intros.
         now rewrite IHt.
       + symmetry in c.
         rewrite (H c).
         lra.
   Qed.

End Jaakkola.

Section Melo.
  
  Context {Ts : Type}            
          {dom : SigmaAlgebra Ts}
          {prts : ProbSpace dom}
          {M : MDP}

          {F : nat -> SigmaAlgebra Ts}
          (sa_seq : nat -> Ts -> sigT M.(act))
          (sa_seq_rv : forall t,
              RandomVariable (F t) (discrete_sa (sigT M.(act))) (fun ω => sa_seq t ω))
          (cost_fun : sigT M.(act) -> M.(state) -> R)
          (Q0 : Rfct (sigT M.(act)))
          (α : nat -> Ts -> Rfct (sigT M.(act)))

          (β : R)
          (alpha_bound : forall t ω sa, 0 <= α t ω sa <= 1)
          (beta_bound : 0 <= β < 1)
          (rvα : forall t sa,
              RandomVariable (F t) borel_sa (fun ω => α t ω sa))

          (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F)
          (alpha_lim1: forall sa ω, is_lim_seq (sum_n (fun k => α k ω sa)) p_infty)
          (alpha_lim2 :
            exists (C : R),
            forall sa,
              almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (α k ω sa)))) (Finite C)))
          (isfilt : IsFiltration F) 
          (filt_sub : forall k, sa_sub (F k) dom).

  Instance melo_sa_seq_proj_rv :
    forall t,
      RandomVariable (F t) (discrete_sa (M.(state))) (fun ω => projT1 (sa_seq t ω)).
  Proof.
    intros.
    apply (compose_rv (sa_seq t)); trivial.
    apply discrete_sa_rv.
  Qed.

  Instance melo_sa_seq_proj_rv2 :
    forall t,
      RandomVariable dom (discrete_sa (M.(state))) (fun ω => projT1 (sa_seq t ω)).
  Proof.
    intros.
    apply (RandomVariable_sa_sub (filt_sub t)).
    typeclasses eauto.
  Qed.

  Instance melo_sa_seq_rv2 :
    forall t,
      RandomVariable dom (discrete_sa (sigT M.(act))) (sa_seq t).
  Proof.
    intros.
    apply (RandomVariable_sa_sub (filt_sub t)).
    typeclasses eauto.
  Qed.

  Definition melo_cost k (sa : sigT M.(act)) ω :=
    cost_fun sa (projT1 (sa_seq (S k) ω)).

  (*
  Instance rv_countable_discrete_pair {T1 T2} {countable1:Countable T1} {countable2:Countable T2}
    {dom2} (rv1 : Ts -> T1) (rv2 : Ts -> T2) :
    RandomVariable dom2 (discrete_sa T1) rv1 ->
    RandomVariable dom2 (discrete_sa T2) rv2 ->
    RandomVariable dom2 (discrete_sa (T1 * T2)) (fun ω => (rv1 ω, rv2 ω)).
  Proof.
    intros.
    generalize (product_sa_rv rv1 rv2).
    apply RandomVariable_proper; try easy.
    apply countable_discrete_prod_prod.
  Qed.

  Instance rv_finitetype_discrete_pair {T1 T2} {dec1:EqDec T1 eq} {fin1:FiniteType T1} {dec2:EqDec T2 eq} {fin2:FiniteType T2}
    {dom2} (rv1 : Ts -> T1) (rv2 : Ts -> T2) :
    RandomVariable dom2 (discrete_sa T1) rv1 ->
    RandomVariable dom2 (discrete_sa T2) rv2 ->
    RandomVariable dom2 (discrete_sa (T1 * T2)) (fun ω => (rv1 ω, rv2 ω)).
  Proof.
    apply @rv_countable_discrete_pair
    ; now apply finite_countable.
  Qed.
  
  Instance rvpair_rv k :
    RandomVariable (F (S k)) (discrete_sa (sigT M.(act) * M.(state))) (fun ω => (sa_seq k ω, projT1 (sa_seq (S k) ω))).
  Proof.
    generalize (rv_finitetype_discrete_pair
                      (dec1:=EqDecsigT)
                      (dec2:=M.(st_eqdec))
                      (sa_seq k) (fun ω => projT1 (sa_seq (S k) ω)) (dom2 := F (S k))); intros.
    apply H.
    + now apply (RandomVariable_sa_sub (isfilt k)).
    + now apply (compose_rv (sa_seq (S k))).
  Qed.
  
  Instance rvpair_rv' k :
    RandomVariable dom (discrete_sa (sigT M.(act) * M.(state))) (fun ω => (sa_seq k ω, projT1 (sa_seq (S k) ω))).
  Proof.
    apply (RandomVariable_sa_sub (filt_sub (S k))).
    apply rvpair_rv.
  Qed.
  *)

  Instance melo_cost_rv k sa :
    RandomVariable (F (S k)) borel_sa (melo_cost k sa).
  Proof.
    pose (rv2 := fun ω => projT1 (sa_seq (S k) ω)).
    pose (cost2 := fun ns => cost_fun sa ns).
    assert (RandomVariable (F (S k)) borel_sa (compose cost2 rv2)).
    {
      typeclasses eauto.
    }
    revert H.
    now apply RandomVariable_proper.
  Qed.

  Instance melo_cost_rv2 k sa :
    RandomVariable dom borel_sa (melo_cost k sa).
  Proof.
    apply (RandomVariable_sa_sub (filt_sub (S k))).
    apply melo_cost_rv.
  Qed.

  Lemma frf_melo_cost k sa :
    FiniteRangeFunction (melo_cost k sa).
  Proof.
    pose (rv2 := fun ω => projT1 (sa_seq (S k) ω)).
    pose (cost2 := fun ns => cost_fun sa ns).
    assert (FiniteRangeFunction (compose cost2 rv2)).
    {
      apply FiniteRangeFunction_compose_after.
      apply FiniteRange_FiniteRangeFunction.
    }
    revert X.
    apply FiniteRangeFunction_ext.
    reflexivity.
  Qed.

  Instance islp_melo_cost k sa :
    IsLp prts 2 (melo_cost k sa).
  Proof.
    unfold IsLp.
    assert (IsFiniteExpectation prts
              (rvsqr (rvabs (melo_cost k sa)))).
    {
      assert (IsFiniteExpectation 
                prts
                (rvsqr (melo_cost k sa))).
      {
        generalize (FiniteRangeFunction_compose_after (melo_cost k sa) (C := R)); intros.
        specialize (X Rsqr (frf_melo_cost k sa)).
        apply IsFiniteExpectation_simple.
        - typeclasses eauto.
        - easy.
      }
      revert H.
      apply IsFiniteExpectation_proper.
      intros ?.
      unfold rvsqr, rvabs.
      now rewrite <- Rsqr_abs.
    }
    revert H.
    apply IsFiniteExpectation_proper.
    rewrite rvpower2; try reflexivity.
    apply nnfabs.
 Qed.
    
  Context
     (indep_next_state:  
        forall k,
          independent_sas prts
            (pullback_rv_sub dom (discrete_sa (M.(state))) 
               (fun ω : Ts => projT1 (sa_seq (S k) ω)) (melo_sa_seq_proj_rv2 (S k))) 
            (filt_sub k))
      (ident_distr_next_state: forall k,
          identically_distributed_rvs prts (discrete_sa (M.(state))) 
            (fun ω : Ts => projT1 (sa_seq 1%nat ω))
            (fun ω : Ts => projT1 (sa_seq (S k) ω))
      ).

  Lemma indep_melo_cost:
    forall k sa,
      independent_sas prts (pullback_rv_sub dom borel_sa (melo_cost k sa) 
                              (RandomVariable_sa_sub (filt_sub (S k)) _))
        (filt_sub k).
   Proof.
     intros.
     unfold melo_cost.
     pose (rv2 := fun ω => projT1 (sa_seq (S k) ω)).
     pose (cost2 := fun ns => cost_fun sa ns).
     assert (RandomVariable dom borel_sa (compose cost2 rv2)).
     {
       typeclasses eauto.
     }
     assert (independent_sas prts (pullback_rv_sub dom borel_sa (compose cost2 rv2) H)
                             (filt_sub k)).
     {
       specialize (indep_next_state k).
       revert indep_next_state.
       apply independent_sas_sub_proper; try easy.
       unfold rv2.
       rewrite pullback_sa_compose_equiv.
       apply pullback_sa_sub_proper; try easy.
     }
     revert H0.
     apply independent_sas_proper; try easy.
   Qed.

  Lemma ident_distr_melo_cost: forall k sa,
          identically_distributed_rvs prts borel_sa
            (rv1 := (RandomVariable_sa_sub (filt_sub 1%nat) _))
            (rv2 := (RandomVariable_sa_sub (filt_sub (S k)) _))
            (melo_cost 0%nat sa)
            (melo_cost k sa).
  Proof.
    intros.
    unfold melo_cost.
    pose (rv0 := fun ω => projT1 (sa_seq 1%nat ω)).
    pose (rv2 := fun ω => projT1 (sa_seq (S k) ω)).
    pose (cost2 := fun ns => cost_fun sa ns).
    specialize (ident_distr_next_state k).
    eapply identically_distributed_rv_compose with (codf := borel_sa) (f := cost2) in ident_distr_next_state.
    revert ident_distr_next_state.
    apply identically_distributed_rvs_proper; try easy.
    Unshelve.
    apply discrete_sa_rv.
  Qed.

  Theorem qlearn_single_path_melo
      (x' : Rfct (sigT M.(act))) :
    let next_state := (fun (t : nat) (sa : {x : state M & act M x}) (ω : Ts) => projT1 (sa_seq (S t) ω)) in
    let X := (qlearn_Q next_state melo_cost Q0 α β) in
    let XF := (qlearn_XF next_state melo_cost melo_cost_rv islp_melo_cost filt_sub β) in
    XF x' = x' ->
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) (x' sa)).
  Proof.
    intros.
    generalize (qlearn (M := M) next_state _); intros.
    specialize (H0 melo_cost _ _ Q0 α alpha_bound _ _ filt_sub).
    cut_to H0; try easy.
    apply (H0 β _ x' _ H beta_bound alpha_lim1 alpha_lim2).
    - intros.
      apply indep_melo_cost.
    - intros.
      generalize (indep_next_state k).
      now apply independent_sas_proper.      
    - intros.
      generalize (ident_distr_next_state k).
      now apply identically_distributed_rvs_proper.
    - intros.
      apply ident_distr_melo_cost.
  Qed.

  Fixpoint melo_qlearn_Q_single_path (t : nat) : (Ts -> Rfct (sigT M.(act)))    :=
           match t with
           | 0%nat => (fun ω  => Q0)
           | S t' => let g := melo_qlearn_Q_single_path t' in 
                     (fun ω sa =>
                        (g ω sa) +
                          if (EqDecsigT sa (sa_seq t' ω))
                          then
                            (α t' ω sa) * ((melo_cost t' sa ω) + β * (qlearn_Qmin (g ω) (projT1 (sa_seq t ω)))
                                                                   - (g ω sa))

                          else 0)
           end.

  Lemma melo_qlearn_q_single_path_qlearn_Q :
    let next_state := (fun (t : nat) (sa : {x : state M & act M x}) (ω : Ts) => projT1 (sa_seq (S t) ω)) in
    let X := (qlearn_Q next_state melo_cost Q0 α β) in
    (forall t ω sa, sa_seq t ω <> sa -> α t ω sa = 0) ->
    forall t ω sa,
      melo_qlearn_Q_single_path t ω sa =
        X t ω sa.
   Proof.
     intros.
     revert sa.
     induction t.
     - now simpl.
     - intros.
       simpl.
       rewrite <- IHt.
       f_equal.
       specialize (H t ω sa).
       match_destr.
       + do 4 f_equal.
         unfold qlearn_Qmin.
         apply Rmin_list_Proper, refl_refl, map_ext.
         intros.
         now rewrite IHt.
       + symmetry in c.
         rewrite (H c).
         lra.
   Qed.

End Melo.

