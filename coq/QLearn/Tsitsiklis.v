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

Lemma almost_isfe_condexp_sqr_bounded (dom2 : SigmaAlgebra Ts) (sub2: sa_sub dom2 dom) (B : R) 
      (w : Ts -> R)
      {rv : RandomVariable dom borel_sa w} :
  (almostR2 prts Rbar_le
    (ConditionalExpectation _ sub2 (rvsqr w))
    (const (Rsqr B))) ->
  IsFiniteExpectation prts (rvsqr w).
Proof.
  intros.
  assert (Rbar_IsFiniteExpectation prts (ConditionalExpectation _ sub2 (rvsqr w))).
  {
    apply Rbar_IsFiniteExpectation_nnf_bounded_almost with (g := const (Rsqr B)); trivial.
    - apply RandomVariable_sa_sub; trivial.
      apply Condexp_rv.
    - typeclasses eauto.
    - apply Condexp_nneg.
      typeclasses eauto.
    - apply Rbar_IsFiniteExpectation_const.
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

(*
 Definition process_swap (Y Z : nat -> Ts -> R) (T:Ts -> option nat) (n:nat) (x : Ts) : R
   := match (T x) with
      | None => Y n x
      | Some b =>
        if (lt_dec n b)%nat then Y n x else Z n x
      end.
 *)
  
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
  (exists (A : R),
       almost prts (fun ω => Rbar_lt (Lim_seq (@sum_n R_AbelianGroup (fun n : nat => rvsqr (α n) ω))) (Rbar.Finite A))) ->
  (almostR2 prts Rle (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const C)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (α n ω) * (w n ω)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  Admitted.


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
  assert (rvB: forall j t,
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
    apply almostR2_prob_space_sa_sub_lift in H9.
    revert H9.
    apply almost_impl.
    revert H0.
    apply almost_impl, all_almost.
    unfold impl; intros.
    rewrite H9.
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
    pose (b := Rmax x0 0).
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
      apply H6.
      rewrite INR_up_pos.
      + apply Rle_lt_trans with (r2 := b).
        * unfold b.
          apply Rmax_l.
        * apply (archimed b).
      + unfold b.
        apply Rle_ge.
        apply Rmax_r.
    - simpl.
      now red.
  }
  pose (wk k n := rvmult (w n) (IB k n)).
  pose (Wk := fix Wk k n ω :=
                match n with
                | 0%nat => W 0%nat ω
                | S n' =>
                  (1 - α n' ω) * (Wk k n' ω) + (α n' ω) * (wk k n' ω)
                end).
  assert (almost prts (fun ω => exists k, forall t,
                             Wk k t ω = W t ω)).
  {
    revert H9.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H9.
    exists x0.
    intros.
    unfold Wk.
    induction t; trivial.
    rewrite IHt.
    rewrite H5.
    unfold wk.
    unfold rvmult.
    rewrite H9.
    ring.
  }
  
  
  Admitted.

  
Lemma lemma1_bounded_alpha_beta (α β w W : nat -> Ts -> R) (Ca Cb B : R) 
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F} :    
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rle (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (const B)) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) ->
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) ->
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->  
  (almostR2 prts Rle (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const Ca)) ->
  (almostR2 prts Rle (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  Admitted.


Lemma lemma1_alpha_beta (α β w B W : nat -> Ts -> R) (W0 Ca Cb : R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {rv : forall n, RandomVariable dom borel_sa (w n)}
      {adaptB : IsAdapted borel_sa B F}
      {adaptw : IsAdapted borel_sa w (fun n => F (S n))}
      {adapta : IsAdapted borel_sa α F} 
      {adaptb : IsAdapted borel_sa β F} 
      {isfew2 : forall n, IsFiniteExpectation prts (rvsqr (w n))}
      {isfew : forall n, IsFiniteExpectation prts (w n)} :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (w n)) (const 0)) ->
  (forall (n:nat), almostR2 prts Rle (ConditionalExpectation _ (filt_sub n) (rvsqr (w n))) (B n)) ->  
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) ->
  (forall (n:nat), almostR2 prts Rle (const 0) (β n)) ->  
  (forall (n:nat), almostR2 prts Rle (α n) (const 1)) ->
  (forall (n:nat), almostR2 prts Rle (β n) (const 1)) ->  
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => α k ω)) p_infty)) ->
  (almost prts (fun ω => is_lim_seq (sum_n (fun k => β k ω)) p_infty)) ->  
  (almostR2 prts Rle (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const Ca)) ->
  (almostR2 prts Rle (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  (almost prts (fun ω => exists (b:R), forall n, B n ω <= b)) ->
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
      apply EventIndicator_rv with (dom := F t).
  }
(*  assert (isfef: forall t, IsFiniteExpectation prts (rvsqr (w t))) by admit. *)
  assert (isfefg : forall k t, IsFiniteExpectation prts
             (rvmult (rvsqr (w t)) (IB k t))).
  {
      intros.
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
    generalize (Condexp_factor_out prts (filt_sub t) 
                                   (rvsqr (w t)) (IB k t)); intros.
    apply almostR2_prob_space_sa_sub_lift in H13.
    revert H13.
    apply almost_impl.
    revert H0.
    apply almost_impl, all_almost.
    unfold impl; intros.
    rewrite H13.
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
    revert H10.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H10.
    pose (b := Rmax x0 0).
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
          apply Rmax_l.
        * apply (archimed b).
      + unfold b.
        apply Rle_ge.
        apply Rmax_r.
    - simpl.
      now red.
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
    specialize (isfefg k n).
    revert isfefg.
    apply IsFiniteExpectation_proper.
    intros ?.
    rv_unfold.
    unfold wk.
    rewrite Rsqr_mult.
    f_equal.
    unfold IB, Rsqr.
    match_destr; lra.
  }

  assert (isfewk : forall k n, IsFiniteExpectation prts (wk k  n)).
  {
    intros.
    now apply isfe_rsqr.
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
      now rewrite (ConditionalExpectation_ext prts (filt_sub n) _ _ H20) in H12.
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

Lemma Dvoretzky_converge_W  (W w: nat -> Ts -> R) (alpha : nat -> Ts -> R) 
      {F : nat -> SigmaAlgebra Ts} (isfilt : IsFiltration F) (filt_sub : forall n, sa_sub (F n) dom)
      {adaptZ : IsAdapted borel_sa W F} (adapt_alpha : IsAdapted borel_sa alpha F) 
      {rvw : forall n, RandomVariable dom borel_sa (w n)}

      {rvalpha : forall n, RandomVariable dom borel_sa (alpha n)}      
      (alpha_pos:forall n x, 0 <= alpha n x) 
      (alpha_one:forall n x, 0 <= 1 - alpha n x ) :
  (forall n,
      almostR2 (prob_space_sa_sub prts (filt_sub n)) eq
               (ConditionalExpectation prts (filt_sub n) (w n))
               (const 0)) ->
  (exists (C: R),
      (forall n,
          almostR2 (prob_space_sa_sub prts (filt_sub n)) Rbar_le
            (ConditionalExpectation prts (filt_sub n) (rvsqr (w n)))
            (const (Rsqr C)))) ->
   almost prts (fun omega : Ts => is_lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => alpha n omega)) 
                                                     Rbar.p_infty)  ->
   (exists (A2 : R),
       almost prts (fun omega => Rbar.Rbar_lt (Lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => rvsqr (alpha n) omega))) (Rbar.Finite A2))) ->
(*   (exists (sigma : R), forall n, rv_le (rvsqr (w n)) (const (Rsqr sigma))) -> *)
  rv_eq (W 0%nat) (const 0) ->
  (forall n, rv_eq (W (S n)) (rvplus (rvmult (rvminus (const 1) (alpha n)) (W n)) (rvmult (w n) (alpha n)))) ->
  almost _ (fun omega => is_lim_seq (fun n => W n omega) (Rbar.Finite 0)).
Proof.
  intros condexpw condexpw2 alpha_inf alpha_sqr W0 Wrel.

  assert (svy1: forall n : nat, IsFiniteExpectation prts (rvsqr (alpha n))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
    - apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_const.
    - intro z; rv_unfold.
      apply Rle_0_sqr.
    - intro z; rv_unfold.
      unfold Rsqr.
      replace (1) with (1 * 1) by lra.
      specialize (alpha_one n z).
      apply Rmult_le_compat; trivial; try lra.
  }
  assert (isfew2: forall n : nat, IsFiniteExpectation prts (rvsqr (w n) )).
  {
    intros.
    destruct condexpw2 as [C ?].
    specialize (H n).
    eapply almost_isfe_condexp_sqr_bounded with (sub2 := filt_sub n).
    apply almost_prob_space_sa_sub_lift with (sub := filt_sub n) in H.
    apply H.
  }

  assert (isfew : forall n, IsFiniteExpectation prts (w n)).
  {
    intros.
    now apply isfe_rsqr.
  }
      
  assert (isfemult : forall n, IsFiniteExpectation prts (rvmult (w n) (alpha n))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := rvmin (w n) (const 0))
                                           (rv_X3 := rvmax (w n) (const 0)); trivial.
    - apply IsFiniteExpectation_min; trivial.
      + apply rvconst.
      + apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_max; trivial.
      + apply rvconst.
      + apply IsFiniteExpectation_const.
    - intros ?.
      rv_unfold.
      specialize (alpha_pos n a).
      specialize (alpha_one n a).
      unfold Rmin.
      match_destr.
      + rewrite <- (Rmult_1_r (w n a)) at 1.
        apply Rmult_le_compat_neg_l; lra.
      + apply Rmult_le_pos; lra.
    - intros ?.
      rv_unfold.
      specialize (alpha_pos n a).
      specialize (alpha_one n a).
      unfold Rmax.
      match_destr.
      + apply Rmult_le_0_r; lra.
      + rewrite <- (Rmult_1_r (w n a)) at 2.
        apply Rmult_le_compat_l; lra.
  }
  
  assert (svy2 : forall n : nat, IsFiniteExpectation prts (rvsqr (rvmult (w n) (alpha n)))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := (const 0))
                                           (rv_X3 := (rvsqr (w n))); trivial.
    - apply IsFiniteExpectation_const.
    - intros ?.
      rv_unfold.
      apply Rle_0_sqr.
    - intros ?.
      rv_unfold.
      apply Rsqr_le_abs_1.
      rewrite <- (Rmult_1_r (Rabs (w n a))).
      rewrite Rabs_mult.
      specialize (alpha_one n a).
      specialize (alpha_pos n a).
      apply Rmult_le_compat_l.
      + apply Rabs_pos.
      + rewrite Rabs_right; lra.
  }
    
  assert (forall (n:nat) (x:Ts), 0 <= (fun n x => 0) n x).
  {
    intros.
    lra.
  }
  assert (forall n, RandomVariable dom borel_sa (rvmult (w n) (alpha n))).
  {
    intros.
    typeclasses eauto.
  }
  generalize (Dvoretzky_DS_extended_alt W (fun n => rvmult (w n) (alpha n)) 
                                        (fun n => rvmult (rvminus (const 1) (alpha n)) (W n)) 
                                        isfilt filt_sub H H alpha_pos H0 Wrel); intros.
  apply H1.
  - intros.
    assert (RandomVariable (F n) borel_sa (alpha n)) by apply adapt_alpha.
    generalize (ConditionalExpectation.Condexp_factor_out prts (filt_sub n) (w n) (alpha n)); intros.
    apply almost_prob_space_sa_sub_lift with (sub := filt_sub n).
    specialize (condexpw n).
    revert condexpw.
    apply almost_impl.
    revert H3.
    unfold almostR2.
    apply almost_impl, all_almost.
    intros; red; intros; red; intros.
    rewrite H3.
    unfold Rbar_rvmult.
    replace (Rbar.Finite (const 0 x)) with (Rbar.Rbar_mult  (Rbar.Finite (alpha n x)) (Rbar.Finite  (const 0 x))).
    + f_equal.
      rewrite <- H4.
      apply ConditionalExpectation.ConditionalExpectation_ext.
      now intro z.
    + unfold const.
      now rewrite Rbar.Rbar_mult_0_r.
  - intros ??.
    rv_unfold.
    unfold Rabs, Rmax.
    match_destr; match_destr.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 <= (1 + -1 * alpha n omega)).
      {
        specialize (alpha_one n omega).
        lra.
      }
      apply Rge_le in r0.
      generalize (Rmult_le_pos _ _ H2 r0).
      lra.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 <= (1 + -1 * alpha n omega)).
      {
        specialize (alpha_one n omega).
        lra.
      }
      apply Rlt_gt in r0.
      assert (W n omega <= 0) by lra.
      generalize (Rmult_le_ge_compat_neg_l _ _ _ H3 H2); intros.
      rewrite Rmult_0_r in H4.
      rewrite Rmult_comm in H4.
      lra.
  - destruct condexpw2 as [C ?].
    assert (forall n,
               FiniteExpectation prts (rvsqr (rvmult (w n) (alpha n))) 
               <= C^2 * FiniteExpectation prts (rvsqr (alpha n))).
    {
      intros.
      assert (RandomVariable (F n) borel_sa (rvsqr (alpha n))).
      {
        now apply rvsqr_rv.
      }
      assert (almostR2 (prob_space_sa_sub prts (filt_sub n)) Rbar_le
                        (ConditionalExpectation prts (filt_sub n) (rvmult (rvsqr (w n)) (rvsqr (alpha n))))
                        (Rbar_rvmult (rvsqr (alpha n)) (const (Rsqr C)))).
                                     
      {
        specialize (H2 n).
        revert H2.
        apply almost_impl.
        generalize (NonNegCondexp_factor_out prts (filt_sub n) (rvsqr (w n)) (rvsqr (alpha n))).
        apply almost_impl, all_almost.
        unfold impl; intros.
        rewrite <- Condexp_nneg_simpl in H2.
        rewrite H2.
        unfold Rbar_rvmult, const.
        apply Rbar_le_pos_compat_l.
        - apply nnfsqr.
        - rewrite <- Condexp_nneg_simpl.
          apply H4.
      }
      assert (almostR2 (prob_space_sa_sub prts (filt_sub n)) Rbar_le
                        (ConditionalExpectation prts (filt_sub n) (rvsqr (rvmult (w n) (alpha n))))
                        (Rbar_rvmult (rvsqr (alpha n)) (const (Rsqr C)))).
                                     
      {

        generalize (NonNegCondexp_factor_out prts (filt_sub n) (rvsqr (w n)) (rvsqr (alpha n))).
        apply almost_impl.
        specialize (H2 n).
        revert H2.
        apply almost_impl, all_almost.
        unfold impl; intros.
        assert (rv_eq (rvsqr (rvmult (w n) (alpha n)))
                      (rvmult (rvsqr (w n)) (rvsqr (alpha n)))).
        {
          intros ?.
          rv_unfold.
          unfold Rsqr.
          lra.
        }
        rewrite (ConditionalExpectation_ext prts (filt_sub n) _ _ H6).
        rewrite <- Condexp_nneg_simpl in H5.
        rewrite H5.
        unfold Rbar_rvmult, const.
        apply Rbar_le_pos_compat_l.
        - apply nnfsqr.
        - rewrite <- Condexp_nneg_simpl.
          apply H2.
      }
      assert (IsFiniteExpectation prts
                    (FiniteConditionalExpectation prts (filt_sub n) 
                                                  (rvsqr (rvmult (w n) (alpha n))))).
      {
        apply FiniteCondexp_isfe.
      }
      rewrite <- (FiniteCondexp_FiniteExpectation prts (filt_sub n)) with (isfe' := H6).
      rewrite <- Rsqr_pow2.
      rewrite <- FiniteExpectation_scale.
      apply FiniteExpectation_ale.
      - apply (RandomVariable_sa_sub (filt_sub n)).
        apply FiniteCondexp_rv.
      - typeclasses eauto.
      - apply almostR2_prob_space_sa_sub_lift in H5.
        revert H5.
        apply almost_impl, all_almost.
        unfold impl; intros.
        assert (Rbar_le (FiniteConditionalExpectation prts (filt_sub n) (rvsqr (rvmult (w n) (alpha n)))
                        x)
                        (rvscale C² (rvsqr (alpha n)) x)).
        {
          generalize (FiniteCondexp_eq prts (filt_sub n) (rvsqr (rvmult (w n) (alpha n)))); intros.
          apply (f_equal (fun a => a x)) in H7.
          rewrite <- H7.
          eapply Rbar_le_trans.
          apply H5.
          unfold Rbar_rvmult, rvscale, rvsqr, const, Rsqr.
          simpl.
          lra.
        }
        now simpl in H7.
    }
    apply (@Series.ex_series_le Hierarchy.R_AbsRing Hierarchy.R_CompleteNormedModule ) with 
        (b := fun n => C^2 * FiniteExpectation prts (rvsqr (alpha n))).
    + intros.
      unfold Hierarchy.norm; simpl.
      unfold Hierarchy.abs; simpl.
      rewrite Rabs_right.
      * eapply Rle_trans.
        apply H3.
        unfold pow; lra.
      * apply Rle_ge, (FiniteExpectation_sq_nneg prts (rvmult (w n) (alpha n)) (svy2 n)).
    + apply (@Series.ex_series_scal Hierarchy.R_AbsRing).
      rewrite <- ex_finite_lim_series.
      rewrite ex_finite_lim_seq_correct.
      split.
      * apply ex_lim_seq_incr.
        intros.
        apply sum_n_pos_incr; try lia.
        intros.
        apply FiniteExpectation_pos.
        typeclasses eauto.
      * generalize (sum_expectation prts (fun n => rvsqr (alpha n))); intros.
        assert (forall n, RandomVariable dom borel_sa (rvsqr (alpha n))).
        {
          intros.
          typeclasses eauto.
        }
        specialize (H4 H5 svy1).
        rewrite (Lim_seq_ext _ _ H4).
        destruct alpha_sqr as [A2 alpha_sqr].
        generalize (Dominated_convergence_almost 
                      prts 
                      (fun n omega => Rbar.Finite (rvsum (fun n0 => rvsqr (alpha n0)) n omega))
                      (Rbar_rvlim (fun n omega => Rbar.Finite (rvsum (fun n0 => rvsqr (alpha n0)) n omega)))
                   ); intros.
        specialize (H6 (const (Rbar.Finite A2))).
        cut_to H6.
        -- assert  (isfefn : forall n : nat,
                   Rbar_IsFiniteExpectation prts
                     (fun omega : Ts =>
                      Rbar.Finite
                        (rvsum (fun n0 : nat => rvsqr (alpha n0)) n omega))).
           { 
             intros.
             apply Rbar_IsFiniteExpectation_nnf_bounded_almost with
                 (g := const (Rbar.Finite A2)).
             - typeclasses eauto.
             - typeclasses eauto.
             - typeclasses eauto.
             - revert alpha_sqr.
               apply almost_impl, all_almost.
               intros; red; intros.
               simpl.
               unfold rvsum.
               left.
               generalize (Lim_seq_increasing_le
                             (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n0 : nat => rvsqr (alpha n0) x))); intros.
                 cut_to H8.
                 --- specialize (H8 n).
                     generalize (Rbar.Rbar_le_lt_trans _ _ _ H8 H7); intros.
                     simpl in H9; lra.
                 --- intros.
                     apply sum_n_pos_incr; try lia.                     
                     intros.
                     apply nnfsqr.
             - apply Rbar_IsFiniteExpectation_const.
           }
           assert
             (isfe : Rbar_IsFiniteExpectation prts
                   (Rbar_rvlim
                      (fun (n : nat) (omega : Ts) =>
                       Rbar.Finite
                         (rvsum (fun n0 : nat => rvsqr (alpha n0)) n omega)))).
           {
             apply Rbar_IsFiniteExpectation_nnf_bounded_almost with
                 (g := const (Rbar.Finite A2)).
             - typeclasses eauto.
             - typeclasses eauto.
             - typeclasses eauto.
             - revert alpha_sqr.
               apply almost_impl, all_almost.
               intros; red; intros.
               unfold Rbar_rvlim.
               rewrite Elim_seq_fin.
               unfold const, rvsum.
               now apply Rbar.Rbar_lt_le.
             - apply Rbar_IsFiniteExpectation_const.
           }
           specialize (H6 isfefn isfe).
           apply is_lim_seq_unique in H6.
           ++ rewrite Lim_seq_ext with
                  (v :=  (fun n : nat =>
                            Rbar_FiniteExpectation 
                              prts
                              (fun omega : Ts =>
                                 Rbar.Finite (rvsum (fun n0 : nat => rvsqr (alpha n0)) n omega)))).
              ** rewrite H6.
                 now simpl.
              ** intros.
                 rewrite <- FinExp_Rbar_FinExp.
                 --- apply Rbar_FiniteExpectation_ext.
                     now intro z.
                 --- typeclasses eauto.
           ++ apply Rbar_IsFiniteExpectation_const.
           ++ intros.
              revert alpha_sqr.
              unfold almostR2.
              apply almost_impl, all_almost.
              intros; red; intros.
              unfold Rbar_rvabs, const.
              simpl.
              unfold rvsum.
              rewrite Rabs_right.
              ** generalize (Lim_seq_increasing_le (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n0 : nat => rvsqr (alpha n0) x))); intros.
                 cut_to H8.
                 --- specialize (H8 n).
                     generalize (Rbar.Rbar_le_lt_trans _ _ _ H8 H7); intros.
                     simpl in H9; lra.
                 --- intros.
                     apply sum_n_pos_incr; try lia.                     
                     intros.
                     apply nnfsqr.
              ** apply Rle_ge, sum_n_nneg.
                 intros.
                 apply nnfsqr.
           ++ apply all_almost.
              intros.
              unfold Rbar_rvlim.
              apply ELim_seq_correct.
              rewrite ex_Elim_seq_fin.
              apply ex_lim_seq_incr.
              intros.
              apply sum_n_pos_incr; try lia.
              intros.
              apply nnfsqr.
        -- intros.
           typeclasses eauto.
        -- typeclasses eauto.
        -- typeclasses eauto.
  - apply all_almost; intros.
    apply is_lim_seq_const.
  - apply all_almost; intros.
    apply ex_series_const0.
  - trivial.
 Qed.

Lemma Dvoretzky_converge_W_alpha_beta  (W w: nat -> Ts -> R) (alpha beta : nat -> Ts -> R) 
      {F : nat -> SigmaAlgebra Ts} (isfilt : IsFiltration F) (filt_sub : forall n, sa_sub (F n) dom)
      {adaptZ : IsAdapted borel_sa W F} (adapt_alpha : IsAdapted borel_sa alpha F)
      (adapt_beta : IsAdapted borel_sa beta F) 
      {rvw : forall n, RandomVariable dom borel_sa (w n)}

      {rvalpha : forall n, RandomVariable dom borel_sa (alpha n)}
      {rvbeta : forall n, RandomVariable dom borel_sa (beta n)}            
      (alpha_pos:forall n x, 0 <= alpha n x)
      (alpha_one:forall n x, 0 <= 1 - alpha n x ) 
      (beta_pos:forall n x, 0 <= beta n x)
      (beta_one:forall n x, 0 <= 1 - beta n x ) :
  (forall n,
      almostR2 (prob_space_sa_sub prts (filt_sub n)) eq
               (ConditionalExpectation prts (filt_sub n) (w n))
               (const 0)) ->
  (exists (C: R),
      (forall n,
          almostR2 (prob_space_sa_sub prts (filt_sub n)) Rbar_le
            (ConditionalExpectation prts (filt_sub n) (rvsqr (w n)))
            (const (Rsqr C)))) ->
   almost prts (fun omega : Ts => is_lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => alpha n omega)) 
                                                     Rbar.p_infty)  ->
   almost prts (fun omega : Ts => is_lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => beta n omega)) 
                                                     Rbar.p_infty)  ->
   (exists (A2 : R),
       almost prts (fun omega => Rbar.Rbar_lt (Lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => rvsqr (alpha n) omega))) (Rbar.Finite A2))) ->

   (exists (A3 : R),
       almost prts (fun omega => Rbar.Rbar_lt (Lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => rvsqr (beta n) omega))) (Rbar.Finite A3))) ->

(*   (exists (sigma : R), forall n, rv_le (rvsqr (w n)) (const (Rsqr sigma))) -> *)
  rv_eq (W 0%nat) (const 0) ->
  (forall n, rv_eq (W (S n)) (rvplus (rvmult (rvminus (const 1) (alpha n)) (W n)) (rvmult (w n) (beta n)))) ->
  almost _ (fun omega => is_lim_seq (fun n => W n omega) (Rbar.Finite 0)).
Proof.
  intros condexpw condexpw2 alpha_inf beta_inf alpha_sqr beta_sqr W0 Wrel.

  assert (svy1: forall n : nat, IsFiniteExpectation prts (rvsqr (alpha n))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
    - apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_const.
    - intro z; rv_unfold.
      apply Rle_0_sqr.
    - intro z; rv_unfold.
      unfold Rsqr.
      replace (1) with (1 * 1) by lra.
      specialize (alpha_one n z).
      apply Rmult_le_compat; trivial; try lra.
  }
  assert (svy1b: forall n : nat, IsFiniteExpectation prts (rvsqr (beta n))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
    - apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_const.
    - intro z; rv_unfold.
      apply Rle_0_sqr.
    - intro z; rv_unfold.
      unfold Rsqr.
      replace (1) with (1 * 1) by lra.
      specialize (beta_one n z).
      apply Rmult_le_compat; trivial; try lra.
  }

  assert (isfew2: forall n : nat, IsFiniteExpectation prts (rvsqr (w n) )).
  {
    intros.
    destruct condexpw2 as [C ?].
    specialize (H n).
    eapply almost_isfe_condexp_sqr_bounded with (sub2 := filt_sub n).
    apply almost_prob_space_sa_sub_lift with (sub := filt_sub n) in H.
    apply H.
  }

  assert (isfew : forall n, IsFiniteExpectation prts (w n)).
  {
    intros.
    now apply isfe_rsqr.
  }
      
  assert (isfemult : forall n, IsFiniteExpectation prts (rvmult (w n) (beta n))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := rvmin (w n) (const 0))
                                           (rv_X3 := rvmax (w n) (const 0)); trivial.
    - apply IsFiniteExpectation_min; trivial.
      + apply rvconst.
      + apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_max; trivial.
      + apply rvconst.
      + apply IsFiniteExpectation_const.
    - intros ?.
      rv_unfold.
      specialize (beta_pos n a).
      specialize (beta_one n a).
      unfold Rmin.
      match_destr.
      + rewrite <- (Rmult_1_r (w n a)) at 1.
        apply Rmult_le_compat_neg_l; lra.
      + apply Rmult_le_pos; lra.
    - intros ?.
      rv_unfold.
      specialize (beta_pos n a).
      specialize (beta_one n a).
      unfold Rmax.
      match_destr.
      + apply Rmult_le_0_r; lra.
      + rewrite <- (Rmult_1_r (w n a)) at 2.
        apply Rmult_le_compat_l; lra.
  }
  
  assert (svy2 : forall n : nat, IsFiniteExpectation prts (rvsqr (rvmult (w n) (alpha n)))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := (const 0))
                                           (rv_X3 := (rvsqr (w n))); trivial.
    - apply IsFiniteExpectation_const.
    - intros ?.
      rv_unfold.
      apply Rle_0_sqr.
    - intros ?.
      rv_unfold.
      apply Rsqr_le_abs_1.
      rewrite <- (Rmult_1_r (Rabs (w n a))).
      rewrite Rabs_mult.
      specialize (alpha_one n a).
      specialize (alpha_pos n a).
      apply Rmult_le_compat_l.
      + apply Rabs_pos.
      + rewrite Rabs_right; lra.
  }
    
  assert (svy2b : forall n : nat, IsFiniteExpectation prts (rvsqr (rvmult (w n) (beta n)))).
  {
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := (const 0))
                                           (rv_X3 := (rvsqr (w n))); trivial.
    - apply IsFiniteExpectation_const.
    - intros ?.

      rv_unfold.
      apply Rle_0_sqr.
    - intros ?.
      rv_unfold.
      apply Rsqr_le_abs_1.
      rewrite <- (Rmult_1_r (Rabs (w n a))).
      rewrite Rabs_mult.
      specialize (beta_one n a).
      specialize (beta_pos n a).
      apply Rmult_le_compat_l.
      + apply Rabs_pos.
      + rewrite Rabs_right; lra.
  }

  assert (forall (n:nat) (x:Ts), 0 <= (fun n x => 0) n x).
  {
    intros.
    lra.
  }
  assert (forall n, RandomVariable dom borel_sa (rvmult (w n) (beta n))).
  {
    intros.
    typeclasses eauto.
  }
  generalize (Dvoretzky_DS_extended_alt W (fun n => rvmult (w n) (beta n)) 
                                        (fun n => rvmult (rvminus (const 1) (alpha n)) (W n))
             isfilt filt_sub H H alpha_pos H0 Wrel); intros.
  apply H1.
  - intros.
    assert (RandomVariable (F n) borel_sa (beta n)) by apply adapt_beta.
    generalize (ConditionalExpectation.Condexp_factor_out prts (filt_sub n) (w n) (beta n)); intros.
    apply almost_prob_space_sa_sub_lift with (sub := filt_sub n).
    specialize (condexpw n).
    revert condexpw.
    apply almost_impl.
    revert H3.
    unfold almostR2.
    apply almost_impl, all_almost.
    intros; red; intros; red; intros.
    rewrite H3.
    unfold Rbar_rvmult.
    replace (Rbar.Finite (const 0 x)) with (Rbar.Rbar_mult  (Rbar.Finite (beta n x)) (Rbar.Finite  (const 0 x))).
    + f_equal.
      rewrite <- H4.
      apply ConditionalExpectation.ConditionalExpectation_ext.
      now intro z.
    + unfold const.
      now rewrite Rbar.Rbar_mult_0_r.
  - intros ??.
    rv_unfold.
    unfold Rabs, Rmax.
    match_destr; match_destr.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 <= (1 + -1 * alpha n omega)).
      {
        specialize (alpha_one n omega).
        lra.
      }
      apply Rge_le in r0.
      generalize (Rmult_le_pos _ _ H2 r0).
      lra.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 <= (1 + -1 * alpha n omega)).
      {
        specialize (alpha_one n omega).
        lra.
      }
      apply Rlt_gt in r0.
      assert (W n omega <= 0) by lra.
      generalize (Rmult_le_ge_compat_neg_l _ _ _ H3 H2); intros.
      rewrite Rmult_0_r in H4.
      rewrite Rmult_comm in H4.
      lra.
  - destruct condexpw2 as [C ?].
    assert (forall n,
               FiniteExpectation prts (rvsqr (rvmult (w n) (beta n))) 
               <= C^2 * FiniteExpectation prts (rvsqr (beta n))).
    {
      intros.
      assert (RandomVariable (F n) borel_sa (rvsqr (beta n))).
      {
        now apply rvsqr_rv.
      }
      assert (almostR2 (prob_space_sa_sub prts (filt_sub n)) Rbar_le
                        (ConditionalExpectation prts (filt_sub n) (rvmult (rvsqr (w n)) (rvsqr (beta n))))
                        (Rbar_rvmult (rvsqr (beta n)) (const (Rsqr C)))).
                                     
      {
        specialize (H2 n).
        revert H2.
        apply almost_impl.
        generalize (NonNegCondexp_factor_out prts (filt_sub n) (rvsqr (w n)) (rvsqr (beta n))).
        apply almost_impl, all_almost.
        unfold impl; intros.
        rewrite <- Condexp_nneg_simpl in H2.
        rewrite H2.
        unfold Rbar_rvmult, const.
        apply Rbar_le_pos_compat_l.
        - apply nnfsqr.
        - rewrite <- Condexp_nneg_simpl.
          apply H4.
      }
      assert (almostR2 (prob_space_sa_sub prts (filt_sub n)) Rbar_le
                        (ConditionalExpectation prts (filt_sub n) (rvsqr (rvmult (w n) (beta n))))
                        (Rbar_rvmult (rvsqr (beta n)) (const (Rsqr C)))).
                                     
      {

        generalize (NonNegCondexp_factor_out prts (filt_sub n) (rvsqr (w n)) (rvsqr (beta n))).
        apply almost_impl.
        specialize (H2 n).
        revert H2.
        apply almost_impl, all_almost.
        unfold impl; intros.
        assert (rv_eq (rvsqr (rvmult (w n) (beta n)))
                      (rvmult (rvsqr (w n)) (rvsqr (beta n)))).
        {
          intros ?.
          rv_unfold.
          unfold Rsqr.
          lra.
        }
        rewrite (ConditionalExpectation_ext prts (filt_sub n) _ _ H6).
        rewrite <- Condexp_nneg_simpl in H5.
        rewrite H5.
        unfold Rbar_rvmult, const.
        apply Rbar_le_pos_compat_l.
        - apply nnfsqr.
        - rewrite <- Condexp_nneg_simpl.
          apply H2.
      }
      assert (IsFiniteExpectation prts
                    (FiniteConditionalExpectation prts (filt_sub n) 
                                                  (rvsqr (rvmult (w n) (beta n))))).
      {
        apply FiniteCondexp_isfe.
      }
      rewrite <- (FiniteCondexp_FiniteExpectation prts (filt_sub n)) with (isfe' := H6).
      rewrite <- Rsqr_pow2.
      rewrite <- FiniteExpectation_scale.
      apply FiniteExpectation_ale.
      - apply (RandomVariable_sa_sub (filt_sub n)).
        apply FiniteCondexp_rv.
      - typeclasses eauto.
      - apply almostR2_prob_space_sa_sub_lift in H5.
        revert H5.
        apply almost_impl, all_almost.
        unfold impl; intros.
        assert (Rbar_le (FiniteConditionalExpectation prts (filt_sub n) (rvsqr (rvmult (w n) (beta n)))
                        x)
                        (rvscale C² (rvsqr (beta n)) x)).
        {
          generalize (FiniteCondexp_eq prts (filt_sub n) (rvsqr (rvmult (w n) (beta n)))); intros.
          apply (f_equal (fun a => a x)) in H7.
          rewrite <- H7.
          eapply Rbar_le_trans.
          apply H5.
          unfold Rbar_rvmult, rvscale, rvsqr, const, Rsqr.
          simpl.
          lra.
        }
        now simpl in H7.
    }
    apply (@Series.ex_series_le Hierarchy.R_AbsRing Hierarchy.R_CompleteNormedModule ) with 
        (b := fun n => C^2 * FiniteExpectation prts (rvsqr (beta n))).
    + intros.
      unfold Hierarchy.norm; simpl.
      unfold Hierarchy.abs; simpl.
      rewrite Rabs_right.
      * eapply Rle_trans.
        apply H3.
        unfold pow; lra.
      * apply Rle_ge, (FiniteExpectation_sq_nneg prts (rvmult (w n) (beta n)) (svy2b n)).
    + apply (@Series.ex_series_scal Hierarchy.R_AbsRing).
      rewrite <- ex_finite_lim_series.
      rewrite ex_finite_lim_seq_correct.
      split.
      * apply ex_lim_seq_incr.
        intros.
        apply sum_n_pos_incr; try lia.
        intros.
        apply FiniteExpectation_pos.
        typeclasses eauto.
      * generalize (sum_expectation prts (fun n => rvsqr (beta n))); intros.
        assert (forall n, RandomVariable dom borel_sa (rvsqr (beta n))).
        {
          intros.
          typeclasses eauto.
        }
        specialize (H4 H5 svy1b).
        rewrite (Lim_seq_ext _ _ H4).
        destruct beta_sqr as [A2 beta_sqr].
        generalize (Dominated_convergence_almost 
                      prts 
                      (fun n omega => Rbar.Finite (rvsum (fun n0 => rvsqr (beta n0)) n omega))
                      (Rbar_rvlim (fun n omega => Rbar.Finite (rvsum (fun n0 => rvsqr (beta n0)) n omega)))
                   ); intros.
        specialize (H6 (const (Rbar.Finite A2))).
        cut_to H6.
        -- assert  (isfefn : forall n : nat,
                   Rbar_IsFiniteExpectation prts
                     (fun omega : Ts =>
                      Rbar.Finite
                        (rvsum (fun n0 : nat => rvsqr (beta n0)) n omega))).
           { 
             intros.
             apply Rbar_IsFiniteExpectation_nnf_bounded_almost with
                 (g := const (Rbar.Finite A2)).
             - typeclasses eauto.
             - typeclasses eauto.
             - typeclasses eauto.
             - revert beta_sqr.
               apply almost_impl, all_almost.
               intros; red; intros.
               simpl.
               unfold rvsum.
               left.
               generalize (Lim_seq_increasing_le
                             (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n0 : nat => rvsqr (beta n0) x))); intros.
                 cut_to H8.
                 --- specialize (H8 n).
                     generalize (Rbar.Rbar_le_lt_trans _ _ _ H8 H7); intros.
                     simpl in H9; lra.
                 --- intros.
                     apply sum_n_pos_incr; try lia.                     
                     intros.
                     apply nnfsqr.
             - apply Rbar_IsFiniteExpectation_const.
           }
           assert
             (isfe : Rbar_IsFiniteExpectation prts
                   (Rbar_rvlim
                      (fun (n : nat) (omega : Ts) =>
                       Rbar.Finite
                         (rvsum (fun n0 : nat => rvsqr (beta n0)) n omega)))).
           {
             apply Rbar_IsFiniteExpectation_nnf_bounded_almost with
                 (g := const (Rbar.Finite A2)).
             - typeclasses eauto.
             - typeclasses eauto.
             - typeclasses eauto.
             - revert beta_sqr.
               apply almost_impl, all_almost.
               intros; red; intros.
               unfold Rbar_rvlim.
               rewrite Elim_seq_fin.
               unfold const, rvsum.
               now apply Rbar.Rbar_lt_le.
             - apply Rbar_IsFiniteExpectation_const.
           }
           specialize (H6 isfefn isfe).
           apply is_lim_seq_unique in H6.
           ++ rewrite Lim_seq_ext with
                  (v :=  (fun n : nat =>
                            Rbar_FiniteExpectation 
                              prts
                              (fun omega : Ts =>
                                 Rbar.Finite (rvsum (fun n0 : nat => rvsqr (beta n0)) n omega)))).
              ** rewrite H6.
                 now simpl.
              ** intros.
                 rewrite <- FinExp_Rbar_FinExp.
                 --- apply Rbar_FiniteExpectation_ext.
                     now intro z.
                 --- typeclasses eauto.
           ++ apply Rbar_IsFiniteExpectation_const.
           ++ intros.
              revert beta_sqr.
              unfold almostR2.
              apply almost_impl, all_almost.
              intros; red; intros.
              unfold Rbar_rvabs, const.
              simpl.
              unfold rvsum.
              rewrite Rabs_right.
              ** generalize (Lim_seq_increasing_le (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n0 : nat => rvsqr (beta n0) x))); intros.
                 cut_to H8.
                 --- specialize (H8 n).
                     generalize (Rbar.Rbar_le_lt_trans _ _ _ H8 H7); intros.
                     simpl in H9; lra.
                 --- intros.
                     apply sum_n_pos_incr; try lia.                     
                     intros.
                     apply nnfsqr.
              ** apply Rle_ge, sum_n_nneg.
                 intros.
                 apply nnfsqr.
           ++ apply all_almost.
              intros.
              unfold Rbar_rvlim.
              apply ELim_seq_correct.
              rewrite ex_Elim_seq_fin.
              apply ex_lim_seq_incr.
              intros.
              apply sum_n_pos_incr; try lia.
              intros.
              apply nnfsqr.
        -- intros.
           typeclasses eauto.
        -- typeclasses eauto.
        -- typeclasses eauto.
  - apply all_almost; intros.
    apply is_lim_seq_const.
  - apply all_almost; intros.
    apply ex_series_const0.
  - trivial.
 Qed.

