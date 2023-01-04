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

Context {Ts : Type} (β γ : R) (* (w α : Ts -> nat -> R)  *)
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

Lemma isfe_almost_condexp_sqr_bounded (dom2 : SigmaAlgebra Ts) (sub2: sa_sub dom2 dom) (B : R) 
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

Lemma isfe_almost_condexp_const (dom2 : SigmaAlgebra Ts) (sub2: sa_sub dom2 dom) (B : R) 
      (w : Ts -> R)
      {rv : RandomVariable dom borel_sa w} :
  (almostR2 prts eq
    (ConditionalExpectation _ sub2 w)
    (const B)) ->
  is_conditional_expectation prts dom2 w (ConditionalExpectation prts sub2 w) ->
  IsFiniteExpectation prts w.
Proof.
  intros.
  assert (Rbar_IsFiniteExpectation prts (ConditionalExpectation _ sub2 w)).
  {
    apply Rbar_IsFiniteExpectation_proper_almostR2 with (rv_X1 := const B).
    - typeclasses eauto.
    - apply RandomVariable_sa_sub; trivial.
      apply Condexp_rv.
    - apply Rbar_IsFiniteExpectation_const.
    - now symmetry.
  }
  now apply (is_conditional_expectation_FiniteExpectation prts w
             (ConditionalExpectation _ sub2 w)).
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

  Lemma isfe_sqr_X_almost_01 (a : Ts -> R) 
        {rv : RandomVariable dom borel_sa a} 
        (apos: almostR2 prts Rle (const 0) a)
        (aone: almostR2 prts Rle a (const 1)):
    IsFiniteExpectation prts (rvsqr a).
  Proof.
    apply IsFiniteExpectation_abs_bound_almost with (g := const 1).
    - typeclasses eauto.
    - typeclasses eauto.
    - revert aone.
      apply almost_impl.
      revert apos.
      apply almost_impl, all_almost.
      rv_unfold; unfold const.
      unfold impl; intros.
      rewrite <- Rabs_sqr.
      rewrite <- (Rmult_1_r 1).
      unfold Rsqr.
      now apply Rmult_le_compat.
    - apply IsFiniteExpectation_const.
  Qed.

  Lemma isfe_X_almost_01 (a : Ts -> R) 
        {rv : RandomVariable dom borel_sa a} 
        (apos: almostR2 prts Rle (const 0) a)
        (aone: almostR2 prts Rle a (const 1)):
    IsFiniteExpectation prts a.
  Proof.
    apply IsFiniteExpectation_abs_bound_almost with (g := const 1); trivial.
    - typeclasses eauto.
    - revert aone.
      apply almost_impl.
      revert apos.
      apply almost_impl, all_almost.
      rv_unfold; unfold const.
      unfold impl; intros.
      rewrite Rabs_right; trivial.
      lra.
    - apply IsFiniteExpectation_const.
  Qed.

  Lemma isfe_rvmult_almost_01 (b w : Ts -> R) 
        {rvb : RandomVariable dom borel_sa b}
        {rvw : RandomVariable dom borel_sa w}         
        (bpos: almostR2 prts Rle (const 0) b)
        (bone: almostR2 prts Rle b (const 1)):
    IsFiniteExpectation prts w ->
    IsFiniteExpectation prts (rvmult w b).
  Proof.
    intros.
    apply IsFiniteExpectation_abs_bound_almost with (g := rvabs w); trivial.
    - typeclasses eauto.
    - typeclasses eauto.
    - revert bone.
      apply almost_impl.
      revert bpos.
      apply almost_impl, all_almost.
      rv_unfold; unfold const.
      unfold impl; intros.
      rewrite Rabs_mult.
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l.
      + apply Rabs_pos.
      + rewrite Rabs_right; lra.
    - now apply RandomVariableFinite.IsFiniteExpectation_abs.
  Qed.

  Lemma isfe_rvsqr_rvmult_almost_01 (b w : Ts -> R) 
        {rvb : RandomVariable dom borel_sa b}
        {rvw : RandomVariable dom borel_sa w}         
        (bpos: almostR2 prts Rle (const 0) b)
        (bone: almostR2 prts Rle b (const 1)):
    IsFiniteExpectation prts (rvsqr w) ->
    IsFiniteExpectation prts (rvsqr (rvmult w b)).
  Proof.
    intros.
    apply IsFiniteExpectation_abs_bound_almost with (g := rvsqr w); trivial.
    - typeclasses eauto.
    - typeclasses eauto.
    - revert bone.
      apply almost_impl.
      revert bpos.
      apply almost_impl, all_almost.
      rv_unfold; unfold const.
      unfold impl; intros.
      rewrite <- Rabs_sqr.
      rewrite Rsqr_mult.
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l.
      + apply Rle_0_sqr.
      + rewrite <- Rmult_1_r.
        unfold Rsqr.
        apply Rmult_le_compat; trivial.
  Qed.

Lemma Dvoretzky_converge_W_alpha_beta  (W w α β: nat -> Ts -> R) 
      {F : nat -> SigmaAlgebra Ts} (isfilt : IsFiltration F) (filt_sub : forall n, sa_sub (F n) dom)
      {adaptZ : IsAdapted borel_sa W F} (adapt_alpha : IsAdapted borel_sa α F)
      (adapt_beta : IsAdapted borel_sa β F) 
      {rvw : forall n, RandomVariable dom borel_sa (w n)}

      {rvalpha : forall n, RandomVariable dom borel_sa (α n)}
      {rvbeta : forall n, RandomVariable dom borel_sa (β n)}            
(*
      (alpha_pos:forall n x, 0 <= α n x)
      (alpha_one:forall n x, 0 <= 1 - α n x )  
*)
      (apos: forall (n:nat), almostR2 prts Rle (const 0) (α n)) 
      (aone: forall (n:nat), almostR2 prts Rle (α n) (const 1)) 
      (bpos: forall (n:nat), almostR2 prts Rle (const 0) (β n)) 
      (bone: forall (n:nat), almostR2 prts Rle (β n) (const 1)) :
  (forall n,
      almostR2 prts eq
               (ConditionalExpectation prts (filt_sub n) (w n))
               (const 0)) ->
  (exists (C: R),
      (forall n,
          almostR2 prts Rbar_le
            (ConditionalExpectation prts (filt_sub n) (rvsqr (w n)))
            (const (Rsqr C)))) ->
   almost prts (fun ω : Ts => is_lim_seq (sum_n(fun n : nat => α n ω)) p_infty)  ->
   almost prts (fun ω : Ts => is_lim_seq (sum_n (fun n : nat => β n ω)) p_infty)  ->
   (exists (A2 : R),
       almost prts (fun ω => Rbar_lt (Lim_seq (sum_n (fun n : nat => rvsqr (α n) ω))) (Rbar.Finite A2))) ->

   (exists (A3 : R),
       almost prts (fun ω => Rbar_lt (Lim_seq (sum_n (fun n : nat => rvsqr (β n) ω))) (Rbar.Finite A3))) ->
  (forall n, rv_eq (W (S n)) (rvplus (rvmult (rvminus (const 1) (α n)) (W n)) (rvmult (w n) (β n)))) ->
  almost _ (fun ω => is_lim_seq (fun n => W n ω) (Rbar.Finite 0)).
Proof.
  intros condexpw condexpw2 alpha_inf beta_inf alpha_sqr beta_sqr (* W0 *) Wrel.

  assert (svy1b: forall n : nat, IsFiniteExpectation prts (rvsqr (β n))).
  {
    intros.
    now apply isfe_sqr_X_almost_01.
  }

  assert (isfew2: forall n : nat, IsFiniteExpectation prts (rvsqr (w n) )).
  {
    intros.
    destruct condexpw2 as [C ?].
    specialize (H n).
    eapply isfe_almost_condexp_sqr_bounded with (sub2 := filt_sub n).
    apply H.
  }

  assert (isfew : forall n, IsFiniteExpectation prts (w n)).
  {
    intros.
    now apply isfe_rsqr.
  }
      
  assert (isfemult : forall n, IsFiniteExpectation prts (rvmult (w n) (β n))).
  {
    intros.
    now apply isfe_rvmult_almost_01.
  }

  assert (svy2b : forall n : nat, IsFiniteExpectation prts (rvsqr (rvmult (w n) (β n)))).
  {
    intros.
    now apply isfe_rvsqr_rvmult_almost_01.
 }

  assert (forall (n:nat) (x:Ts), 0 <= (fun n x => 0) n x).
  {
    intros.
    lra.
  }
  assert (forall n, RandomVariable dom borel_sa (rvmult (w n) (β n))).
  {
    intros.
    typeclasses eauto.
  }
  assert (HH: forall n : nat, almostR2 prts Rle (const 0) (const 0)).
  {
    intros.
    apply all_almost.
    intros; unfold const; lra.
  }
  generalize (Dvoretzky_DS_extended_alt_almost W (fun n => rvmult (w n) (β n)) 
                                        (fun n => rvmult (rvminus (const 1) (α n)) (W n))
             isfilt filt_sub HH HH apos H0 Wrel); intros.
  apply H1.
  - intros.
    assert (RandomVariable (F n) borel_sa (β n)) by apply adapt_beta.
    generalize (ConditionalExpectation.Condexp_factor_out prts (filt_sub n) (w n) (β n)); intros.
    apply almost_prob_space_sa_sub_lift with (sub := filt_sub n) in H3.
    specialize (condexpw n).
    revert condexpw.
    apply almost_impl.
    revert H3.
    unfold almostR2.
    apply almost_impl, all_almost.
    intros; red; intros; red; intros.
    rewrite H3.
    unfold Rbar_rvmult.
    replace (Rbar.Finite (const 0 x)) with (Rbar_mult  (Rbar.Finite (β n x)) (Rbar.Finite  (const 0 x))).
    + f_equal.
      rewrite <- H4.
      apply ConditionalExpectation.ConditionalExpectation_ext.
      now intro z.
    + unfold const.
      now rewrite Rbar_mult_0_r.
  - intros.
    specialize (apos n).
    revert apos.
    apply almost_impl.
    specialize (aone n).
    revert aone.
    apply almost_impl.
    apply all_almost; unfold impl; intros omega ??.
    rv_unfold.
    rewrite Rplus_0_r.
    unfold Rabs, Rmax.
    match_destr; match_destr.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 <= (1 + -1 * α n omega)).
      {
        lra.
      }
      apply Rge_le in r0.
      generalize (Rmult_le_pos _ _ H4 r0).
      lra.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 <= (1 + -1 * α n omega)).
      {
        lra.
      }
      apply Rlt_gt in r0.
      assert (W n omega <= 0) by lra.
      generalize (Rmult_le_ge_compat_neg_l _ _ _ H5 H4); intros.
      rewrite Rmult_0_r in H6.
      rewrite Rmult_comm in H6.
      lra.
  - destruct condexpw2 as [C ?].
    assert (forall n,
               FiniteExpectation prts (rvsqr (rvmult (w n) (β n))) 
               <= C^2 * FiniteExpectation prts (rvsqr (β n))).
    {
      intros.
      assert (RandomVariable (F n) borel_sa (rvsqr (β n))).
      {
        now apply rvsqr_rv.
      }
      assert (almostR2 prts Rbar_le
                        (ConditionalExpectation prts (filt_sub n) (rvmult (rvsqr (w n)) (rvsqr (β n))))
                        (Rbar_rvmult (rvsqr (β n)) (const (Rsqr C)))).
                                     
      {
        specialize (H2 n).
        revert H2.
        apply almost_impl.
        generalize (NonNegCondexp_factor_out prts (filt_sub n) (rvsqr (w n)) (rvsqr (β n))); intros.
        apply almost_prob_space_sa_sub_lift with (sub := filt_sub n) in H2.
        revert H2.
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
      assert (almostR2 prts Rbar_le
                        (ConditionalExpectation prts (filt_sub n) (rvsqr (rvmult (w n) (β n))))
                        (Rbar_rvmult (rvsqr (β n)) (const (Rsqr C)))).
                                     
      {

        generalize (NonNegCondexp_factor_out prts (filt_sub n) (rvsqr (w n)) (rvsqr (β n))); intros.
        apply almost_prob_space_sa_sub_lift with (sub := filt_sub n) in H5.
        revert H5.
        apply almost_impl.
        specialize (H2 n).
        revert H2.
        apply almost_impl, all_almost.
        unfold impl; intros.
        assert (rv_eq (rvsqr (rvmult (w n) (β n)))
                      (rvmult (rvsqr (w n)) (rvsqr (β n)))).
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
                                                  (rvsqr (rvmult (w n) (β n))))).
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
      - revert H5.
        apply almost_impl, all_almost.
        unfold impl; intros.
        assert (Rbar_le (FiniteConditionalExpectation prts (filt_sub n) (rvsqr (rvmult (w n) (β n)))
                        x)
                        (rvscale C² (rvsqr (β n)) x)).
        {
          generalize (FiniteCondexp_eq prts (filt_sub n) (rvsqr (rvmult (w n) (β n)))); intros.
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
    apply (@ex_series_le R_AbsRing R_CompleteNormedModule ) with 
        (b := fun n => C^2 * FiniteExpectation prts (rvsqr (β n))).
    + intros.
      unfold norm; simpl.
      unfold abs; simpl.
      rewrite Rabs_right.
      * eapply Rle_trans.
        apply H3.
        unfold pow; lra.
      * apply Rle_ge, (FiniteExpectation_sq_nneg prts (rvmult (w n) (β n)) (svy2b n)).
    + apply (@ex_series_scal R_AbsRing).      
      rewrite <- ex_finite_lim_series.
      rewrite ex_finite_lim_seq_correct.
      split.
      * apply ex_lim_seq_incr.
        intros.
        apply sum_n_pos_incr; try lia.
        intros.
        apply FiniteExpectation_pos.
        typeclasses eauto.
      * generalize (sum_expectation prts (fun n => rvsqr (β n))); intros.
        assert (forall n, RandomVariable dom borel_sa (rvsqr (β n))).
        {
          intros.
          typeclasses eauto.
        }
        specialize (H4 H5 svy1b).
        rewrite (Lim_seq_ext _ _ H4).
        destruct beta_sqr as [A2 beta_sqr].
        generalize (Dominated_convergence_almost 
                      prts 
                      (fun n omega => Rbar.Finite (rvsum (fun n0 => rvsqr (β n0)) n omega))
                      (Rbar_rvlim (fun n omega => Rbar.Finite (rvsum (fun n0 => rvsqr (β n0)) n omega)))
                   ); intros.
        specialize (H6 (const (Rbar.Finite A2))).
        cut_to H6.
        -- assert  (isfefn : forall n : nat,
                   Rbar_IsFiniteExpectation prts
                     (fun omega : Ts =>
                      Rbar.Finite
                        (rvsum (fun n0 : nat => rvsqr (β n0)) n omega))).
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
                             (sum_n  (fun n0 : nat => rvsqr (β n0) x))); intros.
                 cut_to H8.
                 --- specialize (H8 n).
                     generalize (Rbar_le_lt_trans _ _ _ H8 H7); intros.
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
                         (rvsum (fun n0 : nat => rvsqr (β n0)) n omega)))).
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
               now apply Rbar_lt_le.
             - apply Rbar_IsFiniteExpectation_const.
           }
           specialize (H6 isfefn isfe).
           apply is_lim_seq_unique in H6.
           ++ rewrite Lim_seq_ext with
                  (v :=  (fun n : nat =>
                            Rbar_FiniteExpectation 
                              prts
                              (fun omega : Ts =>
                                 Rbar.Finite (rvsum (fun n0 : nat => rvsqr (β n0)) n omega)))).
              ** rewrite H6.
                 now simpl.
              ** intros.
                 rewrite <- FinExp_Rbar_FinExp.
                 --- apply Rbar_FiniteExpectation_ext.
                     now intro z.
                 --- apply rvsum_rv.
                     intros.
                     typeclasses eauto.
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
              ** generalize (Lim_seq_increasing_le (sum_n (fun n0 : nat => rvsqr (β n0) x))); intros.
                 cut_to H8.
                 --- specialize (H8 n).
                     generalize (Rbar_le_lt_trans _ _ _ H8 H7); intros.
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
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const Ca)) ->
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
  generalize (Dvoretzky_converge_W_alpha_beta W w α β isfilt filt_sub); intros dvor.
  eapply dvor; trivial.
  - intros.
    now apply (RandomVariable_sa_sub (filt_sub n)).
  - intros.
    now apply (RandomVariable_sa_sub (filt_sub n)).
  - exists B.
    apply H0.
  - exists (Ca + 1).
    revert H7.
    apply almost_impl, all_almost.
    unfold impl; intros.
    eapply Rbar_le_lt_trans.
    apply H7.
    unfold const; simpl.
    lra.
  - exists (Cb + 1).
    revert H8.
    apply almost_impl, all_almost.
    unfold impl; intros.
    eapply Rbar_le_lt_trans.
    apply H8.
    unfold const; simpl.
    lra.
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
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const Ca)) ->
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  (almost prts (fun ω => exists (b:Ts ->R), forall n, B n ω <= Rabs (b ω))) ->
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
      apply EventIndicator_rv with (dom := F t).
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
    revert H10.
    apply almost_impl, all_almost.
    unfold impl; intros.
    destruct H10.
    pose (b := Rabs  (x0 x)).
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
    generalize isfe_almost_condexp_sqr_bounded; intros.
    assert (RandomVariable dom borel_sa (wk k n)).
    {
      apply rvmult_rv; trivial.
      apply (RandomVariable_sa_sub (filt_sub n)).
      apply EventIndicator_rv with (dom := F n).
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
  (almost prts (fun ω => exists (b:Ts ->R), forall n, B n ω <= Rabs (b ω))) ->
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

Definition is_lim_seq'_uniform_fun {Ts} (u : nat -> Ts -> R) (l : Ts -> R) :=
   forall eps : posreal, 
     eventually (fun n => forall (x:Ts), Rabs (u n x - l x) < eps).

Definition is_lim_seq'_uniform_almost (u : nat -> Ts -> R) (l : Ts -> R) :=
   forall eps : posreal, 
     eventually (fun n => almostR2 prts Rlt (rvabs (rvminus (u n) l)) (const eps)).

Lemma uniform_lim_all_almost (u : nat -> Ts -> R) (l : Ts -> R) :
  is_lim_seq'_uniform_fun u l ->
  is_lim_seq'_uniform_almost u l.
Proof.
  intros ??.
  destruct (H eps).
  exists x; intros.
  apply all_almost; intros.
  rv_unfold'.
  now apply H0.
Qed.

Definition is_lim_seq'_uniform_constlim {Ts} (u : nat -> Ts -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, 
      eventually (fun n => forall (x:Ts), Rabs (u n x - l) < eps)
    | p_infty => forall M : R, eventually (fun n => forall (x:Ts), M < u n x)
    | m_infty => forall M : R, eventually (fun n => forall (x:Ts), u n x < M)
  end.

Definition is_lim_seq'_uniform_fun_Rbar {Ts} (u : nat -> Ts -> R) (l : Ts -> Rbar) :=
   forall eps : posreal, 
     eventually (fun n => forall (x:Ts), 
                     match (l x) with
                     | Finite l' => Rabs (u n x - l') < eps
                     | p_infty => 1/eps < u n x
                     | m_infty => u n x < - 1/eps
                     end).

Lemma uniform_converge_sq (α : nat -> Ts -> R) :
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
  is_lim_seq'_uniform_almost (fun n => rvsqr (α n)) (const 0) ->
  eventually (fun n => almostR2 prts Rle  (α n) (const 1)).
Proof.
  intros.
  assert (0 < 1) by lra.
  specialize (H0 (mkposreal _ H1)).
  destruct H0 as [N ?].
  exists N.
  intros.
  specialize (H0 n H2).
  specialize (H n).
  revert H; apply almost_impl.
  revert H0; apply almost_impl.
  apply all_almost; unfold impl; intros.
  unfold const in *.
  unfold rvsqr, rvabs in H.
  rewrite rvminus_unfold in H.
  simpl in H.
  rewrite Rminus_0_r, <- Rabs_sqr in H.
  replace 1 with (Rsqr 1) in H by (unfold Rsqr; lra).
  apply Rsqr_lt_abs_0 in H.
  do 2 rewrite Rabs_right in H; lra.
Qed.    

Lemma uniform_converge_sum_sq (α : nat -> Ts -> R) :
  let A := fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω)) in
  is_lim_seq'_uniform_almost (fun n => fun ω => sum_n (fun k => rvsqr (α k) ω) n) A ->
  is_lim_seq'_uniform_almost (fun n => rvsqr (α n)) (const 0).
Proof.
  unfold is_lim_seq'_uniform_almost; intros.
  assert (0 < eps/2).
  {
    generalize (cond_pos eps); intros; lra.
  }
  specialize (H (mkposreal _ H0)).
  destruct H as [N ?].
  exists (S N).
  intros.
  assert (N <= (n-1))%nat by lia.
  generalize (H _ H2); intros.
  assert (N <= n)%nat by lia.
  specialize (H _ H4).
  revert H; apply almost_impl.
  revert H3; apply almost_impl.
  apply all_almost; unfold impl; intros.
  simpl in H; simpl in H3.
  rv_unfold'_in_star.
  rewrite Rminus_0_r, <- Rabs_sqr.
  pose (A := Lim_seq (sum_n (fun k => rvsqr (α k) x))).
  pose (B := fun n => sum_n (fun k : nat => (α k x)²) n).
  generalize (Rabs_triang (B n - A) (A - B (n-1)%nat)); intros.
  replace  (Rabs (B n - A + (A - B (n-1)%nat))) with (α n x)² in H5.
  - eapply Rle_lt_trans.
    apply H5.
    rewrite Rabs_minus_sym in H.
    unfold A, B, rvsqr.
    lra.
  - replace (n) with (S (n-1)) by lia.
    replace (S (n-1) - 1)%nat with (n-1)%nat by lia.
    unfold B.
    rewrite sum_Sn.
    unfold plus; simpl.
    replace (S (n-1)) with (n) by lia.
    rewrite Rabs_sqr at 1.
    f_equal.
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
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) (const Ca)) ->
  (almostR2 prts Rbar_le (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) (const Cb)) ->
  (forall n ω, W (S n) ω = (1 - α n ω) * (W n ω) + (β n ω) * (w n ω)) ->
  is_lim_seq'_uniform_almost (fun n => fun ω => sum_n (fun k => rvsqr (α k) ω) n) 
                             (fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω))) ->
  is_lim_seq'_uniform_almost (fun n => fun ω => sum_n (fun k => rvsqr (β k) ω) n) 
                             (fun ω => Lim_seq (sum_n (fun k => rvsqr (β k) ω))) ->
 (almost prts (fun ω => exists (b:Ts -> R), forall n, B n ω <= Rabs (b ω))) ->
  almost prts (fun ω => is_lim_seq (fun n => W n ω) 0).
Proof.
  
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
    - revert H5; apply almost_impl.
      apply all_almost; intros ??.
      destruct N.
      + rewrite Lim_seq_ext with
            (v := (sum_n (fun k : nat => rvsqr (α k) x1))); trivial.
        intros.
        apply sum_n_ext; intros.
        now replace (n0 + 0)%nat with n0 by lia.
      + rewrite Lim_seq_ext with
            (v :=  fun n => sum_n (fun k : nat => rvsqr (α k) x1) (n + S N) -
                            sum_n (fun k : nat => rvsqr (α k) x1) N).
        * apply Rbar_le_trans with
              (y := Lim_seq (fun n : nat => sum_n (fun k : nat => rvsqr (α k) x1) (n + S N))).
          -- apply Lim_seq_le_loc.
             exists (0%nat); intros.
             assert (0 <= sum_n (fun k : nat => rvsqr (α k) x1) N).
             {
               apply sum_n_nneg.
               intros.
               apply nnfsqr.
             }
             lra.
          -- now rewrite <- Lim_seq_incr_n with (N := S N) in H5.
        * intros.
          now rewrite sum_shift_diff.
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
    - revert H10.
      apply almost_impl, all_almost; intros ??.
      destruct H10.
      now exists x2.
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
   apply (@exists_almost Ts dom prts (fun (T : nat) =>
                     (fun ω : Ts => forall t0 t : nat, (t0 >= T)%nat -> rvabs (W t t0) ω <= delta ω))).
   revert H2.
   apply almost_impl, all_almost; intros ??.
   now apply lemma2 with (α := α) (w := w).
 Qed.

 Lemma lemma8_part1 (x Y W : nat -> Ts -> R) (D : posreal) (ω : Ts) 
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
     
 Lemma lemma8_almost_part1  (x Y W : nat -> Ts -> R) (D : posreal) 
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
   apply (lemma8_part1 x Y W D x0 α w); trivial.
 Qed.

 Lemma lemma8_part2 (x Y W : nat -> Ts -> R) (D : posreal) (ω : Ts)
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
     
 Lemma lemma8_almost_part2  (x Y W : nat -> Ts -> R) (D : posreal) 
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
   apply (lemma8_part2 x Y W D x0 α w); trivial.
 Qed.

 Lemma lemma8_abs  (x Y W : nat -> Ts -> R) (ω : Ts) (D : posreal) 
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
       now apply lemma8_part2 with (D := D) (α := α) (w := w).
     - apply Rplus_le_reg_r with (r := (W t ω)).
       ring_simplify.
       rewrite Rplus_comm.
       now apply lemma8_part1 with (D := D) (α := α) (w := w).
   }
   apply Rplus_le_reg_r with (r := - Rabs (W t ω)).
   ring_simplify.
   apply Rle_trans with (r2 := Rabs (x t ω - W t ω) ); trivial.
   apply Rabs_triang_inv.
  Qed.

 Lemma lemma8_abs_part2  (x Y W : nat -> Ts -> R) 
      (α w : nat -> Ts -> R) (ω : Ts) (eps D : posreal) :
   (forall t, 0 <= α t ω <= 1) ->
   (W 0%nat ω = 0) ->
   (forall t,
       W (S t) ω =
       (1 - α t ω) * (W t ω) +
       (α t ω) * (w t ω)) ->
   (forall t,
       Rabs (x t ω) <= Rabs (W t ω) + (Y t ω)) ->
   is_lim_seq (fun t => Y t ω) (β * D) ->
   (exists (T : nat),
       forall t,
         (t >= T)%nat ->
         Rabs (W t ω) <= β * eps * D) ->
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

   Lemma LimSup_lt_nneg (f : nat -> R) (B : R) :
    (forall n, 0 <= f n) ->
    Rbar_lt (LimSup_seq f) B ->
    exists (N : nat),
    forall (n : nat), 
      (N <= n)%nat ->
      f n <= B.
  Proof.
    intros.
    unfold LimSup_seq, proj1_sig in H0.
    match_destr_in H0.
    unfold is_LimSup_seq in i.
    match_destr_in i.
    - simpl in H0.
      assert (0 < (B - r)/2) by lra.
      specialize (i (mkposreal _ H1)).
      destruct i.
      destruct H3.
      exists x.
      intros.
      specialize (H3 n H4).
      simpl in H3.
      lra.
    - now simpl in H0.
    - specialize (i (-1)).
      destruct i.
      specialize (H1 x).
      specialize (H x).
      cut_to H1; try lia; try lra.
 Qed.

  Lemma lemma8_abs_combined  (x Y W : nat -> Ts -> R) 
        (α w : nat -> Ts -> R) (ω : Ts) (eps D : posreal) :
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
   (exists (T : nat),
       forall t,
         (t >= T)%nat ->
         Rabs (W t ω) <= β * eps * D) ->
   exists (N : nat),
   forall (t : nat), 
     (N <= t)%nat ->
     Rabs (x t ω) <=  (β * (1 + 2 * eps) * D).
  Proof.
    intros.
    apply LimSup_lt_nneg.
    - intros.
      apply Rabs_pos.
    - apply Rbar_le_lt_trans with (y:= β * (1 + eps) * D).
      + apply lemma8_abs_part2 with (Y := Y) (W :=W) (α := α) (w := w); trivial.
        intros.
        apply lemma8_abs with (D := D) (α := α) (w := w); trivial.
      + simpl.
        apply Rmult_lt_compat_r; [apply cond_pos |].
        apply Rmult_lt_compat_l; trivial.
        generalize (cond_pos eps); intros.
        lra.
   Qed.

  Lemma lemma8_abs_combined_almost  (x Y W : nat -> Ts -> R) 
        (α w : nat -> Ts -> R) (eps : posreal) (D : Ts -> posreal) :
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
               exists (T : nat),
                 forall t,
                   (t >= T)%nat ->
                   Rabs (W t ω) <= β * eps * D ω) ->
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
    
 Lemma lemma8_abs_part2_almost  (x Y W : nat -> Ts -> R) 
      (α w : nat -> Ts -> R) (eps : posreal) (D : Ts -> posreal) :
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
                  forall t,
                    (t >= T ω)%nat ->
                    Rabs (W t ω) <= β * eps * D ω))) ->
   almost prts (fun ω => 
                  Rbar_le (LimSup_seq (fun t => Rabs (x t ω))) (β * (1 + eps) * D ω)).
 Proof.
   intros.
   destruct H5.
   revert H4; apply almost_impl.
   revert H5; apply almost_impl.
   apply all_almost; intros ???.
   apply lemma8_abs_part2 with (Y := Y) (W := W) (α := α) (w := w); try easy.
   now exists (x0 x1).
 Qed.

 Lemma Y_prod (Y : nat -> Ts -> R) (D : Ts -> R) (β : R) 
      (α : nat -> Ts -> R) :
   β < 1 ->
   (rv_eq (Y 0%nat) D) ->
   (forall t ω, 0 <= α t ω <= 1) ->
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
    - specialize (H2 0%nat ω).
      rewrite H2.
      specialize (H0 ω).
      rv_unfold'.
      rewrite H0.
      simpl.
      lra.
    - specialize (H2 (S t) ω).
      rewrite H2.
      rv_unfold'.
      rewrite IHt.
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

  Lemma Y_lim (Y : nat -> Ts -> R) (β : R) (D : Ts -> R)
      (α : nat -> Ts -> R) :
    β < 1 ->
    (rv_eq (Y 0%nat) D) ->
    (forall t ω, 0 <= α t ω <= 1) ->
    (forall ω, is_lim_seq (sum_n (fun t => α t ω)) p_infty) ->
    (forall t,
        rv_eq (Y (S t))
              (rvplus 
                 (rvmult (rvminus (const 1) (α t)) (Y t))
                 (rvmult (α t) (rvscale β D)))) ->
    forall ω,
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

  Lemma vecrvminus_unfold {n} (x y : Ts -> vector R n) :
    rv_eq (vecrvminus x y) (fun ω => Rvector_minus (x ω) (y ω)).
  Proof.
    intros ?.
    now unfold vecrvminus, Rvector_minus, vecrvplus.
  Qed.

  Lemma Rabs_plus (a b : R) :
    Rabs (Rabs a + Rabs b) = Rabs a + Rabs b.
  Proof.
    apply Rabs_right.
    apply Rle_ge.
    apply Rplus_le_le_0_compat; apply Rabs_pos.
  Qed.

  Lemma powerRZ_up_log_base (base val : R) :
    base > 1 ->
    val > 0 ->
    {k | powerRZ base (k - 1) <= val < powerRZ base k}.
  Proof.
    intros.
    pose (exp := (ln val)/(ln base)).
    pose (k := up exp).
    assert (val = Rpower base exp).
    {
      unfold exp.
      rewrite log_power_base; lra.
    }
    assert (val < powerRZ base k).
    {
      rewrite powerRZ_Rpower; try lra.
      rewrite H1.
      apply Rpower_lt; try lra.
      unfold k.
      apply archimed.
    }
    assert (powerRZ base (k-1) <= val).
    {
      rewrite powerRZ_Rpower; try lra.
      rewrite H1.
      apply Rle_Rpower; try lra.
      unfold k.
      rewrite minus_IZR.
      generalize (archimed exp); intros.
      lra.
    }
    exists k; lra.
  Defined.

  Lemma powerRZ_up_log_base_ext (base val : R) 
    (pf1 pf1':base > 1)
    (pf2 pf2':val > 0) :
    ` (powerRZ_up_log_base _ _ pf1 pf2) = ` (powerRZ_up_log_base _ _ pf1' pf2').
  Proof.
    now simpl.
  Qed.    

  Lemma powerRZ_up_log_base_alt (base val : R) :
    base > 1 ->
    val > 0 ->
    {k | powerRZ base (k - 1) < val <= powerRZ base k}.
  Proof.
    intros.
    generalize (powerRZ_up_log_base base val H H0); intros.
    destruct H1 as [k1 ?].
    destruct (Req_EM_T (powerRZ base (k1-1)) val).
    - exists (k1-1)%Z.
      split; try lra.
      rewrite <- e.
      rewrite powerRZ_Rpower; try lra.
      rewrite powerRZ_Rpower; try lra.      
      apply Rpower_lt; try lra.
      rewrite minus_IZR.
      lra.
    - exists k1; lra.
  Qed.

  Lemma powerRZ_up_log_base_alt_ext (base val : R) 
    (pf1 pf1':base > 1)
    (pf2 pf2':val > 0) :
    ` (powerRZ_up_log_base_alt _ _ pf1 pf2) = ` (powerRZ_up_log_base_alt _ _ pf1' pf2').
  Proof.
    unfold proj1_sig; repeat match_destr.
    destruct (Z.lt_trichotomy x x0) as [? | [?|?]]; trivial.
    - assert (x  <= x0 - 1)%Z by lia.
      assert (powerRZ base x <= powerRZ base (x0 - 1)%Z).
      {
        repeat rewrite powerRZ_Rpower by lra.
        apply Rle_Rpower; try lra.
        now apply IZR_le.
      }
      lra.
    - assert (x0  <= x - 1)%Z by lia.
      assert (powerRZ base x0 <= powerRZ base (x - 1)%Z).
      {
        repeat rewrite powerRZ_Rpower by lra.
        apply Rle_Rpower; try lra.
        now apply IZR_le.
      }
      lra.
  Qed.    

  Lemma powerRZ_up_log_increasing (base val1 val2 : R)
        (pfb: base > 1)
        (pf1: val1 > 0)
        (pf2: val2 > 0) :
    val1 >= val2 ->
    (proj1_sig (powerRZ_up_log_base _ _ pfb pf1) >=
     proj1_sig (powerRZ_up_log_base _ _ pfb pf2))%Z.
  Proof.
    intros.
    Admitted.

  Lemma powerRZ_up_log_alt_increasing  (base val1 val2 : R)
        (pfb: base > 1)
        (pf1: val1 > 0)
        (pf2: val2 > 0) :
    val1 >= val2 ->
    (proj1_sig (powerRZ_up_log_base _ _ pfb pf1) >=
     proj1_sig (powerRZ_up_log_base _ _ pfb pf2))%Z.
  Proof.
    intros.
    Admitted.

  Definition powerRZ_ge_fun (base val : R) : R.
  Proof.
    generalize (powerRZ_up_log_base_alt base val); intros.
    destruct (Rgt_dec base 1).
    - destruct (Rgt_dec val 0).
      + specialize (H r r0).
        exact (powerRZ base (` H)).
      + exact 0.
    - exact 0.
  Defined.

  Lemma powerRZ_ge_fun_increasing (base val1 val2 : R) :
    val1 >= val2 ->
    powerRZ_ge_fun base val1 >= powerRZ_ge_fun base val2.
  Proof.
    intros.
    Admitted.

  Lemma increasing_Rbar_measurable (f : Rbar -> Rbar) :
    (forall u v, Rbar_le u v -> Rbar_le (f u) (f v)) ->
    (RbarMeasurable (dom := Rbar_borel_sa) f).
  Proof.
    intros ??.
    assert (forall (z1 z2 : Rbar),
               Rbar_le z1 z2 ->
               Rbar_le (f z2) r ->
               Rbar_le (f z1) r).
    {
      intros.
      eapply Rbar_le_trans.
      now apply (H z1 z2).
      apply H1.
    }
    assert (exists (z : Rbar),
               (pre_event_equiv
                  (fun omega : Rbar => Rbar_le (f omega) r)
                  (fun omega : Rbar => Rbar_le omega z)) \/
               (pre_event_equiv
                  (fun omega : Rbar => Rbar_le (f omega) r)
                  (fun omega : Rbar => Rbar_lt omega z))
               ).
    {
      exists (Rbar_lub (fun w => Rbar_le (f w) r)).
      unfold Rbar_lub, proj1_sig, pre_event_equiv.
      match_destr.
      destruct r0.
      unfold Rbar_is_upper_bound in *.
      destruct (Rbar_le_lt_dec (f x) r).
      - left.
        
        admit.
      - right.
        admit.
    }
    destruct H0 as [z ?].
    apply sa_proper with (x := (fun omega : Rbar => Rbar_le omega z)); try easy.
    Admitted.
    

  Lemma powerRZ_ge (base val : R) :
    base > 1 ->
    val <= powerRZ_ge_fun base val.
  Proof.
    intros.
    unfold powerRZ_ge_fun.
    match_destr; try lra.
    match_destr; try lra.
    unfold proj1_sig.
    match_destr.
    lra.
  Qed.

  Lemma powerRZ_ge_scale (base val scal : R) :
    base > 1 ->
    scal > 0 ->
    val <= scal * powerRZ_ge_fun base (val / scal).
  Proof.
    intros.
    generalize (powerRZ_ge base (val / scal) H); intros.
    apply Rmult_le_compat_l with (r := scal) in H1; try lra.
    field_simplify in H1; lra.
  Qed.

  Definition rvinv (x : Ts -> R) := rvpower x (const (-1)).
  
  Global Instance rvinv_rv (x : Ts -> R) (dom2 : SigmaAlgebra Ts) :
    RandomVariable dom2 borel_sa x ->
    RandomVariable dom2 borel_sa (rvinv x).
  Proof.
    intros.
    typeclasses eauto.
  Qed.

  Lemma Rinv_powerRZ (x : R) :
    0 < x ->
    Rinv x = powerRZ x (-1)%Z.
  Proof.
    intros.
    replace (-1)%Z with (- (1))%Z by lia.
    rewrite powerRZ_neg; try lra.
    now rewrite powerRZ_1.
  Qed.
    
  Lemma Rinv_Rpower (x : R) :
    0 < x ->
    Rinv x = Rpower x (-1).
  Proof.
    intros.
    generalize (powerRZ_Rpower x (-1)%Z H); intros.
    rewrite <- H0.
    now apply Rinv_powerRZ.
  Qed.

  Lemma lemma3_part1 (W : nat -> nat -> Ts -> R) (ω : Ts) (ε G0 :R)
        (t0 : nat) (α x ww G M : nat -> Ts -> R) :
    (W 0%nat t0 ω = 0) ->
    M t0 ω <= G t0 ω ->
    (forall t, Rabs (x t ω) <= M t ω) ->
    (forall t, 0 <= α t ω <= 1) ->
    (forall t,
        W (S t) t0 ω =
        (1 - α (t + t0)%nat ω) * (W t t0 ω) +
        (α (t + t0)%nat ω) * (ww (t + t0)%nat ω)) ->
(*    (forall t, Rabs (W t t0 ω) <= ε) -> *)
    (forall t,
        x (S t) ω <= 
        (1 - α t ω) * (x t ω) + 
        (α t ω) * (1 + ww t ω) * (G t0 ω)) ->
    forall t,
      x (t + t0)%nat ω <= (1 + W t t0 ω) * (G t0 ω).
  Proof.
    intros.
    induction t.
    - simpl.
      rewrite H.
      rewrite Rplus_0_r, Rmult_1_l.
      apply Rle_trans with (r2 := Rabs (x t0 ω)).
      + apply Rle_abs.
      + eapply Rle_trans.
        apply H1.
        easy.
    - replace (S t + t0)%nat with (S (t + t0)) by lia.
      eapply Rle_trans.
      apply H4.
      specialize (H2 (t + t0)%nat).
      apply Rmult_le_compat_l with (r := (1 - α (t + t0)%nat ω)) in IHt; try lra.
      apply Rplus_le_compat_r with (r :=  α (t + t0)%nat ω * (1 + ww (t + t0)%nat ω) * G t0 ω) in IHt.
      eapply Rle_trans.
      apply IHt.
      rewrite H3.
      ring_simplify.
      lra.
  Qed.

  Lemma lemma3_part2 (W : nat -> nat -> Ts -> R) (ω : Ts) (ε G0 :R)
        (t0 : nat) (α x ww G M : nat -> Ts -> R) :
    (W 0%nat t0 ω = 0) ->
    M t0 ω <= G t0 ω ->
    (forall t, Rabs (x t ω) <= M t ω) ->
    (forall t, 0 <= α t ω <= 1) ->
    (forall t,
        W (S t) t0 ω =
        (1 - α (t + t0)%nat ω) * (W t t0 ω) +
        (α (t + t0)%nat ω) * (ww (t + t0)%nat ω)) ->
(*    (forall t, Rabs (W t t0 ω) <= ε) -> *)
    (forall t,
        (1 - α t ω) * (x t ω) + 
        (α t ω) * (-1 + ww t ω) * (G t0 ω) <= x (S t) ω) ->
    forall t,
      (-1 + W t t0 ω) * (G t0 ω) <= x (t + t0)%nat ω.
  Proof.
    intros.
    induction t.
    - simpl.
      rewrite H.
      rewrite Rplus_0_r.
      specialize (H1 t0).
      assert (Rabs (x t0 ω) <= G t0 ω) by lra.
      rewrite Rabs_le_between in H5.
      lra.
    - replace (S t + t0)%nat with (S (t + t0)) by lia.
      eapply Rle_trans.
      shelve.
      apply H4.
      Unshelve.
      specialize (H2 (t + t0)%nat).
      apply Rmult_le_compat_l with (r := (1 - α (t + t0)%nat ω)) in IHt; try lra.
      apply Rplus_le_compat_r with (r :=  α (t + t0)%nat ω * (-1 + ww (t + t0)%nat ω) * G t0 ω) in IHt.
      eapply Rle_trans.
      shelve.
      apply IHt.
      Unshelve.
      rewrite H3.
      ring_simplify.
      lra.
  Qed.

    Lemma lemma3 (W : nat -> nat -> Ts -> R) (ω : Ts) (ε G0 :R)
        (t0 : nat) (α x ww G M : nat -> Ts -> R) :
    (W 0%nat t0 ω = 0) ->
    M t0 ω <= G t0 ω ->
    (forall t, Rabs (x t ω) <= M t ω) ->
    (forall t, 0 <= α t ω <= 1) ->
    (forall t,
        W (S t) t0 ω =
        (1 - α (t + t0)%nat ω) * (W t t0 ω) +
        (α (t + t0)%nat ω) * (ww (t + t0)%nat ω)) ->
    (forall t, Rabs (W t t0 ω) <= ε) -> 
    (forall t,
        (1 - α t ω) * (x t ω) + 
        (α t ω) * (-1 + ww t ω) * (G t0 ω) <= x (S t) ω <=
        (1 - α t ω) * (x t ω) + 
        (α t ω) * (1 + ww t ω) * (G t0 ω)) ->
    forall t,
      Rabs(x (t + t0)%nat ω) <= (1 + ε) * (G t0 ω).
   Proof.
     intros.
     assert (Gpos: 0 <= G t0 ω).
     {
       specialize (H1 t0).
       generalize (Rabs_pos  (x t0 ω)); intros.
       lra.
     }
     rewrite Rabs_le_between.
     split.
     - eapply Rle_trans with (r2 := (-1 + W t t0 ω) * (G t0 ω)).
       shelve.
       apply lemma3_part2 with (α := α) (ww := ww) (M := M); try easy.
       intros.
       specialize (H5 t1).
       lra.
       Unshelve.
       specialize (H4 t).
       rewrite Rabs_le_between in H4.       
       ring_simplify.
       unfold Rminus.
       apply Rplus_le_compat_r.
       rewrite Rmult_comm.
       apply Rmult_le_compat_l; try lra.
     - eapply Rle_trans with (r2 := (1 + W t t0 ω) * (G t0 ω)).
       + apply lemma3_part1 with (α := α) (ww := ww) (M := M); try easy.
         intros.
         specialize (H5 t1).
         lra.
       + specialize (H4 t).
         rewrite Rabs_le_between in H4.
         apply Rmult_le_compat_r; try lra.
   Qed.

   Lemma lemma3_nth {n} (X w α : nat -> Ts -> vector R n) 
         (XF : vector R n -> vector R n) (γ G0 : R) (G : nat -> Ts -> R)
         (ω : Ts) (ε : posreal) :
    (forall k i pf, 0 <= vecrvnth i pf (α k) ω <= 1) ->
    0 < G0 ->
    0 <= γ < 1 ->
    γ * (1 + ε) = 1 ->
    let M := fun t => Rmax_list_map (seq 0 (S t)) 
                                    (fun n0 : nat => rvmaxabs (X n0) ω) in
    (forall t, (M t) <= (rvscale (1 + ε) (G t)) ω) ->
    (forall t, (G t ω) <= (G (S t) ω)) ->
    (forall t,
        (G t ω < G (S t) ω) ->
        (M (S t) <= G (S t) ω)) ->
    G 0%nat ω = Rmax (M 0%nat) G0 ->
    (forall x, Rvector_max_abs (XF x) <= γ * (Rmax (Rvector_max_abs x) G0)) ->
    is_lim_seq (fun k => G k ω) p_infty ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (X k ω)) (X k) ) (w k))))) ->
    exists (t0 : nat),
      (M t0) <= (G t0 ω) /\
      forall k, (rvmaxabs (X k) ω) <= (rvscale (1 + ε) (G t0) ω).
   Proof.
    intros.
    pose (ww := fun t => vecrvscalerv (rvinv (G t)) (w t)).
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
    assert (forall (T : nat),
               exists (t : nat),
                 (t >= T)%nat /\ (G t ω) < (G (S t) ω)).
    {
      intros.
      apply is_lim_seq_spec in H8.
      unfold is_lim_seq' in H8.
      revert H8.
      contrapose.
      unfold eventually.
      push_neg.
      intros.
      exists (G T ω).
      intros.
      assert (forall x, (x >= T)%nat -> G x ω = G (S x) ω).
      {
        intros.
        specialize (H8 _ H10).
        specialize (H4 x0).
        lra.
      }
      assert (forall x, (x >= T)%nat -> G x ω = G T ω).
      {
        intros.
        pose (h := (x0 - T)%nat).
        replace x0 with (h + T)%nat by lia.
        induction h.
        - now simpl.
        - replace (S h + T)%nat with (S (h + T)) by lia.
          now rewrite H10 in IHh; try lia.
      }
      exists (max x T).
      split; try lia.
      specialize (H11 (max x T)).
      rewrite H11; try lra.
      lia.
    }
    assert (forall (T : nat),
               exists (t : nat),
                 (t >= T)%nat /\ (M t) <= (G t ω)).
    {
      intros.
      destruct (H10 T) as [t [? ?]].
      exists (S t).
      split; try lia.
      now apply H5.
   }
    assert (forall i pf,
            exists (T : nat),
              forall t0 t : nat,
                (t0 >= T)%nat ->
                Rabs (WW i pf t t0 ω) <= ε).
    {
      intros.
      apply lemma2 with (α := fun k => vecrvnth i pf (α k))
                        (w := fun k => vecrvnth i pf (ww k)); try easy.
      - intros.
        simpl.
        now rv_unfold'.
      - generalize lemma1_alpha_alpha; intros.
        specialize (H12 (fun t ω => vector_nth i pf (α t ω))
                        (fun t ω => vector_nth i pf (ww t ω))).
        admit.
    }
    assert (forall i pf,
               exists t0,
               forall t,
                 Rabs(vector_nth i pf (X (t + t0)%nat ω)) <= (1 + ε) * (G t0 ω)).
    {
      intros.
      specialize (H12 i pf).
      destruct H12 as [T ?].
      specialize (H11 T).
      destruct H11 as [t0 [? ?]].
      exists t0.
      intros.
      generalize (lemma3 (WW i pf) ω ε G0 t0 
                         (fun t ω => vector_nth i pf (α t ω))
                         (fun t ω => vector_nth i pf (X t ω))
                         (fun t ω => vector_nth i pf (ww t ω))
                         G (fun t ω =>
                               Rmax_list_map (seq 0 (S t)) (fun n0 : nat => rvmaxabs (X n0) ω))
                 ); intros.
      apply H14; try easy.
      - intros.
        apply Rle_trans with (r2 := rvmaxabs (X t1) ω).
        + apply Rvector_max_abs_nth_le.
        + apply Rmax_list_map_seq_ge; try lia.
          exists t1.
          split; try lia.
          lra.
      - intros.
        apply H.
      - intros.
        simpl.
        now rv_unfold'.
      - intros.
        now apply H12.
      - intros.
        split.
        + admit.
        + rewrite H9.
          unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult.
          rewrite Rvector_nth_plus, Rvector_nth_mult, Rvector_nth_plus.
          rewrite Rvector_nth_plus, Rvector_nth_scale.
          ring_simplify.
          do 4 rewrite Rplus_assoc.
          apply Rplus_le_compat_l.
          apply Rplus_le_compat_l.
          rewrite Rmult_assoc.
          do 2 rewrite <- Rmult_plus_distr_l.
          apply Rmult_le_compat_l; [apply H |].
          assert (vector_nth i pf (XF (X t1 ω)) <= G t1 ω).
          {
            apply Rle_trans with (r2 := Rvector_max_abs (XF (X t1 ω))).
            eapply Rle_trans.
            apply Rle_abs.
            apply Rvector_max_abs_nth_le.
            eapply Rle_trans.
            apply H7.
            unfold Rmax.
            match_destr.
            - apply Rle_trans with (r2 := 1 * G0).
              + apply Rmult_le_compat_r; try lra.
              + rewrite Rmult_1_l.
                apply Rle_trans with (r2 := G 0%nat ω).
                * rewrite H6.
                  apply Rmax_r.
                * clear r.
                  induction t1; try lra.
                  eapply Rle_trans.
                  apply IHt1.
                  apply H4.
            - apply Rle_trans with (r2 := γ * M t1).
              + apply Rmult_le_compat_l; try lra.
                unfold M.
                apply Rmax_list_map_seq_ge; try lia.
                exists t1.
                split; try lia.
                unfold rvmaxabs; lra.
              + eapply Rle_trans with (r2 := γ * (1 + ε) * (G t1 ω)).
                rewrite Rmult_assoc.
                apply Rmult_le_compat_l; try lra.
                apply H3.
                rewrite H2; lra.
          }
          apply Rle_trans with (r2 := (G t1 ω) + vector_nth i pf (w t1 ω)); try lra.
          unfold ww, vecrvscalerv.
          rewrite Rvector_nth_scale.
          

    Admitted.
    

  Theorem Tsitsiklis1 {n} (X w α : nat -> Ts -> vector R n) 
        (XF : vector R n -> vector R n)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
        (adapt_w : IsAdapted  (Rvector_borel_sa n) w (fun k => F (S k)))
        {rvXF : RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) XF}
        {rvw : forall k i pf, RandomVariable dom borel_sa (fun ω : Ts => vector_nth i pf (w k ω))}
        {iscond : forall k i pf, is_conditional_expectation prts (F k) (vecrvnth i pf (w k)) (ConditionalExpectation prts (filt_sub k) (vecrvnth i pf (w k)))} :

    (forall k ω i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    (forall i pf ω, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Rbar.Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (vecrvnth i pf (w k))) (const 0)) ->
    (exists (A B : R),
        0 < A /\ 0 < B /\
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (rvsqr (vecrvnth i pf (w k))))
                   (rvplus (const A) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    0 <= β < 1 ->
    (exists (D : nonnegreal),
        forall x, Rvector_max_abs (XF x) <= β * Rvector_max_abs x + D) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (X k ω)) (X k) ) (w k))))) ->
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
               0 < G0 /\
               β * G0 + D <= γ * G0).
    {
      exists ((D + 1) / (γ - β)).
      split.
      - apply Rdiv_lt_0_compat; try lra.
        generalize (cond_nonneg D); lra.
      - field_simplify; try lra.
        unfold Rdiv.
        apply Rmult_le_compat_r; try lra.
        left.
        apply Rinv_0_lt_compat.
        lra.
    }
    destruct H8 as [G0 [? ?]].
    assert (forall x i pf,
               Rabs (vector_nth i pf (XF x)) <=
               γ * Rmax (Rvector_max_abs x) G0).
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
        + assert (Rvector_max_abs x > G0) by lra.
          pose (G1 := Rvector_max_abs x - G0).
          replace (Rvector_max_abs x) with (G0 + G1).
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
    assert (adaptX : IsAdapted (Rvector_borel_sa n) X F).
    {
      intros ?.
      induction n0.
      - easy.
      - assert (RandomVariable (F (S n0)) (Rvector_borel_sa n)
                               (vecrvplus (X n0) (vecrvmult (α n0) (vecrvplus (vecrvminus (fun ω : Ts => XF (X n0 ω)) (X n0)) (w n0))))).
        {
          apply Rvector_plus_rv.
          - now apply (RandomVariable_sa_sub (isfilt n0)).
          - apply Rvector_mult_rv.
            + now apply (RandomVariable_sa_sub (isfilt n0)).
            + apply Rvector_plus_rv; try easy.
              apply Rvector_minus_rv.
              * apply (compose_rv (dom2 := Rvector_borel_sa n)); try easy.
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

    assert (Gpos:forall t ω, 0 < G t ω).
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
        apply (rvchoiceb_restricted_rv _ _ _) with (rvc0:=rvc); trivial.
        + apply Restricted_RandomVariable.
          now apply (RandomVariable_sa_sub (isfilt n0)).
        + apply rvscale_rv.
          assert (1 + ε > 1) by lra.

          assert (Hpf:forall (a' : event_restricted_domain
              (exist (sa_sigma (F (S n0)))
                 (fun x : Ts =>
                  (if Rle_dec (M (S n0) x) ((1 + ε) * G n0 x) then true else false) = false)
                 (rvc
                    (exist (fun e : pre_event bool => sa_sigma (discrete_sa bool) e)
                       (fun x : bool => x = false) I)))), 0 < (M (S n0) (` a') / G0)).
          {
            intros [??]; simpl in *.
            match_destr_in e.
            apply Rdiv_lt_0_compat; try lra.
            apply Rlt_le_trans with (r2 := (1 + ε) * G n0 x); try lra.
            apply Rmult_lt_0_compat; try lra.
            apply Gpos.
          } 
          
          cut (RandomVariable (event_restricted_sigma
       (exist (sa_sigma (F (S n0)))
          (fun x : Ts => (if Rle_dec (M (S n0) x) ((1 + ε) * G n0 x) then true else false) = false)
          (rvc
             (exist (fun e : pre_event bool => sa_sigma (discrete_sa bool) e)
                (fun x : bool => x = false) I)))) borel_sa
                    (fun ω =>  powerRZ (1 + ε)
                                       (` (powerRZ_up_log_base_alt (1 + ε) (M (S n0) (` ω) / G0) H15 (Hpf ω))))).
          {
            apply RandomVariable_proper; try easy.
            intros ?.
            unfold powerRZ_ge_fun.
            match_destr; try easy.
            match_destr; try easy.
            - f_equal.
              apply powerRZ_up_log_base_alt_ext.
            - elimtype False.
              generalize (Hpf a); intros.
              elim n1.
              apply Rlt_gt.
              apply H16.
          }
          admit.
    }
    
    pose (ww := fun t => vecrvscalerv (rvinv (G t)) (w t)).

    assert (rvww :  forall (k i : nat) (pf : (i < n)%nat), RandomVariable dom borel_sa (vecrvnth i pf (ww k))).
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
      assert (isfef : IsFiniteExpectation prts (vecrvnth i pf (w k))).
      {
        admit.
      }
      assert (isfefg: IsFiniteExpectation prts (rvmult (vecrvnth i pf (w k)) (rvinv (G k)))).
      {
        admit.
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
          now apply Rmult_lt_0_compat.
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
      revert H15.
      apply almost_impl, all_almost; intros ??.
      unfold ww.
      generalize (is_conditional_expectation_factor_out_nneg_both_Rbar prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))) (rvsqr (rvinv (G k)))); intros.
      specialize (H19 (ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (w k))))).
      admit.
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
    assert (exists (pt : Ts),
               
  Admitted.


  Theorem Tsitsiklis3 {n} (X w α : nat -> Ts -> vector R n) (D0 : Ts -> R) 
        (XF : vector R n -> vector R n)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
        {rvD0 : RandomVariable (F 0%nat) borel_sa D0}        
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
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Rbar.Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const A) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0) ->
    0 < β < 1 ->
    (forall x, Rvector_max_abs (XF x) <= β * Rvector_max_abs x) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
 Proof.
   intros.
   pose (eps := (1/β-1)/3).
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
       apply almost_forall in H4.
       revert H4.
       apply almost_impl, all_almost; intros ????.
       apply H4.
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
         pose (BB := fun (n:nat) => rvplus (const A) (rvscale (Rabs B) (rvsqr D0))).
         eapply lemma1_alpha_alpha with (α := α1) (w := w1) (W := W) (filt_sub := filt_sub) (B := BB) (Ca := Ca); try easy.
         - simpl.
           typeclasses eauto.
         - intros ?.
           unfold BB; simpl.
           apply rvplus_rv; try typeclasses eauto.
           apply rvscale_rv.
           apply rvsqr_rv.
           induction n0; try easy.
           now apply (RandomVariable_sa_sub (isfilt n0)).
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
           apply Rplus_le_compat_l.
           apply Rmult_le_compat_l.
           + apply Rabs_pos.
           + unfold rvmaxlist, Rmax_list_map.
             apply Rmax_list_le_iff.
             * apply map_not_nil.
               simpl.
               discriminate.
             * intros.
               apply in_map_iff in H12.
               destruct H12 as [? [? ?]].
               rewrite <- H12.
               specialize (H3 x1).
               simpl in H3.
               apply Rsqr_le_abs_1.
               generalize (rvmaxabs_pos (X x1) x); intros.
               rewrite Rabs_right; try lra.
               rewrite Rabs_right; trivial.
               destruct (Rle_dec 0 (D0 x)); lra.
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
         - unfold BB.
           apply all_almost; intros.
           exists (rvplus (rvabs (const A)) (rvscale (Rabs B) (rvsqr D0))).
           intros.
           rv_unfold.
           replace (Rabs B * Rsqr (D0 x)) with (Rabs (B * Rsqr(D0 x))).
           + rewrite Rabs_plus.
             apply Rplus_le_compat_r.
             apply Rle_abs.
           + rewrite Rabs_mult.
             f_equal.
             now rewrite <- Rabs_sqr.
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
           specialize (H16 (mkposreal _ H8) (fun ω => mkposreal _ (Dpos k ω))).
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
             rewrite H7.
             unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult.
             rewrite Rvector_nth_plus, Rvector_nth_mult.
             repeat rewrite Rvector_nth_plus.
             rewrite Rvector_nth_scale.
             ring_simplify.
             apply Rplus_le_compat_r.
             apply Rplus_le_compat_l.
             rewrite Rmult_assoc.
             apply Rmult_le_compat_l.
             specialize (H (t + tauk x)%nat x i pf).
             apply H.
             simpl.
             specialize (H6 (X (t + tauk x)%nat x)).
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
             rewrite H7.
             unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult.
             rewrite Rvector_nth_plus, Rvector_nth_mult.
             repeat rewrite Rvector_nth_plus.
             rewrite Rvector_nth_scale.
             ring_simplify.
             apply Rplus_ge_compat_r.
             apply Rplus_ge_compat_l.
             rewrite Ropp_mult_distr_r.
             rewrite Rmult_assoc.
             apply Rmult_ge_compat_l.
             specialize (H (t + tauk x)%nat x i pf).
             apply Rle_ge, H.
             simpl.
             assert (Rabs (vector_nth i pf (XF (X (t + tauk x)%nat x))) <=  β * D k x).
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
           + apply Y_lim with (α := αtau); try easy.
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
             specialize (H14 (tauk x) t).
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
   rewrite Rabs_right; try lra.
   apply Rle_ge.
   apply rvmaxabs_pos.
 Unshelve.
 apply Rvector_max_abs_nth_le.
Qed.

  Theorem Tsitsiklis3_beta_0 {n} (X w α : nat -> Ts -> vector R n) (D0 : Ts -> R) 
        (XF : vector R n -> vector R n)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
        {rvD0 : RandomVariable (F 0%nat) borel_sa D0}        
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
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Rbar.Finite C))) ->
    (forall k i pf, almostR2 prts eq (ConditionalExpectation _ (filt_sub k) (fun ω => vector_nth i pf (w k ω))) (const 0)) ->
    (exists (A B : R),
        forall k i pf, 
          almostR2 prts Rbar_le (ConditionalExpectation 
                                   _ (filt_sub k) 
                                   (fun ω => Rsqr (vector_nth i pf (w k ω))))
                   (rvplus (const A) 
                           (rvscale (Rabs B) (rvmaxlist 
                                         (fun j ω => rvsqr (rvmaxabs (X j)) ω)
                                         k)))) ->
    (forall k, almostR2 prts Rle (rvmaxabs (X k)) D0) ->
    β = 0 ->
    (forall x, Rvector_max_abs (XF x) <= β * Rvector_max_abs x) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
  Proof.
    intros.
    assert (forall x, XF x = Rvector_zero).
    {
      intros.
      specialize (H6 x).
      rewrite H5 in H6.
      rewrite Rmult_0_l in H6.
      apply Rvector_max_abs_zero.
      generalize (Rvector_max_abs_nonneg (XF x)); intros.
      lra.
    }
    assert (forall i pf,
               almost prts (fun ω => is_lim_seq (fun n0 => vector_nth i pf (X n0 ω)) 0)).
    {
      intros.
      pose (X1 := fun t => vecrvnth i pf (X t)).
      pose (α1 := fun t => vecrvnth i pf (α t)).
      pose (w1 := fun t => vecrvnth i pf (w t)).
      
      destruct H3 as [A [B ?]].
      destruct H1 as [Ca ?].
      pose (BB := fun (n:nat) => rvplus (const A) (rvscale (Rabs B) (rvsqr D0))).
      eapply lemma1_alpha_alpha with (α := α1) (w := w1) (W := X1) (filt_sub := filt_sub) (B := BB) (Ca := Ca); try easy.
      - unfold X1.
        now apply vecrvnth_rv.
      - intros ?.
        unfold BB; simpl.
        apply rvplus_rv; try typeclasses eauto.
        apply rvscale_rv.
        apply rvsqr_rv.
        induction n0; try easy.
        now apply (RandomVariable_sa_sub (isfilt n0)).
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
        apply Rplus_le_compat_l.
        apply Rmult_le_compat_l.
        + apply Rabs_pos.
        + unfold rvmaxlist, Rmax_list_map.
          apply Rmax_list_le_iff.
          * apply map_not_nil.
            simpl.
            discriminate.
          * intros.
            apply in_map_iff in H9.
            destruct H9 as [? [? ?]].
            rewrite <- H9.
            specialize (H3 x1).
            simpl in H3.
            apply Rsqr_le_abs_1.
            generalize (rvmaxabs_pos (X x1) x); intros.
            rewrite Rabs_right; try lra.
            rewrite Rabs_right; trivial.
            destruct (Rle_dec 0 (D0 x)); lra.
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
        unfold vecrvnth.
        rewrite H7.
        unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale.
        unfold α1, w1.
        rewrite Rvector_nth_plus, Rvector_nth_mult.
        do 2 rewrite Rvector_nth_plus.
        rewrite Rvector_nth_scale.
        rewrite H8, Rvector_nth_zero.
        unfold vecrvnth.
        lra.
      - unfold BB.
        apply all_almost; intros.
        exists (rvplus (rvabs (const A)) (rvscale (Rabs B) (rvsqr D0))).
        intros.
        rv_unfold.
        replace (Rabs B * Rsqr (D0 x)) with (Rabs (B * Rsqr(D0 x))).
        + rewrite Rabs_plus.
          apply Rplus_le_compat_r.
          apply Rle_abs.
        + rewrite Rabs_mult.
          f_equal.
          now rewrite <- Rabs_sqr.
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


