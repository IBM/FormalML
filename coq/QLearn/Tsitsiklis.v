Require Import List EquivDec Morphisms.
Require Import mdp qvalues fixed_point pmf_monad.
Require Import RealAdd CoquelicotAdd EquivDec.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import infprod Dvoretzky Expectation RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import RandomVariableL2.
Require Import ConditionalExpectation VectorConditionalExpectation DiscreteProbSpace.
Require Import IndefiniteDescription ClassicalDescription.
Require Import RelationClasses.
Require Import Dvoretzky infprod.
Require Import Martingale MartingaleStopped.
Require Bellman.
Require Import FiniteTypeVector.

Set Bullet Behavior "Strict Subproofs".

Section Stochastic_convergence.
  
Context {Ts : Type}  (* (w α : Ts -> nat -> R)  *)
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
       almost prts (fun ω => Rbar_lt (Lim_seq (sum_n (fun n : nat => rvsqr (α n) ω))) (Finite A2))) ->

   (exists (A3 : R),
       almost prts (fun ω => Rbar_lt (Lim_seq (sum_n (fun n : nat => rvsqr (β n) ω))) (Finite A3))) ->
  (forall n, rv_eq (W (S n)) (rvplus (rvmult (rvminus (const 1) (α n)) (W n)) (rvmult (w n) (β n)))) ->
  almost _ (fun ω => is_lim_seq (fun n => W n ω) (Finite 0)).
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
    replace (Finite (const 0 x)) with (Rbar_mult  (Finite (β n x)) (Finite  (const 0 x))).
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
                      (fun n omega => Finite (rvsum (fun n0 => rvsqr (β n0)) n omega))
                      (Rbar_rvlim (fun n omega => Finite (rvsum (fun n0 => rvsqr (β n0)) n omega)))
                   ); intros.
        specialize (H6 (const (Finite A2))).
        cut_to H6.
        -- assert  (isfefn : forall n : nat,
                   Rbar_IsFiniteExpectation prts
                     (fun omega : Ts =>
                        (rvsum (fun n0 : nat => rvsqr (β n0)) n omega))).
           { 
             intros.
             apply Rbar_IsFiniteExpectation_nnf_bounded_almost with
                 (g := const (Finite A2)).
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
                         (rvsum (fun n0 : nat => rvsqr (β n0)) n omega)))).
           {
             apply Rbar_IsFiniteExpectation_nnf_bounded_almost with
                 (g := const (Finite A2)).
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
                                 Finite (rvsum (fun n0 : nat => rvsqr (β n0)) n omega)))).
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
  (exists (b : Ts -> R),
      almost prts (fun ω => forall n, B n ω <= Rabs (b ω))) ->
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
   apply (@exists_almost Ts dom prts _ (fun (T : nat) =>
                     (fun ω : Ts => forall t0 t : nat, (t0 >= T)%nat -> rvabs (W t t0) ω <= delta ω))).
   revert H2.
   apply almost_impl, all_almost; intros ??.
   now apply lemma2 with (α := α) (w := w).
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
        apply lemma8_abs with (β := β) (D := D) (α := α) (w := w); trivial.
      + simpl.
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
    - unfold part_prod, part_prod_n.
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
    val1 <= val2 ->
    (proj1_sig (powerRZ_up_log_base _ _ pfb pf1) <=
     proj1_sig (powerRZ_up_log_base _ _ pfb pf2))%Z.
  Proof.
    intros.
    simpl.
    apply up_le.
    unfold Rdiv.
    apply Rmult_le_compat_r.
    - left.
      apply Rinv_0_lt_compat.
      rewrite <- ln_1.
      apply ln_increasing; lra.
    - apply ln_le; lra.
  Qed.

  Lemma powerRZ_up_log_alt_increasing (base val1 val2 : R)
        (pfb: base > 1)
        (pf1: val1 > 0)
        (pf2: val2 > 0) :
    val1 <= val2 ->
    (proj1_sig (powerRZ_up_log_base_alt _ _ pfb pf1) <=
     proj1_sig (powerRZ_up_log_base_alt _ _ pfb pf2))%Z.
  Proof.
    intros.
    unfold proj1_sig.
    match_destr; match_destr.
    destruct (Z_le_gt_dec x x0); trivial.
    elimtype False.
    assert (x0 <= x - 1)%Z by lia.
    assert (powerRZ base x0 <= powerRZ base (x-1)%Z).
    {
      repeat rewrite powerRZ_Rpower by lra.
      apply Rle_Rpower; [lra |].
      now apply IZR_le.
    }
    lra.
  Qed.    

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


  Lemma powerRZ_ge_fun_rv (base : R) :
    RandomVariable borel_sa borel_sa (fun v => powerRZ_ge_fun base v).
  Proof.
    apply increasing_rv.
    intros.
    unfold powerRZ_ge_fun.
    match_destr; try lra.
    match_destr.
    - match_destr.
      + rewrite powerRZ_Rpower; try lra.
        rewrite powerRZ_Rpower; try lra.
        apply Rle_Rpower; try lra.
        apply IZR_le.
        now apply powerRZ_up_log_alt_increasing.
      + assert (v <= 0) by lra.
        generalize (Rlt_le_trans 0 u v); intros.
        cut_to H1; try lra.
    - match_destr; try lra.
      apply powerRZ_le; try lra.
  Qed.

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

   Lemma rvinv_Rinv (x : Ts -> R) (ω : Ts) :
     0 < x ω ->
     rvinv x ω = / (x ω).
   Proof.
     unfold rvinv, rvpower, const.
     intros.
     replace (-1) with (Ropp 1) by lra.
     rewrite power_Ropp; trivial.
     f_equal.
     rewrite power_1; lra.
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

  Lemma lemma3 {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R) (ω : Ts) (ε G0 :R)
        (t0 : nat) (α x ww : nat -> Ts -> vector R (S n)) (M G : nat -> Ts -> R) 
        (XF : vector R (S n) -> vector R (S n)) :
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
                     (vecrvplus (x k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (x k ω)) (x k) ) (vecrvscalerv (G k) (ww k)))))) ->
    (forall k i pf, rv_le (rvabs (vecrvnth i pf (fun ω => XF (x k ω)))) (G k)) ->
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

   Lemma lemma3_almost {n} (W : forall (i : nat),  (i < (S n))%nat -> nat -> nat -> Ts -> R) (ε G0 :R)
         (α x ww : nat -> Ts -> vector R (S n)) (M G : nat -> Ts -> R) 
        (XF : vector R (S n) -> vector R (S n)) :
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
                     (vecrvplus (x k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (x k ω)) (x k) ) (vecrvscalerv (G k) (ww k)))))) ->
    (forall k i pf, rv_le (rvabs (vecrvnth i pf (fun ω => XF (x k ω)))) (G k)) ->
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
    

  Theorem Tsitsiklis1 {n} (β : R) (X w α : nat -> Ts -> vector R (S n)) 
        (XF : vector R (S n) -> vector R (S n))
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa (S n)) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S n)) (X 0%nat)}
        (adapt_w : IsAdapted  (Rvector_borel_sa (S n)) w (fun k => F (S k)))
        {rvXF : RandomVariable (Rvector_borel_sa (S n)) (Rvector_borel_sa (S n)) XF}
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
    assert (adaptX : IsAdapted (Rvector_borel_sa (S n)) X F).
    {
      intros ?.
      induction n0.
      - easy.
      - assert (RandomVariable (F (S n0)) (Rvector_borel_sa (S n))
                               (vecrvplus (X n0) (vecrvmult (α n0) (vecrvplus (vecrvminus (fun ω : Ts => XF (X n0 ω)) (X n0)) (w n0))))).
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
        now rewrite Rbar_Expectation_const in H15.
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

  Theorem Tsitsiklis3_beta_pos {n} (X w α : nat -> Ts -> vector R n) (β : R) (D0 : Ts -> R) 
        (XF : vector R n -> vector R n)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
        {rvXF : RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) XF}
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
    0 < β < 1 ->
    (forall x, Rvector_max_abs (XF x)<= 
               β * Rvector_max_abs x) ->
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
         - exists (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr D0))).
           apply almost_forall in H4.
           revert H4.
           apply almost_impl, all_almost; intros ???.
           unfold BB.
           rv_unfold.
           assert (Rabs B * Rsqr (D0 x) = Rabs (B * Rsqr(D0 x))).
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

  Theorem Tsitsiklis3_beta_0 {n} (X w α : nat -> Ts -> vector R n) (β : R) (D0 : Ts -> R) 
        (XF : vector R n -> vector R n)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
        {rvXF : RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) XF}
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
      pose (BB := fun (n : nat) =>
                    rvplus (const (Rabs A)) 
                           (rvscale (Rabs B)
                                    (rvmaxlist (fun (j : nat) => rvsqr (rvmaxabs (X j))) n))).
(*
      pose (BB := fun (n:nat) => rvplus (const A) (rvscale (Rabs B) (rvsqr D0))).
*)
      eapply lemma1_alpha_alpha with (α := α1) (w := w1) (W := X1) (filt_sub := filt_sub) (B := BB) (Ca := Ca); try easy.
      - unfold X1.
        now apply vecrvnth_rv.
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
      - exists (rvplus (const (Rabs A)) (rvscale (Rabs B) (rvsqr D0))).
        apply almost_forall in H4.
        revert H4.
        apply almost_impl, all_almost; intros ???.
        unfold BB.
        rv_unfold.
        assert (Rabs B * Rsqr (D0 x) = Rabs (B * Rsqr(D0 x))).
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

  Theorem Tsitsiklis3 {n} (X w α : nat -> Ts -> vector R n) (β : R) (D0 : Ts -> R) 
        (XF : vector R n -> vector R n)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
(*
        {rvD0 : RandomVariable (F 0%nat) borel_sa D0}        
*)
        {XF_rv : RandomVariable (Rvector_borel_sa n) (Rvector_borel_sa n) XF}
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
    (forall x, Rvector_max_abs (XF x) <= β * Rvector_max_abs x) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
  Proof.
    intros.
    destruct (Rlt_dec 0 β).
    - now apply Tsitsiklis3_beta_pos with (w0 := w) (β0 := β) (α0 := α) (D1 := D0) (XF0 := XF) (filt_sub0 := filt_sub) (rvw0 := rvw).
    - assert (β = 0) by lra.
      now apply Tsitsiklis3_beta_0 with (w0 := w) (β0 := β) (α0 := α) (D1 := D0) (XF0 := XF) (filt_sub0 := filt_sub) (rvw0 := rvw).
  Qed.

    Theorem Tsitsiklis_1_3 {n} (β : R) (X w α : nat -> Ts -> vector R n) 
        (XF : vector R n -> vector R n)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F) 
        (filt_sub : forall k, sa_sub (F k) dom) 
        (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
        {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
        (npos : (0 < n)%nat)
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
    (forall x, Rvector_max_abs (XF x) <= β * Rvector_max_abs x) ->
    (forall k, rv_eq (X (S k)) 
                     (vecrvplus (X k) (vecrvmult (α k) (vecrvplus (vecrvminus (fun ω => XF (X k ω)) (X k) ) (w k))))) ->
    almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
  Proof.
    intros.
    destruct n; try lia.
    generalize (Tsitsiklis1 β X w α XF isfilt filt_sub 
                            adapt_alpha); intros Tsit1.
    specialize (Tsit1 adapt_w _ _ iscond H H0 H1 H2 H3 H4).
    assert (exists D : nonnegreal,
          forall x : vector R (S n),
          Rvector_max_abs (XF x) <= β * Rvector_max_abs x + D).
    {
      assert (0 <= 0) by lra.
      exists (mknonnegreal 0 H7).
      intros.
      simpl.
      now rewrite Rplus_0_r.
    }
    specialize (Tsit1 H7 H6).
    destruct Tsit1 as [D0 Tsit1].
    pose (D0' := rvplus (const 1) (rvabs D0)).
    generalize (Tsitsiklis3 X w α β D0' XF isfilt filt_sub); intros Tsit3.
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
      
  Lemma is_condexp_diff_ce_zero {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (f : Ts -> R)
        (ce : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f} 
        {isfce:IsFiniteExpectation prts ce} 
        {rvce : RandomVariable dom borel_sa ce}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce}  :
      is_conditional_expectation prts dom2 f ce ->
      is_conditional_expectation prts dom2 (rvminus f ce) (const 0).
  Proof.
    intros.
    generalize (is_conditional_expectation_minus prts sub f ce ce ce H); intros.
    cut_to H0.
    - revert H0.
      apply is_conditional_expectation_proper; try easy.
      apply all_almost; intros.
      unfold Rbar_rvminus, Rbar_rvopp, Rbar_rvplus, const.
      simpl.
      apply Rbar_finite_eq.
      lra.
    - eapply (is_conditional_expectation_id (dom2 := dom2) prts ce).
      Unshelve.
      now apply (Rbar_real_rv ce); intros.
  Qed.
    
  Lemma is_condexp_diff_indep_zero {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (f : Ts -> R)
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f} :
    independent_sas prts (pullback_rv_sub _ _ _ rv) sub ->
    is_conditional_expectation prts dom2 
                               (rvminus f (const (FiniteExpectation prts f)))
                               (const 0).
  Proof.
    intros.
    eapply is_condexp_diff_ce_zero; try easy.
    - apply IsFiniteExpectation_const.
    - now apply (is_conditional_expectation_independent_sa prts sub).
  Qed.

  Lemma expec_sqr_sum_bound (x y : Ts -> R)
        {rvx : RandomVariable dom borel_sa x}
        {rvy : RandomVariable dom borel_sa y} :
    Rbar_le
      (NonnegExpectation (rvsqr (rvplus x y)))
      (Rbar_mult 2 (Rbar_plus (NonnegExpectation (rvsqr x)) 
                              (NonnegExpectation (rvsqr y)))).
  Proof.
    rewrite <- NonnegExpectation_sum; try typeclasses eauto.
    assert (0 < 2) by lra.
    replace 2 with (pos (mkposreal _ H)); try now simpl.
    erewrite <- NonnegExpectation_scale.
    apply NonnegExpectation_le.
    generalize (rvprod_bound x y); intros.
    intros ?.
    rv_unfold.
    specialize (H0 a); simpl in H0.
    rewrite Rsqr_plus.
    simpl; lra.
  Qed.

  Lemma SimpleExpectation_compose {Td} (f1 : Ts -> Td) (f2 : Td -> R)
        {dec : EqDec Td eq}
        {σd: SigmaAlgebra Td} 
        {has_pre: HasPreimageSingleton σd}
        {rv1: RandomVariable dom σd f1}
        {rv2: RandomVariable dom borel_sa (fun v => f2 (f1 v))}
        {frf1 : FiniteRangeFunction f1}
        {frf2 : FiniteRangeFunction (fun v => f2 (f1 v))} :
    SimpleExpectation (fun v => f2 (f1 v)) = 
    list_sum (map (fun (v : Td) => (f2 v) * (ps_P (preimage_singleton f1 v)))
                 (nodup dec (frf_vals (FiniteRangeFunction := frf1)))).
 Proof.
   rewrite (expectation_indicator_sum (fun v : Ts => f2 (f1 v)) 
                                      (induced_sigma_generators' frf1) 
                                      (induced_gen_ispart' frf1)).
   unfold induced_sigma_generators'.
   rewrite map_map.

   f_equal.
   apply map_ext_in.
   intros.
   unfold SimpleExpectation, SimpleExpectation.induced_sigma_generators'_obligation_1.
   destruct (classic (exists (x : Ts), f1 x = a)).
   - rewrite list_sum_all_but_zero with (c := f2 a); try easy.
    + {
       simpl.
       destruct (Req_EM_T (f2 a) 0).
     - rewrite e.
       lra.
     - f_equal.
       apply ps_proper.
       intros ?.
       simpl.
       unfold pre_event_preimage.
       unfold SimpleExpectation.induced_sigma_generators'_obligation_1.
       unfold pre_event_singleton.
       rv_unfold.
       match_destr; unfold  Equivalence.equiv, complement in *.
       + subst.
         split;trivial.
         intros _.
         lra.
       + split; try tauto.
         lra.
     }
   + apply NoDup_nodup.
   + destruct frf1; destruct frf2.
     apply nodup_In.
     apply in_map_iff.
     simpl.
     destruct H0.
     rewrite <- H0.
     exists ((f2 (f1 x)), 1).
     simpl.
     split; try lra.
     simpl.
     apply in_prod_iff.
     simpl.
     split; try easy; try tauto.
   + {
     intros.
     simpl.
     destruct (Req_EM_T r 0).
     - rewrite e.
       lra.
     - apply Rmult_eq_0_compat_l.
       unfold SimpleExpectation.induced_sigma_generators'_obligation_1.
       assert (rv_eq
                 (rvmult (fun v0 : Ts => f2 (f1 v0))
                         (EventIndicator (fun x : Ts => dec (f1 x) a)))
                 (rvscale (f2 a)
                          (EventIndicator (fun x : Ts => dec (f1 x) a)))).
       {
         intros ?.
         rv_unfold.
         match_destr; try lra.
         unfold  Equivalence.equiv in e.
         now rewrite e.
       }         
       generalize (ps_none prts); intros.
       replace R0 with 0 in H3 by lra.
       rewrite <- H3.
       apply ps_proper.
       intros ?; simpl.
       unfold pre_event_preimage, pre_event_singleton, pre_event_none.
       rewrite H2.
       rv_unfold.
       match_destr; lra.
     }
   - assert (event_equiv (preimage_singleton f1 a) 
                         event_none).
     {
       intros ?.
       simpl.
       unfold pre_event_preimage, pre_event_singleton, pre_event_none.
       rewrite not_exists in H0.
       specialize (H0 x).
       tauto.
     }
     generalize (ps_none prts); intros none.
     replace R0 with 0 in none by lra.
     assert (ps_P (preimage_singleton f1 a) = 0).
     {
       rewrite <- none.
       now apply ps_proper.
     }
     rewrite H2.
     rewrite Rmult_0_r.
     simpl.
     apply list_sum0_is0, Forall_forall.
     intros.
     apply in_map_iff in H3.
     destruct H3 as [? [? ?]].
     destruct (Req_EM_T x0 0).
     + rewrite e in H3.
       lra.
     + rewrite <- H3.
       apply Rmult_eq_0_compat.
       right.
       rewrite <- none.
       apply ps_proper.
       intros ?.
       simpl.
       unfold pre_event_preimage, pre_event_singleton, pre_event_none.
       rv_unfold.
       match_destr.
       red in e.
       * rewrite not_exists in H0.
         now specialize (H0 x1).
       * rewrite Rmult_0_r.
         lra.
   Qed.

 Program Global Instance fin_image_frf {A B} {fin:FiniteType B} (f:A->B) : FiniteRangeFunction f
   := {|
     frf_vals := fin_elms
   |}.
 Next Obligation.
   apply fin_finite.
 Qed.
 
  Lemma SimpleExpectation_compose_Finite_type {Td} (f1 : Ts -> Td) (f2 : Td -> R)
        {dec : EqDec Td eq}
        {fin : FiniteType Td}
        {σd: SigmaAlgebra Td} 
        {has_pre: HasPreimageSingleton σd}
        {rv1: RandomVariable dom σd f1}
        {rv2: RandomVariable dom borel_sa (fun v => f2 (f1 v))}
        {frf2 : FiniteRangeFunction (fun v => f2 (f1 v))} :
    SimpleExpectation (fun v => f2 (f1 v)) = 
    list_sum (map (fun (v : Td) => (f2 v) * (ps_P (preimage_singleton f1 v)))
                  (fin_elms (FiniteType := fin_finite_nodup _))).
  Proof.
    now rewrite (SimpleExpectation_compose _ _).
  Qed.

  Program Instance inner_frf_compose {A B C} (g1 : A -> B) (g2 : B -> C)
          (frf1 : FiniteRangeFunction g1) :
    FiniteRangeFunction (compose g2 g1)
    := { frf_vals := map g2 frf_vals }.
  Next Obligation.
    apply in_map_iff.
    exists (g1 x).
    split; trivial.
    now destruct frf1.
  Qed.

  Lemma FiniteExpectation_compose_Finite_type {Td} (f1 : Ts -> Td) (f2 : Td -> R)
        {dec : EqDec Td eq}
        {fin : FiniteType Td}
        {σd: SigmaAlgebra Td} 
        {has_pre: HasPreimageSingleton σd}
        {rv1: RandomVariable dom σd f1}
        {rv2: RandomVariable dom borel_sa (fun v => f2 (f1 v))}
(*        {frf2 : FiniteRangeFunction (fun v => f2 (f1 v))} *)
        {isfe : IsFiniteExpectation prts (fun v : Ts => f2 (f1 v))} :
    FiniteExpectation prts (fun v => f2 (f1 v)) = 
    list_sum (map (fun (v : Td) => (f2 v) * (ps_P (preimage_singleton f1 v)))
                  (fin_elms (FiniteType := fin_finite_nodup _))).
  Proof.
    assert (frf2 : FiniteRangeFunction (fun v => f2 (f1 v))).
    {
      assert (FiniteRangeFunction f1) by apply fin_image_frf.
      now apply inner_frf_compose.
    }
    erewrite FiniteExpectation_simple.
    apply SimpleExpectation_compose_Finite_type.
  Qed.

  Lemma nncondexp_sqr_sum_bound_nneg (x y : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rvx : RandomVariable dom borel_sa x}
        {rvy : RandomVariable dom borel_sa y} :
    almostR2 prts Rbar_le
             (NonNegCondexp prts sub (rvsqr (rvplus x y)))
             (Rbar_rvmult (const 2)
                          (Rbar_rvplus (NonNegCondexp prts sub (rvsqr x)) 
                                       (NonNegCondexp prts sub (rvsqr y)))).
  Proof.
    intros.
    generalize (NonNegCondexp_plus prts sub (rvsqr x) (rvsqr y)); intros.
    assert (0 <= 2) by lra.
    assert (nnegsc: NonnegativeFunction (rvscale (mknonnegreal 2 H0) (rvplus (rvsqr x) (rvsqr y)))).
    {
      typeclasses eauto.
    }
    generalize (NonNegCondexp_scale prts sub (mknonnegreal 2 H0) (rvplus (rvsqr x) (rvsqr y))); intros.
    generalize (NonNegCondexp_ale prts sub
                                  (rvsqr (rvplus x y))
                                  (rvscale (mknonnegreal 2 H0)
                                           (rvplus (rvsqr x) 
                                                   (rvsqr y)))); intros.
    apply almost_prob_space_sa_sub_lift in H.
    apply almost_prob_space_sa_sub_lift in H1.
    apply almost_prob_space_sa_sub_lift in H2.    
    - revert H; apply almost_impl.
      revert H1; apply almost_impl.
      revert H2; apply almost_impl.
      apply all_almost; intros ????.
      unfold Rbar_rvmult.
      rewrite <- H2.
      simpl in H1.
      unfold Rbar_rvmult, const  in H1.
      unfold const.
      rewrite <- H1.
      apply H.
    - apply all_almost.
      intros.
      generalize (rvprod_bound x y); intros.
      rv_unfold.
      specialize (H3 x0); simpl in H3.
      rewrite Rsqr_plus.
      simpl; lra.
  Qed.

  Lemma conditional_variance_bound1_alt (x : Ts -> R) (c : R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isfe : IsFiniteExpectation prts x} :
    almostR2 prts Rle (rvsqr x) (const c²) ->
    almostR2 prts Rbar_le (Rbar_rvminus (ConditionalExpectation prts sub (rvsqr x))
                                        (rvsqr (FiniteConditionalExpectation prts sub x)))
          (const c²).
  Proof.
    intros.
    assert (csqr_nn:NonnegativeFunction (const (B := Ts) (c²))).
    {
      intros ?.
      unfold const.
      apply Rle_0_sqr.
    }
    generalize (NonNegCondexp_ale 
                  prts sub (rvsqr x) (const (c²))); intros.
    cut_to H0; try easy.
    apply almost_prob_space_sa_sub_lift in H0.
    revert H0; apply almost_impl.
    revert H; apply almost_impl.
    apply all_almost; intros ???.
    rewrite <- Condexp_nneg_simpl in H0.
    rewrite <- Condexp_nneg_simpl in H0.    
    rewrite Condexp_const in H0.
    rv_unfold.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
    eapply Rbar_le_trans.
    shelve.
    apply H0.
    Unshelve.
    simpl.
    destruct  (ConditionalExpectation prts sub (fun omega : Ts => (x omega)²) x0).
    - simpl.
      assert (0 <=  (FiniteConditionalExpectation prts sub x x0)²).
      {
        apply Rle_0_sqr.
      }
      lra.
    - now simpl.
    - now simpl.
 Qed.

  Lemma conditional_variance_bound1 (x : Ts -> R) (c : R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isfe : IsFiniteExpectation prts x}
        {isfe0 : IsFiniteExpectation prts (rvsqr x)} :
    almostR2 prts Rle (rvsqr x) (const c²) ->
    almostR2 prts Rle (rvminus (FiniteConditionalExpectation prts sub (rvsqr x))
                               (rvsqr (FiniteConditionalExpectation prts sub x)))
          (const c²).
  Proof.
    intros.
    generalize (FiniteCondexp_ale 
                  prts sub (rvsqr x) (const c²)); intros.
    cut_to H0; try easy.
    apply almost_prob_space_sa_sub_lift in H0.
    revert H0; apply almost_impl.
    revert H; apply almost_impl.
    apply all_almost; intros ???.
    rewrite FiniteCondexp_const in H0.
    rv_unfold.
    eapply Rle_trans.
    shelve.
    apply H0.
    Unshelve.
    assert (0 <=  (FiniteConditionalExpectation prts sub x x0)²).
    {
      apply Rle_0_sqr.
    }
    lra.
  Qed.

  Lemma conditional_variance_bound1_fun (x c : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {rv2 : RandomVariable dom2 borel_sa c}        
        {isfe : IsFiniteExpectation prts x}
        {isfe2 : IsFiniteExpectation prts c}
        {isfe0 : IsFiniteExpectation prts (rvsqr x)} :
    almostR2 prts Rle (rvsqr x) (c) ->
    almostR2 prts Rle (rvminus (FiniteConditionalExpectation prts sub (rvsqr x))
                               (rvsqr (FiniteConditionalExpectation prts sub x)))
             (c).
  Proof.
    intros.
    assert (rv3: RandomVariable dom borel_sa c).
    {
      now apply (RandomVariable_sa_sub sub).
    }
    generalize (FiniteCondexp_ale 
                  prts sub (rvsqr x) (c)); intros.
    cut_to H0; try easy.
    apply almost_prob_space_sa_sub_lift in H0.
    revert H0; apply almost_impl.
    revert H; apply almost_impl.
    apply all_almost; intros ???.
    rewrite FiniteCondexp_id with (f := c) in H0; trivial.
    rv_unfold.
    eapply Rle_trans.
    shelve.
    apply H0.
    Unshelve.
    assert (0 <=  (FiniteConditionalExpectation prts sub x x0)²).
    {
      apply Rle_0_sqr.
    }
    lra.
  Qed.

  Ltac rewrite_condexp_pf_irrel H
  := match type of H with
     | @NonNegCondexp ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv1 ?nnf1 ?x = _ =>
         match goal with
           [|- context [@NonNegCondexp ?Ts ?dom ?prts ?dom2 ?sub ?g ?rv2 ?nnf2 ?x]] =>
             rewrite <- (fun pf => @NonNegCondexp_ext
                                 Ts dom prts dom2 sub f g rv1 rv2 nnf1 nnf2 pf x); [rewrite H | reflexivity]
         end
     | @ConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv1 ?x = _ =>
         match goal with
           [|- context [@ConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?g ?rv2 ?x]] =>
             rewrite <- (fun pf => @ConditionalExpectation_ext
                                 Ts dom prts dom2 sub f g rv1 rv2 pf x); [rewrite H | reflexivity]
         end
     | @FiniteConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv1 ?nnf1 ?x = _ =>
         match goal with
           [|- context [@FiniteConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv2 ?nnf2 ?x]] =>
             rewrite <- (fun pf => @FiniteConditionalExpectation_ext
                                 Ts dom prts dom2 sub f f rv1 rv2 nnf1 nnf2 pf x); [rewrite H | reflexivity]
         end
     end.

  Lemma isfe_L2_variance (x : Ts -> R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (rv : RandomVariable dom borel_sa x) 
        {isl2: IsLp prts 2 x} :
    IsFiniteExpectation prts x /\
    IsFiniteExpectation prts (rvsqr x) /\
    RandomVariable 
      dom borel_sa
      (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))) /\
    IsFiniteExpectation 
      prts
      (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))) /\
    IsFiniteExpectation
      prts
      (rvsqr (FiniteConditionalExpectation prts sub x)) /\
    IsFiniteExpectation prts  (rvmult (FiniteConditionalExpectation prts sub x) x).
  Proof.
    generalize (conditional_expectation_L2fun_L2 prts sub x); intros.
    assert (almostR2 (prob_space_sa_sub prts sub) eq 
                     (conditional_expectation_L2fun prts sub x)
                     (FiniteConditionalExpectation prts sub x)).
    {
      generalize (conditional_expectation_L2fun_eq3 prts sub x); intros.
      generalize (FiniteCondexp_is_cond_exp prts sub x); intros.
      generalize (is_conditional_expectation_unique prts sub x _ _ H0 H1); intros.
      revert H2.
      apply almost_impl, all_almost; intros ??.
      now apply Rbar_finite_eq in H2.
   }
    apply almostR2_prob_space_sa_sub_lift in H0.
    assert (RandomVariable dom borel_sa (FiniteConditionalExpectation prts sub x)).
    {
      apply FiniteCondexp_rv'.
    }
    repeat split.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - assert (IsFiniteExpectation 
                prts
                (rvsqr (rvminus x (conditional_expectation_L2fun prts sub x)))).
      {
        assert (IsLp prts 2 (rvminus x (conditional_expectation_L2fun prts sub x))).
        {
          assert (0 <= 2) by lra.
          apply (IsLp_minus prts (mknonnegreal 2 H2)); try easy.
          apply RandomVariable_sa_sub; trivial.
          apply conditional_expectation_L2fun_rv.
        }
        typeclasses eauto.
      }
      eapply (IsFiniteExpectation_proper_almostR2 
               prts
               (rvsqr (rvminus x (conditional_expectation_L2fun prts sub x)))
               (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x)))).
      revert H0.
      apply almost_impl, all_almost; intros ??.
      rv_unfold.
      now rewrite H0.
    - assert (IsFiniteExpectation prts (rvsqr (conditional_expectation_L2fun prts sub x))).
      {
        typeclasses eauto.
      }
      eapply (IsFiniteExpectation_proper_almostR2
               prts
               (rvsqr (conditional_expectation_L2fun prts sub x))
               (rvsqr (FiniteConditionalExpectation prts sub x))).
      revert H0.
      apply almost_impl, all_almost; intros ??.
      rv_unfold.
      now rewrite H0.
    - assert (IsFiniteExpectation prts (rvmult (conditional_expectation_L2fun prts sub x) x)).
      {
        typeclasses eauto.
      }
      eapply (IsFiniteExpectation_proper_almostR2
                    prts
                    (rvmult (conditional_expectation_L2fun prts sub x) x)
                    (rvmult (FiniteConditionalExpectation prts sub x) x)).
      revert H0.
      apply almost_impl, all_almost; intros ??.
      rv_unfold.
      now rewrite H0.
  Qed.

  Lemma conditional_variance_alt (x : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isfe1 : IsFiniteExpectation prts x} 
        {isfe2 : IsFiniteExpectation prts (rvsqr x)}        
        {rv2 : RandomVariable 
                 dom borel_sa
                 (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x)))} 
        {isfe3 : IsFiniteExpectation 
                   prts
                   (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x)))}
        {isfe4 : IsFiniteExpectation
                   prts
                   (rvsqr (FiniteConditionalExpectation prts sub x))}
        {isfe5 : IsFiniteExpectation prts  (rvmult (FiniteConditionalExpectation prts sub x) x)}  :
    almostR2 prts eq
             (FiniteConditionalExpectation 
                prts sub
                (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x)))) 
             (rvminus (FiniteConditionalExpectation prts sub (rvsqr x))
                      (rvsqr (FiniteConditionalExpectation prts sub x))).
  Proof.
      assert (rv3: RandomVariable dom2 borel_sa (FiniteConditionalExpectation prts sub x)).
      {
        apply FiniteCondexp_rv.
      }
      assert (rv4: RandomVariable dom borel_sa (FiniteConditionalExpectation prts sub x)).
      {
        apply FiniteCondexp_rv'.
      }
      assert (rv5: RandomVariable dom borel_sa (rvsqr (FiniteConditionalExpectation prts sub x))).
      {
        typeclasses eauto.
      }
      assert (rv6: RandomVariable dom borel_sa (rvmult (FiniteConditionalExpectation prts sub x) x)).
      {
        typeclasses eauto.
      }
      assert (rv7: RandomVariable dom borel_sa
                             (rvplus (rvscale (-2) (rvmult (FiniteConditionalExpectation prts sub x) x))
                                     (rvsqr (FiniteConditionalExpectation prts sub x)))).
      {
        typeclasses eauto.
      }
      assert (rv8: RandomVariable 
                dom borel_sa
                (rvplus (rvsqr x)
                        (rvplus (rvscale (-2) (rvmult (FiniteConditionalExpectation prts sub x) x))
                                (rvsqr (FiniteConditionalExpectation prts sub x))))).
      {
        typeclasses eauto.
      }

     assert (isfe6: IsFiniteExpectation prts (FiniteConditionalExpectation prts sub x)).
      {
        apply FiniteCondexp_isfe.
      }
      
      assert (isfe7: IsFiniteExpectation prts
                                  (rvplus (rvscale (-2) (rvmult (FiniteConditionalExpectation prts sub x) x))
                                          (rvsqr (FiniteConditionalExpectation prts sub x)))).
      {
        apply IsFiniteExpectation_plus; try typeclasses eauto.
      }

      assert (isfe8: IsFiniteExpectation 
                prts
                (rvplus (rvsqr x)
                        (rvplus (rvscale (-2) (rvmult (FiniteConditionalExpectation prts sub x) x))
                                (rvsqr (FiniteConditionalExpectation prts sub x))))).
      {
        apply IsFiniteExpectation_plus; try typeclasses eauto.
      }
      assert (almostR2 (prob_space_sa_sub prts sub) eq
                       (FiniteConditionalExpectation 
                          prts sub
                          (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))))
                       (FiniteConditionalExpectation 
                          prts sub
                          (rvplus (rvsqr x)
                                  (rvplus
                                     (rvscale (- 2)
                                      (rvmult (FiniteConditionalExpectation prts sub x) x))
                                     (rvsqr (FiniteConditionalExpectation prts sub x)))))).
      {
        apply FiniteCondexp_proper.
        apply all_almost; intros ?.
        rv_unfold.
        unfold Rsqr.
        lra.
      }
      generalize (FiniteCondexp_plus 
                    prts sub (rvsqr x)
                    (rvplus (rvscale (-2)
                             (rvmult (FiniteConditionalExpectation prts sub x) x))
                            (rvsqr (FiniteConditionalExpectation prts sub x))) ); intros.
      generalize (FiniteCondexp_plus 
                    prts sub 
                    (rvscale (-2)
                             (rvmult (FiniteConditionalExpectation prts sub x) x))
                    (rvsqr (FiniteConditionalExpectation prts sub x))) ; intros.

      generalize (FiniteCondexp_scale 
                    prts sub (-2)
                    (rvmult (FiniteConditionalExpectation prts sub x) x)); intros.
      generalize (FiniteCondexp_factor_out_l prts sub x (FiniteConditionalExpectation prts sub x)); intros.

      apply almost_prob_space_sa_sub_lift in H.
      apply almost_prob_space_sa_sub_lift in H0.
      apply almost_prob_space_sa_sub_lift in H1.
      apply almost_prob_space_sa_sub_lift in H2.
      apply almost_prob_space_sa_sub_lift in H3.            
      revert H3; apply almost_impl.
      revert H2; apply almost_impl.
      revert H1; apply almost_impl.
      revert H0; apply almost_impl.      
      revert H; apply almost_impl.
      apply all_almost; intros ??????.
      rewrite H.
      rewrite_condexp_pf_irrel H0.
      unfold rvplus at 1.
      rewrite_condexp_pf_irrel H1.
      unfold rvplus at 1.
      rewrite H2.
      unfold rvscale.
      rewrite H3.
      rv_unfold.
      unfold Rsqr.

      rewrite (FiniteCondexp_id _ _ (fun omega : Ts =>
                                       FiniteConditionalExpectation prts sub x omega * FiniteConditionalExpectation prts sub x omega)).
      lra.
  Qed.

  Instance conditional_variance_L2_alt_rv (x : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isl2: IsLp prts 2 x} :
     RandomVariable 
       dom borel_sa
       (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))).
   Proof.
     now generalize (isfe_L2_variance x sub rv); intros.
   Qed.

  Instance conditional_variance_L2_alt_isfe (x : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isl2: IsLp prts 2 x} :
    IsFiniteExpectation 
      prts
      (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))).
   Proof.
     now generalize (isfe_L2_variance x sub rv); intros.
   Qed.    

           
   Lemma conditional_variance_L2_alt (x : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isl2: IsLp prts 2 x} :
    almostR2 prts eq
             (FiniteConditionalExpectation 
                prts sub
                (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x)))) 
             (rvminus (FiniteConditionalExpectation prts sub (rvsqr x))
                      (rvsqr (FiniteConditionalExpectation prts sub x))).
     Proof.
       generalize (isfe_L2_variance x sub rv); intros.
       apply conditional_variance_alt; try easy.
     Qed.       

  Lemma conditional_variance_bound (x : Ts -> R) (c : R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isfe : IsFiniteExpectation prts x}
        {isfe2 : IsFiniteExpectation prts (rvsqr x)}        
        {rv2 : RandomVariable 
                 dom borel_sa
                 (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x)))}
        {isfe0 : IsFiniteExpectation 
                   prts
                   (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x)))}
        {isfe4 : IsFiniteExpectation prts
            (rvsqr (FiniteConditionalExpectation prts sub x))}
        {isfe5 : IsFiniteExpectation prts
            (rvmult (FiniteConditionalExpectation prts sub x) x)}    :
    almostR2 prts Rle (rvsqr x) (const c²) ->
    almostR2 prts Rle (FiniteConditionalExpectation prts sub (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))))
          (const c²).
  Proof.
    intros.
    generalize (conditional_variance_alt x sub); intros.
    generalize (conditional_variance_bound1 x c sub H); intros.
    revert H1; apply almost_impl.
    revert H0; apply almost_impl.
    apply all_almost; intros ???.
    rewrite H0.
    apply H1.
 Qed.

  Lemma conditional_variance_bound_L2 (x : Ts -> R) (c : R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {isl2: IsLp prts 2 x} :
    almostR2 prts Rle (rvsqr x) (const c²) ->
    almostR2 prts Rle (FiniteConditionalExpectation prts sub (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))))
          (const c²).
  Proof.
    intros.
    generalize (conditional_variance_L2_alt x sub); intros.
    generalize (conditional_variance_bound1 x c sub H); intros.
    revert H1; apply almost_impl.
    revert H0; apply almost_impl.
    apply all_almost; intros ???.
    rewrite H0.
    apply H1.
 Qed.

  Lemma conditional_variance_bound_L2_fun (x c : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa x}
        {rv2 : RandomVariable dom2 borel_sa c}        
        {isfe2 : IsFiniteExpectation prts c}
        {isl2: IsLp prts 2 x} :
    almostR2 prts Rle (rvsqr x) (c) ->
    almostR2 prts Rle (FiniteConditionalExpectation prts sub (rvsqr (rvminus x (FiniteConditionalExpectation prts sub x))))
          (c).
  Proof.
    intros.
    generalize (conditional_variance_L2_alt x sub); intros.
    generalize (conditional_variance_bound1_fun x c sub H); intros.
    revert H1; apply almost_impl.
    revert H0; apply almost_impl.
    apply all_almost; intros ???.
    rewrite H0.
    apply H1.
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

  Ltac rewrite_condexp_pf_irrel H
  := match type of H with
     | @NonNegCondexp ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv1 ?nnf1 ?x = _ =>
         match goal with
           [|- context [@NonNegCondexp ?Ts ?dom ?prts ?dom2 ?sub ?g ?rv2 ?nnf2 ?x]] =>
             rewrite <- (fun pf => @NonNegCondexp_ext
                                 Ts dom prts dom2 sub f g rv1 rv2 nnf1 nnf2 pf x); [rewrite H | reflexivity]
         end
     | @ConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv1 ?x = _ =>
         match goal with
           [|- context [@ConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?g ?rv2 ?x]] =>
             rewrite <- (fun pf => @ConditionalExpectation_ext
                                 Ts dom prts dom2 sub f g rv1 rv2 pf x); [rewrite H | reflexivity]
         end
     | @FiniteConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv1 ?nnf1 ?x = _ =>
         match goal with
           [|- context [@FiniteConditionalExpectation ?Ts ?dom ?prts ?dom2 ?sub ?f ?rv2 ?nnf2 ?x]] =>
             rewrite <- (fun pf => @FiniteConditionalExpectation_ext
                                 Ts dom prts dom2 sub f f rv1 rv2 nnf1 nnf2 pf x); [rewrite H | reflexivity]
         end
     end.


Section MDP.

  Context {M : MDP}  (γ : R).
  Arguments t {_}.

  
  Definition Ts := {x : state M & act M x} .
  Definition Td := Rfct Ts.

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

  Definition N_sig_act := length (nodup EqDecsigT fin_elms ).

  Context {Ts : Type}            
          {dom : SigmaAlgebra Ts}
          {prts : ProbSpace dom}
          {F : nat -> SigmaAlgebra Ts}

          (next_state : (sigT M.(act)) -> Ts -> M.(state))
          {rv_ns0: forall sa, RandomVariable (F 0%nat) (discrete_sa (state M)) (next_state sa)}
          (next_state_rv : forall t sa,
              RandomVariable (F t) (discrete_sa (sigT M.(act))) sa ->
              RandomVariable (F (S t)) (discrete_sa (state M)) (fun ω => next_state (sa ω) ω))
          
          (cost : (sigT M.(act)) -> Ts -> R)
          {rv_cost : forall sa, RandomVariable dom borel_sa (cost sa)}
          {isfe_cost : forall (sa : sigT M.(act)),
              IsFiniteExpectation prts (cost sa)}
          (islp_cost: forall sa : {x : state M & act M x}, IsLp prts 2 (cost sa))
          (Q0 : Rfct (sigT M.(act)))
          (α : nat -> Ts -> Rfct (sigT M.(act)))
          (rvα : forall t sa,
              RandomVariable dom borel_sa (fun ω => α t ω sa))
          (alpha_bound : forall t ω sa, 0 <= α t ω sa <= 1)
          (rvα' : forall t sa,
              RandomVariable (F t) borel_sa (fun ω => α t ω sa))
          {rv_cost0 : forall sa, RandomVariable (F 0%nat) borel_sa (cost sa)}
          (isfilt : IsFiltration F) 
          (filt_sub : forall k, sa_sub (F k) dom) 
          (indep_cost: forall k sa,
              independent_sas prts (pullback_rv_sub dom borel_sa (cost sa) (rv_cost sa))
                              (filt_sub k))
          (β : R).

  Instance rv_ns: forall sa, RandomVariable dom (discrete_sa (state M)) (next_state sa).
  Proof.
    intros.
    specialize (rv_ns0 sa).
    now apply (RandomVariable_sa_sub (filt_sub 0%nat)) in rv_ns0.
  Qed.

  (* Definition SA := sigT M.(act). *)

  Definition qlearn_Qmin (Q : Rfct (sigT M.(act))) (s : M.(state)) : R :=
    Min_{act_list s} (fun a => Q (existT _ s a)).

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


  Instance IsFiniteExpectation_minus'
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
         {isfe1:IsFiniteExpectation prts rv_X1}
         {isfe2:IsFiniteExpectation prts rv_X2} :
    IsFiniteExpectation prts (fun ω => (rv_X1 ω) - (rv_X2 ω)).
  Proof.
    generalize (IsFiniteExpectation_minus prts rv_X1 rv_X2).
    apply IsFiniteExpectation_proper; try easy.
    intros ?; rv_unfold; lra.
  Qed.

  Instance IsFiniteExpectation_opp' rv_X 
         {isfe:IsFiniteExpectation prts rv_X} :
    IsFiniteExpectation prts (fun ω => - (rv_X ω)).
  Proof.
    generalize (IsFiniteExpectation_opp prts rv_X).
    apply IsFiniteExpectation_proper; try easy.
    intros ?; rv_unfold; lra.
  Qed.

  Existing Instance FiniteCondexp_rv'.    

  Context {finA : FiniteType (sigT M.(act))}.
  Definition Rmax_all : Rfct (sigT M.(act)) -> R := let (ls,_) := finA in fun (f:Rfct (sigT M.(act))) => Max_{ls}(fun s => (f s)).
  Definition Rmin_all : Rfct (sigT M.(act)) -> R := let (ls,_) := finA in fun (f:Rfct (sigT M.(act))) => Min_{ls}(fun s => (f s)).
  
  Instance isfe_qmin (Q : Rfct (sigT M.(act))) (sa : (sigT M.(act))) :
    IsFiniteExpectation prts (fun ω => qlearn_Qmin Q (next_state sa ω)).
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
        exists  (existT (act M) (next_state sa a) x).
        split; trivial.
    - intros ?.
      unfold const, qlearn_Qmin.
      unfold Rmax_all.
      match_destr.
      apply Rle_trans with (r2 := Max_{ act_list (next_state sa a)}(fun a0 : act M (next_state sa a) => Q (existT (act M) (next_state sa a) a0))).
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
          exists  (existT (act M) (next_state sa a) x).
          split; trivial.
  Qed.

  Definition qlearn_XF (Q : Rfct (sigT M.(act))) : Rfct (sigT M.(act)) :=
    fun sa => FiniteExpectation prts (cost sa) +
              β * (FiniteExpectation prts (fun ω => qlearn_Qmin Q (next_state sa ω))).


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

  Definition finite_Rsum {B:Type} {decB : EqDec B eq} {finB:FiniteType B} (f:B->R)
    := list_sum (map f (nodup decB fin_elms)).

  Instance rv_finite_Rsum {B:Type} {decB : EqDec B eq} {finB:FiniteType B} (f:Ts->B->R)
                          {dom2 : SigmaAlgebra Ts}
                          {rvf : forall b, RandomVariable dom2 borel_sa (fun ω => f ω b)}
    : RandomVariable dom2 borel_sa (fun ω => finite_Rsum (f ω)).
  Proof.
    unfold finite_Rsum.
    now apply list_sum_map_rv.
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

  Instance isfe_qmin1 (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q ω sa))
    (sa : (sigT M.(act))) :
    IsFiniteExpectation prts (fun ω : Ts => qlearn_Qmin (Q ω) (next_state sa ω)).
  Proof.
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
        exists  (existT (act M) (next_state sa a) x).
        split; trivial.
    - intros ?.
      unfold Rmax_all, qlearn_Qmin.
      apply Rle_trans with
          (r2 :=  Max_{ act_list (next_state sa a)}(fun a0 : act M (next_state sa a) => Q a (existT (act M) (next_state sa a) a0))).
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
          exists  (existT (act M) (next_state sa a) x).
          split; trivial.
  Qed.

  Instance isl2_qmin1 (Q : Ts -> Rfct (sigT M.(act)))
    (isrvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q ω sa))
    (isfeQ : forall sa, IsLp prts 2 (fun ω => Q ω sa))
    (sa : (sigT M.(act))) :
    IsLp prts 2 (fun ω : Ts => qlearn_Qmin (Q ω) (next_state sa ω)).
  Proof.
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
                 Min_{ act_list (next_state sa a)}
                     (fun a0 : act M (next_state sa a) => Q a (existT (act M) (next_state sa a) a0)) = Q a sa0).
      {
        generalize (Rmin_list_map_exist (fun a0 : act M (next_state sa a) => Q a (existT (act M) (next_state sa a) a0))  (act_list (next_state sa a))); intros.
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

  Instance rv0 
    (sa : (sigT M.(act))) :
    RandomVariable dom borel_sa 
                   (fun ω : Ts => Q0 sa).
  Proof.
    apply rvconst.
  Qed.

  Instance rv0'
    (sa : (sigT M.(act))) :
    RandomVariable (F 0%nat) borel_sa 
                   (fun ω : Ts => Q0 sa).
  Proof.
    apply rvconst.
  Qed.

  Instance rv_qmin0 
    (sa : (sigT M.(act))) :
    RandomVariable dom borel_sa 
                   (fun ω : Ts => qlearn_Qmin Q0 (next_state sa ω)).
  Proof.
    typeclasses eauto.
  Qed.

  Instance rv_qmin0'
    (sa : (sigT M.(act))) :
    RandomVariable (F 0%nat) borel_sa 
                   (fun ω : Ts => qlearn_Qmin Q0 (next_state sa ω)).
  Proof.
    typeclasses eauto.
  Qed.

  Instance isfe0
    (sa : (sigT M.(act))) :
    IsFiniteExpectation prts (fun ω : Ts => Q0 sa).
  Proof.
    apply IsFiniteExpectation_const.
  Qed.

  Instance isfe_qmin0
    (sa : (sigT M.(act))) :
    IsFiniteExpectation prts (fun ω : Ts => qlearn_Qmin Q0 (next_state sa ω)).
  Proof.
    typeclasses eauto.
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

  Global Instance HasPreimageSingleton_discrete {B} : HasPreimageSingleton (discrete_sa B).
  Proof.
    intros ?????.
    red in rv.
    apply (rv (DiscreteProbSpace.discrete_singleton c)).
  Qed.
    
  Instance rv_qlearn_XF (g : Ts -> Rfct (sigT M.(act)))
           (rvg : forall sa, RandomVariable dom borel_sa (fun ω : Ts => g ω sa)) :
    forall sa, RandomVariable dom borel_sa (fun ω : Ts => qlearn_XF (g ω) sa).
  Proof.
    intros.
    apply rvplus_rv; try typeclasses eauto.
    apply rvscale_rv.
    assert (rv2 : forall a, RandomVariable dom borel_sa (fun v : Ts => qlearn_Qmin (g a) (next_state sa v))).
    {
      intros.
      typeclasses eauto.
    } 
    eapply RandomVariable_proper; [reflexivity | reflexivity | ..].
    {
      intros ?.
      rewrite (FiniteExpectation_simple _ _).
      apply SimpleExpectation_compose_Finite_type.
    }
    apply list_sum_rv; intros; try typeclasses eauto.
  Qed.

  Instance rv_qmin_next (g : Ts -> Rfct (sigT M.(act))) t'
    (rvg : forall sa, RandomVariable dom borel_sa (fun ω : Ts => g ω sa))
    (isfe : forall sa, IsFiniteExpectation prts (fun ω : Ts => (g ω sa)))
    (sa : (sigT M.(act))) :
    RandomVariable dom borel_sa (fun ω => (g ω sa) + 
                     (α t' ω sa) * (qlearn_XF (g ω) sa - (g ω) sa +
                     ((cost sa ω) - FiniteExpectation (isfe := isfe_cost sa) prts (cost sa)) +
                     (qlearn_Qmin (g ω) (next_state sa ω) -
                      FiniteConditionalExpectation 
                        (rv := rv_qmin1 g _ rvg _) 
                        prts (filt_sub t')
                        (fun ω => qlearn_Qmin (g ω) (next_state sa ω)) ω))).
  Proof.
    typeclasses eauto.
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

  Instance isfe_qlearn_XF (g : Ts -> Rfct (sigT M.(act))) 
           (rvg : forall sa, RandomVariable dom borel_sa (fun ω : Ts => (g ω sa)))
           (isfe : forall sa, IsFiniteExpectation prts (fun ω : Ts => (g ω sa)))
           (sa : (sigT M.(act))) :
    IsFiniteExpectation prts (fun ω : Ts => qlearn_XF (g ω) sa).
  Proof.
    assert (rv2 : forall a, RandomVariable dom borel_sa (fun v : Ts => qlearn_Qmin (g a) (next_state sa v))).
    {
      intros.
      typeclasses eauto.
    } 
    apply IsFiniteExpectation_plus.
    - apply rvconst.
    - apply rvscale_rv.
      eapply RandomVariable_proper; [reflexivity | reflexivity | ..].
      {
        intros ?.
        rewrite (FiniteExpectation_simple _ _).
        apply SimpleExpectation_compose_Finite_type.
      }
      apply list_sum_rv; intros; try typeclasses eauto.
    - apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_scale.
      eapply IsFiniteExpectation_proper.
      {
        intros ?.
        rewrite (FiniteExpectation_simple _ _).
        apply SimpleExpectation_compose_Finite_type.
      }
      apply IsFiniteExpectation_list_sum; try typeclasses eauto.
      intros.
      eapply IsFiniteExpectation_proper.
      intros ?.
      apply Rmult_comm.
      apply IsFiniteExpectation_scale.
      apply IsFiniteExpectation_bounded with
          (rv_X1 := fun ω => Rmin_all (g ω)) (rv_X3 := fun ω => Rmax_all (g ω)); try typeclasses eauto.
      + intros ?.
        unfold Rmin_all, qlearn_Qmin.
        match_destr.
        apply Rge_le, Rmin_list_incl.
        * rewrite map_not_nil.
           apply act_list_not_nil.
        * intros ??.
           apply in_map_iff in H.
           destruct H as [? [? ?]].
           subst.
           apply in_map_iff.
           exists  (existT (act M) c x).
           split; trivial.
      + intros ?.
        unfold Rmax_all, qlearn_Qmin.
        apply Rle_trans with
            (r2 :=  Max_{ act_list c}(fun a0 : act M c => g a (existT (act M) c a0))).
        * apply Rge_le, Rmax_list_map_ge_Rmin.
        * match_destr.
          apply Rmax_list_incl.
          -- rewrite map_not_nil.
             apply act_list_not_nil.
          -- intros ??.
             apply in_map_iff in H.
             destruct H as [? [? ?]].
             subst.
             apply in_map_iff.
             exists  (existT (act M) c x).
             split; trivial.
  Qed.

  Instance isfe_qmin_next (g : Ts -> Rfct (sigT M.(act))) t'
           (rvg : forall sa, RandomVariable dom borel_sa (fun ω : Ts => (g ω sa)))
           (isfe : forall sa, IsFiniteExpectation prts (fun ω : Ts => (g ω sa)))
           (sa : (sigT M.(act))) :
    IsFiniteExpectation prts (fun ω => (g ω sa) + 
                     (α t' ω sa) * (qlearn_XF (g ω) sa - (g ω) sa +
                     ((cost sa ω) - FiniteExpectation (isfe := isfe_cost sa) prts (cost sa)) +
                     (qlearn_Qmin (g ω) (next_state sa ω) -
                      FiniteConditionalExpectation 
                        (rv := rv_qmin1 g _ rvg _) 
                        (isfe := isfe_qmin1 g rvg isfe sa)  
                        prts (filt_sub t')
                        (fun ω => qlearn_Qmin (g ω) (next_state sa ω)) ω))).
  Proof.
    apply IsFiniteExpectation_plus; trivial.
    - apply rvmult_rv; try typeclasses eauto.
    - apply isfe_small_mult; try easy.
      + apply rvplus_rv; try typeclasses eauto.
      + apply IsFiniteExpectation_plus; try typeclasses eauto.
        * apply IsFiniteExpectation_plus; try typeclasses eauto.
          apply IsFiniteExpectation_minus'; try typeclasses eauto.
          apply IsFiniteExpectation_const.
    Qed.

  Fixpoint qlearn_Qaux (t : nat) {struct t} : {f : (Ts -> Rfct (sigT M.(act))) |     (forall sa, RandomVariable dom borel_sa 
                                                                                                           (fun ω : Ts => (f ω sa)))
                                                                              &
                                                                              (forall sa, IsFiniteExpectation prts (fun ω : Ts => (f ω sa)))}
    :=

           match t with
           | 0%nat => exist2 _ _ (fun ω  => Q0) (rv0) (isfe0)
           | S t' => let '(exist2 g rvg isfe) := qlearn_Qaux t' in 
                    exist2
                      (fun x : Ts -> {x : state M & act M x} -> R =>
                         forall x0 : {x : state M & act M x},
                           RandomVariable dom borel_sa (fun ω : Ts => x ω x0))
                      (fun x : Ts -> {x : state M & act M x} -> R =>
                         forall x0 : {x : state M & act M x},
                           IsFiniteExpectation prts (fun ω : Ts => x ω x0))
                      (fun ω sa => (g ω sa) + 
                                  (α t' ω sa) * (qlearn_XF (g ω) sa - (g ω) sa +
                                                   ((cost sa ω) - FiniteExpectation (isfe := isfe_cost sa) prts (cost sa)) +
                                                   (qlearn_Qmin (g ω) (next_state sa ω) -
                                                      FiniteConditionalExpectation 
                                                        (rv := rv_qmin1 g _ rvg _) 
                                                        (isfe := isfe_qmin1 g rvg isfe sa)  
                                                        prts (filt_sub t')
                                                        (fun ω => qlearn_Qmin (g ω) (next_state sa ω)) ω)))
                      (fun sa : {x : state M & act M x} =>
                         (rv_qmin_next g t' rvg isfe) sa)
                      (fun sa : {x : state M & act M x} =>
                         (isfe_qmin_next g t' rvg isfe) sa)
           end.
  
  Fixpoint qlearn_Q_basic (t : nat) : (Ts -> Rfct (sigT M.(act)))    :=
           match t with
           | 0%nat => (fun ω  => Q0)
           | S t' => let g := qlearn_Q_basic t' in 
                     (fun ω sa => (g ω sa) + 
                                  (α t' ω sa) * ((cost sa ω) + β * (qlearn_Qmin (g ω) (next_state sa ω))
                                                                   - (g ω sa)))
           end.

  Lemma cost_F_rv :
    forall sa n,
      RandomVariable (F n) borel_sa (cost sa).
  Proof.
    intros.
    induction n; trivial.
    now apply (RandomVariable_sa_sub (isfilt n)).
  Qed.
    
  Instance qlearn_Q_basic_rv
    :
    forall t sa, RandomVariable (F t) borel_sa (fun ω => qlearn_Q_basic t ω sa).
  Proof.
    induction t; simpl; intros.
    - apply rvconst.
    - apply rvplus_rv.
      + now apply (RandomVariable_sa_sub (isfilt t)).
      + apply rvmult_rv.
        * now apply (RandomVariable_sa_sub (isfilt t)).
        * apply rvplus_rv.
          -- apply rvplus_rv; trivial.
             ++ apply cost_F_rv.
             ++ apply rvscale_rv.
                apply rv_qmin1.
                ** intros.
                   apply (RandomVariable_sa_sub (isfilt t)).      
                   now apply IHt.
                ** apply next_state_rv.
                   apply rvconst.
          -- cut (RandomVariable (F (S t)) borel_sa (rvopp (fun ω : Ts => qlearn_Q_basic t ω sa))).
             { apply RandomVariable_proper; try reflexivity.
               intros ?.
               unfold rvopp, rvscale; lra.
             }
             apply rvopp_rv.
             generalize (IHt sa).
             apply RandomVariable_proper_le; try reflexivity.
             apply isfilt.
  Qed.

  Instance qlearn_Q_basic_rv_dom :
    forall t sa, RandomVariable dom borel_sa (fun ω => qlearn_Q_basic t ω sa).
  Proof.
    induction t; simpl; intros; typeclasses eauto.
  Qed.

  Instance isfe_qlearn_Q_basic :
    forall t sa, IsFiniteExpectation prts (fun ω => qlearn_Q_basic t ω sa).
  Proof.
    intros.
    revert sa.
    induction t.
    - simpl.
      intros.
      apply IsFiniteExpectation_const.
    - intros.
      simpl.
      apply IsFiniteExpectation_plus; try typeclasses eauto.
      apply isfe_small_mult; try typeclasses eauto.
      intros; apply alpha_bound.
  Qed.      

  Instance isl2_qlearn_Q_basic
     (isl2_sa: forall sa, IsLp prts 2 (cost sa)):
    forall k sa, IsLp prts 2 (fun ω => qlearn_Q_basic k ω sa).
  Proof.
    intros.
    revert sa.
    induction k.
    - simpl.
      intros.
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
                   (cost sa ω + 
                    β * qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω) -
                    qlearn_Q_basic k ω sa)))); try typeclasses eauto.
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
                        (cost sa ω + 
                         β * qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω) -
                         qlearn_Q_basic k ω sa))).
        {
          apply H0; try typeclasses eauto.
          generalize (IsLp_opp prts (mknonnegreal _ H) (fun ω => qlearn_Q_basic k ω sa)); intros.
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


  Definition qlearn_Q (t : nat) : Ts -> Rfct (sigT M.(act))
    := let '(exist2 g _ _) := qlearn_Qaux t in g.

  Instance rv_qlearn_Q (t : nat) sa :
    RandomVariable dom borel_sa (fun ω : Ts => (qlearn_Q t ω sa)).
  Proof.
    unfold qlearn_Q; match_destr.
  Qed.

  Instance isfe_qlearn_Q (t : nat) sa :
    IsFiniteExpectation prts (fun ω : Ts => (qlearn_Q t ω sa)).
  Proof.
    unfold qlearn_Q; match_destr.
  Qed.

  Definition qlearn_w (Q : nat -> Ts -> Rfct (sigT M.(act)))
             (t : nat) (ω : Ts) (sa : (sigT M.(act)))     
             (rvQ : forall sa, RandomVariable dom borel_sa (fun ω => Q t ω sa))
             (isfeQ : forall sa, IsFiniteExpectation prts (fun ω => Q t ω sa)) : R :=
    ((cost sa ω) - FiniteExpectation (isfe := isfe_cost sa) prts (cost sa)) +
                     β *(qlearn_Qmin (Q t ω) (next_state sa ω) -
                         FiniteConditionalExpectation 
                           (rv := rv_qmin1 (Q t) _ rvQ _)
                           (isfe := isfe_qmin1 (Q t) rvQ isfeQ sa)
                           prts (filt_sub t)
                           (fun ω => qlearn_Qmin (Q t ω) (next_state sa ω)) ω).

(*
  Existing Instance finite_fun_vec_encoder.
 *)
  
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

  Lemma fold_left_Rmax_abs l : List.Forall (Rle 0) l -> fold_left Rmax l 0 = Rmax_list l.
  Proof.
    intros.
    rewrite fold_symmetric.
    - induction l; simpl; trivial.
      invcs H.
      rewrite IHl; trivial.
      destruct l; simpl; trivial.
      rewrite Rmax_left; trivial.
    - apply Rmax_assoc.
    - apply Rmax_comm.
  Qed.

  Instance finfun_sa : SigmaAlgebra (Rfct (sigT M.(act))) :=
    iso_sa (iso := Isomorphism_symm (finite_fun_vec_encoder finA EqDecsigT (B := R)))
      (Rvector_borel_sa _).


  Theorem Tsitsiklis_1_3_fintype  (X w  : nat -> Ts -> Rfct (sigT M.(act)))
    (XF : Rfct (sigT M.(act)) -> Rfct (sigT M.(act)))
    (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F) 
    {rvX0 : forall sa, RandomVariable (F 0%nat) borel_sa (fun ω => X 0%nat ω sa)}
    (adapt_w : forall sa, IsAdapted borel_sa (fun t ω => w t ω sa) (fun k => F (S k)))
    {rvXF : RandomVariable finfun_sa finfun_sa XF}
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
    (forall x, Rmax_norm _ (XF x) <= β * Rmax_norm _ x) ->
    (forall k ω sa, X (S k) ω sa = 
                    (X k ω sa) +  ((α k ω sa) * (((XF (X k ω) sa) - (X k ω sa) ) +  (w k ω sa)))) ->
    almost prts (fun ω => is_lim_seq (fun n => Rmax_norm _ (X n ω)) 0).
  Proof.
    intros.
  
    pose (Xvec := fun t ω => our_iso_f (X t ω)).
    pose (wvec := fun t ω => our_iso_f (w t ω)).
    pose (αvec := fun t ω => our_iso_f (α t ω)).    
    pose (XFvec := fun vecrf => our_iso_f (XF (our_iso_b vecrf))).
    pose (N := length (nodup EqDecsigT fin_elms)).
    generalize (Tsitsiklis_1_3 β Xvec wvec αvec XFvec isfilt filt_sub); intros.
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
    assert (rvXFvec: RandomVariable (Rvector_borel_sa (length (nodup EqDecsigT fin_elms)))
                           (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) XFvec).
    {
      unfold XFvec.
      apply (rv_cod_iso_sa_b (Isomorphism_symm (finite_fun_vec_encoder finA EqDecsigT (B := R)))).
      apply (RandomVariable_proper
               _ _ (reflexivity _)
               _ finfun_sa (reflexivity _) _ 
               (fun ω' => XF (our_iso_b ω'))).
      {
        intros ?.
        apply iso_b_f.
      }
      unfold our_iso_b.
      generalize (rv_dom_iso_sa_f (finite_fun_vec_encoder finA EqDecsigT (B := R)) rvXF).
      apply RandomVariable_proper; try reflexivity.
      symmetry.
      apply iso_sa_symm_id.
    }
    specialize (H6 _ _ H9 _ _ _ H12).
    cut_to H6; trivial.
    - revert H6.
      apply almost_impl, all_almost; intros ??.
      revert H6.
      apply is_lim_seq_ext.
      intros.
      unfold rvmaxabs.
      unfold Xvec, our_iso_f, iso_f; simpl.
      unfold finite_fun_to_vector; simpl.
      unfold Rvector_max_abs, vector_fold_left; simpl.
      rewrite map_map.
      unfold Rmax_norm.
      unfold fin_elms; destruct finA.
      generalize (nodup_equiv EqDecsigT fin_elms)
      ; intros eqq1.
      rewrite <- (map_equivlist (fun x0 : sigT (act M) => Rabs (X n x x0)) _ (reflexivity _) _ _ eqq1).
      apply fold_left_Rmax_abs.
      apply Forall_map.
      apply Forall_forall; intros.
      apply Rabs_pos.
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
    - intros x.
      generalize (H4 (our_iso_b x)); intros HH.
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
          now rewrite map_map.
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
          apply HH2.
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

    Lemma Condexp_minus' (f1 f2 : Ts -> R) 
          {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}
    :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub (fun ω => (f1 ω) - (f2 ω)))
             (Rbar_rvminus (ConditionalExpectation prts sub f1) (ConditionalExpectation prts sub f2)).
   Proof.
     generalize (Condexp_minus prts sub f1 f2).
     apply almost_impl, all_almost; intros ??.
     rewrite <- H.
     apply ConditionalExpectation_ext.
     intros ?.
     rv_unfold; lra.
   Qed.

   Corollary Condexp_const' c 
             {dom2 : SigmaAlgebra Ts}
             (sub : sa_sub dom2 dom) :
    rv_eq (ConditionalExpectation prts sub (fun _ => c)) (const (Finite c)).
  Proof.
    apply Condexp_id.
    apply rvconst'.
  Qed.

  Lemma Condexp_f_minus_condexp_f (f : Ts -> R)
                     {dom2 : SigmaAlgebra Ts}
                     (sub : sa_sub dom2 dom) 
                     {rv : RandomVariable dom borel_sa f}
                     {isfe : IsFiniteExpectation prts f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub (fun ω => (f ω) - (FiniteConditionalExpectation prts sub f ω)))
             (const 0).
  Proof.
    generalize (Condexp_minus' f (FiniteConditionalExpectation prts sub f) sub).
    apply almost_impl, all_almost; intros ??.
    rewrite H.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, const.
    rewrite Rbar_plus_comm.
    rewrite Condexp_id.
    - erewrite FiniteCondexp_eq.
      simpl; f_equal; lra.
    - apply FiniteCondexp_rv.
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
    eapply RandomVariable_proper; [reflexivity | reflexivity | ..].
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
    FiniteExpectation prts (fun ω : Ts => qlearn_Qmin x (next_state sa ω)) =
    list_sum (map (fun v : state M => qlearn_Qmin x v * ps_P (preimage_singleton (next_state sa) v)) 
                  (fin_elms (FiniteType := fin_finite_nodup _))).
  Proof.
    apply FiniteExpectation_compose_Finite_type.
    typeclasses eauto.
  Qed.

  Lemma Rmin_list_map_add {A} (f g : A -> R) (l : list A):
    Min_{ l}(fun a : A => (f a + g a)) >=
    Min_{ l}(fun a : A => (f a)) + (Min_{ l}(fun a : A => (g a))).
  Proof.
    destruct (is_nil_dec l).
    - subst; simpl. lra.
    - rewrite Rmin_list_ge_iff.
      intros x Hx. rewrite in_map_iff in Hx.
      destruct Hx as [a [Ha Hina]].
      rewrite <-Ha.
      apply Rplus_ge_compat; try (apply Rmin_spec; rewrite in_map_iff; exists a; split ; trivial).
      rewrite map_not_nil.
      congruence.
  Qed.

  Lemma Rmin_list_map_sub {A} (f g : A -> R) (l : list A):
    Min_{ l}(fun a : A => (f a - g a)) <=
    Min_{ l}(fun a : A => (f a)) - (Min_{ l}(fun a : A => (g a))).
  Proof.
    generalize (Rmin_list_map_add (fun a : A => (f a - g a))
                                  (fun a : A => (g a))); intros.
    assert (Min_{ l}(fun a : A => f a - g a + g a) =
            Min_{ l}(fun a : A => f a)).
    {
      apply Rmin_list_Proper.
      replace  (map (fun a : A => f a - g a + g a) l) with
          (map (fun a : A => f a) l).
      apply Permutation.Permutation_refl.
      apply map_ext.
      intros; lra.
    }
    specialize (H l).
    rewrite H0 in H.
    lra.
  Qed.

  Lemma Rmax_list_map_sub {A} (f g : A -> R) (l : list A):
    Max_{ l}(fun a : A => (f a - g a)) >=
    Max_{ l}(fun a : A => (f a)) - (Max_{ l}(fun a : A => (g a))).
  Proof.
    generalize (Rmax_list_map_add (fun a : A => (f a - g a))
                                  (fun a : A => (g a))); intros.
    assert (Max_{ l}(fun a : A => f a - g a + g a) =
            Max_{ l}(fun a : A => f a)).
    {
      apply Rmax_list_Proper.
      replace  (map (fun a : A => f a - g a + g a) l) with
          (map (fun a : A => f a) l).
      apply Permutation.Permutation_refl.
      apply map_ext.
      intros; lra.
    }
    specialize (H l).
    rewrite H0 in H.
    lra.
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
    replace  (FiniteExpectation prts (cost sa) +
              β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin x (next_state sa ω)) -
              (FiniteExpectation prts (cost sa) +
               β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin y (next_state sa ω))))
      with
        (β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin x (next_state sa ω)) -
         β * FiniteExpectation prts (fun ω : Ts => qlearn_Qmin y (next_state sa ω))) by lra.
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
                           ps_P (preimage_singleton (next_state sa) x0))))
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

                     * ps_P (preimage_singleton (next_state sa) x0))
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
          destruct (M a).
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
          now generalize (frf_vals_prob_1 _ (next_state sa)).
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

  Lemma Rfct_minus_zero (x : Rfct (sigT M.(act))) :
    Rfct_minus (sigT M.(act)) x (Rfct_zero (sigT M.(act))) = x.
  Proof.
    unfold Rfct_minus, Rfct_zero.
    intros.
    apply Rfct_eq_ext.
    intros.
    lra.
  Qed.

  Lemma finite_ex_choice
    {Idx:Type} {decA: EqDec Idx eq} {finI:FiniteType Idx} {A:Type}
    (P: Idx -> A -> Prop) :
    (forall (idx:Idx), exists a, P idx a) ->
    exists (l:list A),
      Forall2 P (nodup decA fin_elms) l.
  Proof.
    clear.
    destruct finI; simpl.
    clear fin_finite; intros HH.
    induction fin_elms; simpl.
    - exists nil; trivial.
    - destruct IHfin_elms as [l F2].
      match_destr.
      + eauto.
      + destruct (HH a); eauto.
  Qed.

  
  Lemma max_abs_sqr (a b : R) :
    Rmax (Rsqr a) (Rsqr b) = Rsqr (Rmax (Rabs a) (Rabs b)).
  Proof.
    unfold Rmax.
    match_destr; match_destr; try now rewrite Rsqr_abs.
    - apply Rsqr_le_abs_0 in r; lra.
    - apply Rsqr_le_abs_1 in r; lra.
  Qed.
    
   Lemma vec_max_abs_sqr {n} (v : vector R n) :
     Rvector_max_sqr v = Rsqr (Rvector_max_abs v).
   Proof.
     unfold Rvector_max_sqr, Rvector_max_abs, Rvector_sqr, Rvector_abs.
   Admitted.
   
   Lemma Rmax_list_abs_sqr (l : list R) :
     Rsqr (Rmax_list (map Rabs l)) = Rmax_list (map Rsqr l).
   Proof.
     induction l.
     - simpl; unfold Rsqr; lra.
     - simpl.
       rewrite <- IHl.
       destruct l.
       + simpl.
         now rewrite <- Rsqr_abs.
       + simpl.
         rewrite max_abs_sqr.
         rewrite Rsqr_abs.
         f_equal.
         rewrite Rabs_right; trivial.
         
     Admitted.

  Theorem qlearn 
          (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F)
          (fixpt0: forall sa, qlearn_XF (Rfct_zero (sigT M.(act))) sa = 0) :
    0 <= β < 1 ->
    (forall sa ω, is_lim_seq (sum_n (fun k => α k ω sa)) p_infty) ->

    (exists (C : R),
      forall sa,
        almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (α k ω sa)))) (Finite C))) ->
    let X := qlearn_Q_basic in 
    let w := fun t ω sa => qlearn_w (qlearn_Q_basic) t ω sa (qlearn_Q_basic_rv_dom t) (isfe_qlearn_Q_basic t) in
    let XF := qlearn_XF  in
    (forall sa, RandomVariable (F 0%nat) borel_sa (fun ω => X 0%nat ω sa)) ->
    almost prts (fun ω => is_lim_seq (fun n => Rmax_norm _ (X n ω)) 0).
   Proof.
     intros.
     assert (rvXF : RandomVariable finfun_sa finfun_sa qlearn_XF).
     {
       apply rv_finfun_sa.
       intros.
       apply rvplus_rv; try typeclasses eauto.
       apply rvscale_rv.
       assert (rv2 : forall ω, RandomVariable dom borel_sa (fun v : Ts => qlearn_Qmin ω (next_state sa v))).
       {
         intros.
         typeclasses eauto.
       } 
       eapply RandomVariable_proper; [reflexivity | reflexivity | ..].
       {
         intros ?.
         rewrite (FiniteExpectation_simple _ _).
         apply SimpleExpectation_compose_Finite_type.
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
       now apply qlearn_Q_basic_rv.
     }
     assert (forall n sa,  RandomVariable (F n) (discrete_sa (state M)) (next_state sa)).
     {
       intros.
       induction n; trivial.
       now apply (RandomVariable_sa_sub (isfilt n)).
     }
     assert (forall n sa, RandomVariable (F n) borel_sa (cost sa)).
     {
       intros.
       induction n; trivial.
       now apply (RandomVariable_sa_sub (isfilt n)).
     }
     assert (rvw: forall (k : nat) (sa : {x : state M & act M x}),
                RandomVariable dom borel_sa (fun ω : Ts => w k ω sa)).
     {
       unfold w.
       intros.
       typeclasses eauto.
     }
     apply Tsitsiklis_1_3_fintype with 
         (w := w) (XF := XF) (rvw := rvw); try easy.
     - intros.
       subst w.
       unfold qlearn_w.
       unfold IsAdapted; intros.
       apply rvplus_rv.
       + typeclasses eauto.
       + apply (RandomVariable_sa_sub (isfilt n)).
         apply rvscale_rv.
         apply rvminus_rv'; trivial.
         apply rv_qmin1; trivial.
         apply FiniteCondexp_rv.
     - intros.
       now apply Condexp_cond_exp.
     - intros.
       subst w.
       unfold qlearn_w.
       apply almostR2_prob_space_sa_sub_lift with (sub := filt_sub k).
       generalize (Condexp_minus' (fun ω => cost sa ω) (fun _ => FiniteExpectation 
                                                                   (isfe := isfe_cost sa)
                                                                   prts (cost sa)) 
                                  (filt_sub k) 
                                  (rv1 := rv_cost sa)
                                  (isfe1 := isfe_cost sa)
                                  (isfe2 := IsFiniteExpectation_const prts (FiniteExpectation 
                                                                   (isfe := isfe_cost sa)
                                                                   prts (cost sa)))); intros.
       generalize (@Condexp_plus _ _ prts _ (filt_sub k)
                     (fun ω : Ts =>
                               cost sa ω - FiniteExpectation prts (cost sa))
                     (fun ω => β *
                               (qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω) -
                                FiniteConditionalExpectation prts (filt_sub k)
                                                             (isfe :=
                                                                (isfe_qmin1 (qlearn_Q_basic k) (qlearn_Q_basic_rv_dom k) (isfe_qlearn_Q_basic k) sa))
                                                             (fun ω0 : Ts => qlearn_Qmin (qlearn_Q_basic k ω0) (next_state sa ω0)) ω)) _ _ ); intros.
       cut_to H8.
       generalize (is_conditional_expectation_independent_sa prts (filt_sub k) (cost sa)); intros.
       cut_to H9.

       generalize (Condexp_cond_exp prts (filt_sub k) (cost sa)); intros.
       generalize (is_conditional_expectation_unique prts (filt_sub k) (cost sa)); intros.
       specialize (H11 _ _ _ _ _ (isfe_cost sa) H9 H10).
       generalize (Condexp_scale prts (filt_sub k) β
                      (fun ω : Ts =>
                         (qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω) -
                          FiniteConditionalExpectation 
                            prts (filt_sub k)
                            (fun ω0 : Ts => qlearn_Qmin (qlearn_Q_basic k ω0) (next_state sa ω0)) ω))); intros.
       generalize (Condexp_f_minus_condexp_f  
                     (fun ω : Ts =>
                        qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω) ) (filt_sub k)); intros.
       + revert H13; apply almost_impl.
         revert H12; apply almost_impl.
         revert H11; apply almost_impl.
         revert H8; apply almost_impl.
         revert H7; apply almost_impl.
         apply all_almost; intros ??????.
         unfold rvplus in H8.
         rewrite_condexp H8.
         replace (Finite (const 0 x)) with (Rbar_plus (Finite (const 0 x)) (Finite (const 0 x))) by now rewrite Rbar_plus_0_r.
         unfold Rbar_rvplus.
         f_equal.
         * etransitivity; [| etransitivity]; [| apply H7 |]; apply refl_refl.
           -- apply ConditionalExpectation_ext.
              reflexivity.
           -- unfold const.
              unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
              generalize (Condexp_const' (FiniteExpectation prts (cost sa)) (filt_sub k) x); intros.
              rewrite H14.
              unfold const.
              unfold const in H11.
              repeat change (fun x => ?h x) with h.
              rewrite <- H11.
              simpl; f_equal.
              lra.
         * unfold rvscale in H12.
           rewrite H12.
           unfold Rbar_rvmult, const.
           rewrite H13.
           unfold const.
           now rewrite Rbar_mult_0_r.
       + apply indep_cost.
       + apply IsFiniteExpectation_minus'; try typeclasses eauto.
         apply IsFiniteExpectation_const.
       + apply IsFiniteExpectation_scale.
         apply IsFiniteExpectation_minus'; try typeclasses eauto.
     - unfold w, qlearn_w.
       assert (isl2_qmin: forall k sa,
                  IsLp prts 2 (fun ω => (qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω)))).
       {
         typeclasses eauto.
       }
       assert (forall k,
                  RandomVariable (F k) borel_sa
                    (fun ω => (Rmax_all (fun sa => Rsqr (qlearn_Q_basic k ω sa))))).
       {
         intros.
         apply rv_Rmax_all.
         intros.
         apply rvsqr_rv.
         apply H4.
       }
       (pose (Xmin := fun k sa ω => qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω))).
       assert (forall k sa,
                  IsFiniteExpectation 
                    prts
                    (rvsqr
                       (rvminus (Xmin k sa)
                                (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa))))).
       {
         intros.

         generalize (conditional_variance_L2_alt_isfe (Xmin k sa) (filt_sub k)); intros.
         revert H8.
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
                           (fun ω => Rmax_all (fun sa => Rsqr (qlearn_Q_basic k ω sa)))).
      {
        intros.
        assert (RandomVariable dom borel_sa (Xmin k sa)) by typeclasses eauto.
        assert (IsLp prts 2 (Xmin k sa)) by typeclasses eauto.
        assert (IsFiniteExpectation 
                  prts
                  (fun ω : Ts =>
                     Rmax_all (fun sa : {x : state M & act M x} => (qlearn_Q_basic k ω sa)²))).
        {
          apply isfe_Rmax_all; intros; typeclasses eauto.
        }
        generalize (conditional_variance_bound_L2_fun 
                      (Xmin k sa)
                      (fun ω => (Rmax_all (fun sa => Rsqr (qlearn_Q_basic k ω sa))))
                      (filt_sub k)); intros.
        cut_to H12.
        - revert H12.
          apply almost_impl, all_almost; intros ??.
          etransitivity; [| etransitivity]; [| apply H12 |]; apply refl_refl.
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
                     Min_{ act_list (next_state sa x)}
                         (fun a0 : act M (next_state sa x) => qlearn_Q_basic k x (existT (act M) (next_state sa x) a0)) = qlearn_Q_basic k x sa0).
         {
           generalize (Rmin_list_map_exist (fun a0 : act M (next_state sa x) => qlearn_Q_basic k x (existT (act M) (next_state sa x) a0))  (act_list (next_state sa x))); intros.
           cut_to H13.
           - destruct H13 as [? [? ?]].
             exists (existT _ _ x0).
             now rewrite <- H14.
           - apply act_list_not_nil.
         }
         destruct H13.
         rewrite H13.
         apply Rmax_spec.
         apply in_map_iff.
         exists x0.
         split; trivial.
      }
      generalize (fun k sa =>
                    nncondexp_sqr_sum_bound_nneg
                      (fun ω : Ts =>
                         cost sa ω - FiniteExpectation prts (cost sa))
                      (rvscale 
                         β 
                         (fun ω => (Xmin k sa ω) -
                                   (FiniteConditionalExpectation 
                                      prts (filt_sub k)
                                      (Xmin k sa) ω)))
                      (filt_sub k)
                 ); intros.                           
      assert (forall sa,
                 IsFiniteExpectation 
                   prts
                   (fun ω => Rsqr
                               ((cost sa ω) -
                                (FiniteExpectation prts (cost sa))))).
      {
        intros.
        assert (sa_sub dom dom) by reflexivity.
        generalize (conditional_variance_L2_alt_isfe (cost sa) H11).
        apply IsFiniteExpectation_proper.
        intros ?.
        rv_unfold.
        f_equal.
        ring_simplify.
        f_equal.
        admit.
      }
      assert (exists A,
                 0 < A /\
                 forall sa, 
                   FiniteExpectation prts 
                                     (fun ω => Rsqr
                                                 ((cost sa ω) -
                                                  (FiniteExpectation prts (cost sa))))
                   <=   A).
      {
        assert (forall sa,
                   exists A,
                     FiniteExpectation prts 
                                     (fun ω => Rsqr
                                                 ((cost sa ω) -
                                                  (FiniteExpectation prts (cost sa))))
                   <=   A).
        {
          intros.
          unfold FiniteExpectation.
          unfold proj1_sig.
          match_destr.
          exists x; lra.
        }
        apply (finite_ex_choice _ (decA:=EqDecsigT)) in H12.
        destruct H12 as [l F2l].
        exists (Rabs (Rmax_list l) + 1).
        split.
        - unfold Rabs; match_destr; lra.
        - intros sa.
          apply Rle_trans with (r2:=Rmax_list l); [| unfold Rabs; match_destr; lra].
          destruct (Forall2_In_l F2l (a:=sa)) as [?[??]].
          + apply nodup_In; apply fin_finite.
          + eapply Rle_trans; try apply H13.
            now apply Rmax_spec.
      }
      destruct H12 as [A [? ?]].
      exists (2 * A); exists 2.
      split; try lra.
      split; try lra.
      intros.
      specialize (H10 k sa).
      specialize (H9 k sa).
      specialize (H13 sa).
      revert H10; apply almost_impl.
      revert H9; apply almost_impl.
      apply all_almost; intros ???.
      erewrite Condexp_nneg_simpl.
      unfold rvplus, rvscale in H10.
      unfold Xmin in H10.
      eapply Rbar_le_trans; [| eapply Rbar_le_trans]; [| apply H10 |].
       + apply refl_refl.
         now apply NonNegCondexp_ext.
       + unfold rvplus, const, Rbar_rvmult, Rbar_rvplus.
         do 2 rewrite <- Condexp_nneg_simpl.
         do 2 erewrite FiniteCondexp_eq.
         simpl.
         rewrite Rmult_plus_distr_l.
         apply Rplus_le_compat.
         * apply Rmult_le_compat_l; try lra.
           unfold rvsqr.
           eapply Rle_trans; [| eapply Rle_trans]; [| apply H13 |]; try lra.
           right; admit.
         * unfold rvscale.
           apply Rmult_le_compat_l; try lra.
           clear H10.
           apply Rle_trans with
               (r2 := FiniteConditionalExpectation 
                        prts (filt_sub k)
                        (rvsqr
                           (rvminus (Xmin k sa)
                                    (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa)))) x ).
           -- admit.
           -- eapply Rle_trans.
              ++ apply H9.
              ++ unfold Rmax_norm, Rmax_all, X, rvmaxlist, Rmax_list_map.
                 match_destr.
                 apply Rmax_spec.
                 apply in_map_iff.
                 exists k.
                 split; trivial.
                 ** admit.
                 ** apply in_seq; lia.
     - intros.
       generalize (qlearn_XF_contraction H x (Rfct_zero (sigT M.(act)))); intros.
       rewrite Rfct_minus_zero in H7.
       replace (Rmax_norm (sigT (M.(act)))
                          (Rfct_minus {x : state M & act M x} (qlearn_XF x)
                                      (qlearn_XF (Rfct_zero {x : state M & act M x})))) with
           (Rmax_norm (sigT (M.(act))) (qlearn_XF x)) in H7; trivial.
       f_equal.
       apply Rfct_eq_ext.
       intros.
       unfold Rfct_minus.
       rewrite fixpt0.
       lra.
     - intros.
       subst w X XF.
       unfold qlearn_XF, qlearn_w.
       replace (FiniteConditionalExpectation 
                  prts (filt_sub k)
                  (fun ω0 : Ts => qlearn_Qmin (qlearn_Q_basic k ω0) (next_state sa ω0)) ω) with
           (FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (qlearn_Q_basic k ω) (next_state sa ω0))).
       + simpl.
         lra.
       + admit.
   Admitted.
       
End MDP.

    
