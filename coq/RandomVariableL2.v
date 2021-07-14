Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Export RandomVariableLpR.
Require Import quotient_space.
Require Import RbarExpectation.

Require Import Event.
Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section L2.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Lemma big2 : 1 <= 2.
  Proof.
    lra.
  Qed.
  Let nneg2 : nonnegreal := bignneg 2 big2.
  Canonical nneg2.


  Global Instance IsL2_Finite (rv_X:Ts->R)
        {rrv:RandomVariable dom borel_sa rv_X}
        {lp:IsLp prts 2 rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    apply IsLp_Finite in lp; trivial.
    apply big2.
  Qed.

  Global Instance is_L2_mult_finite x y 
        {xrv:RandomVariable dom borel_sa x}
        {yrv:RandomVariable dom borel_sa y} : 
    IsLp prts 2 x -> IsLp prts 2 y ->
    IsFiniteExpectation prts (rvmult x y).
  Proof.
    intros HH1 HH2.
    unfold IsLp, IsFiniteExpectation in *.
    match_case_in HH1
    ; [intros ? eqq1 | intros eqq1]
    ; rewrite eqq1 in HH1
    ; try contradiction.
    match_destr_in HH1; try contradiction.
    match_case_in HH2
    ; [intros ? eqq2 | intros eqq2]
    ; rewrite eqq2 in HH2
    ; try contradiction.
    match_destr_in HH2; try contradiction.
    apply Expectation_abs_then_finite.
    - generalize (rvprod_abs_bound x y)
      ; intros xyle.

      rewrite (Expectation_pos_posRV _).
      generalize (Finite_Expectation_posRV_le (rvabs (rvmult x y))
                                              (rvplus (rvsqr x) (rvsqr y))
                                              _
                                              _
                 )
      ; intros HH.
      rewrite <- HH; trivial.
      + etransitivity; try eapply xyle.
        intros a.
        unfold rvscale, rvabs, rvmult.
        assert (0 <= Rabs (x a * y a))
          by apply Rabs_pos.
        lra.
      + generalize (Expectation_posRV_sum (rvsqr x) (rvsqr y))
        ; intros HH3.
        erewrite Expectation_posRV_pf_irrel in HH3.
        rewrite HH3.

        rewrite rvpower_abs2_unfold in eqq1, eqq2.
        
        rewrite (Expectation_pos_posRV _) in eqq1.
        rewrite (Expectation_pos_posRV _) in eqq2.
        invcs eqq1.
        invcs eqq2.
        rewrite H0, H1.
        reflexivity.
  Qed.

  Definition L2RRVinner (x y:LpRRV prts 2) : R
    := FiniteExpectation prts (rvmult x y).

  Global Instance L2RRV_inner_proper : Proper (LpRRV_eq prts ==> LpRRV_eq prts ==> eq) L2RRVinner.
  Proof.
    unfold Proper, respectful, LpRRV_eq.

    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold L2RRVinner.
    assert (eqq:almost prts eq (rvmult x1 y1) (rvmult x2 y2)).
    - LpRRV_simpl.
      now apply almost_eq_mult_proper.
    - eapply FiniteExpectation_proper_almost; try eapply eqq
      ; try typeclasses eauto.
  Qed.    

  Lemma L2RRV_inner_comm (x y : LpRRV prts 2) :
    L2RRVinner x y = L2RRVinner y x.
  Proof.
    unfold L2RRVinner.
    apply FiniteExpectation_ext.
    apply rvmult_comm.
  Qed.
  
  Lemma L2RRV_inner_pos (x : LpRRV prts 2) : 0 <= L2RRVinner x x.
  Proof.
    unfold L2RRVinner.
    apply FiniteExpectation_pos.
    typeclasses eauto.
  Qed.

  Lemma L2RRV_inner_zero_inv (x:LpRRV prts 2) : L2RRVinner x x = 0 ->
                                         LpRRV_eq prts x (LpRRVconst prts 0).
  Proof.
    unfold L2RRVinner, LpRRV_eq; intros.
    eapply FiniteExpectation_zero_pos in H; try typeclasses eauto.
    destruct H as  [P [Pall eq_on]].
    exists P.
    split; trivial.
    intros a Pa.
    specialize (eq_on a Pa).
    unfold LpRRVconst, const, rvmult; simpl in *.
    now apply Rsqr_0_uniq in eq_on.
  Qed.
  
  Lemma L2RRV_inner_scal (x y : LpRRV prts 2) (l : R) :
    L2RRVinner (LpRRVscale prts l x) y = l * L2RRVinner x y.
  Proof.
    unfold L2RRVinner, LpRRVscale; simpl.
    rewrite (FiniteExpectation_ext _ _ (rvscale l (rvmult x y))).
    - destruct (Req_EM_T l 0).
      + subst.
        erewrite (FiniteExpectation_ext _ _ (const 0)).
        * rewrite FiniteExpectation_const; lra.
        * intro x0.
          unfold rvscale, rvmult, const; lra.
      + now rewrite (FiniteExpectation_scale _ l (rvmult x y)).
    - intro x0.
      unfold rvmult, rvscale.
      lra.
  Qed.

  Global Instance L2Expectation_l1_prod (rv_X1 rv_X2:Ts->R) 
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {l21:IsLp prts 2 rv_X1}
        {l22:IsLp prts 2 rv_X2}        
    :  IsFiniteExpectation prts (rvabs (rvmult rv_X1 rv_X2)).

  Proof.
    assert (PositiveRandomVariable (rvabs (rvmult rv_X1 rv_X2))) by apply prvabs.
    generalize (Expectation_pos_posRV (rvabs (rvmult rv_X1 rv_X2))); intros.
    generalize (rvprod_abs1_bound rv_X1 rv_X2); intros.
    assert (PositiveRandomVariable (rvplus (rvsqr rv_X1) (rvsqr rv_X2)))
      by (apply rvplus_prv; apply prvsqr).
    generalize (Finite_Expectation_posRV_le _ _ H H2 H1); intros.
    unfold IsLp, IsFiniteExpectation in *.
    rewrite (Expectation_pos_posRV _) in l21.
    rewrite (Expectation_pos_posRV _)  in l22.    
    match_case_in l21
    ; [intros ? eqq1 | intros eqq1..]
    ; rewrite eqq1 in l21
    ; try contradiction.
    match_case_in l22
    ; [intros ? eqq2 | intros eqq2..]
    ; rewrite eqq2 in l22
    ; try contradiction.
    assert (PositiveRandomVariable (rvsqr rv_X1)) by apply prvsqr.
    assert (PositiveRandomVariable (rvsqr rv_X2)) by apply prvsqr.
    generalize (Expectation_posRV_sum (rvsqr rv_X1) (rvsqr rv_X2)); intros.
    cut_to H3.
    - rewrite Expectation_pos_posRV with (prv := H).
      now rewrite <- H3.
    - erewrite Expectation_posRV_pf_irrel in H6.
      rewrite H6.
      rewrite (Expectation_posRV_ext _ _ (rvpower_abs2_unfold _)) in eqq1.
      rewrite (Expectation_posRV_ext _ _  (rvpower_abs2_unfold _)) in eqq2.
      erewrite Expectation_posRV_pf_irrel in eqq1.
      rewrite eqq1.
      erewrite Expectation_posRV_pf_irrel in eqq2.
      rewrite eqq2.
      simpl.
      now unfold is_finite.
  Qed.

  Lemma conv_l2_prob_le_div
        (eps : posreal) 
        (X : Ts -> R) 
        (rv : RandomVariable dom borel_sa X)
        (posrv: PositiveRandomVariable X) :
  Rbar_le (ps_P (event_ge dom X eps))
          (Rbar_div (Expectation_posRV (rvsqr X)) 
                    (Rsqr eps)).
    Proof.
      assert (event_equiv (event_ge dom X eps)
                          (event_ge dom (rvsqr X) (Rsqr eps))).
      - intro x.
        split; intros.
        + apply Rge_le in H.
          apply Rle_ge.
          apply Rsqr_incr_1; trivial.
          left; apply cond_pos.
        + apply Rge_le in H.
          apply Rle_ge.
          apply Rsqr_incr_0; trivial.
          left; apply cond_pos.
      - rewrite H.
        rewrite mkpos_Rsqr.
        rewrite Rbar_div_div_pos.
        apply Markov_ineq_div.
    Qed.

  Lemma conv_l2_prob_le1 
        (eps : posreal) 
        (Xn: Ts -> R)
        (rvxn : RandomVariable dom borel_sa Xn) :
    is_finite (Expectation_posRV (rvsqr (rvabs Xn))) ->
    ps_P (event_ge dom (rvabs Xn) eps) <=
    (Expectation_posRV (rvsqr (rvabs Xn))) / (Rsqr eps).
    Proof.
      assert (RandomVariable dom borel_sa (rvabs Xn)).
      - now apply rvabs_rv.
      - assert (PositiveRandomVariable (rvabs Xn)).
        now apply prvabs.
        intros.
        generalize (conv_l2_prob_le_div eps (rvabs Xn) H H0).
        rewrite <- H1.
        simpl.
        intros.
        erewrite ps_proper; try eapply H2.
        intros ?; simpl.
        reflexivity.
    Qed.

  Lemma conv_l2_prob_le 
        (eps : posreal) 
        (X Xn: Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : RandomVariable dom borel_sa Xn) :
    is_finite (Expectation_posRV (rvsqr (rvabs (rvminus X Xn)))) ->
    ps_P (event_ge dom (rvabs (rvminus X Xn)) eps) <=
    (Expectation_posRV (rvsqr (rvabs (rvminus X Xn)))) / (Rsqr eps).
    Proof.
      intros.
      apply conv_l2_prob_le1; trivial.
    Qed.

  Lemma conv_l1_prob_le 
        (eps : posreal) 
        (X: Ts -> R)
        {rvx : RandomVariable dom borel_sa X}:
    is_finite (Expectation_posRV (rvabs X)) ->
    ps_P (event_ge dom (rvabs X) eps) <=
    (Expectation_posRV (rvabs X)) / eps.
    Proof.
      assert (RandomVariable dom borel_sa (rvabs X)).
      - now apply rvabs_rv.
      - assert (PositiveRandomVariable (rvabs X)).
        now apply prvabs.
        intros.
        generalize (Markov_ineq_div (rvabs X) H H0 eps); intros.
        rewrite <- H1 in H2.
        intros.
        erewrite ps_proper; try eapply H2.
        intros ?; simpl.
        reflexivity.
    Qed.
        
  Lemma conv_l1_prob_le_minus
        (eps : posreal) 
        (X Xn: Ts -> R)
        {rvx : RandomVariable dom borel_sa X}
        {rvxn : RandomVariable dom borel_sa Xn} :
    is_finite (Expectation_posRV (rvabs (rvminus X Xn))) ->
    ps_P (event_ge dom (rvabs (rvminus X Xn)) eps) <=
    (Expectation_posRV (rvabs (rvminus X Xn))) / eps.
    Proof.
      apply conv_l1_prob_le.
    Qed.

  Lemma conv_l2_prob1 
        (eps : posreal) 
        (Xn: nat -> Ts -> R)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) :
    (forall n, is_finite (Expectation_posRV (rvsqr (rvabs (Xn n))))) ->
    is_lim_seq (fun n => Expectation_posRV (rvsqr (rvabs (Xn n)))) 0 ->
    is_lim_seq (fun n => ps_P (event_ge dom (rvabs (Xn n)) eps)) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                    (w := (fun n => (Expectation_posRV (rvsqr (rvabs (Xn n)))) / (Rsqr eps))).
    - unfold eventually.
      exists (0%nat).
      intros.
      split.
      + apply ps_pos.
      + apply conv_l2_prob_le1; trivial.
    - apply is_lim_seq_const.
    - apply is_lim_seq_div with (l1 := 0) (l2 := Rsqr eps); trivial.
      + apply is_lim_seq_const.
      + apply Rbar_finite_neq.
        apply Rgt_not_eq.
        apply Rsqr_pos.
      + unfold is_Rbar_div.
        simpl.
        unfold is_Rbar_mult, Rbar_mult'.
        f_equal.
        now rewrite Rmult_0_l.
  Qed.

  Lemma conv_l2_prob 
        (eps : posreal) 
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) :
    (forall n, is_finite (Expectation_posRV (rvsqr (rvabs (rvminus X (Xn n)))))) ->
    is_lim_seq (fun n => Expectation_posRV (rvsqr (rvabs (rvminus X (Xn n))))) 0 ->
    is_lim_seq (fun n => ps_P (event_ge dom (rvabs (rvminus X (Xn n))) eps)) 0.
  Proof.
    intros.
    apply conv_l2_prob1; trivial.
  Qed.

    Lemma conv_l1_prob
        (eps : posreal) 
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) :
    (forall n, is_finite (Expectation_posRV (rvabs (rvminus X (Xn n))))) ->
    is_lim_seq (fun n => Expectation_posRV (rvabs (rvminus X (Xn n)))) 0 ->
    is_lim_seq (fun n => ps_P (event_ge dom (rvabs (rvminus X (Xn n))) eps)) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                    (w := (fun n => (Expectation_posRV (rvabs (rvminus X (Xn n)))) / eps)).
    - unfold eventually.
      exists (0%nat).
      intros.
      split.
      + apply ps_pos.
      + apply conv_l1_prob_le; trivial.
    - apply is_lim_seq_const.
    - apply is_lim_seq_div with (l1 := 0) (l2 := eps); trivial.
      + apply is_lim_seq_const.
      + apply Rbar_finite_neq.
        apply Rgt_not_eq.
        apply cond_pos.
      + unfold is_Rbar_div.
        simpl.
        unfold is_Rbar_mult, Rbar_mult'.
        f_equal.
        now rewrite Rmult_0_l.
  Qed.



  Lemma L2RRV_inner_plus (x y z : LpRRV prts 2) :
    L2RRVinner (LpRRVplus prts x y) z = L2RRVinner x z + L2RRVinner y z.
  Proof.
    unfold L2RRVinner, LpRRVplus; simpl.
    erewrite (FiniteExpectation_ext _ _ (rvplus (rvmult x z) (rvmult y z))).
    - erewrite <- FiniteExpectation_plus.
      apply FiniteExpectation_pf_irrel.
    - intro x0.
      unfold rvmult, rvplus.
      lra.
  Qed.

  (* get abs version by saying (x : L2RRV) <-> (abs x : L2RRV) *)

  Lemma L2RRV_inner_plus_r (x y z : LpRRV prts 2) :
    L2RRVinner x (LpRRVplus prts y z) = L2RRVinner x y  + L2RRVinner x z.
  Proof.
    do 3 rewrite L2RRV_inner_comm with (x := x).
    now rewrite L2RRV_inner_plus.
  Qed.

  Lemma L2RRV_inner_scal_r (x y : LpRRV prts 2) (l : R) :
    L2RRVinner x (LpRRVscale prts l y) = l * L2RRVinner x y.
  Proof.
    do 2 rewrite L2RRV_inner_comm with (x := x).
    now rewrite L2RRV_inner_scal.
  Qed.

  Lemma L2RRV_Cauchy_Schwarz (x1 x2 : LpRRV prts 2) :
    0 < L2RRVinner x2 x2 ->
    Rsqr (L2RRVinner x1 x2) <= (L2RRVinner x1 x1)*(L2RRVinner x2 x2).
  Proof.
    generalize (L2RRV_inner_pos 
                  (LpRRVminus prts
                     (LpRRVscale prts (L2RRVinner x2 x2) x1)
                     (LpRRVscale prts (L2RRVinner x1 x2) x2))); intros.
    rewrite LpRRVminus_plus, LpRRVopp_scale in H.
    repeat (try rewrite L2RRV_inner_plus in H; try rewrite L2RRV_inner_plus_r in H; 
            try rewrite L2RRV_inner_scal in H; try rewrite L2RRV_inner_scal_r in H).
    ring_simplify in H.
    unfold pow in H.
    do 3 rewrite Rmult_assoc in H.
    rewrite <- Rmult_minus_distr_l in H.
    replace (0) with (L2RRVinner x2 x2 * 0) in H by lra.
    apply Rmult_le_reg_l with (r := L2RRVinner x2 x2) in H; trivial.
    rewrite L2RRV_inner_comm with (x := x2) (y := x1) in H.
    unfold Rsqr; lra.
  Qed.


  Ltac L2RRV_simpl
    := repeat match goal with
              | [H : LpRRV _ _ |- _ ] => destruct H as [???]
              end
       ; unfold LpRRVplus, LpRRVminus, LpRRVopp, LpRRVscale
       ; simpl.

   Lemma L2RRV_L2_L1 
         (x : LpRRV prts 2) :
    Rsqr (FiniteExpectation prts x) <= FiniteExpectation prts (rvsqr x).
   Proof.
     generalize (L2RRV_Cauchy_Schwarz x (LpRRVconst prts 1)); intros.
     assert (L2RRVinner (LpRRVconst prts 1) (LpRRVconst prts 1) = 1).
     unfold L2RRVinner.
     L2RRV_simpl.
     unfold rvmult.
     rewrite (FiniteExpectation_ext prts _ (const 1)).
     - apply FiniteExpectation_const.
     - intro x0.
       unfold const; lra.
     - rewrite H0 in H.
       rewrite Rmult_1_r in H.
       assert (L2RRVinner x (LpRRVconst prts 1) = FiniteExpectation prts x).
       + unfold L2RRVinner.
         rewrite (FiniteExpectation_ext _ _  x); trivial.
         intro x0.
         L2RRV_simpl.
         unfold rvmult, const.
         lra.
       + rewrite H1 in H.
         unfold L2RRVinner in H.
         rewrite (FiniteExpectation_ext _ _ _ (symmetry (rvsqr_eq _))) in H.
         apply H; lra.
  Qed.

     Lemma conv_l2_l1 
        (Xn: nat -> Ts -> R)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) 
        (isl: forall n, IsLp prts 2 (Xn n)):
    is_lim_seq (fun n => FiniteExpectation prts (rvsqr (rvabs (Xn n)))) 0 ->
    is_lim_seq (fun n => FiniteExpectation prts (rvabs (Xn n))) 0.
    Proof.
      intros.
      assert (forall n, 0 <= FiniteExpectation prts (rvsqr (rvabs (Xn n)))).
      - intros.
        apply FiniteExpectation_pos.
        unfold PositiveRandomVariable, rvabs, rvsqr; intros.
        apply Rle_0_sqr.
      - apply is_lim_seq_le_le_loc with 
            (u := fun _ => 0) 
            (w := (fun n => Rsqrt (mknonnegreal (FiniteExpectation prts (rvsqr (rvabs (Xn n)))) (H0 n)))).
        + exists (0%nat); intros.
          assert (0 <= FiniteExpectation prts (rvabs (Xn n))).
          * apply FiniteExpectation_pos.
            unfold rvabs, PositiveRandomVariable; intros.
            apply Rabs_pos.
          * split; trivial.
            generalize (L2RRV_L2_L1 (pack_LpRRV prts (rvabs (Xn n))));intros.
            generalize Rsqr_le_to_Rsqrt; intros.
            specialize (H4 (mknonnegreal _ (H0 n))
                           (mknonnegreal _ H2)).
            apply H4; simpl.
            apply H3.
        + apply is_lim_seq_const.
        + apply is_lim_seq_ext with 
          (u := fun n=> Rsqrt_abs (FiniteExpectation prts (rvsqr (rvabs (Xn n))))).
          * intros.
            unfold Rsqrt_abs; f_equal.
            apply nonneg_ext. (* CAUTION : This uses proof irrelevance. *)
            now rewrite Rabs_pos_eq.
          * replace (0) with (Rsqrt_abs 0) by apply Rsqrt_abs_0.
            apply is_lim_seq_continuous; [|trivial].
            apply continuity_pt_Rsqrt_abs_0.
    Qed.

    Lemma conv_l2_l1_minus 
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) 
        (isl: forall n, IsLp prts 2 (rvminus X (Xn n))) :
    is_lim_seq (fun n => FiniteExpectation prts (rvsqr (rvabs (rvminus X (Xn n))))) 0 ->
    is_lim_seq (fun n => FiniteExpectation prts (rvabs (rvminus X (Xn n)))) 0.
    Proof.
      now apply conv_l2_l1.
    Qed.


  Definition L2RRVq_inner : LpRRVq prts 2 -> LpRRVq prts 2 -> R
    := quot_lift2_to _ L2RRVinner.

  Lemma L2RRVq_innerE x y : L2RRVq_inner (Quot _ x) (Quot _ y) = (L2RRVinner x y).
  Proof.
    apply quot_lift2_toE.
  Qed.

  Hint Rewrite L2RRVq_innerE : quot.

  Lemma L2RRVq_inner_comm (x y : LpRRVq_ModuleSpace prts nneg2) :
    L2RRVq_inner x y = L2RRVq_inner y x.
  Proof.
    LpRRVq_simpl.
    apply L2RRV_inner_comm.
  Qed.
  
  Lemma L2RRVq_inner_pos (x : LpRRVq_ModuleSpace prts nneg2) : 0 <= L2RRVq_inner x x.
  Proof.
    LpRRVq_simpl.
    apply L2RRV_inner_pos.
  Qed.
  
  Lemma L2RRVq_inner_zero_inv (x:LpRRVq_ModuleSpace prts nneg2) : L2RRVq_inner x x = 0 ->
                                                       x = zero.
  Proof.
    unfold zero; simpl.
    LpRRVq_simpl; intros; LpRRVq_simpl.
    now apply L2RRV_inner_zero_inv.
  Qed.
  
  Lemma L2RRVq_inner_scal (x y : LpRRVq_ModuleSpace prts nneg2) (l : R) :
    L2RRVq_inner (scal l x) y = l * L2RRVq_inner x y.
  Proof.
    unfold scal; simpl.
    LpRRVq_simpl.
    apply L2RRV_inner_scal.
  Qed.

  Lemma L2RRVq_inner_plus (x y z : LpRRVq_ModuleSpace prts nneg2) :
    L2RRVq_inner (plus x y) z = L2RRVq_inner x z + L2RRVq_inner y z.
  Proof.
    unfold plus; simpl.
    LpRRVq_simpl.
    apply L2RRV_inner_plus.
  Qed.
  
  Definition L2RRVq_PreHilbert_mixin : PreHilbert.mixin_of (LpRRVq_ModuleSpace prts nneg2)
    := PreHilbert.Mixin (LpRRVq_ModuleSpace prts nneg2) L2RRVq_inner
                        L2RRVq_inner_comm  L2RRVq_inner_pos L2RRVq_inner_zero_inv
                        L2RRVq_inner_scal L2RRVq_inner_plus.

  Canonical L2RRVq_PreHilbert :=
    PreHilbert.Pack (LpRRVq prts 2) (PreHilbert.Class _ _ L2RRVq_PreHilbert_mixin) (LpRRVq prts 2).

  Context {p:R}.
  Context (pbig:1 <= p).

  Lemma L2RRVq_Cauchy_Schwarz (x1 x2 : LpRRVq prts 2) :
    0 < L2RRVq_inner x2 x2 ->
    Rsqr (L2RRVq_inner x1 x2) <= (L2RRVq_inner x1 x1)*(L2RRVq_inner x2 x2).
  Proof.
    LpRRVq_simpl.
    apply L2RRV_Cauchy_Schwarz.
  Qed.

  (*
  (* generalize to be over any normed space *)
   Definition Cauchy_crit (Un : nat -> LpRRV prts 2) : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat,
        (forall n m:nat,
          (n >= N)%nat -> (m >= N)%nat -> LpRRVnorm prts (LpRRVminus prts (Un n) (Un m)) < eps).
*)
   Lemma inv_pow_2_pos  (n : nat) :
        0 < / (2 ^ n) .
  Proof.
    apply Rinv_0_lt_compat.
    apply pow_lt.
    lra.
  Qed.

  Definition LpRRV_lim_ball_center_center 
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop) :
    ProperFilter F -> cauchy F ->
    forall (n:nat), 
      {b:LpRRV_UniformSpace prts pbig |
        F (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig) b (mkposreal _ (inv_pow_2_pos n)))}.
  Proof.
    intros Pf cF n.
    pose ( ϵ := / (2 ^ n)).
    assert (ϵpos : 0 < ϵ) by apply inv_pow_2_pos.
    destruct (constructive_indefinite_description _ (cF (mkposreal ϵ ϵpos)))
      as [x Fx].
    now exists x.
  Defined.

  Definition LpRRV_lim_ball_center 
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop) :
    ProperFilter F -> cauchy F ->
    forall (n:nat), {b:LpRRV prts p ->Prop | F b}.
  Proof.
    intros Pf cF n.
    pose ( ϵ := / (2 ^ n)).
    assert (ϵpos : 0 < ϵ) by apply inv_pow_2_pos.
    destruct (constructive_indefinite_description _ (cF (mkposreal ϵ ϵpos)))
      as [x Fx].
    simpl in *.
    now exists  (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig) x ϵ).
  Defined.

  Definition LpRRV_lim_ball_cumulative
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : {x:LpRRV prts p->Prop | F x}
    := fold_right (fun x y =>
                     exist _ _ (Hierarchy.filter_and
                       _ _ (proj2_sig x) (proj2_sig y)))
                  (exist _ _ Hierarchy.filter_true)
                  (map (LpRRV_lim_ball_center F PF cF) (seq 0 (S n))).

  Definition LpRRV_lim_picker
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : LpRRV prts p
    := (proj1_sig (
            constructive_indefinite_description
              _
              (filter_ex
                 _
                 (proj2_sig (LpRRV_lim_ball_cumulative F PF cF n))))).

  Definition LpRRV_lim_picker_ext0
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : LpRRV prts p
    := match n with
       | 0 => LpRRVzero prts
       | S n' => LpRRV_lim_picker F PF cF n
       end.

    Lemma lim_picker_cumulative_included
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N n:nat) :
      (N <= n)%nat ->
      forall x,
      proj1_sig (LpRRV_lim_ball_cumulative F PF cF n) x ->
       (proj1_sig (LpRRV_lim_ball_center F PF cF N)) x.
    Proof.
      unfold LpRRV_lim_ball_cumulative.
      intros.
      assert (inn:In N (seq 0 (S n))).
      {
        apply in_seq.
        lia.
      }
      revert inn H0.
      generalize (seq 0 (S n)).
      clear.
      induction l; simpl.
      - tauto.
      - intros [eqq | inn]; intros.
        + subst.
          tauto.
        + apply (IHl inn).
          tauto.
    Qed.
    
  Lemma lim_picker_included
             (F : (LpRRV_UniformSpace prts pbig  -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N n:nat) :
    (N <= n)%nat ->
    (proj1_sig (LpRRV_lim_ball_center F PF cF N)) 
      (LpRRV_lim_picker F PF cF n).
  Proof.
    intros.
    unfold LpRRV_lim_picker.
    unfold proj1_sig at 2.
    match_destr.
    eapply lim_picker_cumulative_included; eauto.
  Qed.

  Lemma lim_ball_center_ball_center_center  (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (n:nat) :
    forall (x:UniformSpace.sort (LpRRV_UniformSpace prts pbig)),
      (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig)
                      (proj1_sig (LpRRV_lim_ball_center_center F PF cF n))
                      (mkposreal _ (inv_pow_2_pos n))) x

      <-> proj1_sig (LpRRV_lim_ball_center F PF cF n) x.
  Proof.
    unfold LpRRV_lim_ball_center; simpl.
    unfold LpRRV_lim_ball_center_center; simpl.
    intros.
    destruct ( constructive_indefinite_description
            (fun x0 : LpRRV prts p => F (Hierarchy.ball x0 (/ 2 ^ n)))
            (cF {| pos := / 2 ^ n; cond_pos := inv_pow_2_pos n |})); simpl.
    tauto.
  Qed.
    
  Lemma lim_picker_center_included
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (n:nat) :
    (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig)
                    (proj1_sig (LpRRV_lim_ball_center_center F PF cF n))
                    (mkposreal _ (inv_pow_2_pos n)))
      (LpRRV_lim_picker F PF cF n).
  Proof.
    simpl.
    apply lim_ball_center_ball_center_center.
    now apply lim_picker_included.
  Qed.

  Lemma lim_picker_center_included2
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (N:nat) :
    forall (n:nat), 
      (n >= N)%nat ->
      (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig)
                    (proj1_sig (LpRRV_lim_ball_center_center F PF cF N))
                    (mkposreal _ (inv_pow_2_pos N)))
      (LpRRV_lim_picker F PF cF n).
  Proof.
    intros.
    simpl.
    apply lim_ball_center_ball_center_center.
    apply lim_picker_included.
    lia.
  Qed.

  Lemma LpRRVq_opp_opp (x : LpRRVq_AbelianGroup prts (bignneg _ pbig)) :
    opp x = LpRRVq_opp prts x.
  Proof.
    unfold opp; simpl.
    LpRRVq_simpl.
    reflexivity.
  Qed.

  Lemma L2RRVq_norm_norm (x : LpRRVq prts 2) :
    Hnorm x = LpRRVq_norm prts x.
  Proof.
    unfold Hnorm; simpl.
    LpRRVq_simpl.
    rewrite LpRRVq_normE.
    unfold LpRRVnorm.
    unfold L2RRVinner.
    rewrite power_sqrt.
    - f_equal.
      apply FiniteExpectation_ext.
      intros ?; simpl.
      now rewrite rvpower_abs2_unfold, rvsqr_eq.
    - apply FiniteExpectation_pos.
      typeclasses eauto.
  Qed.
  
  Lemma Hnorm_minus_opp {T:PreHilbert} (a b:T) :
    (Hnorm (minus a b) = Hnorm (minus b a)).
  Proof.
    rewrite <- (norm_opp (minus a b)).
    rewrite opp_minus.
    reflexivity.
  Qed.

  Let pnneg : nonnegreal := bignneg p pbig.
  Canonical pnneg.
    
  Lemma LpRRVq_minus_plus_opp'
        (x y : LpRRVq prts p) :
    LpRRVq_minus prts x y = LpRRVq_plus prts x (LpRRVq_opp prts y).
  Proof.
    unfold minus, plus, opp; simpl.
    LpRRVq_simpl.
    now rewrite LpRRVminus_plus.
  Qed.

  Lemma LpRRV_norm_opp (x : LpRRV prts p) : LpRRVnorm prts (LpRRVopp prts x) = LpRRVnorm prts x.
  Proof.
    unfold LpRRVnorm, LpRRVopp.
    f_equal.
    apply FiniteExpectation_ext.
    simpl.
    intro z.
    rv_unfold.
    f_equal.
    replace (-1 * (x z)) with (- x z) by lra.
    now rewrite Rabs_Ropp.
  Qed.

  Lemma lim_ball_center_dist (x y : LpRRV prts p)
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N:nat) :
    (proj1_sig (LpRRV_lim_ball_center F PF cF N)) x ->
    (proj1_sig (LpRRV_lim_ball_center F PF cF N)) y ->
    LpRRVnorm prts (LpRRVminus prts x y) < 2 / 2 ^ N.
  Proof.
    unfold LpRRV_lim_ball_center; simpl.
    unfold proj1_sig.
    match_case; intros.
    match_destr_in H.
    invcs H.
    unfold Hierarchy.ball in *; simpl in *.
    unfold ball in *; simpl in *.
    generalize (Rplus_lt_compat _ _ _ _ H0 H1)
    ; intros HH.
    field_simplify in HH.
    - eapply Rle_lt_trans; try eapply HH.
      generalize (LpRRV_norm_plus prts pbig (LpRRVminus prts (p:=bignneg _ pbig) x x1) (LpRRVminus prts x1 y)); intros HH2.
      repeat rewrite LpRRVminus_plus in HH2.
      repeat rewrite LpRRVminus_plus.
      assert (eqq:LpRRV_seq (LpRRVplus prts (LpRRVplus prts x (LpRRVopp prts x1))
                                   (LpRRVplus prts x1 (LpRRVopp prts y)))
                            ((LpRRVplus prts x (LpRRVopp prts y)))).
      {
        intros ?; simpl.
        rv_unfold; lra.
      }
      generalize (LpRRV_norm_opp (LpRRVplus prts x (LpRRVopp prts x1)))
      ; intros eqq3.
      subst pnneg.
      rewrite <- eqq.
      eapply Rle_trans; try eapply HH2.
      apply Rplus_le_compat_r.
      simpl in *.
      rewrite <- eqq3.
      right.
      apply LpRRV_norm_sproper.
      intros ?; simpl.
      rv_unfold; lra.
    - revert HH.
      apply pow_nzero.
      lra.
  Qed.
  
  Lemma lim_filter_cauchy 
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    forall N : nat,
      forall n m : nat,
        (n >= N)%nat ->
        (m >= N)%nat -> 
        LpRRVnorm prts (LpRRVminus 
                            prts  
                            (LpRRV_lim_picker F PF cF n)
                            (LpRRV_lim_picker F PF cF m)) < 2 / 2 ^ N.
  Proof.
    intros.
    apply (lim_ball_center_dist _ _ F PF cF); now apply lim_picker_included.
  Qed.    
    
  Lemma cauchy_filter_sum_bound 
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) (pbigger:1 < p):
    ex_series (fun n => 
                 LpRRVnorm prts 
                             (LpRRVminus prts
                                (LpRRV_lim_picker F PF cF (S n))
                                (LpRRV_lim_picker F PF cF n))).
  Proof.
    apply (@ex_series_le R_AbsRing R_CompleteNormedModule) with
        (b := fun n => 2 / 2 ^ n).
    intros; unfold norm; simpl.
    unfold abs; simpl.
    rewrite Rabs_pos_eq.
    left.
    apply (lim_filter_cauchy F PF cF n (S n) n); try lia.
    unfold LpRRVnorm.
    apply power_nonneg.
    unfold Rdiv.
    apply (@ex_series_scal_l R_AbsRing R_CompleteNormedModule).
    apply ex_series_ext with (a := fun n => (/ 2) ^ n).
    - intros.
      intros; rewrite Rinv_pow; lra.
    - apply ex_series_geom.
      rewrite Rabs_Rinv by lra.
      rewrite Rabs_pos_eq; try lra.
 Qed.
  
  Lemma series_is_lim_seq (f:nat -> R) (l:R) :
    is_lim_seq (sum_n f) l <-> is_series f l.
  Proof.
    easy.
   Qed.

  Lemma series_sum_le (f : nat -> R) (x: R) :
    is_series f x ->
    (forall n, 0 <= f n) ->
    forall n, sum_n f n <= x.
  Proof.
    intros.
    rewrite <- series_is_lim_seq in H.
    apply is_lim_seq_incr_compare; trivial.
    intros.
    rewrite sum_Sn.
    now apply Rplus_le_pos_l.
  Qed.    

  Lemma islp_Rbar_lim_telescope_abs_gen (f : nat -> LpRRV prts p) :
    ex_series (fun n => 
                 LpRRVnorm prts 
                           (LpRRVminus prts (f (S n)) (f n))) ->
    (forall (n:nat), RandomVariable dom borel_sa (f n)) ->
    IsLp_Rbar prts p
              (Rbar_rvlim
                 (fun n => LpRRVsum 
                             prts pbig
                             (fun n0 => LpRRVabs prts (LpRRVminus prts (f (S n0)) 
                                                                  (f n0))) n)).
  Proof.
    intros.
    apply ex_series_ext with (b := fun n : nat => LpRRVnorm prts (LpRRVabs prts (LpRRVminus prts (f (S n)) (f n))))
      in H.
    - unfold ex_series in H.
      destruct H.
      apply islp_Rbar_rvlim_bounded with (c := x); try lra.
      + intros.
        eapply Rle_trans.
        apply LpRRV_norm_sum.
        apply series_sum_le; trivial.
        intros.
        unfold LpRRVnorm.
        apply power_nonneg.
      + intros.
        typeclasses eauto.
      + intros.
        apply LpRRVsum_pos.
        typeclasses eauto.
      + intros n xx.
        unfold LpRRVsum, pack_LpRRV; simpl.
        unfold rvsum.
        rewrite sum_Sn.
        apply Rplus_le_compat1_l.
        unfold rvabs.
        apply Rabs_pos.
    - intros.
      now rewrite norm_abs.
  Qed.

  Lemma cauchy_filter_sum_abs
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar 
      prts p
      (Rbar_rvlim
         (fun n0 =>
            LpRRVsum prts pbig 
                     (fun n =>
                        (LpRRVabs prts
                                  (LpRRVminus prts
                                              (LpRRV_lim_picker F PF cF (S (S n)))
                                              (LpRRV_lim_picker F PF cF (S n))))) n0)).
  Proof.
    apply (islp_Rbar_lim_telescope_abs prts pbig
                                       (fun n => LpRRV_lim_picker F PF cF (S n)))
    ; [ | typeclasses eauto ]; intros.
    generalize (lim_filter_cauchy F PF cF (S n) (S (S n)) (S n)); intros.
    simpl.
    cut_to H; try lia.
    simpl in H.
    unfold Rdiv in H.
    rewrite Rinv_mult_distr in H; try lra; [|apply pow_nzero; lra].
    rewrite <- Rmult_assoc in H.
    rewrite Rinv_r in H; try lra.
    rewrite Rmult_1_l in H.
    apply H.
  Qed.

  Lemma cauchy_filter_sum_abs_ext0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar 
      prts p
      (Rbar_rvlim
         (fun n0 =>
            LpRRVsum prts pbig 
                     (fun n =>
                        (LpRRVabs prts
                                  (LpRRVminus prts
                                              (LpRRV_lim_picker_ext0 F PF cF (S n))
                                              (LpRRV_lim_picker_ext0 F PF cF n)))) n0)).
  Proof.
    apply  islp_Rbar_lim_telescope_abs_gen
    ; [ | typeclasses eauto ]; intros.

    apply (@ex_series_le R_AbsRing R_CompleteNormedModule) with
        (b := fun n => match n with 
                       | 0 => LpRRVnorm prts (LpRRV_lim_picker_ext0 F PF cF 1)
                       | S n' => 2 / (pow 2 n')
                       end).

    - intros; unfold norm; simpl.
      unfold abs; simpl.
      rewrite Rabs_pos_eq.
      match_destr.
      + simpl.
        unfold LpRRVminus, LpRRVzero.
        unfold pack_LpRRV, LpRRVconst.
        unfold rvminus, rvplus, rvopp, rvscale, const; simpl.
        right.
        apply LpRRV_norm_sproper.
        intro z.
        simpl.
        ring.
      + left.
        simpl.
        apply (lim_filter_cauchy F PF cF n (S (S n)) (S n)); try lia.
      + unfold LpRRVnorm.
        apply power_nonneg.
    - rewrite ex_series_incr_1.
      unfold Rdiv.
      apply (@ex_series_scal_l R_AbsRing R_CompleteNormedModule).
      apply ex_series_ext with (a := fun n => (/ 2)^n).
      intros; now rewrite Rinv_pow.
      apply ex_series_geom.
      rewrite Rabs_pos_eq; lra.
 Qed.

  Lemma cauchy_filter_sum
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p 
         (Rbar_rvlim
            (rvsum
               (fun n =>
                  (LpRRVminus prts
                              (LpRRV_lim_picker F PF cF (S (S n)))
                              (LpRRV_lim_picker F PF cF (S n)))))).
  Proof.
    generalize (cauchy_filter_sum_abs F PF cF).
    unfold IsLp_Rbar; intros.
    unfold LpRRVnorm in H.
    eapply (is_finite_Rbar_Expectation_posRV_le _ _ _ H).
    Unshelve.
    intro x.
    unfold Rbar_rvlim.
    apply Rbar_power_le with (p := p); [simpl; lra | apply Rbar_abs_nneg | ].
    simpl.
    apply Rbar_Rabs_lim_sum_le.
  Qed.

  Lemma cauchy_filter_sum_ext0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
         (Rbar_rvlim
            (rvsum
               (fun n =>
                  (LpRRVminus prts
                              (LpRRV_lim_picker_ext0 F PF cF (S n))
                              (LpRRV_lim_picker_ext0 F PF cF n))))).
  Proof.
    generalize (cauchy_filter_sum_abs_ext0 F PF cF).
    unfold IsLp_Rbar; intros.
    unfold LpRRVnorm in H.
    eapply (is_finite_Rbar_Expectation_posRV_le _ _ _ H).
    Unshelve.
    intro x.
    unfold Rbar_rvlim.
    apply Rbar_power_le with (p := p); [simpl; lra | apply Rbar_abs_nneg | ].
    simpl.
    apply Rbar_Rabs_lim_sum_le.
  Qed.

  Lemma LpRRVsum_telescope0
        (f: nat -> LpRRV prts p) : 
    forall n0,
      LpRRV_seq (LpRRVsum prts pbig
                (fun n => (LpRRVminus prts (f (S n)) (f n))) 
                n0)
      (LpRRVminus prts (f (S n0)) (f 0%nat)).
   Proof.
     intros; induction n0.
     - intros x; simpl.
       unfold rvsum.
       now rewrite sum_O.
     - simpl in *.
       intros x; simpl.
       specialize (IHn0 x).
       simpl in *.
       unfold rvsum in *.
       rewrite sum_Sn.
       rewrite IHn0.
       rv_unfold.
       unfold plus; simpl.
       lra.
   Qed.

   Lemma LpRRVsum_telescope
        (f: nat -> LpRRV prts p) : 
     forall n0,
      LpRRV_seq (LpRRVplus prts (f 0%nat)
                 (LpRRVsum prts pbig
                           (fun n => (LpRRVminus prts (f (S n)) (f n))) 
                           n0))
                 (f (S n0)).
     Proof.
       intros.
       rewrite LpRRVsum_telescope0.
       rewrite LpRRVminus_plus.
       intros ?; simpl.
       rv_unfold; lra.
     Qed.

  Lemma cauchy_filter_sum_telescope
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    forall n0, 
      LpRRV_seq (LpRRVplus 
                   prts
                   (LpRRV_lim_picker F PF cF (S 0%nat))
                   (LpRRVsum prts pbig 
                             (fun n =>
                                (LpRRVminus prts
                                            (LpRRV_lim_picker F PF cF (S (S n)))
                                            (LpRRV_lim_picker F PF cF (S n)))) n0))
                (LpRRV_lim_picker F PF cF (S (S n0))).
  Proof.
    intros.
    apply (LpRRVsum_telescope 
             (fun n =>
                LpRRV_lim_picker F PF cF (S n))).
  Qed.

  Lemma cauchy_filter_Rbar_lim
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
         (Rbar_rvlim
            (fun n => LpRRVminus prts
                        (LpRRV_lim_picker F PF cF (S (S n)))
                        (LpRRV_lim_picker F PF cF (S 0%nat))
                        
         )).
  Proof.
   apply (IsLp_Rbar_proper prts p) with
       (x :=  
             (Rbar_rvlim
               (fun n0 =>
                  LpRRVsum prts pbig 
                           (fun n =>
                              (LpRRVminus prts
                                          (LpRRV_lim_picker F PF cF (S (S n)))
                                          (LpRRV_lim_picker F PF cF (S n))))
                           n0))); trivial.
   intro z.
   unfold Rbar_rvlim.
   apply Lim_seq_ext.
   intros.
   apply (LpRRVsum_telescope0 (fun n => (LpRRV_lim_picker F PF cF (S n)))).
   apply cauchy_filter_sum.
  Qed.

   Lemma cauchy_filter_Rbar_lim_ext0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
         (Rbar_rvlim
            (fun n => LpRRVminus prts
                        (LpRRV_lim_picker_ext0 F PF cF (S n))
                        (LpRRV_lim_picker_ext0 F PF cF 0%nat))
                        
         ).
  Proof.
   apply (IsLp_Rbar_proper prts p) with
       (x :=  
             (Rbar_rvlim
               (fun n0 =>
                  LpRRVsum prts pbig 
                           (fun n =>
                              (LpRRVminus prts
                                          (LpRRV_lim_picker_ext0 F PF cF (S n))
                                          (LpRRV_lim_picker_ext0 F PF cF n)))
                           n0))); trivial.
   intro z.
   unfold Rbar_rvlim.
   apply Lim_seq_ext.
   intros.
   apply (LpRRVsum_telescope0 (fun n => (LpRRV_lim_picker_ext0 F PF cF n))).
   apply  cauchy_filter_sum_ext0.
  Qed.

  Lemma IsLp_IsLp_Rbar (f : LpRRV prts p) :
    IsLp_Rbar prts p (LpRRV_rv_X prts f).
  Proof.
    unfold IsLp_Rbar.
    unfold IsLp, IsLp_Rbar; intros.
    generalize (LpRRV_LpS_FiniteLp prts f); intros.
    unfold IsFiniteExpectation in H.
    generalize (rvpower_prv (rvabs f) (const p)); intros.
    rewrite Expectation_pos_posRV with (prv := H0) in H.
    match_case_in H; intros.
    - rewrite Expectation_Rbar_Expectation in H1.
      unfold rvpower, rvabs, const in H1.
      unfold Rbar_power, Rbar_abs.
      erewrite Rbar_Expectation_posRV_pf_irrel.
      erewrite Rbar_Expectation_posRV_pf_irrel in H1.      
      now rewrite H1.
    - now rewrite H1 in H.
    - generalize (Expectation_posRV_pos (rvpower (rvabs f) (const p))); intros.
      rewrite H1 in H2.
      now simpl in H2.
   Qed.

  Lemma IsLp_Rbar_IsLp (f : Ts -> R) :
    IsLp_Rbar prts p f ->
    IsLp prts p f.
  Proof.
    unfold IsLp, IsLp_Rbar; intros.
    unfold IsFiniteExpectation.
    generalize (rvpower_prv (rvabs f) (const p)); intros.
    rewrite Expectation_pos_posRV with (prv := H0).
    rewrite Expectation_Rbar_Expectation.
    unfold Rbar_power, Rbar_abs in H.
    unfold rvpower, rvabs, const.
    erewrite Rbar_Expectation_posRV_pf_irrel.
    erewrite Rbar_Expectation_posRV_pf_irrel in H.
    now rewrite <- H.
  Qed.

  Lemma cauchy_filter_Rbar_rvlim1
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
              (Rbar_rvlim (fun n => (LpRRV_lim_picker F PF cF (S n)))).
   Proof.
     generalize (cauchy_filter_Rbar_lim_ext0 F PF cF); intros.
     unfold LpRRV_lim_picker_ext0 in H.
     eapply IsLp_Rbar_proper; trivial.
     shelve.
     apply H.
     Unshelve.
     intro x.
     unfold Rbar_rvlim.
     apply Lim_seq_ext.
     intros.
     unfold LpRRVzero, LpRRVconst, const.
     unfold pack_LpRRV; simpl.
     unfold rvminus, rvplus, rvopp, rvscale.
     ring.
   Qed.

  Program Definition pinf_Indicator 
          (f : Ts -> Rbar) :=
    EventIndicator (P := (fun x => (f x) = p_infty)) _.
  Next Obligation.
    apply ClassicalDescription.excluded_middle_informative.
  Qed.

  Instance Rbar_positive_indicator_prod (f : Ts -> Rbar) (c : posreal) :
    Rbar_PositiveRandomVariable (rvscale c (pinf_Indicator f)).
  Proof.
    unfold pinf_Indicator.
    apply rvscale_prv.
    typeclasses eauto.
  Qed.

  Lemma finite_Rbar_Expectation_posRV_le_inf
        (f : Ts -> Rbar)
        (fpos : Rbar_PositiveRandomVariable f) 
        (c : posreal)   :
    is_finite (Rbar_Expectation_posRV f) ->
    Rbar_le (Expectation_posRV (rvscale c (pinf_Indicator f)))
            (Rbar_Expectation_posRV f).
  Proof.
    generalize (Rbar_Expectation_posRV_le (rvscale c (pinf_Indicator f)) f); intros.
    apply H.
    intro x.
    unfold rvscale, pinf_Indicator.
    unfold EventIndicator.
    match_destr.
    - rewrite Rmult_1_r.
      rewrite e.
      now simpl.
    - rewrite Rmult_0_r.
      apply fpos.
  Qed.
  
  Lemma finite_Rbar_Expectation_posRV_le_inf2
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) 
        (fpos : Rbar_PositiveRandomVariable f) :
    is_finite (Rbar_Expectation_posRV f) ->
    forall (c:posreal), Rbar_le (c * (ps_P (exist _ _ (sa_pinf_Rbar f rv))))
            (Rbar_Expectation_posRV f).
  Proof.
    intros.
    generalize (finite_Rbar_Expectation_posRV_le_inf f fpos c H); intros.
    rewrite Expectation_posRV_scale in H0.
    unfold pinf_Indicator in H0.
    assert (SimpleRandomVariable (EventIndicator (fun x : Ts => pinf_Indicator_obligation_1 f x))) by typeclasses eauto.
    assert (RandomVariable dom borel_sa (EventIndicator (fun x : Ts => pinf_Indicator_obligation_1 f x))).
    apply EventIndicator_pre_rv.
    now apply sa_pinf_Rbar.
    generalize (srv_Expectation_posRV (EventIndicator (fun x : Ts => pinf_Indicator_obligation_1 f x))); intros.
    rewrite H2 in H0.
    generalize (SimpleExpectation_pre_EventIndicator 
                  (P := (fun x => f x = p_infty)) (sa_pinf_Rbar f rv)
                  (fun x : Ts => pinf_Indicator_obligation_1 f x)); intros.
    replace (@SimpleExpectation Ts dom prts
                  (@EventIndicator Ts (fun x : Ts => @eq Rbar (f x) p_infty)
                                   (fun x : Ts => pinf_Indicator_obligation_1 f x)) H1 X)
      with
        (ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv))) in H0.
    apply H0.
    rewrite SimpleExpectation_pf_irrel with (srv2 := X) in H3.
    symmetry.
    apply H3.
   Qed.

   Lemma finite_Rbar_Expectation_posRV_never_inf
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) 
        (fpos : Rbar_PositiveRandomVariable f) :
    is_finite (Rbar_Expectation_posRV f) ->
    ps_P (exist sa_sigma _ (sa_pinf_Rbar f rv)) = 0.
     Proof.
       intros.
       generalize (finite_Rbar_Expectation_posRV_le_inf2 f rv fpos H); intros.
       rewrite <- H in H0.
       simpl in H0.
       destruct (Rlt_dec 
                   0
                   (ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv)))).
       - assert (0 <
                 ((real (Rbar_Expectation_posRV f))+1)
                   /
                   (ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv)))).
         + unfold Rdiv.
           apply Rmult_lt_0_compat.
           generalize (Rbar_Expectation_posRV_pos f); intros.
           rewrite <- H in H1; simpl in H1.
           lra.
           now apply Rinv_0_lt_compat.
         + specialize (H0 (mkposreal _ H1)).
           simpl in H0.
           unfold Rdiv in H0.
           rewrite Rmult_assoc in H0.
           rewrite Rinv_l in H0.
           lra.
           now apply Rgt_not_eq.
       - generalize (ps_pos (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv))); intros.
         assert (0 >= ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv))) by lra.
         intuition.
   Qed.

  Lemma finite_Rbar_Expectation_posRV_almost_finite
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) 
        (fpos : Rbar_PositiveRandomVariable f) :
    is_finite (Rbar_Expectation_posRV f) ->
    ps_P (exist sa_sigma _ (sa_finite_Rbar f rv)) = 1.
  Proof.
    intros.
    generalize (finite_Rbar_Expectation_posRV_never_inf f rv fpos H); intros.
    assert (event_equiv
              (exist sa_sigma (fun x : Ts => is_finite (f x)) (sa_finite_Rbar f rv))
              (event_complement
                 (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv)))).
    - intro x.
      simpl.
      unfold pre_event_complement.
      generalize (fpos x); intros.
      destruct (f x); unfold is_finite.
      + simpl in H1.
        split; intros.
        * discriminate.
        * reflexivity.
      + simpl.
        split; intros.
        * discriminate.
        * tauto.
      + now simpl in H1.
    - rewrite H1.
      rewrite ps_complement.
      rewrite H0.
      lra.
   Qed.

  Class Rbar_IsFiniteExpectation (rv_X:Ts->Rbar) 
    := Rbar_is_finite_expectation :
         match Rbar_Expectation rv_X with
         | Some (Finite _) => True
         | _ => False
         end.

  Lemma Rbar_rvabs_plus_posfun_negfun
        (f : Ts -> Rbar ) :
    rv_eq (Rbar_rvabs f)
          (Rbar_rvplus (Rbar_pos_fun_part f) (Rbar_neg_fun_part f)).
  Proof.
    intro x.
    unfold Rbar_rvabs, Rbar_rvplus, Rbar_pos_fun_part, Rbar_neg_fun_part.
    destruct (f x).
    - simpl.
      unfold Rbar_max, Rabs, Rbar_plus, Rbar_plus'.
      match_destr; simpl.
      + destruct (Rbar_le_dec r 0); destruct (Rbar_le_dec (-r) 0); unfold Rbar_le in *
        ; try lra.
        now rewrite Rplus_0_l.
      + destruct (Rbar_le_dec r 0); destruct (Rbar_le_dec (-r) 0); unfold Rbar_le in *
        ; try lra.
        * assert (r = 0) by lra; subst.
          now rewrite Rplus_0_r.
        * now rewrite Rplus_0_r.
    - simpl.
      unfold Rbar_max, Rabs, Rbar_plus, Rbar_plus'.
      destruct (Rbar_le_dec p_infty 0); destruct (Rbar_le_dec m_infty 0); unfold Rbar_le in *; tauto.
    - simpl.
      unfold Rbar_max, Rabs, Rbar_plus, Rbar_plus'.
      destruct (Rbar_le_dec p_infty 0); destruct (Rbar_le_dec m_infty 0); unfold Rbar_le in *; tauto.
  Qed.

  Lemma finiteExp_Rbar_rvabs 
        (f : Ts -> Rbar) 
        {rv : RandomVariable dom Rbar_borel_sa f}:
    Rbar_IsFiniteExpectation f <->
    is_finite (Rbar_Expectation_posRV (Rbar_rvabs f)).
  Proof.
    unfold Rbar_IsFiniteExpectation, Rbar_Expectation.
    generalize (Rbar_rvabs_plus_posfun_negfun f); intros.
    rewrite (Rbar_Expectation_posRV_ext _ _ H).
    unfold Rbar_minus'.
    unfold Rbar_plus', Rbar_opp.
    rewrite Rbar_Expectation_posRV_plus.
    generalize (Rbar_Expectation_posRV_pos (Rbar_pos_fun_part f)); intros.
    generalize (Rbar_Expectation_posRV_pos (Rbar_neg_fun_part f)); intros.  
    destruct (Rbar_Expectation_posRV (Rbar_pos_fun_part f)); unfold is_finite.
    - destruct (Rbar_Expectation_posRV (Rbar_neg_fun_part f)); simpl; intuition discriminate.
    - destruct (Rbar_Expectation_posRV (Rbar_neg_fun_part f)); simpl; intuition discriminate.
    - now simpl in H0.
    - now apply Rbar_pos_fun_part_rv.
    - now apply Rbar_neg_fun_part_rv.      
  Qed.

  Lemma finite_Rbar_Expectation_almost_finite
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) :
    Rbar_IsFiniteExpectation f ->
    ps_P (exist sa_sigma _ (sa_finite_Rbar f rv)) = 1.
  Proof.
    intros.
    generalize (finite_Rbar_Expectation_posRV_almost_finite (Rbar_rvabs f) (Rbar_rvabs_rv f) (Rbar_rvabs_prv f)); intros.
    assert (pre_event_equiv
              (fun x : Ts => is_finite (Rbar_rvabs f x))
              (fun x : Ts => is_finite (f x))).
    {
      intro x.
      now unfold Rbar_rvabs, is_finite; destruct (f x); simpl.
    }
    assert (event_equiv
              (exist sa_sigma (fun x : Ts => is_finite (Rbar_rvabs f x))
                     (sa_finite_Rbar (Rbar_rvabs f) (Rbar_rvabs_rv f)))
              (exist sa_sigma (fun x : Ts => is_finite (f x)) (sa_finite_Rbar f rv))).
    easy.
    erewrite <- ps_proper; try eapply H2.
    apply H0.
    now apply finiteExp_Rbar_rvabs.
  Qed.    

    Lemma Rbar_rv_le_pos_fun_part (rv_X1 rv_X2 : Ts -> Rbar) :
      Rbar_rv_le rv_X1 rv_X2 ->
      Rbar_rv_le (fun x : Ts => Rbar_pos_fun_part rv_X1 x) 
                 (fun x : Ts => Rbar_pos_fun_part rv_X2 x).
    Proof.
      intros le12 a.
      unfold Rbar_pos_fun_part, Rbar_max.
      match_destr; match_destr; trivial.
      - simpl; lra.
      - unfold Rbar_le in *.
        match_destr.
        + lra.
        + easy.
      - specialize (le12 a).
        unfold Rbar_le in *.
        match_destr; match_destr_in le12; lra.
    Qed.

    Lemma Rbar_rv_le_neg_fun_part (rv_X1 rv_X2 : Ts -> Rbar) :
      Rbar_rv_le rv_X1 rv_X2 ->
      Rbar_rv_le (fun x : Ts => Rbar_neg_fun_part rv_X2 x) 
                 (fun x : Ts => Rbar_neg_fun_part rv_X1 x).
    Proof.
      intros le12 a.
      unfold Rbar_neg_fun_part, Rbar_max; simpl.
      specialize (le12 a).
      rewrite <- Rbar_opp_le in le12.
      match_destr; match_destr; trivial.
      - simpl; lra.
      - unfold Rbar_le in *.
        match_destr.
        + lra.
        + easy.
      - unfold Rbar_le in *.
        match_destr; match_destr_in le12; lra.
    Qed.

  Lemma Rbar_IsFiniteExpectation_bounded (rv_X1 rv_X2 rv_X3 : Ts -> Rbar)
        {isfe1:Rbar_IsFiniteExpectation rv_X1}
        {isfe2:Rbar_IsFiniteExpectation rv_X3}
    :
      Rbar_rv_le rv_X1 rv_X2 ->
      Rbar_rv_le rv_X2 rv_X3 ->
      Rbar_IsFiniteExpectation rv_X2.
  Proof.
    intros.
    unfold Rbar_IsFiniteExpectation in *.
    unfold Rbar_Expectation in *.
    unfold Rbar_minus' in *.
    match_case_in isfe1
    ; [ intros ? eqq1 | intros eqq1]
    ; rewrite eqq1 in isfe1
    ; try contradiction.
    match_case_in isfe2
    ; [ intros ? eqq2 | intros eqq2]
    ; rewrite eqq2 in isfe2
    ; try contradiction.
    match_destr_in isfe1; try contradiction.
    match_destr_in isfe2; try contradiction.
    apply Finite_Rbar_plus' in eqq1.
    apply Finite_Rbar_plus' in eqq2.
    destruct eqq1 as [eqq1pos eqq1neg].
    destruct eqq2 as [eqq2pos eqq2neg].
    generalize (Rbar_rv_le_pos_fun_part _ _ H0).
    generalize (Rbar_rv_le_neg_fun_part _ _ H).
    intros.
    apply Finite_Rbar_opp in eqq1neg.
    rewrite <- (is_finite_Rbar_Expectation_posRV_le _ _ H1); trivial.
    rewrite <- (is_finite_Rbar_Expectation_posRV_le _ _ H2); simpl; trivial.
  Qed.

  Lemma Rbar_pos_fun_part_pos (rv_X : Ts -> Rbar) 
        {prv : Rbar_PositiveRandomVariable rv_X} :
    rv_eq rv_X (Rbar_pos_fun_part rv_X).
  Proof.
    unfold Rbar_pos_fun_part, Rbar_max.
    intro x.
    match_case; intros.
    now apply Rbar_le_antisym.
  Qed.

  Lemma Rbar_neg_fun_part_pos (rv_X : Ts -> Rbar) 
        {prv : Rbar_PositiveRandomVariable rv_X} :
    rv_eq (Rbar_neg_fun_part rv_X) (fun x => (const 0) x).
  Proof.
    unfold Rbar_neg_fun_part, const, Rbar_max.
    intro x.
    specialize (prv x).
    rewrite <- Rbar_opp_le in prv.
    replace (Rbar_opp 0) with (Finite 0) in prv by (simpl; apply Rbar_finite_eq; lra).
    match_case; intros.
    now apply Rbar_le_antisym.
  Qed.

  Instance prv_0 :
    (@Rbar_PositiveRandomVariable Ts (fun x => const 0 x)).
  Proof.
    unfold Rbar_PositiveRandomVariable.
    intros.
    simpl.
    unfold const.
    lra.
  Qed.

  Lemma Rbar_Expectation_pos_posRV (rv_X : Ts -> Rbar) 
        {prv : Rbar_PositiveRandomVariable rv_X} :
    Rbar_Expectation rv_X = Some (Rbar_Expectation_posRV rv_X).
  Proof.
    unfold Rbar_Expectation.
    rewrite <- (Rbar_Expectation_posRV_ext _ _ (Rbar_pos_fun_part_pos rv_X)).
    rewrite (Rbar_Expectation_posRV_ext _ _ (Rbar_neg_fun_part_pos rv_X)).
    replace (Rbar_Expectation_posRV (const 0)) with (Finite 0).
    - unfold Rbar_minus'.
      simpl.
      rewrite Ropp_0.
      unfold Rbar_plus'.
      match_case; intros.
      + f_equal.
        apply Rbar_finite_eq.
        lra.
    - generalize (Rbar_Expectation_posRV_const (Finite 0)); intros.
      symmetry.
      assert (0 <= 0) by lra.
      apply (H H0).
  Qed.

  Lemma Rbar_IsLp_bounded n (rv_X1 rv_X2 : Ts -> Rbar)
        (rle:Rbar_rv_le (fun (omega : Ts) => Rbar_power (Rbar_abs (rv_X1 omega)) n) rv_X2)
        {islp:Rbar_IsFiniteExpectation rv_X2}
    :
      IsLp_Rbar prts n rv_X1.
  Proof.
    unfold IsLp_Rbar.
    assert (Rbar_IsFiniteExpectation (fun x => const 0 x)).
    {
      generalize (Rbar_Expectation_pos_posRV (fun x => Finite (const 0 x))); intros.
      unfold Rbar_IsFiniteExpectation.
      rewrite H.
      assert (0 <= 0) by lra.
      generalize (Rbar_Expectation_posRV_const 0 H0); intros.
      rewrite Rbar_Expectation_posRV_pf_irrel with (prv2 := prv_0) in H1.
      now rewrite H1.
    }
    generalize (Rbar_IsFiniteExpectation_bounded (const 0)
                                                 (fun (omega : Ts) => Rbar_power (Rbar_abs (rv_X1 omega)) n) rv_X2); intros.
    cut_to H0; trivial.
    - unfold Rbar_IsFiniteExpectation in H0.
      rewrite Rbar_Expectation_pos_posRV with (prv := power_abs_pos rv_X1 n) in H0.
      match_destr_in H0; easy.
    - intro x.
      unfold const.
      apply Rbar_power_nonneg.
  Qed.

  Instance Rbar_power_pos m (rv_X: Ts -> Rbar) :
    Rbar_PositiveRandomVariable 
      (fun omega => Rbar_power (rv_X omega) m).
  Proof.
    intro x.
    apply Rbar_power_nonneg.
  Qed.

  Lemma IsLp_Rbar_down_le m n (rv_X:Ts->Rbar)
        {rrv:RandomVariable dom Rbar_borel_sa rv_X}
        (pfle:0 <= n <= m)
        {lp:IsLp_Rbar prts m rv_X} : IsLp_Rbar prts n rv_X.
  Proof.
    apply Rbar_IsLp_bounded with (rv_X2 := fun omega => Rbar_max 1 (Rbar_power (Rbar_abs (rv_X omega)) m)).
    - intros a.
      case_eq (rv_X a); intros.
      + unfold Rbar_abs, Rbar_power.
        replace (Rbar_max 1 (power (Rabs r) m)) with (Finite (Rmax 1 (power (Rabs r) m))).
        unfold Rbar_le.
        destruct (Rle_lt_dec 1 (Rabs r)).
        * eapply Rle_trans; [| eapply Rmax_r].
          now apply Rle_power.
        * eapply Rle_trans; [| eapply Rmax_l].
          unfold power.
          match_destr; [lra | ].
          generalize (Rabs_pos r); intros.
          destruct (Req_EM_T n 0).
          -- subst.
             rewrite Rpower_O; lra.
          -- assert (eqq:1 = Rpower 1 n).
             {
               unfold Rpower.
               rewrite ln_1.
               rewrite Rmult_0_r.
               now rewrite exp_0.
             }
             rewrite eqq.
             apply Rle_Rpower_l; lra.
        * unfold Rbar_max.
          match_case; intros.
          -- simpl in r0.
             now rewrite Rmax_right.
          -- simpl in n0.
             rewrite Rmax_left; trivial.
             left; lra.
      + simpl.
        unfold Rbar_max.
        case_eq (Rbar_le_dec 1 p_infty); intros; trivial.
        now simpl in n0.
      + simpl.
        unfold Rbar_max.
        case_eq (Rbar_le_dec 1 p_infty); intros; trivial.
        now simpl in n0.
    - assert (Rbar_PositiveRandomVariable 
                 (fun omega : Ts => Rbar_max 1 (Rbar_power (Rbar_abs (rv_X omega)) m))).
      {
        intro x.
        unfold Rbar_max.
        match_destr.
        - apply Rbar_power_nonneg.
        - simpl; lra.
      }
      unfold Rbar_IsFiniteExpectation.
      rewrite Rbar_Expectation_pos_posRV with (prv := H).
      unfold IsLp_Rbar in lp.
      assert (0 <= 1) by lra.

      assert (rv1: RandomVariable dom Rbar_borel_sa 
                                  (fun omega => (Rbar_power (Rbar_abs (rv_X omega)) m))).
      {
        apply Rbar_measurable_rv.
        apply Rbar_power_measurable.
        apply Rbar_Rabs_measurable.
        now apply rv_Rbar_measurable.
      }
      generalize (@Rbar_Expectation_posRV_plus Ts dom prts
                    (const (Finite 1))
                    (fun omega => (Rbar_power (Rbar_abs (rv_X omega)) m))
                    _ _ (prvconst _ H0) _ ); intros.
      assert (is_finite
                 (@Rbar_Expectation_posRV Ts dom prts
            (Rbar_rvplus (@const Rbar Ts (Finite (IZR (Zpos xH))))
               (fun omega : Ts => Rbar_power (Rbar_abs (rv_X omega)) m))
            (@pos_Rbar_plus Ts 
                            (@const Rbar Ts (Finite (IZR (Zpos xH))))
                            (fun omega : Ts => Rbar_power (Rbar_abs (rv_X omega)) m)
                            (prvconst _ H0)
                            (Rbar_power_pos m (fun omega : Ts => Rbar_abs (rv_X omega))) ))).
      {
        rewrite H1.
        assert (is_finite (@Rbar_Expectation_posRV Ts dom prts (@const Rbar Ts (Finite 1))  (prvconst _ H0))).
        - generalize (Rbar_Expectation_posRV_const _ H0); intros.
          unfold const in H2.
          unfold const.
          rewrite H2.
          now simpl.
        - rewrite <- H2.
          rewrite <- lp.
          now simpl.
      } 
      assert (Rbar_rv_le
                (fun omega : Ts => Rbar_max 1 (Rbar_power (Rbar_abs (rv_X omega)) m))
                (Rbar_rvplus (const (Finite 1))
                             (fun omega => Rbar_power (Rbar_abs (rv_X omega)) m))).
      {
        intro x.
        unfold Rbar_rvplus, const, Rbar_max.
        match_destr.
        - replace (Rbar_power (Rbar_abs (rv_X x)) m) with
              (Rbar_plus (Finite 0) (Rbar_power (Rbar_abs (rv_X x)) m)) at 1.
          + apply Rbar_plus_le_compat.
            * simpl; lra.
            * apply Rbar_le_refl.
          + apply Rbar_plus_0_l.
        - replace (Finite 1) with (Rbar_plus (Finite 1) (Finite 0)) at 1.
          + apply Rbar_plus_le_compat.
            * apply Rbar_le_refl.
            * apply Rbar_power_nonneg.
          + simpl.
            apply Rbar_finite_eq.
            lra.
      }
      generalize (is_finite_Rbar_Expectation_posRV_le _ _ H3 H2); intros.
      now rewrite <- H4.
   Qed.

  Lemma IsL1_Rbar_abs_Finite (rv_X:Ts->Rbar)
        {lp:IsLp_Rbar prts 1 rv_X} : is_finite (Rbar_Expectation_posRV (Rbar_rvabs rv_X)).
  Proof.
    red in lp.
    assert (rv_eq (fun omega => Rbar_power (Rbar_abs (rv_X omega)) 1)
                  (Rbar_rvabs rv_X)).
    - intro x.
      unfold Rbar_power, Rbar_rvabs.      
      destruct (rv_X x); simpl; trivial.
      unfold power.
      match_destr.
      + generalize (Rabs_pos r); intros.
        apply Rbar_finite_eq.
        lra.
      + rewrite Rpower_1; trivial.
        apply Rabs_pos_lt.
        unfold Rabs in n.
        match_destr_in n; lra.
    - now rewrite (Rbar_Expectation_posRV_ext _ _ H) in lp.
    Qed.

  Lemma IsL1_Rbar_Finite (rv_X:Ts->Rbar)
        {rv:RandomVariable dom Rbar_borel_sa rv_X}
        {lp:IsLp_Rbar prts 1 rv_X} : Rbar_IsFiniteExpectation rv_X.
  Proof.
    apply finiteExp_Rbar_rvabs; trivial.
    now apply IsL1_Rbar_abs_Finite.
  Qed.

  Lemma Rbar_IsLp_IsFiniteExpectation (f : Ts -> Rbar) (n : R)
        {rrv:RandomVariable dom Rbar_borel_sa f} :
    1 <= n ->
    IsLp_Rbar prts n f -> Rbar_IsFiniteExpectation f.
  Proof.
    intros.
    apply IsL1_Rbar_Finite; trivial.
    apply (IsLp_Rbar_down_le n 1 f); trivial.
    lra.
  Qed.

  Lemma Rbar_IsLp_Almost_finite (f : Ts -> Rbar) (n : R)
        {rrv:RandomVariable dom Rbar_borel_sa f} :
    1 <= n ->
    IsLp_Rbar prts n f ->
    ps_P (exist sa_sigma _ (sa_finite_Rbar f rrv)) = 1.    
  Proof.
    intros.
    apply Rbar_IsLp_IsFiniteExpectation in H0; trivial.
    now apply finite_Rbar_Expectation_almost_finite.
  Qed.

  Instance picker_rv
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) 
        (n : nat) :
    RandomVariable dom borel_sa (LpRRV_rv_X prts (LpRRV_lim_picker F PF cF n)).
  Proof.
    exact (LpRRV_rv prts (LpRRV_lim_picker F PF cF n)).
  Qed.

  Lemma Rbar_lim_seq_pos_rv
        (f : nat -> Ts -> R) :
    (forall n, RandomVariable dom Rbar_borel_sa (f n)) ->
    (forall n, Rbar_PositiveRandomVariable (f n)) ->
    RandomVariable dom Rbar_borel_sa (fun omega => Lim_seq (fun n => f n omega)).
  Proof.
    intros.
    unfold RandomVariable.
    apply Rbar_borel_sa_preimage2.    
    intros.
    apply Rbar_lim_seq_measurable_pos; trivial.
    intros.
    unfold RbarMeasurable.
    apply Rbar_borel_sa_preimage2.        
    apply H.
  Qed.
    
   Lemma cauchy_filter_sum_abs_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      ps_P P = 1 /\
      (forall x, 
          P x -> 
          is_finite (Lim_seq 
                       (fun n0 =>
                          LpRRVsum prts pbig 
                                   (fun n =>
                                      (LpRRVabs prts
                                                (LpRRVminus prts
                                                            (LpRRV_lim_picker F PF cF (S (S n)))
                                                            (LpRRV_lim_picker F PF cF (S n))))) n0 x))).
   Proof.
    generalize (cauchy_filter_sum_abs F PF cF); intros.
    pose (limpick :=
             (Rbar_rvlim
           (fun n0 : nat =>
            LpRRVsum prts pbig
              (fun n : nat =>
               LpRRVabs prts
                 (LpRRVminus prts (LpRRV_lim_picker F PF cF (S (S n)))
                    (LpRRV_lim_picker F PF cF (S n)))) n0))).
    assert (rv:RandomVariable dom Rbar_borel_sa limpick).
    {
      subst limpick.
      unfold Rbar_rvlim.
      apply Rbar_lim_seq_pos_rv.
      - intros.
        apply borel_Rbar_borel.
        apply LpRRV_rv.
      - intros.
        apply positive_Rbar_positive.
        apply LpRRVsum_pos.
        intros.
        unfold LpRRVabs, pack_LpRRV;simpl.
        apply prvabs.
    }
    exists (exist _ _ (sa_finite_Rbar limpick rv)).
    split.
    - subst limpick.
      apply Rbar_IsLp_Almost_finite with (n := p); trivial.
    - intros.
      apply H0.
  Qed.

   Lemma cauchy_filter_sum_abs_ext0_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      ps_P P = 1 /\
      (forall x, 
          P x -> 
          is_finite (Lim_seq 
                       (fun n0 =>
                          LpRRVsum prts pbig 
                                   (fun n =>
                                      (LpRRVabs prts
                                                (LpRRVminus prts
                                                            (LpRRV_lim_picker_ext0 F PF cF (S n))
                                                            (LpRRV_lim_picker_ext0 F PF cF n)))) n0 x))).
   Proof.
    generalize (cauchy_filter_sum_abs_ext0 F PF cF); intros.
    pose (limpick :=
             (Rbar_rvlim
           (fun n0 : nat =>
            LpRRVsum prts pbig
              (fun n : nat =>
               LpRRVabs prts
                 (LpRRVminus prts (LpRRV_lim_picker_ext0 F PF cF (S n))
                    (LpRRV_lim_picker_ext0 F PF cF n))) n0))).
    assert (rv:RandomVariable dom Rbar_borel_sa limpick).
    {
      subst limpick.
      unfold Rbar_rvlim.
      apply Rbar_lim_seq_pos_rv.
      - intros.
        apply borel_Rbar_borel.
        apply LpRRV_rv.
      - intros.
        apply positive_Rbar_positive.
        apply LpRRVsum_pos.
        intros.
        unfold LpRRVabs, pack_LpRRV;simpl.
        apply prvabs.
    }
    exists (exist _ _ (sa_finite_Rbar limpick rv)).
    split.
    - subst limpick.
      apply Rbar_IsLp_Almost_finite with (n := p); trivial.
    - intros.
      apply H0.
  Qed.

  Lemma cauchy_filter_sum_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      ps_P P = 1 /\
      (forall x, 
          P x -> 
          ex_finite_lim_seq
            (fun n0 =>
               LpRRVsum prts pbig 
                        (fun n =>
                           (LpRRVminus prts
                                       (LpRRV_lim_picker F PF cF (S (S n)))
                                       (LpRRV_lim_picker F PF cF (S n)))) n0 x)).
  Proof.
    generalize (cauchy_filter_sum_abs_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    unfold LpRRVsum, pack_LpRRV, rvsum; simpl.
    unfold LpRRVsum, pack_LpRRV, rvsum in H0; simpl in H0.
    unfold rvabs in H0.
    now apply lim_sum_abs_bounded.
 Qed.

  Lemma ex_finite_lim_seq_ext (f g : nat -> R) :
    (forall n, f n = g n) ->
    ex_finite_lim_seq f <-> ex_finite_lim_seq g.
  Proof.
    intros.
    unfold ex_finite_lim_seq.
    split; intros;
      destruct H0 as [l ?]; exists l.
    - now apply is_lim_seq_ext with (u := f).      
    - now apply is_lim_seq_ext with (u := g).      
  Qed.

  Lemma ex_finite_lim_seq_S (f : nat -> R) :
    ex_finite_lim_seq f <-> ex_finite_lim_seq (fun n => f (S n)).
  Proof.
    unfold ex_finite_lim_seq.
    split; intros; destruct H as [l ?]; exists l.
    now apply is_lim_seq_incr_1 in H.
    now apply is_lim_seq_incr_1.    
  Qed.

  Lemma cauchy_filter_sum_ext0_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      ps_P P = 1 /\
      (forall x, 
          P x -> 
          ex_finite_lim_seq
            (fun n0 =>
               LpRRVsum prts pbig 
                        (fun n =>
                           (LpRRVminus prts
                                       (LpRRV_lim_picker_ext0 F PF cF (S n))
                                       (LpRRV_lim_picker_ext0 F PF cF n))) n0 x)).
  Proof.
    generalize (cauchy_filter_sum_abs_ext0_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    unfold LpRRVsum, pack_LpRRV, rvsum; simpl.
    unfold LpRRVsum, pack_LpRRV, rvsum in H0; simpl in H0.
    unfold rvabs in H0.
    now apply lim_sum_abs_bounded.
 Qed.
    
  Lemma cauchy_filter_rvlim_finite0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      ps_P P = 1 /\
      (forall x, P x -> 
                 ex_finite_lim_seq (fun n => (LpRRV_lim_picker F PF cF (S (S n))) x)).
  Proof.
    generalize (cauchy_filter_sum_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    rewrite ex_finite_lim_seq_ext in H0.
    shelve.
    intros.
    generalize (LpRRVsum_telescope0 (fun n => LpRRV_lim_picker F PF cF (S n)) n); intros.
    apply H2.
    Unshelve.
    unfold LpRRVminus, pack_LpRRV in H0; simpl in H0.
    unfold rvminus, rvplus, rvopp, rvscale in H0.
    unfold ex_finite_lim_seq in H0.
    destruct H0 as [l ?].
    unfold ex_finite_lim_seq.
    exists (l + LpRRV_lim_picker F PF cF 1 x).
    apply is_lim_seq_ext with
        (u :=  fun n : nat =>
                 (LpRRV_lim_picker F PF cF (S (S n)) x + -1 * LpRRV_lim_picker F PF cF 1 x)
                   +
                   (LpRRV_lim_picker F PF cF 1 x)); [(intros; lra) |].
    apply is_lim_seq_plus'; trivial.
    apply is_lim_seq_const.
 Qed.

    Lemma cauchy_filter_rvlim_ext0_finite0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      ps_P P = 1 /\
      (forall x, P x -> 
                 ex_finite_lim_seq (fun n => (LpRRV_lim_picker F PF cF (S n)) x)).
  Proof.
    generalize (cauchy_filter_sum_ext0_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    rewrite ex_finite_lim_seq_ext in H0.
    shelve.
    intros.
    generalize (LpRRVsum_telescope0 (fun n => LpRRV_lim_picker_ext0 F PF cF n) n); intros.
    apply H2.
    Unshelve.
    unfold LpRRVminus, pack_LpRRV in H0; simpl in H0.
    unfold rvminus, rvplus, rvopp, rvscale, const in H0.
    rewrite ex_finite_lim_seq_ext in H0.
    apply H0.
    intros.
    lra.
 Qed.

    Lemma cauchy_filter_rvlim_Sext0_finite0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      ps_P P = 1 /\
      (forall x, P x -> 
                 ex_finite_lim_seq (fun n => (LpRRV_lim_picker F PF cF n) x)).
   Proof.
     generalize (cauchy_filter_rvlim_ext0_finite0 F PF cF); intros.
     destruct H as [P [? ?]].
     exists P.
     split; trivial; intros.
     specialize (H0 x H1).
     now apply ex_finite_lim_seq_S.
   Qed.



  Lemma cauchy_filter_rvlim_finite
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      exists (dec: forall x, {P x} + {~ P x}),
        ps_P P = 1 /\
        (forall x,
          ex_finite_lim_seq (fun n => (rvmult (EventIndicator dec)
                                              (LpRRV_lim_picker F PF cF (S n)))
                                        x) ) /\
        IsLp prts p
             (rvlim (fun n => (rvmult (EventIndicator dec)
                                      (LpRRV_lim_picker F PF cF (S n))))).
  Proof.
    generalize (cauchy_filter_rvlim_ext0_finite0 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P.
    assert (forall x: Ts, {P x} + {~ P x}).
    {
      intros.
      apply ClassicalDescription.excluded_middle_informative.
    }
    exists X.
    split; trivial.
    split.
    - intros.
      destruct (X x).
      + specialize (H0 x e).
        unfold ex_finite_lim_seq.
        unfold ex_finite_lim_seq in H0.
        destruct H0.
        exists x0.
        eapply is_lim_seq_ext.
        shelve.
        apply H0.
        Unshelve.
        intros; simpl.
        unfold rvmult, EventIndicator.
        match_destr; try tauto; lra.
      + unfold rvmult, EventIndicator, ex_finite_lim_seq.
        exists 0.
        apply is_lim_seq_ext with (u := (const 0)); [|apply is_lim_seq_const].
        intros.
        unfold const.
        match_destr; try tauto; lra.
    - generalize (cauchy_filter_Rbar_rvlim1 F PF cF); intros.
      apply IsLp_Rbar_IsLp.
      apply (IsLp_Rbar_proper_almost prts _ (Rbar_rvlim (fun n : nat => LpRRV_lim_picker F PF cF (S n))))
      ; try typeclasses eauto; trivial.
      exists P. split; trivial; intros a Pa.
      specialize (H0 _ Pa).
      unfold Rbar_rvlim.
      unfold rvlim.
      unfold rvmult, EventIndicator.
      destruct (X a); [| tauto].
      rewrite Lim_seq_ext with (u := (fun n : nat => 1 * LpRRV_lim_picker F PF cF (S n) a))
                               (v := (fun n : nat => LpRRV_lim_picker F PF cF (S n) a)); [|intros; lra].
      rewrite ex_finite_lim_seq_correct in H0.
      destruct H0.
      auto.
  Qed.

  Lemma cauchy_filter_rvlim_finite1
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    { P: event dom | 
         exists dec: forall x, {P x} + {~ P x},
           ps_P P = 1 /\
           (forall x,
               ex_finite_lim_seq (fun n => (rvmult (EventIndicator dec)
                                                (LpRRV_lim_picker F PF cF (S n)))
                                             x) ) /\
           IsLp prts p
                (rvlim (fun n => (rvmult (EventIndicator dec)
                                      (LpRRV_lim_picker F PF cF (S n)))))
    }.
  Proof.
    apply constructive_indefinite_description.
    apply cauchy_filter_rvlim_finite.
  Qed.

  Lemma cauchy_filter_rvlim_finite2
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    { P: event dom &
         {dec: forall x, {P x} + {~ P x} |
           ps_P P = 1 /\
           (forall x,
               ex_finite_lim_seq (fun n => (rvmult (EventIndicator dec)
                                                   (LpRRV_lim_picker F PF cF (S n)))
                                          x) ) /\
           IsLp prts p
                (rvlim (fun n => (rvmult (EventIndicator dec)
                                         (LpRRV_lim_picker F PF cF (S n)))))}
    }.
  Proof.
    destruct (cauchy_filter_rvlim_finite1 F PF cF).
    exists x.
    apply constructive_indefinite_description.
    apply e.
  Qed.

  Definition cauchy_rvlim_fun  (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : Ts -> R
    := match cauchy_filter_rvlim_finite2 F PF cF with
       | existT P (exist dec PP) =>  (rvlim (fun n => (rvmult (EventIndicator dec)
                                                              (LpRRV_lim_picker F PF cF (S n)))))
       end.

  Global Instance cauchy_rvlim_fun_isl2 (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : IsLp prts p (cauchy_rvlim_fun F PF cF).
  Proof.
    unfold cauchy_rvlim_fun.
    repeat match_destr.
    tauto.
  Qed.

  Global Instance cauchy_rvlim_fun_rv (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : RandomVariable dom borel_sa (cauchy_rvlim_fun F PF cF).
  Proof.
    unfold cauchy_rvlim_fun.
    repeat match_destr.
    apply rvlim_rv.
    - typeclasses eauto.
    - tauto.
  Qed.
  
  Definition LpRRV_lim_with_conditions (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : LpRRV prts p
      := pack_LpRRV prts (cauchy_rvlim_fun F PF cF).

  Definition LpRRV_lim (F : ((LpRRV prts p -> Prop) -> Prop)) : LpRRV prts p.
  Proof.
    destruct (excluded_middle_informative (ProperFilter F)).
    - destruct (excluded_middle_informative (cauchy (T:= LpRRV_UniformSpace prts pbig) F)).
      + exact (LpRRV_lim_with_conditions _ _ c).
      + exact (LpRRVzero prts).
    - exact (LpRRVzero prts).
  Defined.
  
  Lemma Lim_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    Lim_seq (fun n => f (u n)) = f (Lim_seq u).
  Proof.
    intros.
    unfold ex_finite_lim_seq in H0.
    destruct H0.
    generalize (is_lim_seq_continuous f u x); intros.
    generalize (is_lim_seq_unique _ _ H0); intros.
    rewrite H2 in H.
    specialize (H1 H H0).
    apply is_lim_seq_unique in H1.
    now rewrite H2.
  Qed.

  Lemma is_finite_Lim_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    is_finite (Lim_seq (fun n => f (u n))).
  Proof.
    intros.
    unfold ex_finite_lim_seq in H0.
    destruct H0.
    generalize (is_lim_seq_continuous f u x); intros.
    generalize (is_lim_seq_unique _ _ H0); intros.
    rewrite H2 in H.
    specialize (H1 H H0).
    apply is_lim_seq_unique in H1.
    now rewrite H1.
  Qed.

  Lemma ex_lim_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    ex_lim_seq (fun n => f (u n)).
  Proof.
    intros.
    unfold ex_finite_lim_seq in H0.
    destruct H0.
    generalize (is_lim_seq_continuous f u x); intros.
    generalize (is_lim_seq_unique _ _ H0); intros.
    unfold ex_lim_seq.
    exists (f x).
    rewrite H2 in H.
    now apply H1.
  Qed.

  Lemma lim_seq_lim_inf (f : nat -> R) :
    ex_lim_seq f ->
    Lim_seq f = LimInf_seq f.
  Proof.
    intros.
    rewrite ex_lim_LimSup_LimInf_seq in H.
    unfold Lim_seq.
    rewrite H.
    now rewrite x_plus_x_div_2.
  Qed.

  Lemma is_finite_LimInf_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    is_finite (LimInf_seq (fun n => f (u n))).
  Proof.
    intros.
    rewrite <- lim_seq_lim_inf.
    apply is_finite_Lim_seq_continuous; trivial.
    now apply ex_lim_seq_continuous.
 Qed.

  Lemma LpRRVnorm_Expectation_posRV 
        (f : LpRRV prts p)
        (rv : RandomVariable dom borel_sa f) :
    LpRRVnorm prts f = power (Expectation_posRV (rvpower (rvabs f)  (const p))) (/ p).
  Proof.
    unfold LpRRVnorm.
    f_equal.
    now erewrite FiniteExpectation_posRV.
  Qed.

   Lemma rvpowerabs_rvminus_rvlim_comm (f : nat -> Ts -> R) (n:nat):
     (forall x, ex_finite_lim_seq (fun n0 => f n0 x)) ->
     (rv_eq
        (rvpower (rvabs (rvminus (rvlim f) (f n))) (const p))
        (rvlim (fun x => (rvpower (rvabs (rvminus (f x) (f n))) (const p))))).
    Proof.
      intros exfin z.
      unfold rvpower, rvabs, rvminus, rvplus, rvopp, rvscale, rvlim, const.
      pose (p_power_abs := fun x => @p_power p (Rabs x) ).
      generalize (Lim_seq_ext 
                    (fun n0 : nat => power (Rabs (f n0 z + -1 * f n z)) p)
                    (fun n0 => p_power_abs (f n0 z + -1 * f n z))); intros.
      rewrite H.
      - rewrite Lim_seq_continuous; trivial.
        + unfold p_power_abs, p_power.
          rewrite Lim_seq_plus, Lim_seq_const.
          * specialize (exfin z).
            rewrite ex_finite_lim_seq_correct in exfin.
            destruct exfin.
            rewrite <- H1.
            now simpl.
          * specialize (exfin z).
            rewrite ex_finite_lim_seq_correct in exfin.
            now destruct exfin.
          * apply ex_lim_seq_const.
          * specialize (exfin z).
            rewrite ex_finite_lim_seq_correct in exfin.
            destruct exfin.
            rewrite <- H1.
            rewrite Lim_seq_const.
            now simpl.
        + apply continuity_p_power_Rabs; lra.
        + unfold ex_finite_lim_seq.
          specialize (exfin z).
          unfold ex_finite_lim_seq in exfin.
          destruct exfin.
          exists (x + -1 * f n z).
          apply is_lim_seq_plus'; trivial.
          apply is_lim_seq_const.
      - intros.
        now unfold p_power_abs.
   Qed.

    Lemma lt_Rbar_lt (x : Rbar) (y : R) :
      0 < y ->
      Rbar_lt x y -> (real x) < y.
    Proof.
      intros.
      destruct x.
      - now simpl in H.
      - now simpl.
      - now simpl.
    Qed.

    Lemma le_Rbar_le (x : Rbar) (y : R) :
      0 <= y ->
      Rbar_le x y -> (real x) <= y.
    Proof.
      intros.
      destruct x.
      - now simpl in H.
      - now simpl.
      - now simpl.
    Qed.

    Lemma LimInf_seq_ext (f g : nat -> R) :
      eventually (fun n => f n = g n) ->
      LimInf_seq f = LimInf_seq g.
    Proof.
      intros.
      unfold eventually in H.
      destruct H.
      apply Rbar_le_antisym.
      - apply LimInf_le.
        exists x.
        intros.
        specialize (H n H0).
        lra.
      - apply LimInf_le.
        exists x.
        intros.
        specialize (H n H0).
        lra.
    Qed.

  Instance Rbar_real_rv 
           (f : Ts -> Rbar)
           (rv : RandomVariable dom Rbar_borel_sa f) :
    RandomVariable dom borel_sa (fun omega => real (f omega)).
  Proof.
    apply measurable_rv.
    apply Rbar_real_measurable.
    now apply rv_Rbar_measurable.
  Qed.
  
  Lemma norm_rvminus_rvlim_le
        (f : nat -> LpRRV prts p) 
        (rvl : RandomVariable dom borel_sa (rvlim f)) 
        (isl : IsLp prts p (rvlim f)) :
    (forall x, ex_finite_lim_seq (fun n => f n x)) ->
    (forall (eps:posreal),
      exists (N : nat),
        forall (n m : nat), 
          (n >= N)%nat ->
          (m >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (f m) (f n))) < eps) ->
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) <= eps. 
  Proof.
    intros.
    specialize (H0 eps).
    destruct H0 as [N ?].
    exists N.
    intros.
    unfold LpRRVnorm, LpRRVminus, pack_LpRRV; simpl.
    replace (pos eps) with (power (power eps p) (/ p)) by (apply inv_power_cancel; [left; apply cond_pos| lra]).
    apply Rle_power_l.
    left; apply Rinv_0_lt_compat; lra.
    split.
    apply FiniteExpectation_pos; typeclasses eauto.
    assert (1 <= 2) by lra.
    generalize (rvpowerabs_rvminus_rvlim_comm f n H); intros.
    rewrite (FiniteExpectation_ext_alt _ _ _ H3).
    assert (rv_eq 
              (rvlim (fun x : nat => rvpower (rvabs (rvminus (f x) (f n))) (const p)))
              (fun omega => LimInf_seq (fun x : nat => rvpower (rvabs (rvminus (f x) (f n))) (const p) omega))).
    {
      intros z.
      unfold rvlim.
      rewrite lim_seq_lim_inf; trivial.
      pose (p_power_abs := fun x => @p_power p (Rabs x) ).      
      unfold rvpower, rvabs, const, rvminus, rvplus, rvopp, rvscale.
      apply ex_lim_seq_ext with (u := fun n0 => p_power_abs (f n0 z + -1 * f n z)).
      intros.
      now unfold p_power_abs, p_power.
      specialize (H z).
      unfold ex_finite_lim_seq in H.
      destruct H.
      unfold ex_lim_seq.
      exists (p_power_abs (x + -1 * f n z)).
      apply is_lim_seq_continuous.
      apply continuity_p_power_Rabs; lra.
      apply is_lim_seq_plus'; trivial.
      apply is_lim_seq_const.
    }
    rewrite (FiniteExpectation_ext_alt _ _ _ H4).
    unfold LpRRVnorm in H0.
    erewrite FiniteExpectation_posRV.
    apply le_Rbar_le.
    rewrite <- (power0_Sbase p).
    assert (0 < eps) by apply cond_pos.
    apply Rle_power_l; lra.
    assert (forall omega : Ts, is_finite (LimInf_seq (fun n0 : nat => rvpower (rvabs (rvminus (f n0) (f n))) (const p) omega))).
    {
      intros.
      unfold rvpower, rvabs, rvminus, rvplus, rvopp, rvscale, rvlim, const.
      pose (p_power_abs := fun x => @p_power p (Rabs x) ).
      specialize (H omega).

      generalize (LimInf_seq_ext 
                    (fun n0 : nat => power (Rabs (f n0 omega + -1 * f n omega)) p)
                    (fun n0 => p_power_abs (f n0 omega + -1 * f n omega))); intros.
      rewrite H5.
      - apply is_finite_LimInf_seq_continuous.
        + rewrite ex_finite_lim_seq_correct in H.
          destruct H.
          unfold p_power_abs, p_power.
          rewrite Lim_seq_plus, Lim_seq_const; trivial.
          * apply continuity_p_power_Rabs; lra.
          * apply ex_lim_seq_const.
          * rewrite Lim_seq_const.
            rewrite <- H6.
            now simpl.
        + unfold ex_finite_lim_seq.
          unfold ex_finite_lim_seq in H.
          destruct H.
          exists (x + -1 * f n omega).
          apply is_lim_seq_plus'; trivial.
          apply is_lim_seq_const.
      - intros.
        exists (0%nat); intros.
        now unfold p_power_abs.
    }
    eapply Rbar_le_trans.
    - apply Fatou; trivial.
      + intros; typeclasses eauto.
      + intros.
        generalize (IsLp_minus prts pnneg (f n0) (f n)); intros.
        unfold IsLp in H6.
        unfold IsFiniteExpectation in H6.
        erewrite Expectation_pos_posRV in H6.
        simpl in H6.
        match_case_in H6; intros.
        * rewrite H7; now simpl.
        * now rewrite H7 in H6.
        * now rewrite H7 in H6.
      + apply Rbar_real_rv.
        apply Rbar_lim_inf_rv.
        intros.
        typeclasses eauto.
    - simpl.
      unfold LpRRVnorm in H1.
      simpl in H1.
      assert (forall n0,
                 (n0 >= N)%nat ->
                 Expectation_posRV (fun omega : Ts => rvpower (rvabs (rvminus (f n0) (f n))) (const p) omega) <=
                 (power eps p)).
      {
        intros.
        specialize (H0 n n0 H1 H6).
        generalize (Rle_power_l (power (FiniteExpectation prts (rvpower (rvabs (rvminus (f n0) (f n))) (const p))) (/ p) ) (pos eps) p); intros.
        rewrite power_inv_cancel in H7.
        erewrite FiniteExpectation_posRV in H7.
        apply H7.
        lra.
        split; [apply power_nonneg |].
        erewrite FiniteExpectation_posRV in H0.
        left; apply H0.
        apply FiniteExpectation_pos.
        typeclasses eauto.
        lra.
      }
      replace (Finite (power eps p)) with (LimInf_seq (fun _ => power eps p)) by apply LimInf_seq_const.
      apply LimInf_le.
      exists N; intros.
      apply H6.
      lia.
  Qed.
    
  Lemma norm_rvminus_rvlim
        (f : nat -> LpRRV prts p) 
        (rvl : RandomVariable dom borel_sa (rvlim f)) 
        (isl : IsLp prts p (rvlim f)) :
    (forall x, ex_finite_lim_seq (fun n => f n x)) ->
    (forall (eps:posreal),
      exists (N : nat),
        forall (n m : nat), 
          (n >= N)%nat ->
          (m >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (f m) (f n))) < eps) ->
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.
  Proof.
    intros.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/2) by lra.
    generalize (norm_rvminus_rvlim_le f rvl isl H H0 (mkposreal _ H2)); intros.
    destruct H3 as [N ?].
    exists N.
    intros.
    eapply Rle_lt_trans.
    apply H3; trivial.
    simpl; lra.
  Qed.

End L2.
Section L2_complete.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Context {p:R}.
  Context (pbig:1 <= p).

  Let pnneg : nonnegreal := bignneg p pbig.
  Canonical pnneg.

  Global Instance event_restricted_islp P n (pf1 : ps_P P = 1) pf 
           (f : Ts -> R) 
           (isl:  IsLp  prts n f):
    IsLp (event_restricted_prob_space prts P pf) n (event_restricted_function P f).
  Proof.
    unfold IsLp, IsFiniteExpectation in *.
    now rewrite event_restricted_Expectation with (P0 := P) (pf0 := pf) in isl; trivial.
  Qed.

  Program Definition event_restricted_LpRRV n P (pf1 : ps_P P = 1) pf (rv:LpRRV prts n) :
    LpRRV (event_restricted_prob_space prts P pf) n
    := {|
    LpRRV_rv_X := event_restricted_function P (LpRRV_rv_X _ rv)
      |} .
  Next Obligation.
    destruct rv.
    now apply event_restricted_islp.
  Qed.

  Lemma restricted_LpRRVminus P (pf1 : ps_P P = 1) pf
        (f g : LpRRV prts p) :
    LpRRV_seq 
      (LpRRVminus (event_restricted_prob_space prts P pf)
                  (event_restricted_LpRRV p P pf1 pf f)
                  (event_restricted_LpRRV p P pf1 pf g))
      (event_restricted_LpRRV p P pf1 pf (LpRRVminus prts f g)).
  Proof.
    easy.
  Qed.

  Lemma restricted_LpRRVnorm P (pf1 : ps_P P = 1) pf
        (f : LpRRV prts p) :
    LpRRVnorm prts f = LpRRVnorm (event_restricted_prob_space prts P pf)
                                 (event_restricted_LpRRV p P pf1 pf f).
  Proof.
    intros.
    unfold LpRRVnorm.
    f_equal.
    unfold FiniteExpectation.
    simpl.
    destruct (IsFiniteExpectation_Finite prts (rvpower (rvabs f) (const p))).
    destruct (IsFiniteExpectation_Finite 
                (event_restricted_prob_space prts P pf)
                (rvpower (rvabs (event_restricted_function P f)) (const p))).
    simpl.
    rewrite event_restricted_Expectation with (P0 := P) (pf0 := pf) in e; trivial.
    assert (rv_eq
              (event_restricted_function P (rvpower (rvabs f) (const p)))
              (rvpower (rvabs (event_restricted_function P f)) (const p))) by easy.
    rewrite (Expectation_ext H) in e.
    rewrite e in e0.
    now inversion e0.
  Qed.

  Lemma restricted_LpRRV_rvlim P (pf1 : ps_P P = 1) pf
        (f : nat -> LpRRV prts p) 
        (rv : RandomVariable dom borel_sa (rvlim (fun x : nat => f x)))
        (isl : IsLp prts p (rvlim (fun x : nat => f x)))
        (rve : RandomVariable (event_restricted_sigma P) borel_sa
         (rvlim (fun x : nat => event_restricted_LpRRV p P pf1 pf (f x)))) 
        (isle : IsLp (event_restricted_prob_space prts P pf) p
         (rvlim (fun x : nat => event_restricted_LpRRV p P pf1 pf (f x)))) :
    ps_P P = 1 ->
    LpRRV_seq 
      (pack_LpRRV (event_restricted_prob_space prts P pf)
                  (rvlim (fun x : nat => event_restricted_LpRRV p P pf1 pf (f x))))
      (event_restricted_LpRRV p P pf1 pf
                               (pack_LpRRV prts (rvlim (fun x : nat => f x)))).
  Proof.
    easy.
  Qed.

  Lemma norm_rvminus_rvlim_almost 
        (f : nat -> LpRRV prts p) 
        (rvl : RandomVariable dom borel_sa (rvlim f)) 
        (isl : IsLp prts p (rvlim f))
        (P : event dom) :
    ps_P P = 1 ->
    (forall x, P x -> ex_finite_lim_seq (fun n => f n x)) ->
    (forall (eps:posreal),
      exists (N : nat),
        forall (n m : nat), 
          (n >= N)%nat ->
          (m >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (f m) (f n))) < eps) ->
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.
  Proof.
    intros.
    pose (nts := event_restricted_domain P).
    pose (ndom := event_restricted_sigma P).
    assert (pf : 0 < ps_P P).
    rewrite H; lra.
    pose (nprts := event_restricted_prob_space prts P pf).
    pose (nf := fun n => event_restricted_LpRRV _ P H pf (f n)).
    pose (nrvlim := event_restricted_function P (rvlim f)).
    assert (rv_eq nrvlim (rvlim nf)) by easy.
    assert (nrvl : RandomVariable ndom borel_sa (rvlim nf)).
    {
      apply rvlim_rv.
      - typeclasses eauto.
      - intros.
        destruct omega; simpl.
        apply H0.
        now simpl.
    }
    assert (nisl : IsLp nprts p (rvlim nf)).
    {
      unfold nprts, nf.
      generalize (event_restricted_islp P p H pf _ isl); intros.
      apply H3.
    }
    generalize (norm_rvminus_rvlim nprts pbig nf nrvl nisl); intros.
    cut_to H3.
    - specialize (H3 eps).
      destruct H3 as [N ?].
      exists N.
      intros.
      specialize (H3 n H4).
      rewrite restricted_LpRRVnorm with (P := P) (pf := pf) (pf1 := H); trivial.
      unfold nprts in H3.
      rewrite <- restricted_LpRRVminus; trivial.
      unfold nf in H3.
      rewrite restricted_LpRRV_rvlim in H3; trivial.
      apply H3.
    - intros.
      unfold nf.
      unfold event_restricted_domain in x.
      apply H0.
      destruct x.
      now simpl.
    - intros.
      specialize (H1 eps0).
      destruct H1 as [N ?].
      exists N.
      intros.
      specialize (H1 n m H4 H5).
      unfold nprts, nf.
      generalize (restricted_LpRRVminus P H pf (f m) (f n)); intros.
      unfold pnneg in H6.
      rewrite (LpRRV_norm_sproper (event_restricted_prob_space prts P pf) _ _ H6).
      now rewrite  <- restricted_LpRRVnorm.
   Qed.
 

  Lemma two_pow_gt (r : R) :
    exists n, r < pow 2 n.
  Proof.
    assert (2 > 1) by lra.
    replace (2) with (Rabs 2) in H by (apply Rabs_right; lra).
    generalize (Pow_x_infinity 2 H r); intros.
    destruct H0 as [N ?].
    exists (S N).
    specialize (H0 N).
    rewrite Rabs_right in H0.
    cut_to H0; try lia.
    apply Rge_le in H0.
    eapply Rle_lt_trans.
    apply H0.
    replace (2^N) with (1 * (2^N)) by lra.
    simpl.
    apply Rmult_lt_compat_r; try lra.
    apply pow2_pos.
    left.
    apply pow2_pos.
  Qed.
        
  Lemma inv_two_pow_lt (eps : posreal) :
    exists n, / (pow 2 n) < eps.
  Proof.
    generalize (two_pow_gt (/ eps)); intros.
    destruct H.
    exists x.
    replace (pos eps) with (/ / eps) by
        (rewrite Rinv_involutive; trivial; apply Rgt_not_eq; apply cond_pos).
    apply Rinv_lt_contravar; trivial.
    apply Rmult_lt_0_compat.
    - apply Rinv_0_lt_compat, cond_pos.
    - apply pow2_pos.
  Qed.


  Lemma Npow_eps (eps : posreal) :
    exists (N : nat), 2 / (pow 2 N) < eps.
  Proof.
    generalize (cond_pos eps); intros.
    assert (0 < eps/2) by lra.
    generalize (inv_two_pow_lt (mkposreal _ H0)); intros.
    destruct H1 as [N ?].
    exists N.
    unfold Rdiv.
    rewrite Rmult_comm.
    apply Rmult_lt_reg_r with (r := /2).
    apply Rinv_0_lt_compat; lra.
    rewrite Rmult_assoc.
    rewrite <- Rinv_r_sym; try lra.
    rewrite Rmult_1_r.
    unfold Rdiv in H1.
    apply H1.
  Qed.

  Lemma LpRRVnorm_rvminus_rvlim_almost 
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal)
        (rv : RandomVariable dom borel_sa (rvlim (fun n : nat => LpRRV_lim_picker prts pbig F PF cF (S n)))) 
        (islp : IsLp prts p (rvlim (fun n : nat => LpRRV_lim_picker prts pbig F PF cF (S n)))):
    let f := fun n => LpRRV_lim_picker prts pbig F PF cF (S n)  in 
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.

  Proof.
    unfold cauchy in cF.
    generalize (cauchy_filter_rvlim_finite2 prts pbig F PF cF); intros.
    destruct X as [P [dec [? [? ?]]]].
    apply norm_rvminus_rvlim_almost  with (P := P); trivial.
    - intros.
      specialize (H0 x).
      rewrite ex_finite_lim_seq_ext in H0.
      apply H0.
      intros.
      unfold rvmult, EventIndicator.
      match_destr; try tauto.
      subst f.
      lra.
    - intros.
      generalize (lim_filter_cauchy prts pbig F PF cF); intros.
      generalize (Npow_eps eps1); intros.
      destruct H3 as [N ?].
      exists N; intros.
      specialize (H2 N (S m) (S n)).
      subst f.
      eapply Rlt_trans.
      apply H2; try lia.
      apply H3.
   Qed.
  
  Global Instance IsLp_EventIndicator_mult {P : event dom} (dec : forall x, {P x} + {~ P x}) 
         (rv_X: Ts -> R)
         {rv : RandomVariable dom borel_sa rv_X}
         {islp:IsLp prts p rv_X} :
    IsLp prts p (rvmult (EventIndicator dec) rv_X).
  Proof.
    generalize (IsLp_bounded prts p (rvmult (EventIndicator dec) rv_X) (rvpower (rvabs rv_X) (const p))); intros.
    apply H; trivial.
    intro x.
    unfold rvpower, rvabs, rvmult, const, EventIndicator.
    apply Rle_power_l.
    lra.
    split.
    apply Rabs_pos.
    match_destr.
    - rewrite Rmult_1_l; now right.
    - rewrite Rmult_0_l.
      rewrite Rabs_R0.
      apply Rabs_pos.
  Qed.

  Definition LpRRVindicator {P : event dom} (dec : forall x, {P x} + {~ P x}) (rv : LpRRV prts p) : LpRRV prts p
    :=  pack_LpRRV prts (rvmult (EventIndicator dec) rv).

  Instance rvlim_rv_almost_P 
           (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
           (PF:ProperFilter F)
           (cF:cauchy F)
           {P : event dom} 
           (dec : forall x, {P x} + {~ P x})
           (pf:forall x : Ts,
               ex_finite_lim_seq
                 (fun n : nat => rvmult (EventIndicator dec) (LpRRV_lim_picker prts pbig F PF cF (S n)) x)):
    let f := fun n : nat => LpRRVindicator dec (LpRRV_lim_picker prts pbig F PF cF (S n)) in
    RandomVariable dom borel_sa (rvlim f).
  Proof.
    intros.
    subst f.
    apply rvlim_rv.
    unfold LpRRVindicator.
    unfold pack_LpRRV; simpl.
    typeclasses eauto.
    intros.
    eauto.
  Qed.

  Lemma LpRRVminus_indicator_comm {P : event dom} (dec : forall x, {P x} + {~ P x})
        (f g : LpRRV prts p) :
    LpRRV_seq
      (LpRRVminus prts (LpRRVindicator dec f) (LpRRVindicator dec g))
      (LpRRVindicator dec (LpRRVminus prts f g)).
  Proof.
    intro x.
    unfold LpRRVindicator.
    unfold LpRRVminus, pack_LpRRV; simpl.
    unfold EventIndicator, rvminus, rvmult, rvplus, rvopp, rvscale.
    match_destr; lra.
  Qed.

  Lemma LpRRVnorm_indicator {P : event dom} (dec : forall x, {P x} + {~ P x})
        (f : LpRRV prts p) :
    ps_P P = 1 ->
    LpRRVnorm prts f = LpRRVnorm prts (LpRRVindicator dec f).
  Proof.
    intros.
    unfold LpRRVnorm.
    f_equal.
    apply FiniteExpectation_proper_almost.
    typeclasses eauto.
    typeclasses eauto.
    unfold almost.
    exists P.
    split; trivial.
    intros.
    unfold LpRRVindicator, pack_LpRRV; simpl.
    unfold rvpower, rvabs, const, rvmult, EventIndicator.
    match_destr.
    - now rewrite Rmult_1_l.
    - tauto.
  Qed.

  Lemma LpRRVnorm_rvminus_rvlim_almost_P
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal):
    let '(existT P (exist dec _)) := (cauchy_filter_rvlim_finite2 prts pbig F PF cF) in
    let f := fun n : nat => LpRRVindicator dec (LpRRV_lim_picker prts pbig F PF cF (S n)) in 
    exists (rv:RandomVariable dom borel_sa (rvlim f)),
    exists (isl: IsLp prts p (rvlim f)),
    ps_P P = 1 /\
    (forall x : Ts, ex_finite_lim_seq (fun n : nat => f n x)) /\
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.
  Proof.
    unfold cauchy in cF.
    destruct (cauchy_filter_rvlim_finite2 prts pbig F PF cF)
             as [P [dec [? [? ?]]]].
    intros.
    exists (rvlim_rv_almost_P _ _ _ _ H0).
    exists H1.
    generalize ( norm_rvminus_rvlim_almost f); intros.
    simpl.
    split; trivial.
    split; trivial.
    intros.
    subst f.
    specialize (H2 (rvlim_rv_almost_P F PF cF dec H0)).
    specialize (H2 H1 P H).
    apply H2; [intros; apply H0 |].
    intros.
    generalize (lim_filter_cauchy prts pbig F PF cF); intros.
    generalize (Npow_eps eps1); intros.
    destruct H4 as [N ?].
    exists N; intros.
    specialize (H3 N (S m) (S n) ).
    cut_to H3; try lia.
    rewrite LpRRVminus_indicator_comm .
    rewrite <- LpRRVnorm_indicator; trivial.
    eapply Rlt_trans.
    apply H3.
    apply H4.
  Qed.

  Lemma LpRRVnorm_LpRRV_cauchy_picker
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal) :
    exists (N : nat),
    exists (x : LpRRV prts p),
      (F (Hierarchy.ball x eps)) /\
      (forall (n:nat), (n >= N)%nat ->
                       ((Hierarchy.ball (M := LpRRV_UniformSpace prts pbig) x eps) 
                          (LpRRV_lim_picker prts pbig F PF cF n))).
   Proof.
     intros.
     generalize (inv_two_pow_lt eps); intros.
     destruct H as [N ?].
     generalize (lim_picker_center_included2 prts pbig F PF cF N); intros.
     pose (x0 := (LpRRV_lim_ball_center_center prts pbig F PF cF N)).     
     exists N.
     exists (proj1_sig x0).
     intros.
     generalize (ball_le (M:= LpRRV_UniformSpace prts pbig) (proj1_sig x0) (mkposreal _ (inv_pow_2_pos N)) eps); intros.
     split.
     - destruct x0.
       simpl in *.
       eapply filter_imp; try eapply f.
       apply ball_le.
       lra.
     - intros.
       specialize (H0 n).
       apply H1.
       now left.
       now apply H0.
   Qed.

   Lemma ball_LpRRV_lim_picker
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal) :
     exists (N : nat),
       forall (n : nat), (n >= N)%nat ->
                         (Hierarchy.ball (M := LpRRV_UniformSpace prts pbig) 
                                         (LpRRV_lim_picker prts pbig F PF cF (S n)) eps (LpRRV_lim prts pbig F)).
     Proof.
       generalize (LpRRVnorm_rvminus_rvlim_almost_P F PF cF eps); intros.
       match_case_in H; intros.
       rewrite H0 in H.
       match_destr_in H.
       simpl in H.
       destruct H as [? [? [? [? ?]]]].
       specialize (H2 eps).
       destruct H2 as [N ?].
       exists N.
       intros.
       specialize (H2 n H3).
       unfold LpRRV_lim.
       match_destr; try tauto.
       match_destr; try tauto.
       do 2 red; simpl.
       unfold LpRRV_lim_with_conditions.
       unfold LpRRVball, LpRRVnorm.
       unfold LpRRVnorm in H1.
       unfold bignneg; simpl.
       assert ((FiniteExpectation prts (rvpower (rvabs (rvminus (LpRRV_lim_picker prts pbig F PF cF (S n)) (cauchy_rvlim_fun prts pbig F p0 c))) (const p))) =
                 (FiniteExpectation prts
            (rvpower
               (rvabs
                  (LpRRVminus prts
                     (pack_LpRRV prts (rvlim (fun n : nat => rvmult (EventIndicator x0) (LpRRV_lim_picker prts pbig F PF cF (S n)))))
                     (LpRRVindicator x0 (LpRRV_lim_picker prts pbig F PF cF (S n))))) (const p)))).
       {
         apply FiniteExpectation_proper_almost.       
         typeclasses eauto.
         typeclasses eauto.
         unfold almost.
         exists x.
         split; trivial.
         intros.
         unfold rvpower, const.
         f_equal.
         unfold rvabs, LpRRVminus, pack_LpRRV; simpl.
         unfold rvminus, rvplus, rvopp, rvscale, cauchy_rvlim_fun.
         rewrite (proof_irrelevance _ p0 PF).
         rewrite (proof_irrelevance _ c cF).
         rewrite H0.
         rewrite <- Rabs_Ropp at 1.
         f_equal.
         rewrite Rplus_comm.
         ring_simplify.
         f_equal.
         unfold EventIndicator, rvmult.
         match_destr.
         lra.
         tauto.
       }
       unfold LpRRVnorm, LpRRVminus, pack_LpRRV in H2.
       simpl in H2.
       clear H0.
       clear a.
       erewrite FiniteExpectation_pf_irrel; rewrite H4.
       erewrite FiniteExpectation_pf_irrel in H2.
       apply H2.
     Qed.

  Lemma LpRRVnorm_LpRRV_lim
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal) :
    exists (x : LpRRV prts p),
      (F (Hierarchy.ball x eps)) /\
      ((Hierarchy.ball (M := LpRRV_UniformSpace prts pbig) x eps) (LpRRV_lim prts pbig F)).
  Proof.
    generalize (cond_pos eps); intro eps_pos.
    assert (eps_half: 0 < eps/2) by lra.
    generalize (LpRRVnorm_LpRRV_cauchy_picker F PF cF (mkposreal _ eps_half)); intros.
    destruct H as [N [x [? ?]]].
    exists x.
    split.
    - generalize (ball_le (M:= LpRRV_UniformSpace prts pbig) x (mkposreal _ eps_half) eps); intros.
      eapply filter_imp.
      apply H1.
      simpl; lra.
      apply H.
    - generalize (ball_LpRRV_lim_picker F PF cF (mkposreal _ eps_half)); intros.
      destruct H1.
      specialize (H0 (S (max N x0))).
      cut_to H0; try lia.
      specialize (H1 (max N x0)).
      cut_to H1; try lia.
      replace (pos eps) with ((mkposreal _ eps_half) + (mkposreal _ eps_half)) by (simpl; lra).
      now apply Hierarchy.ball_triangle with (y := (LpRRV_lim_picker prts pbig F PF cF (S (max N x0)))).
   Qed.      

  Lemma L2RRV_lim_complete (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop) 
        (PF : ProperFilter F)
        (cF : cauchy F) :
    forall eps : posreal, F (Hierarchy.ball (LpRRV_lim  prts pbig F) eps).
  Proof.
    intros.
    assert (0 < eps/2).
    {
      apply Rlt_div_r; try lra.
      rewrite Rmult_0_l.
      apply cond_pos.
    }
    generalize (LpRRVnorm_LpRRV_lim F PF cF (mkposreal _ H)); intros.
    destruct H0 as [? [? ?]].
    generalize (Hierarchy.ball_triangle 
                  (M := LpRRV_UniformSpace prts pbig)); intros.
    apply filter_imp with (P := (Hierarchy.ball x (mkposreal _ H))); trivial.
    intros.
    apply Hierarchy.ball_sym in H1.
    replace (pos eps) with ((pos (mkposreal _ H)) + (pos (mkposreal _ H))).
    apply (Hierarchy.ball_triangle _ _ _ _ _ H1 H3).
    simpl; lra.
  Qed.

  Program Definition LpRRVq_lim_with_conditions (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
          (PF:ProperFilter F)
          (cF:cauchy F) : LpRRVq prts p
    := Quot _ (LpRRV_lim_with_conditions prts pbig F PF cF).

  Lemma LpRRVq_lim_with_conditionsE F PF cF : LpRRVq_lim_with_conditions F PF cF  = Quot _ (LpRRV_lim_with_conditions prts pbig F PF cF).
  Proof.
    reflexivity. 
  Qed.
  
  Hint Rewrite LpRRVq_lim_with_conditionsE : quot.

  Definition LpRRV_toLpRRVq_set (s:(LpRRV prts p)->Prop) (x:LpRRVq prts p) : Prop
    := forall y, x = Quot _ y -> s y.

  Definition LpRRVq_filter_to_LpRRV_filter (F:((LpRRVq prts p)->Prop)->Prop) : ((LpRRV prts p)->Prop)->Prop
    := (fun x:(LpRRV prts p)->Prop => F (LpRRV_toLpRRVq_set x)).
  
  Lemma LpRRVq_filter_to_LpRRV_filter_filter (F:((LpRRVq prts p)->Prop)->Prop) 
        (FF:Filter F) :
    Filter (LpRRVq_filter_to_LpRRV_filter F).
  Proof.
    destruct FF.
    unfold LpRRVq_filter_to_LpRRV_filter, LpRRV_toLpRRVq_set.
    constructor; intros.
    - eapply filter_imp; try eapply filter_true; intros.
      destruct (Quot_inv x); subst.
      eauto.
    - generalize (filter_and _ _ H H0); intros HH.
      eapply filter_imp; try eapply HH; intros ? [??].
      intros; subst.
      specialize (H1 _ (eq_refl _)).
      specialize (H2 _ (eq_refl _)).
      tauto.
    - eapply filter_imp; try eapply H0; simpl; intros.
      subst.
      apply H.
      now apply H1.
  Qed.

  Lemma LpRRVq_filter_to_LpRRV_filter_proper (F:((LpRRVq prts p)->Prop)->Prop) 
        (PF:ProperFilter F) :
    ProperFilter (LpRRVq_filter_to_LpRRV_filter F).
  Proof.
    destruct PF.
    constructor.
    - intros.
      destruct (filter_ex (LpRRV_toLpRRVq_set P) H).
      destruct (Quot_inv x); subst.
      exists x0.
      unfold LpRRV_toLpRRVq_set in *.
      now apply H0.
    - now apply LpRRVq_filter_to_LpRRV_filter_filter.
  Qed.

  Lemma rvpower2 (x:Ts->R) {posx:PositiveRandomVariable x} : rv_eq (rvpower x (const 2)) (rvsqr x).
  Proof.
    intros ?.
    unfold rvpower, rvsqr, const.
    apply power2_sqr.
    apply posx.
  Qed.
          
  Lemma LpRRVq_filter_to_LpRRV_filter_cauchy
        (F : (LpRRVq_UniformSpace prts p pbig -> Prop) -> Prop)
    (PF:ProperFilter F)
    (cF:cauchy F) : 
    @cauchy (LpRRV_UniformSpace prts pbig) (LpRRVq_filter_to_LpRRV_filter F).
  Proof.
    unfold cauchy ; intros.
    destruct (cF eps) as [??]; simpl in *.
    unfold LpRRVq_filter_to_LpRRV_filter, LpRRV_toLpRRVq_set.
    destruct (Quot_inv x); subst.
    exists x0.
    eapply filter_imp; try eapply H; intros; subst.
    repeat red.
    do 2 red in H0.
    simpl in H0.
    rewrite LpRRVq_ballE in H0.
    apply H0.
  Qed.

  Definition LpRRVq_lim_with_conditions2 (F : (LpRRVq_UniformSpace prts p pbig -> Prop) -> Prop)
    (PF:ProperFilter F)
    (cF:cauchy F) : LpRRVq prts p.
    Proof.
      simpl in F.
      pose (LpRRVq_filter_to_LpRRV_filter F).
      generalize (LpRRVq_lim_with_conditions P); intros.
      specialize (X (LpRRVq_filter_to_LpRRV_filter_proper F PF)).
      specialize (X (LpRRVq_filter_to_LpRRV_filter_cauchy F PF cF)).
      exact X.
  Defined.

  Definition LpRRVq_lim (lim : ((LpRRVq prts p -> Prop) -> Prop)) : LpRRVq prts p.
  Proof.
    destruct (excluded_middle_informative (ProperFilter lim)).
    - destruct (excluded_middle_informative (cauchy (T:=LpRRVq_UniformSpace prts p pbig) lim)).
      + exact (LpRRVq_lim_with_conditions2 _ p0 c).
      + exact (LpRRVq_zero prts).
    - exact (LpRRVq_zero prts).
  Defined.

  Lemma LpRRVq_lim_complete (F : (LpRRVq_UniformSpace prts p pbig -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (LpRRVq_ball prts pbig (LpRRVq_lim F) eps).
  Proof.
    intros.
    unfold LpRRVq_lim; simpl.
    match_destr; [| tauto].
    match_destr; [| tauto].
    generalize (L2RRV_lim_complete (LpRRVq_filter_to_LpRRV_filter F)); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_proper F H); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_cauchy F H H0); intros.
    specialize (H1 H2 H3 eps).
    unfold LpRRV_lim in H1; simpl in H1.
    match_destr_in H1; [|tauto].
    match_destr_in H1; [|tauto].
    unfold Hierarchy.ball, UniformSpace.ball in H1; simpl in H1.
    unfold LpRRVq_lim_with_conditions2.
    rewrite  LpRRVq_lim_with_conditionsE.
    rewrite (proof_irrelevance _ _ p1).
    rewrite (proof_irrelevance _ _ c0).
    unfold LpRRVq_filter_to_LpRRV_filter in *.
    eapply filter_imp; try eapply H1.
    intros x; simpl in *.

    unfold LpRRV_toLpRRVq_set; simpl; intros HH.
    unfold ball, Hnorm, minus, plus, opp, inner; simpl.
    destruct (Quot_inv x); subst.
    rewrite LpRRVq_ballE.
    specialize (HH _ (eq_refl _)).
    unfold LpRRVball in *.
    eapply Rle_lt_trans; try eapply HH.
    unfold LpRRVnorm.
    apply Rle_power_l; [| split].
    - simpl.
      left; apply Rinv_pos; lra.
    - apply FiniteExpectation_pos.
      typeclasses eauto.
    - apply FiniteExpectation_le.
      reflexivity.
  Qed.

    
  Lemma L2RRVq_lim_complete' (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (LpRRVq_lim F) eps).
  Proof.
    intros.
    unfold L2RRVq_lim; simpl.
    match_destr; [| tauto].
    match_destr; [| tauto].
    generalize (L2RRV_lim_complete (LpRRVq_filter_to_LpRRV_filter F)); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_proper F H); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_cauchy F H H0); intros.
    specialize (H1 H2 H3 eps).
    unfold L2RRV_lim in H1; simpl in H1.
    match_destr_in H1; [|tauto].
    match_destr_in H1; [|tauto].
    unfold Hierarchy.ball, UniformSpace.ball in H1; simpl in H1.
    unfold L2RRVq_lim_with_conditions2.
    rewrite  L2RRVq_lim_with_conditionsE.
    rewrite (proof_irrelevance _ _ p0).
    rewrite (proof_irrelevance _ _ c0).
    unfold LpRRVq_filter_to_LpRRV_filter in *.
    eapply filter_imp; try eapply H1.
    intros x; simpl in *.

    unfold LpRRV_toLpRRVq_set; simpl; intros HH.
    unfold ball, Hnorm, minus, plus, opp, inner; simpl.
    LpRRVq_simpl.
    rewrite L2RRVq_innerE.
    specialize (HH _ (eq_refl _)).
    simpl.
    eapply Rle_lt_trans; try eapply HH.
    unfold LpRRVnorm.
    rewrite power_sqrt.
    - apply sqrt_le_1_alt.
      apply FiniteExpectation_le.
      rewrite rvpower2; try typeclasses eauto.
      intros ?.
      rv_unfold; simpl.
      rewrite <- Rsqr_abs.
      unfold Rsqr.
      rv_unfold.
      lra.
    - apply FiniteExpectation_pos.
      typeclasses eauto.
  Qed.

  Definition L2RRVq_Hilbert_mixin : Hilbert.mixin_of (L2RRVq_PreHilbert prts)
    := Hilbert.Mixin (L2RRVq_PreHilbert prts) L2RRVq_lim L2RRVq_lim_complete.

  Canonical L2RRVq_Hilbert :=
    Hilbert.Pack (LpRRVq prts 2) (Hilbert.Class _ _ L2RRVq_Hilbert_mixin) (LpRRVq prts 2).

End L2_complete.
