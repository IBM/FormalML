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

      rewrite (Expectation_pos_pofrf _).
      generalize (Finite_NonnegExpectation_le (rvabs (rvmult x y))
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
      + generalize (NonnegExpectation_sum (rvsqr x) (rvsqr y))
        ; intros HH3.
        erewrite NonnegExpectation_pf_irrel in HH3.
        rewrite HH3.

        rewrite rvpower_abs2_unfold in eqq1, eqq2.
        
        rewrite (Expectation_pos_pofrf _) in eqq1.
        rewrite (Expectation_pos_pofrf _) in eqq2.
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
    assert (eqq:almostR2 prts eq (rvmult x1 y1) (rvmult x2 y2)).
    - LpRRV_simpl.
      now apply almostR2_eq_mult_proper.
    - eapply FiniteExpectation_proper_almostR2; try eapply eqq
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
    assert (NonnegativeFunction (rvabs (rvmult rv_X1 rv_X2))) by apply nnfabs.
    generalize (Expectation_pos_pofrf (rvabs (rvmult rv_X1 rv_X2))); intros.
    generalize (rvprod_abs1_bound rv_X1 rv_X2); intros.
    assert (NonnegativeFunction (rvplus (rvsqr rv_X1) (rvsqr rv_X2)))
      by (apply rvplus_nnf; apply nnfsqr).
    generalize (Finite_NonnegExpectation_le _ _ H H2 H1); intros.
    unfold IsLp, IsFiniteExpectation in *.
    rewrite (Expectation_pos_pofrf _) in l21.
    rewrite (Expectation_pos_pofrf _)  in l22.    
    match_case_in l21
    ; [intros ? eqq1 | intros eqq1..]
    ; rewrite eqq1 in l21
    ; try contradiction.
    match_case_in l22
    ; [intros ? eqq2 | intros eqq2..]
    ; rewrite eqq2 in l22
    ; try contradiction.
    assert (NonnegativeFunction (rvsqr rv_X1)) by apply nnfsqr.
    assert (NonnegativeFunction (rvsqr rv_X2)) by apply nnfsqr.
    generalize (NonnegExpectation_sum (rvsqr rv_X1) (rvsqr rv_X2)); intros.
    cut_to H3.
    - rewrite Expectation_pos_pofrf with (nnf := H).
      now rewrite <- H3.
    - erewrite NonnegExpectation_pf_irrel in H6.
      rewrite H6.
      rewrite (NonnegExpectation_ext _ _ (rvpower_abs2_unfold _)) in eqq1.
      rewrite (NonnegExpectation_ext _ _  (rvpower_abs2_unfold _)) in eqq2.
      erewrite NonnegExpectation_pf_irrel in eqq1.
      rewrite eqq1.
      erewrite NonnegExpectation_pf_irrel in eqq2.
      rewrite eqq2.
      simpl.
      now unfold is_finite.
  Qed.

  Lemma conv_l2_prob_le_div
        (eps : posreal) 
        (X : Ts -> R) 
        (rv : RandomVariable dom borel_sa X)
        (pofrf: NonnegativeFunction X) :
  Rbar_le (ps_P (event_ge dom X eps))
          (Rbar_div (NonnegExpectation (rvsqr X)) 
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
    is_finite (NonnegExpectation (rvsqr (rvabs Xn))) ->
    ps_P (event_ge dom (rvabs Xn) eps) <=
    (NonnegExpectation (rvsqr (rvabs Xn))) / (Rsqr eps).
    Proof.
      assert (RandomVariable dom borel_sa (rvabs Xn)).
      - now apply rvabs_rv.
      - assert (NonnegativeFunction (rvabs Xn)).
        now apply nnfabs.
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
    is_finite (NonnegExpectation (rvsqr (rvabs (rvminus X Xn)))) ->
    ps_P (event_ge dom (rvabs (rvminus X Xn)) eps) <=
    (NonnegExpectation (rvsqr (rvabs (rvminus X Xn)))) / (Rsqr eps).
    Proof.
      intros.
      apply conv_l2_prob_le1; trivial.
    Qed.

  Lemma conv_l1_prob_le 
        (eps : posreal) 
        (X: Ts -> R)
        {rvx : RandomVariable dom borel_sa X}:
    is_finite (NonnegExpectation (rvabs X)) ->
    ps_P (event_ge dom (rvabs X) eps) <=
    (NonnegExpectation (rvabs X)) / eps.
    Proof.
      assert (RandomVariable dom borel_sa (rvabs X)).
      - now apply rvabs_rv.
      - assert (NonnegativeFunction (rvabs X)).
        now apply nnfabs.
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
    is_finite (NonnegExpectation (rvabs (rvminus X Xn))) ->
    ps_P (event_ge dom (rvabs (rvminus X Xn)) eps) <=
    (NonnegExpectation (rvabs (rvminus X Xn))) / eps.
    Proof.
      apply conv_l1_prob_le.
    Qed.

  Lemma conv_l2_prob1 
        (eps : posreal) 
        (Xn: nat -> Ts -> R)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) :
    (forall n, is_finite (NonnegExpectation (rvsqr (rvabs (Xn n))))) ->
    is_lim_seq (fun n => NonnegExpectation (rvsqr (rvabs (Xn n)))) 0 ->
    is_lim_seq (fun n => ps_P (event_ge dom (rvabs (Xn n)) eps)) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                    (w := (fun n => (NonnegExpectation (rvsqr (rvabs (Xn n)))) / (Rsqr eps))).
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
    (forall n, is_finite (NonnegExpectation (rvsqr (rvabs (rvminus X (Xn n)))))) ->
    is_lim_seq (fun n => NonnegExpectation (rvsqr (rvabs (rvminus X (Xn n))))) 0 ->
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
    (forall n, is_finite (NonnegExpectation (rvabs (rvminus X (Xn n))))) ->
    is_lim_seq (fun n => NonnegExpectation (rvabs (rvminus X (Xn n)))) 0 ->
    is_lim_seq (fun n => ps_P (event_ge dom (rvabs (rvminus X (Xn n))) eps)) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                    (w := (fun n => (NonnegExpectation (rvabs (rvminus X (Xn n)))) / eps)).
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
        unfold NonnegativeFunction, rvabs, rvsqr; intros.
        apply Rle_0_sqr.
      - apply is_lim_seq_le_le_loc with 
            (u := fun _ => 0) 
            (w := (fun n => Rsqrt (mknonnegreal (FiniteExpectation prts (rvsqr (rvabs (Xn n)))) (H0 n)))).
        + exists (0%nat); intros.
          assert (0 <= FiniteExpectation prts (rvabs (Xn n))).
          * apply FiniteExpectation_pos.
            unfold rvabs, NonnegativeFunction; intros.
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

  Lemma L2RRVq_ball_ball (x : LpRRVq prts 2) eps (y : LpRRVq prts 2) :
    ball x eps y <-> LpRRVq_ball prts big2 x eps y.
  Proof.
    unfold ball.
    rewrite L2RRVq_norm_norm.
    LpRRVq_simpl.
    rewrite LpRRVq_ballE.
    unfold minus, plus, opp; simpl.
    autorewrite with quot.
    rewrite LpRRVq_normE.
    unfold LpRRVball.
    now rewrite LpRRVminus_plus.
  Qed.

  Lemma Hnorm_minus_opp {T:PreHilbert} (a b:T) :
    (Hnorm (minus a b) = Hnorm (minus b a)).
  Proof.
    rewrite <- (norm_opp (minus a b)).
    rewrite opp_minus.
    reflexivity.
  Qed.

  Lemma hball_pre_uniform_eq x eps :
    @Hierarchy.ball (@PreHilbert_UniformSpace L2RRVq_PreHilbert) x (pos eps)
    = @Hierarchy.ball (LpRRVq_UniformSpace prts 2 big2) x (pos eps).
  Proof.
    unfold Hierarchy.ball.
    apply functional_extensionality; simpl; intros.
    unfold ball.
    rewrite L2RRVq_norm_norm.
    destruct (Quot_inv x); subst.
    destruct (Quot_inv x0); subst.
    rewrite LpRRVq_ballE.
    unfold minus, plus, opp; simpl.
    autorewrite with quot.
    rewrite LpRRVq_normE.
    unfold LpRRVball.
    erewrite LpRRV_norm_proper; [reflexivity |].
    rewrite LpRRVminus_plus.
    reflexivity.
  Qed.

  Lemma hball_pre_uniform (F : (PreHilbert_UniformSpace -> Prop) -> Prop) x eps :
    F (@Hierarchy.ball (@PreHilbert_UniformSpace L2RRVq_PreHilbert) x (pos eps)) ->
    F (@Hierarchy.ball (LpRRVq_UniformSpace prts 2 big2) x (pos eps)).
  Proof.
    now rewrite hball_pre_uniform_eq.
  Qed.
  
  Lemma cauchy_pre_uniform (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    @cauchy (@PreHilbert_UniformSpace L2RRVq_PreHilbert) F ->
    @cauchy (LpRRVq_UniformSpace prts 2 big2) F.
  Proof.
    intros HH eps.
    destruct (HH eps) as [x HH2].
    exists x.
    now apply hball_pre_uniform.
  Qed.

  Lemma L2RRVq_lim_complete (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (LpRRVq_lim prts big2 F) eps).
  Proof.
    intros.
    generalize (LpRRVq_lim_complete prts big2 F H)
    ; intros HH.
    cut_to HH.
    - specialize (HH eps).
      replace (LpRRVq_ball prts big2 (LpRRVq_lim prts big2 F) eps) with
          (ball (LpRRVq_lim prts big2 (fun x : LpRRVq prts 2 -> Prop => F x)) eps) in HH; trivial.
      apply functional_extensionality; simpl; intros.
      unfold ball; simpl.
      rewrite L2RRVq_norm_norm.
      replace (fun x : LpRRVq prts 2 -> Prop => F x) with F by trivial.

      destruct (Quot_inv (LpRRVq_lim prts big2 F)) as [l leqq].
      rewrite leqq.
      destruct (Quot_inv x); subst; simpl in *.
      unfold minus, plus, opp; simpl.
      autorewrite with quot.
      rewrite LpRRVq_ballE, LpRRVq_normE.
      unfold LpRRVball.
      erewrite LpRRV_norm_proper; [reflexivity |].
      rewrite LpRRVminus_plus.
      reflexivity.
    - now apply cauchy_pre_uniform.
  Qed.
  
  Definition L2RRVq_Hilbert_mixin : Hilbert.mixin_of (L2RRVq_PreHilbert)
    := Hilbert.Mixin (L2RRVq_PreHilbert) (LpRRVq_lim prts big2) L2RRVq_lim_complete.

  Canonical L2RRVq_Hilbert :=
    Hilbert.Pack (LpRRVq prts 2) (Hilbert.Class _ _ L2RRVq_Hilbert_mixin) (LpRRVq prts 2).

End L2.
