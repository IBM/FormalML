Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Classical.
Require Import FunctionalExtensionality.

Require Import hilbert.

Require Import BorelSigmaAlgebra.
Require Import ProbSpace.
Require Import RandomVariable.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section fe.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).


  Class IsFiniteExpectation (rv_X:Ts->R) 
    := is_finite_expectation :
         match Expectation rv_X with
         | Some (Finite _) => True
         | _ => False
         end.

  Lemma IsFiniteExpectation_Finite (rv_X:Ts->R)
        {isfe:IsFiniteExpectation rv_X} :
    { x : R | Expectation rv_X = Some (Finite x)}.
  Proof.
    red in isfe.
    match_destr_in isfe; try contradiction.
    destruct r; try contradiction.
    eauto.
  Qed.

  Definition FiniteExpectation (rv_X:Ts->R)
             {isfe:IsFiniteExpectation rv_X} : R
    := proj1_sig (IsFiniteExpectation_Finite rv_X).

  Ltac simpl_finite
    := repeat match goal with
              | [|- context [proj1_sig ?x]] => destruct x; simpl
              | [H: context [proj1_sig ?x] |- _] => destruct x; simpl in H
              end.

  Lemma FiniteExpectation_Expectation (rv_X:Ts->R)
        {isfe:IsFiniteExpectation rv_X} : 
    Expectation rv_X = Some (Finite (FiniteExpectation rv_X)).
  Proof.
    unfold IsFiniteExpectation in isfe.
    unfold FiniteExpectation.
    now simpl_finite.
  Qed.

  Instance Expectation_IsFiniteExpectation (rv_X:Ts->R) n :
    Expectation rv_X = Some (Finite n) ->
    IsFiniteExpectation rv_X.
  Proof.
    intros HH.
    red.
    now rewrite HH.
  Qed.
  

  Lemma Expectation_FiniteExpectation (rv_X:Ts->R) n
        {isfe:IsFiniteExpectation rv_X} : 
    Expectation rv_X = Some (Finite n) ->
    FiniteExpectation rv_X = n.
  
  Proof.
    intros HH.
    unfold IsFiniteExpectation in isfe.
    unfold FiniteExpectation.
    destruct (IsFiniteExpectation_Finite rv_X); simpl.
    congruence.
  Qed.

  Lemma Expectation_FiniteExpectation' (rv_X:Ts->R) n 
        (eqq:Expectation rv_X = Some (Finite n)) :
    @FiniteExpectation rv_X (Expectation_IsFiniteExpectation rv_X n eqq) = n.
  Proof.
    unfold FiniteExpectation.
    destruct (IsFiniteExpectation_Finite rv_X); simpl.
    congruence.
  Qed.

  Lemma FiniteExpectation_pf_irrel rv_X
        {isfe1:IsFiniteExpectation rv_X}
        {isfe2:IsFiniteExpectation rv_X} :
    @FiniteExpectation rv_X isfe1 = @FiniteExpectation rv_X isfe2.
  Proof.
    unfold FiniteExpectation in *.
    simpl_finite.
    congruence.
  Qed.

  Lemma FiniteExpectation_ext rv_X1 rv_X2
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X2} :
    rv_eq rv_X1 rv_X2 ->
    @FiniteExpectation rv_X1 isfe1 = @FiniteExpectation rv_X2 isfe2.
  Proof.
    unfold FiniteExpectation.
    intros eqq.
    simpl_finite.
    rewrite eqq in e.
    congruence.
  Qed.

  Global Instance IsFiniteExpectation_proper
    : Proper (rv_eq ==> iff) IsFiniteExpectation.
  Proof.
    unfold IsFiniteExpectation.
    intros x y eqq.
    now rewrite eqq.
  Qed.

  Global Instance IsFiniteExpectation_const c : IsFiniteExpectation (const c).
  Proof.
    red.
    now rewrite Expectation_const.
  Qed.

  Lemma FiniteExpectation_const c : FiniteExpectation (const c) = c.
  Proof.
    unfold FiniteExpectation; simpl_finite.
    rewrite Expectation_const in e.
    congruence.
  Qed.

  Hint Rewrite FiniteExpectation_const : prob.

  Global Instance IsFiniteExpectation_plus 
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2} 
         {isfe1:IsFiniteExpectation rv_X1}
         {isfe2:IsFiniteExpectation rv_X2} :
    IsFiniteExpectation (rvplus rv_X1 rv_X2).
  Proof.
    red.
    red in isfe1, isfe2.
    generalize (Expectation_sum_finite rv_X1 rv_X2).
    repeat match_destr_in isfe1; try contradiction.
    repeat match_destr_in isfe2; try contradiction.
    intros HH.
    now rewrite (HH _ _ (eq_refl _) (eq_refl _)).
  Qed.

  Lemma FiniteExpectation_plus
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable prts borel_sa rv_X1}
        {rv2 : RandomVariable prts borel_sa rv_X2} 
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X2} :
    FiniteExpectation (rvplus rv_X1 rv_X2) =
    FiniteExpectation rv_X1 + FiniteExpectation rv_X2.
  Proof.
    destruct (IsFiniteExpectation_Finite rv_X1) as [r1 e1].
    destruct (IsFiniteExpectation_Finite rv_X2) as [r2 e2].
    generalize (Expectation_sum_finite rv_X1 rv_X2 r1 r2 e1 e2); trivial
    ; intros HH.
    erewrite FiniteExpectation_Expectation in e1,e2,HH.
    invcs HH.
    invcs e1.
    invcs e2.
    rewrite H0, H1, H2.
    trivial.
  Qed.

  Hint Rewrite FiniteExpectation_plus : prob.

  Global Instance IsFiniteExpectation_scale (c:R) (rv_X:Ts->R)
         {isfe:IsFiniteExpectation rv_X} :
    IsFiniteExpectation (rvscale c rv_X).
  Proof.
    unfold IsFiniteExpectation in *.
    destruct (Req_EM_T c 0).
    - subst.
      rewrite (Expectation_ext (rv_X2:=(const 0))).
      + rewrite Expectation_const; trivial.
      + intros ?; unfold rvscale, const.
        lra.
    - rewrite (Expectation_scale c rv_X n).
      match_destr_in isfe.
      match_destr_in isfe; try contradiction.
  Qed.

  Lemma IsFiniteExpectation_scale_inv c rv_X 
        {isfe:IsFiniteExpectation (rvscale c rv_X)} :
    c <> 0 ->
    IsFiniteExpectation rv_X.
  Proof.
    intros.
    eapply IsFiniteExpectation_proper
    ; try eapply (IsFiniteExpectation_scale (Rinv c))
    ; try eapply isfe.
    intros ?.
    unfold rvscale.
    now field.
  Qed.
  
  Lemma FiniteExpectation_scale c  rv_X 
        {isfe:IsFiniteExpectation rv_X} :
    FiniteExpectation (rvscale c rv_X) = c * FiniteExpectation rv_X.
  Proof.
    unfold IsFiniteExpectation in *.
    destruct (Req_EM_T c 0).
    - subst.
      rewrite (FiniteExpectation_ext (rvscale 0 rv_X) (const 0)).
      + autorewrite with prob.
        lra.
      + intros ?; unfold rvscale, const.
        lra.
    - unfold FiniteExpectation; simpl_finite.
      rewrite (Expectation_scale c rv_X n) in e.
      repeat match_destr_in isfe.
      invcs e.
      congruence.
  Qed.

  Hint Rewrite FiniteExpectation_scale : prob.

  Global Instance IsFiniteExpectation_opp rv_X 
         {isfe:IsFiniteExpectation rv_X} :
    IsFiniteExpectation (rvopp rv_X).
  Proof.
    now apply IsFiniteExpectation_scale.
  Qed.

  Lemma IsFiniteExpectation_opp_inv rv_X 
        {isfe:IsFiniteExpectation (rvopp rv_X)} :
    IsFiniteExpectation rv_X.
  Proof.
    apply (IsFiniteExpectation_scale_inv (-1))
    ; trivial.
    lra.
  Qed.

  Lemma FiniteExpectation_opp rv_X 
        {isfe:IsFiniteExpectation rv_X} :
    FiniteExpectation (rvopp rv_X) = -1 * FiniteExpectation rv_X.
  Proof.
    unfold rvopp.
    generalize (FiniteExpectation_scale (-1) rv_X).
    now erewrite FiniteExpectation_pf_irrel.
  Qed.

  Hint Rewrite FiniteExpectation_opp : prob.

  
  Global Instance IsFiniteExpectation_minus
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2} 
         {isfe1:IsFiniteExpectation rv_X1}
         {isfe2:IsFiniteExpectation rv_X2} :
    IsFiniteExpectation (rvminus rv_X1 rv_X2).
  Proof.
    unfold rvminus.
    typeclasses eauto.
  Qed.

  Lemma FiniteExpectation_minus
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable prts borel_sa rv_X1}
        {rv2 : RandomVariable prts borel_sa rv_X2} 
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X2} :
    FiniteExpectation (rvminus rv_X1 rv_X2) =
    FiniteExpectation rv_X1 - FiniteExpectation rv_X2.
  Proof.
    unfold rvminus.
    erewrite FiniteExpectation_pf_irrel at 1.
    rewrite FiniteExpectation_plus.
    rewrite FiniteExpectation_opp.
    lra.
  Qed.

  Hint Rewrite FiniteExpectation_plus : prob.

  Lemma pos_fun_part_proper_almost x y 
        {rvx:RandomVariable prts borel_sa x}
        {rvy:RandomVariable prts borel_sa y} :
    rv_almost_eq prts x y ->
    rv_almost_eq prts (fun x0 => nonneg (pos_fun_part x x0)) (fun x0 => nonneg (pos_fun_part y x0)).
  Proof.
    unfold pos_fun_part; simpl.
    unfold rv_almost_eq; intros eqq.
    apply Rle_antisym; trivial.
    - apply ps_le1.
      apply (Hsigma_borel_eq_pf prts)
      ; now apply positive_part_rv.
    - rewrite <- eqq.
      apply ps_sub.
      + now apply (Hsigma_borel_eq_pf prts).
      + apply (Hsigma_borel_eq_pf prts)
        ; now apply positive_part_rv.
      + intros a; intros eqq2.
        congruence.
  Qed.

  Lemma neg_fun_part_proper_almost x y 
        {rvx:RandomVariable prts borel_sa x}
        {rvy:RandomVariable prts borel_sa y} :
    rv_almost_eq prts x y ->
    rv_almost_eq prts (fun x0 => nonneg (neg_fun_part x x0)) (fun x0 => nonneg (neg_fun_part y x0)).
  Proof.
    unfold neg_fun_part; simpl.
    unfold rv_almost_eq; intros eqq.
    apply Rle_antisym; trivial.
    - apply ps_le1.
      apply (Hsigma_borel_eq_pf prts)
      ; now apply negative_part_rv.
    - rewrite <- eqq.
      apply ps_sub.
      + now apply (Hsigma_borel_eq_pf prts).
      + apply (Hsigma_borel_eq_pf prts)
        ; now apply negative_part_rv.
      + intros a; intros eqq2.
        congruence.
  Qed.

  Lemma list_sum0_is0 l :
    Forall (fun x => x = 0) l ->
    RealAdd.list_sum l = 0%R.
  Proof.
    induction l; simpl; trivial.
    inversion 1; subst.
    rewrite IHl; trivial.
    lra.
  Qed.

  Lemma SimplePosExpectation_pos_zero x
        {rvx:RandomVariable prts borel_sa x} 
        {xsrv:SimpleRandomVariable x} :
    rv_almost_eq prts x (const 0) ->
    SimpleExpectation x = 0.
  Proof.
    intros eqq.
    unfold SimpleExpectation.
    apply list_sum0_is0.
    apply List.Forall_forall.
    intros ? inn.
    apply in_map_iff in inn.
    destruct inn as [?[??]].
    red in eqq.
    unfold const in eqq.
    destruct (Req_EM_T x1 0).
    - subst.
      lra.
    - replace (ps_P (fun omega : Ts => x omega = x1)) with 0 in H; [lra |].
      apply Rle_antisym.
      + apply ps_pos.
        eapply Hsigma_borel_eq_pf; eauto.
        apply rvconst.
      +
        assert (event_sub  (fun x0 : Ts => x x0 = 0) (event_complement (fun omega : Ts => x omega = x1))).
        {
          unfold event_complement.
          red; intros.
          lra.
        }
        apply (ps_sub prts) in H1.
        * rewrite ps_complement in H1.
          -- rewrite eqq in H1.
             lra.
          -- eapply Hsigma_borel_eq_pf; eauto.
             apply rvconst.
        * eapply Hsigma_borel_eq_pf; eauto.
          apply rvconst.
        * apply sa_complement.
          eapply Hsigma_borel_eq_pf; eauto.
          apply rvconst.
  Qed.

  Lemma Expectation_simple_proper_almost x y
        {rvx:RandomVariable prts borel_sa x}
        {rvy:RandomVariable prts borel_sa y} 
        {xsrv:SimpleRandomVariable x}
        {ysrv:SimpleRandomVariable y} :
    rv_almost_eq prts x y ->
    SimpleExpectation x = SimpleExpectation y.
  Proof.
    intros.
    generalize (SimplePosExpectation_pos_zero (rvminus x y))
    ; intros HH.
    cut_to HH.
    - unfold rvminus in HH.
      erewrite SimpleExpectation_pf_irrel in HH.
      rewrite <- sumSimpleExpectation with (srv1:=xsrv) (srv2:=srvopp) in HH; trivial.
      + unfold rvopp in HH.
        erewrite (@SimpleExpectation_pf_irrel _ _ _ (rvscale (-1) y)) in HH.
        rewrite <- scaleSimpleExpectation with (srv:=ysrv) in HH.
        lra.
      + typeclasses eauto.
    - clear HH.
      unfold rv_almost_eq in *.
      unfold const.
      rewrite ps_proper; try eapply H.
      intros a.
      unfold rvminus, rvplus, rvopp, rvscale.
      split; intros; lra.
  Qed.

  Lemma Expectation_posRV_almost_0 x 
        {rvx:RandomVariable prts borel_sa x}
        {prv:PositiveRandomVariable x} :
    rv_almost_eq prts x (const 0) ->
    Expectation_posRV x = 0.
  Proof.
    intros.
    unfold Expectation_posRV, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    destruct i as [xub xlub].
    unfold is_ub_Rbar in xub.
    specialize (xub 0).
    specialize (xlub 0).
    unfold is_ub_Rbar in xlub.
    cut_to xub.
    - cut_to xlub.
      + now apply Rbar_le_antisym.
      + intros.
        unfold BoundedPositiveRandomVariable in H0.
        destruct H0 as [? [? [? [[? ?] ?]]]].
        unfold rv_almost_eq in H.
        assert (rv_almost_eq prts x2 (const 0)).
        * unfold rv_almost_eq.
          assert (event_sub (fun x0 : Ts => x x0 = const 0 x0)
                            (fun x5 : Ts => x2 x5 = const 0 x5)).
          -- unfold event_sub; intros.
             unfold const in H3.
             unfold const.
             unfold RealRandomVariable_le in H1.
             specialize (H1 x5).
             unfold PositiveRandomVariable in H0.
             specialize (H0 x5).
             lra.
          -- unfold RandomVariable in *.
             rewrite <- borel_sa_preimage2 in rvx.
             rewrite <- borel_sa_preimage2 in x3.
             assert (sa_sigma (fun x5 : Ts => x2 x5 = const 0 x5)).
             ++ unfold const.
                now apply sa_le_pt.
             ++ assert (sa_sigma (fun x5 : Ts => x x5 = const 0 x5)).    
                ** unfold const.
                   now apply sa_le_pt.
                ** apply (ps_sub prts) in H3; trivial.
                   generalize (ps_le1 prts (fun x5 : Ts => x2 x5 = const 0 x5) H4); intros.
                   lra.
        * generalize (SimplePosExpectation_pos_zero x2 H3); intros.
          rewrite H4 in H2.
          rewrite <- H2.
          simpl; lra.
    - exists (const 0); exists (rvconst 0); exists (srvconst 0).
      split.
      + unfold BoundedPositiveRandomVariable.
        split.
        * apply prvconst; lra.
        * unfold RealRandomVariable_le, const.
          apply prv.
      + apply SimpleExpectation_const.
  Qed.

  Lemma Expectation_almost_0 x 
        {rvx:RandomVariable prts borel_sa x} :
    rv_almost_eq prts x (const 0) ->
    Expectation x = Some (Finite 0).
  Proof.
    unfold rv_almost_eq.
    intros.
    assert (RandomVariable prts borel_sa (pos_fun_part x)).
    now apply positive_part_rv.
    assert (RandomVariable prts borel_sa (neg_fun_part x)).
    now apply negative_part_rv.
    unfold RandomVariable in rvx.
    rewrite <- borel_sa_preimage2 in rvx.
    assert (sa_sigma (fun x0 : Ts => nonneg(pos_fun_part x x0) = 0)).
    apply sa_le_pt.
    now apply Relu_measurable.
    assert (sa_sigma (fun x0 : Ts => nonneg(neg_fun_part x x0) = 0)).
    apply sa_le_pt.
    apply Relu_measurable.
    now apply Ropp_measurable.
    unfold Expectation.
    assert (rv_almost_eq prts (fun omega => nonneg(pos_fun_part x omega)) (const 0)).
    unfold rv_almost_eq.
    assert (event_sub (fun x0 : Ts => x x0 = const 0 x0)
                      (fun x0 : Ts => nonneg(pos_fun_part x x0) = const 0 x0)).
    intro x0.
    unfold pos_fun_part, const; simpl.
    unfold Rmax; match_destr.
    unfold const in *.
    apply (ps_sub prts) in H4; trivial.
    generalize (ps_le1 prts (fun x0 : Ts => nonneg(pos_fun_part x x0) = const 0 x0)); intros.
    unfold const in H5.
    specialize (H5 H2).
    lra.
    now apply sa_le_pt.
    assert (rv_almost_eq prts (fun omega => nonneg(neg_fun_part x omega)) (const 0)).
    assert (event_sub (fun x0 : Ts => x x0 = const 0 x0)
                      (fun x0 : Ts => nonneg(neg_fun_part x x0) = const 0 x0)
           ).
    intro x0.
    unfold neg_fun_part, const; simpl.
    unfold Rmax; match_destr.
    lra.
    unfold rv_almost_eq.
    unfold const in *.
    apply (ps_sub prts) in H5; trivial.
    generalize (ps_le1 prts (fun x0 : Ts => nonneg(neg_fun_part x x0) = const 0 x0)); intros.
    unfold const in H6.
    specialize (H6 H3).
    lra.
    now apply sa_le_pt.
    rewrite (Expectation_posRV_almost_0 (fun x0 : Ts => pos_fun_part x x0) H4).
    rewrite (Expectation_posRV_almost_0 (fun x0 : Ts => neg_fun_part x x0) H5).
    simpl; f_equal; f_equal; lra.
  Qed.

  Lemma Expectation_finite_proper_almost rv_X1 rv_X2
        {rrv1:RandomVariable prts borel_sa rv_X1}
        {rrv2:RandomVariable prts borel_sa rv_X2}
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X2}
    :
      rv_almost_eq prts rv_X1 rv_X2 ->
      FiniteExpectation rv_X1 = FiniteExpectation rv_X2.

  Proof.
    intros.
    generalize (Expectation_almost_0 (rvminus rv_X1 rv_X2))
    ; intros HH.
    cut_to HH.
    - apply (Expectation_FiniteExpectation _ _ (isfe:=IsFiniteExpectation_minus _ _)) in HH.
      rewrite FiniteExpectation_minus in HH.
      lra.
    - unfold rv_almost_eq in *.
      unfold const in *.
      assert (event_equiv (fun x0 : Ts => rvminus rv_X1 rv_X2 x0 = 0) (fun x0 : Ts => rv_X1 x0 = rv_X2 x0)).
      intros a.
      unfold rvminus, rvplus, rvopp, rvscale.
      split; intros; lra.
      now rewrite H0.
  Qed.

  Lemma FiniteExpectation_le rv_X1 rv_X2
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X2}
    :
      RealRandomVariable_le rv_X1 rv_X2 ->
      FiniteExpectation rv_X1 <= FiniteExpectation rv_X2.
  Proof.
    intros.
    unfold FiniteExpectation.
    simpl_finite.
    apply (Expectation_le rv_X1 rv_X2 _ _ e e0) in H.
    now simpl in H.
  Qed.

  Lemma RealRandomVariable_le_pos rv_X1 rv_X2 :
    RealRandomVariable_le rv_X1 rv_X2 ->
    RealRandomVariable_le (fun x : Ts => pos_fun_part rv_X1 x) (fun x : Ts => pos_fun_part rv_X2 x).
  Proof.
    unfold RealRandomVariable_le.
    intros le12 a.
    unfold pos_fun_part; simpl.
    now apply Rle_max_compat_r.
  Qed.

  Lemma RealRandomVariable_le_neg rv_X1 rv_X2 :
    RealRandomVariable_le rv_X1 rv_X2 ->
    RealRandomVariable_le (fun x : Ts => neg_fun_part rv_X2 x) (fun x : Ts => neg_fun_part rv_X1 x).
  Proof.
    unfold RealRandomVariable_le.
    intros le12 a.
    unfold pos_fun_part; simpl.
    replace 0 with (- 0) by lra.
    repeat rewrite Rmax_opp_Rmin.
    apply Ropp_le_contravar.
    now apply Rle_min_compat_r.
  Qed.

  Lemma IsFiniteExpectation_bounded rv_X1 rv_X2 rv_X3
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X3}
    :
      RealRandomVariable_le rv_X1 rv_X2 ->
      RealRandomVariable_le rv_X2 rv_X3 ->
      IsFiniteExpectation rv_X2.
  Proof.
    intros.
    unfold IsFiniteExpectation in *.
    unfold Expectation in *.
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
    generalize (RealRandomVariable_le_pos _ _ H0).
    generalize (RealRandomVariable_le_neg _ _ H).
    intros.
    apply Finite_Rbar_opp in eqq1neg.

    rewrite <- (Finite_Expectation_posRV_le _ _ _ _ H1); trivial.
    rewrite <- (Finite_Expectation_posRV_le _ _ _ _ H2); simpl; trivial.
  Qed.

  Global Instance IsFiniteExpectation_min
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2} 
         {isfe1:IsFiniteExpectation rv_X1}
         {isfe2:IsFiniteExpectation rv_X2} :
    IsFiniteExpectation (rvmin rv_X1 rv_X2).
  Proof.
    intros.
    assert (isfep:IsFiniteExpectation (rvplus rv_X1 rv_X2)) by typeclasses eauto.
    unfold IsFiniteExpectation in *.
    unfold Expectation in *.
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
    
    rewrite <- (Finite_Expectation_posRV_le
                 ((fun x : Ts => pos_fun_part (rvmin rv_X1 rv_X2) x))
                 ((fun x : Ts => pos_fun_part (rvplus rv_X1 rv_X2) x))
                 (positive_part_prv _)
                 (positive_part_prv _)).
    -
      rewrite <- (Finite_Expectation_posRV_le
                   ((fun x : Ts => neg_fun_part (rvmin rv_X1 rv_X2) x))
                   (rvplus (fun x : Ts => neg_fun_part rv_X1 x) (fun x : Ts => neg_fun_part rv_X2 x))
                   (negative_part_prv _)
                   _).
      + now simpl.
      + intros a.
        unfold neg_fun_part, rvmin, rvplus, rvopp, rvscale; simpl.
        unfold Rmax, Rmin.
        destruct ( Rle_dec (rv_X1 a) (rv_X2 a))
        ; repeat match_destr; try lra.
      + rewrite Expectation_posRV_sum.
        * apply Finite_Rbar_opp in eqq1neg.
          apply Finite_Rbar_opp in eqq2neg.
          rewrite <- eqq1neg.
          rewrite <- eqq2neg.
          reflexivity.
        * typeclasses eauto.
        * typeclasses eauto.
    - intros a.
      unfold pos_fun_part, rvmin, rvplus; simpl.
      unfold Rmax, Rmin.
      destruct ( Rle_dec (rv_X1 a) (rv_X2 a))
      ; repeat match_destr; lra.
    - match_case_in isfep
      ; [ intros ? eqqp | intros eqqp]
      ; rewrite eqqp in isfep
      ; try contradiction.
      match_destr_in isfep; try contradiction.
      apply Finite_Rbar_plus' in eqqp.
      destruct eqqp as [eqqppos eqqpneg].
      trivial.
  Qed.

  Global Instance IsFiniteExpectation_max
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2} 
         {isfe1:IsFiniteExpectation rv_X1}
         {isfe2:IsFiniteExpectation rv_X2} :
    IsFiniteExpectation (rvmax rv_X1 rv_X2).
  Proof.
    intros.
    assert (isfep:IsFiniteExpectation (rvplus rv_X1 rv_X2)) by typeclasses eauto.
    unfold IsFiniteExpectation in *.
    unfold Expectation in *.
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
    
    rewrite <- (Finite_Expectation_posRV_le
                 ((fun x : Ts => pos_fun_part (rvmax rv_X1 rv_X2) x))
                 (rvplus (fun x : Ts => pos_fun_part rv_X1 x) (fun x : Ts => pos_fun_part rv_X2 x))
                 (positive_part_prv _)
                 _).
    -
      rewrite <- (Finite_Expectation_posRV_le
                   ((fun x : Ts => neg_fun_part (rvmax rv_X1 rv_X2) x))
                   (rvplus (fun x : Ts => neg_fun_part rv_X1 x) (fun x : Ts => neg_fun_part rv_X2 x))
                   (negative_part_prv _)
                   _).
      + now simpl.
      + intros a.
        unfold neg_fun_part, rvmax, rvplus, rvopp, rvscale; simpl.
        unfold Rmax, Rmin.
        destruct ( Rle_dec (rv_X1 a) (rv_X2 a))
        ; repeat match_destr; try lra.
      + rewrite Expectation_posRV_sum.
        * apply Finite_Rbar_opp in eqq1neg.
          apply Finite_Rbar_opp in eqq2neg.
          rewrite <- eqq1neg.
          rewrite <- eqq2neg.
          reflexivity.
        * typeclasses eauto.
        * typeclasses eauto.
    - intros a.
      unfold pos_fun_part, rvmax, rvplus; simpl.
      unfold Rmax, Rmin.
      destruct ( Rle_dec (rv_X1 a) (rv_X2 a))
      ; repeat match_destr; try lra.
    - rewrite Expectation_posRV_sum.
      + rewrite <- eqq1pos.
        rewrite <- eqq2pos.
        reflexivity.
      + typeclasses eauto.
      + typeclasses eauto.
  Qed.
  
End fe.

Hint Rewrite FiniteExpectation_const FiniteExpectation_plus FiniteExpectation_scale FiniteExpectation_opp FiniteExpectation_minus: prob.
