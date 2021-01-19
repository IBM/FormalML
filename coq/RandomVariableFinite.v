Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import FunctionalExtensionality.

Require Import hilbert.

Require Export Expectation.
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
        {isfe2:IsFiniteExpectation rv_X2}
        (eqq: rv_eq rv_X1 rv_X2)
    :
    @FiniteExpectation rv_X1 isfe1 = @FiniteExpectation rv_X2 isfe2.
  Proof.
    unfold FiniteExpectation.
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
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
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
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
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
      erewrite (FiniteExpectation_ext (rvscale 0 rv_X) (const 0)).
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
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
         {isfe1:IsFiniteExpectation rv_X1}
         {isfe2:IsFiniteExpectation rv_X2} :
    IsFiniteExpectation (rvminus rv_X1 rv_X2).
  Proof.
    unfold rvminus.
    typeclasses eauto.
  Qed.

  Lemma FiniteExpectation_minus
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
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
        {rvx:RandomVariable dom borel_sa x}
        {rvy:RandomVariable dom borel_sa y} :
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
        {rvx:RandomVariable dom borel_sa x}
        {rvy:RandomVariable dom borel_sa y} :
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
        {rvx:RandomVariable dom borel_sa x} 
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
        {rvx:RandomVariable dom borel_sa x}
        {rvy:RandomVariable dom borel_sa y} 
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
        {rvx:RandomVariable dom borel_sa x}
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
    - exists (const 0); exists (rvconst _ _ 0); exists (srvconst 0).
      split.
      + unfold BoundedPositiveRandomVariable.
        split.
        * apply prvconst; lra.
        * apply prv.
      + apply SimpleExpectation_const.
  Qed.

  Lemma Expectation_almost_0 x 
        {rvx:RandomVariable dom borel_sa x} :
    rv_almost_eq prts x (const 0) ->
    Expectation x = Some (Finite 0).
  Proof.
    unfold rv_almost_eq.
    intros.
    assert (RandomVariable dom borel_sa (pos_fun_part x)).
    now apply positive_part_rv.
    assert (RandomVariable dom borel_sa (neg_fun_part x)).
    now apply negative_part_rv.
    unfold RandomVariable in rvx.
    rewrite <- borel_sa_preimage2 in rvx.
    assert (sa_sigma (fun x0 : Ts => nonneg(pos_fun_part x x0) = 0)).
    { apply sa_le_pt.
      apply rv_measurable.
      typeclasses eauto.
    }
    assert (sa_sigma (fun x0 : Ts => nonneg(neg_fun_part x x0) = 0)).
    { apply sa_le_pt.
      apply rv_measurable.
      typeclasses eauto.
    }
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

    Lemma IsFiniteExpectation_proper_almost rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
        {isfe1:IsFiniteExpectation rv_X1}
    :
      rv_almost_eq prts rv_X1 rv_X2 ->
      IsFiniteExpectation rv_X2.
  Proof.
    intros.
    generalize (Expectation_almost_0 (rvminus rv_X1 rv_X2))
    ; intros HH.
    cut_to HH.
    - assert (isfe2:IsFiniteExpectation (rvminus rv_X1 rv_X2))
             by (now red; rewrite HH).
      assert (isfe3:IsFiniteExpectation (rvopp (rvminus rv_X1 rv_X2)))
        by now apply IsFiniteExpectation_opp.
      assert (isfe4:IsFiniteExpectation (rvplus rv_X1 (rvopp (rvminus rv_X1 rv_X2))))
        by (apply IsFiniteExpectation_plus; trivial; try typeclasses eauto).
      eapply IsFiniteExpectation_proper; try eapply isfe4.
      intros a.
      rv_unfold; lra.
    - unfold rv_almost_eq in *.
      unfold const in *.
      assert (event_equiv (fun x0 : Ts => rvminus rv_X1 rv_X2 x0 = 0) (fun x0 : Ts => rv_X1 x0 = rv_X2 x0)).
      intros a.
      unfold rvminus, rvplus, rvopp, rvscale.
      split; intros; lra.
      now rewrite H0.
  Qed.

  Lemma FiniteExpectation_proper_almost rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
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
      rv_le rv_X1 rv_X2 ->
      FiniteExpectation rv_X1 <= FiniteExpectation rv_X2.
  Proof.
    intros.
    unfold FiniteExpectation.
    simpl_finite.
    apply (Expectation_le rv_X1 rv_X2 _ _ e e0) in H.
    now simpl in H.
  Qed.


  Lemma IsFiniteExpectation_bounded rv_X1 rv_X2 rv_X3
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X3}
    :
      rv_le rv_X1 rv_X2 ->
      rv_le rv_X2 rv_X3 ->
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
    generalize (rv_le_pos_fun_part _ _ H0).
    generalize (rv_le_neg_fun_part _ _ H).
    intros.
    apply Finite_Rbar_opp in eqq1neg.

    rewrite <- (Finite_Expectation_posRV_le _ _ _ _ H1); trivial.
    rewrite <- (Finite_Expectation_posRV_le _ _ _ _ H2); simpl; trivial.
  Qed.

  Global Instance IsFiniteExpectation_min
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
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
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
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

  Global Instance IsFiniteExpectation_case
         (c: Ts -> bool) (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
         {isfe1:IsFiniteExpectation rv_X1}
         {isfe2:IsFiniteExpectation rv_X2} :
    IsFiniteExpectation (rvchoice c rv_X1 rv_X2).
  Proof.
    intros.
    eapply IsFiniteExpectation_bounded
    ; try eapply rvchoice_le_min
    ; try eapply rvchoice_le_max
    ; typeclasses eauto.
  Qed.

  Lemma FiniteExpectation_pos  (rv_X : Ts -> R)
        {prv : PositiveRandomVariable rv_X}
        {isfe:IsFiniteExpectation rv_X} :
    0 <= FiniteExpectation rv_X.
  Proof.
    unfold FiniteExpectation.
    simpl_finite.
    generalize (Expectation_posRV_pos rv_X).
    erewrite Expectation_pos_posRV in e.
    invcs e.
    rewrite H0.
    simpl.
    trivial.
  Qed.

  Lemma FiniteExpectation_zero_pos 
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {posrv :PositiveRandomVariable X}
        {isfe:IsFiniteExpectation X} :
    FiniteExpectation X = 0%R ->
    ps_P (fun omega => X omega = 0) = 1.
  Proof.
    unfold FiniteExpectation.
    simpl_finite.
    intros; subst.
    now apply Expectation_zero_pos.
  Qed.


  Definition rvsum (Xn : nat -> Ts -> R) (n : nat) :=
    (fun omega => sum_n (fun n0 => Xn n0 omega) n).
  
  Instance rvsum_measurable 
           (Xn : nat -> Ts -> R)
           (Xn_rv : forall n, RealMeasurable dom (Xn n)) :
      forall (n:nat), RealMeasurable dom (rvsum Xn n).
  Proof.
    unfold RealMeasurable in *.
    induction n; intros.
    - assert (event_equiv (fun omega : Ts => rvsum Xn 0 omega <= r)
                          (fun omega : Ts => Xn 0%nat omega <= r)).
      + intro x.
        unfold rvsum, sum_n.
        now rewrite sum_n_n.
      + now rewrite H.
    - assert (event_equiv  (fun omega : Ts => rvsum Xn (S n) omega <= r)
                           (fun omega => (rvplus (rvsum Xn n) (Xn (S n))) omega <= r)).
      + intro x.
        unfold rvsum, rvplus, sum_n.
        rewrite sum_n_Sm.
        now unfold plus; simpl.
        lia.
      + rewrite H.
        now apply plus_measurable.
   Qed.

  Instance rvsum_rv (Xn : nat -> Ts -> R)
           {rv : forall (n:nat), RandomVariable dom borel_sa (Xn n)} :
    forall (n:nat), RandomVariable dom borel_sa (rvsum Xn n).
      Proof.
        intros.
        apply measurable_rv.
        apply rvsum_measurable; intros.
        now apply rv_measurable.
      Qed.

  Instance rvsum_pos (Xn : nat -> Ts -> R)
           {Xn_pos : forall n, PositiveRandomVariable (Xn n)} :
    forall (n:nat), PositiveRandomVariable (rvsum Xn n).
  Proof.
    intros.
    unfold PositiveRandomVariable in Xn_pos.
    unfold PositiveRandomVariable, rvsum; intros.
    induction n.
    - unfold sum_n.
      now rewrite sum_n_n.
    - unfold sum_n.
      rewrite sum_n_Sm.
      apply Rplus_le_le_0_compat ; trivial.
      lia.
  Qed.

  Lemma Lim_seq_pos (f : nat -> R) :
    (forall n, 0 <= f n) ->
    Rbar_le 0 (Lim_seq f).
  Proof.
    intros.
    generalize (Lim_seq_le_loc (fun _ => 0) f); intros.
    rewrite Lim_seq_const in H0.
    apply H0.
    exists (0%nat).
    intros.
    apply H.
  Qed.

  Instance series_rv_pos
         (Xn : nat -> Ts -> R)
         (Xn_pos : forall n, PositiveRandomVariable (Xn n)) 
         (is_fin_lim : 
            forall omega, is_finite (Lim_seq (sum_n (fun n => Xn n omega)))):
    PositiveRandomVariable (fun omega => Lim_seq (sum_n (fun n => Xn n omega))).
  Proof.
    unfold PositiveRandomVariable in *; intros.
    generalize (Lim_seq_pos (sum_n (fun n : nat => Xn n x))).
    rewrite <- is_fin_lim; simpl.
    intros; apply H.
    intros.
    now apply rvsum_pos.
 Qed.

  Global Instance IsFiniteExpectation_sum (Xn : nat -> Ts -> R)
         {Xn_rv : forall n, RandomVariable dom borel_sa  (Xn n)} 
         {isfe: forall (n:nat), IsFiniteExpectation (Xn n)} :
    forall n, IsFiniteExpectation (rvsum Xn n).
  Proof.
    intros.
    induction n.
    - unfold rvsum, sum_n.
      rewrite (IsFiniteExpectation_proper _ (Xn 0%nat)); trivial.
      intro x.
      now rewrite sum_n_n.
    - rewrite (IsFiniteExpectation_proper _ (rvplus (rvsum Xn n) (Xn (S n)))).
      apply IsFiniteExpectation_plus; trivial.
      now apply rvsum_rv.
      intro x.
      unfold rvsum, rvplus, sum_n.
      rewrite sum_n_Sm; [|lia].      
      now unfold plus; simpl.
   Qed.

  Lemma sum_expectation
        (Xn : nat -> Ts -> R)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
        (Xn_rv : forall n, RandomVariable dom borel_sa  (Xn n)) 
        (isfe : forall n, IsFiniteExpectation (Xn n)) :
    forall (n:nat),
      sum_n (fun n0 : nat => FiniteExpectation (Xn n0)) n =
      FiniteExpectation (rvsum Xn n).
    Proof.
      intros.
      induction n.
      - unfold rvsum, sum_n.
        rewrite sum_n_n.
        symmetry.
        rewrite FiniteExpectation_ext with (rv_X2 := Xn 0%nat) (isfe2 := isfe 0%nat); trivial.
        intro x.
        now rewrite sum_n_n.
      - unfold rvsum, sum_n.
        rewrite sum_n_Sm; [unfold plus; simpl | lia].
        symmetry.
        rewrite FiniteExpectation_ext with (rv_X2 := rvplus (rvsum Xn n) (Xn (S n))) (isfe2 := (IsFiniteExpectation_plus (rvsum Xn n) (Xn (S n)))).
        rewrite FiniteExpectation_plus.
        unfold sum_n in IHn.
        now rewrite IHn.
        intro x.
        rewrite sum_n_Sm; unfold plus, rvsum, rvplus, sum_n; simpl; trivial.
        lia.
  Qed.

    Lemma FiniteExpectation_posRV (X:Ts->R) 
          {posX: PositiveRandomVariable X}
          {isfeX: IsFiniteExpectation X} :
      FiniteExpectation X = real (Expectation_posRV  X).
    Proof.
      unfold FiniteExpectation.
      unfold proj1_sig.
      match_destr.
      rewrite (Expectation_pos_posRV) with  (prv:=posX) in e.
      invcs e.
      rewrite H0.
      now simpl.
    Qed.
    
    Lemma IsFiniteExpectation_posRV (X:Ts->R) 
          {posX: PositiveRandomVariable X}
          {isfeX: IsFiniteExpectation X} :
      is_finite (Expectation_posRV  X).
    Proof.
      red in isfeX.
      rewrite Expectation_pos_posRV with (prv:=posX) in isfeX.
      match_destr_in isfeX; try tauto.
      reflexivity.
   Qed.

  Lemma monotone_convergence_FiniteExpectation
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (posX: PositiveRandomVariable X) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
        (isfeX: IsFiniteExpectation X)
        (isfe: forall (n:nat), IsFiniteExpectation (Xn n)) :
    (forall (n:nat), rv_le (Xn n) X) ->
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
    Lim_seq (fun n => FiniteExpectation (Xn n)) =  (FiniteExpectation X).
  Proof.
    intros.
    generalize (monotone_convergence X Xn rvx posX Xn_rv Xn_pos H H0); intros.
    cut_to H2; trivial.
    - rewrite (Lim_seq_ext _  (fun n : nat => Expectation_posRV (Xn n))).
      + rewrite H2.
        rewrite FiniteExpectation_posRV with (posX:=posX).
        red in isfeX.
        rewrite Expectation_pos_posRV with (prv:=posX) in isfeX.
        match_destr_in isfeX; try tauto.
      + intros n.
        now rewrite FiniteExpectation_posRV with (posX:=Xn_pos n).
    - intros.
      now apply IsFiniteExpectation_posRV.
  Qed.

Lemma Fatou_FiniteExpectation
        (Xn : nat -> Ts -> R)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (isfe_Xn : forall n, IsFiniteExpectation (Xn n))
        (isfe_limInf : IsFiniteExpectation
                         (fun omega : Ts => LimInf_seq (fun n : nat => Xn n omega)))
        (isf:forall omega, is_finite (LimInf_seq (fun n : nat => Xn n omega)))

        (lim_rv : RandomVariable dom borel_sa 
                                 (fun omega => LimInf_seq (fun n => Xn n omega))) :
                                                                                    
    Rbar_le (FiniteExpectation (fun omega => LimInf_seq (fun n => Xn n omega)))
            (LimInf_seq (fun n => FiniteExpectation (Xn n))).
  Proof.
    assert (fin_exp: forall n, is_finite (Expectation_posRV (Xn n))).
    - intros.
      now apply IsFiniteExpectation_posRV.
    - generalize (Fatou Xn Xn_pos Xn_rv fin_exp isf lim_rv); intros.
      rewrite FiniteExpectation_posRV with (posX := LimInf_seq_pos Xn Xn_pos).
      unfold LimInf_seq.
      destruct (ex_LimInf_seq (fun n : nat => FiniteExpectation (Xn n))).
      generalize (is_LimInf_seq_ext  (fun n : nat => FiniteExpectation (Xn n)) 
                                     (fun n : nat => Expectation_posRV (Xn n)) x); intros.
      cut_to H0; trivial.
      apply is_LimInf_seq_unique in H0.      
      rewrite <- H0.
      now rewrite IsFiniteExpectation_posRV.
      intros.
      now rewrite FiniteExpectation_posRV with (posX :=Xn_pos n).
   Qed.

  Lemma Lim_seq_increasing_le (f : nat -> R) :
    (forall n, f n <= f (S n)) ->
    forall n, Rbar_le (f n) (Lim_seq f).
  Proof.
    intros.
    rewrite <- Lim_seq_const.
    apply Lim_seq_le_loc.
    exists n.
    intros.
    now apply incr_le_strong.
  Qed.

  Lemma rvsum_le_series (Xn : nat -> Ts -> R) 
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :
    (forall omega, is_finite (Lim_seq (fun n => rvsum Xn n omega))) ->
    forall n:nat,
      rv_le (rvsum Xn n)
            (fun omega => Lim_seq (fun n0 : nat => rvsum Xn n0 omega)).
   Proof.
     intros isfin n x.
     generalize (Lim_seq_increasing_le (fun n => rvsum Xn n x)); intros.
     rewrite <- isfin in H.
     apply H.
     intros.
     unfold rvsum, sum_n.
     replace (sum_n_m (fun n1 : nat => Xn n1 x) 0 n0) with
         (sum_n_m (fun n1 : nat => Xn n1 x) 0 n0 + 0) by lra.
     rewrite sum_n_Sm; [|lia].
     unfold plus; simpl.
     apply Rplus_le_compat_l.
     apply Xn_pos.
   Qed.

  Lemma series_expectation
        (Xn : nat -> Ts -> R)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
        (Xn_rv : forall n, RandomVariable dom borel_sa  (Xn n))
        (isfe : forall n, IsFiniteExpectation (Xn n)) 
        (lim_rv : RandomVariable dom borel_sa 
                                 (fun omega => Lim_seq (sum_n (fun n => Xn n omega))))
        (lim_fin : forall omega,
            is_finite (Lim_seq (fun n : nat => rvsum Xn n omega)))
        (lim_fe : IsFiniteExpectation
                    (fun omega : Ts => Lim_seq (fun n : nat => rvsum Xn n omega)))
        (lim_pos : PositiveRandomVariable
           (fun omega : Ts => Lim_seq (fun n : nat => rvsum Xn n omega))):    
    (forall omega, ex_lim_seq (fun n : nat => rvsum Xn n omega)) ->
    Lim_seq (sum_n (fun n => FiniteExpectation (Xn n))) =
    FiniteExpectation (fun omega => Lim_seq (fun n => rvsum Xn n omega)).
  Proof.
    generalize (monotone_convergence_FiniteExpectation
                  (fun omega : Ts => Lim_seq (fun n => rvsum Xn n omega))
                  (fun n => rvsum Xn n) lim_rv lim_pos (rvsum_rv Xn) (rvsum_pos Xn)
               lim_fe (IsFiniteExpectation_sum Xn)); intros.
    cut_to H.
    - rewrite Lim_seq_ext with 
          (v := fun n : nat => FiniteExpectation (rvsum Xn n)); [apply H |].
      now apply sum_expectation.
    - now apply rvsum_le_series.
    - intros; intro x.
      unfold rvsum, sum_n.
      rewrite sum_n_Sm; [unfold plus; simpl | lia].
      replace (sum_n_m (fun n0 : nat => Xn n0 x) 0 n) with
          (sum_n_m (fun n0 : nat => Xn n0 x) 0 n + 0) at 1 by lra.
      apply Rplus_le_compat_l.
      apply Xn_pos.
    - intros.
      rewrite lim_fin.
      now apply Lim_seq_correct.
  Qed.

(*
  Lemma lim_ascending (E : nat -> event Ts) :
    (forall (n:nat), sa_sigma (E n)) ->
    (forall n, event_sub (E n) (E (S n))) ->
    is_lim_seq (fun n => ps_P (E n)) (ps_P (union_of_collection E)).
  Proof.
    Admitted.

  Lemma lim_ascending2 (E : nat -> event Ts) :
    (forall (n:nat), sa_sigma (E n)) ->
    (forall n, event_sub (E n) (E (S n))) ->
    Lim_seq (fun n => ps_P (E n)) =  (ps_P (union_of_collection E)).
  Proof.
    intros.
    apply is_lim_seq_unique.
    now apply lim_ascending.
  Qed.
*)
  Lemma lim_descending (E : nat -> event Ts) :
    (forall (n:nat), sa_sigma (E n)) ->
    (forall n, event_sub (E (S n)) (E n)) ->
    is_lim_seq (fun n => ps_P (E n)) (ps_P (inter_of_collection E)).
  Proof.
    Admitted.

  Lemma lim_descending2 (E : nat -> event Ts) :
    (forall (n:nat), sa_sigma (E n)) ->
    (forall n, event_sub (E (S n)) (E n)) ->
    Lim_seq (fun n => ps_P (E n)) = (ps_P (inter_of_collection E)).
  Proof.
    intros.
    apply is_lim_seq_unique.
    now apply lim_descending.
  Qed.

  Lemma Lim_series_tails (f : nat -> R) :
        ex_series f ->
        Lim_seq (fun k : nat => Series (fun n : nat => f (n + k)%nat)) = 0.
    Proof.
    Admitted.

  Lemma ps_union_le_ser col :
    ex_series (fun n0 : nat => ps_P (col n0)) ->
    (forall n : nat, sa_sigma (col n)) ->
    ps_P (union_of_collection col) <=
    Series (fun n0 : nat => ps_P (col n0)).
  Proof.
    intros.
    apply ps_countable_boole_inequality; trivial.
    rewrite <- infinite_sum_infinite_sum'.
    rewrite <- is_series_Reals.
    now apply Series_correct.
  Qed.

  Lemma Borel_Cantelli (E : nat -> event Ts) :
    (forall (n:nat), sa_sigma (E n)) ->
    ex_series (fun n => ps_P (E n)) ->
    ps_P (inter_of_collection 
            (fun k => union_of_collection 
                        (fun n => E (n + k)%nat))) = 0.
  Proof.
    intros.
    assert (Rbar_le
              (Lim_seq (fun k => ps_P (union_of_collection (fun n => E (n+k)%nat))))
              (Lim_seq (fun k => Series (fun n => ps_P (E (n+k)%nat))))).
    {
    apply Lim_seq_le_loc; exists (0%nat); intros.
    apply ps_union_le_ser.
    apply ex_series_ext with (a :=  (fun n0 : nat => ps_P (E (n + n0)%nat))).
    intros.
    f_equal; f_equal; lia.
    now rewrite <- ex_series_incr_n with (a := (fun n0 => ps_P (E n0))).
    intros.
    apply H.
    }
    generalize (Lim_series_tails (fun n => ps_P (E n)) H0); intros.    
    unfold ex_series in H0.
    destruct H0.
    assert (ps_P (inter_of_collection 
                    (fun k => union_of_collection 
                                (fun n => E (n + k)%nat))) =
            Lim_seq (fun k => ps_P (union_of_collection
                                    (fun n => E (n + k)%nat)))).
    { 
      rewrite lim_descending2; trivial.
      intros.
      now apply sa_countable_union.
      intros n x0.
      unfold union_of_collection; intros.
      destruct H3.
      exists (S x1).
      now replace (S x1 + n)%nat with (x1 + S n)%nat by lia.
    } 
    rewrite H2 in H1.
    rewrite H3.
    apply Rbar_le_antisym in H1.
    - symmetry in H1.
      now rewrite H1.
    - replace (Finite 0) with (Lim_seq (fun _ => 0)) by apply Lim_seq_const.
      apply Lim_seq_le_loc; exists (0%nat); intros.
      apply ps_pos.
      now apply sa_countable_union.
  Qed.    

End fe.

Hint Rewrite FiniteExpectation_const FiniteExpectation_plus FiniteExpectation_scale FiniteExpectation_opp FiniteExpectation_minus: prob.
