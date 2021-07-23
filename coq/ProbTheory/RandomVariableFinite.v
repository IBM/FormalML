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
           
  Lemma FiniteExpectation_ext_alt rv_X1 rv_X2
        {isfe1:IsFiniteExpectation rv_X1}
        (eqq: rv_eq rv_X1 rv_X2)
    :
    @FiniteExpectation rv_X1 isfe1 = 
    @FiniteExpectation rv_X2 (proj1 (IsFiniteExpectation_proper _ _ eqq) isfe1).
  Proof.
    now apply FiniteExpectation_ext.
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

  Instance pos_fun_part_proper_almost : Proper (almost prts eq ==> almost prts eq) 
                                            (fun x x0 => nonneg (pos_fun_part x x0)).
  Proof.
    intros x1 x2 eqq1.
    apply (almost_sub prts eq (fun x x0 => nonneg (pos_fun_part x x0))); trivial.
    intros.
    unfold pos_fun_part; simpl.
    now rewrite H.
  Qed.

  Instance neg_fun_part_proper_almost : Proper (almost prts eq ==> almost prts eq) 
                                            (fun x x0 => nonneg (neg_fun_part x x0)).
  Proof.
    intros x1 x2 eqq1.
    apply (almost_sub prts eq (fun x x0 => nonneg (neg_fun_part x x0))); trivial.
    intros.
    unfold neg_fun_part; simpl.
    now rewrite H.
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
        {xsrv:FiniteRangeFunction x} :
    almost prts eq x (const 0) ->
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
    - subst.
      apply almost_alt_eq in eqq.
      destruct eqq as [P[Pempty Pnone]].
      assert (sub:preimage_singleton x x1 ≤ P).
      {
        intros a pre; simpl.
        apply Pnone.
        vm_compute in pre.
        congruence.
      }
      generalize (ps_sub _ _ _ sub)
      ; intros PP.
      rewrite Pempty in PP.
      assert (eqq1:ps_P (preimage_singleton x x1) = 0).
      {
        generalize (ps_pos (preimage_singleton x x1)).
        lra.
      }
      rewrite eqq1.
      lra.
  Qed.

  Lemma Expectation_simple_proper_almost x y
        {rvx:RandomVariable dom borel_sa x}
        {rvy:RandomVariable dom borel_sa y} 
        {xsrv:FiniteRangeFunction x}
        {ysrv:FiniteRangeFunction y} :
    almost prts eq x y ->
    SimpleExpectation x = SimpleExpectation y.
  Proof.
    intros.
    generalize (SimplePosExpectation_pos_zero (rvminus x y))
    ; intros HH.
    cut_to HH.
    - unfold rvminus in HH.
      erewrite SimpleExpectation_pf_irrel in HH.
      erewrite sumSimpleExpectation' with (srv1:=xsrv) (srv2:=srvopp) in HH; trivial.
      + unfold rvopp in HH.
        erewrite (@SimpleExpectation_pf_irrel _ _ _ (rvscale (-1) y)) in HH.
        erewrite <- scaleSimpleExpectation with (srv:=ysrv) in HH.
        field_simplify in HH.
        apply Rminus_diag_uniq_sym in HH.
        symmetry.
        apply HH.
    - destruct H as [P [Pa Pb]].
      exists P.
      split; trivial.
      intros.
      vm_compute.
      rewrite Pb; trivial.
      lra.
      Unshelve.
      typeclasses eauto.
      typeclasses eauto.
  Qed.

  Lemma NonnegExpectation_almost_0 x 
        {prv:PositiveRandomVariable x} :
    almost prts eq x (const 0) ->
    NonnegExpectation x = 0.
  Proof.
    intros.
    unfold NonnegExpectation, SimpleExpectationSup.
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
        simpl.
        assert (almost prts eq x2 (const 0)).
        * destruct H as [P [Pall eq_on]].
          exists P.
          split; trivial.
          intros a ?.
          specialize (H1 a).
          rewrite eq_on in H1; trivial.
          unfold const in *.
          specialize (H0 a).
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

  Lemma Expectation_almost_0 x :
    almost prts eq x (const 0) ->
    Expectation x = Some (Finite 0).
  Proof.
    intros.
    unfold Expectation.
    assert (almost prts eq (fun omega => nonneg(pos_fun_part x omega)) (const 0)).
    {
      rewrite (pos_fun_part_proper_almost _ _ H).
      unfold const; simpl.
      unfold Rmax.
      match_destr; try lra.
      reflexivity.
    } 
    assert (almost prts eq (fun omega => nonneg(neg_fun_part x omega)) (const 0)).
    {
      rewrite (neg_fun_part_proper_almost _ _ H).
      unfold const; simpl.
      unfold Rmax.
      match_destr; try lra.
      reflexivity.
    }
    rewrite (NonnegExpectation_almost_0 _ H0).
    rewrite (NonnegExpectation_almost_0 _ H1).
    simpl; repeat f_equal.
    lra.
  Qed.
  
  Lemma IsFiniteExpectation_proper_almost rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
        {isfe1:IsFiniteExpectation rv_X1}
    :
      almost prts eq rv_X1 rv_X2 ->
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
    -  rewrite H.
       apply almost_eq_subr.
       rv_unfold; intros ?.
       lra.
  Qed.

  Lemma FiniteExpectation_proper_almost rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X2}
    :
      almost prts eq rv_X1 rv_X2 ->
      FiniteExpectation rv_X1 = FiniteExpectation rv_X2.

  Proof.
    intros.
    generalize (Expectation_almost_0 (rvminus rv_X1 rv_X2))
    ; intros HH.
    cut_to HH.
    - apply (Expectation_FiniteExpectation _ _ (isfe:=IsFiniteExpectation_minus _ _)) in HH.
      rewrite FiniteExpectation_minus in HH.
      lra.
    - rewrite H.
      apply almost_eq_subr.
      rv_unfold; intros ?.
      lra.
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

    rewrite <- (Finite_NonnegExpectation_le _ _ _ _ H1); trivial.
    rewrite <- (Finite_NonnegExpectation_le _ _ _ _ H2); simpl; trivial.
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
    
    rewrite <- (Finite_NonnegExpectation_le
                 ((fun x : Ts => pos_fun_part (rvmin rv_X1 rv_X2) x))
                 ((fun x : Ts => pos_fun_part (rvplus rv_X1 rv_X2) x))
                 (positive_part_prv _)
                 (positive_part_prv _)).
    -
      rewrite <- (Finite_NonnegExpectation_le
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
      + rewrite NonnegExpectation_sum.
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
    
    rewrite <- (Finite_NonnegExpectation_le
                 ((fun x : Ts => pos_fun_part (rvmax rv_X1 rv_X2) x))
                 (rvplus (fun x : Ts => pos_fun_part rv_X1 x) (fun x : Ts => pos_fun_part rv_X2 x))
                 (positive_part_prv _)
                 _).
    -
      rewrite <- (Finite_NonnegExpectation_le
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
      + rewrite NonnegExpectation_sum.
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
    - rewrite NonnegExpectation_sum.
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
    generalize (NonnegExpectation_pos rv_X).
    erewrite Expectation_pos_posRV in e.
    invcs e.
    rewrite H0.
    simpl.
    trivial.
  Qed.

  Lemma FiniteExpectation_zero_pos'
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {posrv :PositiveRandomVariable X}
        {isfe:IsFiniteExpectation X} :
    FiniteExpectation X = 0%R ->
    ps_P (preimage_singleton X 0) = 1.
  Proof.
    unfold FiniteExpectation.
    simpl_finite.
    intros; subst.
    now apply Expectation_zero_pos.
  Qed.

  Lemma FiniteExpectation_zero_pos
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {posrv :PositiveRandomVariable X}
        {isfe:IsFiniteExpectation X} :
    FiniteExpectation X = 0%R ->
    almost prts eq X (const 0).
  Proof.
    intros eqq1.
    apply (FiniteExpectation_zero_pos' X) in eqq1.
    exists (preimage_singleton X 0).
    split; trivial.
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

    Lemma FiniteNonnegExpectation (X:Ts->R) 
          {posX: PositiveRandomVariable X}
          {isfeX: IsFiniteExpectation X} :
      FiniteExpectation X = real (NonnegExpectation  X).
    Proof.
      unfold FiniteExpectation.
      unfold proj1_sig.
      match_destr.
      rewrite (Expectation_pos_posRV) with  (prv:=posX) in e.
      invcs e.
      rewrite H0.
      now simpl.
    Qed.
    
    Lemma IsFiniteNonnegExpectation (X:Ts->R) 
          {posX: PositiveRandomVariable X}
          {isfeX: IsFiniteExpectation X} :
      is_finite (NonnegExpectation  X).
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
    - rewrite (Lim_seq_ext _  (fun n : nat => NonnegExpectation (Xn n))).
      + rewrite H2.
        rewrite FiniteNonnegExpectation with (posX:=posX).
        red in isfeX.
        rewrite Expectation_pos_posRV with (prv:=posX) in isfeX.
        match_destr_in isfeX; try tauto.
      + intros n.
        now rewrite FiniteNonnegExpectation with (posX:=Xn_pos n).
    - intros.
      now apply IsFiniteNonnegExpectation.
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
    assert (fin_exp: forall n, is_finite (NonnegExpectation (Xn n))).
    - intros.
      now apply IsFiniteNonnegExpectation.
    - generalize (Fatou Xn Xn_pos Xn_rv fin_exp isf lim_rv); intros.
      rewrite FiniteNonnegExpectation with (posX := LimInf_seq_pos Xn Xn_pos).
      unfold LimInf_seq.
      destruct (ex_LimInf_seq (fun n : nat => FiniteExpectation (Xn n))).
      generalize (is_LimInf_seq_ext  (fun n : nat => FiniteExpectation (Xn n)) 
                                     (fun n : nat => NonnegExpectation (Xn n)) x); intros.
      cut_to H0; trivial.
      apply is_LimInf_seq_unique in H0.      
      rewrite <- H0.
      now rewrite IsFiniteNonnegExpectation.
      intros.
      now rewrite FiniteNonnegExpectation with (posX :=Xn_pos n).
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
                  (fun n => rvsum Xn n) lim_rv lim_pos (rvsum_rv _ Xn) (rvsum_pos Xn)
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
  Lemma sa_collection_take (E : nat -> event dom) n :
    (forall m, sa_sigma (E m)) -> (forall e, In e (collection_take E n) -> sa_sigma e).
  Proof.
    unfold collection_take.
    intros.
    apply in_map_iff in H0.
    destruct H0 as [?[??]]; subst.
    auto.
  Qed.
   *)
  
  Lemma sum_prob_fold_right  (E : nat -> event dom) n :
        sum_n (fun n0 : nat => ps_P (E n0)) n =
        fold_right Rplus 0 (map ps_P (collection_take E (S n))).
  Proof.
    rewrite sum_n_fold_right_seq.
    f_equal.
    unfold collection_take.
    now rewrite map_map.
  Qed.    
  
  Lemma is_finite_Lim_bounded (f : nat -> R) (m M : R) :
    (forall (n:nat), m <= f n <= M) ->
    is_finite (Lim_seq f).
  Proof.
    generalize (Lim_seq_le_loc f (fun _ => M)); intros.
    generalize (Lim_seq_le_loc (fun _ => m) f); intros.    
    cut_to H.
    cut_to H1.
    rewrite Lim_seq_const in H.
    rewrite Lim_seq_const in H1.
    unfold is_finite.
    destruct (Lim_seq f).
    reflexivity.
    now simpl in H.
    now simpl in H1.
    exists (0%nat); intros; apply H0.
    exists (0%nat); intros; apply H0.
  Qed.    

  Lemma is_finite_Lim_seq_psP (E : nat -> event dom) :
    is_finite (Lim_seq (fun n => ps_P (E n))).
  Proof.
    intros.
    apply is_finite_Lim_bounded with (m := 0) (M := 1).
    intros.
    split.
    now apply ps_pos.
    now apply ps_le1.
  Qed.

  Lemma lim_ascending (E : nat -> event dom) :
    ascending_collection E ->
    Lim_seq (fun n => ps_P (E n)) =  (ps_P (union_of_collection E)).
  Proof.
    intros asc.
    generalize (union_of_make_collection_disjoint prts E); intros HH.
    unfold sum_of_probs_equals in HH.
    rewrite <- make_collection_disjoint_union in HH.
    rewrite <- infinite_sum_infinite_sum' in HH.
    rewrite <- is_series_Reals in HH.
    apply is_series_unique in HH.
    unfold Series in HH.
    rewrite <- is_finite_Lim_seq_psP; trivial.
    rewrite Rbar_finite_eq.
    rewrite Lim_seq_ext with (v  := fun n => ps_P (E n)) in HH.
    apply HH.
    intros.
    rewrite <- ascending_make_disjoint_collection_take_union by trivial.
    rewrite ps_list_disjoint_union.
    - apply  sum_prob_fold_right.
    - apply collection_take_preserves_disjoint.
      apply make_collection_disjoint_disjoint.
  Qed.

  Lemma diff_inter_compl (A B : event dom) :
    (event_equiv (event_diff A B) 
                 (event_inter A (event_complement B))).
  Proof.
    firstorder.
  Qed.
  
  Lemma union_diff (A B : event dom) :
    event_equiv A (event_union (event_diff A B) (event_inter A B)).
  Proof.
    unfold event_union, event_diff, event_inter, event_equiv.
    unfold pre_event_union, pre_event_diff, pre_event_inter.
    repeat red; simpl; intros.
    tauto.
  Qed.

  Lemma sub_diff_union (A B : event dom) :
    event_sub B A ->
    event_equiv A (event_union (event_diff A B) B).
  Proof.
    unfold event_union, event_diff, event_inter, event_equiv, event_sub.
    unfold pre_event_union, pre_event_diff, pre_event_inter, pre_event_sub.
    repeat red; simpl; intros.
    split; intros.
    - destruct (classic (proj1_sig B x)); tauto.
    - intuition.
  Qed.

  Lemma ps_diff_sub (A B : event dom) :
    event_sub B A ->
    ps_P (event_diff A B) = ps_P A - ps_P B.
  Proof.
    intros.
    generalize (ps_disjoint_union prts (event_diff A B) B); intros.
    cut_to H0.
    - rewrite <- sub_diff_union in H0; trivial.
      lra.
    - firstorder.
  Qed.

  Lemma event_sub_descending (E : nat -> event dom) :
    (forall n, event_sub (E (S n)) (E n)) ->
    forall n, event_sub (E n) (E 0%nat).
  Proof.
    induction n.
    intro x.
    tauto.
    now eapply transitivity.
  Qed.

  Lemma union_diff_inter (A:event dom) (E : nat -> event dom) :
        event_equiv (union_of_collection (fun n : nat => event_diff A (E n)))
                    (event_diff A (inter_of_collection E)).
  Proof.
    unfold event_equiv, union_of_collection, event_diff, inter_of_collection.
    unfold pre_event_equiv, pre_union_of_collection, pre_event_equiv, pre_inter_of_collection; simpl.
    intros.
    split; [firstorder |]; intros.
    destruct H.
    apply not_all_ex_not in H0.
    firstorder.
  Qed.
    
  Lemma lim_descending (E : nat -> event dom) :
    (forall n, event_sub (E (S n)) (E n)) ->
    Lim_seq (fun n => ps_P (E n)) = (ps_P (inter_of_collection E)).
  Proof.
    intros.
    generalize (lim_ascending (fun n => event_diff (E 0%nat) (E n))); intros asc.
    generalize (is_finite_Lim_seq_psP E); intros isf.
    cut_to asc.
    - rewrite Lim_seq_ext with (v := (fun n => (ps_P (E 0%nat)) - (ps_P (E n)))) in asc.
      + rewrite union_diff_inter in asc. 
        rewrite ps_diff_sub in asc.
        * rewrite Lim_seq_minus in asc.
          -- rewrite Lim_seq_const in asc.
             rewrite <- isf in asc.
             simpl in asc.
             rewrite Rbar_finite_eq in asc.
             ring_simplify in asc.
             rewrite <- isf.
             rewrite Rbar_finite_eq.
             lra.
          -- apply ex_lim_seq_const.
          -- apply ex_lim_seq_decr.
             intros.
             now apply ps_sub.
          -- rewrite Lim_seq_const.
             now rewrite <- isf.
        * firstorder.
      + intros.
        apply ps_diff_sub; trivial.
        now apply event_sub_descending.
    - unfold ascending_collection; intros.
      firstorder.
  Qed.
    
  Lemma sum_shift (f : nat -> R) (n n0 : nat) :
    sum_n_m f n (n0 + n) = sum_n_m (fun n1 : nat => f (n1 + n)%nat) 0 n0.
  Proof.
    induction n0.
    - replace (0 + n)%nat with n by lia.
      do 2 rewrite sum_n_n.
      now replace (0 + n)%nat with n by lia.
    - replace (S n0 + n)%nat with (S (n0 + n)%nat) by lia.
      rewrite sum_n_Sm; [|lia].
      rewrite sum_n_Sm; [|lia].
      replace (S n0 + n)%nat with (S (n0 + n)%nat) by lia.
      now apply Rplus_eq_compat_r.
   Qed.

  Lemma Lim_series_tails (f : nat -> R) :
        ex_series f ->
        (forall n, 0 <= f n) ->
        Lim_seq (fun k : nat => Series (fun n : nat => f (n + k)%nat)) = 0.
    Proof.
      intros.
      generalize (Cauchy_ex_series f H); intros.
      unfold Cauchy_series in H1.
      apply is_lim_seq_unique.
      rewrite <- is_lim_seq_spec.
      unfold is_lim_seq', Series; intros.
      assert (0 < eps) by apply cond_pos.
      assert (0 < eps/2) by lra.
      specialize (H1 (mkposreal _ H3)).
      destruct H1.
      exists x; intros.
      assert (Rbar_le (Lim_seq (fun k => (sum_n (fun n0 : nat => f (n0 + n)%nat) k))) (eps/2)).
      { 
        replace (Finite (eps/2)) with (Lim_seq (fun n => eps/2)) by apply Lim_seq_const.
        apply Lim_seq_le_loc.
        exists x; intros.
        unfold norm in H1; simpl in H1.
        specialize (H1 n (n0 + n)%nat H4).
        assert (x <= n0 + n)%nat by lia.
        specialize (H1 H6).
        rewrite Rabs_right in H1.
        - unfold sum_n; left.
          now replace  (sum_n_m (fun n1 : nat => f (n1 + n)%nat) 0 n0) with
              (sum_n_m f n (n0 + n)) by apply sum_shift.
        - apply Rle_ge.
          replace 0 with (sum_n_m (fun _ => 0) n (n0 + n)%nat) by 
              (rewrite sum_n_m_const; lra).
          now apply sum_n_m_le.
      }
      rewrite Rminus_0_r.
      generalize (Lim_seq_pos (sum_n (fun n0 : nat => f (n0 + n)%nat))); intros.
      cut_to H6.
      - destruct (Lim_seq (sum_n (fun n0 : nat => f (n0 + n)%nat))).
        + simpl in H5.
          simpl in H6.
          rewrite Rabs_right.
          * assert (eps/2 < eps) by lra.
            now apply Rle_lt_trans with (r2 := eps/2).
          * now apply Rle_ge.
        + now simpl in H6.
        + now simpl in H6.
      - intros.
        replace 0 with (sum_n (fun _ => 0) n0) by (rewrite sum_n_const; lra).
        apply sum_n_m_le.
        intros; apply H0.
    Qed.

  Lemma ps_union_le_ser col :
    ex_series (fun n0 : nat => ps_P (col n0)) ->
    ps_P (union_of_collection col) <=
    Series (fun n0 : nat => ps_P (col n0)).
  Proof.
    intros.
    apply ps_countable_boole_inequality; trivial.
    rewrite <- infinite_sum_infinite_sum'.
    rewrite <- is_series_Reals.
    now apply Series_correct.
  Qed.

  Theorem Borel_Cantelli (E : nat -> event dom) :
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
      rewrite lim_descending; trivial.
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
    - intros.
      now apply ps_pos.
  Qed.    

End fe.

Hint Rewrite FiniteExpectation_const FiniteExpectation_plus FiniteExpectation_scale FiniteExpectation_opp FiniteExpectation_minus: prob.
