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

  Instance pos_fun_part_proper_almostR2 : Proper (almostR2 prts eq ==> almostR2 prts eq) 
                                            (fun x x0 => nonneg (pos_fun_part x x0)).
  Proof.
    intros x1 x2 eqq1.
    apply (almostR2_sub prts eq (fun x x0 => nonneg (pos_fun_part x x0))); trivial.
    intros.
    unfold pos_fun_part; simpl.
    now rewrite H.
  Qed.

  Instance neg_fun_part_proper_almostR2 : Proper (almostR2 prts eq ==> almostR2 prts eq) 
                                            (fun x x0 => nonneg (neg_fun_part x x0)).
  Proof.
    intros x1 x2 eqq1.
    apply (almostR2_sub prts eq (fun x x0 => nonneg (neg_fun_part x x0))); trivial.
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
        {xfrf:FiniteRangeFunction x} :
    almostR2 prts eq x (const 0) ->
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

  Lemma Expectation_simple_proper_almostR2 x y
        {rvx:RandomVariable dom borel_sa x}
        {rvy:RandomVariable dom borel_sa y} 
        {xfrf:FiniteRangeFunction x}
        {yfrf:FiniteRangeFunction y} :
    almostR2 prts eq x y ->
    SimpleExpectation x = SimpleExpectation y.
  Proof.
    intros.
    generalize (SimplePosExpectation_pos_zero (rvminus x y))
    ; intros HH.
    cut_to HH.
    - unfold rvminus in HH.
      erewrite SimpleExpectation_pf_irrel in HH.
      erewrite sumSimpleExpectation' with (frf1:=xfrf) (frf2:=frfopp) in HH; trivial.
      + unfold rvopp in HH.
        erewrite (@SimpleExpectation_pf_irrel _ _ _ (rvscale (-1) y)) in HH.
        erewrite <- scaleSimpleExpectation with (frf:=yfrf) in HH.
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

  Lemma NonnegExpectation_almostR2_0 x 
        {nnf:NonnegativeFunction x} :
    almostR2 prts eq x (const 0) ->
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
        unfold BoundedNonnegativeFunction in H0.
        destruct H0 as [? [? [? [[? ?] ?]]]].
        simpl.
        assert (almostR2 prts eq x2 (const 0)).
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
    - exists (const 0); exists (rvconst _ _ 0); exists (frfconst 0).
      split.
      + unfold BoundedNonnegativeFunction.
        split.
        * apply nnfconst; lra.
        * apply nnf.
      + apply SimpleExpectation_const.
  Qed.

  Lemma Expectation_almostR2_0 x :
    almostR2 prts eq x (const 0) ->
    Expectation x = Some (Finite 0).
  Proof.
    intros.
    unfold Expectation.
    assert (almostR2 prts eq (fun omega => nonneg(pos_fun_part x omega)) (const 0)).
    {
      rewrite (pos_fun_part_proper_almostR2 _ _ H).
      unfold const; simpl.
      unfold Rmax.
      match_destr; try lra.
      reflexivity.
    } 
    assert (almostR2 prts eq (fun omega => nonneg(neg_fun_part x omega)) (const 0)).
    {
      rewrite (neg_fun_part_proper_almostR2 _ _ H).
      unfold const; simpl.
      unfold Rmax.
      match_destr; try lra.
      reflexivity.
    }
    rewrite (NonnegExpectation_almostR2_0 _ H0).
    rewrite (NonnegExpectation_almostR2_0 _ H1).
    simpl; repeat f_equal.
    lra.
  Qed.
  
  Lemma IsFiniteExpectation_proper_almostR2 rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
        {isfe1:IsFiniteExpectation rv_X1}
    :
      almostR2 prts eq rv_X1 rv_X2 ->
      IsFiniteExpectation rv_X2.
  Proof.
    intros.
    generalize (Expectation_almostR2_0 (rvminus rv_X1 rv_X2))
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
       apply almostR2_eq_subr.
       rv_unfold; intros ?.
       lra.
  Qed.

  Lemma FiniteExpectation_proper_almostR2 rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
        {isfe1:IsFiniteExpectation rv_X1}
        {isfe2:IsFiniteExpectation rv_X2}
    :
      almostR2 prts eq rv_X1 rv_X2 ->
      FiniteExpectation rv_X1 = FiniteExpectation rv_X2.

  Proof.
    intros.
    generalize (Expectation_almostR2_0 (rvminus rv_X1 rv_X2))
    ; intros HH.
    cut_to HH.
    - apply (Expectation_FiniteExpectation _ _ (isfe:=IsFiniteExpectation_minus _ _)) in HH.
      rewrite FiniteExpectation_minus in HH.
      lra.
    - rewrite H.
      apply almostR2_eq_subr.
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
    rewrite Finite_Rbar_opp in eqq1neg.
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
                 (positive_part_nnf _)
                 (positive_part_nnf _)).
    -
      rewrite <- (Finite_NonnegExpectation_le
                   ((fun x : Ts => neg_fun_part (rvmin rv_X1 rv_X2) x))
                   (rvplus (fun x : Ts => neg_fun_part rv_X1 x) (fun x : Ts => neg_fun_part rv_X2 x))
                   (negative_part_nnf _)
                   _).
      + now simpl.
      + intros a.
        unfold neg_fun_part, rvmin, rvplus, rvopp, rvscale; simpl.
        unfold Rmax, Rmin.
        destruct ( Rle_dec (rv_X1 a) (rv_X2 a))
        ; repeat match_destr; try lra.
      + rewrite NonnegExpectation_sum.
        * rewrite Finite_Rbar_opp in eqq1neg.
          rewrite Finite_Rbar_opp in eqq2neg.
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
                 (positive_part_nnf _)
                 _).
    -
      rewrite <- (Finite_NonnegExpectation_le
                   ((fun x : Ts => neg_fun_part (rvmax rv_X1 rv_X2) x))
                   (rvplus (fun x : Ts => neg_fun_part rv_X1 x) (fun x : Ts => neg_fun_part rv_X2 x))
                   (negative_part_nnf _)
                   _).
      + now simpl.
      + intros a.
        unfold neg_fun_part, rvmax, rvplus, rvopp, rvscale; simpl.
        unfold Rmax, Rmin.
        destruct ( Rle_dec (rv_X1 a) (rv_X2 a))
        ; repeat match_destr; try lra.
      + rewrite NonnegExpectation_sum.
        * rewrite Finite_Rbar_opp in eqq1neg.
          rewrite Finite_Rbar_opp in eqq2neg.
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
        {nnf : NonnegativeFunction rv_X}
        {isfe:IsFiniteExpectation rv_X} :
    0 <= FiniteExpectation rv_X.
  Proof.
    unfold FiniteExpectation.
    simpl_finite.
    generalize (NonnegExpectation_pos rv_X).
    erewrite Expectation_pos_pofrf in e.
    invcs e.
    rewrite H0.
    simpl.
    trivial.
  Qed.

  Lemma FiniteExpectation_zero_pos'
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {pofrf :NonnegativeFunction X}
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
        {pofrf :NonnegativeFunction X}
        {isfe:IsFiniteExpectation X} :
    FiniteExpectation X = 0%R ->
    almostR2 prts eq X (const 0).
  Proof.
    intros eqq1.
    apply (FiniteExpectation_zero_pos' X) in eqq1.
    exists (preimage_singleton X 0).
    split; trivial.
  Qed.

  Instance series_rv_pos
         (Xn : nat -> Ts -> R)
         (Xn_pos : forall n, NonnegativeFunction (Xn n)) 
         (is_fin_lim : 
            forall omega, is_finite (Lim_seq (sum_n (fun n => Xn n omega)))):
    NonnegativeFunction (fun omega => Lim_seq (sum_n (fun n => Xn n omega))).
  Proof.
    unfold NonnegativeFunction in *; intros.
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
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
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
          {posX: NonnegativeFunction X}
          {isfeX: IsFiniteExpectation X} :
      FiniteExpectation X = real (NonnegExpectation  X).
    Proof.
      unfold FiniteExpectation.
      unfold proj1_sig.
      match_destr.
      rewrite (Expectation_pos_pofrf) with  (nnf:=posX) in e.
      invcs e.
      rewrite H0.
      now simpl.
    Qed.
    
    Lemma IsFiniteNonnegExpectation (X:Ts->R) 
          {posX: NonnegativeFunction X}
          {isfeX: IsFiniteExpectation X} :
      is_finite (NonnegExpectation  X).
    Proof.
      red in isfeX.
      rewrite Expectation_pos_pofrf with (nnf:=posX) in isfeX.
      match_destr_in isfeX; try tauto.
      reflexivity.
   Qed.

  Lemma monotone_convergence_FiniteExpectation
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (posX: NonnegativeFunction X) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
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
        rewrite Expectation_pos_pofrf with (nnf:=posX) in isfeX.
        match_destr_in isfeX; try tauto.
      + intros n.
        now rewrite FiniteNonnegExpectation with (posX:=Xn_pos n).
    - intros.
      now apply IsFiniteNonnegExpectation.
  Qed.

Lemma Fatou_FiniteExpectation
        (Xn : nat -> Ts -> R)
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) 
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
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
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
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
        (Xn_rv : forall n, RandomVariable dom borel_sa  (Xn n))
        (isfe : forall n, IsFiniteExpectation (Xn n)) 
        (lim_rv : RandomVariable dom borel_sa 
                                 (fun omega => Lim_seq (sum_n (fun n => Xn n omega))))
        (lim_fin : forall omega,
            is_finite (Lim_seq (fun n : nat => rvsum Xn n omega)))
        (lim_fe : IsFiniteExpectation
                    (fun omega : Ts => Lim_seq (fun n : nat => rvsum Xn n omega)))
        (lim_pos : NonnegativeFunction
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

Section ExpNonNeg.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Lemma pos_fun_mult_ind_ge (X:Ts->R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (fun omega => nonneg (pos_fun_part X omega))
          (rvmult X (EventIndicator (event_ge_dec dom X 0))).
  Proof.
    intros omega.
    unfold pos_fun_part, rvmult, EventIndicator; simpl.
    unfold Rmax.
    repeat match_destr; simpl in *; lra.
  Qed.

  Lemma event_le_dec (σ:SigmaAlgebra Ts) x1 n
        {rv1:RandomVariable σ borel_sa x1} :
    dec_event (event_le σ x1 n).
  Proof.
    unfold event_ge.
    intros x; simpl.
    apply Rle_dec.
  Qed.

  Lemma neg_fun_mult_ind_le (X:Ts->R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (rvopp (fun omega => nonneg (neg_fun_part X omega)))
          (rvmult X (EventIndicator (event_le_dec dom X 0))).
  Proof.
    intros omega.
    unfold neg_fun_part, rvmult, EventIndicator; simpl.
    unfold Rmax, rvopp, rvscale.
    repeat match_destr; simpl in *; try lra.      
  Qed.

  Lemma neg_fun_mult_ind_le' (X:Ts->R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (fun omega => nonneg (neg_fun_part X omega))
          (rvopp (rvmult X (EventIndicator (event_le_dec dom X 0)))).
  Proof.
    intros omega.
    unfold neg_fun_part, rvmult, EventIndicator; simpl.
    unfold Rmax, rvopp, rvscale.
    repeat match_destr; simpl in *; try lra.      
  Qed.

  Lemma Expectation_nonneg_zero_almost_zero
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {pofrf :NonnegativeFunction X} :
    Expectation X = Some (Finite 0) ->
    almostR2 prts eq X (const 0).
  Proof.
    exists (preimage_singleton X 0).
    split.
    - now apply Expectation_zero_pos.
    - intros.
      apply H0.
  Qed.

  Lemma Expectation_mult_indicator_almost_zero
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P), Expectation (rvmult X (EventIndicator dec))
                            = Some (Finite 0)) ->
    almostR2 prts eq X (const 0).
  Proof.
    intros HH.
    generalize (HH (event_ge _ X 0) (event_ge_dec _ X 0))
    ; intros HHpos.

    assert (pos_exp:Expectation (pos_fun_part X) = Some (Finite 0)).
    {
      rewrite <- HHpos.
      apply Expectation_proper.
      apply pos_fun_mult_ind_ge.
    } 

    generalize (HH (event_le _ X 0) (event_le_dec _ X 0))
    ; intros HHneg.

    assert (neg_exp':Expectation (rvopp (neg_fun_part X)) = Some (Finite 0)).
    {
      rewrite <- HHneg.
      apply Expectation_proper.
      apply neg_fun_mult_ind_le.
    }

    assert (neg_exp:Expectation (neg_fun_part X) = Some (Finite 0)).
    {
      generalize (Expectation_opp (neg_fun_part X))
      ; intros HH2.
      rewrite neg_exp' in HH2.
      simpl in *.
      match_destr_in HH2.
      invcs HH2.
      f_equal.
      apply (f_equal Rbar_opp) in H0.
      rewrite Rbar_opp_involutive in H0.
      simpl in H0.
      now rewrite Ropp_0 in H0.
    }

    apply Expectation_nonneg_zero_almost_zero in pos_exp; try typeclasses eauto.
    apply Expectation_nonneg_zero_almost_zero in neg_exp; try typeclasses eauto.
    assert (eqq:almostR2 prts eq
                         (rvplus (fun x : Ts => pos_fun_part X x) (rvopp (fun x : Ts => neg_fun_part X x))) (const 0)).
    {
      transitivity (rvplus (Ts:=Ts) (const 0) (rvopp (const 0)))
      ; [| apply almostR2_eq_subr; intros ?; rv_unfold; lra].
      apply almostR2_eq_plus_proper; trivial.
      now apply almostR2_eq_opp_proper.
    }
    rewrite <- eqq.
    apply almostR2_eq_subr.
    apply rv_pos_neg_id.
  Qed.

  Lemma Expectation_mult_indicator_almost_nonneg_zero'
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some (Finite r) => 0 <= r
        | _ => False
        end) ->
    almostR2 prts eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0).
  Proof.               
    intros.
    apply (Expectation_mult_indicator_almost_zero (neg_fun_part X)).
    - intros P dec.
      generalize (neg_fun_mult_ind_le' X)
      ; intros eqq1.
      assert (rv_eq (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))
                    (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        intros ?.
        rv_unfold; simpl.
        unfold Rmax.
        destruct (dec_event_inter (event_le_dec dom X 0) dec a); simpl in *.
        - destruct p.
          repeat match_destr; try lra; tauto.
        - repeat match_destr; try lra.
          elim n.
          split; trivial.
          lra.
      }
      transitivity (Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        now apply Expectation_proper.
      }

      specialize (H _ (dec_event_inter (event_le_dec dom X 0) dec)).
      match_option_in H; simpl in H; try tauto.
      destruct r; try tauto.
      assert (r = 0).
      { 
        assert (eqq2:Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec)))) =Some (Finite (- r))).
        {
          now rewrite Expectation_opp, eqq; simpl.
        }
        
        rewrite <- H0 in eqq2.
        assert (nnf:NonnegativeFunction (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))).
        {
          typeclasses eauto.
        } 
        rewrite (Expectation_pos_pofrf _ (nnf:=nnf)) in eqq2.
        invcs eqq2.
        generalize (NonnegExpectation_pos (rvmult (fun x : Ts => Rmax (- X x) 0) (EventIndicator dec)))
        ; intros HH2.
        simpl in HH2.
        match_destr_in HH2.
        invcs H2.
        lra.
      }
      rewrite Expectation_opp, eqq, H1.
      simpl.
      now rewrite Ropp_0.
  Qed.

  Definition almostR2_alt {Td} (R:Td->Td->Prop) (r1 r2:Ts -> Td)
    := almost prts (fun x => R (r1 x) (r2 x)).

  Lemma almostR2_almostR2_alt {Td} (R:Td->Td->Prop) (r1 r2:Ts -> Td)
    : almostR2 prts R r1 r2 <-> almostR2_alt R r1 r2.
  Proof.
    split; intros [p [? pH]]
    ; exists p; split; trivial.
  Qed.

  Lemma neg_fun_part_eq_0_nonneg
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0) ->
    NonnegativeFunction X.
  Proof.
    intros ??.
    rewrite (rv_pos_neg_id X x).
    unfold rvplus, rvopp, rvscale.
    rewrite H.
    rv_unfold; simpl.
    field_simplify.
    apply Rmax_r.
  Qed.

  Lemma neg_fun_part_eq_0_nonneg_almost
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    almostR2 prts eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0) ->
    almostR2 prts Rle (const 0) X.
  Proof.
    intros [ p[? pH]].
    exists p; split; trivial.
    intros x px.
    specialize (pH x px).
    rewrite (rv_pos_neg_id X x).

    unfold rvplus, rvopp, rvscale.
    rewrite pH.
    rv_unfold.
    simpl.
    field_simplify.
    apply Rmax_r.
  Qed.

  Lemma Expectation_mult_indicator_almost_nonneg'
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some (Finite r) => 0 <= r
        | _ => False
        end) ->
    almostR2 prts Rle (const 0) X.
  Proof.
    intros.
    apply neg_fun_part_eq_0_nonneg_almost; trivial.
    now apply Expectation_mult_indicator_almost_nonneg_zero'.
  Qed.      

  Lemma Expectation_mult_indicator_almost_nonneg_zero
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some r => Rbar_le 0 r
        | _ => False
        end) ->
    almostR2 prts eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0).
  Proof.               
    intros.
    apply (Expectation_mult_indicator_almost_zero (neg_fun_part X)).
    - intros P dec.
      generalize (neg_fun_mult_ind_le' X)
      ; intros eqq1.
      assert (rv_eq (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))
                    (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        intros ?.
        rv_unfold; simpl.
        unfold Rmax.
        destruct (dec_event_inter (event_le_dec dom X 0) dec a); simpl in *.
        - destruct p.
          repeat match_destr; try lra; tauto.
        - repeat match_destr; try lra.
          elim n.
          split; trivial.
          lra.
      }
      transitivity (Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        now apply Expectation_proper.
      }

      specialize (H _ (dec_event_inter (event_le_dec dom X 0) dec)).
      match_option_in H; simpl in H; try tauto.
      destruct r; try tauto.
      + assert (r = 0).
        { 
          assert (eqq2:Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec)))) =Some (Finite (- r))).
          {
            now rewrite Expectation_opp, eqq; simpl.
          }
          
          rewrite <- H0 in eqq2.
          assert (nnf:NonnegativeFunction (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))).
          {
            typeclasses eauto.
          } 
          rewrite (Expectation_pos_pofrf _ (nnf:=nnf)) in eqq2.
          invcs eqq2.
          generalize (NonnegExpectation_pos (rvmult (fun x : Ts => Rmax (- X x) 0) (EventIndicator dec)))
          ; intros HH2.
          simpl in HH2.
          match_destr_in HH2.
          invcs H2.
          lra.
        }
        rewrite Expectation_opp, eqq, H1.
        simpl.
        now rewrite Ropp_0.
      + assert (eqq2:Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec)))) = Some (m_infty)).
        {
          now rewrite Expectation_opp, eqq; simpl.
        }
        rewrite <- H0 in eqq2.
        assert (nnf:NonnegativeFunction (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))).
        {
          typeclasses eauto.
        } 
        rewrite (Expectation_pos_pofrf _ (nnf:=nnf)) in eqq2.
        invcs eqq2.
        generalize (NonnegExpectation_pos (rvmult (fun x : Ts => Rmax (- X x) 0) (EventIndicator dec)))
        ; intros HH2.
        simpl in HH2.
        match_destr_in HH2.
        invcs H2.
        lra.
  Qed.

  Lemma Expectation_mult_indicator_almost_nonneg
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some r => Rbar_le 0 r
        | _ => False
        end) ->
    almostR2 prts Rle (const 0) X.
  Proof.
    intros.
    apply neg_fun_part_eq_0_nonneg_almost; trivial.
    now apply Expectation_mult_indicator_almost_nonneg_zero.
  Qed.      


Lemma Expectation_EventIndicator:
  forall {Ts : Type} {dom : SigmaAlgebra Ts} {Prts : ProbSpace dom} {P : event dom}
    (dec : forall x : Ts, {P x} + {~ P x}), Expectation (EventIndicator dec) = Some (Finite (ps_P P)).
Proof.
  intros.
  erewrite Expectation_simple.
  now rewrite SimpleExpectation_EventIndicator.
Qed.

Lemma IsFiniteExpectation_parts f :
  IsFiniteExpectation prts f ->
  IsFiniteExpectation prts (pos_fun_part f) /\
  IsFiniteExpectation prts (neg_fun_part f).
Proof.
  unfold IsFiniteExpectation, Expectation.
  intros.
  assert (pp:NonnegExpectation (pos_fun_part (pos_fun_part f)) = 
          NonnegExpectation (pos_fun_part f)).
  {
    apply NonnegExpectation_ext.
    intro x.
    rv_unfold; simpl.
    unfold Rmax.
    do 2 match_destr; lra.
  }    
  assert (pn:NonnegExpectation (pos_fun_part (neg_fun_part f)) = 
          NonnegExpectation (neg_fun_part f)).
  {
    apply NonnegExpectation_ext.
    intro x.
    rv_unfold; simpl.
    unfold Rmax.
    do 2 match_destr; lra.
  }    
  assert (np:NonnegExpectation (neg_fun_part (pos_fun_part f)) =  0).
  {
    rewrite <- NonnegExpectation_const0.
    apply NonnegExpectation_ext.    
    intro x.
    rv_unfold; simpl.
    unfold Rmax.
    do 2 match_destr; lra.
  }    
  assert (nn:NonnegExpectation (neg_fun_part (neg_fun_part f)) =  0).
  {
    rewrite <- NonnegExpectation_const0.
    apply NonnegExpectation_ext.        
    intro x.
    rv_unfold; simpl.
    unfold Rmax.
    do 2 match_destr; lra.
  }    
  rewrite pp, np, pn, nn.
  match_case_in H; intros.
  - rewrite H0 in H.
    match_case_in H; intros.
    + rewrite H1 in H0.
      unfold Rbar_minus', Rbar_plus' in H0.
      match_case_in H0; intros.
      * split; [now simpl |].
        rewrite H2 in H0.
        match_case_in H0; intros.
        -- unfold Rbar_opp in H3.
           match_case_in H3; intros.
           ++ now simpl.
           ++ rewrite H4 in H0.
              discriminate.
           ++ rewrite H4 in H0.
              discriminate.
        -- rewrite H3 in H0.
           discriminate.
        -- rewrite H3 in H0.
           discriminate.
      * rewrite H2 in H0.
        match_destr_in H0.
      * rewrite H2 in H0.
        match_destr_in H0.
    + now rewrite H1 in H.
    + now rewrite H1 in H.
  - now rewrite H0 in H.
Qed.



Global Instance IsFiniteExpectation_indicator f {P} (dec:dec_pre_event P)
       {rv : RandomVariable dom borel_sa f}:
  sa_sigma P ->
  IsFiniteExpectation prts f ->
  IsFiniteExpectation prts (rvmult f (EventIndicator dec)).
Proof.
  intros.
  destruct (IsFiniteExpectation_parts f H0).
  generalize (rv_pos_neg_id f); intros.
  rewrite H3.
  assert (rv_eq
            (rvmult
               (rvplus (pos_fun_part f) (rvopp (neg_fun_part f)))
               (EventIndicator dec))
            (rvplus (rvmult (pos_fun_part f) (EventIndicator dec))
                    (rvopp (rvmult (neg_fun_part f) (EventIndicator dec))))).
  {
    intro x.
    rv_unfold; simpl.
    lra.
  }
  assert (RandomVariable dom borel_sa (EventIndicator dec)) by now apply EventIndicator_pre_rv.
  apply (IsFiniteExpectation_proper _ _ _ H4).
  apply IsFiniteExpectation_plus.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := pos_fun_part f); trivial.
    + apply IsFiniteExpectation_const.
    + intro x.
      rv_unfold; simpl.
      apply Rmult_le_pos.
      * apply Rmax_r.
      * match_destr; lra.
    + intro x.
      rv_unfold; simpl.
      destruct (dec x).
      * lra.
      * rewrite Rmult_0_r.
        apply Rmax_r.
  - apply IsFiniteExpectation_opp.
    apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := neg_fun_part f); trivial.
    + apply IsFiniteExpectation_const.
    + intro x.
      rv_unfold; simpl.
      apply Rmult_le_pos.
      * apply Rmax_r.
      * match_destr; lra.
    + intro x.
      rv_unfold; simpl.
      destruct (dec x).
      * lra.
      * rewrite Rmult_0_r.
        apply Rmax_r.
  Qed.


    Lemma Expectation_mult_indicator_almost_le
        (X1 X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa X1} 
        {rv2 : RandomVariable dom borel_sa X2}
        {isfe2: IsFiniteExpectation prts X2} :      
    (forall P (dec:dec_event P),
        match Expectation (rvmult X1 (EventIndicator dec)), Expectation (rvmult X2 (EventIndicator dec)) with
        | Some r1, Some r2 => Rbar_le r1 r2
        | _, _ => False
        end) ->
    almostR2 prts Rle X1 X2.
    Proof.
      intros.
      pose (An:=fun n => event_ge dom (rvminus X1 X2) (/ (INR (S n)))).
      pose (Dn:= fun n => (event_ge_pre_dec dom (rvminus X1 X2) (/ (INR (S n))))).
      pose (In:=fun n => EventIndicator (Dn n)).
      assert (eqq1: forall n, ps_P (An n) = 0).
      { 
        intros n.
        assert (npos: 0 < / INR (S n)).
        {
          apply Rinv_0_lt_compat.
          apply lt_0_INR.
          lia.
        } 
        specialize (H _ (Dn n)).
        match_case_in H; intros.
        - rewrite H0 in H.
          match_case_in H; intros.
          + rewrite H1 in H.
            assert (eqq3:rv_eq (rvmult (rvplus X2 (const (/ (INR (S n))))) (In n))
                               (rvplus (rvmult X2 (In n)) (rvmult (const (/ INR (S n))) (In n)))).
            {
              rv_unfold.
              intros ?; lra.
            }
            assert (eqq: match Expectation (rvplus (rvmult X2 (In n))
                                                   (rvmult (const (/ (INR (S n)))) (In n))) with
                         | Some r2p => Rbar_le r2p r
                         | _ => True
                         end).
            {
              match_case; intros.
              apply Expectation_le with (rv_X1 := rvplus (rvmult  X2 (In n)) (rvmult (const (/ (INR (S n)))) (In n)))
                                        (rv_X2 := rvmult X1 (In n)); trivial.
              unfold In, Dn.
              intro x.
              rv_unfold.
              match_destr; try lra.
              do 2 rewrite Rmult_1_r.
              destruct e; lra.
            }
            generalize (Expectation_sum_isfin_fun2 (rvmult X2 (In n))
                                                   (rvmult (const (/ INR (S n))) (In n))); intros.
            assert (Expectation  (rvmult (const (/ INR (S n))) (In n)) =
                    Some (Finite ((/ INR (S n)) * ps_P (An n)))).
            {
              assert (rv_eq (rvmult (const (/ INR (S n))) (In n))
                            (rvscale (/ INR (S n)) (In n))) by
                  (intro x; rv_unfold; lra).
              rewrite (Expectation_ext H3).
              generalize (Expectation_scale (/ INR (S n)) (In n)); intros.
              cut_to H4.
              - generalize (Expectation_EventIndicator (Dn n)); intros.
                unfold In in H4.
                now rewrite H5 in H4.
              - now apply Rgt_not_eq.
            }
            specialize (H2 (/ INR (S n) * (ps_P (An n))) H3).
            unfold In in H2.
            simpl in H1.
            simpl in H2.
            rewrite H1 in H2.
            unfold In in eqq.
            simpl in eqq.
            rewrite H2 in eqq.
            generalize (Rbar_le_trans _ _ _ eqq H); intros.
            replace (r0) with (Rbar_plus r0 0) in H4 at 2 by apply Rbar_plus_0_r.
            assert (isfex2: IsFiniteExpectation prts (rvmult X2 (In n))).
            {
              unfold In.
              apply IsFiniteExpectation_indicator; trivial.
              - apply sa_le_ge.
                intros.
                apply rv_measurable.
                typeclasses eauto.
            }
            assert (is_finite r0).
            {
              unfold IsFiniteExpectation in isfex2.
              unfold In in isfex2.
              simpl in H1; simpl in isfex2.
              rewrite H1 in isfex2.
              destruct r0; try tauto.
              now simpl.
            }
            rewrite <- H5 in H4.
            simpl in H4.
            apply Rplus_le_reg_l in H4.
            replace (0) with ((/ INR (S n)) * 0) in H4 by lra.
            simpl in H4.
            apply Rmult_le_reg_l in H4.
            apply antisymmetry; trivial.
            apply ps_pos.
            apply npos.
          + now rewrite H1 in H.
       - now rewrite H0 in H.
      }
      apply almost_alt_eq.
      exists (union_of_collection An).
      split.
      - apply (ps_zero_countable_union _ _ eqq1)
        ; intros HH.
      - intros x xgt.
        apply Rnot_le_gt in xgt.
        simpl.
        assert (pos:0 < X1 x - X2 x) by lra.
        destruct (archimed_cor1 _ pos) as [N [Nlt Npos]].
        exists N.
        rv_unfold.
        apply Rle_ge.
        assert (le1:/ (INR (S N)) <= / (INR N)).
        {
          apply Rinv_le_contravar.
          - now apply lt_0_INR.
          - rewrite S_INR; lra.
        }
        rewrite le1.
        rewrite Nlt.
        lra.
   Qed.
      

End ExpNonNeg.
