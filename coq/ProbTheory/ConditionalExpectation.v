Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Export RandomVariableLpR RandomVariableL2 OrthoProject.
Require Import quotient_space.
Require Import RbarExpectation.

Require Import Event.
Require Import Almost DVector.
Require Import utils.Utils.
Require Import List.
Require Import NumberIso.
Require Import PushNeg.


Set Bullet Behavior "Strict Subproofs". 

Section is_cond_exp.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  (* The universal property that conditional expectations satisfy.
     This section shows its properties (including uniqueness).
     We later show existence (under reasonable conditions)
   *)
  
  Definition is_conditional_expectation
             (dom2 : SigmaAlgebra Ts)
             (f : Ts -> R)
             (ce : Ts -> Rbar)           
             {rvf : RandomVariable dom borel_sa f}
             {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    := forall P (dec:dec_pre_event P),
      sa_sigma dom2 P ->
      Expectation (rvmult f (EventIndicator dec)) =
      Rbar_Expectation (Rbar_rvmult ce (EventIndicator dec)).
  
  Context {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Theorem is_conditional_expectation_id
          (f : Ts -> R)
          {rvf : RandomVariable dom borel_sa f}
          {rvf2 : RandomVariable dom2 borel_sa f} :
    is_conditional_expectation dom2 f (fun x => Finite (f x)).
  Proof.
    unfold is_conditional_expectation; intros.
    unfold Rbar_rvmult; simpl.
    rewrite Expectation_Rbar_Expectation.
    reflexivity.
  Qed.

    Lemma is_conditional_expectation_independent_sa
          (f : Ts -> R) 
          {rv:RandomVariable dom borel_sa f} 
          {isfe : IsFiniteExpectation prts f} :
      independent_sas prts (pullback_rv_sub _ _ _ rv) sub ->
      is_conditional_expectation dom2 f (const (FiniteExpectation prts f)).
    Proof.
      intros indep_sub.
      unfold is_conditional_expectation.
      intros.
      assert (RandomVariable dom borel_sa (EventIndicator dec)).
      {
        apply RandomVariable_sa_sub; trivial.
        now apply EventIndicator_pre_rv.
      }
      assert (indep_ind: independent_rvs prts borel_sa borel_sa f (EventIndicator dec)).
      {
        apply independent_rv_sas.
        revert indep_sub.
        apply independent_sas_sub_proper.
        - now apply sa_equiv_sub.
        - apply pullback_rv_sub.
          now apply EventIndicator_pre_rv.
      }
      assert (IsFiniteExpectation prts (EventIndicator dec)).
      {
        apply IsFiniteExpectation_simple; trivial.
        typeclasses eauto.
      }
      assert (isfexy : IsFiniteExpectation prts (rvmult f (EventIndicator dec))).
      {
        apply IsFiniteExpectation_indicator; trivial.
        now apply sub.
      }
      generalize (independent_expectation_prod prts f (EventIndicator dec) indep_ind); intros.
      rewrite FiniteExpectation_Expectation with (isfe0 := isfexy).
      rewrite H2.
      assert (rv_eq
                 (Rbar_rvmult (fun x : Ts => const (FiniteExpectation prts f) x)
                              (fun x : Ts => EventIndicator dec x))
                 (rvscale (FiniteExpectation prts f)
                                              (EventIndicator dec))).
      {
        intro x.
        unfold Rbar_rvmult.
        simpl.
        rewrite Rbar_finite_eq.
        now rv_unfold.
      }
      rewrite (Rbar_Expectation_ext H3).
      rewrite <- Expectation_Rbar_Expectation.
      rewrite FiniteExpectation_Expectation with (isfe0 := IsFiniteExpectation_scale prts (FiniteExpectation prts f) _ ).
      f_equal.
      rewrite Rbar_finite_eq.
      now rewrite FiniteExpectation_scale.
   Qed.

  Theorem is_conditional_expectation_Expectation
        (f : Ts -> R)
        (ce : Ts -> Rbar)           
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce} :
    is_conditional_expectation dom2 f ce ->
    Expectation f = Rbar_Expectation ce.
  Proof.
    intros HH.
    specialize (HH pre_Ω (dsa_dec dsa_Ω) sa_all).
    etransitivity.
    - etransitivity; [| apply HH].
      apply Expectation_ext.
      intros ?.
      rv_unfold.
      simpl; lra.
    - apply Rbar_Expectation_ext.
      intros ?.
      rv_unfold.
      unfold Rbar_rvmult.
      simpl.
      now rewrite Rbar_mult_1_r.
  Qed.

  Lemma is_conditional_expectation_FiniteExpectation
        (f : Ts -> R)
        (ce : Ts -> Rbar)           
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce} :
    is_conditional_expectation dom2 f ce ->
    IsFiniteExpectation prts f <-> Rbar_IsFiniteExpectation prts ce.
  Proof.
    unfold IsFiniteExpectation, Rbar_IsFiniteExpectation.
    intros HH.
    now erewrite (is_conditional_expectation_Expectation) by eauto.
  Qed.

  (* is_conditional_expectation is proper up to almost *)
  Theorem is_conditional_expectation_proper
        (f1 f2 : Ts -> R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf1 : RandomVariable dom borel_sa f1}
        {rvf2 : RandomVariable dom borel_sa f2}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
    : almostR2 prts eq f1 f2 ->
      almostR2 prts eq ce1 ce2 ->
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2.
  Proof.
    unfold is_conditional_expectation
    ; intros eqq1 eqq2 is1 P dec saP.
    specialize (is1 P dec saP).
    etransitivity.
    - etransitivity; [| apply is1].
      apply Expectation_almostR2_proper.
      + apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        now apply sub.
      + apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        now apply sub.
      + apply almostR2_eq_mult_proper; trivial.
        * now symmetry.
        * reflexivity.
    - apply Rbar_Expectation_almostR2_proper.
      + apply Rbar_rvmult_rv; trivial.
        * eapply RandomVariable_sa_sub; eauto.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + apply Rbar_rvmult_rv; trivial.
        * eapply RandomVariable_sa_sub; eauto.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + apply almostR2_eq_Rbar_mult_proper; trivial.
        reflexivity.
  Qed.

  (* is_conditional_expectation is also almost unique, as long as the 
     input function is finite expectation, or is nonnegative.
     Failing that, if both candidates are almost finite, then the result still holds.
   *)
  
  Lemma is_conditional_expectation_nneg_le
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        {nnf : NonnegativeFunction f}
        {nnf1 : Rbar_NonnegativeFunction ce1}
        {nnf2 : Rbar_NonnegativeFunction ce2}
    : is_conditional_expectation dom2 f ce1 ->
      is_conditional_expectation dom2 f ce2 ->
      almostR2 (prob_space_sa_sub prts sub) Rbar_le ce1 ce2.
  Proof.
    unfold is_conditional_expectation; intros isce1 isce2.

    pose (G := fun x:R => pre_event_inter (fun omega => Rbar_gt (ce1 omega) (ce2 omega)) (fun omega => Rbar_gt x (ce2 omega))).
    assert (sa_G : forall x:R, sa_sigma _ (G x)).
    {
      intros x.
      unfold G.
      unfold pre_event_inter.
      apply (sa_proper _ 
                       (fun x0 : Ts => (Rbar_gt ((Rbar_rvminus ce1 (Rbar_finite_part ce2)) x0) 0) /\ Rbar_lt (ce2 x0) x )).
      - intro z.
        unfold Rbar_rvminus, Rbar_rvopp, Rbar_finite_part.
        split; intros.
        + destruct H.
          split; try easy.
          unfold Rbar_rvplus in H.
          assert (is_finite (ce2 z)).
          * eapply bounded_is_finite.
            apply nnf2.
            apply Rbar_lt_le.
            apply H0.
          * rewrite <- H1 in H |- *.
            unfold Rbar_opp in H.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (ce2 z)) in H.
            rewrite Rbar_plus_0_l in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
        + destruct H.
          unfold Rbar_gt in H0.
          assert (is_finite (ce2 z)).
          * eapply bounded_is_finite.
            apply nnf2.
            apply Rbar_lt_le.
            apply H0.
          * split; try easy.
            unfold Rbar_rvplus.
            rewrite <- H1 in H |- *.
            unfold Rbar_opp.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (- ce2 z)) in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
      - apply sa_inter.
        + apply Rbar_sa_le_gt; intros.
          apply Rbar_plus_measurable.
          * typeclasses eauto.
          * apply rv_Rbar_measurable.
            apply Rbar_rvopp_rv.
            apply Real_Rbar_rv.
            apply measurable_rv.
            now apply Rbar_finite_part_meas.
        + apply Rbar_sa_le_lt.
          intros.
          now apply rv_Rbar_measurable.
    }

    pose (IG := fun x:R => EventIndicator (classic_dec (G x))).

    assert (nneg12I:forall x:R, Rbar_NonnegativeFunction (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun omega : Ts => IG x omega))).
    {
      intros x omega.
      unfold IG, classic_dec; simpl.
      unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp; simpl.
      rv_unfold.
      destruct (excluded_middle_informative (G x omega)).
      - rewrite Rbar_mult_1_r.
        destruct g.
        destruct (ce1 omega); destruct (ce2 omega); simpl in *; try tauto.
        lra.
      - rewrite Rbar_mult_0_r.
        lra.
    } 
    
    assert (eqq1:forall x, Rbar_NonnegExpectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (IG x)) =
                           Rbar_minus (Rbar_NonnegExpectation (Rbar_rvmult ce1 (IG x)))
                                      (Rbar_NonnegExpectation (Rbar_rvmult ce2 (IG x)))).
    {
      intros x.

      generalize (@Rbar_NonnegExpectation_minus_bounded2 _ _ prts (Rbar_rvmult ce1 (IG x)) (Rbar_rvmult ce2 (IG x))); intros HH.
      cut_to HH.
      - unfold IG in HH.
        specialize (HH _ (Rabs x) (Rabs_pos _)).
        cut_to HH.
        + specialize (HH _).
          assert ( nnf12 : Rbar_NonnegativeFunction
                             (Rbar_rvminus (Rbar_rvmult ce1 (IG x))
                                           (Rbar_rvmult ce2 (IG x)))).
          {
            intros a.
            unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, IG, EventIndicator; simpl.
            destruct (classic_dec (G x) a); simpl.
            - repeat rewrite Rbar_mult_1_r.
              destruct g as [??].
              destruct (ce1 a); destruct (ce2 a); simpl in *; lra.
            - repeat rewrite Rbar_mult_0_r; simpl.
              lra.
          }
          specialize (HH nnf12).
          unfold IG.
          rewrite <- HH.
          eapply Rbar_NonnegExpectation_ext.
          intros a.
          unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, EventIndicator; simpl.
          match_destr.
          * now repeat rewrite Rbar_mult_1_r.
          * repeat rewrite Rbar_mult_0_r.
            simpl; f_equal; lra.
        + intros ?.
          unfold G.
          unfold Rbar_rvmult, EventIndicator, const; simpl.
          match_destr.
          * destruct p.
            destruct (ce2 a); simpl in *; try tauto.
            -- field_simplify.
               eapply Rle_trans; [| apply RRle_abs].
               now left.
            -- destruct (Rle_dec 0 1); try lra.
               destruct (Rle_lt_or_eq_dec 0 1 r); try lra.
               now simpl.
          * rewrite Rbar_mult_0_r.
            simpl.
            apply Rabs_pos.
      - apply Rbar_rvmult_rv; trivial.
        + eapply RandomVariable_sa_sub; eauto.
        + apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      - apply Rbar_rvmult_rv; trivial.
        + eapply RandomVariable_sa_sub; eauto.
        + apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
    }
    
    assert (eqq2: forall x, Rbar_NonnegExpectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (IG x)) = 0).
    {
      intros.
      rewrite eqq1.
      generalize (isce1 (G x) (classic_dec (G x)) (sa_G x))
      ; intros HH1.
      generalize (isce2 (G x) (classic_dec (G x)) (sa_G x))
      ; intros HH2.
      rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)) in HH1.
      rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)) in HH2.
      rewrite (Expectation_pos_pofrf _ (nnf:=_)) in HH1.
      rewrite (Expectation_pos_pofrf _ (nnf:=_)) in HH2.
      invcs HH1.
      invcs HH2.
      unfold IG.
      rewrite <- H0, <- H1.
      apply Rbar_minus_eq_0.
    }

    assert (psG0:forall x, ps_P (ProbSpace:=((prob_space_sa_sub prts sub))) (exist _ (G x) (sa_G x)) = 0).
    {
      intros x.
      specialize (eqq2 x).
      assert (Rbar_NonnegExpectation_zero_pos':almostR2 prts eq (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => IG x x0)) (const 0)).
      {
        apply Rbar_Expectation_nonneg_zero_almost_zero; trivial.
        - apply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _) (Rbar_rvminus (Rbar_rvmult ce1 (IG x))
                                                                                             (Rbar_rvmult ce2 (IG x)))).
          + intros ?.
            unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, Rbar_rvmult; simpl.
            unfold IG, EventIndicator; simpl.
            match_destr.
            * now repeat rewrite Rbar_mult_1_r.
            * repeat rewrite Rbar_mult_0_r.
              simpl.
              f_equal; lra.
          + apply Rbar_rvplus_rv.
            * apply Rbar_rvmult_rv.
              -- eapply RandomVariable_sa_sub; eauto.
              -- apply borel_Rbar_borel.
                 apply EventIndicator_pre_rv.
                 now apply sub.
            * apply Rbar_rvopp_rv.
              apply Rbar_rvmult_rv.
              -- eapply RandomVariable_sa_sub; eauto.
              -- apply borel_Rbar_borel.
                 apply EventIndicator_pre_rv.
                 now apply sub.
        - now rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)), eqq2.
      }

      destruct Rbar_NonnegExpectation_zero_pos' as [P [pone pH]].
      unfold const in pH.
      unfold Rbar_rvmult, IG, EventIndicator in pH.
      apply NNPP.
      intros neq.
      assert (HH1:ps_P  (ProbSpace:=prts) (event_inter P (event_sa_sub sub (exist (sa_sigma _) (G x) (sa_G x)))) <> 0).
      {
        rewrite ps_inter_l1; trivial.
      } 
      destruct (zero_prob_or_witness _ HH1) as [a [Pa Ga]]; simpl in *.
      specialize (pH _ Pa).
      match_destr_in pH; try tauto.
      rewrite Rbar_mult_1_r in pH.
      destruct Ga as [??].
      unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp in pH.
      destruct (ce1 a); destruct (ce2 a); simpl in *; try (invcs pH; lra).
    }

    generalize (is_lim_ascending (prob_space_sa_sub prts sub) (fun n => exist _ _ (sa_G (INR n))))
    ; intros HH.
    cut_to HH.
    - apply (is_lim_seq_ext _ (fun _ => 0)) in HH.
      + apply is_lim_seq_unique in HH.
        rewrite Lim_seq_const in HH.
        assert (eqq3:pre_event_equiv (union_of_collection (fun n : nat => exist (sa_sigma _) (G (INR n)) (sa_G (INR n))))
                                     (fun omega : Ts => Rbar_gt (ce1 omega) (ce2 omega))).
        {
          intros a.
          split; simpl.
          - now intros [?[??]].
          - unfold G.
            intros.
            exists (Z.to_nat (up (ce2 a))).
            split; trivial.
            assert (isf:is_finite (ce2 a)).
            {
              generalize (nnf2 a); intros ?.
              destruct (ce2 a).
              - reflexivity.
              - destruct (ce1 a); simpl in *; tauto.
              - simpl in H0; tauto.
            }
            rewrite <- isf.
            simpl.
            rewrite INR_up_pos.
            * apply archimed.
            * generalize (nnf2 a); intros HH2.
              rewrite <- isf in HH2; simpl in HH2.
              lra.
        } 
        destruct (sa_proper dom2 _ _ eqq3) as [sa1 _].
        cut_to sa1.
        * rewrite (ps_proper _ (exist _ _ sa1)) in HH by (now red).

          generalize (ps_complement (prob_space_sa_sub prts sub)
                                    (exist _ _ sa1))
          ; intros eqq4.
          invcs HH.
          simpl in *.
          rewrite <- H0 in eqq4.
          field_simplify in eqq4.
          eexists.
          split; [apply eqq4|].
          intros a; simpl.
          unfold pre_event_complement.
          unfold Rbar_gt.
          intros.
          now apply Rbar_not_lt_le.
        * apply sa_sigma_event_pre.
      + trivial.
    - intros ??.
      unfold G.
      intros [??].
      split; trivial.
      unfold Rbar_gt in *.
      eapply Rbar_lt_le_trans; try eapply H0.
      apply le_INR; lia.
  Qed.

  Local Existing Instance Rbar_le_part.
  
  Theorem is_conditional_expectation_nneg_unique
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        {nnf : NonnegativeFunction f}
        {nnf1 : Rbar_NonnegativeFunction ce1}
        {nnf2 : Rbar_NonnegativeFunction ce2}
    : is_conditional_expectation dom2 f ce1 ->
      is_conditional_expectation dom2 f ce2 ->
      almostR2 (prob_space_sa_sub prts sub) eq ce1 ce2.
  Proof.
    intros.
    apply antisymmetry
    ; eapply is_conditional_expectation_nneg_le; eauto.
  Qed.

  Lemma is_conditional_expectation_almostfinite_le
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        (isf2:almost (prob_space_sa_sub prts sub) (fun a => is_finite (ce2 a))) :
    is_conditional_expectation dom2 f ce1 ->
    is_conditional_expectation dom2 f ce2 ->
    almostR2 (prob_space_sa_sub prts sub) Rbar_le ce1 ce2.
  Proof.
    unfold is_conditional_expectation; intros isce1 isce2.

    pose (G := fun x:R => pre_event_inter (fun omega => Rbar_gt (ce1 omega) (ce2 omega))
                                          (fun omega => Rbar_ge x ((Rbar_rvabs ce2) omega))).
    assert (sa_G : forall x:R, sa_sigma _ (G x)).
    {
      intros x.
      unfold G.
      unfold pre_event_inter.
      apply (sa_proper _ 
                       (fun x0 : Ts => (Rbar_gt ((Rbar_rvminus ce1 (Rbar_finite_part ce2)) x0) 0) /\ Rbar_le (Rbar_abs (ce2 x0)) x )).
      - intro z.
        unfold Rbar_rvminus, Rbar_rvopp, Rbar_finite_part.
        split; intros.
        + destruct H.
          split; try easy.
          unfold Rbar_rvplus in H.
          assert (is_finite (ce2 z)).
          * destruct (ce2 z).
            -- now unfold is_finite.
            -- now simpl in H0.
            -- now simpl in H0.
          * rewrite <- H1 in H |- *.
            unfold Rbar_opp in H.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (ce2 z)) in H.
            rewrite Rbar_plus_0_l in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
        + destruct H.
          unfold Rbar_gt in H0.
          assert (is_finite (ce2 z)).
          * unfold Rbar_rvabs in H0.
            destruct (ce2 z).
            -- now unfold is_finite.
            -- now simpl in H0.
            -- now simpl in H0.
          * split; try easy.
            unfold Rbar_rvplus.
            rewrite <- H1 in H |- *.
            unfold Rbar_opp.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (- ce2 z)) in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
      - apply sa_inter.
        + apply Rbar_sa_le_gt; intros.
          apply Rbar_plus_measurable.
          * typeclasses eauto.
          * apply rv_Rbar_measurable.
            apply Rbar_rvopp_rv.
            apply Real_Rbar_rv.
            apply measurable_rv.
            now apply Rbar_finite_part_meas.
        + apply Rbar_Rabs_measurable.
          now apply rv_Rbar_measurable.
    }

    assert (nnf12: forall x,
               Rbar_NonnegativeFunction (Rbar_rvmult (Rbar_rvminus ce1 ce2) (EventIndicator (classic_dec (G x))))).
    {
      intros x a.
      unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, EventIndicator; simpl.
      destruct (classic_dec (G x) a); simpl.
      - rewrite Rbar_mult_1_r.
        unfold G, Rbar_rvabs in g.
        destruct g as [??].
        destruct (ce1 a); destruct (ce2 a); simpl in *; try tauto.
        lra.
      - now rewrite Rbar_mult_0_r.
    } 

    assert (isfe2abs : forall x,
               match Rbar_Expectation (Rbar_rvabs (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x))))) with
               | Some (Finite _) => True
               | _ => False
               end).
    {
      intros x.
      rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)).
      generalize (Rbar_NonnegExpectation_le (nnf2:=(@nnfconst Ts (Rabs x) (Rabs_pos x))) (Rbar_rvabs (Rbar_rvmult ce2 (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0))) (const (Rabs x)))
      ; intros HH1.
      cut_to HH1.
      - simpl in *.
        rewrite Rbar_NonnegExpectation_const in HH1.
        generalize (Rbar_NonnegExpectation_pos
                      (Rbar_rvabs (Rbar_rvmult ce2 (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0))))
        ; intros HH2.
        simpl in *.
        match_destr.
      - intros a.
        unfold Rbar_rvabs, Rbar_rvmult, const, EventIndicator.
        match_destr.
        + rewrite Rbar_mult_1_r.
          destruct g as [??].
          unfold Rbar_rvabs in *.
          destruct (Rbar_abs (ce2 a)); simpl in *; try tauto.
          etransitivity; try eapply H0.
          apply RRle_abs.
        + rewrite Rbar_mult_0_r; simpl.
          rewrite Rabs_R0.
          apply Rabs_pos.
    } 

    assert (isfe2 : forall x,
               match Rbar_Expectation (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x)))) with
               | Some (Finite _) => True
               | _ => False
               end).
    {
      intros.
      apply Rbar_Expectation_abs_then_finite.
      apply isfe2abs.
    } 

    assert (isfe1 : forall x,
               match Rbar_Expectation (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x)))) with
               | Some (Finite _) => True
               | _ => False
               end).
    {
      intros a.
      specialize (isfe2 a).
      specialize (isce1 _ (classic_dec _) (sa_G a)).
      specialize (isce2 _ (classic_dec _) (sa_G a)).
      rewrite <- isce1.
      now rewrite <- isce2 in isfe2.
    } 

    assert (eqq0:forall x, rv_eq (Rbar_rvmult (Rbar_rvminus ce1 ce2) (EventIndicator (classic_dec (G x))))
                                 ((Rbar_rvminus (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x))))
                                                (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x))))))).
    {
      intros x a.
      unfold Rbar_rvminus, Rbar_rvmult, Rbar_rvplus, Rbar_rvopp.
      rewrite Rbar_mult_plus_distr_fin_r.
      now rewrite Rbar_mult_opp_l.
    } 
    
    assert (eqqlin:forall x, Rbar_Expectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (EventIndicator (classic_dec (G x)))) =

                        match Rbar_Expectation (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x)))),
                              Rbar_Expectation (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x)))) with
                        | Some exp1, Some exp2 => Some (Rbar_minus exp1 exp2)
                        | _, _ => None
                        end).
    {
      intros x.

      transitivity (Rbar_Expectation (Rbar_rvminus (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x))))
                                                   (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x)))))).
      {
        now apply Rbar_Expectation_ext.
      }
      specialize (isfe1 x); specialize (isfe2 x).
      match_case_in isfe1; intros; rewrite H in isfe1; try tauto.
      match_destr_in isfe1; try tauto.
      match_case_in isfe2; intros; rewrite H0 in isfe2; try tauto.
      match_destr_in isfe2; try tauto.
      apply Rbar_Expectation_minus_finite; trivial.
      - apply Rbar_rvmult_rv.
        + now apply RandomVariable_sa_sub.
        + apply Real_Rbar_rv.
          apply EventIndicator_pre_rv.
          now apply sub.
      - apply Rbar_rvmult_rv.
        + now apply RandomVariable_sa_sub.
        + apply Real_Rbar_rv.
          apply EventIndicator_pre_rv.
          now apply sub.
    }

    assert (eqq2: forall x,  Rbar_Expectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0)) = Some (Finite 0)).
    {
      intros x.
      rewrite eqqlin.
      specialize (isce1 _ (classic_dec _) (sa_G x)).
      specialize (isce2 _ (classic_dec _) (sa_G x)).
      specialize (isfe2 x).
      rewrite <- isce1, <- isce2.
      rewrite <- isce2 in isfe2.
      match_destr_in isfe2; try tauto.
      now rewrite Rbar_minus_eq_0.
    }

    assert (rv12 : forall x,
               RandomVariable dom2 Rbar_borel_sa
                              (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0))).
    {
      intros x.
      eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)); try eapply eqq0.
      apply Rbar_rvplus_rv.
      - apply Rbar_rvmult_rv; trivial.
        apply Real_Rbar_rv.
        now apply EventIndicator_pre_rv.
      - apply Rbar_rvopp_rv.
        apply Rbar_rvmult_rv; trivial.
        apply Real_Rbar_rv.
        now apply EventIndicator_pre_rv.
    } 

    assert (psG0:forall x, ps_P (ProbSpace:=((prob_space_sa_sub prts sub))) (exist _ (G x) (sa_G x)) = 0).
    {
      intros x.
      specialize (eqq2 x).
      generalize (@Rbar_Expectation_nonneg_zero_almost_zero _ _ ((prob_space_sa_sub prts sub))
                                                            (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0)))
      ; intros HH2.
      cut_to HH2; trivial.
      - destruct HH2 as [P [pone pH]].
        unfold const in pH.
        unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, EventIndicator in pH.
        apply NNPP.
        intros neq.
        simpl in *.
        assert (HH1:ps_P (ProbSpace:=((prob_space_sa_sub prts sub))) (event_inter P (exist (sa_sigma _) (G x) (sa_G x))) <> 0).
        {
          rewrite ps_inter_l1; trivial.
        } 
        destruct (zero_prob_or_witness _ HH1) as [a [Pa Ga]]; simpl in *.
        specialize (pH _ Pa).
        match_destr_in pH; try tauto.
        rewrite Rbar_mult_1_r in pH.
        destruct Ga as [??].
        unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp in pH.
        destruct (ce1 a); destruct (ce2 a); simpl in *; try (invcs pH; lra).
      - rewrite Rbar_Expectation_prob_space_sa_sub; trivial.
    }

    destruct isf2 as [P [Pone ?]].
    assert (psG0' : forall x, ps_P
                           (event_inter
                              (event_sa_sub sub (exist _ (G x) (sa_G x)))
                              (event_sa_sub sub P))
                         = 0).
    {
      intros a; simpl in *.
      now rewrite ps_inter_r1.
    }

    generalize (is_lim_ascending prts (fun x => (event_inter
                                                (event_sa_sub sub (exist _ (G (INR x)) (sa_G (INR x))))
                                                (exist _ _ (sa_finite_Rbar ce2 (RandomVariable_sa_sub sub _))))))
    ; intros HH.
    cut_to HH.
    - apply (is_lim_seq_ext _ (fun _ => 0)) in HH.
      + apply is_lim_seq_unique in HH.
        rewrite Lim_seq_const in HH.
        assert (eqq3:pre_event_equiv
                       (union_of_collection
                          (fun x : nat => event_inter (event_sa_sub sub (exist (sa_sigma _) (G (INR x)) (sa_G (INR x)))) (exist _ _ (sa_finite_Rbar ce2 (RandomVariable_sa_sub sub _)))))
                       (pre_event_inter 
                          (fun omega : Ts => Rbar_gt (ce1 omega) (ce2 omega))
                          (fun a => is_finite (ce2 a)))).
        { 
          intros a.
          split; simpl.
          - intros [?[[??]?]].
            split; trivial.
          - unfold G.
            intros [??].
            exists (Z.to_nat (up (Rabs (ce2 a)))).
            split; trivial.
            split; trivial.
            unfold Rbar_ge, Rbar_rvabs.
            rewrite <- H1; simpl.
            rewrite INR_up_pos.
            * apply Rge_le.
              left. apply archimed.
            * apply Rle_ge.
              apply Rabs_pos.
        } 
        destruct (sa_proper dom2 _ _ eqq3) as [sa1 _].
        cut_to sa1.
        * rewrite (ps_proper _ (event_sa_sub sub ((exist _ _ sa1)))) in HH by (now red).
          generalize (ps_complement (prob_space_sa_sub prts sub)
                                    ((exist _ _ sa1)))
          ; intros eqq4.
          invcs HH.
          simpl in *.
          rewrite <- H1 in eqq4.
          field_simplify in eqq4.
          eexists.
          split.
          -- rewrite ps_inter_r1.
             ++ apply eqq4.
             ++ apply Pone.
          -- intros a; simpl.
             unfold pre_event_complement.
             unfold Rbar_gt.
             intros [??].
             apply not_and_or in H0.
             specialize (H _ H2).
             destruct H0; try tauto.
             now apply Rbar_not_lt_le.
        * apply  sa_countable_union
          ; intros n.
          simpl.
          apply sa_inter; trivial.
          now apply sa_finite_Rbar.
      + intros n.
        simpl in *.
        rewrite ps_inter_r1; trivial.
        erewrite <- ps_inter_r1; try eapply Pone.
        rewrite ps_proper; try eapply Pone.
        intros ?; simpl.
        split.
        * intros [??]; trivial.
        * intros; split; auto.
    - intros ??.
      unfold G.
      intros [[??]?].
      split; trivial.
      split; trivial.
      unfold Rbar_gt, Rbar_ge in *.
      eapply Rbar_le_trans; try eapply H1.
      apply le_INR; lia.
  Qed.

  Theorem is_conditional_expectation_almostfinite_unique
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        (isf1:almost (prob_space_sa_sub prts sub) (fun a => is_finite (ce1 a)))
        (isf2:almost (prob_space_sa_sub prts sub) (fun a => is_finite (ce2 a))) :
    is_conditional_expectation dom2 f ce1 ->
    is_conditional_expectation dom2 f ce2 ->
    almostR2 (prob_space_sa_sub prts sub) eq ce1 ce2.
  Proof.
    intros.
    apply antisymmetry
    ; eapply is_conditional_expectation_almostfinite_le; eauto.
  Qed.

  Theorem is_conditional_expectation_unique
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        {isfe:IsFiniteExpectation prts f} :
    is_conditional_expectation dom2 f ce1 ->
    is_conditional_expectation dom2 f ce2 ->
    almostR2 (prob_space_sa_sub prts sub) eq ce1 ce2.
  Proof.
    intros.
    
    eapply is_conditional_expectation_almostfinite_unique; eauto.
    - generalize (finite_Rbar_Expectation_almostR2_finite _ ce1)
      ; intros HH1.
      eexists.
      split.
      + apply (finite_Rbar_Expectation_almostR2_finite _ ce1).
        apply Rbar_IsFiniteExpectation_prob_space_sa_sub_f; trivial.
        eapply is_conditional_expectation_FiniteExpectation; eauto.
      + now simpl.
    - generalize (finite_Rbar_Expectation_almostR2_finite _ ce2)
      ; intros HH1.
      eexists.
      split.
      + apply (finite_Rbar_Expectation_almostR2_finite _ ce2).
        apply Rbar_IsFiniteExpectation_prob_space_sa_sub_f; trivial.
        eapply is_conditional_expectation_FiniteExpectation; eauto.
      + now simpl.
  Qed.

  Existing Instance Rbar_rvmult_rv.

  Lemma Rbar_rvmult_assoc (a:Ts->Rbar) (b:Ts->Rbar) (c:Ts->Rbar) :
    rv_eq (Rbar_rvmult a (Rbar_rvmult b c)) (Rbar_rvmult (Rbar_rvmult a b) c).
  Proof.
    intros ?.
    apply Rbar_mult_assoc.
  Qed.

  Lemma rvmult_rvscale c (a b:Ts->R) : 
    rv_eq (rvmult (rvscale c a) b) (rvscale c (rvmult a b)).
  Proof.
    intros ?.
    rv_unfold; lra.
  Qed.

  Theorem is_conditional_expectation_const (c:R)
    :
      is_conditional_expectation dom2 (const c) (const c).
  Proof.
    intros P Pdec saP.
    unfold Rbar_rvmult, rvmult, const; simpl.
    now rewrite Expectation_Rbar_Expectation.
  Qed.
  
  Lemma is_conditional_expectation_scale_nzero (c:R)
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rv : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      c <> 0 ->
      is_conditional_expectation dom2 f ce ->
      is_conditional_expectation dom2 (rvscale c f) (Rbar_rvmult (const c) ce)
                                 (rvce:=Rbar_rvmult_rv _ _)
  .
  Proof.
    intros cnzero isce P Pdec saP.
    
    generalize (Expectation_scale c (rvmult f (EventIndicator Pdec)) cnzero)
    ; intros HH1.
    generalize (Rbar_Expectation_scale c (Rbar_rvmult ce (fun x : Ts => EventIndicator Pdec x)) cnzero)
    ; intros HH2.
    specialize (isce P Pdec saP).
    simpl in *.
    
    rewrite <- (Rbar_Expectation_ext (Rbar_rvmult_assoc _ _ _)).
    rewrite (Expectation_ext (rvmult_rvscale _ _ _)).
    match_destr_in HH1
    ; match_destr_in HH2
    ; rewrite HH1, HH2
    ; trivial.
    now invcs isce.
  Qed.

  Corollary is_conditional_expectation_propere
            {f1 f2 : Ts -> R}
            (eq1:almostR2 prts eq f1 f2) 
            {ce1 ce2 : Ts -> Rbar}
            (eq2:almostR2 prts eq ce1 ce2)
            (rvf1 : RandomVariable dom borel_sa f1)
            (rvf2 : RandomVariable dom borel_sa f2)
            (rvce1 : RandomVariable dom2 Rbar_borel_sa ce1)
            (rvce2 : RandomVariable dom2 Rbar_borel_sa ce2)
            :
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2.
    Proof.
      now apply is_conditional_expectation_proper.
    Qed.
    
  Theorem is_conditional_expectation_scale (c:R)
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rv : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      is_conditional_expectation dom2 f ce ->
      is_conditional_expectation dom2 (rvscale c f) (Rbar_rvmult (const c) ce)
                                 (rvce:=Rbar_rvmult_rv _ _).
  Proof.
    destruct (Req_EM_T c 0).
    - subst.
      intros.
      unfold rvscale, Rbar_rvmult, const.
      apply (is_conditional_expectation_proper (const 0) _ (const 0) _).
      + apply all_almost; intros; unfold const; lra.
      + apply all_almost; intros; unfold const.
        now rewrite Rbar_mult_0_l.
      + apply is_conditional_expectation_const.        
    - now apply is_conditional_expectation_scale_nzero.
  Qed.
  
  Corollary is_conditional_expectation_scale_inv (c:R)
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rv : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      c <> 0 ->
      is_conditional_expectation dom2 (rvscale c f) (Rbar_rvmult (const c) ce)
                                 (rvce:=Rbar_rvmult_rv _ _) ->
      is_conditional_expectation dom2 f ce.
  Proof.
    intros cnzero isce.
    generalize (is_conditional_expectation_scale (/ c) _ _ isce).
    apply is_conditional_expectation_proper
    ; apply all_almost
    ; intros ?
    ; unfold rvscale, Rbar_rvmult, const.
    - now field_simplify.
    - rewrite Rbar_mult_div_fin_cancel_l; trivial.
  Qed.

  Corollary is_conditional_expectation_opp 
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rv : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      is_conditional_expectation dom2 f ce ->
      is_conditional_expectation dom2 (rvopp f) (Rbar_rvopp ce)
                                 (rvce:=Rbar_rvopp_rv _).
  Proof.
    intros isce.
    apply (is_conditional_expectation_scale (-1)) in isce.
    eapply (is_conditional_expectation_proper _ _ _ _ (reflexivity _) _ isce).
    Unshelve.
    apply all_almost.
    intros ?.
    unfold Rbar_rvmult, Rbar_rvopp, const.
    destruct (ce x); simpl; rbar_prover.
  Qed.

  Theorem is_conditional_expectation_plus
        (f1 f2 : Ts -> R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf1 : RandomVariable dom borel_sa f1}
        {rvf2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
    :
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2 ->
      is_conditional_expectation dom2 (rvplus f1 f2) (Rbar_rvplus ce1 ce2)
                                      (rvce:= Rbar_rvplus_rv _ _).
  Proof.
    intros isce1 isce2 ???.
    generalize (rvmult_rvadd_distr (EventIndicator dec) f1 f2); intros eqq1.
    rewrite rvmult_comm in eqq1.
    rewrite (Expectation_ext eqq1).
    generalize (IsFiniteExpectation_indicator prts f1 dec (sub _ H) isfe1)
    ; intros isfe1'.
    generalize (IsFiniteExpectation_indicator prts f2 dec (sub _ H) isfe2)
    ; intros isfe2'.
    
    red in isfe1', isfe2'.
    match_option_in isfe1'; try tauto.
    match_option_in isfe2'; try tauto.
    destruct r; try tauto.
    destruct r0; try tauto.
    rewrite Expectation_sum_finite with (e1:=r) (e2:=r0); trivial.
    - rewrite isce1 in eqq; trivial.
      rewrite isce2 in eqq0; trivial.
      assert (rv_eq (Rbar_rvmult (Rbar_rvplus ce1 ce2) (EventIndicator dec))
                    (Rbar_rvplus (Rbar_rvmult (EventIndicator dec) ce1) (Rbar_rvmult (EventIndicator dec) ce2))).
      {
        intros ?.
        unfold Rbar_rvminus, Rbar_rvmult, Rbar_rvplus, Rbar_rvopp.
        simpl.
        rewrite (Rbar_mult_comm _ (EventIndicator dec a)).
        now rewrite Rbar_mult_r_plus_distr.
      }
      
      rewrite (Rbar_Expectation_ext H0).
      rewrite Rbar_Expectation_sum_finite with (e1:=r) (e2:=r0); trivial.
      + apply Rbar_rvmult_rv; trivial.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
        * eapply RandomVariable_sa_sub; eauto.
      + apply Rbar_rvmult_rv; trivial.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
        * eapply RandomVariable_sa_sub; eauto.
      + rewrite <- eqq.
        apply Rbar_Expectation_ext.
        intros ?.
        unfold Rbar_rvmult.
        apply Rbar_mult_comm.
      + rewrite <- eqq0.
        apply Rbar_Expectation_ext.
        intros ?.
        unfold Rbar_rvmult.
        apply Rbar_mult_comm.
    - apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sub.
    - apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sub.
    - rewrite <- eqq.
      apply Expectation_ext.
      apply rvmult_comm.
    - rewrite <- eqq0.
      apply Expectation_ext.
      apply rvmult_comm.
  Qed.

  Corollary is_conditional_expectation_minus
            (f1 f2 : Ts -> R)
            (ce1 ce2 : Ts -> Rbar)
            {rvf1 : RandomVariable dom borel_sa f1}
            {rvf2 : RandomVariable dom borel_sa f2}
            {isfe1:IsFiniteExpectation prts f1}
            {isfe2:IsFiniteExpectation prts f2}
            {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
            {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
    :
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2 ->
      is_conditional_expectation dom2 (rvminus f1 f2) (Rbar_rvminus ce1 ce2)
                                 (rvce:= Rbar_rvplus_rv _ _).
  Proof.
    intros isce1 isce2.
    apply is_conditional_expectation_plus; trivial.
    - now apply IsFiniteExpectation_opp.
    - now apply is_conditional_expectation_opp.
  Qed.
  
  Lemma Rbar_rvlim_almost_proper (f1 f2:nat->Ts->Rbar) :
    (forall n, almostR2 prts eq (f1 n) (f2 n)) ->
    almostR2 prts eq (Rbar_rvlim f1) (Rbar_rvlim f2).
  Proof.
    intros eqq.
    unfold Rbar_rvlim.
    destruct (choice _ eqq) as [coll collp].
    exists (inter_of_collection coll).
    split.
    - apply ps_one_countable_inter.
      intros n.
      now destruct (collp n).
    - intros x px.
      apply ELim_seq_ext; intros n.
      destruct (collp n) as [? eqq2].
      rewrite eqq2; trivial.
      apply px.
  Qed.

  Global Instance rvmin_almost_proper : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvmin.
  Proof.
    intros ?? [p1[? eqq1]] ?? [p2[? eqq2]].
    exists (event_inter p1 p2).
    split.
    - rewrite ps_inter_l1; trivial.
    - intros ? [??].
      unfold rvmin.
      rewrite eqq1, eqq2; trivial.
  Qed.

  Global Instance Rbar_rvplus_almost_proper {DOM:SigmaAlgebra Ts} (PRTS: ProbSpace DOM)  : Proper (almostR2 PRTS eq ==> almostR2 PRTS eq ==> almostR2 PRTS eq) Rbar_rvplus.
  Proof.
    intros ?? [p1[? eqq1]] ?? [p2[? eqq2]].
    exists (event_inter p1 p2).
    split.
    - rewrite ps_inter_l1; trivial.
    - intros ? [??].
      unfold Rbar_rvplus.
      rewrite eqq1, eqq2; trivial.
  Qed.

  Global Instance Rbar_rvopp_almost_proper {DOM:SigmaAlgebra Ts} (PRTS: ProbSpace DOM) : Proper (almostR2 PRTS eq ==> almostR2 PRTS eq) Rbar_rvopp.
  Proof.
    intros ?? [p1[? eqq1]].
    exists p1.
    split; trivial.
    - intros ??.
      unfold Rbar_rvopp.
      rewrite eqq1; trivial.
  Qed.

  Lemma sa_le_Rbar_ge_rv {domm}
        (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : sa_sigma _ (fun omega => Rbar_ge (rv_X omega) x).
  Proof.
    apply Rbar_sa_le_ge.
    intros.
    now apply rv_Rbar_measurable.
  Qed.

  Definition event_Rbar_ge {domm}
             (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : event domm
    := @exist (pre_event Ts) _ _ (sa_le_Rbar_ge_rv rv_X x).

  Theorem is_conditional_expectation_isfe
        f ce
        {rvf:RandomVariable dom borel_sa f} 
        {rvce:RandomVariable dom2 Rbar_borel_sa ce} :
    is_conditional_expectation dom2 f ce ->
    IsFiniteExpectation prts f ->
    Rbar_IsFiniteExpectation prts ce.
  Proof.
    unfold is_conditional_expectation, IsFiniteExpectation, Rbar_IsFiniteExpectation; intros isce isf.
    specialize (isce _ (dsa_dec dsa_Ω)).

    assert (eqq1:forall f, Expectation (rvmult f (EventIndicator (dsa_dec dsa_Ω))) = Expectation f).
    {
      intros.
      apply Expectation_proper.
      rv_unfold; intros ?; simpl.
      lra.
    }
    assert (eqq2:forall f, Rbar_Expectation (Rbar_rvmult f (EventIndicator (dsa_dec dsa_Ω))) = Rbar_Expectation f).
    {
      intros.
      apply Rbar_Expectation_proper.
      rv_unfold; intros ?; simpl.
      unfold Rbar_rvmult.
      now rewrite Rbar_mult_1_r.
    }

    rewrite eqq1, eqq2 in isce.
    rewrite isce in isf.
    - apply isf.
    - simpl.
      apply sa_all.
  Qed.

  Theorem is_conditional_expectation_nneg
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
        {nnf:NonnegativeFunction f}
    :
      is_conditional_expectation dom2 f ce ->
      almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) ce.
  Proof.
    unfold is_conditional_expectation.
    intros isce.

    specialize (isce (fun x => Rbar_lt (ce x) 0) (classic_dec _)).
    cut_to isce.
    - rewrite (Expectation_pos_pofrf _ (nnf:= indicator_prod_pos _ _ _)) in isce.
      generalize (NonnegExpectation_pos (rvmult f (EventIndicator (classic_dec (fun x : Ts => Rbar_lt (ce x) 0)))))
      ; intros le1.

      case_eq (Rbar_Expectation
           (Rbar_rvmult ce
              (fun x : Ts =>
                 EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))
      ; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in isce
      ; try discriminate.
      assert (nnf1:Rbar_NonnegativeFunction
                     (Rbar_rvopp
                        (Rbar_rvmult ce
                                     (fun x : Ts =>
                                        EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))).
      {
        intros ?.
        unfold Rbar_rvopp, Rbar_rvmult, EventIndicator.
        match_destr.
        - rewrite Rbar_mult_1_r.
          apply Rbar_opp_le.
          rewrite Rbar_opp_involutive.
          simpl.
          rewrite Ropp_0.
          now apply Rbar_lt_le.
        - rewrite Rbar_mult_0_r.
          simpl; lra.
      }

      assert (r = 0).
      {
        apply antisymmetry; [| congruence].
        generalize (Rbar_Expectation_opp
                      (Rbar_rvmult ce
                                   (fun x : Ts =>
                                      EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))
        ; intros HH1.
        simpl in HH1.
        rewrite eqq1 in HH1.
        rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=nnf1)) in HH1.
        generalize (Rbar_NonnegExpectation_pos
                      (Rbar_rvopp
                         (Rbar_rvmult ce
                                      (fun x : Ts =>
                                         EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x))))
        ; intros HH2.
        invcs HH1.
        rewrite H0 in HH2.
        apply Rbar_opp_le.
        unfold Rbar_opp.
        rewrite Ropp_0.
        apply HH2.
      }
      subst.
      generalize (Rbar_Expectation_opp
                    (Rbar_rvmult ce
                                 (fun x : Ts =>
                                    EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))
      ; intros HH1; simpl in HH1.
      rewrite eqq1 in HH1; simpl in HH1.
      rewrite Ropp_0 in HH1.
      assert (rv1:RandomVariable dom2 Rbar_borel_sa
                                 (Rbar_rvopp
                                    (Rbar_rvmult ce
                                                 (fun x : Ts =>
                                                    EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))).
      {
        apply Rbar_rvopp_rv.
        {
          apply Rbar_rvmult_rv; trivial.
          apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          apply Rbar_sa_le_lt; intros.
          now apply rv_Rbar_measurable.
        }
      }
      rewrite <- (Rbar_Expectation_prob_space_sa_sub prts sub) in HH1; trivial.
      apply (Rbar_Expectation_nonneg_zero_almost_zero _) in HH1; trivial.
      eapply almost_impl; try eapply HH1.
      apply all_almost.
      unfold const.
      intros ? eqq0.
      unfold Rbar_rvopp, Rbar_rvmult, EventIndicator in eqq0.
      match_destr_in eqq0.
      + rewrite Rbar_mult_1_r in eqq0.
        apply (f_equal Rbar_opp) in eqq0.
        rewrite Rbar_opp_involutive in eqq0.
        rewrite eqq0.
        simpl; lra.
      + now apply Rbar_not_lt_le.
    - apply Rbar_sa_le_lt; intros.
      now apply rv_Rbar_measurable.
  Qed.

  Lemma is_conditional_expectation_anneg
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      almostR2 prts Rle (const 0) f ->
      is_conditional_expectation dom2 f ce ->
      almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) ce.
  Proof.
    intros anneg isce.
    unfold almostR2, const in anneg.
    destruct (almost_map_R_split _ anneg)
      as [f2 [eqq1 [nneg f2_rv]]].
    specialize (f2_rv rvf).
    apply (is_conditional_expectation_proper _ f2 _ ce) in isce
    ; trivial; try reflexivity.
    eapply is_conditional_expectation_nneg; eauto.
  Qed.

    Theorem is_conditional_expectation_ale
        (f1 : Ts -> R)
        (f2 : Ts -> R)
        (ce1 : Ts -> Rbar)
        (ce2 : Ts -> Rbar)
        {rvf1 : RandomVariable dom borel_sa f1}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {isfe1:IsFiniteExpectation prts f1}
        {rvf2 : RandomVariable dom borel_sa f2}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        {isfe2:IsFiniteExpectation prts f2}
    :
      almostR2 prts Rle f1 f2 ->
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2 ->
      almostR2 (prob_space_sa_sub prts sub) Rbar_le ce1 ce2.
  Proof.
    intros ale isce1 isce2.
    generalize (is_conditional_expectation_minus _ _ _ _ isce2 isce1)
    ; intros HH.

    cut (almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) (Rbar_rvminus ce2 ce1)).
    - apply almost_impl.
      apply all_almost.
      unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, const.
      intros ??.
      destruct (ce1 x); destruct (ce2 x); simpl in *; rbar_prover.
    - apply is_conditional_expectation_anneg in HH; trivial.
      revert ale.
      apply almost_impl.
      apply all_almost.
      intros ??.
      unfold const, rvminus, rvplus, rvopp, rvscale.
      lra.
  Qed.      

  Fixpoint list_Rbar_sum (l : list Rbar) : Rbar :=
    match l with
    | nil => 0
    | x :: xs => Rbar_plus x (list_Rbar_sum xs)
    end.

  Lemma list_Rbar_sum_const_mulR {A : Type} f (l : list A) :
    forall (r:R), list_Rbar_sum (map (fun x => Rbar_mult r (f x)) l)  =
              Rbar_mult r (list_Rbar_sum (map (fun x => f x) l)).
  Proof.
    intro r.
    induction l; simpl.
    - f_equal; lra.
    - rewrite IHl.
      now rewrite Rbar_mult_r_plus_distr.
  Qed.

  Lemma is_conditional_expectation_finexp
             (f : Ts -> R)
             (ce : Ts -> Rbar)           
             {rvf : RandomVariable dom borel_sa f}
             {rvce : RandomVariable dom2 Rbar_borel_sa ce}            
    : is_conditional_expectation dom2 f ce ->
      forall P (dec:dec_pre_event P),
        sa_sigma dom2 P ->
        forall {isfef:IsFiniteExpectation prts (rvmult f (EventIndicator dec))}
          {isfece:Rbar_IsFiniteExpectation prts (Rbar_rvmult ce (EventIndicator dec))},
        FiniteExpectation prts (rvmult f (EventIndicator dec)) =
        Rbar_FiniteExpectation prts (Rbar_rvmult ce (EventIndicator dec)).
  Proof.
    intros isce P decP saP ??.
    unfold FiniteExpectation, Rbar_FiniteExpectation, proj1_sig.
    repeat match_destr.
    rewrite (isce P decP saP) in e.
    congruence.
  Qed.

  Lemma is_conditional_expectation_isfe_finite_part
        {f : Ts -> R}
        {ce : Ts -> Rbar}
        {rvf : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}            
    : is_conditional_expectation dom2 f ce ->
      is_conditional_expectation dom2 f (Rbar_finite_part ce).
  Proof.
    intros isce.
     apply (is_conditional_expectation_FiniteExpectation f _ isce) in isfe.
     apply (Rbar_IsFiniteExpectation_prob_space_sa_sub_f prts sub) in isfe; trivial.
     apply finexp_almost_finite_part in isfe; [| now apply RandomVariable_sa_sub].
     revert isce.
     apply is_conditional_expectation_proper.
    - reflexivity.
    - now apply (almostR2_prob_space_sa_sub_lift _ sub).
  Qed.

  Lemma is_conditional_expectation_isfe_finite_part_b
        {f : Ts -> R}
        {ce : Ts -> Rbar}
        {rvf : RandomVariable dom borel_sa f}
        {isfe:Rbar_IsFiniteExpectation prts ce}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}            
    : is_conditional_expectation dom2 f (Rbar_finite_part ce) ->
      is_conditional_expectation dom2 f ce.
  Proof.
    intros isce.
     apply (Rbar_IsFiniteExpectation_prob_space_sa_sub_f prts sub) in isfe; trivial.
     apply finexp_almost_finite_part in isfe; [| now apply RandomVariable_sa_sub].
     revert isce.
     apply is_conditional_expectation_proper.
    - reflexivity.
    - now apply (almostR2_prob_space_sa_sub_lift _ sub).
  Qed.
  
  Lemma IsFiniteExpectation_factor_out_scale_indicator (g:Ts->R) (f:Ts->R)
        {rvg : RandomVariable dom borel_sa g}
        {rvf : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
        (a:R) :
    IsFiniteExpectation prts (rvmult (scale_val_indicator g a) f).
  Proof.
    unfold scale_val_indicator.
    assert (eqq1: rv_eq
                     (fun omega : Ts => rvmult (rvscale a (val_indicator g a)) f omega)
                     (fun omega : Ts => rvscale a (rvmult f (val_indicator g a)) omega)).
    {
      intros ?.
      rv_unfold; lra.
    }
    rewrite eqq1.
    apply IsFiniteExpectation_scale.
    apply IsFiniteExpectation_indicator; trivial.
    apply sa_le_pt.
    now apply rv_measurable.
Qed.

  Lemma IsFiniteExpectation_factor_out_frf (g:Ts->R) (f:Ts->R)
        {rvg : RandomVariable dom borel_sa g}
        {rvf : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
        {frfg : FiniteRangeFunction g} :
    IsFiniteExpectation prts (rvmult (fun x : Ts => g x) f).
  Proof.
    cut (IsFiniteExpectation prts (rvmult (fun x : Ts => ( (frf_indicator g)) x) f)).
    - apply IsFiniteExpectation_proper.
      intros ?.
      unfold rvmult.
      f_equal.
      now rewrite <- frf_indicator_sum.
    - unfold frf_indicator.
      generalize (nodup Req_EM_T frf_vals); intros l.
      assert (eqq1:rv_eq
             (rvmult
                (fun x : Ts => RealAdd.list_sum (map (fun c : R => scale_val_indicator g c x) l))
                f)
             (fun x : Ts => RealAdd.list_sum (map (fun c : R => rvmult (scale_val_indicator g c) f x) l))).
      {
        intros ?.
        rv_unfold.
        rewrite Rmult_comm.
        rewrite <- list_sum_const_mul.
        f_equal.
        apply map_ext; intros.
        lra.
      }
      rewrite eqq1.
      apply IsFiniteExpectation_list_sum.
      + typeclasses eauto.
      + intros.
        apply IsFiniteExpectation_factor_out_scale_indicator; trivial.
  Qed.

  Lemma Rbar_IsFiniteExpectation_factor_out_frf (g:Ts->R) (f:Ts->Rbar)
        {rvg : RandomVariable dom borel_sa g}
        {rvf : RandomVariable dom Rbar_borel_sa f}
        {isfe:Rbar_IsFiniteExpectation prts f}
        {frfg : FiniteRangeFunction g} :
    Rbar_IsFiniteExpectation prts (Rbar_rvmult (fun x : Ts => g x) f).
  Proof.
    generalize (finexp_almost_finite_part prts _ isfe)
    ; intros eqq.
    unfold Rbar_IsFiniteExpectation.
    assert (
        almostR2 prts eq
               (Rbar_rvmult (fun x : Ts => g x) f)
               (Rbar_rvmult (fun x : Ts => g x) (fun x : Ts => Rbar_finite_part f x))).
    {
      revert eqq.
      apply almost_impl.
      apply all_almost; intros ??.
      unfold Rbar_rvmult.
      congruence.
    }

    erewrite Rbar_Expectation_almostR2_proper; try eapply H.
    - unfold Rbar_rvmult, Rbar_finite_part; simpl.
      rewrite <- Expectation_Rbar_Expectation.
      apply IsFiniteExpectation_factor_out_frf; trivial.
      + now apply Rbar_real_rv.
      + now apply Rbar_finexp_finexp.
    - apply Rbar_rvmult_rv; trivial.
      now apply Real_Rbar_rv.
    - apply Rbar_rvmult_rv; trivial.
      + now apply Real_Rbar_rv.
      + apply Real_Rbar_rv.
        now apply Rbar_real_rv.
  Qed.

  Lemma Rbar_FinExp_FinExp (f:Ts->Rbar) 
        {rv:RandomVariable dom Rbar_borel_sa f}
        {isfe:Rbar_IsFiniteExpectation prts f}
        {isfe':IsFiniteExpectation prts (Rbar_finite_part f)}:
    Rbar_FiniteExpectation prts f =
    FiniteExpectation prts (Rbar_finite_part f).
  Proof.
    generalize (finexp_almost_finite prts _ isfe)
    ; intros eqq1.
    unfold Rbar_FiniteExpectation, FiniteExpectation, proj1_sig.
    repeat match_destr.
    rewrite Expectation_Rbar_Expectation in e0.
    assert (Some (Finite x) = Some (Finite x0)).
    {
      rewrite <- e, <- e0.
      apply Rbar_Expectation_almostR2_proper; trivial.
      - apply Real_Rbar_rv.
        now apply Rbar_real_rv.
      - revert eqq1.
        apply almost_impl.
        apply all_almost; intros ??.
        now rewrite <- H.
    }
    now invcs H.
  Qed.

  Lemma is_conditional_expectation_factor_out_frf
        (f g:Ts->R) (ce:Ts->Rbar)
        {frfg : FiniteRangeFunction g}
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
        {rvgf: RandomVariable dom borel_sa (rvmult g f)}
        {rvgce: RandomVariable dom2 Rbar_borel_sa (Rbar_rvmult g ce)} :
    IsFiniteExpectation prts f ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult g f) (Rbar_rvmult g ce).
  Proof.
    intros isfe isce.
    assert (isfe_ce:Rbar_IsFiniteExpectation prts ce).
    {
      apply is_conditional_expectation_FiniteExpectation in isce.
      now apply isce.
    } 
    assert (isfe_ce':Rbar_IsFiniteExpectation prts (Rbar_rvmult (fun x : Ts => g x) ce)).
    {
      apply Rbar_IsFiniteExpectation_factor_out_frf; trivial.
      - now apply RandomVariable_sa_sub.
      - now apply RandomVariable_sa_sub.
    }
    assert (isfe_ce'':IsFiniteExpectation prts (fun x => real (ce x))).
    {
      apply Rbar_finexp_finexp; trivial.
      now apply RandomVariable_sa_sub.
    } 

    apply is_conditional_expectation_isfe_finite_part_b.
    intros P decP saP.
    unfold Rbar_rvmult, Rbar_finite_part; simpl.
    rewrite <- Expectation_Rbar_Expectation.

    apply finexp_almost_finite_part in isfe_ce; [| now apply RandomVariable_sa_sub].
    symmetry.
    transitivity (Expectation
                    (rvmult (rvmult g (fun x => (Finite (ce x)))) (EventIndicator decP))).
    {
      apply Expectation_almostR2_proper.
      + apply rvmult_rv.
        * apply Rbar_real_rv.
          apply Rbar_rvmult_rv.
          -- apply Real_Rbar_rv.
             apply RandomVariable_sa_sub; trivial.
          -- now apply RandomVariable_sa_sub.
        * apply EventIndicator_pre_rv.
          now apply sub.
      + apply rvmult_rv.
        * apply rvmult_rv.
          -- now apply RandomVariable_sa_sub.
          -- apply Rbar_real_rv.
             apply Real_Rbar_rv.
             apply Rbar_real_rv.
             now apply RandomVariable_sa_sub.
        * apply EventIndicator_pre_rv.
          now apply sub.
      + apply almostR2_eq_mult_proper; try reflexivity.
        revert isfe_ce.
        apply almost_impl.
        apply all_almost; intros ? eqq.
        now rewrite eqq.
    }


    assert (eqq1:forall f, rv_eq
              (rvmult (rvmult g f) (EventIndicator decP))
              (rvmult (rvmult (frf_indicator g) f) (EventIndicator decP))).
    {
      intros.
      apply rvmult_proper; try reflexivity.
      apply rvmult_proper; try reflexivity.
      apply (frf_indicator_sum g).
    }
    rewrite (Expectation_ext (eqq1 f)).
    rewrite (Expectation_ext (eqq1 ce)).
    unfold frf_indicator.
    
    assert (eqq2: forall f, 
              rv_eq
                (rvmult (rvmult (frf_indicator g) f) (EventIndicator decP))
                (fun omega : Ts =>
                   RealAdd.list_sum
                     (map (fun c : R => (scale_val_indicator g c omega) * (f omega) * EventIndicator decP omega)
                          (nodup Req_EM_T frf_vals)))).
    {
      intros ??.
      unfold rvmult, frf_indicator.
      rewrite Rmult_assoc.
      rewrite Rmult_comm.
      rewrite <- list_sum_const_mul.
      f_equal.
      apply map_ext; intros.
      lra.
    } 
    rewrite (Expectation_ext (eqq2 f)).
    rewrite (Expectation_ext (eqq2 ce)).

    assert (isfe1:forall ff, RandomVariable dom borel_sa ff ->
                        IsFiniteExpectation prts ff ->
                         forall c, IsFiniteExpectation prts
                                      (fun omega : Ts =>
                                         val_indicator g c omega * ff omega * EventIndicator decP omega)).
    {
      intros.
      unfold val_indicator.
      assert (eqq:
                rv_eq
                  (fun omega : Ts => val_indicator g c omega * ff omega * EventIndicator decP omega)
                   (fun omega : Ts =>
                      (ff omega * EventIndicator (classic_dec (fun omega0 : Ts => g omega0 = c)) omega) *
                                 EventIndicator decP omega)).
      {
        intros ?.
        unfold val_indicator.
        lra.
      }
      rewrite eqq.
      apply IsFiniteExpectation_indicator; trivial.
      - apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        apply sa_le_pt.
        apply rv_measurable.
        now apply RandomVariable_sa_sub.
      - now apply sub.
      - apply IsFiniteExpectation_indicator; trivial.
        apply sa_le_pt.
        apply rv_measurable.
        now apply RandomVariable_sa_sub.
    }

    assert (isfe1':forall ff, RandomVariable dom borel_sa ff ->
                        IsFiniteExpectation prts ff ->
                        forall c, IsFiniteExpectation prts
                                                 (fun omega : Ts =>
                                                    scale_val_indicator g c omega * ff omega * EventIndicator decP omega)).
    {
      intros.
      unfold scale_val_indicator.
      generalize (IsFiniteExpectation_scale prts c _ (isfe:=isfe1 ff H H0 c)).
      apply IsFiniteExpectation_proper.
      intros ?.
      unfold scale_val_indicator, rvscale.
      lra.
    }

    assert (rvff:forall ff, RandomVariable dom borel_sa ff ->
                       forall c, RandomVariable dom borel_sa
                                                 (fun omega : Ts =>
                                                    scale_val_indicator g c omega * ff omega * EventIndicator decP omega)).
    {
      intros.
      apply rvmult_rv.
      - apply rvmult_rv; trivial.
        apply scale_val_indicator_rv.
        now apply RandomVariable_sa_sub.
      - apply EventIndicator_pre_rv.
        now apply sub.
    } 
    
    generalize (isfe1' f); intros isfef.
    cut_to isfef; trivial.
    
    rewrite (FiniteExpectation_list_sum _ _ _ (isfe:=isfef)).

    assert (RandomVariable dom borel_sa (fun x : Ts => ce x)).
    {
      apply Rbar_real_rv.
      now apply RandomVariable_sa_sub.
    }

    generalize (rvff ce); intros rvfce.
    cut_to rvfce; trivial.
    
    generalize (isfe1' ce); intros isfece.
    cut_to isfece; trivial.

    rewrite (FiniteExpectation_list_sum _ _ _ (isfe:=isfece)).
    do 3 f_equal.
    apply map_ext; intros.
    unfold scale_val_indicator.

    assert (eqq3: forall ff,
               rv_eq (fun omega : Ts =>
                        rvscale a (val_indicator g a) omega * ff omega * EventIndicator decP omega)
                     (rvscale a (rvmult ff (EventIndicator (classic_dec (pre_event_inter
                                                                           (fun omega0 : Ts => g omega0 = a) P)))))).
    {
      intros ??.
      unfold val_indicator, pre_event_inter.
      rv_unfold.
      repeat rewrite Rmult_assoc.
      f_equal.
      rewrite Rmult_comm.
      rewrite Rmult_assoc.
      f_equal.
      repeat match_destr; intuition lra.
    }

    rewrite (FiniteExpectation_ext_alt _ _ _ (eqq3 ce)).
    rewrite (FiniteExpectation_ext_alt _ _ _ (eqq3 f)).

    assert (isfee:forall ff, RandomVariable dom borel_sa (fun x : Ts => ff x) ->
                  IsFiniteExpectation prts ff ->
                  IsFiniteExpectation prts (rvmult (fun x : Ts => ff x)
                                                   (EventIndicator
                                                      (classic_dec (pre_event_inter (fun omega0 : Ts => g omega0 = a) P))))). 
    {
      intros.
      apply IsFiniteExpectation_indicator; trivial.
      apply sa_inter; trivial.
      - apply sa_le_pt.
        apply rv_measurable.
        now apply RandomVariable_sa_sub.
      - now apply sub.
    }

    generalize (isfee f)
    ; intros isfef1.
    cut_to isfef1; trivial.
    generalize (isfee ce)
    ; intros isfece1.
    cut_to isfece1; trivial.

    rewrite (FiniteExpectation_scale' _ _ _ (isfe:=isfef1)).
    rewrite (FiniteExpectation_scale' _ _ _ (isfe:=isfece1)).
    f_equal.
    apply is_conditional_expectation_isfe_finite_part in isce.

    assert (sa_sigma dom2 (pre_event_inter (fun omega0 : Ts => g omega0 = a) P)).
    {
      apply sa_inter; trivial.
      apply sa_le_pt.
      apply rv_measurable.
      now apply RandomVariable_sa_sub.
    } 

    assert (sa_sigma dom (pre_event_inter (fun omega0 : Ts => g omega0 = a) P)).
    {
      apply sa_inter.
      - apply sa_le_pt.
        apply rv_measurable.
        now apply RandomVariable_sa_sub.
      - now apply sub.
    } 

    assert (Rbar_IsFiniteExpectation prts
                                     (Rbar_rvmult (fun x : Ts => Rbar_finite_part ce x)
                                                  (fun x : Ts =>
                                                     EventIndicator
                                                       (classic_dec (pre_event_inter (fun omega0 : Ts => g omega0 = a) P)) x))).
    {
      unfold Rbar_rvmult; simpl.
      unfold Rbar_finite_part.
      unfold Rbar_IsFiniteExpectation.
      rewrite <- Expectation_Rbar_Expectation.
      apply IsFiniteExpectation_indicator; trivial.
    }

    erewrite (is_conditional_expectation_finexp _ _ isce); trivial.
    unfold Rbar_rvmult; simpl.
    erewrite Rbar_FinExp_FinExp.
    - reflexivity.
    - apply Real_Rbar_rv.
      apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv; trivial.
  Qed.


    Lemma NonnegExpectation_sum'
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        {nnf1:NonnegativeFunction rv_X1}
        {nnf2:NonnegativeFunction rv_X2} 
        {nnf3:NonnegativeFunction (rvplus rv_X1 rv_X2)} :
    NonnegExpectation (rvplus rv_X1 rv_X2) =
    Rbar_plus (NonnegExpectation rv_X1) (NonnegExpectation rv_X2).
   Proof.
     now rewrite <- NonnegExpectation_sum.
   Qed.

   Instance list_sum_map_nn f (l : list R)
        {nnf:forall c, In c l -> NonnegativeFunction (f c)} :
    NonnegativeFunction
      (fun omega : Ts => RealAdd.list_sum (map (fun c : R => f c omega) l)).
   Proof.
     induction l; intros ?; simpl.
     - lra.
     - apply Rplus_le_le_0_compat.
       + apply nnf.
         simpl; tauto.
       + apply IHl.
         intros.
         apply nnf.
         simpl; tauto.
   Qed.

   Lemma NonnegExpectation_list_sum_in f (l : list R)
        {rv:forall c, RandomVariable dom borel_sa (f c)}
        {nnf:forall c, In c l -> NonnegativeFunction (f c)} :

    NonnegExpectation
            (fun omega => RealAdd.list_sum
                          (map (fun c => (f c omega))
                               l)) =
    (list_Rbar_sum
       (map_onto l (fun c pf  =>
                      (NonnegExpectation (f c) (pofrf := nnf c pf))))).
  Proof.
    induction l; simpl; intros.
    - eapply NonnegExpectation_const.
    - generalize (NonnegExpectation_sum' (f a)); unfold rvplus; intros HH.
      erewrite HH; trivial.
      + f_equal.
        erewrite IHl; trivial.
      + now apply list_sum_rv.
        Unshelve.
        * lra.
        * intros.
          apply nnf.
          simpl; tauto.
   Qed.

  Lemma Rbar_NonnegExpectation_plus'
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2}
        {nnf1:Rbar_NonnegativeFunction rv_X1}
        {nnf2:Rbar_NonnegativeFunction rv_X2} 
        {nnf3:Rbar_NonnegativeFunction (Rbar_rvplus rv_X1 rv_X2)} :         
    Rbar_NonnegExpectation (Rbar_rvplus rv_X1 rv_X2) =
    Rbar_plus (Rbar_NonnegExpectation rv_X1) (Rbar_NonnegExpectation rv_X2).
  Proof.
    now rewrite <- Rbar_NonnegExpectation_plus.
  Qed.

  Lemma NonnegFunction_list_sum f l
    (nnf:forall c, In c l -> NonnegativeFunction (f c)) :
    NonnegativeFunction (fun omega : Ts => RealAdd.list_sum (map (fun c : R => f c omega) l)).
  Proof.
    induction l; simpl.
    - intros _; lra.
    - apply rvplus_nnf.
      + now apply nnf; left.
      + apply IHl; intros.
        now apply nnf; right.
  Qed.      

    
  Lemma NonnegExpectation_list_sum f (l : list R) 
        {rv:forall c, RandomVariable dom borel_sa (f c)}
        {nnf:forall (c : R), In c l -> NonnegativeFunction (f c)} 
        {nnsum :NonnegativeFunction
                  (fun omega : Ts => RealAdd.list_sum (map (fun c : R => f c omega) l))} :

    NonnegExpectation
            (fun omega => RealAdd.list_sum
                          (map
                             (fun c : R =>
                                (f c omega))
                             l)) =
    (list_Rbar_sum
       (map_onto
          l
          (fun c pf =>
             NonnegExpectation (f c) (pofrf:=nnf c pf)))).
  Proof.
    induction l; simpl.
    - apply (NonnegExpectation_const _ (reflexivity _)).
    - assert (nnf1 : NonnegativeFunction (f a)) by (now apply nnf; left).
      assert (nnf2 : forall c, In c l -> NonnegativeFunction (f c)) by (now intros; apply nnf; right).
      assert (nnf3: NonnegativeFunction (fun omega : Ts => RealAdd.list_sum (map (fun c : R => f c omega) l))).
      {
        now apply NonnegFunction_list_sum.
      } 
      
      generalize (NonnegExpectation_sum' (f a)); unfold rvplus; intros HH.
      erewrite HH; trivial.
      + f_equal.
        now erewrite IHl.
      + now apply list_sum_rv.
  Qed.

   Instance list_Rbar_sum_rv {T} f l
           {rv:forall c, RandomVariable dom Rbar_borel_sa (f c)}
    : RandomVariable dom Rbar_borel_sa
                     (fun omega : Ts => list_Rbar_sum (map (fun c : T => f c omega) l)).
  Proof.
    induction l; simpl.
    - apply rvconst.
    - generalize @Rbar_rvplus_rv; unfold rvplus; intros HH.
      apply HH; trivial.
  Qed.

  Lemma Rbar_NonnegFunction_list_Rbar_sum f l
    (nnf:forall c, In c l -> Rbar_NonnegativeFunction (f c)) :
    Rbar_NonnegativeFunction (fun omega : Ts => list_Rbar_sum (map (fun c : R => f c omega) l)).
  Proof.
    induction l; simpl.
    - intros _.
      apply Rbar_le_refl.
    - apply pos_Rbar_plus.
      + now apply nnf; left.
      + apply IHl; intros.
        now apply nnf; right.
  Qed.

  Lemma Rbar_NonnegExpectation_list_sum_in f (l : list R) 
        {rv:forall c, RandomVariable dom Rbar_borel_sa (f c)}
        {nnf:forall c, In c l -> Rbar_NonnegativeFunction (f c)} 
        {nnsum :Rbar_NonnegativeFunction
                  (fun omega : Ts => list_Rbar_sum (map (fun c : R => f c omega) l))} :


    Rbar_NonnegExpectation
            (fun omega => list_Rbar_sum
                          (map
                             (fun c : R =>
                                (f c omega))
                             l)) =
    (list_Rbar_sum
       (map_onto l 
          (fun c pf =>
             Rbar_NonnegExpectation (f c) (pofrf := nnf c pf)))).
  Proof.
    induction l; simpl.
    - eapply Rbar_NonnegExpectation_const.
    - 
      + 
      assert (nnf1 : Rbar_NonnegativeFunction (f a)) by (now apply nnf; left).
      assert (nnf2 : forall c, In c l -> Rbar_NonnegativeFunction (f c)) by (now intros; apply nnf; right).
      assert (nnf3: Rbar_NonnegativeFunction (fun omega : Ts => list_Rbar_sum (map (fun c : R => f c omega) l))).
      {
        now apply Rbar_NonnegFunction_list_Rbar_sum.
      } 
      f_equal.        
      generalize (Rbar_NonnegExpectation_plus' (f a)); unfold Rbar_rvplus; intros HH.
      erewrite HH; trivial.
      now erewrite <- IHl.
      now apply list_Rbar_sum_rv.
      Unshelve.
      lra.
  Qed.

  Global Instance Rbar_NonnegativeFunction_proper : Proper (rv_eq (Ts := Ts) ==> iff) Rbar_NonnegativeFunction.
    Proof.
      unfold Rbar_NonnegativeFunction, rv_eq, pointwise_relation.
      intros x y eqq.
      split; intros lle z.
      - rewrite <- eqq; auto.
      - rewrite eqq; auto.
    Qed.

  Lemma Rbar_NonnegExpectation_re
        {rv_X1 rv_X2 : Ts -> Rbar}
        (eqq:rv_eq rv_X1 rv_X2)
        {nnf1:Rbar_NonnegativeFunction rv_X1} :
    Rbar_NonnegExpectation rv_X1 = Rbar_NonnegExpectation rv_X2 (pofrf:=((proj1 (Rbar_NonnegativeFunction_proper _ _ eqq)) nnf1)).
  Proof.
    now apply Rbar_NonnegExpectation_ext.
  Qed.

  Lemma list_Rbar_sum_nneg (l : list Rbar) :
    (forall (c : Rbar), In c l -> Rbar_le 0 c) ->
    Rbar_le 0 (list_Rbar_sum l).
  Proof.
    intros lpos.
    induction l.
    - simpl; lra.
    - replace  (list_Rbar_sum (a :: l)) with (Rbar_plus a (list_Rbar_sum l)).
      + replace (Finite 0) with (Rbar_plus 0 0).
        * apply Rbar_plus_le_compat.
          -- apply lpos.
             simpl; tauto.
          -- apply IHl.
             intros.
             apply lpos.
             simpl; tauto.
        *  now rewrite Rbar_plus_0_r.
      + now simpl.
  Qed.

  Lemma list_Rbar_sum_const_mul (l : list Rbar) :
    (forall (c : Rbar), In c l -> Rbar_le 0 c) ->
    forall r, 
      list_Rbar_sum (map (fun x => Rbar_mult r x) l)  =
              Rbar_mult r (list_Rbar_sum l).
  Proof.
    intros lpos r.
    induction l.
    - simpl.
      now rewrite Rbar_mult_0_r.
    - simpl. rewrite IHl.
      + rewrite Rbar_mult_plus_distr_l; trivial.
        * apply lpos.
          simpl; tauto.
        * apply list_Rbar_sum_nneg.
          intros.
          apply lpos.
          now apply in_cons.
      + intros.
        apply lpos.
        now apply in_cons.
  Qed.

  Lemma list_Rbar_sum_map_finite l :
    list_Rbar_sum (map Finite l) = Finite (RealAdd.list_sum l).
  Proof.
    induction l; simpl; trivial.
    now rewrite IHl.
  Qed.

(*
  Lemma frf_fun_pos_frf_vals (g : Ts -> R) 
        {frfg : FiniteRangeFunction g}
        {nng : NonnegativeFunction g} :
    exists (h : Ts -> R),
*)      


  Lemma is_conditional_expectation_factor_out_frf_nneg_aux
        (f g:Ts->R) (ce:Ts->Rbar)
        {frfg : FiniteRangeFunction g}
        {nnf : NonnegativeFunction f}
        {nng : NonnegativeFunction g}        
        {nnce : Rbar_NonnegativeFunction ce}        
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
        {rvgf: RandomVariable dom borel_sa (rvmult g f)}
        {rvgce: RandomVariable dom2 Rbar_borel_sa (Rbar_rvmult g ce)}
        (frfpos : (forall (c : R), In c frf_vals -> 0 <= c)) :
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult g f) (Rbar_rvmult g ce).
  Proof.
    intros (* isfe *) isce.
    intros P decP saP.
    erewrite Expectation_pos_pofrf.
    erewrite Rbar_Expectation_pos_pofrf.

    f_equal.
    
    assert (eqq1:forall f, rv_eq
              (rvmult (rvmult g f) (EventIndicator decP))
              (rvmult (rvmult (frf_indicator g) f) (EventIndicator decP))).
    {
      intros.
      apply rvmult_proper; try reflexivity.
      apply rvmult_proper; try reflexivity.
      apply (frf_indicator_sum g).
    }
    rewrite (NonnegExpectation_re (eqq1 f)).
    assert (eqq1Rbar :
              rv_eq
                (Rbar_rvmult (Rbar_rvmult (fun x : Ts => g x) ce)
                             (fun x : Ts => EventIndicator decP x))
                (Rbar_rvmult (Rbar_rvmult (frf_indicator g) ce)
                             (fun x : Ts => EventIndicator decP x))).
    {
      intros ?.
      unfold Rbar_rvmult.
      f_equal.
      f_equal.
      now rewrite (frf_indicator_sum g).
    }      
    
    rewrite (Rbar_NonnegExpectation_re eqq1Rbar).
    
    assert (eqq2: forall f, 
              rv_eq
                (rvmult (rvmult (frf_indicator g) f) (EventIndicator decP))
                (fun omega : Ts =>
                   RealAdd.list_sum
                     (map (fun c : R => (scale_val_indicator g c omega) * (f omega) * EventIndicator decP omega)
                          (nodup Req_EM_T frf_vals)))).
    {
      intros ??.
      unfold rvmult, frf_indicator.
      rewrite Rmult_assoc.
      rewrite Rmult_comm.
      rewrite <- list_sum_const_mul.
      f_equal.
      apply map_ext; intros.
      lra.
    }
    rewrite (NonnegExpectation_re (eqq2 f)).
    assert (eqq2Rbar: 
              rv_eq
                (Rbar_rvmult (Rbar_rvmult (frf_indicator g) ce) (EventIndicator decP))
                (fun omega : Ts =>
                   list_Rbar_sum
                     (map (fun c : R => (Rbar_mult (Rbar_mult (scale_val_indicator g c omega) (ce omega)) (EventIndicator decP omega)))
                          (nodup Req_EM_T frf_vals)))).
    {
      intros ?.
      unfold Rbar_rvmult, frf_indicator.
      rewrite <- Rbar_mult_assoc.
      rewrite Rbar_mult_comm.
      replace  (Finite (RealAdd.list_sum (map (fun c : R => scale_val_indicator g c a) (nodup Req_EM_T frf_vals)))) with
          (list_Rbar_sum (map (fun c : R => Finite (scale_val_indicator g c a)) (nodup Req_EM_T frf_vals))).
      - rewrite <- list_Rbar_sum_const_mul.
        f_equal.
        + rewrite map_map.
          apply map_ext; intros.
          rewrite (Rbar_mult_comm _ (ce a)).
          rewrite <- Rbar_mult_assoc.
          rewrite (Rbar_mult_comm (EventIndicator decP a) _).
          now rewrite Rbar_mult_assoc.
        + intros.
          rewrite in_map_iff in H.
          destruct H as [? [? ?]].
          unfold scale_val_indicator, val_indicator in H.
          rewrite <- H.
          unfold rvscale.
          simpl.
          apply Rmult_le_pos.
          * rewrite nodup_In in H0.
            now apply frfpos.
          * apply EventIndicator_pos.
      - rewrite <- list_Rbar_sum_map_finite.
        now rewrite map_map.
    }

    rewrite (Rbar_NonnegExpectation_re eqq2Rbar).

    assert (rvff:forall ff, RandomVariable dom borel_sa ff ->
                       forall c, RandomVariable dom borel_sa
                                                (fun omega : Ts =>
                                                   scale_val_indicator g c omega * ff omega * EventIndicator decP omega)).
    {
      intros.
      apply rvmult_rv.
      - apply rvmult_rv; trivial.
        apply scale_val_indicator_rv.
        now apply RandomVariable_sa_sub.
      - apply EventIndicator_pre_rv.
        now apply sub.
    } 
    
    assert (RandomVariable dom borel_sa (fun x : Ts => ce x)).
    {
      apply Rbar_real_rv.
      now apply RandomVariable_sa_sub.
    }

    generalize (rvff f); intros rvfff.
    cut_to rvfff; trivial.


    assert (nnf3: forall c : R,
               In c (nodup Req_EM_T frf_vals) ->
               NonnegativeFunction (fun omega : Ts => scale_val_indicator g c omega * f omega * EventIndicator decP omega)).
    {
      intros ???.
      apply Rmult_le_pos; [| apply EventIndicator_pos].
      apply Rmult_le_pos; [| apply nnf].
      apply Rmult_le_pos; [| apply EventIndicator_pos].
      apply frfpos.
      eapply nodup_In; eauto.
    }

    assert (forall c : R,
               In c (nodup Req_EM_T frf_vals) ->
               Rbar_NonnegativeFunction (fun omega : Ts => Rbar_mult (Rbar_mult (scale_val_indicator g c omega) (ce omega)) (EventIndicator decP omega))).
    {
      intros ???.
      apply Rbar_mult_nneg_compat; [| apply EventIndicator_pos].
      apply Rbar_mult_nneg_compat; [| apply nnce].
      apply Rmult_le_pos; [| apply EventIndicator_pos].
      apply frfpos.
      eapply nodup_In; eauto.
    }

   
    erewrite  NonnegExpectation_list_sum.
    erewrite Rbar_NonnegExpectation_list_sum_in.    

    f_equal.
    apply map_onto_ext; intros a pf.
    
    unfold scale_val_indicator.

    assert (eqq3: forall ff,
               rv_eq (fun omega : Ts =>
                        rvscale a (val_indicator g a) omega * ff omega * EventIndicator decP omega)
                     (rvscale a (rvmult ff (EventIndicator (classic_dec (pre_event_inter
                                                                           (fun omega0 : Ts => g omega0 = a) P)))))).
    {
      intros ??.
      unfold val_indicator, pre_event_inter.
      rv_unfold.
      repeat rewrite Rmult_assoc.
      f_equal.
      rewrite Rmult_comm.
      rewrite Rmult_assoc.
      f_equal.
      repeat match_destr; intuition lra.
    }

    rewrite (NonnegExpectation_re (eqq3 f)).

    assert (eqq3Rbar: 
              rv_eq (fun omega : Ts =>
                         Rbar_mult (Rbar_mult (rvscale a (val_indicator g a) omega) (ce omega))
                                   (EventIndicator decP omega))
                    (Rbar_rvmult (const a) (Rbar_rvmult ce (EventIndicator (classic_dec (pre_event_inter
                                                                                           (fun omega0 : Ts => g omega0 = a) P)))))).
    {
      intros ?.
      unfold val_indicator, pre_event_inter, Rbar_rvmult, const.
      rv_unfold.
      case_eq (ce a0); intros.
      - simpl.
        repeat rewrite Rmult_assoc.
        apply Rbar_finite_eq.
        f_equal.
        rewrite Rmult_comm.
        rewrite Rmult_assoc.
        f_equal.
        repeat match_destr; intuition lra.
      - repeat match_destr; try easy; try rewrite Rmult_1_r; try rewrite Rmult_0_r; try rewrite Rbar_mult_1_r; try rewrite Rbar_mult_1_r; try rewrite Rbar_mult_0_r; try rewrite Rbar_mult_0_r; try rewrite Rbar_mult_0_r; try easy; try tauto.
        now rewrite Rbar_mult_0_l.
      - specialize (nnce a0).
        rewrite H1 in nnce.
        now simpl in nnce.
    }

    rewrite (Rbar_NonnegExpectation_re eqq3Rbar).

    - destruct (Rlt_dec 0 a) as [apos | aneg].
      + {
        generalize (NonnegExpectation_scale (mkposreal _ apos)); intros.
        simpl in H1.
        erewrite (NonnegExpectation_pf_irrel _ (rvscale_nnf (mkposreal _ apos) _ _)).
        rewrite H1.
        generalize (Rbar_NonnegExpectation_scale' _ (mkposreal _ apos)); intros.
        simpl in H2.
        erewrite H2.
        f_equal.
        red in isce.
        assert (Expectation (rvmult f (EventIndicator (classic_dec (pre_event_inter (fun omega0 : Ts => g omega0 = a) P)))) =
                  Rbar_Expectation
                    (Rbar_rvmult ce (fun x : Ts => EventIndicator (classic_dec (pre_event_inter (fun omega0 : Ts => g omega0 = a) P)) x))).
        {
          apply isce.
          apply sa_inter; trivial.
          apply sa_le_pt.
          apply rv_measurable.
          now apply RandomVariable_sa_sub.
        }
        
        erewrite Expectation_pos_pofrf in H3.
        erewrite Rbar_Expectation_pos_pofrf in H3.
        invcs H3.
        apply H5.

        - apply Rbar_rvmult_rv.
          + now apply RandomVariable_sa_sub.
          + apply Real_Rbar_rv.
            apply EventIndicator_pre_rv.
            apply sa_inter.
            * apply sa_le_pt.
              apply rv_measurable.
              now apply RandomVariable_sa_sub.
            * now apply sub.
        - now left.
      }
      + assert (a = 0).
        {
          assert (0 <= a).
          {
            apply frfpos.
            eapply nodup_In; eauto.
          }
          lra.
        }
        subst.
        rewrite (NonnegExpectation_ext _ (@nnfconst Ts 0 (reflexivity _))).
        * rewrite NonnegExpectation_const.
          rewrite (Rbar_NonnegExpectation_ext _ nnf_0).
          -- erewrite <- (Rbar_NonnegExpectation_const 0).
             apply Rbar_NonnegExpectation_pf_irrel.
          -- intros ?;
               unfold Rbar_rvmult, const.
             apply Rbar_mult_0_l.
        * intros ?; rv_unfold.
          lra.
    - intros.
      apply Rbar_rvmult_rv.
      + apply Rbar_rvmult_rv.
        * apply Real_Rbar_rv.
          unfold scale_val_indicator.
          apply rvscale_rv.
          apply EventIndicator_pre_rv.
          apply sa_le_pt.
          apply rv_measurable.
          now apply RandomVariable_sa_sub.
        * now apply RandomVariable_sa_sub.
      + apply Real_Rbar_rv.
        apply EventIndicator_pre_rv.        
        now apply sub.
    - intros.
      typeclasses eauto.
      Unshelve.
      reflexivity.
  Qed.

  Program Definition frf_nneg_nneg (f : Ts -> R) 
    {frf : FiniteRangeFunction f}
    {nneg: NonnegativeFunction f} : FiniteRangeFunction f
    := {|
      frf_vals := filter (fun x => if Rle_dec 0 x then true else false) frf_vals
    |}.
  Next Obligation.
    apply filter_In.
    split.
    - apply frf_vals_complete.
    - match_destr.
      elim n.
      now specialize (nneg x).
  Qed.

  Lemma frf_nneg_nneg_nneg (f : Ts -> R) 
    {frf : FiniteRangeFunction f}
    {nneg: NonnegativeFunction f} :
    forall x, In x (@frf_vals _ _ _ (frf_nneg_nneg f)) -> 0 <= x.
  Proof.
    simpl; intros.
    apply filter_In in H.
    destruct H.
    match_destr_in H0.
  Qed.

  Lemma is_conditional_expectation_factor_out_frf_nneg
        (f g:Ts->R) (ce:Ts->Rbar)
        {frfg : FiniteRangeFunction g}
        {nnf : NonnegativeFunction f}
        {nng : NonnegativeFunction g}        
        {nnce : Rbar_NonnegativeFunction ce}        
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
        {rvgf: RandomVariable dom borel_sa (rvmult g f)}
        {rvgce: RandomVariable dom2 Rbar_borel_sa (Rbar_rvmult g ce)} :
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult g f) (Rbar_rvmult g ce).
  Proof.
    apply (is_conditional_expectation_factor_out_frf_nneg_aux _ _ _ (frfg := frf_nneg_nneg g)).
    apply frf_nneg_nneg_nneg.
  Qed.

  Lemma frf_min (f : Ts -> R) 
    {frf : FiniteRangeFunction f} :
    forall x, RList.MinRlist frf_vals  <= f x.
  Proof.
    intros.
    destruct frf; simpl.
    now apply RList.MinRlist_P1.
  Qed.

  Lemma frf_max (f : Ts -> R) 
    {frf : FiniteRangeFunction f} :
    forall x, f x <= RList.MaxRlist frf_vals.
  Proof.
    intros.
    destruct frf; simpl.
    now apply RList.MaxRlist_P1.
  Qed.
  
  Lemma IsFiniteExpectation_mult_finite_range_pos (f g : Ts -> R) 
    {frf : FiniteRangeFunction g} :
    NonnegativeFunction f ->
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g).
  Proof.
    intros.
    pose (gmin := RList.MinRlist frf_vals).
    pose (gmax := RList.MaxRlist frf_vals).    
    apply (IsFiniteExpectation_bounded prts (rvscale gmin f) (rvmult f g) (rvscale gmax f)).
    - intro x.
      rv_unfold; unfold gmin.
      rewrite Rmult_comm.
      apply Rmult_le_compat_l.
      + apply H.
      + apply frf_min.
    - intro x.    
      rv_unfold; unfold gmin.
      rewrite Rmult_comm.
      apply Rmult_le_compat_r.
      + apply H.
      + apply frf_max.
   Qed.

  Lemma IsFiniteExpectation_mult_finite_range (f g : Ts -> R) 
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom borel_sa g}        
        {frf : FiniteRangeFunction g} :
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g).
  Proof.
    intros.
    destruct (IsFiniteExpectation_parts prts f H).
    generalize (IsFiniteExpectation_mult_finite_range_pos (pos_fun_part f) g (positive_part_nnf f) H0); intros.
    generalize (IsFiniteExpectation_mult_finite_range_pos (neg_fun_part f) g (negative_part_nnf f) H1); intros.    
    rewrite (rv_pos_neg_id f).
    assert (rv_eq (rvmult (rvplus (fun x : Ts => pos_fun_part f x) (rvopp (fun x : Ts => neg_fun_part f x))) g)
                  (rvminus (rvmult (pos_fun_part f) g) (rvmult (neg_fun_part f) g))).
    {
      intro x.
      rv_unfold; simpl.
      rewrite Rmult_plus_distr_r.
      lra.
    }
    rewrite H4.
    apply IsFiniteExpectation_minus; trivial; typeclasses eauto.
  Qed.

  (* should be generalized to (ce : Ts -> Rbar) almost is_finite
        and almost Rbar_NonnegativeFunction *)
     
Theorem is_conditional_expectation_factor_out_nneg_both
          (f g:Ts -> R)
          (ce : Ts -> R)
          {nnegf : NonnegativeFunction f}          
          {nnegg : NonnegativeFunction g}
          {nnegce : NonnegativeFunction ce}          
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom2 borel_sa g}
          {rvce : RandomVariable dom2 borel_sa ce}
          {rvgf: RandomVariable dom borel_sa (rvmult f g)} :
(*    IsFiniteExpectation prts f -> *)
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
    intros (* isfef *) iscondf.
    unfold is_conditional_expectation.
    intros.
    generalize (simple_approx_lim_seq g nnegg); intros.
    assert (forall n, FiniteRangeFunction (simple_approx g n)) by apply simple_approx_frf.
    assert (forall n, RandomVariable dom2 borel_sa (simple_approx g n)).
    {
      intros.
      apply simple_approx_rv; trivial.
      now apply Real_Rbar_rv.
    }
    assert (forall n, RandomVariable dom borel_sa (rvmult f (simple_approx g n))).
    {
      intros.
      apply rvmult_rv; trivial.
      now apply RandomVariable_sa_sub.
    }

    assert (rvgf2:forall n, RandomVariable dom borel_sa (rvmult (simple_approx g n) f)).
    {
      intros.
      apply rvmult_rv; trivial.
      now apply RandomVariable_sa_sub.
    }

    assert (forall n,
               Expectation
                 (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n))
                         (EventIndicator dec)) =
               Rbar_Expectation
                 (Rbar_rvmult
                    (Rbar_rvmult (simple_approx (fun x0 : Ts => g x0) n) ce)
                    (EventIndicator dec))).
    {
      intros.
      assert (nng : NonnegativeFunction (simple_approx (fun x : Ts => g x) n)) by 
          apply simple_approx_pofrf.
      generalize (is_conditional_expectation_factor_out_frf_nneg f (simple_approx g n) ce iscondf) ; intros.
      rewrite <- (H3 P dec H).
      apply Expectation_ext; intros ?.
      rv_unfold; lra.
    }
    assert (forall (x:Ts),
               is_lim_seq (fun n => (rvmult (rvmult f (simple_approx g n))
                                            (EventIndicator dec)) x)
                          ((rvmult (rvmult f g) (EventIndicator dec)) x)).
    {
      intros.
      unfold rvmult.
      replace (Finite (f x * g x * EventIndicator dec x)) with 
          (Rbar_mult ((f x)*(g x)) (EventIndicator dec x)) by now simpl.
      apply is_lim_seq_scal_r.
      replace (Finite (f x * g x)) with (Rbar_mult (f x) (g x)) by now simpl.
      now apply is_lim_seq_scal_l.
    }
    assert (RandomVariable dom Rbar_borel_sa (rvmult (rvmult f g) (EventIndicator dec))).
    {
      apply Real_Rbar_rv.
      apply rvmult_rv; trivial.
      apply RandomVariable_sa_sub; trivial.
      apply EventIndicator_pre_rv; trivial.
    }

   generalize (Rbar_monotone_convergence (rvmult (rvmult f g) (EventIndicator dec))); intros.
   specialize (H6  (fun n => (rvmult (rvmult f (simple_approx g n))
                                            (EventIndicator dec))) ).
   assert (Rbar_NonnegativeFunction (rvmult (rvmult f g) (EventIndicator dec))) by
       typeclasses eauto.
   assert (forall n : nat,
        RandomVariable 
          dom Rbar_borel_sa
          (rvmult (rvmult f (simple_approx g n))
                  (EventIndicator dec))).
   {
     intros.
     apply Real_Rbar_rv.
     apply rvmult_rv.
     - apply rvmult_rv; trivial.
       apply RandomVariable_sa_sub; trivial.
     - apply RandomVariable_sa_sub; trivial.
       apply EventIndicator_pre_rv; trivial.
   }
   assert (forall n : nat,
                  Rbar_NonnegativeFunction
                    ((fun n0 : nat =>
                      rvmult (rvmult f (simple_approx (fun x : Ts => g x) n0))
                        (EventIndicator dec)) n)).
   {
     intros.
     apply NonNegMult.
     - typeclasses eauto.
     - apply NonNegMult; trivial.
       apply simple_approx_pofrf.
   }
   assert (forall n:nat,
              Rbar_NonnegativeFunction
                (rvmult (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x) (fun x : Ts => ce x))
                        (fun x : Ts => EventIndicator dec x))).
   {
     intros.
     apply NonNegMult.
     - typeclasses eauto.
     - apply NonNegMult; trivial.
       apply simple_approx_pofrf.
   }
   specialize (H6 H5 H7 H8 H9).
   assert (forall n,
             Rbar_NonnegExpectation
                (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n))
                        (EventIndicator dec)) =
             Rbar_NonnegExpectation
               (rvmult
                  (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                          (fun x : Ts => ce x)) 
                  (fun x : Ts => EventIndicator dec x))).
   {
     intros.
     specialize (H3 n).
     rewrite Expectation_pos_pofrf with (nnf := (H9 n)) in H3.
     assert (rv_eq
               (Rbar_rvmult (Rbar_rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x) (fun x : Ts => ce x))
                            (fun x : Ts => EventIndicator dec x))
               (rvmult
                  (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                          (fun x : Ts => ce x)) 
                  (fun x : Ts => EventIndicator dec x))).
     {
       intro x.
       now rv_unfold; unfold Rbar_rvmult; simpl.
     }               
     rewrite (Rbar_Expectation_ext H11) in H3.
     rewrite <- Expectation_Rbar_Expectation in H3.
     rewrite Expectation_pos_pofrf with (nnf := (H10 n)) in H3.     
     now inversion H3.
   }
   clear H3.
   cut_to H6.
    - rewrite Expectation_pos_pofrf with (nnf := H7).
      rewrite (NNExpectation_Rbar_NNExpectation' _ _ _).
      rewrite <- H6.
     assert (rv_eq
               (Rbar_rvmult (Rbar_rvmult (fun x : Ts => g x) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))
               (rvmult (rvmult (fun x : Ts => g x) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))).
     {
       intro x.
       now rv_unfold; unfold Rbar_rvmult; simpl.
     }
     rewrite (Rbar_Expectation_ext H3).
     assert (Rbar_NonnegativeFunction  (rvmult (rvmult (fun x : Ts => g x) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))).
     {
       apply NonNegMult.
       - typeclasses eauto.
       - apply NonNegMult; trivial.
     }
     rewrite Rbar_Expectation_pos_pofrf with (nnf := H12).
     f_equal.
     rewrite (ELim_seq_ext _ _ H11).
     generalize (monotone_convergence_Rbar_rvlim

                   (fun n =>
                       (rvmult (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x) (fun x : Ts => ce x))
          (fun x : Ts => EventIndicator dec x))) ); intros.
     assert (forall n : nat,
         RandomVariable dom Rbar_borel_sa
           (fun omega : Ts =>
            rvmult
              (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                      (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x) omega)).
     {
       intros.
       apply Real_Rbar_rv.
       apply rvmult_rv.
       - apply rvmult_rv.
         + apply simple_approx_rv; trivial.
           apply RandomVariable_sa_sub; trivial.
           now apply Real_Rbar_rv.
         + now apply RandomVariable_sa_sub; trivial.
       - apply EventIndicator_pre_rv; trivial.
         apply sub.
         apply H.
     }
     specialize (H13 H14 H10).
     cut_to H13.
     + rewrite H13.
       apply Rbar_NonnegExpectation_ext.
       intro x.
       unfold Rbar_rvlim.
       unfold rvmult.
       replace (Finite (g x * ce x * EventIndicator dec x)) with 
           (Rbar_mult ((g x)*(ce x)) (EventIndicator dec x)) by now simpl.
       rewrite Elim_seq_fin.
       rewrite Lim_seq_scal_r.
       f_equal.
       replace (Finite (g x * ce x)) with (Rbar_mult (g x) (ce x)) by now simpl.
       rewrite Lim_seq_scal_r.
       f_equal.
       specialize (H0 x).
       now apply is_lim_seq_unique in H0.
     + intros n x.
       unfold rvmult.
       apply Rmult_le_compat_r.
       * apply EventIndicator_pos.
       * apply Rmult_le_compat_r; trivial.
         now apply simple_approx_increasing.
   - intros n x.
     unfold rvmult.
     apply Rmult_le_compat_r.
     + apply EventIndicator_pos.
     + apply Rmult_le_compat_l; trivial.
       generalize (simple_approx_le g nnegg n x); intros.
       apply H3.
   - intros n x.
     unfold rvmult.
     apply Rmult_le_compat_r.
     + apply EventIndicator_pos.
     + apply Rmult_le_compat_l; trivial.
       now apply simple_approx_increasing.
   - intros.
     unfold rvmult.
     replace (Finite  (f omega * g omega * EventIndicator dec omega)) with
         (Rbar_mult (f omega * g omega) (EventIndicator dec omega)) by now simpl.
     rewrite is_Elim_seq_fin.
     apply is_lim_seq_scal_r.
     replace (Finite (f omega * g omega)) with (Rbar_mult (f omega) (g omega)) by now simpl.
     apply is_lim_seq_scal_l.
     apply H0.
  Qed.

Theorem is_conditional_expectation_factor_out_nneg_both_Rbar
          (f g:Ts -> R)
          (ce : Ts -> Rbar)
          {nnegf : NonnegativeFunction f}          
          {nnegg : NonnegativeFunction g}
          {nnegce : Rbar_NonnegativeFunction ce}          
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom2 borel_sa g}
          {rvce : RandomVariable dom2 Rbar_borel_sa ce}
          {rvgf: RandomVariable dom borel_sa (rvmult f g)} 
          {rvgce: RandomVariable dom2 Rbar_borel_sa (Rbar_rvmult g ce)} :    
(*    IsFiniteExpectation prts f -> *)
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
    intros (* isfef *) iscondf.
    unfold is_conditional_expectation.
    intros.
    generalize (simple_approx_lim_seq g nnegg); intros.
    assert (forall n, FiniteRangeFunction (simple_approx g n)) by apply simple_approx_frf.
    assert (forall n, RandomVariable dom2 borel_sa (simple_approx g n)).
    {
      intros.
      apply simple_approx_rv; trivial.
      now apply Real_Rbar_rv.
    }
    assert (forall n, RandomVariable dom borel_sa (rvmult f (simple_approx g n))).
    {
      intros.
      apply rvmult_rv; trivial.
      now apply RandomVariable_sa_sub.
    }

    assert (rvgf2:forall n, RandomVariable dom borel_sa (rvmult (simple_approx g n) f)).
    {
      intros.
      apply rvmult_rv; trivial.
      now apply RandomVariable_sa_sub.
    }

    assert (forall n,
               Expectation
                 (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n))
                         (EventIndicator dec)) =
               Rbar_Expectation
                 (Rbar_rvmult
                    (Rbar_rvmult (simple_approx (fun x0 : Ts => g x0) n) ce)
                    (EventIndicator dec))).
    {
      intros.
      assert (nng : NonnegativeFunction (simple_approx (fun x : Ts => g x) n)) by 
          apply simple_approx_pofrf.

      assert (rvsace : RandomVariable dom2 Rbar_borel_sa
                   (Rbar_rvmult
                      (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x) ce)).
      {
        apply Rbar_rvmult_rv; trivial.
        apply Real_Rbar_rv.
        typeclasses eauto.
      }
      generalize (is_conditional_expectation_factor_out_frf_nneg f (simple_approx g n) ce iscondf) ; intros.
      rewrite <- (H3 P dec H).
      apply Expectation_ext; intros ?.
      rv_unfold; lra.
    }
    assert (forall (x:Ts),
               is_lim_seq (fun n => (rvmult (rvmult f (simple_approx g n))
                                            (EventIndicator dec)) x)
                          ((rvmult (rvmult f g) (EventIndicator dec)) x)).
    {
      intros.
      unfold rvmult.
      replace (Finite (f x * g x * EventIndicator dec x)) with 
          (Rbar_mult ((f x)*(g x)) (EventIndicator dec x)) by now simpl.
      apply is_lim_seq_scal_r.
      replace (Finite (f x * g x)) with (Rbar_mult (f x) (g x)) by now simpl.
      now apply is_lim_seq_scal_l.
    }
    assert (RandomVariable dom Rbar_borel_sa (rvmult (rvmult f g) (EventIndicator dec))).
    {
      apply Real_Rbar_rv.
      apply rvmult_rv; trivial.
      apply RandomVariable_sa_sub; trivial.
      apply EventIndicator_pre_rv; trivial.
    }

   generalize (Rbar_monotone_convergence (rvmult (rvmult f g) (EventIndicator dec))); intros.
   specialize (H6  (fun n => (rvmult (rvmult f (simple_approx g n))
                                            (EventIndicator dec))) ).
   assert (Rbar_NonnegativeFunction (rvmult (rvmult f g) (EventIndicator dec))) by
       typeclasses eauto.
   assert (forall n : nat,
        RandomVariable 
          dom Rbar_borel_sa
          (rvmult (rvmult f (simple_approx g n))
                  (EventIndicator dec))).
   {
     intros.
     apply Real_Rbar_rv.
     apply rvmult_rv.
     - apply rvmult_rv; trivial.
       apply RandomVariable_sa_sub; trivial.
     - apply RandomVariable_sa_sub; trivial.
       apply EventIndicator_pre_rv; trivial.
   }
   assert (forall n : nat,
                  Rbar_NonnegativeFunction
                    ((fun n0 : nat =>
                      rvmult (rvmult f (simple_approx (fun x : Ts => g x) n0))
                        (EventIndicator dec)) n)).
   {
     intros.
     apply NonNegMult.
     - typeclasses eauto.
     - apply NonNegMult; trivial.
       apply simple_approx_pofrf.
   }
   assert (forall n:nat,
              Rbar_NonnegativeFunction
                (Rbar_rvmult (Rbar_rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x) (fun x : Ts => ce x))
                        (fun x : Ts => EventIndicator dec x))).
   {
     intros.
     apply Rbar_rvmult_nnf.
     - apply Rbar_rvmult_nnf; trivial.
       apply simple_approx_pofrf.
     - typeclasses eauto.
   }
   specialize (H6 H5 H7 H8 H9).
   assert (forall n,
             Rbar_NonnegExpectation
                (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n))
                        (EventIndicator dec)) =
             Rbar_NonnegExpectation
               (Rbar_rvmult
                  (Rbar_rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                               (fun x : Ts => ce x)) 
                  (fun x : Ts => EventIndicator dec x))).
   {
     intros.
     specialize (H3 n).
     rewrite Expectation_pos_pofrf with (nnf := (H9 n)) in H3.
     rewrite Rbar_Expectation_pos_pofrf with (nnf := (H10 n)) in H3.
     now inversion H3.
   }
   clear H3.
   cut_to H6.
    - rewrite Expectation_pos_pofrf with (nnf := H7).
      rewrite (NNExpectation_Rbar_NNExpectation' _ _ _).
      rewrite <- H6.
     assert (Rbar_NonnegativeFunction  (Rbar_rvmult (Rbar_rvmult (fun x : Ts => g x) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))).
     {
       apply Rbar_rvmult_nnf.
       - now apply Rbar_rvmult_nnf.
       - typeclasses eauto.
     }
     rewrite Rbar_Expectation_pos_pofrf with (nnf := H3).
     f_equal.
     rewrite (ELim_seq_ext _ _ H11).
     apply Rbar_monotone_convergence.
     + apply Rbar_rvmult_rv.
       * apply Rbar_rvmult_rv.
         -- apply Real_Rbar_rv.
            now apply RandomVariable_sa_sub.
         -- now apply RandomVariable_sa_sub.
       * apply Real_Rbar_rv.
         apply EventIndicator_pre_rv; trivial.
         apply sub.
         apply H.
     + 
       {
       intros.
       apply Rbar_rvmult_rv.
       - apply Rbar_rvmult_rv.
         + apply Real_Rbar_rv.
           apply simple_approx_rv; trivial.
           apply RandomVariable_sa_sub; trivial.
           now apply Real_Rbar_rv.
         + now apply RandomVariable_sa_sub; trivial.
       - apply Real_Rbar_rv.
         apply EventIndicator_pre_rv; trivial.
         apply sub.
         apply H.
       }
     + intros n x.
       unfold Rbar_rvmult.
       apply Rbar_le_pos_compat_r.
       * apply EventIndicator_pos.
       * apply Rbar_le_pos_compat_r; trivial.
         apply (simple_approx_le g nnegg n x).
     + intros n x.
       unfold Rbar_rvmult.
       apply Rbar_le_pos_compat_r.
       * apply EventIndicator_pos.
       * apply Rbar_le_pos_compat_r; trivial.
         apply (simple_approx_increasing g nnegg n x).
     + intros.
       apply is_Elim_seq_scal_r'.
       unfold Rbar_rvmult.
       destruct (Req_EM_T (g omega) 0).
       * rewrite e.
         rewrite Rbar_mult_0_l.
         assert (is_Elim_seq (fun n => 0) 0) by apply is_Elim_seq_const.
         revert H12.
         apply is_Elim_seq_ext.
         intros.
         assert (simple_approx (fun x0 : Ts => g x0) n omega = 0).
         {
           generalize (simple_approx_le g nnegg n omega); intros.
           rewrite e in H12.
           simpl in H12.
           generalize (simple_approx_pofrf g n omega); intros.
           lra.
         }
         now rewrite H12, Rbar_mult_0_l.
       * apply is_Elim_seq_scal_r.
         -- apply is_Elim_seq_fin.
            apply (simple_approx_lim_seq g).
            apply nnegg.
         -- unfold ex_Rbar_mult.
            match_destr.
         -- assert (is_finite (g omega)) by now simpl.
            assert (0 < g omega/2).
            {
              specialize (nnegg omega).
              lra.
            }
            destruct (simple_approx_lim g nnegg (mkposreal _ H13) omega H12).
            exists x.
            intros.
            unfold ex_Rbar_mult.
            assert (simple_approx g x omega > 0).
            {
              simpl in H14.
              lra.
            }
            assert (simple_approx g n0 omega <> 0).
            {
              assert (forall h, simple_approx g x omega <= simple_approx g (h + x)%nat omega).
              {
                induction h.
                - simpl; lra.
                - replace (S h + x)%nat with (S (h + x)) by lia.
                  eapply Rle_trans.
                  apply IHh.
                  apply (simple_approx_increasing g nnegg).
             }
              specialize (H17 (n0 - x)%nat).
              replace (n0 - x + x)%nat with n0 in H17 by lia.
              lra.
            }
            now match_destr.
   - intros n x.
     unfold rvmult.
     apply Rmult_le_compat_r.
     + apply EventIndicator_pos.
     + apply Rmult_le_compat_l; trivial.
       apply (simple_approx_le g nnegg n x).
   - intros n x.
     unfold rvmult.
     apply Rmult_le_compat_r.
     + apply EventIndicator_pos.
     + apply Rmult_le_compat_l; trivial.
       now apply simple_approx_increasing.
   - intros.
     unfold rvmult.
     replace (Finite  (f omega * g omega * EventIndicator dec omega)) with
         (Rbar_mult (f omega * g omega) (EventIndicator dec omega)) by now simpl.
     rewrite is_Elim_seq_fin.
     apply is_lim_seq_scal_r.
     replace (Finite (f omega * g omega)) with (Rbar_mult (f omega) (g omega)) by now simpl.
     apply is_lim_seq_scal_l.
     apply H0.
  Qed.

  Lemma IsFiniteExpectation_abs f 
    {rv : RandomVariable dom borel_sa f} :
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvabs f).
  Proof.
    intros.
    generalize (Expectation_pos_part_finite prts f); intros.
    generalize (Expectation_neg_part_finite prts f); intros.
    generalize (rv_pos_neg_abs f); intros.
    rewrite H2.
    apply IsFiniteExpectation_plus.
    - typeclasses eauto.
    - typeclasses eauto.
    - unfold IsFiniteExpectation.
      erewrite Expectation_pos_pofrf.
      now rewrite <- H0.
    - unfold IsFiniteExpectation.
      erewrite Expectation_pos_pofrf.
      now rewrite <- H1.
  Qed.
    
  Lemma is_cond_rle_abs f ce ace
          {rvf : RandomVariable dom borel_sa f}        
          {rvce : RandomVariable dom2 Rbar_borel_sa ce}
          {rvace : RandomVariable dom2 Rbar_borel_sa ace}    :
    IsFiniteExpectation prts f ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvabs f) ace ->    
    almostR2 prts Rbar_le (Rbar_rvabs ce) ace.
  Proof.
    intros.
    generalize (IsFiniteExpectation_abs f); intro.
    assert (f_le_abs: almostR2 prts Rle f (rvabs f)).
    {
      apply almostR2_le_subr.
      intro x; unfold rvabs.
      apply Rle_abs.
   }
    generalize (is_conditional_expectation_ale f (rvabs f) ce ace f_le_abs H0 H1); intros.
    assert (oppf_le_abs: almostR2 prts Rle (rvopp f) (rvabs f)).    
    {
      apply almostR2_le_subr.
      intro x.
      unfold rvopp, rvscale, rvabs.
      replace (-1 * f x) with (- f x) by lra.
      rewrite <- Rabs_Ropp.
      apply Rle_abs.
   }
    generalize (is_conditional_expectation_opp f ce H0); intros.
    generalize (is_conditional_expectation_ale (rvopp f) (rvabs f) (Rbar_rvopp ce) ace oppf_le_abs H4 H1); intros.
    destruct H3 as [? [? ?]].
    destruct H5 as [? [? ?]].
    apply (almost_prob_space_sa_sub_lift prts sub).
    exists (event_inter x x0).
    split.
    - now rewrite ps_inter_l1.
    - intros.
      specialize (H6 x1); simpl in H6.
      specialize (H7 x1); unfold rvopp, rvscale in H7; simpl in H7.
      unfold Rbar_rvabs.
      destruct H8.
      cut_to H6; cut_to H7; trivial.
      + unfold Rbar_rvopp in H7.
        destruct (ce x1); simpl in *
        ; destruct (ace x1); simpl in *
        ; try tauto.
        apply Rabs_le.
        split; lra.
    Qed.


  
  Lemma Jensen (rv_X : Ts -> R) (phi : R -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => phi (rv_X x))} :    
    (forall c x y, convex phi c x y) ->
    FiniteExpectation prts (fun x => phi (rv_X x)) >= phi (FiniteExpectation prts rv_X).
  Proof.
    intros.
    destruct (convex_support_line phi H (FiniteExpectation prts rv_X)) as [a ?].
    pose (b := phi (FiniteExpectation prts rv_X) - a * FiniteExpectation prts rv_X).
    generalize (FiniteExpectation_scale prts a rv_X); intros.
    generalize (FiniteExpectation_const prts b); intros.
    generalize (FiniteExpectation_plus prts (rvscale a rv_X) (const b)); intros.
    rewrite H0,H1 in H2.
    assert (phi (FiniteExpectation prts rv_X) = (a * (FiniteExpectation prts rv_X) + b)) by
        (unfold b; ring).
    rewrite H3, <- H2.
    apply Rle_ge.
    apply FiniteExpectation_le.
    intro x.
    rv_unfold.
    specialize (r (rv_X x)).
    lra.
  Qed.


  Lemma is_condexp_Jensen_helper (rv_X ce phice: Ts -> R) (phi : R -> R) (a b : nat -> R) 
        {rv : RandomVariable dom borel_sa rv_X}
        {rvphi : RandomVariable dom borel_sa (fun x => phi (rv_X x))}
        {rvce : RandomVariable dom2 borel_sa ce}
        {rvace : RandomVariable dom2 borel_sa phice}          
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => phi (rv_X x))} 
        (iscondce : is_conditional_expectation dom2 rv_X ce)
        (iscond_phice : is_conditional_expectation dom2 (fun x => phi (rv_X x)) phice) :
    (forall (x: R),
        is_sup_seq (fun n => (a n) * x + (b n)) (phi x)) -> 
    almostR2 (prob_space_sa_sub prts sub) Rbar_le
      (fun x => phi (ce x)) phice.
  Proof.
    intros.
    assert (forall (n:nat),
               (forall (x:R),
                   (a n) * x + (b n) <= (phi x))).
    {
      intros.
      specialize (H x).
      apply is_sup_seq_lub in H.
      destruct H.
      unfold Rbar_is_upper_bound in H.
      specialize (H (a n * x + b n)).
      apply H.
      now exists n.
    }
    generalize (fun n => is_conditional_expectation_scale (a n) rv_X ce iscondce); intros.
    generalize (fun n => is_conditional_expectation_const (b n)); intros.
    generalize (fun n => is_conditional_expectation_plus (rvscale (a n) rv_X) (const (b n)) _ _ (H1 n) (H2 n)); intros.
    clear H1 H2.
    assert (forall (n:nat),
               almostR2 prts Rle
                        (rvplus (rvscale (a n) rv_X) (const (b n)))
                        (fun x => phi (rv_X x))).
    {
      intros.
      apply all_almost.
      intros.
      rv_unfold.
      apply H0.
    }
    generalize (fun n => is_conditional_expectation_ale 
                           (rvplus (rvscale (a n) rv_X) (const (b n)))
                           (fun x : Ts => phi (rv_X x))
                           (Rbar_rvplus 
                              (Rbar_rvmult (fun x : Ts => const (a n) x) (fun x : Ts => ce x))
                              (fun x : Ts => const (b n) x))
                           phice (H1 n) (H3 n) iscond_phice); intros.

    assert (almost (prob_space_sa_sub prts sub) 
                   (fun x => forall n, 
                        Rbar_le
                          ((Rbar_rvplus (Rbar_rvmult (fun x : Ts => const (a n) x) (fun x : Ts => ce x))
            (fun x : Ts => const (b n) x)) x)
                          (phice x))).
    {
      apply almost_forall.
      intros.
      apply (H2 n).
    }
    assert (rv_eq
              (fun x : Ts => Finite (phi (ce x)))
              (fun x => Sup_seq (fun n => a n * (ce x) + b n))).
    {
      intro x.
      specialize (H (ce x)).
      apply is_sup_seq_unique in H.
      now rewrite H.
    }
     apply (almost_impl' _ H4).    
     apply all_almost.
     intros.
     rewrite H5.
     unfold Rbar_rvplus, Rbar_rvmult, const in H6.
     simpl in H6.
     replace (Finite (phice x)) with
         (Sup_seq (fun n => (phice x))).
     - apply Sup_seq_le.
       intros.
       simpl.
       apply H6.
     - rewrite Rbar_sup_eq_lub.
       unfold Rbar_lub, proj1_sig.
       match_destr.
       destruct r.
       unfold Rbar_is_upper_bound in *.
       apply Rbar_le_antisym.
       + apply H8.
         intros.
         destruct H9.
         rewrite <- H9.
         apply Rbar_le_refl.
       + apply H7.
         now exists (0%nat).
   Qed.

  Lemma is_condexp_Jensen (rv_X ce phice: Ts -> R) (phi : R -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {rvphi : RandomVariable dom borel_sa (fun x => phi (rv_X x))}
        {rvce : RandomVariable dom2 borel_sa ce}
        {rvace : RandomVariable dom2 borel_sa phice}          
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => phi (rv_X x))} 
        (iscondce : is_conditional_expectation dom2 rv_X ce)
        (iscond_phice : is_conditional_expectation dom2 (fun x => phi (rv_X x)) phice) :
    (forall c x y, convex phi c x y) ->
    almostR2 (prob_space_sa_sub prts sub) Rbar_le
      (fun x => phi (ce x)) phice.
   Proof.
     intros.
     destruct (convex_4_2_2_a phi H) as [a [b ?]].
     now apply (is_condexp_Jensen_helper rv_X ce phice phi a b).
   Qed.

  Lemma is_condexp_Jensen_abs (rv_X ce ace : Ts -> R) 
        {rv : RandomVariable dom borel_sa rv_X}
        {rvce : RandomVariable dom2 borel_sa ce}
        {rvace : RandomVariable dom2 borel_sa ace}          
        {isfe : IsFiniteExpectation prts rv_X} :
    is_conditional_expectation dom2 rv_X ce ->
    is_conditional_expectation dom2 (rvabs rv_X) ace ->    
    almostR2 (prob_space_sa_sub prts sub) Rle
             (rvabs ce) ace.
  Proof.
    intros.
    pose (a := fun (n:nat) => if (Nat.eqb n 0%nat) then 1 else -1).
    pose (b := fun (n:nat) => 0).
    generalize (IsFiniteExpectation_abs rv_X isfe); intros.
    apply (is_condexp_Jensen_helper rv_X ce ace Rabs a b); trivial.
    intros.
    apply Rbar_is_lub_sup_seq.
    unfold Rbar_is_lub.
    unfold Rbar_is_upper_bound.
    split; intros.
    - destruct H2.
      rewrite H2.
      unfold a, b.
      rewrite Rplus_0_r.
      match_destr.
      + rewrite Rmult_1_l; simpl.
          apply Rle_abs.
      + replace (-1*x) with (-x) by lra; simpl.
          apply Rabs_maj2.
    - apply H2.
      unfold a, b.
      destruct (Rle_dec 0 x).
      + exists (0%nat); simpl.
        rewrite Rplus_0_r, Rmult_1_l.
        apply Rle_ge in r.
        now rewrite Rabs_right.
      + exists (1%nat); simpl.
        replace (-1 * x + 0) with (-x) by lra.
        rewrite Rabs_left; trivial.
        lra.
  Qed.

  (* TODO: move to RealAdd *)
  Lemma Rbar_mult_le_compat_l (r r1 r2 : Rbar) :
    Rbar_le 0 r ->
    Rbar_le r1 r2 -> Rbar_le (Rbar_mult r r1) (Rbar_mult r r2).
  Proof.
    destruct r; destruct r1; destruct r2; simpl; intros; rbar_prover.
    - now apply Rmult_le_compat_l.
    - rewrite Rmult_0_l.
      apply Rbar_le_refl.
  Qed.

    (* TODO: move to RealAdd *)
  Lemma Rbar_mult_le_compat_r (r r1 r2 : Rbar) :
    Rbar_le 0 r ->
    Rbar_le r1 r2 -> Rbar_le (Rbar_mult r1 r) (Rbar_mult r2 r).
  Proof.
    destruct r; destruct r1; destruct r2; simpl; intros; rbar_prover.
    - now apply Rmult_le_compat_r.
    - rewrite Rmult_0_r.
      apply Rbar_le_refl.
  Qed.

  Theorem is_conditional_expectation_factor_out_nneg
          (f g : Ts -> R)
          (ce ace : Ts -> R)
          {nnegg : NonnegativeFunction g}
          {nnegace : NonnegativeFunction ace}          
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom2 borel_sa g}
          {rvce : RandomVariable dom2 borel_sa ce}
          {rvace : RandomVariable dom2 borel_sa ace}          
          {rvgf: RandomVariable dom borel_sa (rvmult f g)} 
          {rvgaf: RandomVariable dom borel_sa (rvmult (rvabs f) g)} 
          {rvgce: RandomVariable dom2 borel_sa (rvmult g ce)} :
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g) ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvabs f) ace ->    
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
    intros.
    generalize (simple_approx_pofrf g); intros.
    generalize (is_cond_rle_abs f ce ace H H1 H2); intros.
    assert (forall n, almostR2 prts Rle 
                               (rvabs (rvmult (simple_approx g n) ce)) 
                               (rvmult g ace)).
    {
      intros.
      assert (almostR2 prts Rle 
                       (rvabs (rvmult (simple_approx g n) ce)) 
                       (rvmult (simple_approx g n) ace)).
      {
        assert (rv_eq
                  (rvabs
                     (rvmult (simple_approx g n) ce))
                  (rvmult (simple_approx g n) (rvabs ce))).
        - intro x.
          unfold rvabs, rvmult.
          rewrite Rabs_mult.
          rewrite Rabs_right; trivial.
          simpl.
          apply Rle_ge.
          apply simple_approx_pofrf.
        - destruct H4 as [? [? ?]].
          exists x; split; trivial; intros.
          specialize (H6 x0 H7).
          rewrite H5.
          unfold rvmult.
          apply Rmult_le_compat_l; trivial.
          apply simple_approx_pofrf.
      }
      assert (almostR2 prts Rle 
                       (rvmult (simple_approx g n) ace)
                       (rvmult g ace)).
      {
        apply all_almost; intros x.
        unfold rvmult.
        apply Rmult_le_compat_r.
        - apply nnegace.
        - apply (simple_approx_le g nnegg n).
      }
      eapply almostR2_trans.
      - apply Rle_pre.
      - apply H5.
      - apply H6.
    }
    generalize (IsFiniteExpectation_abs f H); intros.
    generalize (is_conditional_expectation_factor_out_nneg_both (rvabs f) g ace (* H6 *)); intros.
    generalize (IsFiniteExpectation_abs (rvmult f g) H0); intros.
    assert (rv_eq
              (rvabs (rvmult f g))
              (rvmult (rvabs f) g)).
    {
      intro x.
      unfold rvabs, rvmult.
      rewrite Rabs_mult.
      replace (Rabs (g x)) with (g x); trivial.
      rewrite Rabs_right; trivial.
      apply Rle_ge.
      apply nnegg.
   }
    rewrite H9 in H8.
    specialize (H7 H2).
    unfold is_conditional_expectation; intros.
    assert (rv_eq
              (Rbar_rvmult (Rbar_rvmult (fun x : Ts => g x) (fun x : Ts => ce x))
                           (fun x : Ts => EventIndicator dec x))
              (rvmult (rvmult g ce) (EventIndicator dec))).
    {
      intro x.
      unfold Rbar_rvmult, rvmult.
      now simpl.
    }
    rewrite (Rbar_Expectation_ext H11).
    rewrite <- Expectation_Rbar_Expectation.
    
    generalize (Dominated_convergence_almost _
                  (fun n => rvmult (rvmult (simple_approx g n) ce) (EventIndicator dec))
                  (rvmult (rvmult g ce) (EventIndicator dec)) ) ; intros.
    assert (rvg1 : RandomVariable dom borel_sa g) by now apply RandomVariable_sa_sub.
    assert (rvce1 : RandomVariable dom borel_sa ce) by now apply RandomVariable_sa_sub.
    assert (rvind : RandomVariable dom borel_sa (EventIndicator dec)).
    {
      apply EventIndicator_pre_rv.
      now apply sub.
    }
    assert (   forall n : nat,
         RandomVariable 
           dom borel_sa
           (rvmult (rvmult (simple_approx g n) ce)
                   (EventIndicator dec))).
    {
      intros.
      apply rvmult_rv; trivial.
      apply rvmult_rv; trivial.
      apply simple_approx_rv; trivial.
      now apply Real_Rbar_rv.
    }
    assert (RandomVariable dom borel_sa
                           (rvmult (rvmult g ce)
                                   (EventIndicator dec))).
    {
      apply rvmult_rv; trivial.
      now apply rvmult_rv.
    }
    assert ( RandomVariable dom borel_sa
                            (rvmult g ace)).
    {
      apply rvmult_rv; trivial.
      now apply RandomVariable_sa_sub.
    }
    assert ( IsFiniteExpectation prts
                                 (rvmult (rvmult g ce)
                                         (EventIndicator dec))).
    {
      apply IsFiniteExpectation_indicator.
      - now apply rvmult_rv.
      - now apply sub.
      - apply (IsFiniteExpectation_abs_bound_almost prts (rvmult g ce) (rvmult g ace)).
        + apply (almost_impl' _ H4); intros.
          apply all_almost; intros.
          unfold rvabs, rvmult.
          unfold rvabs in H16.
          rewrite Rabs_mult.
          rewrite Rabs_right.
          * now apply Rmult_le_compat_l.
          * now apply Rle_ge.
        + generalize (is_conditional_expectation_FiniteExpectation (rvmult (rvabs f) g) (rvmult g ace ) H7 ); intros.
          apply H16 in H8.
          unfold Rbar_IsFiniteExpectation in H8.
          rewrite <- Expectation_Rbar_Expectation in H8.
          apply H8.
     }
    assert ( forall n : nat,
               IsFiniteExpectation 
                 prts
                 (rvmult (rvmult (simple_approx g n) ce)
                         (EventIndicator dec))).
    {
      intro.
      generalize (simple_approx_rv g n); intros.
      assert (RandomVariable dom borel_sa (simple_approx (fun x : Ts => g x) n)) by
          now apply RandomVariable_sa_sub.
      apply IsFiniteExpectation_indicator.
      - apply rvmult_rv; trivial.
      - now apply sub.
      - rewrite rvmult_comm.
        apply IsFiniteExpectation_mult_finite_range; trivial.
        + apply simple_approx_frf.
        + generalize (is_conditional_expectation_isfe f ce H1 H); intros.
          apply Rbar_finexp_finexp in H19.
          assert (rv_eq ce (Rbar_finite_part ce)).
          {
            intro x.
            now unfold Rbar_finite_part.
          }
          now rewrite <- H20 in H19.
          now apply Real_Rbar_rv.
    }
    rewrite FiniteExpectation_Expectation with (isfe := H16).

    assert (isfe'1:forall n : nat,
               Rbar_IsFiniteExpectation prts
                                        (fun omega : Ts =>
                                           rvmult (rvmult (simple_approx (fun x : Ts => g x) n) ce) (EventIndicator dec) omega)).
    {
      intros.
      apply IsFiniteExpectation_Rbar.
      typeclasses eauto.
    }
    assert (isfe'2:Rbar_IsFiniteExpectation prts (rvmult (rvmult g ce) (EventIndicator dec))).
    {
      apply IsFiniteExpectation_Rbar; typeclasses eauto.
    } 

    specialize (H12 (rvmult g ace) _ _ _ _ _).
    
    clear H13 H14 H15.
    cut_to H12.
    apply is_lim_seq_unique in H12.
    rewrite (Rbar_FinExp_FinExp _) in H12.
    erewrite (FiniteExpectation_pf_irrel _) in H12.
    rewrite <- H12.
    generalize (Dominated_convergence _
                  (fun n => rvmult (rvmult f (simple_approx g n)) (EventIndicator dec))
                  (rvmult (rvmult f g) (EventIndicator dec))); intros.
    assert  (forall n : nat,
         RandomVariable dom borel_sa
                        (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n)) (EventIndicator dec))).
    {
      intro.
      apply rvmult_rv; trivial.
      apply rvmult_rv; trivial.
      apply simple_approx_rv; trivial.
      now apply Real_Rbar_rv.
    }
    assert (RandomVariable dom borel_sa (rvmult (rvmult f g) (EventIndicator dec))) by
      typeclasses eauto.
    assert (isfe'5:forall n : nat,
               IsFiniteExpectation 
                 prts
                 (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n)) (EventIndicator dec))).
    {
      intros.
      apply IsFiniteExpectation_indicator.
      - apply rvmult_rv; trivial.
        apply simple_approx_rv; trivial.
        now apply Real_Rbar_rv.
      - now apply sub.
      - apply IsFiniteExpectation_mult_finite_range; trivial.
        apply simple_approx_rv; trivial.
        + now apply Real_Rbar_rv.
        + apply simple_approx_frf.
    }
    assert (forall n : nat,
               Rbar_IsFiniteExpectation 
                 prts
                 (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n)) (EventIndicator dec))).
    {
      intros.
      now apply IsFiniteExpectation_Rbar.
    } 

    assert (IsFiniteExpectation prts (rvmult (rvmult f g) (EventIndicator dec))).
    {
      apply IsFiniteExpectation_indicator; trivial.
      now apply sub.
    }
    assert (isfe'3:Rbar_IsFiniteExpectation prts (rvmult (rvmult f g) (EventIndicator dec))).
    {
      now apply IsFiniteExpectation_Rbar.
    } 

    assert (isfe'4:Rbar_IsFiniteExpectation prts (fun x : Ts => rvmult (rvabs f) g x)).
    {
      now apply IsFiniteExpectation_Rbar.
    } 
    specialize (H13 (rvmult (rvabs f) g) _ _ _ _ _ _).    
    clear H14 H15.
    cut_to H13.
    apply is_lim_seq_unique in H13.

    rewrite (FiniteExpectation_Expectation _ _).
    f_equal.
    rewrite (Rbar_FinExp_FinExp _) in H13.
    erewrite (FiniteExpectation_pf_irrel _) in H13.
    rewrite <- H13.
    - apply Lim_seq_ext.
      intros.
      generalize (simple_approx_frf g); intros.
      generalize (simple_approx_rv g); intros.      
      generalize (is_conditional_expectation_factor_out_frf 
                    f (simple_approx g n) ); intros.
      assert (RandomVariable dom borel_sa (rvmult (simple_approx (fun x : Ts => g x) n) f)).
      {
        apply rvmult_rv; trivial.
        apply simple_approx_rv; trivial.
        now apply Real_Rbar_rv.
      }
      assert ( RandomVariable dom2 Rbar_borel_sa
                    (Rbar_rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                                 (fun x : Ts => ce x))).
      {
        apply Rbar_rvmult_rv.
        - now apply Real_Rbar_rv.
        - now apply Real_Rbar_rv.
      }
      specialize (H15 ce _ _ _ _ _ _ _ H1 P dec H10).      
      assert (rv_eq 
                (Rbar_rvmult
                   (Rbar_rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                                (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))
                (rvmult
                   (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                                (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))).
      {
        intro x.
        unfold Rbar_rvmult, rvmult.
        now simpl.
      }
      rewrite (Rbar_Expectation_ext H22) in H15.
      rewrite <- Expectation_Rbar_Expectation in H15.
      assert (rv_eq
                (rvmult (rvmult (simple_approx (fun x : Ts => g x) n) f) (EventIndicator dec))
                (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n) ) (EventIndicator dec)))
             by (intro x; unfold rvmult; lra).
      rewrite (Expectation_ext H23) in H15.
      rewrite (FiniteExpectation_Expectation _ _) in H15.
      clear H9 H11 H12 H13 H14 H20 H21 H22 H23.
      assert (IsFiniteExpectation prts
                (@rvmult Ts
                (@rvmult Ts (fun x : Ts => @simple_approx Ts (fun x0 : Ts => Finite (g x0)) n x)
                   (fun x : Ts => ce x)) (fun x : Ts => @EventIndicator Ts P dec x))) by easy.
      rewrite FiniteExpectation_Expectation with (isfe := H9) in H15.      
      invcs H15.
      unfold Rbar_FiniteExpectation, proj1_sig.
      repeat match_destr.
      unfold FiniteExpectation, proj1_sig in H12.
      repeat match_destr_in H12.
      rewrite Expectation_Rbar_Expectation in e1, e2.
      rewrite e1 in e.
      simpl in e2.
      cut (Some (Finite x0) = Some (Finite x2)); try congruence.
      rewrite <- e2, <- e0.
      apply Rbar_Expectation_ext; intros ?.
      reflexivity.
    - intros n x.
      generalize (simple_approx_le g nnegg n x); intros.
      unfold rvmult, rvabs, EventIndicator.
      simpl.
      match_destr.
      + rewrite Rmult_1_r.
        rewrite Rabs_mult.
        apply Rmult_le_compat_l.
        * apply Rabs_pos.
        * rewrite Rabs_right; trivial.
          apply Rle_ge.
          apply simple_approx_pofrf.
     + rewrite Rmult_0_r.
       rewrite Rabs_R0.
       apply Rmult_le_pos; trivial.
       apply Rabs_pos.
    - intro.
      unfold rvmult.
      apply is_Elim_seq_fin.
      apply is_lim_seq_mult'.
      + apply is_lim_seq_mult'.
        * apply is_lim_seq_const.
        * now generalize (simple_approx_lim_seq g nnegg x); intros.
      + apply is_lim_seq_const.
    - generalize (is_conditional_expectation_FiniteExpectation _ _ H7); intros.
      generalize (IsFiniteExpectation_abs (rvmult f g) H0); intros.
      rewrite H9 in H14.
      apply H13 in H14.
      assert (rv_eq  (Rbar_rvmult (fun x : Ts => g x) (fun x : Ts => ace x))
                     (rvmult (fun x : Ts => g x) (fun x : Ts => ace x))).
      {
        intro x.
        now unfold Rbar_rvmult, rvmult.
      }
      rewrite H15 in H14.
      apply H14.
    - intros n.
      generalize (is_conditional_expectation_nneg (rvabs f) ace H2); intros.
      apply almost_prob_space_sa_sub_lift in H13.
      generalize (almost_and prts H4 H13); intros.
      apply (almost_impl' _ H14); intros.
      apply all_almost; intros.
      destruct H15.
      unfold rvabs, Rbar_rvmult, rvmult, EventIndicator.
      simpl.
      match_destr.
      + rewrite Rmult_1_r.
        rewrite Rabs_mult.
        apply Rmult_le_compat.
        * apply Rabs_pos.
        * apply Rabs_pos.
        * rewrite Rabs_right.
          -- generalize (simple_approx_le g nnegg n x); intros.
             apply H19.
          -- apply Rle_ge.
             apply simple_approx_pofrf.
        * apply H15.
      + rewrite Rmult_0_r.
        rewrite Rabs_R0.
        apply Rmult_le_pos.
        * apply nnegg.
        * apply H18.
    - apply all_almost; intros.
      unfold rvmult.
      apply is_Elim_seq_fin.
     apply is_lim_seq_mult'.
     + apply is_lim_seq_mult'.
       * now generalize (simple_approx_lim_seq g nnegg x).
       * apply is_lim_seq_const.
     + apply is_lim_seq_const.
  Qed.


  Theorem is_conditional_expectation_factor_out
        (f g ce ace : Ts -> R)
        {nnegace : NonnegativeFunction ace}          
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvce : RandomVariable dom2 borel_sa ce}
        {rvace : RandomVariable dom2 borel_sa ace}        
        {rvgf: RandomVariable dom borel_sa (rvmult f g)} :
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g) ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvabs f) ace ->
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
    intros.
    unfold is_conditional_expectation; intros.
    generalize (rv_pos_neg_id g); intros.
    assert (rv_eq  (rvmult (rvmult f g) (EventIndicator dec)) 
                   (rvplus (rvmult (rvmult f (pos_fun_part g)) (EventIndicator dec))
                           (rvopp (rvmult (rvmult f (neg_fun_part g)) (EventIndicator dec))))).
    {
      intro x.
      rv_unfold.
      specialize (H4 x).
      simpl.
      simpl in H4.
      rewrite H4 at 1.
      ring.
    }
    rewrite (Expectation_ext H5).
    assert (rv_eq (Rbar_rvmult (Rbar_rvmult (fun x : Ts => g x) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))
                  (Rbar_rvplus
                     (rvmult (rvmult (pos_fun_part g) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))
                     (rvopp (rvmult (rvmult (neg_fun_part g) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))))).
    {
      intro x.
      rv_unfold; unfold Rbar_rvmult.
      simpl.
      specialize (H4 x).
      simpl in H4.
      rewrite H4 at 1.
      apply Rbar_finite_eq.
      ring.
    }
    rewrite (Rbar_Expectation_ext H6).
    assert (RandomVariable dom borel_sa (rvmult f (fun x : Ts => pos_fun_part g x))).
    {
      apply rvmult_rv; trivial.
      apply RandomVariable_sa_sub; trivial.
      typeclasses eauto.
    }
    generalize (IsFiniteExpectation_prod_parts prts f g sub H0); intros isfinprod.
    destruct isfinprod.
    assert (rvgafpos : RandomVariable dom borel_sa
            (rvmult (rvabs f) (fun x : Ts => pos_fun_part g x))).
    {
      apply rvmult_rv.
      - typeclasses eauto.
      - apply RandomVariable_sa_sub; trivial.
        typeclasses eauto.
    }
    assert (rvgafneg : RandomVariable dom borel_sa
            (rvmult (rvabs f) (fun x : Ts => neg_fun_part g x))).
    {
      apply rvmult_rv.
      - typeclasses eauto.
      - apply RandomVariable_sa_sub; trivial.
        typeclasses eauto.
    }
    generalize (is_conditional_expectation_factor_out_nneg f (pos_fun_part g) ce ace H H8 H1 H2 P dec H3); intros.
    assert (RandomVariable dom borel_sa (rvmult f (fun x : Ts => neg_fun_part g x))).
    {
      apply rvmult_rv; trivial.
      apply RandomVariable_sa_sub; trivial.
      typeclasses eauto.
    }
    generalize (is_conditional_expectation_factor_out_nneg f (neg_fun_part g) ce ace H H9 H1 H2 P dec H3); intros.    
    rewrite Expectation_sum.
    rewrite H10.
    generalize (Expectation_opp  (rvmult (rvmult f (fun x : Ts => neg_fun_part g x)) (EventIndicator dec))); intros.
    simpl in H13; simpl; rewrite H13.
    simpl in H12; rewrite H12.
    - assert (Rbar_IsFiniteExpectation prts (Rbar_rvmult (Rbar_rvmult (fun x : Ts => Rmax (g x) 0) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))).
      {
        unfold Rbar_IsFiniteExpectation.
        simpl in H10.
        rewrite <- H10.
        apply IsFiniteExpectation_indicator; trivial.
        now apply sub.
      }
      assert (Rbar_IsFiniteExpectation prts 
                                       (Rbar_rvmult (Rbar_rvmult (fun x : Ts => Rmax (- g x) 0) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))).
      {
        unfold Rbar_IsFiniteExpectation.
        simpl in H12.
        rewrite <- H12.
        apply IsFiniteExpectation_indicator; trivial.
        now apply sub.
      }
      match_case; intros.
      match_case; intros.
      match_case_in H17; intros.
      + assert (is_finite r).
        {
          unfold Rbar_IsFiniteExpectation in H14.
          rewrite H16 in H14.
          case_eq r; intros; rewrite H19 in H14; now simpl in H14.
        }
        assert (is_finite r1).
        {
          unfold Rbar_IsFiniteExpectation in H15.
          rewrite H18 in H15.
          case_eq r1; intros; rewrite H20 in H15; now simpl in H15.          
        }
        rewrite <- H19.
        rewrite <- H19 in H16.
        rewrite H18 in H17.
        rewrite <- H20 in H17.
        inversion H17.
        rewrite <- H20.
        simpl.
        symmetry.
        apply Rbar_Expectation_sum_finite; trivial.
        * apply Real_Rbar_rv.
          apply rvmult_rv.
          -- apply rvmult_rv.
             ++ apply positive_part_rv.
                apply RandomVariable_sa_sub; trivial.
             ++ apply RandomVariable_sa_sub; trivial.
          -- apply EventIndicator_pre_rv.
             now apply sub.
        * apply Real_Rbar_rv.
          apply rvopp_rv.
          apply rvmult_rv.
          -- apply rvmult_rv.
             ++ apply negative_part_rv.
                apply RandomVariable_sa_sub; trivial.
             ++ apply RandomVariable_sa_sub; trivial.
          -- apply EventIndicator_pre_rv.
             now apply sub.
        * generalize (Rbar_Expectation_opp (rvmult (rvmult (fun x : Ts => Rmax (- g x) 0) (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x))); intros.
          simpl in H21.
          setoid_rewrite H18 in H21.
          rewrite <- H20 in H21.
          simpl in H21.
          assert (rv_eq 
                    (Rbar_rvopp
                       (fun omega : Ts =>
                          rvmult (rvmult (fun x : Ts => Rmax (- g x) 0) (fun x : Ts => ce x)) 
                                 (fun x : Ts => EventIndicator dec x) omega)) 
                    (fun omega : Ts =>
                       rvopp (rvmult (rvmult (fun x : Ts => Rmax (- g x) 0) (fun x : Ts => ce x)) 
                                     (fun x : Ts => EventIndicator dec x)) omega)).
          {
            intro x.
            unfold Rbar_rvopp; rv_unfold; simpl; apply Rbar_finite_eq; ring.
          }
          now rewrite (Rbar_Expectation_ext H23) in H21.
      + rewrite H18 in H17.
        discriminate.
      + match_case_in H17; intros.
         * rewrite H18 in H17; discriminate.
         * unfold Rbar_IsFiniteExpectation in H15.
           now rewrite H18 in H15.
      + unfold Rbar_IsFiniteExpectation in H14.
        now rewrite H16 in H14.
    - apply rvmult_rv.
      + apply rvmult_rv; trivial.
        apply RandomVariable_sa_sub; trivial.
        now apply positive_part_rv.
      + apply EventIndicator_pre_rv.
        now apply sub.
    - apply rvopp_rv.
      apply rvmult_rv.
      + apply rvmult_rv; trivial.
        apply RandomVariable_sa_sub; trivial.
        now apply negative_part_rv.
      + apply EventIndicator_pre_rv.
        now apply sub.
    - generalize (IsFiniteExpectation_indicator prts (rvmult f (fun x0 : Ts => pos_fun_part g x0)) dec); intros.
      cut_to H13; trivial.
      + generalize (IsFiniteExpectation_parts prts _ H13); intros.
        destruct H14.
        now apply IsFiniteNonnegExpectation.
      + now apply sub.
    - generalize (IsFiniteExpectation_indicator prts (rvmult f (fun x0 : Ts => neg_fun_part g x0)) dec); intros.
      cut_to H13; trivial.
      + generalize (IsFiniteExpectation_opp prts); intros.
        specialize (H14 _ H13).
        generalize (IsFiniteExpectation_parts prts _ H14); intros.
        destruct H15.
        now apply IsFiniteNonnegExpectation.
      + now apply sub.
  Qed.

  Lemma is_conditional_expectation_monotone_convergence
        (f : Ts -> R )
        (ce : Ts -> Rbar )
        (fn : nat -> Ts -> R)
        (cen : nat -> Ts -> Rbar)
        (rvf : RandomVariable dom borel_sa f)
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
        (nnf: NonnegativeFunction f)
        (nnce: Rbar_NonnegativeFunction ce)
        (rvfn : forall n, RandomVariable dom borel_sa (fn n))
        (nnfn : forall n, NonnegativeFunction (fn n))
        (nncen : forall n, Rbar_NonnegativeFunction (cen n))
        (rvcen : forall n, RandomVariable dom2 Rbar_borel_sa (cen n))
    :
    (forall (n:nat), Rbar_rv_le (fn n) f) ->
    (forall (n:nat), rv_le (fn n) (fn (S n))) ->
    (forall (n:nat), Rbar_rv_le (cen n) ce) ->
    (forall (n:nat), Rbar_rv_le (cen n) (cen (S n))) ->
    (forall (omega:Ts), is_Elim_seq (fun n => fn n omega) (f omega)) ->
    (forall (omega:Ts), is_Elim_seq (fun n => cen n omega) (ce omega)) ->
    (forall (n:nat), is_conditional_expectation dom2 (fn n) (cen n)) ->
    is_conditional_expectation dom2 f ce.
  Proof.
    intros fbound fle cebound cele limf limce iscen P decP saP.

    
    assert (rvmultf:
              RandomVariable dom borel_sa (rvmult f (EventIndicator decP))).
    {
      apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sub.
    } 

    assert (rvmultfn:forall n,
              RandomVariable dom borel_sa (rvmult (fn n) (EventIndicator decP))).
    {
      intros.
      apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sub.
    } 

    generalize (Rbar_monotone_convergence (rvmult f (EventIndicator decP))
                                     (fun n => rvmult (fn n) (EventIndicator decP))
                                     _
                                     (indicator_prod_pos f nnf decP)
                                     _
                                     (fun n => (indicator_prod_pos (fn n) (nnfn n) decP))

               )
    ; intros eqq1.
    cut_to eqq1.
    - {
        rewrite (Expectation_pos_pofrf _ (nnf:=(indicator_prod_pos f nnf decP))).
        rewrite <- (NNExpectation_Rbar_NNExpectation' _ _) in eqq1.
        rewrite <- eqq1.
        assert (rvmultce:
                  RandomVariable dom Rbar_borel_sa (Rbar_rvmult ce (EventIndicator decP))).
        {
          apply Rbar_rvmult_rv; trivial.
          - now apply RandomVariable_sa_sub.
          - apply Real_Rbar_rv.
            apply EventIndicator_pre_rv.
            now apply sub.
        } 
        
        assert (rvmultcen:forall n,
                   RandomVariable dom Rbar_borel_sa (Rbar_rvmult (cen n) (EventIndicator decP))).
        {
          intros.
          apply Rbar_rvmult_rv; trivial.
          - now apply RandomVariable_sa_sub.
          - apply Real_Rbar_rv.
            apply EventIndicator_pre_rv.
            now apply sub.
        } 

        assert (nnf_multce : Rbar_NonnegativeFunction
                               (Rbar_rvmult ce (fun x : Ts => EventIndicator decP x))).
        {
          apply Rbar_rvmult_nnf; trivial.
          red; simpl.
          apply EventIndicator_pos.
        } 

        assert (nnf_multcen : forall n, Rbar_NonnegativeFunction
                               (Rbar_rvmult (cen n) (fun x : Ts => EventIndicator decP x))).
        {
          intros.
          apply Rbar_rvmult_nnf; trivial.
          red; simpl.
          apply EventIndicator_pos.
        } 

        assert (nnf_multcen' : forall n, NonnegativeFunction
                               (Rbar_rvmult (cen n) (fun x : Ts => EventIndicator decP x))).
        {
          intros n.
          specialize (nnf_multcen n).
          red in nnf_multcen |- *.
          intros x.
          specialize (nnf_multcen x).
          unfold Rbar_rvmult in *.
          simpl in nnf_multcen.
          match_destr_in nnf_multcen; simpl; trivial; lra.
        } 
        
        generalize (Rbar_monotone_convergence (Rbar_rvmult ce (EventIndicator decP))
                                              (fun n => Rbar_rvmult (cen n) (EventIndicator decP))
                                              _ _ _ _)
        ; intros eqq2.
        cut_to eqq2.
        - rewrite (Rbar_Expectation_pos_pofrf _).
          f_equal.
          rewrite <- eqq2.
          apply ELim_seq_proper; intros n.
          specialize (iscen n _ decP saP).
          rewrite (Expectation_pos_pofrf _) in iscen.
          rewrite (Rbar_Expectation_pos_pofrf _) in iscen.
          invcs iscen.
          now rewrite <- (NNExpectation_Rbar_NNExpectation' _ _).
        - intros ??.
          unfold Rbar_rvmult, EventIndicator.
          apply Rbar_mult_le_compat_r.
          + match_destr; simpl; lra.
          + apply cebound.
        - intros ??.
          unfold Rbar_rvmult, EventIndicator.
          apply Rbar_mult_le_compat_r.
          + match_destr; simpl; lra.
          + apply cele.
        - intros.
          now apply is_Elim_seq_scal_r'.
      }
    - intros ??.
      unfold Rbar_rvmult, EventIndicator; simpl.
      apply Rmult_le_compat_r.
      + match_destr; simpl; lra.
      + apply fbound.
    - intros ??.
      unfold Rbar_rvmult, EventIndicator; simpl.
      apply Rmult_le_compat_r.
      + match_destr; simpl; lra.
      + apply fle.
    - intros.
      unfold rvmult.
      now apply (is_Elim_seq_scal_r' (fun n => fn n omega) (EventIndicator decP omega) (f omega)).
  Qed.
  
  Lemma is_conditional_expectation_monotone_convergence_almost
        (f : Ts -> R )
        (ce : Ts -> Rbar )
        (fn : nat -> Ts -> R)
        (cen : nat -> Ts -> Rbar)
        (rvf : RandomVariable dom borel_sa f)
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
        (nnf: almostR2 prts Rle (const 0) f)
        (nnce: almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) ce)
        (rvfn : forall n, RandomVariable dom borel_sa (fn n))
        (nnfn : forall n, almostR2 prts Rle (const 0) (fn n))
        (nncen : forall n, almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) (cen n))
        (rvcen : forall n, RandomVariable dom2 Rbar_borel_sa (cen n))
    :
    (forall (n:nat), almostR2 prts Rle (fn n) f) ->
    (forall (n:nat), almostR2 prts Rle (fn n) (fn (S n))) ->
    (forall (n:nat), almostR2 (prob_space_sa_sub prts sub) Rbar_le (cen n) ce) ->
    (forall (n:nat), almostR2 (prob_space_sa_sub prts sub) Rbar_le (cen n) (cen (S n))) ->
    (almost prts (fun omega => is_Elim_seq (fun n => fn n omega) (f omega))) ->
    (almost (prob_space_sa_sub prts sub) (fun (omega:Ts) => is_Elim_seq (fun n => cen n omega) (ce omega))) ->
    (forall (n:nat), is_conditional_expectation dom2 (fn n) (cen n)) ->
    is_conditional_expectation dom2 f ce.
  Proof.
    intros fnbound fnincr cenbound cenincr flim celim iscen.

    apply almost_forall in nnfn.
    apply almost_forall in nncen.
    apply almost_forall in fnbound.
    apply almost_forall in fnincr.
    apply almost_forall in cenbound.
    apply almost_forall in cenincr.

    generalize (almost_and _ nnf (almost_and _ nnfn (almost_and _ fnbound (almost_and _ fnincr flim))))
    ; intros almostf.
    generalize (almost_and _ nnce (almost_and _ nncen (almost_and _ cenbound (almost_and _ cenincr celim)))); intros almostce.
    
    destruct almostf as [pf [pfone pfH]].
    destruct almostce as [pce [pceone pceH]].

    (* we are going to use the following almost equal replacements *)
    
    pose (f' :=
            (rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec pf))) x) 0 then false else true)

                f
                (const 0)
            )).
    pose (ce' :=
            (Rbar_rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec pce))) x) 0 then false else true)

                ce
                (const (Finite 0))
         )).

    pose (fn' := fun n =>
                   (rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec pf))) x) 0 then false else true)
                             
                             (fn n)
                             (const 0)
         )).
    pose (cen' := fun n =>
                   (Rbar_rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec pce))) x) 0 then false else true)
                             
                             (cen n)
                             (const (Finite 0))
         )).
    
    assert (feqq:almostR2 prts eq f' f).
    {
      exists pf.
      split; trivial.
      intros.
      unfold f', EventIndicator, rvchoice.
      destruct (classic_dec pf x); try tauto.
      destruct (Req_EM_T 1 0); try lra.
    } 
    assert (ceeqq:almostR2 (prob_space_sa_sub prts sub) eq ce' ce).
    {
      exists pce.
      split; trivial.
      intros.
      unfold ce', EventIndicator, Rbar_rvchoice.
      destruct (classic_dec pce x); try tauto.
      now destruct (Req_EM_T 1 0); try lra.
    }

    assert (fneqq:forall n, almostR2 prts eq (fn' n) (fn n)).
    {
      intros.
      exists pf.
      split; trivial.
      intros.
      unfold fn', EventIndicator, rvchoice.
      destruct (classic_dec pf x); try tauto.
      destruct (Req_EM_T 1 0); try lra.
    } 
    assert (ceneqq:forall n, almostR2 (prob_space_sa_sub prts sub) eq (cen' n) (cen n)).
    {
      intros.
      exists pce.
      split; trivial.
      intros.
      unfold cen', EventIndicator, Rbar_rvchoice.
      destruct (classic_dec pce x); try tauto.
      now destruct (Req_EM_T 1 0); try lra.
    }

    assert (rvf' : RandomVariable dom borel_sa f').
    {
      unfold f'.
      apply rvchoice_rv; trivial; typeclasses eauto.
    } 
    assert (rvce' : RandomVariable dom2 Rbar_borel_sa ce').
    {
      unfold ce'.
      apply Rbar_rvchoice_rv; trivial; typeclasses eauto.
    }

    assert (rvfn' : forall n, RandomVariable dom borel_sa (fn' n)).
    {
      intros.
      unfold fn'.
      apply rvchoice_rv; trivial; typeclasses eauto.
    } 
    assert (rvcen' : forall n, RandomVariable dom2 Rbar_borel_sa (cen' n)).
    {
      intros.
      unfold cen'.
      apply Rbar_rvchoice_rv; trivial; typeclasses eauto.
    }
    
    cut (is_conditional_expectation dom2 f' ce').
    {
      apply is_conditional_expectation_proper; trivial.
      eapply almost_prob_space_sa_sub_lift; eauto.
    }

    assert (iscen' : forall n : nat, is_conditional_expectation dom2 (fn' n) (cen' n)).
    {
      intros.
      generalize (iscen n).
      apply is_conditional_expectation_proper.
      - now symmetry.
      - symmetry.
        eapply almost_prob_space_sa_sub_lift.
        apply ceneqq.
    } 

    eapply (@is_conditional_expectation_monotone_convergence _ _ fn' cen')
    ; unfold f', fn', ce', cen', rvchoice, Rbar_rvchoice, EventIndicator, const, pre_inter_of_collection in *
    ; repeat intros ?
    ; try (destruct (classic_dec _ _)
           ; destruct (Req_EM_T _ _); try lra
           ; try destruct (pfH _ e) as [? [? [? [??]]]]
           ; try destruct (pceH _ e) as [? [? [? [??]]]]
           ; simpl; trivial
           ; try apply Rbar_le_refl
           ; try apply Rle_refl
           ; try apply is_Elim_seq_const).
    - apply H0.
    - now apply iscen'.
  Qed.
End is_cond_exp.

Section is_cond_exp_props.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {dom3 : SigmaAlgebra Ts}
          (sub2 : sa_sub dom3 dom2).

  Theorem is_conditional_expectation_tower
        (f ce1: Ts -> R)
        (ce2: Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 borel_sa ce1}
        {rvce1' : RandomVariable dom borel_sa ce1}
        {rvce2 : RandomVariable dom3 Rbar_borel_sa ce2}
:
    is_conditional_expectation prts dom2 f (fun x => ce1 x) ->
    is_conditional_expectation prts dom3 f ce2 ->
    is_conditional_expectation prts dom3 ce1 ce2.
  Proof.
    unfold is_conditional_expectation.
    intros isce1 isce2 P decP saP.
    rewrite <- isce2; trivial.
    rewrite isce1; trivial.
    - rewrite Expectation_Rbar_Expectation.
      reflexivity.
    - apply sub2; trivial.
  Qed.

End is_cond_exp_props.

Section cond_exp_l2.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  (* For functions in the quotiented L2 space, we define conditional expectation
     via the orthonormal projection 
   *)
  Definition conditional_expectation_L2q
             (x:LpRRVq prts 2)
    : {v : L2RRVq_PreHilbert prts
        | unique
            (fun v : L2RRVq_PreHilbert prts =>
               ortho_phi prts dom2 v /\
               norm (minus (G:=(PreHilbert.AbelianGroup (L2RRVq_PreHilbert prts))) x v) =
               Glb_Rbar (fun r : R => exists w : L2RRVq_PreHilbert prts,
                             ortho_phi prts dom2 w /\
                             r = norm (minus (G:=(PreHilbert.AbelianGroup (L2RRVq_PreHilbert  prts)))x w)))
            v}.
  Proof.
    apply (ortho_projection_hilbert (L2RRVq_PreHilbert prts)
                                    (ortho_phi prts dom2)
                                    (ortho_phi_compatible_m prts sub)
                                    (ortho_phi_complete prts sub)
                                    x).
  Qed.

  Let nneg2 : nonnegreal := bignneg 2 big2.
  Canonical nneg2.

  (* Note that we lose uniqueness, since it only holds over the quotiented space. *)
  Definition conditional_expectation_L2 (f :LpRRV prts 2) :
    {v : LpRRV prts 2 
      | RandomVariable dom2 borel_sa v /\
        LpRRVnorm prts (LpRRVminus prts f v) =
        Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                      RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                      r = LpRRVnorm prts (LpRRVminus prts f w)) /\
        (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts f v) (LpRRVminus prts w v) <= 0) /\
        (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts v w = L2RRVinner prts (pack_LpRRV prts f) w) /\

        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (LpRRVnorm prts (LpRRVminus prts f z) =
                             Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                                           RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                                           r = LpRRVnorm prts (LpRRVminus prts f w))) -> LpRRV_eq prts z v) /\
        
        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts f z) (LpRRVminus prts w z) <= 0) -> LpRRV_eq prts z v) /\
        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts z w = L2RRVinner prts (pack_LpRRV prts f) w)  -> LpRRV_eq prts z v)

    }.
  Proof.
    destruct ((conditional_expectation_L2q (Quot _ f))).
    destruct u as [[HH1 HH2] HH3].
    destruct (charac_ortho_projection_subspace1 _ (ortho_phi_compatible_m _ sub) (Quot (LpRRV_eq prts) f) _ HH1)
      as [cops1_f _].
    destruct (charac_ortho_projection_subspace2 _ (ortho_phi_compatible_m _ sub) (Quot (LpRRV_eq prts) f) _ HH1)
      as [cops2_f _].
    specialize (cops1_f HH2).
    specialize (cops2_f HH2).
    red in HH1.
    apply constructive_indefinite_description in HH1.
    destruct HH1 as [y [eqqy rvy]].
    exists y.
    split; trivial.
    subst.
    unfold norm, minus, plus, opp in *; simpl in *.
    rewrite L2RRVq_norm_norm in HH2.
    autorewrite with quot in HH2.
    rewrite LpRRVq_normE in HH2.
    rewrite LpRRVminus_plus.
    unfold nonneg in HH2 |- *; simpl in *.
    rewrite HH2.
    assert (glb_eq:
              Glb_Rbar
                (fun r : R =>
                   exists w : LpRRVq prts 2,
                     ortho_phi prts dom2 w /\ r = Hnorm (LpRRVq_plus prts (Quot (LpRRV_eq prts) f) (LpRRVq_opp prts w)))
              =
              Glb_Rbar
                (fun r : R =>
                   exists w : LpRRV prts 2, RandomVariable dom2 borel_sa w /\ r = LpRRVnorm prts (LpRRVminus prts f w))).

    { 
      apply Glb_Rbar_eqset; intros.
      split; intros [w [wrv wnorm]].
      + rewrite L2RRVq_norm_norm in wnorm.
        destruct wrv as [w' [? rvw']]; subst.
        exists w'.
        split; trivial.
        autorewrite with quot.
        rewrite LpRRVq_normE.
        now rewrite LpRRVminus_plus.
      + subst.
        exists (Quot _ w).
        split.
        * exists w.
          split; trivial.
        * rewrite L2RRVq_norm_norm.
          autorewrite with quot.
          rewrite LpRRVq_normE.
          now rewrite LpRRVminus_plus.
    } 
    repeat split.
    - now f_equal.
    - intros.
      specialize (cops1_f (Quot _ w)).
      cut_to cops1_f.
      + unfold inner in cops1_f; simpl in cops1_f.
        LpRRVq_simpl.
        rewrite L2RRVq_innerE in cops1_f.
        etransitivity; try eapply cops1_f.
        right.
        apply L2RRV_inner_proper.
        * apply LpRRV_seq_eq; intros ?; simpl.
          rv_unfold; lra.
        * apply LpRRV_seq_eq; intros ?; simpl.
          rv_unfold; lra.
      + red; eauto.
    - intros.
      specialize (cops2_f (Quot _ w)).
      cut_to cops2_f.
      + unfold inner in cops2_f; simpl in cops2_f.
        repeat rewrite L2RRVq_innerE in cops2_f.
        apply cops2_f.
      + red; eauto.
    - intros x xrv xeqq.
      specialize (HH3 (Quot _ x)).
      cut_to HH3.
      + apply Quot_inj in HH3; try typeclasses eauto.
        now symmetry.
      + split.
        * unfold ortho_phi.
          eauto.
        * rewrite L2RRVq_norm_norm.
          autorewrite with quot.
          rewrite LpRRVq_normE.
          rewrite <- LpRRVminus_plus.
          unfold nonneg in *; simpl in *.
          rewrite xeqq.
          symmetry.
          now f_equal.
    - intros x xrv xeqq.
      specialize (HH3 (Quot _ x)).
      cut_to HH3.
      + apply Quot_inj in HH3; try typeclasses eauto.
        now symmetry.
      + split.
        * unfold ortho_phi.
          eauto.
        * destruct (charac_ortho_projection_subspace1 _
                                                      (ortho_phi_compatible_m _ sub)
                                                      (Quot (LpRRV_eq prts) f)
                                                      (Quot _ x))
            as [_ cops1_b].
          -- red; eauto.
          -- apply cops1_b; intros.
             destruct H as [z [? rvz]]; subst.
             specialize (xeqq _ rvz).
             etransitivity; try eapply xeqq.
             right.
             unfold inner, minus, plus, opp; simpl.
             LpRRVq_simpl.
             rewrite L2RRVq_innerE.
             apply L2RRV_inner_proper.
             ++ now rewrite <- LpRRVminus_plus.
             ++ now rewrite <- LpRRVminus_plus.
    - intros x xrv xeqq.
      specialize (HH3 (Quot _ x)).
      cut_to HH3.
      + apply Quot_inj in HH3; try typeclasses eauto.
        now symmetry.
      + split.
        * unfold ortho_phi.
          eauto.
        * destruct (charac_ortho_projection_subspace2 _
                                                      (ortho_phi_compatible_m _ sub)
                                                      (Quot (LpRRV_eq prts) f)
                                                      (Quot _ x))
            as [_ cops2_b].
          -- red; eauto.
          -- apply cops2_b; intros.
             destruct H as [z [? rvz]]; subst.
             specialize (xeqq _ rvz).
             unfold inner, minus, plus, opp; simpl.
             repeat rewrite L2RRVq_innerE.
             rewrite xeqq.
             apply L2RRV_inner_proper; try reflexivity.
             now apply LpRRV_seq_eq; intros ?; simpl.
  Qed.

  Definition conditional_expectation_L2fun (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {isl : IsLp prts 2 f} :
    LpRRV prts 2
    := proj1_sig (conditional_expectation_L2 (pack_LpRRV prts f)).

  Instance conditional_expectation_L2fun_rv
           (f : Ts -> R) 
           {rv : RandomVariable dom borel_sa f}
           {isl : IsLp prts 2 f} :
    RandomVariable dom2 borel_sa (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Instance conditional_expectation_L2fun_L2
           (f : Ts -> R) 
           {rv : RandomVariable dom borel_sa f}
           {isl : IsLp prts 2 f} :
    IsLp prts 2 (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    destruct x; trivial.
  Qed.

  Lemma conditional_expectation_L2fun_eq
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) (conditional_expectation_L2fun f)) =
    Glb_Rbar
      (fun r : R =>
         exists w : LpRRV prts 2,
           RandomVariable dom2 borel_sa w /\ r = LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) w)).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Lemma conditional_expectation_L2fun_eq_finite
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    is_finite (Glb_Rbar
      (fun r : R =>
         exists w : LpRRV prts 2,
           RandomVariable dom2 borel_sa w /\ r = LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) w))).
  Proof.
    assert (phi_ex:exists y : L2RRVq_PreHilbert prts, ortho_phi prts dom2 y).
    {
      unfold ortho_phi.
      exists (LpRRVq_zero _).
      exists (LpRRVzero _).
      split.
      - reflexivity.
      - typeclasses eauto.
    } 
    generalize (@ortho_projection_aux (L2RRVq_PreHilbert prts)
                                      (ortho_phi prts dom2)
                                      phi_ex
                                      (Quot _ (pack_LpRRV prts f)))
    ; intros.
    erewrite Glb_Rbar_eqset; try eapply H.
    intros.
    split.
    - intros [?[??]]; subst.
      exists (Quot _ x0).
      split.
      + red; eauto.
      + unfold norm; simpl.
        rewrite L2RRVq_norm_norm.
        unfold minus, plus, opp; simpl.
        LpRRVq_simpl.
        rewrite LpRRVq_normE.
        now rewrite LpRRVminus_plus.
    - intros [?[??]]; subst.
      destruct H0 as [?[??]]; subst.
      exists x.
      split; trivial.
      unfold norm; simpl.
      rewrite L2RRVq_norm_norm.
      unfold minus, plus, opp; simpl.
      LpRRVq_simpl.
      rewrite LpRRVq_normE.
      now rewrite LpRRVminus_plus.
  Qed.

  Lemma conditional_expectation_L2fun_eq1
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts (pack_LpRRV prts f) (conditional_expectation_L2fun f)) (LpRRVminus prts w (conditional_expectation_L2fun f)) <= 0).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Lemma conditional_expectation_L2fun_eq2
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (conditional_expectation_L2fun f) w = L2RRVinner prts (pack_LpRRV prts f) w).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Lemma conditional_expectation_L2fun_eq3
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    is_conditional_expectation prts dom2 f (fun x => (conditional_expectation_L2fun f) x).
  Proof.
    unfold is_conditional_expectation.
    intros.
    assert (RandomVariable dom2 borel_sa (EventIndicator dec)) by now apply EventIndicator_pre_rv.
    assert (RandomVariable dom borel_sa (EventIndicator dec)) by now apply RandomVariable_sa_sub.
    generalize (conditional_expectation_L2fun_eq2 f (pack_LpRRV prts (EventIndicator dec))); intros.
    cut_to H2.
    - unfold L2RRVinner in H2.
      simpl in H2.
      symmetry in H2.
      unfold FiniteExpectation, proj1_sig in H2.
      do 2 match_destr_in H2.
      subst.
      erewrite Expectation_ext; [rewrite e | reflexivity].
      unfold Rbar_rvmult; simpl.
      rewrite <- Expectation_Rbar_Expectation.
      erewrite Expectation_ext; [rewrite e0 | reflexivity].
      trivial.
    - now apply EventIndicator_pre_rv.
  Qed.

  Lemma conditional_expectation_L2fun_unique
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        (z: LpRRV prts 2)
        {z_rv:RandomVariable dom2 borel_sa z} :
    (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) z) =
     Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                   RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                   r = LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) w))) ->
    LpRRV_eq prts z (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    intuition.
  Qed.

  Lemma conditional_expectation_L2fun_unique1
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        (z: LpRRV prts 2)
        {z_rv:RandomVariable dom2 borel_sa z} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts (pack_LpRRV prts f) z) (LpRRVminus prts w z) <= 0) -> LpRRV_eq prts z (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    intuition.
  Qed.

  Lemma conditional_expectation_L2fun_unique2
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        (z: LpRRV prts 2)
        {z_rv:RandomVariable dom2 borel_sa z} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts z w = L2RRVinner prts (pack_LpRRV prts f) w)  -> LpRRV_eq prts z (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    intuition.
  Qed.

  Lemma conditional_expectation_L2fun_const
        (c : R) :
    LpRRV_eq prts
             (LpRRVconst prts c)
             (conditional_expectation_L2fun (const c)).
  Proof.
    apply conditional_expectation_L2fun_unique2.
    - typeclasses eauto.
    - intros.
      now unfold LpRRVconst.
  Qed.

  Instance IsLp_min_const_nat (f : Ts -> R) (n : nat) 
           {nneg : NonnegativeFunction f} :
    IsLp prts 2 (rvmin f (const (INR n))).
  Proof.
    intros.
    apply IsLp_bounded with (rv_X2 := const (power (INR n) 2)).
    - intro x.
      unfold rvpower, rvabs, rvmin, const.
      apply Rle_power_l; try lra.
      split.
      + apply Rabs_pos.
      + rewrite Rabs_right.
        apply Rmin_r.
        specialize (nneg x).
        apply Rmin_case; try lra.
        apply Rle_ge, pos_INR.
    - apply IsFiniteExpectation_const.
  Qed.

  Lemma conditional_expectation_L2fun_proper (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    almostR2 prts eq f1 f2 ->
    LpRRV_eq prts
             (conditional_expectation_L2fun f1)
             (conditional_expectation_L2fun f2).
  Proof.
    intros eqq.
    unfold conditional_expectation_L2fun, proj1_sig.
    repeat match_destr.
    destruct a as [xrv [xeq [? [? [xuniq ?]]]]].
    rename x0 into y.
    destruct a0 as [yrv [yeq [? [? [yuniq ?]]]]].
    apply yuniq; trivial.
    rewrite (LpRRV_norm_proper prts _ (LpRRVminus prts (pack_LpRRV prts f2) x)) in xeq.
    - unfold nneg2, bignneg, nonneg in *.
      rewrite xeq.
      f_equal.
      apply Glb_Rbar_eqset.
      split; intros [w [wrv wnorm]].
      + subst.
        exists w.
        split; trivial.
        apply LpRRV_norm_proper.
        apply LpRRV_minus_proper; trivial.
        reflexivity.
      + subst.
        exists w.
        split; trivial.
        apply LpRRV_norm_proper.
        apply LpRRV_minus_proper; trivial.
        * now symmetry.
        * reflexivity.
    - apply LpRRV_minus_proper; trivial.
      reflexivity.
  Qed.

  Lemma conditional_expectation_L2fun_nonneg (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        {nneg: NonnegativeFunction f} :
    almostR2 (prob_space_sa_sub prts sub) Rle (const 0) (conditional_expectation_L2fun f).
  Proof.
    generalize (conditional_expectation_L2fun_eq3 f); intros.
    unfold is_conditional_expectation in H.
    apply Expectation_mult_indicator_almost_nonneg; [typeclasses eauto|].
    intros.
    destruct P.
    specialize (H x dec s).
    rewrite Expectation_prob_space_sa_sub.
    - simpl.
      unfold Rbar_rvmult, rvmult in *; simpl in *.
      rewrite <- Expectation_Rbar_Expectation in H.
      rewrite <- H.
      erewrite Expectation_pos_pofrf.
      generalize (NonnegExpectation_pos (rvmult f (EventIndicator dec))); intros.
      rv_unfold; simpl.
      match_case; intros.
      + simpl in H0.
        now rewrite H1 in H0.
      + simpl in H0.
        now rewrite H1 in H0.
    - apply rvmult_rv.
      + apply conditional_expectation_L2fun_rv.
      + now apply EventIndicator_pre_rv.
  Qed.
  
  Lemma conditional_expectation_L2fun_nonneg_prts (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        {nneg: NonnegativeFunction f} :
    almostR2 prts Rle (const 0) (conditional_expectation_L2fun f).
  Proof.
    apply almostR2_prob_space_sa_sub_lift with (sub0 := sub).
    now apply conditional_expectation_L2fun_nonneg.
  Qed.

  Local Existing Instance Rbar_le_pre.

  Lemma conditional_expectation_L2fun_plus f1 f2
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    LpRRV_eq prts
             (conditional_expectation_L2fun (rvplus f1 f2))
             (LpRRVplus prts (conditional_expectation_L2fun f1) (conditional_expectation_L2fun f2)).
  Proof.
    symmetry.
    apply (conditional_expectation_L2fun_unique2)
    ; try typeclasses eauto.
    intros.
    replace (pack_LpRRV prts (rvplus f1 f2)) with
        (LpRRVplus prts (pack_LpRRV prts f1) (pack_LpRRV prts f2)) by reflexivity.
    repeat rewrite L2RRV_inner_plus.
    f_equal
    ; now apply conditional_expectation_L2fun_eq2.
  Qed.
  
End cond_exp_l2.

Section cond_exp2.      

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Lemma conditional_expectation_L2fun_le (f1 f2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    rv_le f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) Rle (conditional_expectation_L2fun prts sub f1) 
             (conditional_expectation_L2fun prts sub f2).
  Proof.
    intros.
    generalize (conditional_expectation_L2fun_eq3 prts sub f1); intro eqq1.
    generalize (conditional_expectation_L2fun_eq3 prts sub f2); intros eqq2.
    assert (isfe1:IsFiniteExpectation prts f1) by (apply (IsLp_Finite prts 2); trivial; lra).
    assert (isfe2:IsFiniteExpectation prts f2) by (apply (IsLp_Finite prts 2); trivial; lra).
    generalize (is_conditional_expectation_isfe prts f2 (fun x => (conditional_expectation_L2fun prts sub f2) x) eqq2 isfe2); intros isce2.  
    apply Expectation_mult_indicator_almost_le;
      [apply conditional_expectation_L2fun_rv |   
       apply conditional_expectation_L2fun_rv | | ].
    apply IsFiniteExpectation_prob_space_sa_sub_f; trivial.
    apply conditional_expectation_L2fun_rv.
    apply Rbar_finexp_finexp in isce2; trivial.
    apply Real_Rbar_rv.
    apply RandomVariable_sa_sub; trivial.
    apply conditional_expectation_L2fun_rv.
    intros.
    destruct P.
    specialize (eqq1 x dec s).
    specialize (eqq2 x dec s).
    assert (RandomVariable 
              dom2 borel_sa
              (rvmult (conditional_expectation_L2fun prts sub f1) (EventIndicator dec))).
    {
      apply rvmult_rv.
      - apply conditional_expectation_L2fun_rv.
      - apply EventIndicator_pre_rv.
        simpl.
        apply s.
    }
    assert (RandomVariable dom2 borel_sa
                           (rvmult (conditional_expectation_L2fun prts sub f2) (EventIndicator dec))).
    {
      apply rvmult_rv.
      - apply conditional_expectation_L2fun_rv.
      - apply EventIndicator_pre_rv.
        simpl.
        apply s.
    }
    rewrite Expectation_prob_space_sa_sub; trivial.
    unfold Rbar_rvmult in *; simpl in *.
    rewrite <- Expectation_Rbar_Expectation in eqq1, eqq2.
    unfold rvmult; simpl.
    simpl; rewrite <- eqq1.
    match_case; intros.
    - rewrite Expectation_prob_space_sa_sub; trivial.
      simpl; rewrite <- eqq2.
      match_case; intros.
      + apply Expectation_le with (rv_X1 := (rvmult f1 (EventIndicator dec)))
                                  (rv_X2 := (rvmult f2 (EventIndicator dec))); trivial.
        {
          intro z.
          rv_unfold.
          match_destr.
          - now do 2 rewrite Rmult_1_r.
          - lra.
        }
      + generalize (IsFiniteExpectation_indicator prts f2 dec)
        ; intros HH.
        cut_to HH; trivial.
        * red in HH.
          simpl in HH.
          now rewrite H3 in HH.
        * simpl.
          now apply sub.
    - + generalize (IsFiniteExpectation_indicator prts f1 dec)
        ; intros HH.
        cut_to HH; trivial.
        * red in HH.
          simpl in HH.
          now rewrite H2 in HH.
        * simpl.
          now apply sub.
  Qed.

  Lemma conditional_expectation_L2fun_le_prts (f1 f2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    rv_le f1 f2 ->
    almostR2 prts Rle (conditional_expectation_L2fun prts sub f1) 
             (conditional_expectation_L2fun prts sub f2).
  Proof.
    intros.
    apply almostR2_prob_space_sa_sub_lift with (sub0 := sub).
    now apply conditional_expectation_L2fun_le.
  Qed.

  Local Existing Instance Rbar_le_pre.
  Local Existing Instance IsLp_min_const_nat.
  Local Existing Instance conditional_expectation_L2fun_rv.

  Definition NonNegConditionalExpectation (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {nnf : NonnegativeFunction f} : Ts -> Rbar :=
    Rbar_rvlim (fun n => LpRRV_rv_X _ (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))).

  Lemma NonNegCondexp_almost_increasing (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almost (prob_space_sa_sub prts sub)
           (fun x => 
              forall n,
                conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x
                <= conditional_expectation_L2fun prts sub (rvmin f (const (INR (S n)))) x).
  Proof.
    apply almost_forall.
    intros.
    apply conditional_expectation_L2fun_le.
    intro x.
    rv_unfold.
    apply Rle_min_compat_l.
    apply le_INR.
    lia.
  Qed.

  Lemma NonNegCondexp_almost_increasing_prts (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almost prts
           (fun x => 
              forall n,
                conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x
                <= conditional_expectation_L2fun prts sub (rvmin f (const (INR (S n)))) x).
  Proof.
    apply almost_prob_space_sa_sub_lift with (sub0 := sub).
    apply NonNegCondexp_almost_increasing.
  Qed.

  Lemma almost_Rbar_rvlim_condexp_incr_indicator_rv (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} 
        (E : event dom2) :
    ps_P (ProbSpace:=(prob_space_sa_sub prts sub)) E = 1 ->
    (forall x0 : Ts,
        E x0 ->
        forall n : nat,
          conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x0 <=
          conditional_expectation_L2fun prts sub (rvmin f (const (INR (S n)))) x0) ->
    (RandomVariable 
       dom2 Rbar_borel_sa
       (Rbar_rvlim
          (fun n0 : nat =>
             rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n0))))
                    (EventIndicator (classic_dec E))))).
  Proof.
    intros.
    apply Rbar_rvlim_rv.
    - typeclasses eauto.
  Qed.

  Lemma NonNegCondexp_almost_nonneg (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) (NonNegConditionalExpectation f).
  Proof.
    unfold NonNegConditionalExpectation.
    assert (almost (prob_space_sa_sub prts sub)
                   (fun x => forall n,
                        0 <= (conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))) x)).
    {
      apply almost_forall.
      intros.
      apply conditional_expectation_L2fun_nonneg.
      intro x.
      unfold rvmin, const.
      apply Rmin_glb; trivial.
      apply pos_INR.
    }
    destruct H as [? [? ?]].
    exists x.
    split; trivial.
    intros.
    specialize (H0 x0 H1).
    unfold const, Rbar_rvlim.
    replace (Finite 0) with (ELim_seq (fun _ => 0)) by apply ELim_seq_const.
    apply ELim_seq_le_loc.
    apply filter_forall; intros.
    apply H0.
  Qed.

  Lemma NonNegCondexp_almost_nonneg_prts (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almostR2 prts Rbar_le (const 0) (NonNegConditionalExpectation f).
  Proof.
    apply almost_prob_space_sa_sub_lift with (sub0 := sub).
    apply NonNegCondexp_almost_nonneg.
  Qed.

  Lemma rvlim_rvmin_indicator (f : Ts -> R) (P:pre_event Ts) (dec:dec_pre_event P) :
    rv_eq (fun  x=> Finite (rvmult f (EventIndicator dec) x))
          (Rbar_rvlim (fun n : nat => rvmult (rvmin f (const (INR n))) (EventIndicator dec))).
  Proof.
    intros a.
    unfold rvmult.
    unfold Rbar_rvlim.
    rewrite Elim_seq_fin.
    rewrite Lim_seq_scal_r.
    generalize (rvlim_rvmin f); intros HH.
    unfold Rbar_rvlim in HH.
    rewrite <- Elim_seq_fin.
    simpl in *.
    unfold rvmin, const.
    rewrite HH.
    now simpl.
  Qed.
    
  Lemma NonNegCondexp_is_Rbar_condexp_almost0  (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    exists (g : nat -> Ts -> R),
      (forall n, (NonnegativeFunction (g n)))
      /\ (forall n, (rv_le (g n) (g (S n))))
      /\ RandomVariable dom2 Rbar_borel_sa (Rbar_rvlim g)
      /\ exists (g_rv:forall n, RandomVariable dom2 borel_sa (g n)),
          (forall n, is_conditional_expectation prts dom2 (rvmin f (const (INR n))) (g n)).
  Proof.
    assert (HHsuc:forall n, rv_le (rvmin f (const (INR n))) (rvmin f (const (INR (S n))))).
    {
      intros n ?.
      rv_unfold.
      apply Rle_min_compat_l.
      apply le_INR; lia.
    }
    
    destruct (almost_forall _ (fun n => conditional_expectation_L2fun_le (rvmin f (const (INR n))) (rvmin f (const (INR (S n)))) (HHsuc n))) as [? [??]].
    destruct (almost_forall _ (fun n => conditional_expectation_L2fun_nonneg prts sub (rvmin f (const (INR n)))))
      as [? [??]].
    pose (E := event_inter x x0).    
    assert (ps_P (ProbSpace := (prob_space_sa_sub prts sub)) E = 1).
    {
      unfold E.
      now rewrite ps_inter_l1.
    }
    exists (fun n => rvmult 
               (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
               (EventIndicator (classic_dec E))).
    assert (g_rv :  forall n, RandomVariable dom2 borel_sa
                                        (rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                                                (EventIndicator (classic_dec E)))).
    {
      typeclasses eauto.
    }
    repeat split.
    - intros n a.
      unfold EventIndicator, rvmult; simpl.
      match_destr; try lra.
      field_simplify.
      destruct p as [px px0].
      apply (H2 _ px0).
    - intros n a.
      unfold EventIndicator, rvmult; simpl.
      match_destr; try lra.
      field_simplify.
      destruct p as [px px0].
      apply (H0 _ px).
    -  apply almost_Rbar_rvlim_condexp_incr_indicator_rv; trivial.
       intros.
       apply H0.
       apply H4.
    - exists g_rv.
      intros n.
      + assert (eqq1: (almostR2 (prob_space_sa_sub prts sub) eq ((rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                                                                         (EventIndicator (classic_dec E))))
                                (conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))))).
        {
          exists E.
          split; trivial.
          intros.
          rv_unfold.
          match_destr; [| tauto].
          lra.
        }
        assert (rv2:RandomVariable dom borel_sa
           (rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                   (EventIndicator (classic_dec E)))).
        {
          apply rvmult_rv.
          - apply RandomVariable_sa_sub; trivial.
            apply conditional_expectation_L2fun_rv.
          - apply EventIndicator_pre_rv.
            apply sub.
            apply sa_sigma_event_pre.
        }
        
        generalize (is_conditional_expectation_proper prts sub)
        ; intros HH.
        generalize (HH (rvmin f (const (INR n))) (rvmin f (const (INR n)))
                       (fun x => conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x)
                       (rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                               (EventIndicator (classic_dec E))))
                   
        ; intros HH2.
        apply (HH2 _ _ _ _ (reflexivity _)); clear HH HH2.
        * apply almost_f_equal.
          apply (almost_prob_space_sa_sub_lift _ sub).
          symmetry in eqq1.
          apply eqq1.
        * apply conditional_expectation_L2fun_eq3.
  Qed.

  Lemma NonNegCondexp_is_Rbar_condexp_g  (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    exists (g : nat -> Ts -> R),
      Rbar_NonnegativeFunction (Rbar_rvlim g)
      /\ exists (g_rv : RandomVariable dom2 Rbar_borel_sa (Rbar_rvlim g)),
        is_conditional_expectation prts dom2 f (Rbar_rvlim g).      
  Proof.
    destruct (NonNegCondexp_is_Rbar_condexp_almost0 f) as [g [gnnf [gincr [glimrv [grv giscond]]]]].
    generalize 3; intros.
    exists g.
    split.
    - now apply Rbar_rvlim_nnf.
    - exists glimrv.
      unfold is_conditional_expectation.
      intros.
      assert (nnexpg: forall n : nat,
                 IsFiniteExpectation prts (g n)).
      {
        intros.
        generalize  (is_conditional_expectation_isfe prts
                                                     (rvmin f (const (INR n))) 
                                                     (g n)); intros.
        cut_to H1; trivial.
        - apply Rbar_finexp_finexp in H1; trivial.
          apply Real_Rbar_rv.
          apply RandomVariable_sa_sub; trivial.
        - typeclasses eauto.
      } 
      assert (forall n : nat,
                 RandomVariable dom2 borel_sa
                                (rvmult (g n) (EventIndicator dec))).
      {
        intros.
        apply rvmult_rv.
        - typeclasses eauto.
        - now apply EventIndicator_pre_rv.
      }
      assert (forall n, 
                 RandomVariable dom borel_sa
                                (rvmult (g n) (EventIndicator dec))).
      {
        intros.
        apply RandomVariable_sa_sub; trivial.
      }
      assert  (forall n : nat,
                  NonnegativeFunction
                    (rvmult (g n)
                            (EventIndicator dec)
              )) by (intros; now apply indicator_prod_pos).
      generalize (monotone_convergence_Rbar_rvlim_fin
                    (fun n => rvmult (g n) (EventIndicator dec)) H2 H3); intros.
      cut_to H4.
      + assert 
          (rv_eq
             (Rbar_rvlim
                (fun n : nat =>
                   rvmult (g n) (EventIndicator dec)))
             (Rbar_rvmult
                (Rbar_rvlim g)
                (fun x : Ts => EventIndicator dec x))).
        {
          intro x.
          rv_unfold.
          unfold Rbar_rvlim, Rbar_rvmult.
          destruct (dec x).
          - repeat rewrite Elim_seq_fin.
            rewrite Lim_seq_mult.
            + now rewrite Lim_seq_const.
            + apply ex_lim_seq_incr.
              intros.
              apply gincr.
            + apply ex_lim_seq_const.
            + rewrite Lim_seq_const.
              unfold ex_Rbar_mult.
              match_destr.
          - setoid_rewrite Rmult_0_r.
            rewrite ELim_seq_const.
            now rewrite Rbar_mult_0_r.
        }
        rewrite <- (Rbar_Expectation_ext H5); clear H5.
        erewrite Rbar_Expectation_pos_pofrf.
        rewrite <- H4.
        erewrite Expectation_pos_pofrf.
        f_equal.
        eassert (forall n,
                    NonnegExpectation (rvmult (rvmin f (const (INR n))) (EventIndicator dec)) =
                    NonnegExpectation (rvmult (g n) (EventIndicator dec))).
        {
          intros.
          unfold is_conditional_expectation in giscond.
          specialize (giscond n P dec H0).
          unfold Rbar_rvmult in giscond; simpl in *.
          rewrite <- Expectation_Rbar_Expectation in giscond.
          rewrite (Expectation_pos_pofrf _ (nnf:=_)) in giscond.
          rewrite (Expectation_pos_pofrf _ (nnf:=_))in giscond.
          now inversion giscond.
        }
        erewrite ELim_seq_ext.
        2: {
          intros.
          rewrite <- H5.
          reflexivity.
        }
        rewrite (monotone_convergence_Rbar_rvlim_fin
                   (fun n =>  (rvmult (rvmin f (const (INR n))) (EventIndicator dec)))).
        * rewrite NNExpectation_Rbar_NNExpectation.
          apply Rbar_NonnegExpectation_ext; intros a.
          now rewrite rvlim_rvmin_indicator.
        * intros.
          apply rvmult_rv.
          -- typeclasses eauto.
          -- apply EventIndicator_pre_rv.
             now apply sub.
        * intros n x.
          rv_unfold.
          match_destr.
          -- do 2 rewrite Rmult_1_r.
             apply Rle_min_compat_l.
             apply le_INR.
             lia.
          -- lra.
      + intros n x.
        rv_unfold.
        match_destr.
        * do 2 rewrite Rmult_1_r.
          apply gincr.
        * lra.
  Qed.

  Lemma NonNegCondexp'  (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    exists g : Ts -> Rbar,
      Rbar_NonnegativeFunction g
      /\ exists (g_rv : RandomVariable dom2 Rbar_borel_sa g),
          is_conditional_expectation prts dom2 f g.
  Proof.
    destruct (NonNegCondexp_is_Rbar_condexp_g f) as [g [?[??]]].
    exists (Rbar_rvlim g); eauto.
  Qed.

  Definition IsFiniteExpectation_dec (f: Ts -> R) :
    {IsFiniteExpectation prts f} + {~ IsFiniteExpectation prts f}.
  Proof.
    unfold IsFiniteExpectation.
    repeat match_destr; eauto.
  Defined.
  
  Lemma NonNegCondexp''  (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    { g : Ts -> Rbar |
      Rbar_NonnegativeFunction g /\
      (RandomVariable dom2 borel_sa f -> g = (fun x => Finite (f x)))
      /\ (IsFiniteExpectation prts f -> exists gr, g = fun x => Finite (gr x))
      /\ exists (g_rv : RandomVariable dom2 Rbar_borel_sa g),
          is_conditional_expectation prts dom2 f g }.
  Proof.
    apply constructive_indefinite_description.
    destruct (classic (RandomVariable dom2 borel_sa f)) as [rv2 | nrv2].
    - exists (fun x => Finite (f x)).
      repeat split; eauto 2.
      eexists.
      apply is_conditional_expectation_id.
    - destruct (NonNegCondexp' f) as [ce [? [??]]].
      destruct (IsFiniteExpectation_dec f).
      + exists (fun x => Finite (Rbar_finite_part ce x)).
        repeat split; try tauto; eauto 2.
        * unfold Rbar_finite_part.
          intros a.
          specialize (H a).
          destruct (ce a); simpl; trivial; lra.
        * eexists.
          now apply is_conditional_expectation_isfe_finite_part.
      + exists ce.
        repeat split; eauto 2; tauto.
  Qed.

  (* This is the definition of Nonnegative Conditional Expectation that we want to use.
     Unlike the NonNegConditionalExpectation definition above, it ensures that certain
     basic properties hold everywhere, instead of almost.
   *)
  Definition NonNegCondexp  (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {nnf : NonnegativeFunction f} : Ts -> Rbar
    := proj1_sig (NonNegCondexp'' f).

  Global Instance NonNegCondexp_nneg (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f}
         {nnf : NonnegativeFunction f} :
    Rbar_NonnegativeFunction (NonNegCondexp f).
  Proof.
    unfold NonNegCondexp, proj1_sig; match_destr.
    destruct a as [?[??]]; eauto.
  Qed.

  Global Instance NonNegCondexp_rv (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f}
         {nnf : NonnegativeFunction f} :
    RandomVariable dom2 Rbar_borel_sa (NonNegCondexp f).
  Proof.
    unfold NonNegCondexp, proj1_sig; match_destr.
    destruct a as [?[?[?[??]]]]; eauto.
  Qed.

  Lemma NonNegCondexp_cond_exp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    is_conditional_expectation prts dom2 f (NonNegCondexp f).
  Proof.
    unfold NonNegCondexp.
    unfold is_conditional_expectation; intros.
    unfold proj1_sig.
    match_destr.
    destruct a as [?[?[?[??]]]]; eauto.
  Qed.

  Lemma NonNegCondexp_finite (f : Ts -> R)
          {rv : RandomVariable dom borel_sa f}
          {nnf : NonnegativeFunction f}
          {rvce : RandomVariable dom2 Rbar_borel_sa (NonNegCondexp f)}
          {isfe:IsFiniteExpectation prts f} :
      exists gr, NonNegCondexp f = fun x => Finite (gr x).
  Proof.
    unfold NonNegCondexp.
    unfold is_conditional_expectation; intros.
    unfold proj1_sig.
    match_destr.
    destruct a as [?[?[?[??]]]]; eauto.
  Qed.

  Lemma NonNegCondexp_id (f : Ts -> R)
        {rv : RandomVariable dom borel_sa f}
        {rv2 : RandomVariable dom2 borel_sa f}
        {nnf : NonnegativeFunction f}
        {rvce : RandomVariable dom2 Rbar_borel_sa (NonNegCondexp f)} :
    NonNegCondexp f = (fun x => Finite (f x)).
  Proof.
    unfold NonNegCondexp.
    unfold is_conditional_expectation; intros.
    unfold proj1_sig.
    match_destr.
    destruct a as [?[?[?[??]]]]; eauto.
  Qed.

  Lemma conditional_expectation_L2fun_cond_exp 
        (f : Ts -> R)
        {rv : RandomVariable dom borel_sa f} {isl : IsLp prts 2 f} :
    is_conditional_expectation prts dom2 f (LpRRV_rv_X _ (conditional_expectation_L2fun prts sub f)).
  Proof.
    intros ???.
    unfold Rbar_rvmult; simpl.
    now apply conditional_expectation_L2fun_eq3.
  Qed.    

  Lemma NonNegCondexp_ext (f1 f2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {nnf1 : NonnegativeFunction f1}
        {nnf2 : NonnegativeFunction f2} :
    rv_eq f1 f2 ->
    rv_eq (NonNegCondexp f1) (NonNegCondexp f2).
  Proof.
    (* classically true *)
    intros ??.
    assert (f1 = f2) by now apply functional_extensionality.
    subst.
    f_equal
    ; apply proof_irrelevance.
  Qed.

  Definition ConditionalExpectation (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f} : Ts -> Rbar :=
    Rbar_rvminus (NonNegCondexp (pos_fun_part f))
                 (NonNegCondexp (neg_fun_part f)).

  Lemma Condexp_nneg_simpl (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    rv_eq (ConditionalExpectation f) (NonNegCondexp f).
  Proof.
    unfold ConditionalExpectation; intros ?.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
    rewrite <- (NonNegCondexp_ext _ _ (pos_fun_part_pos _)).
    rewrite <- (NonNegCondexp_ext _ _ (neg_fun_part_pos f) (nnf1:=nnfconst _ (Rle_refl _))).
    rewrite (NonNegCondexp_id (const 0)).
    unfold const; simpl.
    rewrite Ropp_0.
    now rewrite Rbar_plus_0_r.
  Qed.    

  Lemma ConditionalExpectation_ext (f1 f2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2} :
    rv_eq f1 f2 ->
    rv_eq (ConditionalExpectation f1) (ConditionalExpectation f2).
  Proof.
    intros ??.
    unfold ConditionalExpectation.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
    f_equal.
    - apply NonNegCondexp_ext; intros ?.
      unfold pos_fun_part; simpl.
      now f_equal.
    - f_equal.
      apply NonNegCondexp_ext; intros ?.
      unfold neg_fun_part; simpl.
      f_equal.
      now rewrite H.
  Qed.      

  Global Instance Condexp_rv (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f} :
    RandomVariable dom2 Rbar_borel_sa (ConditionalExpectation f).
  Proof.
    unfold ConditionalExpectation, Rbar_rvminus.
    apply Rbar_rvplus_rv.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

  Lemma Condexp_cond_exp_nneg (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:NonnegativeFunction f}
    :
      is_conditional_expectation prts dom2 f (ConditionalExpectation f).
  Proof.
    generalize (NonNegCondexp_cond_exp f).
    apply is_conditional_expectation_proper; trivial.
    - reflexivity.
    - apply all_almost; intros.
      symmetry.
      apply Condexp_nneg_simpl.
  Qed.
  
  Theorem Condexp_cond_exp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
    :
      is_conditional_expectation prts dom2 f (ConditionalExpectation f).
  Proof.
    intros P dec sa_P.
    assert (isfe1:IsFiniteExpectation prts (rvmult f (EventIndicator dec))).
    {
      apply IsFiniteExpectation_indicator; trivial.
      now apply sub.
    }

    destruct (IsFiniteExpectation_parts prts (rvmult f (EventIndicator dec)))
      as [isfep isfen]; trivial.

    unfold Expectation.
    unfold ConditionalExpectation.
    transitivity (Rbar_Expectation
                    (Rbar_rvminus (Rbar_rvmult
                                     (NonNegCondexp (fun x : Ts => pos_fun_part f x))
                                     (fun x : Ts => EventIndicator dec x))
                                  (Rbar_rvmult
                                     (NonNegCondexp (fun x : Ts => neg_fun_part f x))
                                     (fun x : Ts => EventIndicator dec x)))).
    - unfold IsFiniteExpectation in isfep, isfen.
      match_option_in isfep; try tauto.
      match_option_in isfen; try tauto.
      destruct r; try tauto.
      destruct r0; try tauto.
      rewrite Rbar_Expectation_minus_finite with (e1:=r) (e2:=r0).
      + rewrite Expectation_pos_pofrf with (nnf:= (positive_part_nnf _)) in eqq.
        rewrite Expectation_pos_pofrf with (nnf:= (negative_part_nnf _)) in eqq0.
        invcs eqq.
        invcs eqq0.
        simpl.
        rewrite H0, H1.
        simpl.
        reflexivity.
      + apply Rbar_rvmult_rv.
        * apply (RandomVariable_sa_sub sub).
          apply NonNegCondexp_rv.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + apply Rbar_rvmult_rv.
        * apply (RandomVariable_sa_sub sub).
          apply NonNegCondexp_rv.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + rewrite <- NonNegCondexp_cond_exp; trivial.
        erewrite Expectation_proper; try eapply eqq.
        intros ?.
        rv_unfold; simpl.
        match_destr
        ; repeat rewrite Rmult_1_r
        ; repeat rewrite Rmult_0_r
        ; trivial.
        unfold Rmax; match_destr.
      + rewrite <- NonNegCondexp_cond_exp; trivial.
        erewrite Expectation_proper; try eapply eqq0.
        intros ?.
        rv_unfold; simpl.
        match_destr
        ; repeat rewrite Rmult_1_r
        ; repeat rewrite Rmult_0_r
        ; trivial.
        rewrite Ropp_0.
        unfold Rmax; match_destr.
    - apply Rbar_Expectation_proper.
      intros ?.
      unfold Rbar_rvminus, Rbar_rvmult, Rbar_rvplus, Rbar_rvopp.
      simpl.
      repeat rewrite (Rbar_mult_comm _ (EventIndicator dec a)).
      rewrite Rbar_mult_r_plus_distr.
      now rewrite <- Rbar_mult_opp_r.
  Qed.  

  Global Instance Condexp_nneg (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f}
         {nnf : NonnegativeFunction f} :
    Rbar_NonnegativeFunction (ConditionalExpectation f).
  Proof.
    unfold ConditionalExpectation.
      
    assert (rv2neg:RandomVariable dom2 borel_sa (fun x : Ts => neg_fun_part f x)).
    {
      rewrite <- neg_fun_part_pos; trivial.
      typeclasses eauto.
    } 
    rewrite (NonNegCondexp_id (fun x : Ts => neg_fun_part f x)).
    intros ?.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
    rewrite <- neg_fun_part_pos; trivial.
    unfold Rbar_opp, const.
    rewrite Ropp_0, Rbar_plus_0_r.
    apply NonNegCondexp_nneg.
  Qed.

  Theorem Condexp_id (f : Ts -> R)
        {rv : RandomVariable dom borel_sa f}
        {rv2 : RandomVariable dom2 borel_sa f} :
    rv_eq (ConditionalExpectation f) (fun x => Finite (f x)).
  Proof.
    unfold ConditionalExpectation.
    repeat rewrite NonNegCondexp_id; try typeclasses eauto.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp; simpl.
    intros a.
    f_equal.
    generalize (rv_pos_neg_id f a).
    rv_unfold; simpl.
    lra.
  Qed.

  Corollary Condexp_const c :
    rv_eq (ConditionalExpectation (const c)) (const (Finite c)).
  Proof.
    apply Condexp_id.
    apply rvconst.
  Qed.

  Theorem Condexp_finite (f : Ts -> R)
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f} :
      exists gr, ConditionalExpectation f = fun x => Finite (gr x).
  Proof.
    unfold ConditionalExpectation.
    unfold is_conditional_expectation; intros.
    unfold proj1_sig.
    apply IsFiniteExpectation_parts in isfe.
    destruct isfe as [isfep isfen].
    destruct (NonNegCondexp_finite (fun x : Ts => pos_fun_part f x))
      as [gp eqq1].
    destruct (NonNegCondexp_finite (fun x : Ts => neg_fun_part f x))
      as [gn eqq2].
    rewrite eqq1, eqq2.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp; simpl.
    eexists.
    reflexivity.
  Qed.

  Theorem Condexp_is_finite (f : Ts -> R)
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f} :
    forall x, is_finite (ConditionalExpectation f x).
  Proof.
    intros.
    destruct (Condexp_finite f).
    rewrite H.
    reflexivity.
  Qed.

  Lemma Condexp_Expectation (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
    :
      Expectation f = 
      Rbar_Expectation (ConditionalExpectation f).
    Proof.
      generalize (Condexp_cond_exp f pre_Ω (classic_dec pre_Ω) (sa_all)); intros.
      assert (indall: rv_eq
                (fun (x:Ts) => (EventIndicator (classic_dec pre_Ω)) x)
                (fun (x:Ts) =>  (const 1) x)).
      {
        intro x.
        unfold EventIndicator, pre_Ω, const.
        now match_destr.
      }
      assert (rv_eq
                (rvmult f (EventIndicator (classic_dec pre_Ω)))
                f).
        {
          intro x.
          unfold rvmult.
          rewrite indall.
          unfold const.
          now rewrite Rmult_1_r.
        }
        rewrite (Expectation_ext H0) in H.
        assert (rv_eq
                  (Rbar_rvmult
                     (ConditionalExpectation f)
                     (fun x : Ts => EventIndicator (classic_dec pre_Ω) x))
                  (ConditionalExpectation f)).
        {
          intro x.
          unfold Rbar_rvmult.
          rewrite indall.
          unfold const.
          now rewrite Rbar_mult_1_r.
       }
        now rewrite (Rbar_Expectation_ext H1) in H.
   Qed.

    Global Instance Condexp_Rbar_isfe (f : Ts -> R) 
           {rv : RandomVariable dom borel_sa f}
           {isfe:IsFiniteExpectation prts f}
      : Rbar_IsFiniteExpectation prts (ConditionalExpectation f).
    Proof.
      unfold Rbar_IsFiniteExpectation.
      rewrite <- Condexp_Expectation; trivial.
    Qed.

  Lemma NonNegCondexp_proper (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {nnf1 : NonnegativeFunction f1} 
        {nnf2 : NonnegativeFunction f2} :
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (NonNegCondexp f1)
             (NonNegCondexp f2).
  Proof.
    intros eqq.
    generalize (NonNegCondexp_cond_exp f1); intros HH1.
    generalize (NonNegCondexp_cond_exp f2); intros HH2.
    apply (is_conditional_expectation_nneg_unique prts sub f1 (NonNegCondexp f1) (NonNegCondexp f2) HH1).
    apply (is_conditional_expectation_proper prts sub f2 f1 (NonNegCondexp f2) (NonNegCondexp f2)); trivial.
    - now symmetry.
    - reflexivity.
  Qed.

  Lemma Condexp_proper (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2} :
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation f1)
             (ConditionalExpectation f2).
  Proof.
    intros eqq.
    unfold ConditionalExpectation.
    apply Rbar_rvplus_almost_proper.
    - apply NonNegCondexp_proper.
      now apply pos_fun_part_proper_almostR2.
    - apply Rbar_rvopp_almost_proper.
      apply NonNegCondexp_proper.
      now apply neg_fun_part_proper_almostR2.
  Qed.

  Lemma Condexp_ale (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}

    :
    almostR2 prts Rle f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) Rbar_le
             (ConditionalExpectation f1)
             (ConditionalExpectation f2).
  Proof.
    intros eqq.
    eapply (is_conditional_expectation_ale _ sub f1 f2)
    ; trivial
    ; now apply Condexp_cond_exp.
  Qed.

  Lemma Condexp_scale c (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
    :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation (rvscale c f))
             (Rbar_rvmult (const (Finite c)) (ConditionalExpectation f)).
  Proof.
    assert (
     rvce2 : RandomVariable dom2 Rbar_borel_sa
                            (Rbar_rvmult (fun x : Ts => const c x) (ConditionalExpectation f))).
    {
      apply Rbar_rvmult_rv; typeclasses eauto.
    }
    apply (@is_conditional_expectation_unique _ _ prts _ sub (rvscale c f)
                                                   (ConditionalExpectation (rvscale c f))
                (Rbar_rvmult (const c) (ConditionalExpectation f)) _ _ _).
    - typeclasses eauto.
    - apply Condexp_cond_exp; typeclasses eauto.
    - apply (is_conditional_expectation_scale _ sub
                                                c f
                                                (ConditionalExpectation f))
      ; intros.
      apply Condexp_cond_exp; typeclasses eauto.
  Qed.

  Lemma Condexp_opp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
    :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation (rvopp f))
             (Rbar_rvopp (ConditionalExpectation f)).
  Proof.
    etransitivity.
    - eapply Condexp_scale; typeclasses eauto.
    - apply all_almost.
      unfold Rbar_rvmult, Rbar_rvopp, const.
      intros.
      unfold Rbar_opp.
      match_destr; simpl; rbar_prover.
  Qed.

  Lemma Condexp_plus (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}
    :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation (rvplus f1 f2))
             (Rbar_rvplus (ConditionalExpectation f1) (ConditionalExpectation f2)).
  Proof.

    assert (
     rvce2 : RandomVariable dom2 Rbar_borel_sa
                            (Rbar_rvplus (ConditionalExpectation f1) (ConditionalExpectation f2))).
    {
      apply Rbar_rvplus_rv; typeclasses eauto.
    }
    
    apply (is_conditional_expectation_unique prts sub
                                              (rvplus f1 f2) _ _).
    - apply Condexp_cond_exp; typeclasses eauto.
    - apply (is_conditional_expectation_plus _ sub
                                                f1 f2
                                                (ConditionalExpectation f1)
                                                (ConditionalExpectation f2))
      ; apply Condexp_cond_exp; trivial.
  Qed.

  Lemma Condexp_minus (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}
    :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation (rvminus f1 f2))
             (Rbar_rvminus (ConditionalExpectation f1) (ConditionalExpectation f2)).
  Proof.
    unfold Rbar_rvminus.
    etransitivity.
    - apply Condexp_plus; typeclasses eauto.
    - generalize (Condexp_opp f2).
      apply almost_impl.
      apply all_almost.
      intros ??.
      unfold Rbar_rvplus.
      congruence.
  Qed.

  Theorem Condexp_factor_out
        (f g : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvgf: RandomVariable dom borel_sa (rvmult f g)}
        {isfef: IsFiniteExpectation prts f}
        {isfefg:IsFiniteExpectation prts (rvmult f g)} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation (rvmult f g))
             (Rbar_rvmult g (ConditionalExpectation f)).
  Proof.
    assert (
     rvce2 : RandomVariable dom2 Rbar_borel_sa
                            (Rbar_rvmult (fun x => g x) (ConditionalExpectation f))).
    {
      apply Rbar_rvmult_rv; typeclasses eauto.
    }
    
    apply (is_conditional_expectation_unique prts sub
                                              (rvmult f g) _ _).
    - apply Condexp_cond_exp; typeclasses eauto.
    - assert (RandomVariable dom borel_sa (rvabs f)) by typeclasses eauto.
      assert (NonnegativeFunction (rvabs f)) by typeclasses eauto.
      assert (NonnegativeFunction (fun x : Ts => NonNegCondexp (rvabs f) x)).
      { 
        intros x.
        generalize (NonNegCondexp_nneg (rvabs f) x); simpl.
        match_destr; simpl; try tauto; lra.
      } 

      generalize (is_conditional_expectation_factor_out _ sub
                                                        f g
                                                        (ConditionalExpectation f)
                                                        (NonNegCondexp (rvabs f))
                                                        _ _)
      ; intros HH.
      cut_to HH.
      + revert HH.
        apply is_conditional_expectation_proper; trivial; try reflexivity.
        apply all_almost; intros.
        unfold Rbar_rvmult.
        rewrite Condexp_is_finite; trivial.
      + generalize (Condexp_cond_exp f).
        apply is_conditional_expectation_proper; trivial; try reflexivity.
        apply all_almost; intros.
        now rewrite Condexp_is_finite.
      + generalize (NonNegCondexp_cond_exp (rvabs f)).
        apply is_conditional_expectation_proper; trivial; try reflexivity.
        apply all_almost; intros.
        assert (IsFiniteExpectation prts (rvabs f)) by now apply IsFiniteExpectation_abs.
        destruct (NonNegCondexp_finite (rvabs f)).
        now rewrite H3.
  Qed.

  Theorem NonNegCondexp_factor_out
        (f g : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvgf: RandomVariable dom borel_sa (rvmult f g)}
        {nnf : NonnegativeFunction f}
        {nng : NonnegativeFunction g} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (NonNegCondexp (rvmult f g))
             (Rbar_rvmult g (NonNegCondexp f)).
  Proof.
    assert (
     rvce2 : RandomVariable dom2 Rbar_borel_sa
                            (Rbar_rvmult (fun x => g x) (NonNegCondexp f))).
    {
      apply Rbar_rvmult_rv; typeclasses eauto.
    }
    apply (is_conditional_expectation_nneg_unique prts sub (rvmult f g) _ _).

    - apply NonNegCondexp_cond_exp; typeclasses eauto.
    - apply (is_conditional_expectation_factor_out_nneg_both_Rbar _ sub f g
                                                                  (NonNegCondexp f)).
      apply NonNegCondexp_cond_exp.
  Qed.      

  Lemma Condexp_L2 (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f}
          {islp : IsLp prts 2 f}
    :
      almostR2 (prob_space_sa_sub prts sub) eq
               (ConditionalExpectation f)
               (fun x => conditional_expectation_L2fun prts sub f x).
  Proof.
    eapply is_conditional_expectation_unique; trivial.
    - now apply Condexp_cond_exp.
    - apply conditional_expectation_L2fun_eq3.
  Qed.

  Lemma Condexp_L2_inner
        (f : Ts -> R) 
        {frv : RandomVariable dom borel_sa f}
        {fisl : IsLp prts 2 f}
        (w : Ts -> R)
        {wrv:RandomVariable dom2 borel_sa w}
        {wisl:IsLp prts 2 w} :
    Rbar_Expectation (Rbar_rvmult (ConditionalExpectation f) w) =
    Expectation (rvmult f w).
  Proof.
    transitivity (Expectation (rvmult (fun x => conditional_expectation_L2fun prts sub f x) w)).
    - rewrite Expectation_Rbar_Expectation.
      apply Rbar_Expectation_almostR2_proper.
      + apply Rbar_rvmult_rv; trivial
        ; apply RandomVariable_sa_sub
        ; trivial
        ; typeclasses eauto.
      + apply Real_Rbar_rv.
        simpl.
        apply rvmult_rv; trivial
        ; apply RandomVariable_sa_sub
        ; trivial.
        apply conditional_expectation_L2fun_rv.
      + eapply (almostR2_prob_space_sa_sub_lift prts sub).
        generalize (Condexp_L2 f).
        apply almost_impl; apply all_almost; intros ??.
        unfold Rbar_rvmult, rvmult.
        now rewrite H; simpl.
    - generalize (RandomVariable_sa_sub sub w); intros.

      generalize (conditional_expectation_L2fun_eq2 prts sub f (pack_LpRRV prts w) _); intros HH.
      unfold L2RRVinner in HH.
      simpl in HH.
      repeat erewrite FiniteExpectation_Expectation.
      now rewrite HH.
  Qed.

  Lemma L2_min_dist_finite
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    is_finite (Glb_Rbar
      (fun r : R =>
         exists w : Ts -> R,
           RandomVariable dom2 borel_sa w /\ IsLp prts 2 w /\
           Some (Finite r) = lift (fun x => Rbar_power x (/ 2)) (Expectation (rvsqr (rvminus f w))))).
  Proof.
    generalize (conditional_expectation_L2fun_eq_finite prts f)
    ; intros HH.
    erewrite Glb_Rbar_eqset; try eapply HH.
    intros.
    split.
    - intros [?[?[??]]]; subst.
      symmetry in H1.
      apply some_lift in H1.
      destruct H1 as [???].
      assert (RandomVariable dom borel_sa x0).
      {
        now apply RandomVariable_sa_sub.
      }
      exists (pack_LpRRV prts x0).
      split; trivial.
      LpRRV_simpl.
      unfold LpRRVnorm; simpl.
      assert (IsFiniteExpectation prts (rvsqr (rvminus f x0))).
      {
        assert (IsLp prts 2 (rvminus f x0)).
        {
          apply (IsLp_minus prts (bignneg 2 big2) f x0).
        }
        apply is_L2_mult_finite; trivial
        ; now apply rvminus_rv.
      }
      rewrite (FiniteExpectation_Expectation _ _) in e.
      invcs e.
      simpl in e0.
      invcs e0.
      f_equal.
      apply FiniteExpectation_ext; intros ?.
      unfold rvsqr, rvpower, rvabs.
      now rewrite power_abs2_sqr.
    - intros [[a ??][??]]; subst.
      exists a.
      repeat split; trivial.
      LpRRV_simpl.
      unfold LpRRVnorm; simpl.
      assert (IsFiniteExpectation prts (rvsqr (rvminus f a))).
      {
        assert (IsLp prts 2 (rvminus f a)).
        {
          apply (IsLp_minus prts (bignneg 2 big2) f a).
        }
        apply is_L2_mult_finite; trivial
        ; now apply rvminus_rv.
      }
      rewrite (FiniteExpectation_Expectation _ _); simpl.
      do 3 f_equal.
      apply FiniteExpectation_ext; intros ?.
      unfold rvsqr, rvpower, rvabs.
      now rewrite power_abs2_sqr.
  Qed.

  Lemma Condexp_L2_min_dist
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    lift (fun x => Rbar_power x (/ 2))
         (Rbar_Expectation (Rbar_rvsqr (Rbar_rvminus f (ConditionalExpectation f))))
    = 
    Some (Glb_Rbar
      (fun r : R =>
         exists w : Ts -> R,
           RandomVariable dom2 borel_sa w /\ IsLp prts 2 w /\
           Some (Finite r) = lift (fun x => Rbar_power x (/ 2)) (Expectation (rvsqr (rvminus f w))))).
  Proof.
    transitivity (lift (fun x => Rbar_power x (/ 2))
                 (Expectation (rvpower (rvabs (rvminus f (conditional_expectation_L2fun prts sub f))) (const 2)))).
    - rewrite Expectation_Rbar_Expectation.
      f_equal.
      apply Rbar_Expectation_almostR2_proper.
      + assert (RandomVariable dom Rbar_borel_sa (ConditionalExpectation f)).
        {
          apply RandomVariable_sa_sub; trivial.
          apply Condexp_rv.
        }
        apply Rbar_rvsqr_rv.
        apply Rbar_rvplus_rv; typeclasses eauto.
      + apply Real_Rbar_rv.
        assert (RandomVariable dom borel_sa (conditional_expectation_L2fun prts sub f)).
        {
          apply RandomVariable_sa_sub; trivial.
          apply conditional_expectation_L2fun_rv.
        }
        simpl.
        apply rvpower_rv; try typeclasses eauto.
      + eapply (almostR2_prob_space_sa_sub_lift prts sub).
        generalize (Condexp_L2 f).
        apply almost_impl; apply all_almost; intros ??.
        unfold Rbar_rvpower, Rbar_rvsqr, Rbar_sqr, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, rvpower, rvminus, rvplus, rvopp, rvscale, const, rvabs.
        rewrite H; simpl.
        rewrite power_abs2_sqr.
        do 2 f_equal; lra.
    - generalize (conditional_expectation_L2fun_eq prts sub f); intros HH.
      unfold LpRRVnorm in HH.
      simpl in *.
      
      assert (isfe:IsFiniteExpectation prts (rvpower (rvabs (rvminus f (conditional_expectation_L2fun prts sub f))) (const 2))).
      {
        cut (IsFiniteExpectation prts (rvsqr (rvminus f (conditional_expectation_L2fun prts sub f)))).
        {
          apply IsFiniteExpectation_proper; intros ?.
          unfold rvpower, rvabs.
          rewrite power_abs2_sqr.
          reflexivity.
        }
        
        assert (RandomVariable dom borel_sa (conditional_expectation_L2fun prts sub f)).
        {
          apply RandomVariable_sa_sub; trivial.
          apply conditional_expectation_L2fun_rv.
        }
        
        assert (IsLp prts 2 (rvminus f (conditional_expectation_L2fun prts sub f))).
        {
          apply (IsLp_minus prts (bignneg 2 big2) f (conditional_expectation_L2fun prts sub f)).
        }
        apply is_L2_mult_finite; trivial
        ; now apply rvminus_rv.
      }
      
      rewrite (FiniteExpectation_Expectation _ _); simpl.
      f_equal.
      apply (f_equal Finite) in HH.
      etransitivity; [| etransitivity; try eapply HH].
      + f_equal.
        f_equal.
        apply FiniteExpectation_ext; reflexivity.
      + rewrite <- L2_min_dist_finite; trivial.
        f_equal.
        f_equal.
        apply Glb_Rbar_eqset; intros.
        split.
        * intros [[a ??][??]]; subst; simpl in *.
          exists a.
          repeat split; trivial.
          assert (IsFiniteExpectation prts (rvsqr (rvminus f a))).
          {
            assert (IsLp prts 2 (rvminus f a)).
            {
              apply (IsLp_minus prts (bignneg 2 big2) f a).
            }
            apply is_L2_mult_finite; trivial
            ; now apply rvminus_rv.
          }
          rewrite (FiniteExpectation_Expectation _ _); simpl.
          do 3 f_equal.
          apply FiniteExpectation_ext; intros ?.
          unfold rvsqr, rvpower, rvabs.
          now rewrite power_abs2_sqr.
        * intros [? [?[??]]].
          generalize (RandomVariable_sa_sub sub x0); intros.
          assert (IsFiniteExpectation prts (rvsqr (rvminus f x0))).
          {
            assert (IsLp prts 2 (rvminus f x0)).
            {
              apply (IsLp_minus prts (bignneg 2 big2) f x0).
            }
            apply is_L2_mult_finite; trivial
            ; now apply rvminus_rv.
          }
          rewrite (FiniteExpectation_Expectation _ _) in H1.
          simpl in H1.
          invcs H1.
          exists (pack_LpRRV prts x0).
          split; trivial.
          f_equal.
          apply FiniteExpectation_ext; intros ?.
          unfold rvsqr, rvpower, rvabs.
          now rewrite power_abs2_sqr.
  Qed.

  (* I think this is doable without IsFiniteExpectation, but it needs
     more work on Nonnegative conditional expectation *)
  Lemma Condexp_monotone_convergence
        (f : Ts -> R)
        (fn : nat -> Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvfn : forall n, RandomVariable dom borel_sa (fn n)}
        (nnf: almostR2 prts Rle (const 0) f)
        (nnfn : forall n, almostR2 prts Rle (const 0) (fn n))
        (fbound:forall (n:nat), almostR2 prts Rle (fn n) f)
        (fincr:forall (n:nat), almostR2 prts Rle (fn n) (fn (S n)))
        {isfef:IsFiniteExpectation prts f}
        {isfefn:forall n, IsFiniteExpectation prts (fn n)}
        (flim:almost prts (fun omega => is_Elim_seq (fun n => fn n omega) (f omega))) :
    almost (prob_space_sa_sub prts sub)
           (fun omega => is_Elim_seq (fun n => ConditionalExpectation (fn n) omega) (ConditionalExpectation f omega)).
  Proof.
    
    assert (rvce : RandomVariable dom2 Rbar_borel_sa
                                  (Rbar_rvlim (fun n : nat => ConditionalExpectation (fn n)))).
    {
      apply Rbar_rvlim_rv; trivial.
      typeclasses eauto.
    }

    assert (lece:forall n, almostR2 (prob_space_sa_sub prts sub)
                          Rbar_le (ConditionalExpectation (fn n)) (ConditionalExpectation (fn (S n)))).
    {
      intros.
      apply Condexp_ale; trivial.
    }

    assert (nnfcen:forall n : nat,
        almostR2 (prob_space_sa_sub prts sub) Rbar_le (fun x : Ts => const 0 x)
                 (ConditionalExpectation (fn n))).
    {
      intros.
      eapply is_conditional_expectation_anneg.
      - apply nnfn.
      - now apply Condexp_cond_exp.
    } 

    assert (nnfce: almostR2 (prob_space_sa_sub prts sub) Rbar_le (fun x : Ts => const 0 x)
                             (Rbar_rvlim (fun n : nat => ConditionalExpectation (fn n)))).
    {
      apply almostR2_Rbar_le_fixup_forall_r_split in nnfcen; try apply Rbar_le_pre.
      destruct nnfcen as [f1' [?[??]]].
      assert (HH: forall n, RandomVariable dom2 Rbar_borel_sa (f1' n)) by intuition.
      clear H1.
      apply Rbar_rvlim_almost_proper in H.
      revert H.
      apply almost_impl; apply all_almost; intros ??.
      rewrite H.
      apply Rbar_rvlim_nnf; intros ??.
      apply H0.
    } 

    assert (boundce:forall n : nat,
        almostR2 (prob_space_sa_sub prts sub) Rbar_le (ConditionalExpectation (fn n))
                 (Rbar_rvlim (fun n0 : nat => ConditionalExpectation (fn n0)))).
    {
      intros.
      destruct (almost_and _ (almost_forall _ lece) (almost_forall _ nnfcen)) as [pce [??]].
      pose (cen' :=
              fun n => (Rbar_rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec pce))) x) 0 then false else true)
                             
                             (ConditionalExpectation (fn n))
                             (const (Finite 0))
           )).

    assert (ceneqq:forall n, almostR2 (prob_space_sa_sub prts sub) eq (cen' n) (ConditionalExpectation (fn n))).
    {
      intros.
      exists pce.
      split; trivial.
      intros.
      unfold cen', EventIndicator, Rbar_rvchoice.
      destruct (classic_dec pce x); try tauto.
      now destruct (Req_EM_T 1 0); try lra.
    }

    generalize (Rbar_rvlim_almost_proper _ _ _ ceneqq); apply almost_impl.
    generalize (ceneqq n); apply almost_impl.
    apply almost_forall in lece.
    apply almost_forall in nnfcen.
    destruct lece as [p1 [??]].
    destruct nnfcen as [p2 [??]].

    exists (event_inter pce (event_inter p1 p2)); split.
    { rewrite ps_inter_l1; trivial.
      rewrite ps_inter_l1; trivial.
    }
    intros ????.
    rewrite <- H6.
    rewrite <- H7.
    apply Rbar_rvlim_pos_ge; unfold cen', Rbar_rvchoice, EventIndicator.
      - intros ??.
        destruct (classic_dec _ _)
        ; destruct (Req_EM_T _ _); try lra; try apply Rbar_le_refl.
        now apply H0.
      - intros ??.
        destruct (classic_dec _ _)
        ; destruct (Req_EM_T _ _); try lra; try apply Rbar_le_refl.
        now apply H0.
    } 

    generalize (is_conditional_expectation_monotone_convergence_almost
                  prts sub
                  f (Rbar_rvlim (fun n : nat => ConditionalExpectation (fn n)))
                  fn
                  (fun n => ConditionalExpectation (fn n))
                  rvf
                  nnf
                  nnfce
                  rvfn
                  nnfn
                  nnfcen
                  _
                  fbound
                  fincr
                  boundce
                  lece
                  flim
               ) ; intros HH.
    cut_to HH; trivial.
    - generalize (Condexp_cond_exp f); intros HH2.
      generalize (is_conditional_expectation_unique _ sub _ _ _ HH HH2); intros HH3.
      generalize (almost_and _ (almost_forall _ lece) HH3).
      apply almost_impl; apply all_almost; intros ? [HH4 HH5].
      rewrite <- HH5.
      apply ELim_seq_correct.
      apply ex_Elim_seq_incr; intros.
      apply HH4.
    - generalize (almost_forall _ lece).
      apply almost_impl; apply all_almost; intros ??.
      apply ELim_seq_correct.
      apply ex_Elim_seq_incr; intros.
      apply H.
    - intros.
      now apply Condexp_cond_exp.
  Qed.
  
End cond_exp2.

Section cond_exp_props.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {dom3 : SigmaAlgebra Ts}
          (sub2 : sa_sub dom3 dom2).

  Theorem Condexp_tower
        (f ce: Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {isfe: IsFiniteExpectation prts f}
        {rvce : RandomVariable dom2 borel_sa ce}
        {rvce' : RandomVariable dom borel_sa ce}
    :
      almostR2 (prob_space_sa_sub prts sub) eq
               (ConditionalExpectation prts sub f) (fun x => ce x) ->
      almostR2 (prob_space_sa_sub prts (transitivity sub2 sub)) eq
               (ConditionalExpectation prts (transitivity sub2 sub) ce)
               (ConditionalExpectation prts (transitivity sub2 sub) f).
  Proof.
    intros afin.
    assert (ce_isfe:IsFiniteExpectation prts ce).
    {
      assert (risfe:Rbar_IsFiniteExpectation prts (ConditionalExpectation prts sub f))
        by (now apply Condexp_Rbar_isfe).
      unfold Rbar_IsFiniteExpectation in risfe.
      generalize (@Rbar_Expectation_almostR2_proper
                    _ _ 
                    prts
                    (ConditionalExpectation prts sub f)
                    (fun x : Ts => ce x))
      ; intros HH2.
        cut_to HH2; trivial.
      - rewrite HH2 in risfe.
        rewrite <- Expectation_Rbar_Expectation in risfe.
        apply risfe.
      - apply (RandomVariable_sa_sub sub).
        apply Condexp_rv.
      - now apply Real_Rbar_rv.
      - now apply (almost_prob_space_sa_sub_lift prts sub).
    }
          
    generalize (is_conditional_expectation_tower
                  prts sub2 f ce
                  (ConditionalExpectation prts (transitivity sub2 sub) f)
               )
    ; intros HH.
    cut_to HH; trivial.
    - eapply (is_conditional_expectation_unique prts (transitivity sub2 sub) ce); trivial.
      now apply Condexp_cond_exp.
    - apply (is_conditional_expectation_proper
                    prts sub _ _ _ _ (reflexivity _)
                    (almost_prob_space_sa_sub_lift _ sub _ afin)).
      now apply Condexp_cond_exp.
    - now apply Condexp_cond_exp.
  Qed.

End cond_exp_props.

Section fin_cond_exp.

    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).


  Definition FiniteConditionalExpectation
             (f : Ts -> R)
             {rv : RandomVariable dom borel_sa f}
             {isfe:IsFiniteExpectation prts f} : Ts -> R.
  Proof.
    generalize (Condexp_finite prts sub f)
    ; intros HH.
    apply constructive_indefinite_description in HH.
    destruct HH.
    apply x.
  Defined.

  Lemma FiniteConditionalExpectation_ext (f1 f2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}
    : rv_eq f1 f2 ->
      rv_eq (FiniteConditionalExpectation f1) (FiniteConditionalExpectation f2).
  Proof.
    (* classically true *)
    intros ??.
    assert (f1 = f2) by now apply functional_extensionality.
    subst.
    f_equal; apply proof_irrelevance.
  Qed.

  Lemma FiniteCondexp_eq
             (f : Ts -> R)
             {rv : RandomVariable dom borel_sa f}
             {isfe:IsFiniteExpectation prts f} :
    ConditionalExpectation prts sub f = fun x => (Finite (FiniteConditionalExpectation f x)).
  Proof.
    unfold FiniteConditionalExpectation.
    match_destr.
  Qed.
  
    Global Instance FiniteCondexp_rv (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f}
         {isfe:IsFiniteExpectation prts f} :
    RandomVariable dom2 borel_sa (FiniteConditionalExpectation f).
  Proof.
    generalize (Condexp_rv prts sub f).
    rewrite (FiniteCondexp_eq f).
    typeclasses eauto.
  Qed.

    Instance FiniteCondexp_rv' (f : Ts -> R) 
           {rv : RandomVariable dom borel_sa f}
           {isfe:IsFiniteExpectation prts f} :
      RandomVariable dom borel_sa (FiniteConditionalExpectation f).
    Proof.
      generalize (FiniteCondexp_rv f).
      eapply RandomVariable_proper_le; trivial; try reflexivity.
    Qed.
    
  Lemma FiniteCondexp_is_cond_exp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
    :
      is_conditional_expectation prts dom2 f (FiniteConditionalExpectation f).
  Proof.
    generalize (Condexp_cond_exp prts sub f).
    eapply is_conditional_expectation_proper; trivial.
    - reflexivity.
    - apply all_almost; intros.
      now rewrite (FiniteCondexp_eq f).
  Qed.

  Theorem FiniteCondexp_cond_exp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
        {P:pre_event Ts}
        (dec:dec_pre_event P)
        (saP:sa_sigma dom2 P) :
    Expectation (rvmult f (EventIndicator dec)) =
    Expectation (rvmult (FiniteConditionalExpectation f) (EventIndicator dec)).
  Proof.
    generalize (FiniteCondexp_is_cond_exp f)
    ; intros isce.
    rewrite (isce P dec saP).
    rewrite Expectation_Rbar_Expectation.
    reflexivity.
  Qed.

  Corollary FiniteCondexp_cond_exp_classic (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
        {P:pre_event Ts}
        (saP:sa_sigma dom2 P) :
    Expectation (rvmult f (EventIndicator (classic_dec P))) =
    Expectation (rvmult (FiniteConditionalExpectation f) (EventIndicator (classic_dec P))).
  Proof.
    now apply FiniteCondexp_cond_exp.
  Qed.

  Corollary FiniteCondexp_cond_exp_event (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
        {P:event dom2}
        (dec:dec_event P) :
    Expectation (rvmult f (EventIndicator dec)) =
    Expectation (rvmult (FiniteConditionalExpectation f) (EventIndicator dec)).
  Proof.
    apply FiniteCondexp_cond_exp.
    destruct P; trivial.
  Qed.

  Corollary FiniteCondexp_cond_exp_event_classic (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
        (P:event dom2) :
    Expectation (rvmult f (EventIndicator (classic_dec P))) =
    Expectation (rvmult (FiniteConditionalExpectation f) (EventIndicator (classic_dec P))).
  Proof.
    apply FiniteCondexp_cond_exp_event.
  Qed.

  Global Instance FiniteCondexp_nneg (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f}
         {isfe:IsFiniteExpectation prts f}
         {nnf : NonnegativeFunction f} :
    NonnegativeFunction (FiniteConditionalExpectation f).
  Proof.
    generalize (Condexp_nneg prts sub f)
    ; intros nneg.
    rewrite (FiniteCondexp_eq f) in nneg.
    apply nneg.
  Qed.

  Theorem FiniteCondexp_id (f : Ts -> R)
          {rv : RandomVariable dom borel_sa f}
          {rv2 : RandomVariable dom2 borel_sa f}
          {isfe:IsFiniteExpectation prts f}
    :
      rv_eq (FiniteConditionalExpectation f) f.
  Proof.
    generalize (Condexp_id prts sub f)
    ; intros eqq.
    rewrite (FiniteCondexp_eq f) in eqq.
    intros a.
    specialize (eqq a).
    now invcs eqq.
  Qed.

  Corollary FiniteCondexp_const c :
    rv_eq (FiniteConditionalExpectation (const c)) (const c).
  Proof.
    apply FiniteCondexp_id.
    apply rvconst.
  Qed.

  Theorem FiniteCondexp_Expectation (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f}
    :
      Expectation (FiniteConditionalExpectation f) =
      Expectation f.
  Proof.
    rewrite (Condexp_Expectation prts sub f).
    rewrite (FiniteCondexp_eq f).
    now rewrite Expectation_Rbar_Expectation.
  Qed.

  Global Instance FiniteCondexp_isfe (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f}
    : IsFiniteExpectation prts (FiniteConditionalExpectation f).
  Proof.
    unfold IsFiniteExpectation.
    now rewrite FiniteCondexp_Expectation.
  Qed.

  Global Instance FiniteCondexp_isfe2 (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f}
    : IsFiniteExpectation (prob_space_sa_sub prts sub) (FiniteConditionalExpectation f).
  Proof.
    generalize (FiniteCondexp_isfe f).
    apply IsFiniteExpectation_prob_space_sa_sub_f.
    now apply FiniteCondexp_rv.
  Qed.

  Theorem FiniteCondexp_FiniteExpectation (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f}
          {isfe':IsFiniteExpectation prts (FiniteConditionalExpectation f)}
    :
      FiniteExpectation prts (FiniteConditionalExpectation f) =
      FiniteExpectation prts f.
  Proof.
    generalize (FiniteCondexp_Expectation f).
    repeat erewrite FiniteExpectation_Expectation.
    now intros HH; invcs HH.
  Qed.

  Theorem FiniteCondexp_FiniteExpectation_sub (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
          {isfe:IsFiniteExpectation prts f}
          {isfe':IsFiniteExpectation prts (FiniteConditionalExpectation f)}
    :
      FiniteExpectation (prob_space_sa_sub prts sub) (FiniteConditionalExpectation f) =
      FiniteExpectation prts f.
  Proof.
    erewrite <- FiniteCondexp_FiniteExpectation.
    apply FiniteExpectation_prob_space_sa_sub.
    now apply FiniteCondexp_rv.
  Qed.

  Theorem FiniteCondexp_proper (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}:
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (FiniteConditionalExpectation f1)
             (FiniteConditionalExpectation f2).
  Proof.
    intros eqq1.
    generalize (Condexp_proper prts sub f1 f2 eqq1).
    rewrite (FiniteCondexp_eq f1), (FiniteCondexp_eq f2).
    apply almost_impl.
    apply all_almost.
    intros ? eqq.
    now invcs eqq.
  Qed.
    
  Lemma FiniteCondexp_ale (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2} :
    almostR2 prts Rle f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) Rle
             (FiniteConditionalExpectation f1)
             (FiniteConditionalExpectation f2).
  Proof.
    intros eqq1.
    generalize (Condexp_ale prts sub f1 f2 eqq1).
    rewrite (FiniteCondexp_eq f1), (FiniteCondexp_eq f2).
    apply almost_impl.
    apply all_almost.
    intros ? eqq.
    now simpl in eqq.
  Qed.

  Lemma FiniteCondexp_scale c (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (FiniteConditionalExpectation (rvscale c f))
             (rvscale c (FiniteConditionalExpectation f)).
  Proof.
    generalize (Condexp_scale prts sub c f).
    rewrite (FiniteCondexp_eq f), (FiniteCondexp_eq (rvscale c f)).
    apply almost_impl.
    apply all_almost.
    unfold Rbar_rvmult, rvscale; simpl.
    intros ? eqq.
    congruence.
  Qed.

  Lemma FiniteCondexp_opp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (FiniteConditionalExpectation (rvopp f))
             (rvopp (FiniteConditionalExpectation f)).
  Proof.
    generalize (Condexp_opp prts sub f).
    rewrite (FiniteCondexp_eq f), (FiniteCondexp_eq (rvopp f)).
    apply almost_impl.
    apply all_almost.
    unfold Rbar_rvopp, rvopp, rvscale; simpl.
    intros ? eqq.
    invcs eqq.
    lra.
  Qed.

  Lemma FiniteCondexp_plus (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (FiniteConditionalExpectation (rvplus f1 f2))
             (rvplus (FiniteConditionalExpectation f1) (FiniteConditionalExpectation f2)).
  Proof.
    generalize (Condexp_plus prts sub f1 f2).
    rewrite (FiniteCondexp_eq f1), (FiniteCondexp_eq f2), (FiniteCondexp_eq (rvplus f1 f2)).
    apply almost_impl.
    apply all_almost.
    unfold Rbar_rvplus, rvplus; simpl.
    intros ? eqq.
    congruence.
  Qed.

  Lemma FiniteCondexp_minus (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (FiniteConditionalExpectation (rvminus f1 f2))
             (rvminus (FiniteConditionalExpectation f1) (FiniteConditionalExpectation f2)).
  Proof.
    generalize (Condexp_minus prts sub f1 f2).
    rewrite (FiniteCondexp_eq f1), (FiniteCondexp_eq f2), (FiniteCondexp_eq (rvminus f1 f2)).
    apply almost_impl.
    apply all_almost.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, rvminus, rvplus, rvopp, rvscale; simpl.
    intros ? eqq.
    invcs eqq.
    lra.
  Qed.

  Lemma FiniteCondexp_Jensen (rv_X : Ts -> R) (phi : R -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {rvphi : RandomVariable dom borel_sa (fun x => phi (rv_X x))}
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => phi (rv_X x))} :    
    (forall c x y, convex phi c x y) ->
    almostR2 (prob_space_sa_sub prts sub) Rle
      (fun x => phi ((FiniteConditionalExpectation rv_X) x))
      (FiniteConditionalExpectation (fun x => phi (rv_X x))).
  Proof.
    intros.
    apply (is_condexp_Jensen prts sub rv_X (FiniteConditionalExpectation rv_X)
                                  (FiniteConditionalExpectation (fun x : Ts => phi (rv_X x)))
                                  phi); trivial.
    - apply FiniteCondexp_is_cond_exp.
    - apply FiniteCondexp_is_cond_exp.
  Qed.

  Lemma FiniteCondexp_abs (f: Ts -> R)
        {rv : RandomVariable dom borel_sa f}
        {isfe : IsFiniteExpectation prts f}
        {isfeabs : IsFiniteExpectation prts (rvabs f)} :
    almostR2 (prob_space_sa_sub prts sub) Rle
             (rvabs (FiniteConditionalExpectation f))
             (FiniteConditionalExpectation (rvabs f)).
  Proof.
    apply FiniteCondexp_Jensen.
    apply abs_convex.
  Qed.

  Theorem FiniteCondexp_factor_out
        (f g : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvgf: RandomVariable dom borel_sa (rvmult f g)}
        {isfef: IsFiniteExpectation prts f}
        {isfefg:IsFiniteExpectation prts (rvmult f g)} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (FiniteConditionalExpectation (rvmult f g))
             (rvmult g (FiniteConditionalExpectation f)).
  Proof.
    generalize (Condexp_factor_out prts sub f g)
    ; intros HH.
    rewrite (FiniteCondexp_eq f), (FiniteCondexp_eq (rvmult f g)) in HH.
    revert HH.
    apply almost_impl.
    apply all_almost; intros ? HH.
    unfold Rbar_rvmult in HH; simpl in HH.
    now invcs HH.
  Qed.
    
    Theorem FiniteCondexp_factor_out_l
            (f g : Ts -> R)
            {rvf : RandomVariable dom borel_sa f}
            {rvg : RandomVariable dom2 borel_sa g}
            {rvgf: RandomVariable dom borel_sa (rvmult g f)}
            {isfef: IsFiniteExpectation prts f}
            {isfefg:IsFiniteExpectation prts (rvmult g f)} :
      almostR2 (prob_space_sa_sub prts sub) eq
               (FiniteConditionalExpectation (rvmult g f))
               (rvmult g (FiniteConditionalExpectation f)).
    Proof.
      assert (RandomVariable dom borel_sa (rvmult f g)).
      {
        generalize rvgf.
        apply RandomVariable_proper; try reflexivity.
        unfold rvmult; intros ?; lra.
      }
      assert (IsFiniteExpectation prts (rvmult f g)).
      {
        generalize isfefg.
        apply IsFiniteExpectation_proper.
        unfold rvmult; intros ?; lra.
      } 
      
      rewrite <- (FiniteCondexp_factor_out f g).
      apply FiniteCondexp_proper.
      apply all_almost.
      unfold rvmult; intros ?; lra.
    Qed.
    
    Lemma FiniteCondexp_factor_out_zero
        (f g : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {isfef: IsFiniteExpectation prts f} 
        {isfefg:IsFiniteExpectation prts (rvmult f g)} : 
    almostR2 prts eq (FiniteConditionalExpectation f) (const 0) ->
    FiniteExpectation prts (rvmult f g) = 0.
  Proof.
    intros.
    assert (rvfg : RandomVariable dom borel_sa (rvmult f g)).
    {
      apply rvmult_rv; trivial.
      now apply RandomVariable_sa_sub.
    }
    generalize (FiniteCondexp_FiniteExpectation (rvmult f g)); intros.
    generalize (FiniteCondexp_factor_out f g); intros.
    assert (almostR2 prts eq (FiniteConditionalExpectation (rvmult f g))
                     (const 0)).
    {
      apply almostR2_prob_space_sa_sub_lift in H1.
      revert H1; apply almost_impl.
      revert H; apply almost_impl.
      apply all_almost; intros ???.
      rewrite H1.
      unfold rvmult.
      rewrite H.
      unfold const.
      now rewrite Rmult_0_r.
    }
    erewrite FiniteExpectation_proper_almostR2 in H0; try eapply H2.
    - now rewrite FiniteExpectation_const in H0.
    - apply RandomVariable_sa_sub; trivial.
      typeclasses eauto.
    - apply rvconst.
  Qed.
      
  Lemma FiniteCondexp_factor_out_zero_swapped
        (f g : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {isfef: IsFiniteExpectation prts f}
        {isfefg:IsFiniteExpectation prts (rvmult g f)} :
     almostR2 prts eq (FiniteConditionalExpectation f) (const 0) ->
    FiniteExpectation prts (rvmult g f) = 0.
  Proof.
    intros.
    assert (IsFiniteExpectation prts (rvmult f g)).
    {
      revert isfefg.
      apply IsFiniteExpectation_proper.
      now rewrite rvmult_comm.
    }
    generalize (FiniteCondexp_factor_out_zero f g H); intros.
    rewrite <- H1.
    apply FiniteExpectation_ext.
    now rewrite rvmult_comm.
  Qed.
  
  Lemma SimpleCondexp_factor_out_zero
        (f g : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvgf : RandomVariable dom borel_sa (rvmult g f)}        
        {frf : FiniteRangeFunction f}
        {frg : FiniteRangeFunction g} :
     almostR2 prts eq (ConditionalExpectation prts sub f) (const 0) -> 
    SimpleExpectation (rvmult g f) = 0.
  Proof.
    intros.
    assert (isfe: IsFiniteExpectation prts f) by
        now apply IsFiniteExpectation_simple.
    assert (isfefg: IsFiniteExpectation prts (rvmult g f)).
    {
      apply IsFiniteExpectation_simple; trivial.
      typeclasses eauto.
    }
    generalize (FiniteCondexp_factor_out_zero_swapped f g); intros.
    rewrite simple_FiniteExpectation.
    rewrite <- H0.
    - apply FiniteExpectation_pf_irrel.
    - rewrite (FiniteCondexp_eq _) in H.
      apply (almost_f_equal _ real) in H.
      apply H.
    Qed.

  Lemma IsLp_almost_bounded n rv_X1 rv_X2
        (rle:almostR2 prts Rle (rvpower (rvabs rv_X1) (const n)) rv_X2)
        {rv1:RandomVariable dom borel_sa (rvpower (rvabs rv_X1) (const n))}
        {rv2:RandomVariable dom borel_sa rv_X2}
        {islp:IsFiniteExpectation prts rv_X2}
    :
      IsLp prts n rv_X1.
  Proof.
    apply almostR2_le_split_r in rle.
    destruct rle as [? [?[??]]].
    eapply IsLp_bounded.
    - eauto.
    - eapply IsFiniteExpectation_proper_almostR2; eauto. 
  Qed.      

  Instance FiniteCondexp_Lp_sub {p} (pbig:1<=p)
        (f : Ts -> R) 
        {frv : RandomVariable dom borel_sa f}
        {isfe: IsFiniteExpectation prts f}
        {isl : IsLp prts p f} :
    IsLp prts p (FiniteConditionalExpectation f).
  Proof.
    assert (rvphi:RandomVariable dom borel_sa (fun x : Ts => (fun x0 : R => power (Rabs x0) p) (f x))).
    {
      apply rvpower_rv.
      - apply rvabs_rv; trivial.
      - apply rvconst.
    }

    assert (isfephi:IsFiniteExpectation prts (fun x : Ts => (fun x0 : R => power (Rabs x0) p) (f x))).
    {
      apply isl.
    } 

    generalize (FiniteCondexp_Jensen f (fun x => power (Rabs x) p))
    ; intros.

    cut_to H.
    - eapply (IsLp_almost_bounded p _ (FiniteConditionalExpectation (fun x : Ts => power (Rabs (f x)) p))).
      + apply almostR2_prob_space_sa_sub_lift in H.
        revert H.
        apply almost_impl; apply all_almost; intros ??.
        rv_unfold.
        apply H.
      + apply rvpower_rv; trivial.
        * apply rvabs_rv.
          apply RandomVariable_sa_sub; trivial.
          apply FiniteCondexp_rv.
        * apply rvconst.
      + apply RandomVariable_sa_sub; trivial.
        apply FiniteCondexp_rv.
      + apply FiniteCondexp_isfe. 
    - intros.
      now apply convex_power_abs.
  Qed.
  
  Instance FiniteCondexp_Lp {p} (pbig:1<=p)
        (f : Ts -> R) 
        {frv : RandomVariable dom borel_sa f}
        {isfe: IsFiniteExpectation prts f}
        {isl : IsLp prts p f} :
    IsLp (prob_space_sa_sub prts sub) p (FiniteConditionalExpectation f).
  Proof.
    apply IsLp_prob_space_sa_sub.
    - apply FiniteCondexp_rv.
    - now apply FiniteCondexp_Lp_sub.
  Qed.

  Lemma FiniteCondexp_Lp_contractive {p} (pbig:1<=p)
        (f : Ts -> R) 
        {frv : RandomVariable dom borel_sa f}
        {isfe: IsFiniteExpectation prts f}
        {isl : IsLp prts p f} :
    FiniteExpectation (prob_space_sa_sub prts sub) (rvpower (rvabs (FiniteConditionalExpectation f)) (const p)) (isfe:=FiniteCondexp_Lp pbig f) <=
    FiniteExpectation prts (rvpower (rvabs f) (const p)).
  Proof.
    assert (rvphi:RandomVariable dom borel_sa (fun x : Ts => (fun x0 : R => power (Rabs x0) p) (f x))).
    {
      apply rvpower_rv.
      - apply rvabs_rv; trivial.
      - apply rvconst.
    }

    assert (isfephi:IsFiniteExpectation prts (fun x : Ts => (fun x0 : R => power (Rabs x0) p) (f x))).
    {
      apply isl.
    } 

    generalize (FiniteCondexp_Jensen f (fun x => power (Rabs x) p))
    ; intros.
    cut_to H.
    - eapply FiniteExpectation_ale in H.
      + rewrite FiniteCondexp_FiniteExpectation_sub in H.
        * etransitivity; try eapply H.
          right.
          apply FiniteExpectation_ext; intros ?.
          reflexivity.
        * apply FiniteCondexp_isfe.
      + apply rvpower_rv; try typeclasses eauto.
        apply rvconst.
      + typeclasses eauto.
    - intros.
      now apply convex_power_abs.
  Qed.

  Lemma FiniteCondexp_Lp_norm_contractive {p} (pbig:1<=p)
        (f : Ts -> R) 
        {frv : RandomVariable dom borel_sa f}
        {isfe: IsFiniteExpectation prts f}
        {isl : IsLp prts p f} :
    power (FiniteExpectation (prob_space_sa_sub prts sub)  (rvpower (rvabs (FiniteConditionalExpectation f)) (const p)) (isfe:=FiniteCondexp_Lp pbig f)) (/ p) <=
    power (FiniteExpectation prts (rvpower (rvabs f) (const p))) (/ p).
  Proof.
    assert (HH:forall x isfe ,0 <= FiniteExpectation (prob_space_sa_sub prts sub)  (rvpower (rvabs x) (const p)) (isfe:=isfe)).
    {
      intros.
      replace 0 with (FiniteExpectation (prob_space_sa_sub prts sub) (const 0)).
      - apply FiniteExpectation_le; intros ?.
        unfold const, rvpower; simpl.
        apply power_nonneg.
      - apply FiniteExpectation_const.
    }
    destruct (HH _ (@FiniteCondexp_Lp p pbig f frv isfe isl)).
    - apply Rle_power_inv_l; trivial.
      apply (FiniteCondexp_Lp_contractive pbig f).
    - symmetry in H.
      assert (RandomVariable dom borel_sa (rvpower (rvabs (FiniteConditionalExpectation f)) (const p))).
      {
        apply rvpower_rv; try typeclasses eauto.
      } 
      apply FiniteExpectation_zero_pos in H; trivial.
      + rewrite (FiniteExpectation_proper_almostR2 _ _ _ H).
        rewrite FiniteExpectation_const.
        rewrite power0_Sbase.
        apply power_nonneg.
      + typeclasses eauto.
      + typeclasses eauto.
  Qed.

  Lemma FiniteCondexp_L2_inner
        (f : Ts -> R) 
        {frv : RandomVariable dom borel_sa f}
        {fisl : IsLp prts 2 f}
        (w : Ts -> R)
        {wrv:RandomVariable dom2 borel_sa w}
        {wisl:IsLp prts 2 w} :
    Expectation (rvmult (FiniteConditionalExpectation f) w) =
    Expectation (rvmult f w).
  Proof.
    generalize (Condexp_L2_inner prts sub f w)
    ; intros HH.
    rewrite (FiniteCondexp_eq f) in HH.
    rewrite <- HH.
    unfold Rbar_rvmult.
    simpl.
    now rewrite <- Expectation_Rbar_Expectation.
  Qed.

  Lemma FiniteCondexp_L2_proj
        (f : Ts -> R) 
        {frv : RandomVariable dom borel_sa f}
        {fisl : IsLp prts 2 f}
        (w : Ts -> R)
        {wrv:RandomVariable dom2 borel_sa w}
        {wisl:IsLp prts 2 w} :
    Expectation (rvmult w (rvminus f (FiniteConditionalExpectation f))) = Some (Finite 0).
  Proof.
    generalize (FiniteCondexp_L2_inner f w)
    ; intros HH.
    transitivity (Expectation (rvminus (rvmult f w) (rvmult (FiniteConditionalExpectation f) w))).
    {
      apply Expectation_proper; intros ?.
      rv_unfold; simpl; lra.
    }

    assert (RandomVariable dom borel_sa (rvmult f w)).
    {
      apply rvmult_rv; trivial.
      apply RandomVariable_sa_sub; trivial.
    } 

    assert (RandomVariable dom borel_sa (rvmult (FiniteConditionalExpectation f) w)).
    {
      apply rvmult_rv; trivial.
      - apply RandomVariable_sa_sub; trivial.
        apply FiniteCondexp_rv.
      - apply RandomVariable_sa_sub; trivial.
    } 

    assert (IsFiniteExpectation prts (rvmult f w)).
    {
      apply is_L2_mult_finite; trivial.
      apply RandomVariable_sa_sub; trivial.
    }

    assert (IsFiniteExpectation prts (rvmult (FiniteConditionalExpectation f) w)).
    {
      apply is_L2_mult_finite; trivial.
      - apply RandomVariable_sa_sub; trivial.
        eapply FiniteCondexp_rv.
      - apply RandomVariable_sa_sub; trivial.
      - apply (FiniteCondexp_Lp_sub big2); trivial.
    }

    repeat rewrite (FiniteExpectation_Expectation prts _) in HH.
    invcs HH.

    rewrite (FiniteExpectation_Expectation prts _).
    f_equal.
    rewrite FiniteExpectation_minus.
    f_equal; lra.
  Qed.

  Instance FiniteCondexp_L2_min_dist_isfe
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    IsFiniteExpectation prts (rvsqr (rvminus f (FiniteConditionalExpectation f))).
  Proof.
    assert (RandomVariable dom borel_sa (FiniteConditionalExpectation f)).
    {
      apply RandomVariable_sa_sub; trivial.
      apply FiniteCondexp_rv.
    } 
            
    assert (IsLp prts 2 (rvminus f (FiniteConditionalExpectation f))).
    {
      generalize (FiniteCondexp_Lp_sub big2 f); intros.
      apply (IsLp_minus prts (bignneg 2 big2) f _).
    }
    apply is_L2_mult_finite; trivial
    ; now apply rvminus_rv.
  Qed.

  Lemma FiniteCondexp_L2_min_dist
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    Finite (power 
      (FiniteExpectation prts (rvsqr (rvminus f (FiniteConditionalExpectation f))))
      (/ 2))
    = 
     (Glb_Rbar
      (fun r : R =>
         exists w : Ts -> R,
           RandomVariable dom2 borel_sa w /\ IsLp prts 2 w /\
           Some (Finite r) = lift (fun x => Rbar_power x (/ 2)) (Expectation (rvsqr (rvminus f w))))).
  Proof.
    generalize (Condexp_L2_min_dist prts sub f)
    ; intros HH.
    apply some_lift in HH.
    destruct HH as [???].
    rewrite e0.
    rewrite (FiniteCondexp_eq _) in e.
    unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, Rbar_rvsqr in e.
    simpl in e.
    rewrite <- Expectation_Rbar_Expectation in e.
    assert (IsFiniteExpectation prts (fun x : Ts => (f x + - FiniteConditionalExpectation f x)²)).
    {
      generalize (FiniteCondexp_L2_min_dist_isfe f).
      apply IsFiniteExpectation_proper; intros ?.
      rv_unfold.
      f_equal.
      lra.
    } 
    rewrite (FiniteExpectation_Expectation _ _) in e.
    invcs e. 
    simpl.
    do 2 f_equal.
    apply FiniteExpectation_ext; intros ?.
    rv_unfold.
    f_equal.
    lra.
  Qed.    

  Lemma Glb_Rbar_pos (rset : R -> Prop) :
    (forall (r:R), rset r -> 0 <= r) ->
    Rbar_le 0 (Glb_Rbar rset).
  Proof.
    intros.
    unfold Glb_Rbar, proj1_sig.
    match_destr.
    unfold is_glb_Rbar in i.
    unfold is_lb_Rbar in i.
    destruct i.
    apply H1.
    intros.
    now apply H.
  Qed.

  Lemma finite_Glb_Rbar_pos (rset : R -> Prop) :
    (forall (r:R), rset r -> 0 <= r) ->
    (exists (r1 : R), rset r1) ->
    is_finite (Glb_Rbar rset).
  Proof.
    intros.
    destruct H0.
    apply bounded_is_finite with (a := 0) (b := x).
    - now apply Glb_Rbar_pos.
    - unfold Glb_Rbar, proj1_sig.
      match_destr.
      unfold is_glb_Rbar in i.
      unfold is_lb_Rbar in i.
      destruct i.
      now apply H1.
  Qed.


  Lemma glb_sqrt (rset : R -> Prop) :
    (forall (r:R), rset r -> 0 <= r) ->
    (exists (r1 : R), rset r1) ->
    (Finite (sqrt (Glb_Rbar rset))) = 
    Glb_Rbar (fun r => exists r0, rset r0 /\ r = sqrt r0).
  Proof.
    intros rset_pos nempty.
    generalize (Glb_Rbar_pos rset rset_pos); intro pos_sqrt1.
    assert (pos_sqrt2:Rbar_le 0
              (Glb_Rbar (fun r => exists r0, rset r0 /\ r = sqrt r0))).
    {
      apply Glb_Rbar_pos.
      intros.
      destruct H as [? [? ?]].
      rewrite H0.
      apply sqrt_pos.
    }
    generalize (finite_Glb_Rbar_pos _ rset_pos nempty); intro finite1.
    assert (finite2: is_finite 
              (Glb_Rbar (fun r => exists r0, rset r0 /\ r = sqrt r0))).
    {
      apply finite_Glb_Rbar_pos.
      - intros.
        destruct H as [? [? ?]].
        rewrite H0.
        apply sqrt_pos.
      - destruct nempty.
        exists (sqrt x); exists x.
        now split.
    }
    unfold Glb_Rbar, proj1_sig in *.
    repeat match_destr.
    unfold is_glb_Rbar, is_lb_Rbar in *.
    destruct i; destruct i0.
    apply Rbar_le_antisym.
    - apply H2.
      intros.
      destruct H3 as [? [? ?]].
      rewrite H4.
      apply sqrt_le_1_alt.
      specialize (H x2 H3).
      rewrite <- finite1 in H.
      simpl in H.
      apply H.
    - destruct x; try easy.
      destruct x0; try easy.
      simpl.
      assert (Rbar_le (Rsqr r0) r).
      {
        apply H0.
        intros.
        generalize (H1 (sqrt x)); intros.
        cut_to H4.
        simpl in H4.
        simpl.
        replace (x) with (Rsqr (sqrt x)).
        apply Rsqr_le_abs_1.
        simpl in pos_sqrt1.
        apply Rle_ge in pos_sqrt1.
        simpl in pos_sqrt2.
        apply Rle_ge in pos_sqrt2.        
        rewrite Rabs_right; trivial.
        rewrite Rabs_right; trivial.
        apply Rle_ge.
        apply sqrt_pos.
        rewrite Rsqr_sqrt; trivial.
        apply (rset_pos _ H3).
        exists x.
        split; trivial.
      }
      replace (r0) with (sqrt(Rsqr r0)).
      now apply sqrt_le_1_alt.
      rewrite sqrt_Rsqr_abs.
      simpl in pos_sqrt2.
      rewrite Rabs_right; trivial.
      simpl in pos_sqrt1.
      now apply Rle_ge.
 Qed.

  Lemma glb_power_half (rset : R -> Prop) :
    (forall (r:R), rset r -> 0 <= r) ->
    (exists (r1 : R), rset r1) ->
    (Rbar_power (Glb_Rbar rset) (/2)) = 
    Glb_Rbar (fun r => exists r0, rset r0 /\ r = power r0 (/2)).
  Proof.
    intros.
    generalize (glb_sqrt rset H H0); intros.
    generalize (finite_Glb_Rbar_pos _ H H0); intro finite1.
    generalize (Glb_Rbar_pos _ H); intro rset_pos.
    rewrite <- finite1.
    rewrite <- finite1 in rset_pos.
    simpl in rset_pos.
    unfold Rbar_power.
    rewrite power_sqrt; trivial.
    symmetry.
    rewrite Glb_Rbar_eqset with (E2 := (fun r : R => exists r0 : R, rset r0 /\ r = sqrt r0)).
    now symmetry.
    intros.
    split; intros; destruct H2 as [? [? ?]].
    - exists x0.
      split; trivial.
      rewrite H3.
      rewrite power_sqrt; trivial.
      now apply H.
    - exists x0.
      split; trivial.
      rewrite H3.
      rewrite power_sqrt; trivial.
      now apply H.
  Qed.

    Lemma FiniteCondexp_L2_min_dist_alt
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    Finite (FiniteExpectation prts (rvsqr (rvminus f (FiniteConditionalExpectation f))))
    = 
     (Glb_Rbar
      (fun r : R =>
         exists w : Ts -> R,
           RandomVariable dom2 borel_sa w /\ IsLp prts 2 w /\
           Some (Finite r) = lift (fun x => x) (Expectation (rvsqr (rvminus f w))))).
  Proof.
    generalize (FiniteCondexp_L2_min_dist f); intros.
    assert (nempty: exists (r1 : R) (w : Ts -> R),
               RandomVariable dom2 borel_sa w /\
               IsLp prts 2 w /\ 
               Some (Finite r1) = lift (fun x : Rbar => x) (Expectation (rvsqr (rvminus f w)))).
    {
      exists (FiniteExpectation prts (rvsqr (rvminus f (FiniteConditionalExpectation f)))).
      exists (FiniteConditionalExpectation f).
      split.
      - apply FiniteCondexp_rv.
      - split.
        + apply FiniteCondexp_Lp_sub; try lra; trivial.
        + erewrite FiniteExpectation_Expectation.
          unfold lift; now simpl.
    }
    generalize (glb_power_half
                  (fun r : R =>
         exists w : Ts -> R,
           RandomVariable dom2 borel_sa w /\ IsLp prts 2 w /\
           Some (Finite r) = lift (fun x => x) (Expectation (rvsqr (rvminus f w))))); intros.
    cut_to H0; trivial.
    - rewrite Glb_Rbar_eqset with 
          (E2 :=
              (fun r : R =>
          exists r0 : R,
            (exists w : Ts -> R,
               RandomVariable dom2 borel_sa w /\
               IsLp prts 2 w /\
               Some (Finite r0) = lift (fun x : Rbar => x) (Expectation (rvsqr (rvminus f w)))) /\
            r = power r0 (/ 2))) in H.
      + rewrite <- H0 in H.
        assert (is_finite
                  (Glb_Rbar
           (fun r : R =>
            exists w : Ts -> R,
              RandomVariable dom2 borel_sa w /\
              IsLp prts 2 w /\ Some (Finite r) = lift (fun x : Rbar => x) (Expectation (rvsqr (rvminus f w)))))).
        {
          apply finite_Glb_Rbar_pos; trivial.
          intros.
          destruct H1 as [? [? [? ?]]].
          unfold lift in H3.
          match_case_in H3; intros; rewrite H4 in H3; inversion H3.
          assert (NonnegativeFunction  (rvsqr (rvminus f x))) by typeclasses eauto.
          rewrite Expectation_pos_pofrf with (nnf := H5) in H4.
          invcs H4.
          generalize (@NonnegExpectation_pos _ _ _ _ H5); intros.
          rewrite H8 in H4.
          now simpl in H4.
        }
        rewrite <- H1 in H.
        unfold Rbar_power in H.
        apply Rbar_finite_eq in H.
        apply (f_equal (fun x => power x 2)) in H.
        rewrite power_inv_cancel in H; try lra.
        * rewrite power_inv_cancel in H; try lra.
          -- rewrite <- H1.
             apply Rbar_finite_eq.
             apply H.
          -- generalize (Glb_Rbar_pos
                           (fun r : R =>
                              exists w : Ts -> R,
                                RandomVariable dom2 borel_sa w /\
                                IsLp prts 2 w /\ Some (Finite r) = lift (fun x : Rbar => x) 
                                                               (Expectation (rvsqr (rvminus f w))))); intros.
             cut_to H2.
             ++ rewrite <- H1 in H2.
                simpl in H2.
                apply H2.
             ++ intros.
                destruct H3 as [? [? [? ?]]].
                unfold lift in H5.
                match_case_in H5; intros; rewrite H6 in H5; inversion H5.
                assert (NonnegativeFunction  (rvsqr (rvminus f x))) by typeclasses eauto.
                rewrite Expectation_pos_pofrf with (nnf := H7) in H6.
                invcs H6.
                generalize (@NonnegExpectation_pos _ _ _ _ H7); intros.
                rewrite H10 in H6.
                now simpl in H6.
        * apply FiniteExpectation_pos.
          typeclasses eauto.
      + intros.
        split; intros.
        * destruct H1 as [? [? [? ?]]].
          unfold lift in H3.
          case_eq  (Expectation (rvsqr (rvminus f x0))); intros; rewrite H4 in H3; try congruence.
          assert (Rbar_le 0 r).
          {
            assert (NonnegativeFunction  (rvsqr (rvminus f x0))) by typeclasses eauto.
            rewrite Expectation_pos_pofrf with (nnf := H5) in H4.
            inversion H4. 
            now generalize (@NonnegExpectation_pos _ _ _ _ H5); intros.
          }
          assert (is_finite r).
          {
            inversion H3.
            destruct r.
            - now simpl.
            - simpl in H7.
              discriminate.
            - now simpl in H5.
          }
          exists r.
          split.
          -- exists x0.
             split; trivial.
             split; trivial.
             unfold lift; unfold lift in H3.
             rewrite H4.
             f_equal.
             rewrite <- H6.
             reflexivity.
          -- rewrite <- H6.
             rewrite <- H6 in H3.
             invcs H3.
             reflexivity.
        * destruct H1 as [? [[? [? [? ?]]] ?]].
          exists x1.
          split; trivial.
          split; trivial.
          unfold lift; unfold lift in H3.
          match_case; intros; rewrite H5 in H3; try congruence.
          invcs H3.
          unfold Rbar_power; now simpl.
    - intros.
      destruct H1 as [? [? [? ?]]].
      unfold lift in H3.
      match_case_in H3; intros; rewrite H4 in H3; inversion H3.
      assert (NonnegativeFunction  (rvsqr (rvminus f x))) by typeclasses eauto.
      rewrite Expectation_pos_pofrf with (nnf := H5) in H4.
      invcs H4.
      generalize (@NonnegExpectation_pos _ _ _ _ H5); intros.
      rewrite H8 in H4.
      now simpl in H4.
   Qed.

    Lemma FiniteCondexp_monotone_convergence
        (f : Ts -> R)
        (fn : nat -> Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvfn : forall n, RandomVariable dom borel_sa (fn n)}
        {isfef:IsFiniteExpectation prts f}
        {isfefn:forall n, IsFiniteExpectation prts (fn n)}
        (nnf: almostR2 prts Rle (const 0) f)
        (nnfn : forall n, almostR2 prts Rle (const 0) (fn n))
        (fbound:forall (n:nat), almostR2 prts Rle (fn n) f)
        (fincr:forall (n:nat), almostR2 prts Rle (fn n) (fn (S n)))
        (flim:almost prts (fun omega => is_Elim_seq (fun n => fn n omega) (f omega))) :
    almost (prob_space_sa_sub prts sub)
           (fun omega => is_Elim_seq (fun n => FiniteConditionalExpectation (fn n) omega) (FiniteConditionalExpectation f omega)).
    Proof.
      generalize (Condexp_monotone_convergence prts sub f fn nnf nnfn fbound fincr flim).
      apply almost_impl; apply all_almost; intros ?.
      unfold impl.
      apply is_Elim_seq_proper
      ; repeat intros ?
      ; now rewrite (FiniteCondexp_eq _).
    Qed.

End fin_cond_exp.

Section fin_cond_exp_props.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {dom3 : SigmaAlgebra Ts}
          (sub2 : sa_sub dom3 dom2).

  Lemma FiniteCondexp_tower'
        (f: Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {isfe: IsFiniteExpectation prts f}
        {rv:RandomVariable dom borel_sa (FiniteConditionalExpectation prts sub f)}
    :
      almostR2 (prob_space_sa_sub prts (transitivity sub2 sub))
               eq
               (FiniteConditionalExpectation
                  prts
                  (transitivity sub2 sub)
                  (FiniteConditionalExpectation prts sub f))
               (FiniteConditionalExpectation prts (transitivity sub2 sub) f).
  Proof.
    generalize (Condexp_tower prts sub sub2 f
                              (FiniteConditionalExpectation prts sub f)
               ); intros HH1.
    cut_to HH1.
    - repeat rewrite (FiniteCondexp_eq prts _ _) in HH1.
      revert HH1.
      apply almost_impl; apply all_almost; intros ??.
      now invcs H.
    - now rewrite (FiniteCondexp_eq prts sub f).
  Qed.

  Theorem FiniteCondexp_tower
        (f: Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {isfe: IsFiniteExpectation prts f}
    :
      almostR2 (prob_space_sa_sub prts (transitivity sub2 sub))
               eq
               (FiniteConditionalExpectation
                  prts
                  (transitivity sub2 sub)
                  (rv:=RandomVariable_sa_sub sub _ (rv_x:=FiniteCondexp_rv prts sub f))
                  (FiniteConditionalExpectation prts sub f))
               (FiniteConditionalExpectation prts (transitivity sub2 sub) f).
  Proof.
    apply FiniteCondexp_tower'.
  Qed.

End fin_cond_exp_props.

Section lp_cond_exp.
  (* We can view Conditional Expectation as an operator between sub-Lp spaces *)
  
    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {p} (pbig:1<=p).

    (* TODO: move *)
    Lemma dec_event_sa_sub {P:event dom2}
          (dec:dec_event P) : dec_event (event_sa_sub sub P).
    Proof.
      intros x.
      destruct (dec x).
      - left; apply p0.
      - right; apply n.
    Defined.

    Lemma EventIndicator_sa_sub {P:event dom2}
          (dec:dec_event P) :
      rv_eq (EventIndicator (dec_event_sa_sub dec)) (EventIndicator dec).
    Proof.
      unfold EventIndicator.
      intros ?.
      repeat match_destr; simpl in *; tauto.
    Qed.

    Definition LpRRVcondexp (f:LpRRV prts p) : LpRRV  (prob_space_sa_sub prts sub) p
      := pack_LpRRV  (prob_space_sa_sub prts sub) (FiniteConditionalExpectation
                            prts sub f
                            (rv:=LpRRV_rv _ f)
                            (isfe:=IsLp_Finite prts p f pbig
                                               (rrv:=LpRRV_rv _ _)
                                               (lp:=LpRRV_lp _ _)
                                                  ))
                     (rv:=(FiniteCondexp_rv prts sub f))
                     (lp:=FiniteCondexp_Lp prts sub pbig f).

    Global Instance LpRRV_condexp_sproper : Proper (LpRRV_seq ==> LpRRV_seq) LpRRVcondexp.
    Proof.
      intros ???.
      now apply FiniteConditionalExpectation_ext.
    Qed.

    Global Instance LpRRV_condexp_proper :
      Proper (LpRRV_eq prts ==>
                       LpRRV_eq (prob_space_sa_sub prts sub)) LpRRVcondexp.
    Proof.
      intros ???.
      now apply FiniteCondexp_proper.
    Qed.

    (* the universal property of conditional expectation *)
    Theorem LpRRV_condexp_event (f : LpRRV prts p)
        {P:event dom2}
        (dec:dec_event P) :
      Expectation (LpRRVindicator prts pbig (dec_event_sa_sub dec) f) =
      Expectation (LpRRVindicator (prob_space_sa_sub prts sub) pbig dec (LpRRVcondexp f)).
    Proof.
      generalize (FiniteCondexp_cond_exp_event prts sub f (isfe:=IsLp_Finite _ _ _ pbig (lp:=LpRRV_lp _ _)) dec); intros HH.
      unfold LpRRVindicator; simpl.
      etransitivity; [etransitivity; try eapply HH |].
      - eapply Expectation_ext; intros ?.
        rewrite rvmult_comm.
        apply rvmult_proper; try reflexivity.
        apply EventIndicator_sa_sub.
      - apply Expectation_ext.
        rewrite rvmult_comm.
        apply rvmult_proper; try reflexivity.
    Qed.

    Corollary LpRRV_condexp_event_classic (f : LpRRV prts p) (P:event dom2) :
      Expectation (LpRRVindicator prts pbig (dec_event_sa_sub (classic_dec P)) f) =
      Expectation (LpRRVindicator (prob_space_sa_sub prts sub) pbig (classic_dec P) (LpRRVcondexp f)).
    Proof.
      apply LpRRV_condexp_event.
    Qed.

    Global Instance LpRRV_condexp_nneg (f : LpRRV prts p)
         {nnf : NonnegativeFunction f} :
    NonnegativeFunction (LpRRVcondexp f).
  Proof.
    apply (FiniteCondexp_nneg prts sub f).
  Qed.

  Lemma LpRRV_condexp_id
         (f : LpRRV prts p)
         {rv2 : RandomVariable dom2 borel_sa f} :
    LpRRV_seq (LpRRVcondexp f) (LpRRV_sa_sub_f prts sub p f).
  Proof.
    intros ?.
    unfold LpRRVcondexp; simpl.
    rewrite FiniteCondexp_id; trivial.
  Qed.

  Lemma LpRRV_condexp_id'
         (f : LpRRV (prob_space_sa_sub prts sub) p) :
    LpRRV_seq (LpRRVcondexp (LpRRV_sa_sub _ _ _ f)) f.
  Proof.
    intros ?.
    unfold LpRRVcondexp; simpl.
    rewrite FiniteCondexp_id; trivial.
    typeclasses eauto.
  Qed.

  Corollary LpRRV_condexp_const c :
    LpRRV_seq (LpRRVcondexp (LpRRVconst _ c)) (LpRRVconst _ c).
  Proof.
    eapply LpRRV_condexp_id.
  Qed.

  Theorem LpRRV_condexp_Expectation (f : LpRRV prts p)
    :
      Expectation (LpRRVcondexp f) =
      Expectation f.
  Proof.
    unfold LpRRVcondexp; simpl.
    now rewrite (FiniteCondexp_Expectation prts sub f).
  Qed.

  Lemma LpRRV_condexp_ale (f1 f2:LpRRV prts p):
    almostR2 prts Rle f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) Rle
             (LpRRVcondexp f1)
             (LpRRVcondexp f2).
  Proof.
    apply FiniteCondexp_ale.
  Qed.

  Lemma LpRRV_condexp_scale c (f : LpRRV prts p) :
    LpRRV_eq (prob_space_sa_sub prts sub) 
             (LpRRVcondexp (LpRRVscale _ c f))
             (LpRRVscale _ c (LpRRVcondexp f)).
  Proof.
    red.
    unfold LpRRVcondexp; simpl.
    generalize (FiniteCondexp_scale prts sub c f (isfe:=IsLp_Finite _ _ _ pbig (lp:=LpRRV_lp _ _))).
    apply almost_impl; apply all_almost; intros ??.
    rewrite <- H.
    now apply FiniteConditionalExpectation_ext.
  Qed.

  Lemma LpRRV_condexp_opp (f : LpRRV prts p) :
    LpRRV_eq (prob_space_sa_sub prts sub)
             (LpRRVcondexp (LpRRVopp _ f))
             (LpRRVopp _ (LpRRVcondexp f)).
  Proof.
    red.
    unfold LpRRVcondexp; simpl.
    generalize (FiniteCondexp_opp prts sub f (isfe:=IsLp_Finite _ _ _ pbig (lp:=LpRRV_lp _ _))).
    apply almost_impl; apply all_almost; intros ??.
    rewrite <- H.
    now apply FiniteConditionalExpectation_ext.
  Qed.

  Lemma LpRRV_condexp_plus (f1 f2 : LpRRV prts p) :
    LpRRV_eq (prob_space_sa_sub prts sub)
             (LpRRVcondexp (LpRRVplus _ f1 f2 (p:=bignneg _ pbig)))
             (LpRRVplus _ (LpRRVcondexp f1) (LpRRVcondexp f2) (p:=bignneg _ pbig)).
  Proof.
    red.
    unfold LpRRVcondexp; simpl.
    generalize (FiniteCondexp_plus prts sub f1 f2
                                   (isfe1:=IsLp_Finite _ _ _ pbig (lp:=LpRRV_lp _ _))
                                   (isfe2:=IsLp_Finite _ _ _ pbig (lp:=LpRRV_lp _ _))).
    apply almost_impl; apply all_almost; intros ??.
    rewrite <- H.
    now apply FiniteConditionalExpectation_ext.
  Qed.

  Lemma LpRRV_condexp_minus (f1 f2 : LpRRV prts p) :
    LpRRV_eq (prob_space_sa_sub prts sub)
             (LpRRVcondexp (LpRRVminus _ f1 f2 (p:=bignneg _ pbig)))
             (LpRRVminus _ (LpRRVcondexp f1) (LpRRVcondexp f2) (p:=bignneg _ pbig)).
  Proof.
    red.
    unfold LpRRVcondexp; simpl.
    generalize (FiniteCondexp_minus prts sub f1 f2
                                   (isfe1:=IsLp_Finite _ _ _ pbig (lp:=LpRRV_lp _ _))
                                   (isfe2:=IsLp_Finite _ _ _ pbig (lp:=LpRRV_lp _ _))).
    apply almost_impl; apply all_almost; intros ??.
    rewrite <- H.
    now apply FiniteConditionalExpectation_ext.
  Qed.

  Lemma LpRRV_condexp_Jensen (f : LpRRV prts p) (phi : R -> R)
        {rvphi : RandomVariable dom borel_sa (fun x => phi (f x))}
        {isfephi : IsLp prts p (fun x => phi (f x))} : 
    (forall c x y, convex phi c x y) ->
    almostR2 (prob_space_sa_sub prts sub) Rle
      (fun x => phi ((LpRRVcondexp f) x))
      (LpRRVcondexp (pack_LpRRV _ (fun x => phi (f x)))).
  Proof.
    intros.
    unfold LpRRVcondexp; simpl.
    now eapply FiniteCondexp_Jensen.
  Qed.

  Theorem LpRRV_condexp_factor_out
          (f : LpRRV prts p)
          (g : LpRRV (prob_space_sa_sub prts sub) p)
          {rvfg:RandomVariable dom borel_sa (rvmult f g)}
        {isfef: IsFiniteExpectation prts f}
        {isfefg:IsLp prts p (rvmult f g)} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (LpRRVcondexp (pack_LpRRV _ (rvmult f g)))
             (rvmult g (LpRRVcondexp f)).
  Proof.
    intros.
    unfold LpRRVcondexp; simpl.
    apply (FiniteCondexp_factor_out prts sub f g (isfefg:=IsLp_Finite _ _ _ pbig)).
  Qed.

  Lemma LpRRV_condexp_contract (f:LpRRV prts p) :
    LpRRVnorm (prob_space_sa_sub prts sub) (LpRRVcondexp f) <= LpRRVnorm prts f.
  Proof.
    apply FiniteCondexp_Lp_norm_contractive.
  Qed.

End lp_cond_exp.

Section condexp.
  Lemma is_condexp_expectation_sa_sub_proper {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 dom2' : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          (sub' : sa_sub dom2' dom)
          (sub_sub:sa_sub dom2' dom2)
          (f : Ts -> R) 
          {rvf : RandomVariable dom borel_sa f}
          (ce : Ts -> Rbar) 
          {rvce : RandomVariable dom2 Rbar_borel_sa ce}
          {rvce' : RandomVariable dom2' Rbar_borel_sa ce} :
    is_conditional_expectation prts dom2 f ce ->
    is_conditional_expectation prts dom2' f ce.
  Proof.
    intros ????.
    rewrite H; trivial.
    now apply sub_sub.
  Qed.

  Lemma NonNegCondexp_sa_proper {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        {dom2 dom2' : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (sub' : sa_sub dom2' dom)
        (sub_equiv:sa_equiv dom2 dom2')
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf:NonnegativeFunction f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (NonNegCondexp prts sub f)
             (NonNegCondexp prts sub' f).
  Proof.
    apply sa_equiv_subs in sub_equiv.
    destruct sub_equiv as [sub'_sub sub_sub'].
    generalize (NonNegCondexp_cond_exp prts sub' f); intros isc.
    generalize (NonNegCondexp_rv prts sub' f); intros rvce'.
    assert (rvce : RandomVariable dom2 Rbar_borel_sa (NonNegCondexp prts sub' f)).
    {
      generalize (NonNegCondexp_rv prts sub' f).
      apply RandomVariable_proper_le; trivial; try reflexivity.
    }
    generalize (is_condexp_expectation_sa_sub_proper
                  prts sub' sub sub'_sub f
                  (NonNegCondexp prts sub' f)
                  isc)
    ; intros isc'.
    generalize (NonNegCondexp_cond_exp prts sub f); intros isc2.
    apply (@is_conditional_expectation_nneg_unique _ _ prts _ sub f
                                                  (NonNegCondexp prts sub f)
                                                  (NonNegCondexp prts sub' f) _ _ _)
    ; trivial.
    - apply NonNegCondexp_nneg.
    - apply NonNegCondexp_nneg.
  Qed.

  Lemma Condexp_sa_proper {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        {dom2 dom2' : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (sub' : sa_sub dom2' dom)
        (sub_equiv:sa_equiv dom2 dom2')
        (f : Ts -> R) 
        {rvf : RandomVariable dom borel_sa f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub f)
             (ConditionalExpectation prts sub' f).
  Proof.
    unfold ConditionalExpectation.
    unfold Rbar_rvminus.
    apply Rbar_rvplus_almost_proper.
    - now apply NonNegCondexp_sa_proper.
    - apply Rbar_rvopp_almost_proper.
      now apply NonNegCondexp_sa_proper.
  Qed.    

  Lemma Condexp_all_proper {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        {dom2 dom2' : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (sub' : sa_sub dom2' dom)
        (sub_equiv:sa_equiv dom2 dom2')
        (f1 f2 : Ts -> R) 
        {rvf1 : RandomVariable dom borel_sa f1} 
        {rvf2 : RandomVariable dom borel_sa f2} :
      almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub f1)
             (ConditionalExpectation prts sub' f2).
  Proof.
    intros.
    etransitivity.
    - now apply Condexp_proper.
    - now apply Condexp_sa_proper.
  Qed.    

   Lemma Condexp_all_proper'  {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        {dom2 dom2' : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (sub' : sa_sub dom2' dom)
        (sub_equiv:sa_equiv dom2 dom2')
        (f1 f2 : Ts -> R) 
        {rvf1 : RandomVariable dom borel_sa f1} 
        {rvf2 : RandomVariable dom borel_sa f2} :
      almostR2 prts eq f1 f2 ->
    almostR2 prts eq
             (ConditionalExpectation prts sub f1)
             (ConditionalExpectation prts sub' f2).
  Proof.
    intros.
    generalize (Condexp_all_proper prts sub sub' sub_equiv f1 f2 H).
    apply almostR2_prob_space_sa_sub_lift.
  Qed.

  Lemma FiniteCondexp_all_proper {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 dom2' : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          (sub' : sa_sub dom2' dom)
          (sub_equiv:sa_equiv dom2 dom2')
          (f1 f2 : Ts -> R) 
          {rv1 : RandomVariable dom borel_sa f1}
          {rv2 : RandomVariable dom borel_sa f2}
          {isfe1:IsFiniteExpectation prts f1}
          {isfe2:IsFiniteExpectation prts f2} :
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (FiniteConditionalExpectation prts sub f1)
             (FiniteConditionalExpectation prts sub' f2).
  Proof.
    intros eqq1.
    generalize (Condexp_all_proper prts sub sub' sub_equiv f1 f2 eqq1).
    rewrite (FiniteCondexp_eq _ _ f1), (FiniteCondexp_eq _ _ f2).
    apply almost_impl.
    apply all_almost.
    intros ? eqq.
    now invcs eqq.
  Qed.

End condexp.
