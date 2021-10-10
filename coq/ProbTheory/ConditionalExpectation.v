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
Require Import Almost.
Require Import utils.Utils.
Require Import List.

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
      sa_sigma (SigmaAlgebra := dom2) P ->
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
    assert (sa_G : forall x:R, sa_sigma (G x)).
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
      assert (HH1:ps_P  (ProbSpace:=prts) (event_inter P (event_sa_sub sub (exist sa_sigma (G x) (sa_G x)))) <> 0).
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
        assert (eqq3:pre_event_equiv (union_of_collection (fun n : nat => exist sa_sigma (G (INR n)) (sa_G (INR n))))
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
    assert (sa_G : forall x:R, sa_sigma (G x)).
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
        assert (HH1:ps_P (ProbSpace:=((prob_space_sa_sub prts sub))) (event_inter P (exist sa_sigma (G x) (sa_G x))) <> 0).
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
                          (fun x : nat => event_inter (event_sa_sub sub (exist sa_sigma (G (INR x)) (sa_G (INR x)))) (exist _ _ (sa_finite_Rbar ce2 (RandomVariable_sa_sub sub _)))))
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
  
  Lemma Rbar_rvlim_almost_proper (f1 f2:nat->Ts->R) :
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
      apply Lim_seq_ext; intros n.
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
    : sa_sigma (fun omega => Rbar_ge (rv_X omega) x).
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

  Lemma Rbar_FiniteExpectation_ext rv_X1 rv_X2
        {isfe1:Rbar_IsFiniteExpectation prts rv_X1}
        {isfe2:Rbar_IsFiniteExpectation prts rv_X2}
        (eqq: rv_eq rv_X1 rv_X2)
    :
    Rbar_FiniteExpectation prts rv_X1 = Rbar_FiniteExpectation prts rv_X2.
  Proof.
    unfold Rbar_FiniteExpectation, proj1_sig.
    repeat match_destr.
    rewrite eqq in e.
    congruence.
  Qed.

  Global Instance Rbar_IsFiniteExpectation_proper
    : Proper (rv_eq ==> iff) (Rbar_IsFiniteExpectation prts).
  Proof.
    unfold Rbar_IsFiniteExpectation.
    intros x y eqq.
    now rewrite eqq.
  Qed.
           
  Lemma Rbar_FiniteExpectation_ext_alt {rv_X1 rv_X2}
        {isfe1:Rbar_IsFiniteExpectation prts rv_X1}
        (eqq: rv_eq rv_X1 rv_X2)
    :
      Rbar_FiniteExpectation prts rv_X1 =
      Rbar_FiniteExpectation prts rv_X2 (isfe:=proj1 (Rbar_IsFiniteExpectation_proper _ _ eqq) isfe1).
  Proof.
    now apply Rbar_FiniteExpectation_ext.
  Qed.

  Instance list_sum_rv f l
           {rv:forall c, RandomVariable dom borel_sa (f c)}
    : RandomVariable dom borel_sa
                     (fun omega : Ts => RealAdd.list_sum (map (fun c : R => f c omega) l)).
  Proof.
    induction l; simpl.
    - apply rvconst.
    - generalize @rvplus_rv; unfold rvplus; intros HH.
      apply HH; trivial.
  Qed.

  
  Lemma FiniteExpectation_list_sum f l 
        {rv:forall c, RandomVariable dom borel_sa (f c)}
        {isfe:forall c, IsFiniteExpectation prts (f c)} :
    Expectation
            (fun omega => RealAdd.list_sum
                          (map
                             (fun c : R =>
                                (f c omega))
                             l)) =
    Some (Finite
            (RealAdd.list_sum
               (map
                  (fun c : R =>
                     FiniteExpectation prts (f c))
                  l))).
  Proof.
    induction l; simpl.
    - apply Expectation_const.
    - generalize Expectation_sum_finite; unfold rvplus; intros HH.
      apply HH; trivial.
      + now apply list_sum_rv.
      + now rewrite <- FiniteExpectation_Expectation.
  Qed.

  Lemma is_conditional_expectation_finexp
             (f : Ts -> R)
             (ce : Ts -> Rbar)           
             {rvf : RandomVariable dom borel_sa f}
             {rvce : RandomVariable dom2 Rbar_borel_sa ce}            
    : is_conditional_expectation dom2 f ce ->
      forall P (dec:dec_pre_event P),
        sa_sigma (SigmaAlgebra := dom2) P ->
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
  
  Global Instance val_indicator_rv g c
         {rv:RandomVariable dom borel_sa g} :
    RandomVariable dom borel_sa (val_indicator g c).
  Proof.
    apply EventIndicator_pre_rv.
    apply sa_le_pt.
    now apply rv_measurable.
  Qed.

  Global Instance scale_val_indicator_rv g c
         {rv:RandomVariable dom borel_sa g} :
    RandomVariable dom borel_sa (scale_val_indicator g c).
  Proof.
    apply rvscale_rv.
    now apply val_indicator_rv.
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

  Lemma IsFiniteExpectation_list_sum (f : R -> Ts -> R) (l : list R)
        {rv:forall c : R, RandomVariable dom borel_sa (f c)}
        {isfe : forall c : R, IsFiniteExpectation prts (f c)} :
  IsFiniteExpectation prts (fun omega : Ts => RealAdd.list_sum (map (fun c : R => f c omega) l)).
  Proof.
    unfold IsFiniteExpectation.
    now rewrite (FiniteExpectation_list_sum f l).
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
    
    rewrite (FiniteExpectation_list_sum _ _ (isfe:=isfef)).

    assert (RandomVariable dom borel_sa (fun x : Ts => ce x)).
    {
      apply Rbar_real_rv.
      now apply RandomVariable_sa_sub.
    }

    generalize (rvff ce); intros rvfce.
    cut_to rvfce; trivial.
    
    generalize (isfe1' ce); intros isfece.
    cut_to isfece; trivial.

    rewrite (FiniteExpectation_list_sum _ _ (isfe:=isfece)).
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

    assert (sa_sigma (SigmaAlgebra:=dom2) (pre_event_inter (fun omega0 : Ts => g omega0 = a) P)).
    {
      apply sa_inter; trivial.
      apply sa_le_pt.
      apply rv_measurable.
      now apply RandomVariable_sa_sub.
    } 

    assert (sa_sigma (SigmaAlgebra:=dom) (pre_event_inter (fun omega0 : Ts => g omega0 = a) P)).
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
          (f g ce : Ts -> R)
          {nnegf : NonnegativeFunction f}          
          {nnegg : NonnegativeFunction g}
          {nnegce : NonnegativeFunction ce}          
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom2 borel_sa g}
          {rvce : RandomVariable dom2 borel_sa ce}
          {rvgf: RandomVariable dom borel_sa (rvmult f g)} :
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g) ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
    intros isfef isfefg iscondf.
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
      generalize (is_conditional_expectation_factor_out_frf f (simple_approx g n) ce _ iscondf) ; intros.
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
    assert (RandomVariable dom borel_sa (rvmult (rvmult f g) (EventIndicator dec))).
    {
      apply rvmult_rv; trivial.
      apply RandomVariable_sa_sub; trivial.
      apply EventIndicator_pre_rv; trivial.
    }

   generalize (monotone_convergence (rvmult (rvmult f g) (EventIndicator dec))); intros.
   specialize (H6  (fun n => (rvmult (rvmult f (simple_approx g n))
                                            (EventIndicator dec))) ).
   assert (NonnegativeFunction (rvmult (rvmult f g) (EventIndicator dec))) by
       typeclasses eauto.
   assert (forall n : nat,
        RandomVariable 
          dom borel_sa
          (rvmult (rvmult f (simple_approx g n))
                  (EventIndicator dec))).
   {
     intros.
     apply rvmult_rv.
     - apply rvmult_rv; trivial.
       apply RandomVariable_sa_sub; trivial.
     - apply RandomVariable_sa_sub; trivial.
       apply EventIndicator_pre_rv; trivial.
   }
   assert (forall n : nat,
                  NonnegativeFunction
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
              NonnegativeFunction
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
             real( NonnegExpectation
                (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n))
                        (EventIndicator dec))) =
             real (NonnegExpectation
               (rvmult
                  (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                          (fun x : Ts => ce x)) 
                  (fun x : Ts => EventIndicator dec x)))).
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
     rewrite (Lim_seq_ext _ _ H11).
     generalize (monotone_convergence_Rbar
                   (fun n =>
                       (rvmult (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x) (fun x : Ts => ce x))
          (fun x : Ts => EventIndicator dec x))) ); intros.
     assert (forall n : nat,
         RandomVariable dom borel_sa
           (fun omega : Ts =>
            rvmult
              (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x)
                      (fun x : Ts => ce x)) (fun x : Ts => EventIndicator dec x) omega)).
     {
       intros.
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
     + intros.
       assert (IsFiniteExpectation prts (rvmult ce (EventIndicator dec))).
       {
         specialize (iscondf P dec H).
         unfold IsFiniteExpectation.
         assert (rv_eq (Rbar_rvmult (fun x : Ts => ce x) (fun x : Ts => EventIndicator dec x))
                       (rvmult ce (EventIndicator dec))).
         {
           intro x.
           now rv_unfold; unfold Rbar_rvmult; simpl.
         }
         rewrite (Rbar_Expectation_ext H15) in iscondf.
         rewrite <- Expectation_Rbar_Expectation in iscondf.
         rewrite <- iscondf.
         apply IsFiniteExpectation_indicator; trivial.
         apply sub; trivial.
      }
       assert (rvceind: RandomVariable dom borel_sa (rvmult ce (EventIndicator dec))).
       {
         apply rvmult_rv.
         - apply RandomVariable_sa_sub; trivial.
         - apply EventIndicator_pre_rv.
           apply sub.
           apply H.
       }
       assert (rvapprox: RandomVariable dom borel_sa (simple_approx (fun x : Ts => g x) n)) by
         now apply RandomVariable_sa_sub.
       generalize (IsFiniteExpectation_mult_finite_range (rvmult ce (EventIndicator dec)) (simple_approx g n) H15); intros.
       assert (rv_eq 
                 (rvmult (rvmult (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x) (fun x : Ts => ce x))
                         (fun x : Ts => EventIndicator dec x))
                 (rvmult (rvmult ce (EventIndicator dec))
                         (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x))).
       {
         intro x.
         rv_unfold.
         lra.
       }
       assert (NonnegativeFunction 
                 (rvmult (rvmult ce (EventIndicator dec))
                         (fun x : Ts => simple_approx (fun x0 : Ts => g x0) n x))).
       {
         apply NonNegMult.
         - apply simple_approx_pofrf.
         - apply NonNegMult; trivial.
           typeclasses eauto.
       }
       rewrite (NonnegExpectation_ext _ _ H17).
       now apply IsFiniteNonnegExpectation.
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
     assert (NonnegativeFunction (rvmult f g)) by now apply NonNegMult.
     apply Finite_NonnegExpectation_le with (nnf2 := H3).
     + intro x.
       rv_unfold.
       match_destr.
       * rewrite Rmult_1_r.
         apply Rmult_le_compat_l; trivial.
         generalize (simple_approx_le g nnegg n x); intros.
         apply H12.
       * rewrite Rmult_0_r.
         apply H3.
     + now apply IsFiniteNonnegExpectation.
   - intros.
     unfold rvmult.
     replace (Finite  (f omega * g omega * EventIndicator dec omega)) with
         (Rbar_mult (f omega * g omega) (EventIndicator dec omega)) by now simpl.
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
          {rvce : RandomVariable dom2 borel_sa ce}
          {rvace : RandomVariable dom2 borel_sa ace}    :
    IsFiniteExpectation prts f ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvabs f) ace ->    
    almostR2 prts Rle (rvabs ce) ace.
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
      unfold rvabs.
      apply Rabs_le.
      cut_to H6; cut_to H7.
      + split; lra.
      + now apply event_inter_sub_r in H8.
      + now apply event_inter_sub_l in H8.
      + now apply event_inter_sub_r in H8.
    Qed.
  
  Lemma IsFiniteExpectation_abs_id (f : Ts -> R)
          {rvf : RandomVariable dom borel_sa f} :
    IsFiniteExpectation prts (rvabs f) ->
    IsFiniteExpectation prts f.
  Proof.
    intros.
    apply IsFiniteExpectation_bounded with (rv_X1 := rvopp (rvabs f)) (rv_X3 := rvabs f); trivial.
    - now apply IsFiniteExpectation_opp.
    - intro x.
      unfold rvopp, rvabs, rvscale.
      apply Ropp_le_cancel.
      ring_simplify.
      rewrite <- Rabs_Ropp.
      apply Rle_abs.
    - intro x.
      unfold rvabs.
      apply Rle_abs.
  Qed.

  Lemma IsFiniteExpectation_abs_bound (f g : Ts -> R)
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom borel_sa g} :
    rv_le (rvabs f) g ->
    IsFiniteExpectation prts g ->
    IsFiniteExpectation prts f.
  Proof.
    intros.
    apply IsFiniteExpectation_abs_id; trivial.
    apply IsFiniteExpectation_bounded with (rv_X1 := fun (x:Ts) => 0) (rv_X3 := g); trivial.
    - apply IsFiniteExpectation_const.
    - intro x.
      unfold rvabs.
      apply Rabs_pos.
   Qed.

  Lemma IsFiniteExpectation_abs_bound_almost (f g : Ts -> R)
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom borel_sa g} :
    almostR2 prts Rle (rvabs f) g ->
    IsFiniteExpectation prts g ->
    IsFiniteExpectation prts f.
  Proof.
    intros ale isfe.
    destruct (almostR2_le_split_r _ _ _ ale)
      as [g' [eqq [lee rvg']]].
    cut_to rvg'; try typeclasses eauto.
    eapply IsFiniteExpectation_abs_bound; try eapply lee; trivial.
    eapply IsFiniteExpectation_proper_almostR2; try eapply isfe; eauto.
  Qed.

  Instance Dominated_convergence0
          (fn : nat -> Ts -> R)
          (g : Ts -> R)
          {rvn : forall n, RandomVariable dom borel_sa (fn n)}
          {rvg : RandomVariable dom borel_sa g} :
    (forall n, rv_le (rvabs (fn n)) g) ->
    IsFiniteExpectation prts g ->
    forall n, IsFiniteExpectation prts (fn n).
  Proof.
    intros.
    now apply IsFiniteExpectation_abs_bound with (g := g).
  Qed.

  Instance Dominated_convergence1
          (fn : nat -> Ts -> R)
          (f g : Ts -> R)
          {rvn : forall n, RandomVariable dom borel_sa (fn n)}
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom borel_sa g} 
          (isfeg : IsFiniteExpectation prts g)
          (le_fn_g : (forall n, rv_le (rvabs (fn n)) g)) 
          (lim : almost prts (fun x => is_lim_seq (fun n => fn n x) (f x))) :
    IsFiniteExpectation prts f.
  Proof.
    intros.
    assert (almostR2 prts Rbar_le (rvabs f) g).
    {
      destruct lim as [? [? ?]].
      exists x; split; trivial.
      intros.
      specialize (H0 x0 H1).
      apply is_lim_seq_abs in H0.
      unfold rvabs.
      apply is_lim_seq_le with (u := (fun n : nat => Rabs (fn n x0)) )
                               (v := (fun n => g x0)); trivial.
      - intro.
        specialize (le_fn_g n x0).
        now unfold rvabs in le_fn_g.
      - apply is_lim_seq_const.
    }
    apply IsFiniteExpectation_abs_bound_almost with (g := g); trivial.
  Qed.

  Theorem Dominated_convergence
          (fn : nat -> Ts -> R)
          (f g : Ts -> R)
          {rvn : forall n, RandomVariable dom borel_sa (fn n)}
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom borel_sa g} 
          {isfen : forall n, IsFiniteExpectation prts (fn n)}
          {isfe: IsFiniteExpectation prts f} : 
    IsFiniteExpectation prts g ->
    (forall n, rv_le (rvabs (fn n)) g) ->
    (forall x, is_lim_seq (fun n => fn n x) (f x)) ->
    is_lim_seq (fun n => FiniteExpectation prts (fn n)) (FiniteExpectation prts f).
  Proof.
    intros.
    assert (forall n, NonnegativeFunction (rvplus g (fn n))).
    {
      intros n x.
      specialize (H0 n x).
      rv_unfold; unfold rvabs in H0.
      unfold Rabs in H0.
      match_destr_in H0; lra.
    }

    assert (forall n, NonnegativeFunction (rvminus g (fn n))).
    {
      intros n x.
      specialize (H0 n x).
      rv_unfold; unfold rvabs in H0.
      unfold Rabs in H0.
      match_destr_in H0; lra.
   }

    generalize (Rbar_NN_Fatou (fun n => rvplus g (fn n)) _ _); intros.
    generalize (Rbar_NN_Fatou  (fun n => rvminus g (fn n)) _ _ ); intros.

    assert (forall n, IsFiniteExpectation prts (rvplus g (fn n))).
    {
      intro n.
      now apply IsFiniteExpectation_plus.
    }
    assert (forall n, IsFiniteExpectation prts (rvminus g (fn n))).
    {
      intro n.
      now apply IsFiniteExpectation_minus.
    }
    generalize (fun n => IsFiniteNonnegExpectation prts (rvplus g (fn n))); intros.
    generalize (fun n => IsFiniteNonnegExpectation prts (rvminus g (fn n))); intros.
    specialize (H4 H8).
    specialize (H5 H9).
    cut_to H4.
    cut_to H5.

    - assert (rv_eq (fun omega : Ts => LimInf_seq (fun n : nat => rvplus g (fn n) omega))
                    (rvplus g f)).
      {
        intro x.
        unfold rvplus, Rbar_rvplus.
        rewrite LimInf_seq_const_plus.
        rewrite is_LimInf_seq_unique with (l := f x); trivial.
        now apply is_lim_LimInf_seq.
     }

      assert (rv_eq (fun omega : Ts => LimInf_seq (fun n : nat => rvminus g (fn n) omega))
                    (rvminus g f)).
      {
        intro x.
        rv_unfold.
        unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
        rewrite LimInf_seq_const_plus.
        rewrite LimInf_seq_ext with (g := fun n => - (fn n x)).
        rewrite LimInf_seq_opp.        
        - rewrite is_LimSup_seq_unique with (l:=f x).
          + simpl; apply Rbar_finite_eq; lra.
          + now apply is_lim_LimSup_seq.
        - exists (0%nat).
          intros.
          lra.
      }
      erewrite (Rbar_NonnegExpectation_ext _ _ H10) in H4.
      erewrite (Rbar_NonnegExpectation_ext _ _ H11) in H5.

      erewrite <- NNExpectation_Rbar_NNExpectation in H4.
      erewrite <- NNExpectation_Rbar_NNExpectation in H5.      

      erewrite <- FiniteNonnegExpectation_alt in H4.
      erewrite <- FiniteNonnegExpectation_alt in H5.      

      rewrite LimInf_seq_ext with (g := fun n => (FiniteExpectation prts g) + 
                                                 (FiniteExpectation prts (fn n))) in H4.

      rewrite LimInf_seq_ext with (g := fun n => (FiniteExpectation prts g) -
                                                 (FiniteExpectation prts (fn n))) in H5.

      rewrite LimInf_seq_const_plus in H4.
      rewrite LimInf_seq_const_minus in H5.

      erewrite FiniteExpectation_plus in H4.
      erewrite FiniteExpectation_minus in H5.

      assert (Rbar_le (FiniteExpectation prts f) 
                      (LimInf_seq (fun n => FiniteExpectation prts (fn n)))).
      {
        case_eq (LimInf_seq (fun n => FiniteExpectation prts (fn n))); intros.
        - rewrite H12 in H4; simpl in H4.
          simpl.
          apply Rplus_le_reg_l in H4.
          apply H4.
        - now simpl.
        - rewrite H12 in H4; now simpl in H4.
      }

      assert (Rbar_le (LimSup_seq (fun n => FiniteExpectation prts (fn n)))
                      (FiniteExpectation prts f)).
      {
        case_eq (LimSup_seq (fun n => FiniteExpectation prts (fn n))); intros.
        - rewrite H13 in H5; simpl in H5.
          apply Rplus_le_reg_l in H5.
          simpl.
          apply Ropp_le_cancel.
          apply H5.
        - rewrite H13 in H5; now simpl in H5.
        - now simpl.
      }

      generalize (Rbar_le_trans _ _ _ H13 H12); intros.
      generalize (LimSup_LimInf_seq_le (fun n => FiniteExpectation prts (fn n))); intros.
      generalize (Rbar_le_antisym _ _ H14 H15); intros.
      rewrite H16 in H13.
      generalize (Rbar_le_antisym _ _ H13 H12); intros.

      assert (Lim_seq (fun n => FiniteExpectation prts (fn n)) = FiniteExpectation prts f).
      {
        unfold Lim_seq.
        rewrite H16, H17.
        now rewrite x_plus_x_div_2.
      }
      rewrite <- H18.
      apply Lim_seq_correct.
      now apply ex_lim_LimSup_LimInf_seq.

      exists (0%nat); intros.
      erewrite <- FiniteNonnegExpectation_alt.
      simpl.
      erewrite <- FiniteExpectation_minus.
      apply FiniteExpectation_pf_irrel.
      
      exists (0%nat); intros.
      erewrite <- FiniteNonnegExpectation_alt.
      simpl.
      erewrite <- FiniteExpectation_plus.
      apply FiniteExpectation_pf_irrel.

      - apply Rbar_lim_inf_rv.
        intros.
        typeclasses eauto.

      - apply Rbar_lim_inf_rv.
        intros.
        typeclasses eauto.

        Unshelve.
        + intro x.
          unfold rvplus.
          generalize (is_lim_seq_le (fun n => 0) (fun n => g x + fn n x) 0 (g x + f x)); intros.
          unfold rvplus in H2.
          apply H4.
          * intros.
            apply H2.
          * apply is_lim_seq_const.
          * apply is_lim_seq_plus'; trivial.
            apply is_lim_seq_const.
        + intro x.
          rv_unfold.
          generalize (is_lim_seq_le (fun n => 0) (fun n => g x + (-1)*fn n x) 0 (g x + (-1)*f x)); intros.         
          apply H4.
          * intros.
            apply H3.
          * apply is_lim_seq_const.
          * apply is_lim_seq_plus'.
            -- apply is_lim_seq_const.
            -- replace (Finite (-1 * f x)) with (Rbar_mult (-1) (f x)).
               ++ now apply is_lim_seq_scal_l.
               ++ now simpl.
        + easy.
        + easy.
        + easy.
        + easy.
  Qed.

  Theorem Dominated_convergence_almost
          (fn : nat -> Ts -> R)
          (f g : Ts -> R)
          {rvn : forall n, RandomVariable dom borel_sa (fn n)}
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom borel_sa g} 
          {isfefn : forall n, IsFiniteExpectation prts (fn n)}
          {isfe: IsFiniteExpectation prts f} : 
    IsFiniteExpectation prts g ->
    (forall n, almostR2 prts Rle (rvabs (fn n)) g) ->
    (almost prts (fun x => is_lim_seq (fun n => fn n x) (f x))) ->
    is_lim_seq (fun n => FiniteExpectation prts (fn n)) (FiniteExpectation prts f).
  Proof.
    intros isfeg ale islim.
    assert (ale':forall n, almostR2 prts (fun x y => Rle (Rabs x) y) (fn n) g).
    {
      intros n; generalize (ale n).
      apply almost_impl; apply all_almost; intros ??.
      apply H.
    } 

    destruct (almostR2_le_forall_l_split prts _ _ ale')
      as [fn' [g' [eqqfn [eqqg [le' [rvf' rvg']]]]]].

    assert (rvfn':forall n, RandomVariable dom borel_sa (fn' n)) by eauto.

    assert (isfefn':forall n, IsFiniteExpectation prts (fn' n)).
    {
      intros n.
      eapply (IsFiniteExpectation_proper_almostR2 prts (fn n)); trivial; typeclasses eauto.
    } 
    
    cut (is_lim_seq (fun n : nat => FiniteExpectation prts (fn' n)) (FiniteExpectation prts f)).
    - apply is_lim_seq_ext; intros.
      now apply FiniteExpectation_proper_almostR2; trivial.
    - destruct (almost_and prts (almost_forall _ eqqfn) islim) as [p [pone ph]].
      unfold pre_inter_of_collection, pre_event_inter in ph.

      assert (rvfne:(forall n : nat, RandomVariable dom borel_sa (rvmult (fn n) (EventIndicator (classic_dec p))))).
      {
        intros.
        apply rvmult_rv; trivial.
        apply EventIndicator_rv.
      }

      assert (rvfe:RandomVariable dom borel_sa (rvmult f (EventIndicator (classic_dec p)))).
      {
        apply rvmult_rv; trivial.
        apply EventIndicator_rv.
      }

      assert (isfen : forall n : nat, IsFiniteExpectation prts (rvmult (fn n) (EventIndicator (classic_dec p)))).
      {
        intros.
        apply IsFiniteExpectation_indicator; trivial.
        now destruct p.
      } 
      assert (isfe0 : IsFiniteExpectation prts (rvmult f (EventIndicator (classic_dec p)))).
      {
        apply IsFiniteExpectation_indicator; trivial.
        now destruct p.
      } 

      generalize (Dominated_convergence 
                    (fun n => rvmult (fn n) (EventIndicator (classic_dec p)))
                    (rvmult f (EventIndicator (classic_dec p)))
                    g'
                 ); intros HH.
      cut_to HH.
      + assert (eqq1:FiniteExpectation prts f =
                     FiniteExpectation prts
                                       (rvmult f (EventIndicator (classic_dec p)))).
        {
          apply FiniteExpectation_proper_almostR2; trivial.
          exists p; split; trivial; intros.
          rv_unfold.
          match_destr; try lra; tauto.
        }
        rewrite eqq1.
        revert HH.
        apply is_lim_seq_ext; intros.
        apply FiniteExpectation_proper_almostR2; trivial.
        exists p; split; trivial; intros.
        rv_unfold.
        match_destr; try tauto.
        rewrite (proj1 (ph x e)).
        lra.
      + eapply IsFiniteExpectation_proper_almostR2; try eapply isfeg; auto.
      + intros ??.
        transitivity (rvabs (fn' n) a).
        * rv_unfold.
          match_destr.
          -- rewrite (proj1 (ph a e)); trivial.
             rewrite Rmult_1_r.
             reflexivity.
          -- rewrite Rmult_0_r.
             rewrite Rabs_R0.
             apply Rabs_pos.
        * apply le'.
      + intros.
        rv_unfold.
        destruct (classic_dec p x).
        * rewrite Rmult_1_r.
          destruct (ph x e) as [_ islim'].
          revert islim'.
          apply is_lim_seq_ext; intros.
          now rewrite Rmult_1_r.
        * rewrite Rmult_0_r.
          generalize (is_lim_seq_const 0).
          apply is_lim_seq_ext; intros.
          now rewrite Rmult_0_r.
  Qed.
  
  Lemma Jensen (rv_X : Ts -> R) (phi : R -> R) (a : R) 
        {rv : RandomVariable dom borel_sa rv_X}
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => phi (rv_X x))} :    
    (* following implied if phi is convex, constructive? *)
    (forall x, a * (x - FiniteExpectation prts rv_X) <= phi x - phi (FiniteExpectation prts rv_X)) ->
    FiniteExpectation prts (fun x => phi (rv_X x)) >= phi (FiniteExpectation prts rv_X).
  Proof.
    intros.
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
    specialize (H (rv_X x)).
    lra.
  Qed.

  Lemma Jensen_abs (rv_X : Ts -> R) 
        {rv : RandomVariable dom borel_sa rv_X}
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => Rabs (rv_X x))} :    
    FiniteExpectation prts (fun x => Rabs (rv_X x)) >= Rabs (FiniteExpectation prts rv_X).    
  Proof.
    destruct (Rle_dec 0 (FiniteExpectation prts rv_X)).
    - apply (Jensen rv_X Rabs 1).
      intros.
      rewrite Rmult_1_l.
      rewrite (Rabs_right (FiniteExpectation prts rv_X)); try lra.
      unfold Rminus.
      apply Rplus_le_compat_r.
      apply Rle_abs.
    - apply (Jensen rv_X Rabs (-1)).
      intros.
      assert (FiniteExpectation prts rv_X < 0) by lra.
      rewrite (Rabs_left (FiniteExpectation prts rv_X)); try lra.
      ring_simplify.
      rewrite Rplus_comm.
      apply Rplus_le_compat_l.
      apply Rabs_maj2.
   Qed.

(*  
  Theorem Domainated_convergence3
          (fn : nat -> Ts -> R)
          (f g : Ts -> R)
          {rvn : forall n, RandomVariable dom borel_sa (fn n)}
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom borel_sa g} 
          {isfen : forall n, IsFiniteExpectation prts (fn n)}
          {isfe: IsFiniteExpectation prts f} : 
    IsFiniteExpectation prts g ->
    (forall n, rv_le (rvabs (fn n)) g) ->
    (forall x, is_lim_seq (fun n => fn n x) (f x)) ->
    is_lim_seq (fun n => FiniteExpectation prts (fn n)) (FiniteExpectation prts f).
  Proof.
    intros.
    pose (gn := fun n => rvabs (rvminus (fn n) f)).
    assert (forall n, IsFiniteExpectation prts (gn n)).
    {
      intros.
      unfold gn.
      apply IsFiniteExpectation_abs.
      - typeclasses eauto.
      - now apply IsFiniteExpectation_minus.
    }
    assert (forall x, is_lim_seq (fun n => gn n x) 0).
    {
      intro.
      unfold gn.
      rv_unfold.
      replace (Finite 0) with (Rbar_abs 0).
      - apply is_lim_seq_abs.
        replace (0) with (f x + -1 * f x) by lra.
        apply is_lim_seq_plus'; trivial.
        apply is_lim_seq_const.
      - simpl.
        now rewrite Rabs_R0.
    }
    assert (rv_le (rvabs f) g).
    {
      intro x.
      unfold rvabs.
      assert (is_lim_seq (fun n => Rabs (fn n x)) (Rbar_abs (f x))).
      - now apply is_lim_seq_abs.
      - simpl in H4.
        unfold rv_le, rvabs, pointwise_relation in H0.
        generalize (is_lim_seq_le (fun n => Rabs (fn n x)) (fun n => g x) (Rabs (f x)) (g x)); intros.
        apply H5; trivial.
        apply is_lim_seq_const.
    }
    assert (forall n, rv_le (gn n) (rvscale 2 g)).
    {
      intros n x.
      unfold gn; rv_unfold.
      specialize (H0 n x); simpl in H0.
      generalize (Rabs_triang (fn n x) (-1 * f x)); intros.
      eapply Rle_trans.
      - apply H5.
      - replace (-1 * f x) with (- f x) by lra.
        rewrite Rabs_Ropp.
        specialize (H4 x); simpl in H4.
        replace (2 * g x) with ((g x) + (g x)) by lra.
        now apply Rplus_le_compat.
    }
    assert (forall n, NonnegativeFunction (rvminus (rvscale 2 g) (gn n))).
    {
      intros n x.
      rv_unfold.
      specialize (H5 n x).
      unfold gn in H5.
      unfold gn.
      lra.
    }
    assert (forall x, is_LimInf_seq (fun n => (rvminus (rvscale 2 g) (gn n)) x) (2 * g x)).
    {
      intros.
      apply is_lim_LimInf_seq.
      rv_unfold; simpl.
      replace (Finite (2 * g x)) with (Finite (2 * g x + 0)) by now rewrite Rplus_0_r.
      apply is_lim_seq_plus'.
      - apply is_lim_seq_const.
      - replace (Finite 0) with (Rbar_mult (-1) (0)).
        + now apply is_lim_seq_scal_l.
        + now rewrite Rbar_mult_0_r.
   }
    assert (rv_eq (fun x => LimInf_seq (fun n => (rvminus (rvscale 2 g) (gn n)) x)) 
                  (rvscale 2 g)).
    {
      intro x.
      specialize (H7 x).
      now apply is_LimInf_seq_unique in H7.
    }
    assert (isfe_Xn : forall n : nat, IsFiniteExpectation prts (rvminus (rvscale 2 g) (gn n))) by admit.
    assert (isfe_limInf : IsFiniteExpectation prts
                            (fun omega : Ts =>
                             LimInf_seq (fun n : nat => rvminus (rvscale 2 g) (gn n) omega))) by admit.

(*
    generalize (Rbar_NN_Fatou (fun n => rvminus (rvscale 2 g) (gn n)) _ _ _ _); intros fatou.
    cut_to fatou.
    - rewrite (FiniteExpectation_ext prts _ _ H8) in fatou.
      + rewrite LimInf_seq_ext with (g := fun n => (FiniteExpectation prts (rvscale 2 g)) - 
                                                   (FiniteExpectation prts (gn n))) in fatou.
        * Search FiniteExpectation.
          rewrite <- FiniteNonnegExpectation in Fatou.
      + intro x.
        specialize (H8 x).
        apply (f_equal (fun (z:Rbar) => real z)) in H8.
        rewrite H8.

        now simpl.
 *)       
      
 *)

  (* from theory of probability 1 *)
  (* by Gordan Žitkovic ́ *)
  Lemma convex_4_2_2 (phi : R -> R) :
    (forall c x y, convex phi c x y) ->
    exists (a b : nat -> R),
    forall (x: R),
      is_sup_seq (fun n => (a n) * x + (b n)) (phi x).
  Proof.
    Admitted.


  Lemma is_condexp_Jensen (rv_X ce phice: Ts -> R) (phi : R -> R) (a b : nat -> R) 
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
    apply (is_condexp_Jensen rv_X ce ace Rabs a b); trivial.
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

  Theorem is_conditional_expectation_factor_out_nneg
          (f g ce ace : Ts -> R)
          {nnegg : NonnegativeFunction g}
          {nnegace : NonnegativeFunction ace}          
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom2 borel_sa g}
          {rvce : RandomVariable dom2 borel_sa ce}
          {rvace : RandomVariable dom2 borel_sa ace}          
          {rvgf: RandomVariable dom borel_sa (rvmult f g)} 
          {rvgaf: RandomVariable dom borel_sa (rvmult (rvabs f) g)} 
          {rvgce: RandomVariable dom2 borel_sa (Rbar_rvmult g ce)} :
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
                               (rvabs (Rbar_rvmult (simple_approx g n) ce)) 
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
          apply Rle_ge, simple_approx_pofrf.
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
        apply almostR2_le_subr.
        intro x.
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
    generalize (is_conditional_expectation_factor_out_nneg_both (rvabs f) g ace H6); intros.
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
    specialize (H7 H8 H2).
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
    
    generalize (Dominated_convergence_almost
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
      - apply (IsFiniteExpectation_abs_bound_almost (rvmult g ce) (rvmult g ace)).
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
    specialize (H12 (Rbar_rvmult g ace) _ _ _ _ _).
    clear H13 H14 H15.
    cut_to H12.
    apply is_lim_seq_unique in H12.
    rewrite FiniteExpectation_Expectation with (isfe := H16).
    rewrite <- H12.
    generalize (Dominated_convergence
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
    assert (forall n : nat,
               IsFiniteExpectation 
                 prts
                 (rvmult (rvmult f (simple_approx (fun x : Ts => g x) n)) (EventIndicator dec))).
    {
      intro.
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
    assert (IsFiniteExpectation prts (rvmult (rvmult f g) (EventIndicator dec))).
    {
      apply IsFiniteExpectation_indicator; trivial.
      now apply sub.
    }
    specialize (H13 (rvmult (rvabs f) g) _ _ _ _ _ _).    
    clear H14 H15.
    cut_to H13.
    apply is_lim_seq_unique in H13.
    rewrite FiniteExpectation_Expectation with (isfe := H19).    
    f_equal.
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
      rewrite FiniteExpectation_Expectation with (isfe := (H18 n)) in H15.
      clear H9 H11 H12 H13 H14 H20 H21 H22 H23.
      assert (IsFiniteExpectation prts
                (@rvmult Ts
                (@rvmult Ts (fun x : Ts => @simple_approx Ts (fun x0 : Ts => Finite (g x0)) n x)
                   (fun x : Ts => ce x)) (fun x : Ts => @EventIndicator Ts P dec x))) by easy.
      rewrite FiniteExpectation_Expectation with (isfe := H9) in H15.      
      invcs H15.
      rewrite H12.
      apply FiniteExpectation_pf_irrel.
    - intros n x.
      generalize (simple_approx_le g nnegg n x); intros.
      unfold rvmult, rvabs, EventIndicator.
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
      unfold Rbar_IsFiniteExpectation in H14.
      rewrite <- Expectation_Rbar_Expectation in H14.
      apply H14.
    - intros n.
      generalize (is_conditional_expectation_nneg (rvabs f) ace H2); intros.
      apply almost_prob_space_sa_sub_lift in H13.
      generalize (almost_and prts H4 H13); intros.
      apply (almost_impl' _ H14); intros.
      apply all_almost; intros.
      destruct H15.
      unfold rvabs, Rbar_rvmult, rvmult, EventIndicator.
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

(*
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
    (forall (n:nat), is_finite (NonnegExpectation (fn n))) ->
    (forall (omega:Ts), is_lim_seq (fun n => fn n omega) (f omega)) ->
    (forall (omega:Ts), is_lim_seq (fun n => cen n omega) (ce omega)) ->
    (forall (n:nat), is_conditional_expectation dom2 (fn n) (cen n)) ->
    is_conditional_expectation dom2 f ce.
  Proof.
    intros fbound fle ffin limf limce iscen P decP saP.

    
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

    generalize (monotone_convergence (rvmult f (EventIndicator decP))
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
          apply Lim_seq_proper.
          intros n.
          specialize (iscen n _ decP saP).
          rewrite (Expectation_pos_pofrf _) in iscen.
          rewrite (Rbar_Expectation_pos_pofrf _) in iscen.
          invcs iscen.
          rewrite H0.
          rewrite NNExpectation_Rbar_NNExpectation.

          admit.
        - intros ??.
          unfold Rbar_rvmult, EventIndicator.
          match_destr.
          + repeat rewrite Rbar_mult_1_r.
            apply bounded.
      } 
    specialize (eqq1 ).

    - unfold Rbar_rvlim in HH.
    
  Qed.
*)
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
    Rbar_rvlim (fun n => conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))).

  (* if f has finite exp, we can discard the infinite points *)
  Definition FiniteNonNegConditionalExpectation (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {isfe : IsFiniteExpectation prts f}
             {nnf : NonnegativeFunction f} : Ts -> R :=
    rvlim (fun n => conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))).

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
    - intros.
      apply ex_lim_seq_incr.
      intros.
      rv_unfold.
      match_destr.
      + setoid_rewrite Rmult_1_r.
        apply H0.
        apply e.
      + setoid_rewrite Rmult_0_r.
        lra.
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
    replace (Finite 0) with (Lim_seq (fun _ => 0)) by apply Lim_seq_const.
    apply Lim_seq_le_loc.
    exists 0%nat.
    intros.
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
    rewrite Lim_seq_scal_r.
    generalize (rvlim_rvmin f); intros HH.
    unfold Rbar_rvlim in HH.
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
      generalize (monotone_convergence_Rbar
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
          - rewrite Lim_seq_mult.
            + now rewrite Lim_seq_const.
            + apply ex_lim_seq_incr.
              intros.
              apply gincr.
            + apply ex_lim_seq_const.
            + rewrite Lim_seq_const.
              unfold ex_Rbar_mult.
              match_destr.
          - setoid_rewrite Rmult_0_r.
            rewrite Lim_seq_const.
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
        erewrite Lim_seq_ext.
        2: {
          intros.
          rewrite <- H5.
          reflexivity.
        }
        rewrite (monotone_convergence_Rbar
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
        * intros.
          apply IsFiniteNonnegExpectation.
          apply IsFiniteExpectation_indicator; try typeclasses eauto.
          now apply sub.
      + intros n x.
        rv_unfold.
        match_destr.
        * do 2 rewrite Rmult_1_r.
          apply gincr.
        * lra.
      + intros.
        apply IsFiniteNonnegExpectation.
        apply IsFiniteExpectation_indicator; try typeclasses eauto.
        * now apply RandomVariable_sa_sub.
        * now apply sub.
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

  Definition ConditionalExpectation (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f} : Ts -> Rbar :=
    Rbar_rvminus (NonNegCondexp (pos_fun_part f))
                 (NonNegCondexp (neg_fun_part f)).

  Global Instance Condexp_rv (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f} :
    RandomVariable dom2 Rbar_borel_sa (ConditionalExpectation f).
  Proof.
    unfold ConditionalExpectation, Rbar_rvminus.
    apply Rbar_rvplus_rv.
    - typeclasses eauto.
    - typeclasses eauto.
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
        (saP:sa_sigma (SigmaAlgebra := dom2) P) :
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
        (saP:sa_sigma (SigmaAlgebra := dom2) P) :
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
  
        
  Lemma FiniteCondexp_Jensen (rv_X : Ts -> R) (phi : R -> R) (a b : nat -> R) 
        {rv : RandomVariable dom borel_sa rv_X}
        {rvphi : RandomVariable dom borel_sa (fun x => phi (rv_X x))}
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => phi (rv_X x))} :    
    (forall (x: R),
      is_sup_seq (fun n => (a n) * x + (b n)) (phi x)) ->
    almostR2 (prob_space_sa_sub prts sub) Rbar_le
      (fun x => phi ((FiniteConditionalExpectation rv_X) x))
      (FiniteConditionalExpectation (fun x => phi (rv_X x))).
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
    generalize (fun n => FiniteCondexp_scale (a n) rv_X); intros.
    generalize (fun n => FiniteCondexp_const (b n)); intros.
    generalize (fun n => FiniteCondexp_plus (rvscale (a n) rv_X) (const (b n))); intros.
    assert (forall n,
               almostR2 (prob_space_sa_sub prts sub) eq
                        (FiniteConditionalExpectation (rvplus (rvscale (a n) rv_X) (const (b n))))
                        (rvplus (rvscale (a n) (FiniteConditionalExpectation rv_X))
                                (const (b n)))).
    {
     intros.
     generalize (almost_and _ (H1 n) (H3 n)); intros.
     apply (almost_impl' _ H4).
     apply all_almost; intros.
     destruct H5.
     rewrite H6.
     unfold rvplus.
     rewrite H5.
     now rewrite H2.
    }
    clear H1 H2 H3.
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
    generalize (fun n => FiniteCondexp_ale _ _ (H1 n)); intros.
    clear H1.
    assert (forall (n:nat),
               almostR2 (prob_space_sa_sub prts sub) Rle
                        (rvplus (rvscale (a n) (FiniteConditionalExpectation rv_X)) (const (b n)))
                        (FiniteConditionalExpectation (fun x : Ts => phi (rv_X x)))).
    {
      intros.
      specialize (H4 n).
      specialize (H2 n).
      generalize (almost_and _ H4 H2); intros.
      apply (almost_impl' _ H1).
      apply all_almost; intros.
      destruct H3.
      now rewrite <- H3.
   }
    clear H2.
    assert (almost (prob_space_sa_sub prts sub) 
                   (fun x => forall n, 
                        ((rvplus (rvscale (a n) (FiniteConditionalExpectation rv_X)) (const (b n))) x)
                          <= (FiniteConditionalExpectation (fun x : Ts => phi (rv_X x))) x)).
    {
      apply almost_forall.
      intros.
      apply (H1 n).
    }
    assert (rv_eq
              (fun x : Ts => Finite (phi (FiniteConditionalExpectation rv_X x)))
              (fun x => Sup_seq (fun n => a n * (FiniteConditionalExpectation rv_X x) + b n))).
    {
      intro x.
      specialize (H (FiniteConditionalExpectation rv_X x)).
      apply is_sup_seq_unique in H.
      now rewrite H.
    }
     apply (almost_impl' _ H2).    
     apply all_almost.
     intros.
     rewrite H3.
     unfold rvplus, rvscale, const in H5.
     replace (Finite ( FiniteConditionalExpectation (fun x0 : Ts => phi (rv_X x0)) x)) with
         (Sup_seq (fun n => ( FiniteConditionalExpectation (fun x0 : Ts => phi (rv_X x0)) x))).
     - apply Sup_seq_le.
       intros.
       simpl.
       apply H5.
     - rewrite Rbar_sup_eq_lub.
       unfold Rbar_lub, proj1_sig.
       match_destr.
       destruct r.
       unfold Rbar_is_upper_bound in *.
       apply Rbar_le_antisym.
       + apply H7.
         intros.
         destruct H8.
         rewrite <- H8.
         apply Rbar_le_refl.
       + apply H6.
         now exists (0%nat).
   Qed.

  Lemma FiniteCondexp_Jensen_abs (rv_X : Ts -> R) 
        {rv : RandomVariable dom borel_sa rv_X}
        {isfe : IsFiniteExpectation prts rv_X} 
        {isfephi : IsFiniteExpectation prts (fun x => Rabs (rv_X x))} :   
    almostR2 (prob_space_sa_sub prts sub) Rle
             (rvabs (FiniteConditionalExpectation rv_X))
             (FiniteConditionalExpectation (rvabs rv_X)).
  Proof.
    pose (a := fun (n:nat) => if (Nat.eqb n 0%nat) then 1 else -1).
    pose (b := fun (n:nat) => 0).
    generalize (FiniteCondexp_Jensen rv_X Rabs a b); intros.
    cut_to H.
    - apply (almost_impl' _ H).
      apply all_almost.
      intros.
      unfold rvabs.
      apply H0.
    - intros.
      apply Rbar_is_lub_sup_seq.
      unfold Rbar_is_lub.
      unfold Rbar_is_upper_bound.
      split; intros.
      + destruct H0.
        rewrite H0.
        unfold a, b.
        rewrite Rplus_0_r.
        match_destr.
        * rewrite Rmult_1_l; simpl.
          apply Rle_abs.
        * replace (-1*x) with (-x) by lra; simpl.
          apply Rabs_maj2.
      + apply H0.
        unfold a, b.
        destruct (Rle_dec 0 x).
        * exists (0%nat); simpl.
          rewrite Rplus_0_r, Rmult_1_l.
          apply Rle_ge in r.
          now rewrite Rabs_right.
        * exists (1%nat); simpl.
          replace (-1 * x + 0) with (-x) by lra.
          rewrite Rabs_left; trivial.
          lra.
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

Section cond_exp_props.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Existing Instance RandomVariable_sa_sub.
  Existing Instance conditional_expectation_L2fun_rv.

  (* prove ext theorems for the conditional expectations stuff) *)

  Let nneg2 : nonnegreal := bignneg 2 big2.
  Canonical nneg2.

  Lemma LpRRVnorm_const {p} c : p <> 0 -> LpRRVnorm (p:=p) prts (LpRRVconst prts c) = Rabs c.
  Proof.
    intros.
    unfold LpRRVnorm; simpl.
    rv_unfold.
    generalize (FiniteExpectation_const prts (power (Rabs c) p))
    ; intros HH.
    unfold const in HH.
    erewrite FiniteExpectation_pf_irrel.
    rewrite HH.
    apply inv_power_cancel; trivial.
    apply Rabs_pos.
  Qed.
  
  Lemma LpRRVnorm0 {p} : p <> 0 -> LpRRVnorm (p:=p) prts (LpRRVzero prts) = 0.
  Proof.
    intros.
    unfold LpRRVzero.
    rewrite LpRRVnorm_const; trivial.
    now rewrite Rabs_R0.
  Qed.

  Lemma rvmin_INR_le (f : Ts -> R) :
    forall (n:nat),
      rv_le (rvmin f (const (INR n))) (rvmin f (const (INR (S n)))).
  Proof.
    intros n x.
    unfold rvmin, const.
    apply Rle_min_compat_l.
    apply le_INR.
    lia.
  Qed.

  Instance NonNeg_rvmin (f g : Ts -> R)
           {nnf: NonnegativeFunction f}
           {nng: NonnegativeFunction g} :
    NonnegativeFunction (rvmin f g).
  Proof.
    unfold NonnegativeFunction in *.
    unfold rvmin.
    intros.
    now apply Rmin_glb.
  Qed.

  Instance NonNeg_INR (n : nat) :
    @NonnegativeFunction Ts (const (INR n)).
  Proof.
    unfold NonnegativeFunction.
    intro.
    apply pos_INR.
  Qed.


  Lemma Rbar_mult_pos_div_pos (x : Rbar) (c : posreal) :
    x = Rbar_mult_pos (Rbar_div_pos x c) c.
  Proof.
    destruct x.
    - simpl.
      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite Rinv_l.
      + now rewrite Rmult_1_r.
      + apply Rgt_not_eq.
        apply cond_pos.
    - now simpl.
    - now simpl.
  Qed.

  Lemma  Rbar_le_mult_pos_div_pos (x r : Rbar) (c : posreal) :
    Rbar_le (Rbar_mult_pos x c) r <-> Rbar_le x (Rbar_div_pos r c).
  Proof.
    generalize (cond_pos c); intros.
    assert (pos c <> 0) by now apply Rgt_not_eq.
    split; intros.
    - rewrite Rbar_mult_pos_le with (z := c).
      now rewrite <- Rbar_mult_pos_div_pos.
    - rewrite Rbar_mult_pos_le with (z := c) in H1.
      now rewrite <- Rbar_mult_pos_div_pos in H1.
  Qed.

  Instance Rbar_mult_pos_measurable (domm :SigmaAlgebra Ts) (f : Ts -> Rbar) (c:posreal) :
    RbarMeasurable (dom := domm) f ->
    RbarMeasurable (dom := domm) (fun omega => Rbar_mult_pos (f omega) c).
  Proof.
    intros ? r.
    assert (pre_event_equiv (fun omega : Ts => Rbar_le (Rbar_mult_pos (f omega) c) r)
                            (fun omega : Ts => Rbar_le (f omega) (Rbar_div_pos r c))).
    - red; intros.
      apply Rbar_le_mult_pos_div_pos.
    - rewrite H0.
      apply H.
  Qed.

  Lemma pos_fun_part_scale_pos_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (pos_fun_part (rvscale c f) x)) (rvscale c (fun x : Ts => pos_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    now rewrite (scale_Rmax0 (mkposreal c H)); simpl.
  Qed.

  Lemma neg_fun_part_scale_pos_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (neg_fun_part (rvscale c f) x)) (rvscale c (fun x : Ts => neg_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    rewrite Ropp_mult_distr_r.
    now rewrite (scale_Rmax0 (mkposreal c H)); simpl.
  Qed.

  Lemma pos_fun_part_scale_neg_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (pos_fun_part (rvscale (- c) f) x)) (rvscale c (fun x : Ts => neg_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    rewrite <- (scale_Rmax0 (mkposreal c H)); simpl.
    f_equal; lra.
  Qed.

  Lemma neg_fun_part_scale_neg_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (neg_fun_part (rvscale (- c) f) x)) (rvscale c (fun x : Ts => pos_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    rewrite Ropp_mult_distr_r.
    rewrite <- (scale_Rmax0 (mkposreal c H)); simpl.
    f_equal; lra.
  Qed.

  Lemma Rbar_rvlim_plus_min (f1 f2 : Ts -> R) :
    rv_eq
      (Rbar_rvlim
         (fun n : nat =>
            rvplus (rvmin f1 (const (INR n))) 
                   (rvmin f2 (const (INR n)))))
      (Rbar_rvlim
         (fun n : nat =>
            rvmin (rvplus f1 f2) (const (INR n)))). 
  Proof.
    intro x.
    unfold Rbar_rvlim, rvmin, rvplus, const.
    rewrite Lim_seq_plus.
    - do 3 rewrite Lim_seq_min.
      now simpl.
    - apply ex_lim_seq_incr.
      intros.
      apply Rle_min_compat_l.
      apply le_INR.
      lia.
    - apply ex_lim_seq_incr.
      intros.
      apply Rle_min_compat_l.
      apply le_INR.
      lia.
    - do 2 rewrite Lim_seq_min.
      now simpl.
  Qed.

  Instance almostR2_eq_Rbar_plus_proper
          : Proper (almostR2 prts eq ==> almostR2 prts eq  ==> almostR2 prts eq) Rbar_rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (event_inter Px Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold Rbar_rvplus.
      now rewrite eq_onx, eq_ony.
  Qed.

  Instance almostR2_eq_Rbar_mult_proper
          : Proper (almostR2 prts eq ==> almostR2 prts eq  ==> almostR2 prts eq) Rbar_rvmult.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (event_inter Px Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold Rbar_rvmult.
      now rewrite eq_onx, eq_ony.
  Qed.

End cond_exp_props.
