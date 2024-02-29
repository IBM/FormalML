Require Import QArith.
Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Export ConditionalExpectation.
Require Import RbarExpectation.

Require Import Event.
Require Import Almost DVector.
Require Import utils.Utils.
Require Import List.
Require Import PushNeg.
Require Import Reals.
Require Import Coquelicot.Rbar Coquelicot.Lim_seq.

Require Import Martingale.

Set Bullet Behavior "Strict Subproofs". 

Section stopped_process.

  Local Open Scope R.
  Local Existing Instance Rge_pre.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rle_pre.
  
  Context {Ts:Type}.

    Definition lift1_min (x:nat) (y : option nat)
      := match y with
         | None => x
         | Some b => min x b
         end.
    
  Lemma lift1_lift2_min (x:nat) (y : option nat) :
    lift2_min (Some x) y = Some (lift1_min x y).
  Proof.
    destruct y; reflexivity.
  Qed.
  
  Definition process_stopped_at (Y : nat -> Ts -> R) (T:Ts -> option nat) (n:nat) (x : Ts) : R
    := Y (lift1_min n (T x)) x.

  Definition process_stopped_at_alt (Y : nat -> Ts -> R) (T:Ts -> option nat) (n:nat) : Ts -> R
    := match n with
       | 0%nat => Y 0%nat
       | S n =>
           rvplus
             (rvsum (fun t => rvmult
                             (Y t)
                             (EventIndicator (stopping_time_pre_event_dec T t))) n%nat)
             (rvmult
                (Y (S n))
                (EventIndicator
                   (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n%nat)))))
       end.
       
  Lemma process_stopped_at_as_alt (Y : nat -> Ts -> R) (T:Ts -> option nat) :
    forall n, rv_eq (process_stopped_at Y T n) (process_stopped_at_alt Y T n).
  Proof.
    intros n ts.
    unfold process_stopped_at_alt, process_stopped_at.
    unfold lift1_min.
    rv_unfold; unfold rvsum.
    destruct n; match_option.
    - destruct (Min.min_dec (S n) n0).
      + assert (nle: (S n <= n0)%nat) by lia.
        rewrite e.
        rewrite (@Hierarchy.sum_n_ext_loc Hierarchy.R_AbelianGroup _ (fun _ => 0)).
        * rewrite sum_n_zero.
          field_simplify.
          match_destr; try lra.
          elim n1.
          unfold stopping_time_pre_event_alt, pre_event_complement.
          match_option; auto 2.
          assert (n2 = n0) by congruence.
          lia.
        * intros; match_destr; try lra.
          unfold stopping_time_pre_event in *.
          assert (n0 = n1) by congruence.
          lia.
      + rewrite e.
        assert (nle: (n0 <= S n)%nat) by lia.
        match_destr.
        * red in p.
          unfold stopping_time_pre_event_alt in p.
          rewrite eqq in p.
          assert (n0 = S n) by lia.
          subst.
          rewrite (@Hierarchy.sum_n_ext_loc Hierarchy.R_AbelianGroup _ (fun _ => 0)).
          -- rewrite sum_n_zero.
             lra.
          -- intros.
             match_destr; try lra.
             unfold stopping_time_pre_event in *.
             congruence.
        * field_simplify.
          unfold stopping_time_pre_event_alt, pre_event_complement in *.
          match_option_in n1; [| tauto].
          assert (n0 = n2) by congruence.
          subst.
          assert (n2 <= n)%nat by tauto.
          clear nle n1 eqq0 e.
          {
            induction n; simpl.
            - rewrite Hierarchy.sum_O.
              assert (n2 = 0)%nat by lia.
              subst.
              match_destr; try lra.
              elim n.
              now red.
            - rewrite Hierarchy.sum_Sn.
              destruct (le_lt_dec n2 n).
              + specialize (IHn l).
                rewrite <- IHn.
                unfold Hierarchy.plus; simpl.
                match_destr; try lra.
                unfold stopping_time_pre_event in s.
                assert (n2 = S n) by congruence.
                lia.
              + assert (n2 = S n) by lia.
                subst.
                rewrite (@Hierarchy.sum_n_ext_loc Hierarchy.R_AbelianGroup _ (fun _ => 0)).
                -- rewrite sum_n_zero.
                   unfold Hierarchy.plus; simpl.
                   match_destr; try lra.
                   unfold stopping_time_pre_event in n0; congruence.
                -- intros.
                   match_destr; try lra.
                   unfold stopping_time_pre_event in *.
                   assert (S n = n0) by congruence.
                   lia.
          } 
    - rewrite (@Hierarchy.sum_n_ext Hierarchy.R_AbelianGroup _ (fun _ => 0)).
      + rewrite sum_n_zero.
        field_simplify.
        match_destr; try lra.
        elim n0.
        unfold stopping_time_pre_event_alt, pre_event_complement.
        match_option; auto 2.
        congruence.
      + intros; match_destr; try lra.
        unfold stopping_time_pre_event in *; congruence.
  Qed.

  Context 
    {dom: SigmaAlgebra Ts}
    (prts: ProbSpace dom).

  Section process_stopped_at_props.
    
    Context (Y : nat -> Ts -> R) (F : nat -> SigmaAlgebra Ts)
            {filt:IsFiltration F}
            {sub:IsSubAlgebras dom F}
            (T:Ts -> option nat)
            {is_stop:IsStoppingTime T F}.

    Global Instance process_stopped_at_rv
           {rv:forall n, RandomVariable dom borel_sa (Y n)} :
      forall n, RandomVariable dom borel_sa (process_stopped_at Y T n).
    Proof.
      intros.
      cut (RandomVariable dom borel_sa (process_stopped_at_alt Y T n))
      ; [apply RandomVariable_proper; try reflexivity; apply process_stopped_at_as_alt; try reflexivity |].
      destruct n; simpl; trivial.
      apply rvplus_rv.
      - apply rvsum_rv; intros.
        apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        eapply sub.
        apply is_stop.
      - apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        apply sa_complement.
        eapply sub.
        apply is_stopping_time_as_alt; trivial.
    Qed.

    Global Instance process_stopped_at_adapted 
           {adapt:IsAdapted borel_sa Y F} :
      IsAdapted borel_sa (process_stopped_at Y T) F.
    Proof.
      intros n.
      cut (RandomVariable (F n) borel_sa (process_stopped_at_alt Y T n))
      ; [apply RandomVariable_proper; try reflexivity; apply process_stopped_at_as_alt; try reflexivity |].
      destruct n; simpl; trivial.
      apply rvplus_rv.
      - apply rvsum_rv_loc; intros.
        apply rvmult_rv; trivial.
        + cut (RandomVariable (F m) borel_sa (Y m)).
          { eapply (RandomVariable_proper_le (F m) _); try reflexivity.
            apply is_filtration_le; trivial; lia.
          } 
          apply adapt.
        + apply EventIndicator_pre_rv.
          generalize (is_stop m).
          apply is_filtration_le; trivial; lia.
      - apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        apply sa_complement.
        apply is_stopping_time_as_alt in is_stop; trivial.
        generalize (is_stop n).
        apply is_filtration_le; trivial; lia.
    Qed.

    Global Instance process_stopped_at_isfe
           {rv:forall n, RandomVariable dom borel_sa (Y n)}
           {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      forall n, IsFiniteExpectation prts (process_stopped_at Y T n).
    Proof.
      intros n.
      eapply IsFiniteExpectation_proper; try apply process_stopped_at_as_alt.
      unfold process_stopped_at_alt.
      destruct n; trivial.
      apply IsFiniteExpectation_plus.
      - apply rvsum_rv_loc; intros.
        apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        eapply sub.
        apply is_stop.
      - apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        apply sa_complement.
        apply is_stopping_time_as_alt in is_stop; trivial.
        eapply sub.
        apply is_stop.
      - apply IsFiniteExpectation_sum; intros.
        + apply rvmult_rv; trivial.
          apply EventIndicator_pre_rv.
          eapply sub.
          apply is_stop.
        + apply IsFiniteExpectation_indicator; trivial.
          eapply sub.
          apply is_stop.
      - apply IsFiniteExpectation_indicator; trivial.
        apply sa_complement.
        apply is_stopping_time_as_alt in is_stop; trivial.
        eapply sub.
        apply is_stop.
    Qed.

    Instance process_stopped_at_alt_rv
             {rv:forall n, RandomVariable dom borel_sa (Y n)} :
      forall n, RandomVariable dom borel_sa (process_stopped_at_alt Y T n).
    Proof.
      intros.
      generalize (process_stopped_at_rv n).
      apply RandomVariable_proper; try reflexivity.
      now rewrite process_stopped_at_as_alt.
    Qed.

    Instance process_stopped_at_alt_isfe
           {rv:forall n, RandomVariable dom borel_sa (Y n)}
           {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      forall n, IsFiniteExpectation prts (process_stopped_at_alt Y T n).
    Proof.
      intros.
      generalize (process_stopped_at_isfe n).
      apply IsFiniteExpectation_proper.
      now rewrite process_stopped_at_as_alt.
    Qed.

    Instance process_stopped_at_alt_adapted 
           {adapt:IsAdapted borel_sa Y F} :
      IsAdapted borel_sa (process_stopped_at_alt Y T) F.
    Proof.
      intros n.
      generalize (process_stopped_at_adapted n).
      apply RandomVariable_proper; try reflexivity.
      now rewrite process_stopped_at_as_alt.
    Qed.

    Lemma process_stopped_at_alt_diff1_eq n :
      rv_eq (rvminus
               (process_stopped_at_alt Y T (S n))
               (process_stopped_at_alt Y T n))
            (rvmult
               (rvminus
                  (Y (S n))
                  (Y n))
               (EventIndicator (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n%nat))))).
    Proof.
      intros ts.
      unfold process_stopped_at_alt.
      rv_unfold; unfold rvsum.
      destruct n.
      - rewrite Hierarchy.sum_O.
        repeat match_destr
        ; unfold stopping_time_pre_event, stopping_time_pre_event_alt, pre_event_complement in *
        ; try rewrite s in *; try lia; try lra.
        match_option_in n0; try tauto.
        rewrite eqq in n.
        assert (n1 <> 0%nat) by congruence.
        lia.
      - rewrite Hierarchy.sum_Sn.
        unfold Hierarchy.plus; simpl.
        field_simplify.
        repeat match_destr
        ; unfold stopping_time_pre_event, stopping_time_pre_event_alt, pre_event_complement in *
        ; try rewrite s in *; try lia; try lra.
        + match_destr_in p; try tauto.
          assert (n2 <> S n) by congruence.
          lia.
        + match_destr_in p; try tauto.
          assert (n2 <> S n) by congruence.
          lia.
    Qed.        

    Instance process_stopped_at_alt_diff1_rv
             {rv:forall n, RandomVariable dom borel_sa (Y n)} n
:
      RandomVariable dom borel_sa
                     (rvmult (rvminus (Y (S n)) (Y n))
                             (EventIndicator
                                (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n))))).
    Proof.
      apply rvmult_rv.
      - typeclasses eauto.
      - apply EventIndicator_pre_rv.
        apply sa_complement.
        apply is_stopping_time_as_alt in is_stop; trivial.
        eapply sub.
        apply is_stop.
    Qed.

    Instance process_stopped_at_alt_diff1_isfe n
             {rv:forall n, RandomVariable dom borel_sa (Y n)}
             {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      IsFiniteExpectation prts
            (rvmult (rvminus (Y (S n)) (Y n))
               (EventIndicator
                  (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n))))).
    Proof.
      apply IsFiniteExpectation_indicator; try typeclasses eauto.
      apply sa_complement.
      apply is_stopping_time_as_alt in is_stop; trivial.
      eapply sub.
      apply is_stop.
    Qed.

    Lemma process_stopped_at_sub_martingale
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
      IsMartingale prts Rle (process_stopped_at Y T) F.
    Proof.
      cut (IsMartingale prts Rle (process_stopped_at_alt Y T) F).
      {
        apply is_martingale_eq_proper; try reflexivity.
        intros.
        apply all_almost; intros.
        now rewrite process_stopped_at_as_alt.
      } 
      intros n.
      generalize (process_stopped_at_alt_diff1_eq n); intros eqq1.
      generalize (FiniteConditionalExpectation_ext
                    prts (sub n)
                    _ _
                    eqq1)
      ; intros eqq2; clear eqq1.

      generalize (FiniteCondexp_minus prts (sub n)  (process_stopped_at_alt Y T (S n)) (process_stopped_at_alt Y T n)); intros HH.
      apply almostR2_prob_space_sa_sub_lift in HH; revert HH.
      apply almost_impl.
      generalize (FiniteCondexp_minus prts (sub n)  (Y (S n)) (Y n)); intros HH.
      apply almostR2_prob_space_sa_sub_lift in HH; revert HH.
      apply almost_impl.

      assert (rv':RandomVariable (F n) borel_sa
                                 (EventIndicator (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n))))).
      {
        apply EventIndicator_pre_rv.
        apply sa_complement.
        apply is_stopping_time_as_alt; trivial.
      } 

      assert (rvm':RandomVariable dom borel_sa
                                  (rvmult
                                     (EventIndicator
                                        (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n))))
                                     (rvminus (Y (S n)) (Y n)))).
      {
        generalize (process_stopped_at_alt_diff1_rv n).
        apply RandomVariable_proper; try reflexivity.
        apply rvmult_comm.
      }

      generalize (FiniteCondexp_factor_out prts (sub n)
                                             (rvminus (Y (S n)) (Y n))
                                             (EventIndicator
                                                (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n))))); intros HH.
      apply almostR2_prob_space_sa_sub_lift in HH; revert HH.
      apply almost_impl.
      generalize (mart n).
      apply almost_impl.
      apply all_almost; intros ts martle eqq3 eqq4 eqq5.
      rewrite eqq2, eqq3 in eqq5.
      unfold rvmult in eqq5.
      rewrite eqq4 in eqq5.
      clear eqq2 eqq3 eqq4.
      rv_unfold.

      assert (rvYn:RandomVariable (F n) borel_sa (Y n))
        by apply adapt.
      rewrite (FiniteCondexp_id _ _ (Y n)) in eqq5.
      assert (rvYn':RandomVariable (F n) borel_sa (process_stopped_at_alt Y T n))
        by apply process_stopped_at_alt_adapted.
      rewrite (FiniteCondexp_id _ _ (process_stopped_at_alt Y T n)) in eqq5.
      rewrite (Rplus_comm (FiniteConditionalExpectation prts (sub n) (process_stopped_at_alt Y T (S n)) ts)) in eqq5.
      apply Radd_minus in eqq5.
      rewrite <- eqq5.
      match_destr; lra.
    Qed.

    Lemma process_stopped_at_opp n :
      rv_eq (rvopp (process_stopped_at Y T n))
            (process_stopped_at (fun n => rvopp (Y n)) T n).
    Proof.
      reflexivity.
    Qed.
            
  End process_stopped_at_props.

  Section process_stopped_at_props_ext.

      Context (Y : nat -> Ts -> R) (F : nat -> SigmaAlgebra Ts)
            {filt:IsFiltration F}
            {sub:IsSubAlgebras dom F}
            (T:Ts -> option nat)
            {is_stop:IsStoppingTime T F}.

  Lemma process_stopped_at_super_martingale
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rge Y F} :
      IsMartingale prts Rge (process_stopped_at Y T) F.
    Proof.
      apply is_sub_martingale_neg.
      cut (IsMartingale prts Rle (process_stopped_at (fun n => rvopp (Y n)) T) F).
      {
        apply is_martingale_eq_proper; try reflexivity.
      }
      eapply process_stopped_at_sub_martingale.
      apply is_super_martingale_neg.
      revert mart.
      apply is_martingale_eq_proper; try reflexivity.
      intros; apply all_almost; intros.
      rv_unfold; lra.
    Qed.

    Lemma process_stopped_at_martingale
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts eq Y F} :
      IsMartingale prts eq (process_stopped_at Y T) F.
    Proof.
      apply is_martingale_sub_super_eq.
      - apply process_stopped_at_sub_martingale.
        now apply is_martingale_eq_any.
      - eapply is_martingale_eq_any in mart.
        apply process_stopped_at_super_martingale.
    Qed.

    Lemma process_stopped_at_0 :
      rv_eq ((process_stopped_at Y T) 0%nat)
            (Y 0).
     Proof.
       intros x.
       unfold process_stopped_at, lift1_min.
       match_destr.
     Qed.
       
     Lemma expectation_process_stopped_at_0 
           {rv:forall n, RandomVariable dom borel_sa (Y n)}
           {isfe:forall n, IsFiniteExpectation prts (Y n)} :
       FiniteExpectation prts ((process_stopped_at Y T) 0%nat) = FiniteExpectation prts (Y 0).
     Proof.
       apply FiniteExpectation_ext.
       apply process_stopped_at_0.
     Qed.
     
     Lemma process_stopped_at_sub_martingale_expectation_0
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
      forall n, FiniteExpectation prts ((process_stopped_at Y T) n) >= FiniteExpectation prts (Y 0).
    Proof.
      intros.
      rewrite <- expectation_process_stopped_at_0.
      apply Rle_ge.
      apply (@is_sub_martingale_expectation _ _ _ _ F
               (process_stopped_at_rv Y F T)
               _ 
               (process_stopped_at_adapted Y F T) 
               filt
               sub); try lia.
      now apply process_stopped_at_sub_martingale.
    Qed.

     Lemma process_stopped_at_super_martingale_expectation_0
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rge Y F} :
       forall n, FiniteExpectation prts ((process_stopped_at Y T) n) <= FiniteExpectation prts (Y 0).
     Proof.
      intros.
      rewrite <- expectation_process_stopped_at_0.
      apply Rge_le.
      apply (@is_super_martingale_expectation _ _ _ _
               F
               (process_stopped_at_rv Y F T)
               _ 
               (process_stopped_at_adapted Y F T) 
               filt
             sub); try lia.
      now apply process_stopped_at_super_martingale.
    Qed.

    Lemma process_stopped_at_martingale_expectation_0
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts eq Y F} :
      forall n, FiniteExpectation prts ((process_stopped_at Y T) n) = FiniteExpectation prts (Y 0).
    Proof.
      intros.
      rewrite <- expectation_process_stopped_at_0.
      apply (@is_martingale_expectation _ _ _ _
               F
               (process_stopped_at_rv Y F T)
               _
               (process_stopped_at_adapted Y F T) 
               filt sub).
      apply process_stopped_at_martingale.
    Qed.

    Lemma process_stopped_at_martingale_expectation
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts eq Y F} :
      forall s t, FiniteExpectation prts ((process_stopped_at Y T) s) = FiniteExpectation prts (Y t).
    Proof.
      intros.
      rewrite process_stopped_at_martingale_expectation_0.
      now apply (@is_martingale_expectation _ _ _ _
                   F
                   rv _
                   adapt
                   filt
                 sub).
    Qed.

  End process_stopped_at_props_ext.

  Section process_under_props.

    Context (Y : nat -> Ts -> R) (F : nat -> SigmaAlgebra Ts)
            {filt:IsFiltration F}
            {sub:IsSubAlgebras dom F}
            (T:Ts -> option nat)
            {is_stop:IsStoppingTime T F}.

    Definition process_under (Y : nat -> Ts -> R) (T:Ts -> option nat) (x : Ts) : R
      := match T x with
         | None => 0
         | Some n => Y n x
         end.

    Lemma process_stopped_at_fin_limit :
      forall ts, T ts <> None -> is_lim_seq (fun n => process_stopped_at Y T n ts) (process_under Y T ts).
    Proof.
      intros.
      unfold process_stopped_at, process_under.
      case_eq (T ts); [intros | congruence].
      simpl.
      apply (is_lim_seq_incr_n _ n).
      apply (is_lim_seq_ext (fun n0 : nat => Y n ts)).
      - intros.
        now rewrite min_r by lia.
      - apply is_lim_seq_const.
    Qed.

    Lemma process_stopped_at_almost_fin_limit :
      almost prts (fun ts => T ts <> None) ->
      almost prts (fun ts => is_lim_seq (fun n => process_stopped_at Y T n ts) (process_under Y T ts)).
    Proof.
      apply almost_impl.
      apply all_almost; intros ??.
      now apply process_stopped_at_fin_limit.
    Qed.

    Global Instance process_under_rv
             {rv:forall n, RandomVariable dom borel_sa (Y n)} :
      RandomVariable dom borel_sa (process_under Y T).
    Proof.
      unfold process_under.
      apply measurable_rv; intros ?.
      apply (sa_proper
               _
               (pre_event_union
                  (fun omega => T omega = None /\ 0 <= r)
                  (fun omega => exists n, stopping_time_pre_event T n omega /\ Y n omega <= r)
               )
            ).
      - intros ?.
        unfold pre_event_union.
        split; intros.
        + destruct H.
          * destruct H.
            now rewrite H.
          * destruct H as [? [??]].
            now rewrite H.
        + match_option_in H; try tauto.
          right.
          eauto.
      - apply sa_union.
        + apply sa_inter.
          * apply (sa_proper
                     _
                     (pre_event_complement (fun omega => exists n, T omega = Some n))
                  ).
            -- intros ?.
               unfold pre_event_complement.
               split; intros ?.
               ++ destruct (T x); trivial.
                  elim H; eauto.
               ++ rewrite H.
                  intros [??]; congruence.
            -- apply sa_complement.
               apply sa_countable_union; intros.
               eapply sub.
               apply is_stop.
          * apply sa_sigma_const.
            lra.
        + apply sa_countable_union; intros.
          apply sa_inter.
          * eapply sub.
            apply is_stop.
          * now apply rv_measurable.
    Qed.

  End process_under_props.

  Section opt_stop_thm.

    Context (Y : nat -> Ts -> R) (F : nat -> SigmaAlgebra Ts)
            {filt:IsFiltration F}
            {sub:IsSubAlgebras dom F}
            (T:Ts -> option nat)
            {is_stop:IsStoppingTime T F}.

    Section variant_a.

      Context (N:nat)
              (Nbound:almost prts (fun ts => match T ts with
                                          | Some k => (k <= N)%nat
                                          | None => False
                                          end)).
      
    Instance optional_stopping_time_a_isfe
             {rv:forall n, RandomVariable dom borel_sa (Y n)}
             {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      IsFiniteExpectation prts (process_under Y T).
    Proof.
      intros.
      apply (IsFiniteExpectation_abs_bound_almost _ _
                                                  (rvsum (fun k => rvabs (Y k)) N)).
      - revert Nbound.
        apply almost_impl.
        apply all_almost; intros ??.
        unfold process_under, rvsum; rv_unfold.
        match_destr; try tauto.
        induction N.
        + rewrite Hierarchy.sum_O.
          now replace n with 0%nat by lia.
        + rewrite Hierarchy.sum_Sn.
          unfold Hierarchy.plus; simpl.
          destruct (Nat.eq_dec n (S n0)).
          * subst.
            assert (0 <= @Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n0 : nat => Rabs (Y n0 x)) n0).
            {
              apply sum_n_nneg; intros.
              apply Rabs_pos.
            }
            lra.
          * cut_to IHn0; try lia.
            assert (0 <= Rabs (Y (S n0) x)) by apply Rabs_pos.
            lra.
      - apply IsFiniteExpectation_sum; intros.
        + typeclasses eauto.
        + now apply IsFiniteExpectation_abs.
    Qed.

    Lemma optional_stopping_time_a_stopped_eq :
      almostR2 prts eq (process_stopped_at Y T N) (process_under Y T).
    Proof.
      revert Nbound.
      apply almost_impl.
      apply all_almost; intros ??.
      unfold process_stopped_at, lift1_min, process_under.
      match_destr; try tauto.
      now rewrite min_r.
    Qed.

    Lemma optional_stopping_time_a
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts eq Y F} :
          FiniteExpectation prts (Y 0%nat) = FiniteExpectation prts (process_under Y T).
    Proof.
      rewrite <- (process_stopped_at_martingale_expectation_0 Y F T N).
      apply FiniteExpectation_proper_almostR2.
      - typeclasses eauto.
      - typeclasses eauto.
      - apply optional_stopping_time_a_stopped_eq.
    Qed.
    
    Lemma optional_stopping_time_sub_a
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
      FiniteExpectation prts (process_under Y T) >= FiniteExpectation prts (Y 0%nat).
    Proof.
      rewrite <- (process_stopped_at_sub_martingale_expectation_0 Y F T N).
      apply Rle_ge.
      apply FiniteExpectation_ale.
      - typeclasses eauto.
      - typeclasses eauto.
      - generalize optional_stopping_time_a_stopped_eq.
        apply almostR2_subrelation.
        intros ???; lra.
    Qed.

    Lemma optional_stopping_time_super_a
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rge Y F} :
      FiniteExpectation prts (process_under Y T) <= FiniteExpectation prts (Y 0%nat).
    Proof.
      rewrite <- (process_stopped_at_super_martingale_expectation_0 Y F T N).
      apply FiniteExpectation_ale.
      - typeclasses eauto.
      - typeclasses eauto.
      - generalize optional_stopping_time_a_stopped_eq; intros HH.
        symmetry in HH.
        revert HH.
        apply almostR2_subrelation.
        intros ???; lra.
    Qed.

    End variant_a.
    
    Section variant_b.

      Context (Tfin:almost prts (fun ts => T ts <> None))
              (K:R)
              (Kbound: forall n, almost prts (fun ω => Rabs (Y n ω) < K)).

      Lemma Kbound_stopped :
        forall n : nat, almostR2 prts Rle (rvabs (process_stopped_at Y T n)) (const K).
      Proof.
        apply almost_forall in Kbound.
        intros.
        revert Kbound.
        apply almost_impl.
        apply all_almost; intros ??.
        unfold process_stopped_at.
        unfold const, rvabs.
        red in H.
        left.
        apply H.
      Qed.

      Instance optional_stopping_time_b_isfe
               {rv:forall n, RandomVariable dom borel_sa (Y n)}
               {isfe:forall n, IsFiniteExpectation prts (Y n)} :
        IsFiniteExpectation prts (process_under Y T).
      Proof.
        apply (Dominated_convergence1_almost prts (process_stopped_at Y T) _ (const K)).
        - typeclasses eauto.
        - apply Kbound_stopped.
        - now apply process_stopped_at_almost_fin_limit.
      Qed.

      (* this should replace the existing rvlim *)
      Global Instance rvlim_rv' (f: nat -> Ts -> R)
             {rv : forall n, RandomVariable dom borel_sa (f n)} :
        RandomVariable dom borel_sa (rvlim f).
      Proof.
        intros.
        unfold rvlim.
        apply Rbar_real_rv.
        generalize (Rbar_rvlim_rv f).
        apply RandomVariable_proper; try reflexivity.
        intros ?.
        now rewrite <- Elim_seq_fin.
      Qed.

      Instance optional_stopping_time_b_isfe'
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        Rbar_IsFiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
      Proof.
        generalize (process_stopped_at_almost_fin_limit Y T Tfin)
        ; intros HH.
        generalize Kbound_stopped; intros Kbound_stopped.

        cut (Rbar_IsFiniteExpectation
               prts
               (process_under Y T)).
        {
          intros HH2.
          eapply Rbar_IsFiniteExpectation_proper_almostR2; try eapply HH2.
          - typeclasses eauto.
          - typeclasses eauto.
          - revert HH.
            apply almost_impl.
            apply all_almost; intros ??.
            unfold Rbar_rvlim.
            apply is_lim_seq_unique in H.
            rewrite Elim_seq_fin.
            congruence.
        }
        apply IsFiniteExpectation_Rbar.
        apply optional_stopping_time_b_isfe.
      Qed.
        
      Lemma optional_stopping_time_b_eq
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        FiniteExpectation prts (process_under Y T) =
          Rbar_FiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
      Proof.
        generalize (process_stopped_at_almost_fin_limit Y T Tfin)
        ; intros HH.
        rewrite <- FinExp_Rbar_FinExp; try typeclasses eauto.
        apply Rbar_FiniteExpectation_proper_almostR2.
        - typeclasses eauto.
        - apply Rbar_rvlim_rv. typeclasses eauto.
        - unfold almostR2, Rbar_rvlim.
          revert HH.
          apply almost_impl, all_almost.
          unfold impl; intros.
          apply is_lim_seq_unique in H.
          rewrite Elim_seq_fin.
          now rewrite H.
      Qed.

      Lemma optional_stopping_time_b_helper
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
      is_lim_seq
        (fun n : nat => Rbar_FiniteExpectation prts (fun x : Ts => process_stopped_at Y T n x) (isfe:= (IsFiniteExpectation_Rbar prts (fun x : Ts => process_stopped_at Y T n x)
                                                      (process_stopped_at_isfe Y F T n))))
        (Rbar_FiniteExpectation prts
                                (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x))).
      Proof.
        generalize (process_stopped_at_almost_fin_limit Y T Tfin)
        ; intros HH.
        generalize Kbound_stopped; intros Kbound_stopped.
        apply (Dominated_convergence_almost prts (process_stopped_at Y T)
                                                 (Rbar_rvlim (process_stopped_at Y T)) (const K)).
        - apply Rbar_IsFiniteExpectation_const.
        - intros.
          unfold almostR2.
          specialize (Kbound_stopped n).
          revert Kbound_stopped.
          apply almost_impl, all_almost.
          unfold impl; intros; simpl.
          now unfold rvabs in H.
        - revert HH.
          apply almost_impl, all_almost.
          unfold impl; intros.
          unfold Rbar_rvlim.
          apply ELim_seq_correct.
          rewrite ex_Elim_seq_fin.
          unfold ex_lim_seq.
          now exists (process_under Y T x).
      Qed.

      Lemma optional_stopping_time_b_helper'
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        Lim_seq 
        (fun n : nat => Rbar_FiniteExpectation prts (fun x : Ts => process_stopped_at Y T n x) (isfe:= (IsFiniteExpectation_Rbar prts (fun x : Ts => process_stopped_at Y T n x)
                                                      (process_stopped_at_isfe Y F T n)))) = 
        Finite (Rbar_FiniteExpectation prts
                                (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x))).
      Proof.
        apply is_lim_seq_unique.
        apply optional_stopping_time_b_helper.
      Qed.

      Lemma optional_stopping_time_b
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts eq Y F} :
         FiniteExpectation prts (process_under Y T) = FiniteExpectation prts (Y 0%nat).
      Proof.        
        rewrite optional_stopping_time_b_eq.
        rewrite <- Rbar_finite_eq, <- optional_stopping_time_b_helper'.
        rewrite <- (Lim_seq_const (FiniteExpectation prts (Y 0))).
        apply Lim_seq_ext; intros.
        rewrite FinExp_Rbar_FinExp; try typeclasses eauto.
        now rewrite process_stopped_at_martingale_expectation_0 with (adapt := adapt).
      Qed.

      Lemma optional_stopping_time_sub_b
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
        FiniteExpectation prts (process_under Y T) >= FiniteExpectation prts (Y 0%nat).
      Proof.
        rewrite optional_stopping_time_b_eq. 
        apply Rle_ge.
        cut (Rbar_ge (Rbar_FiniteExpectation prts (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x)))
                     (FiniteExpectation prts (Y 0))); [trivial |].
          rewrite <- optional_stopping_time_b_helper'.
          rewrite <- (Lim_seq_const (FiniteExpectation prts (Y 0))).
          apply Lim_seq_le_loc.
          exists 0%nat; intros.
          rewrite FinExp_Rbar_FinExp; try typeclasses eauto.
          apply Rge_le.
          now apply process_stopped_at_sub_martingale_expectation_0 with (adapt := adapt).
      Qed.

      Lemma optional_stopping_time_super_b
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rge Y F} :
        FiniteExpectation prts (process_under Y T) <= FiniteExpectation prts (Y 0%nat).
      Proof.
        rewrite optional_stopping_time_b_eq. 
        cut (Rbar_le (Rbar_FiniteExpectation prts (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x)))
                     (FiniteExpectation prts (Y 0))); [trivial |].
        rewrite <- optional_stopping_time_b_helper'.
          rewrite <- (Lim_seq_const (FiniteExpectation prts (Y 0))).
          apply Lim_seq_le_loc.
          exists 0%nat; intros.
          rewrite FinExp_Rbar_FinExp; try typeclasses eauto.
          now apply process_stopped_at_super_martingale_expectation_0 with (adapt := adapt).
      Qed.

    End variant_b.

    Section variant_c.

      Context (ETfin:Rbar_IsFiniteExpectation
                       prts
                       (fun ts => match T ts with
                               | Some n => INR n
                               | None => p_infty
                               end))
      
              (K:R)
              (Kbound: forall n, almost prts (fun ω => Rabs (Y (S n) ω - Y n ω) <= K)).

      Instance optional_stopping_time_sub_c_ET_rv : RandomVariable dom Rbar_borel_sa
                                      (fun ts => match T ts with
                                              | Some n => INR n
                                              | None => p_infty
                                              end).
      Proof.
        apply Rbar_measurable_rv.
        intros ?.
        red in is_stop.
        destruct r.
        - destruct (Rle_dec 0 r).
          + destruct (archimed r).
            apply Rgt_lt in H.
            apply (sa_proper
                     _
                     (pre_list_union
                        (map (stopping_time_pre_event T)
                             (seq 0 (Z.to_nat (up r)))))).
            {
              intros ?.
              unfold stopping_time_pre_event, pre_list_union.
              split.
              - intros [? [??]].
                apply in_map_iff in H1.
                destruct H1 as [?[??]]; subst.
                rewrite H2; simpl.
                apply in_seq in H3.
                destruct H3 as [_ ?].
                simpl in H1.
                unfold lt in H1.
                apply le_INR in H1.
                rewrite INR_up_pos in H1 by lra.
                rewrite S_INR in H1.
                lra.
              - match_option; simpl; try tauto.
                intros le1.
                exists (fun ts => T ts = Some n).
                split; trivial.
                apply in_map_iff.
                eexists; split; trivial.
                apply in_seq.
                split; try lia.
                simpl.
                rewrite <- INR_up_pos in H, H0 by lra.
                case_eq (Z.to_nat (up r)); intros.
                * rewrite H1 in *.
                  simpl in *; lra.
                * simpl.
                  rewrite H1 in *.
                  assert (INR n < INR (S n0)) by lra.
                  now apply INR_lt in H2.
            }
            apply sa_pre_list_union; intros.
            apply in_map_iff in H1.
            destruct H1 as [? [??]]; subst.
            eapply sub; apply is_stop.
          + apply (sa_proper _ (pre_event_none)).
            * intros ?.
              unfold pre_event_none.
              split; [tauto | intros].
              match_destr_in H.
              simpl in H.
              generalize (pos_INR n0).
              lra.
            * apply sa_none.
        - apply (sa_proper _ (pre_Ω)).
          + intros ?.
            unfold pre_Ω.
            split; [intros | trivial].
            match_destr.
          + apply sa_all.
        - apply (sa_proper _ (pre_event_none)).
          + intros ?.
            unfold pre_event_none.
            split; [tauto | intros].
            match_destr_in H.
          + apply sa_none.
      Qed.

      Lemma optional_stopping_time_sub_c_Kbound_stopped_telescope :
        forall n : nat, rv_eq (process_stopped_at Y T n)
                          (rvplus
                             (Y 0%nat)
                             (fun ts => match lift1_min n (T ts) with
                              | 0%nat => 0%R
                              | S n =>
                                  rvsum (fun k => rvminus (Y (S k)) (Y k)) n ts
                              end)).
      Proof.
        unfold process_stopped_at.
        intros n ts.
        rv_unfold; unfold rvsum.
        induction (lift1_min n (T ts)); try lra.
        destruct n0.
        - rewrite Hierarchy.sum_O; lra.
        - rewrite Hierarchy.sum_Sn.
          unfold Hierarchy.plus; simpl.
          lra.
      Qed.

      Lemma Rabs_sum_n_triang f n :
        Rabs (@Hierarchy.sum_n Hierarchy.R_AbelianGroup f n) <= @Hierarchy.sum_n Hierarchy.R_AbelianGroup  (fun k => Rabs (f k)) n.
      Proof.
        induction n.
        - now repeat rewrite Hierarchy.sum_O.
        - repeat rewrite Hierarchy.sum_Sn.
          unfold Hierarchy.plus; simpl.
          rewrite Rabs_triang.
          lra.
      Qed.

      Definition optional_stopping_time_sub_c_Kbound
        := (Rbar_rvplus 
              (Rbar_rvabs (Y 0%nat))
              (Rbar_rvmult (const (Finite K)) (fun ts => match T ts with
                                 | Some n => INR n
                                 | None => p_infty
                                 end))).

      Instance optional_stopping_time_sub_c_Kbound_rv
               {rv:forall n, RandomVariable dom borel_sa (Y n)}
        :
        RandomVariable dom Rbar_borel_sa optional_stopping_time_sub_c_Kbound.
      Proof.
        apply Rbar_rvplus_rv.
        - apply Rbar_rvabs_rv.
          now apply Real_Rbar_rv.
        - apply Rbar_rvmult_rv; typeclasses eauto.
      Qed.
    
      Instance optional_stopping_time_sub_c_Kbound_isfe
               {rv:forall n, RandomVariable dom borel_sa (Y n)}
               {isfe:forall n, IsFiniteExpectation prts (Y n)} :
        Rbar_IsFiniteExpectation prts optional_stopping_time_sub_c_Kbound.
      Proof.
        apply Rbar_is_finite_expectation_isfe_plus.
        - apply Rbar_rvabs_rv.
          now apply Real_Rbar_rv.
        - apply Rbar_rvmult_rv; typeclasses eauto.
        - unfold Rbar_rvabs; simpl.
          apply IsFiniteExpectation_Rbar.
          apply IsFiniteExpectation_abs; trivial.
        - apply Rbar_IsFiniteExpectation_scale.
          typeclasses eauto.
      Qed.

      Lemma optional_stopping_time_sub_c_Kbound_stopped :
        forall n : nat, almostR2 prts Rbar_le (rvabs (process_stopped_at Y T n))
                          optional_stopping_time_sub_c_Kbound.
      Proof.
        intros.
        transitivity (rvabs (rvplus
                             (Y 0%nat)
                             (fun ts => match lift1_min n (T ts) with
                              | 0%nat => 0%R
                              | S n =>
                                  rvsum (fun k => rvminus (Y (S k)) (Y k)) n ts
                                     end))).
        {
          apply all_almost; intros ?.
          right.
          unfold rvabs; f_equal.
          apply optional_stopping_time_sub_c_Kbound_stopped_telescope.
        }

        transitivity (Rbar_rvplus
                        (Rbar_rvabs (Y 0))
                        (Rbar_rvabs (fun ts : Ts =>
                                  match lift1_min n (T ts) with
                                  | 0%nat => 0
                                  | S n0 => rvsum (fun k : nat => rvminus (Y (S k)) (Y k)) n0 ts
                                  end))).
        {
          apply all_almost; intros.
          unfold rvabs; rv_unfold.
          unfold Rbar_rvplus, Rbar_rvabs.
          simpl.
          destruct (lift1_min n (T x)); simpl
          ; apply Rabs_triang.
        }
        unfold optional_stopping_time_sub_c_Kbound.
        unfold Rbar_rvplus.
        apply almostR2_Rbar_le_plus_proper; try reflexivity.
        rv_unfold.
        unfold Rbar_rvabs, Rbar_rvmult.
        transitivity (fun omega : Ts =>
                        Rabs
                          (INR (lift1_min n (T omega)) * K)).
        {
          apply almost_forall in Kbound.
          revert Kbound.
          apply almost_impl.
          apply all_almost; intros ??.
          transitivity (Rabs
                          match lift1_min n (T x) with
                          | 0%nat => 0
                          | S n0 => rvsum (fun (k : nat) (omega0 : Ts) => K) n0 x
                          end).
          {
            match_destr; try reflexivity.
            red in H.
            unfold rvsum.
            simpl.
            rewrite Rabs_sum_n_triang.
            transitivity (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun _ => K) n0).
            {
              apply sum_n_le_loc; intros.
              replace (Y (S n1) x + -1 * Y n1 x)
                with (Y (S n1) x - Y n1 x)
                by lra.
              auto.
            }
            rewrite Rabs_pos_eq; try reflexivity.
            apply sum_n_nneg; intros.
            rewrite <- (H 0%nat).
            apply Rabs_pos.
          }

          transitivity (Rabs
                          match lift1_min n (T x) with
                          | 0%nat => 0
                          | S n0 => (INR (S n0) * K)
                          end).
          { 
            match_destr; try reflexivity.
            unfold rvsum.
            now rewrite Hierarchy.sum_n_const.
          }

          destruct (lift1_min n (T x)); simpl; try lra.
          rewrite Rmult_0_l; reflexivity.
        }
        apply finexp_almost_finite in ETfin.
        - revert ETfin.
          apply almost_impl.
          generalize (Kbound 0%nat).
          apply almost_impl.
          apply all_almost; intros ???.
          match_option_in H0.
          unfold lift1_min.
          rewrite Rabs_mult.
          assert (0 <= K).
          {
            rewrite <- H.
            apply Rabs_pos.
          } 
          repeat rewrite Rabs_pos_eq; trivial.
          + rewrite Rmult_comm.
            apply Rmult_le_compat_l; trivial.
            apply le_INR.
            apply Nat.le_min_r.
          + apply pos_INR.
        - intros ?.
          apply optional_stopping_time_sub_c_ET_rv.
      Qed.

      Lemma optional_stopping_time_c_Tfin : almost prts (fun ts : Ts => T ts <> None).
      Proof.
        apply finexp_almost_finite in ETfin.
        revert ETfin.
        apply almost_impl.
        apply all_almost; intros ??.
        match_destr_in H.
        typeclasses eauto.
      Qed.
      
      Instance optional_stopping_time_c_isfe
               {rv:forall n, RandomVariable dom borel_sa (Y n)}
               {isfe:forall n, IsFiniteExpectation prts (Y n)} :
        IsFiniteExpectation prts (process_under Y T).
      Proof.
        apply (Dominated_convergence1_almost prts (process_stopped_at Y T) _ optional_stopping_time_sub_c_Kbound).
        - apply Rbar_finexp_finexp; typeclasses eauto.
        - intros n.
          generalize (optional_stopping_time_sub_c_Kbound_stopped n).
          apply almost_impl.
          generalize optional_stopping_time_sub_c_Kbound_isfe; intros HH.
          apply finexp_almost_finite in HH; [| typeclasses eauto].
          revert HH.
          apply almost_impl.
          apply all_almost; intros ???.
          rewrite <- H in H0 |- *.
          now simpl in *.
        - apply process_stopped_at_almost_fin_limit.
          apply optional_stopping_time_c_Tfin.
      Qed.

      Instance optional_stopping_time_c_isfe'
               {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        Rbar_IsFiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
      Proof.
        generalize (process_stopped_at_almost_fin_limit Y T optional_stopping_time_c_Tfin)
        ; intros HH.
        generalize Kbound_stopped; intros Kbound_stopped.

        cut (Rbar_IsFiniteExpectation
               prts
               (process_under Y T)).
        {
          intros HH2.
          eapply Rbar_IsFiniteExpectation_proper_almostR2; try eapply HH2.
          - typeclasses eauto.
          - typeclasses eauto.
          - revert HH.
            apply almost_impl.
            apply all_almost; intros ??.
            unfold Rbar_rvlim.
            apply is_lim_seq_unique in H.
            rewrite Elim_seq_fin.
            congruence.
        }
        apply IsFiniteExpectation_Rbar.
        apply optional_stopping_time_c_isfe.
      Qed.
        
      Lemma optional_stopping_time_c_eq
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        FiniteExpectation prts (process_under Y T) =
          Rbar_FiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
      Proof.
        generalize (process_stopped_at_almost_fin_limit Y T optional_stopping_time_c_Tfin)
        ; intros HH.
        rewrite <- FinExp_Rbar_FinExp; try typeclasses eauto.
        apply Rbar_FiniteExpectation_proper_almostR2.
        - typeclasses eauto.
        - apply Rbar_rvlim_rv. typeclasses eauto.
        - unfold almostR2, Rbar_rvlim.
          revert HH.
          apply almost_impl, all_almost.
          unfold impl; intros.
          apply is_lim_seq_unique in H.
          rewrite Elim_seq_fin.
          now rewrite H.
      Qed.

      Lemma optional_stopping_time_c_helper
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
      is_lim_seq
        (fun n : nat => Rbar_FiniteExpectation prts (fun x : Ts => process_stopped_at Y T n x) (isfe:= (IsFiniteExpectation_Rbar prts (fun x : Ts => process_stopped_at Y T n x)
                                                      (process_stopped_at_isfe Y F T n))))
        (Rbar_FiniteExpectation prts
                                (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x))).
      Proof.
        generalize (process_stopped_at_almost_fin_limit Y T optional_stopping_time_c_Tfin)
        ; intros HH.
        generalize Kbound_stopped; intros Kbound_stopped.
        apply (Dominated_convergence_almost prts (process_stopped_at Y T)
                                                 (Rbar_rvlim (process_stopped_at Y T)) (optional_stopping_time_sub_c_Kbound)).
        - typeclasses eauto.
        - intros.
          apply optional_stopping_time_sub_c_Kbound_stopped.
        - revert HH.
          apply almost_impl, all_almost.
          unfold impl; intros.
          unfold Rbar_rvlim.
          apply ELim_seq_correct.
          rewrite ex_Elim_seq_fin.
          unfold ex_lim_seq.
          now exists (process_under Y T x).
      Qed.

      Lemma optional_stopping_time_c_helper'
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        Lim_seq 
        (fun n : nat => Rbar_FiniteExpectation prts (fun x : Ts => process_stopped_at Y T n x) (isfe:= (IsFiniteExpectation_Rbar prts (fun x : Ts => process_stopped_at Y T n x)
                                                      (process_stopped_at_isfe Y F T n)))) = 
        Finite (Rbar_FiniteExpectation prts
                                (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x))).
      Proof.
        apply is_lim_seq_unique.
        apply optional_stopping_time_c_helper.
      Qed.

      Lemma optional_stopping_time_c
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts eq Y F} :
         FiniteExpectation prts (process_under Y T) = FiniteExpectation prts (Y 0%nat).
      Proof.        
        rewrite optional_stopping_time_c_eq.
        rewrite <- Rbar_finite_eq, <- optional_stopping_time_c_helper'.
        rewrite <- (Lim_seq_const (FiniteExpectation prts (Y 0))).
        apply Lim_seq_ext; intros.
        rewrite FinExp_Rbar_FinExp; try typeclasses eauto.
        now rewrite process_stopped_at_martingale_expectation_0 with (adapt := adapt).
      Qed.

      Lemma optional_stopping_time_sub_c
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
        FiniteExpectation prts (process_under Y T) >= FiniteExpectation prts (Y 0%nat).
      Proof.
        rewrite optional_stopping_time_c_eq. 
        apply Rle_ge.
        cut (Rbar_ge (Rbar_FiniteExpectation prts (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x)))
                     (FiniteExpectation prts (Y 0))); [trivial |].
          rewrite <- optional_stopping_time_c_helper'.
          rewrite <- (Lim_seq_const (FiniteExpectation prts (Y 0))).
          apply Lim_seq_le_loc.
          exists 0%nat; intros.
          rewrite FinExp_Rbar_FinExp; try typeclasses eauto.
          apply Rge_le.
          now apply process_stopped_at_sub_martingale_expectation_0 with (adapt := adapt).
      Qed.

      Lemma optional_stopping_time_super_c
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rge Y F} :
        FiniteExpectation prts (process_under Y T) <= FiniteExpectation prts (Y 0%nat).
      Proof.
        rewrite optional_stopping_time_c_eq. 
        cut (Rbar_le (Rbar_FiniteExpectation prts (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x)))
                     (FiniteExpectation prts (Y 0))); [trivial |].
        rewrite <- optional_stopping_time_c_helper'.
          rewrite <- (Lim_seq_const (FiniteExpectation prts (Y 0))).
          apply Lim_seq_le_loc.
          exists 0%nat; intros.
          rewrite FinExp_Rbar_FinExp; try typeclasses eauto.
          now apply process_stopped_at_super_martingale_expectation_0 with (adapt := adapt).
      Qed.
      
    End variant_c.
  End opt_stop_thm.

End stopped_process.


Local Existing Instance Rge_pre.
Local Existing Instance Rle_pre.

Section optional_stopping_time_thm.
  (** * Optional Stopping Theorem (Fair Games Theorem) *)
  (** This presents a statement and proof of the optional stopping time theorem, 
     also known as the fair games theorem, for discrete-time (sub/super)-martingales
     over general probability spaces. *)
  
  Context   (**r Given *)
    {Ts:Type} (**r a sample space, *)
    {σ: SigmaAlgebra Ts} (**r a σ-Algebra over the sample space, *)
    (prts: ProbSpace σ) (**r and a probability space defined over the σ-Algebra *)
    
    (**r and given *)
    (F : nat -> SigmaAlgebra Ts) (**r a sequence of σ-algebra *)
    {filt:IsFiltration F} (**r that form a filtration *)
    {sub:IsSubAlgebras σ F} (**r and are all contained in the base σ-algebra *)
    
    (**r and given *)
    (τ:Ts -> option nat) (**r a random time *)
    {is_stop:IsStoppingTime τ F} (**r that is a stopping time with respect to the given filtration *)
    
    (**r and given *)
    (Y : nat -> Ts -> R) (**r a stochastic process *)
    {rv:forall n, RandomVariable σ borel_sa (Y n)} (**r all of whose components are measurable *)
    {isfe:forall n, IsFiniteExpectation prts (Y n)} (**r and have finite expectation (∀ n, E (Y n) < ∞) *)
    {adapt:IsAdapted borel_sa Y F} (**r , where the process is adapted to the filtration *)

    (conditions:    (**r and  one of these conditions holds: *)
      (exists (N:nat), (**r There is a natural number [N] such that *)
          almost prts (fun ω => match τ ω with (**r  τ <= N almost surely *)
                             | Some k => (k <= N)%nat 
                             | None => False
                             end))
        
      \/ (**r OR *)
        (almost prts (fun ω => τ ω <> None) (**r the stopping time is almost surely finite *)
         /\ exists (K:R), (**r and there is a real number [K], such that *)
            (forall n, almost prts (fun ω => Rabs (Y n ω) < K))) (**r  ∀ n, | (Y n) | < K, almost surely *)
      \/ (**r OR *)
        (Rbar_IsFiniteExpectation (**r E(τ) < ∞ *)
           prts
           (fun ω => match τ ω with
                  | Some n => INR n
                  | None => p_infty
                  end)
         /\ exists (K:R), (**r and there is a real number [K], such that *)
          forall n, almost prts (fun ω => Rabs (Y (S n) ω - Y n ω) <= K)) (**r ∀ n, | Y (n + 1) - Y n | <= K, almost surely *)
    ).
    

  Instance optional_stopping_time_isfe : IsFiniteExpectation prts (process_under Y τ). (**r The process Y stopped at time τ has finite expectation *)

  Proof.
    destruct conditions as [[??]|[[?[??]]|[?[??]]]].
    - eapply optional_stopping_time_a_isfe; eauto.
    - eapply optional_stopping_time_b_isfe; eauto.
    - eapply optional_stopping_time_c_isfe; eauto.
  Qed.

  Theorem optional_stopping_time
          {mart:IsMartingale prts eq Y F} (**r If the stochastic process is a martingale with respect to the filtration *)
    : (**r then the expectation of the stopped process is the same as when the process started  *)
    FiniteExpectation prts (process_under Y τ) = FiniteExpectation prts (Y 0%nat).
  Proof.
    destruct conditions as [[??]|[[?[??]]|[?[??]]]].
    - rewrite (optional_stopping_time_a prts Y F τ x H); eauto.
      apply FiniteExpectation_pf_irrel.
    - rewrite <- (optional_stopping_time_b prts Y F τ H x H0); eauto.
      apply FiniteExpectation_pf_irrel.
    - rewrite <- (optional_stopping_time_c prts Y F τ H x H0); eauto.
      apply FiniteExpectation_pf_irrel.
  Qed.
    
  Theorem optional_stopping_time_sub
          {mart:IsMartingale prts Rle Y F} (**r If the stochastic process is a sub-martingale with respect to the filtration *)
    : (**r then the expectation of the stopped process is greater than or equal to when the process started  *)
    FiniteExpectation prts (process_under Y τ) >= FiniteExpectation prts (Y 0%nat).
  Proof.
    destruct conditions as [[??]|[[?[??]]|[?[??]]]].
    - rewrite <- (optional_stopping_time_sub_a prts Y F τ x H); eauto.
      right; apply FiniteExpectation_pf_irrel.
    - rewrite <- (optional_stopping_time_sub_b prts Y F τ H x H0); eauto.
      right; apply FiniteExpectation_pf_irrel.
    - rewrite <- (optional_stopping_time_sub_c prts Y F τ H x H0); eauto.
      right; apply FiniteExpectation_pf_irrel.
  Qed.
    
  Theorem optional_stopping_time_super
          {mart:IsMartingale prts Rge Y F} (**r If the stochastic process is a super-martingale with respect to the filtration *)
    : (**r then the expectation of the stopped process is less than or equal to when the process started  *)
    FiniteExpectation prts (process_under Y τ) <= FiniteExpectation prts (Y 0%nat).
  Proof.
    destruct conditions as [[??]|[[?[??]]|[?[??]]]].
    - rewrite <- (optional_stopping_time_super_a prts Y F τ x H); eauto.
      right; apply FiniteExpectation_pf_irrel.
    - rewrite <- (optional_stopping_time_super_b prts Y F τ H x H0); eauto.
      right; apply FiniteExpectation_pf_irrel.
    - rewrite <- (optional_stopping_time_super_c prts Y F τ H x H0); eauto.
      right; apply FiniteExpectation_pf_irrel.
  Qed.

End optional_stopping_time_thm.
