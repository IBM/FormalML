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
  
  Context {Ts:Type}.

    Definition process_under (Y : nat -> Ts -> R) (T:Ts -> option nat) (x : Ts) : R
    := match T x with
       | None => 0
       | Some n => Y n x
       end.

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
      eapply RandomVariable_proper; try apply process_stopped_at_as_alt; try reflexivity.
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
      eapply (RandomVariable_proper _ (F n)); try apply process_stopped_at_as_alt; try reflexivity.
      destruct n; simpl; trivial.
      apply rvplus_rv.
      - apply rvsum_rv_loc; intros.
        apply rvmult_rv; trivial.
        + eapply (RandomVariable_proper_le (F m) _); try reflexivity.
          * apply is_filtration_le; trivial; lia.
          * apply adapt.
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
     
     Lemma process_stopped_at_sub_martinagle_expectation_0
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
      forall n, FiniteExpectation prts ((process_stopped_at Y T) n) >= FiniteExpectation prts (Y 0).
    Proof.
      intros.
      rewrite <- expectation_process_stopped_at_0.
      apply Rle_ge.
      apply is_sub_martingale_expectation with (sas := F) (adapt0 :=process_stopped_at_adapted Y F T) 
                                           (rv0 := process_stopped_at_rv Y F T) 
                                           (filt0 := filt) (sub0 := sub); try lia.
      now apply process_stopped_at_sub_martingale.
    Qed.

     Lemma process_stopped_at_super_martinagle_expectation_0
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rge Y F} :
       forall n, FiniteExpectation prts ((process_stopped_at Y T) n) <= FiniteExpectation prts (Y 0).
     Proof.
      intros.
      rewrite <- expectation_process_stopped_at_0.
      apply Rge_le.
      apply is_super_martingale_expectation with (sas := F) (adapt0 :=process_stopped_at_adapted Y F T) 
                                           (rv0 := process_stopped_at_rv Y F T) 
                                           (filt0 := filt) (sub0 := sub); try lia.
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
      apply is_martingale_expectation with (sas := F) (adapt0 :=process_stopped_at_adapted Y F T) 
                                           (rv0 := process_stopped_at_rv Y F T) 
                                           (filt0 := filt) (sub0 := sub).
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
      now apply is_martingale_expectation with (sas := F) (rv0 := rv) (adapt0 := adapt) (filt0 := filt) (sub0 := sub).
    Qed.

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

  End process_stopped_at_props_ext.

  Section opt_stop_thm.
  End opt_stop_thm.    

    
End stopped_process.
