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
Require Import NumberIso.
Require Import PushNeg.
Require Import Reals.
Require Import Coquelicot.Rbar.

Set Bullet Behavior "Strict Subproofs". 

Section martingale.
  Local Open Scope R.
  Local Existing Instance Rge_pre.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).
  
  Class IsMartingale (RR:R->R->Prop) {pre:PreOrder RR}
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
    := is_martingale :
      forall n, almostR2 prts RR (Y n) (FiniteConditionalExpectation prts (sub n) (Y (S n))).

  Lemma is_martingale_eq_proper (RR:R->R->Prop) {pre:PreOrder RR}
        (Y1 Y2 : nat -> Ts -> R) (sas1 sas2 : nat -> SigmaAlgebra Ts)
        {rv1:forall n, RandomVariable dom borel_sa (Y1 n)}
        {rv2:forall n, RandomVariable dom borel_sa (Y2 n)}
        {isfe1:forall n, IsFiniteExpectation prts (Y1 n)}
        {isfe2:forall n, IsFiniteExpectation prts (Y2 n)}
        {adapt1:IsAdapted borel_sa Y1 sas1}
        {adapt2:IsAdapted borel_sa Y2 sas2}
        {filt1:IsFiltration sas1}
        {filt2:IsFiltration sas2}
        {sub1:IsSubAlgebras dom sas1}
        {sub2:IsSubAlgebras dom sas2} :
    (forall n, almostR2 prts eq (Y1 n) (Y2 n)) ->
    (forall n, sa_equiv (sas1 n) (sas2 n)) ->
    IsMartingale RR Y1 sas1 -> IsMartingale RR Y2 sas2.
  Proof.
    intros eqq1 eqq2 mart n.
    generalize (FiniteCondexp_all_proper prts (sub1 n) (sub2 n) (eqq2 n) (Y1 (S n)) (Y2 (S n)) (eqq1 _)); intros HH.
    apply almostR2_prob_space_sa_sub_lift in HH.
    specialize (mart n).
    eapply almostR2_eq_proper; try eapply mart.
    - symmetry; auto.
    - symmetry; auto.
  Qed.

  Lemma is_martingale_eq_proper_iff (RR:R->R->Prop) {pre:PreOrder RR}
        (Y1 Y2 : nat -> Ts -> R) (sas1 sas2 : nat -> SigmaAlgebra Ts)
        {rv1:forall n, RandomVariable dom borel_sa (Y1 n)}
        {rv2:forall n, RandomVariable dom borel_sa (Y2 n)}
        {isfe1:forall n, IsFiniteExpectation prts (Y1 n)}
        {isfe2:forall n, IsFiniteExpectation prts (Y2 n)}
        {adapt1:IsAdapted borel_sa Y1 sas1}
        {adapt2:IsAdapted borel_sa Y2 sas2}
        {filt1:IsFiltration sas1}
        {filt2:IsFiltration sas2}
        {sub1:IsSubAlgebras dom sas1}
        {sub2:IsSubAlgebras dom sas2} :
    (forall n, almostR2 prts eq (Y1 n) (Y2 n)) ->
    (forall n, sa_equiv (sas1 n) (sas2 n)) ->
    IsMartingale RR Y1 sas1 <-> IsMartingale RR Y2 sas2.
  Proof.
    intros; split; intros.
    - eapply (is_martingale_eq_proper RR Y1 Y2); eauto.
    - eapply (is_martingale_eq_proper RR Y2 Y1); eauto.
      + intros; symmetry; auto.
      + intros; symmetry; auto.
  Qed.
  
  Lemma is_martingale_eq_proper_transport (RR:R->R->Prop) {pre:PreOrder RR}
        (Y1 Y2 : nat -> Ts -> R) (sas1 sas2 : nat -> SigmaAlgebra Ts)
        {rv1:forall n, RandomVariable dom borel_sa (Y1 n)}
        {rv2:forall n, RandomVariable dom borel_sa (Y2 n)}
        {isfe1:forall n, IsFiniteExpectation prts (Y1 n)}
        {adapt1:IsAdapted borel_sa Y1 sas1}
        {adapt2:IsAdapted borel_sa Y2 sas2}
        {filt1:IsFiltration sas1}
        {sub1:IsSubAlgebras dom sas1}
        (Y_eqq:(forall n, almostR2 prts eq (Y1 n) (Y2 n)))
        (sas_eqq:forall n, sa_equiv (sas1 n) (sas2 n)) :
    IsMartingale RR Y1 sas1 -> IsMartingale RR Y2 sas2
                                           (isfe:=fun n =>
                                                    IsFiniteExpectation_proper_almostR2 prts _ _ (Y_eqq n))
                                           (filt:=IsFiltration_proper' _ _ sas_eqq filt1)
                                           (sub:=IsSubAlgebras_eq_proper' _ _ (reflexivity _) _ _ sas_eqq sub1).
  Proof.
    now apply is_martingale_eq_proper.
  Qed.

  Example IsSubMartingale 
          (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)}
          {adapt:IsAdapted borel_sa Y sas}
          {filt:IsFiltration sas}
          {sub:IsSubAlgebras dom sas}
    := IsMartingale Rle Y sas.
  
  Example IsSuperMartingale 
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
      := IsMartingale Rge Y sas.

  Lemma is_martingale_sub_super_eq 
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
    : IsMartingale Rle Y sas ->
      IsMartingale Rge Y sas ->
      IsMartingale eq Y sas.
  Proof.
    intros ???.
    apply antisymmetry.
    - now apply H.
    - apply almostR2_Rge_le.
      apply H0.
  Qed.
  
  Instance is_martingale_eq_any (RR:R->R->Prop) {pre:PreOrder RR}
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
    : IsMartingale eq Y sas ->
      IsMartingale RR Y sas.
  Proof.
    intros ??.
    generalize (H n).
    apply almost_impl; apply all_almost; intros ??.
    rewrite H0.
    reflexivity.
  Qed.

  Corollary is_martingale_eq_sub
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
    : IsMartingale eq Y sas ->
      IsMartingale Rle Y sas.
  Proof.
    apply is_martingale_eq_any.
  Qed.

  Corollary is_martingale_eq_super
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
    : IsMartingale eq Y sas ->
      IsMartingale Rge Y sas.
  Proof.
    apply is_martingale_eq_any.
  Qed.

  Lemma is_sub_martingale_neg
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas} :
   IsMartingale Rle (fun n => rvopp (Y n)) sas <-> IsMartingale Rge Y sas.
  Proof.
    split; intros HH
    ; intros n; specialize (HH n)
    ; revert HH
    ; apply almost_impl
    ; generalize (FiniteCondexp_opp prts (sub n) (Y (S n)))
    ; intros HH
    ; apply almostR2_prob_space_sa_sub_lift in HH
    ; revert HH
    ; apply almost_impl
    ; apply all_almost
    ; intros ???.
    - rewrite H in H0.
      unfold rvopp, rvscale in *; lra.
    - rewrite H.
      unfold rvopp, rvscale in *; lra.
  Qed.

  Lemma is_super_martingale_neg
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas} :
   IsMartingale Rge (fun n => rvopp (Y n)) sas <-> IsMartingale Rle Y sas.
  Proof.
    rewrite <- is_sub_martingale_neg.
    apply is_martingale_eq_proper_iff; try reflexivity.
    intros; apply all_almost; intros ?.
    now rewrite rvopp_opp.
  Qed.

  Lemma is_sub_martingale_proper 
        (Y1 Y2 : nat -> Ts -> R) (sas1 sas2 : nat -> SigmaAlgebra Ts)
        {rv1:forall n, RandomVariable dom borel_sa (Y1 n)}
        {rv2:forall n, RandomVariable dom borel_sa (Y2 n)}
        {isfe1:forall n, IsFiniteExpectation prts (Y1 n)}
        {isfe2:forall n, IsFiniteExpectation prts (Y2 n)}
        {adapt1:IsAdapted borel_sa Y1 sas1}
        {adapt2:IsAdapted borel_sa Y2 sas2}
        {filt1:IsFiltration sas1}
        {filt2:IsFiltration sas2}
        {sub1:IsSubAlgebras dom sas1}
        {sub2:IsSubAlgebras dom sas2} :
    (forall n, almostR2 prts eq (Y1 n) (Y2 n)) ->
    (forall n, sa_sub (sas2 n) (sas1 n)) ->
    IsMartingale Rle Y1 sas1 -> IsMartingale Rle Y2 sas2.
  Proof.
    intros eqq1 eqq2 mart.
    assert (adopt2':IsAdapted borel_sa Y2 sas1).
    {
      generalize adapt2.
      apply is_adapted_proper; trivial.
      reflexivity.
    } 

    assert (mart':IsMartingale Rle Y2 sas1).
    {
      now apply (is_martingale_eq_proper _ _ _ _ _ eqq1 (fun n => reflexivity _)).
    } 
    clear Y1 adapt1 rv1 isfe1 eqq1 mart.
    intros n.
    red in mart'.
    assert (RandomVariable dom borel_sa (FiniteConditionalExpectation prts (sub1 n) (Y2 (S n)))).
    {
      generalize (FiniteCondexp_rv prts (sub1 n) (Y2 (S n))).
      apply RandomVariable_sa_sub.
      apply sub1.
    } 

    generalize (FiniteCondexp_tower' prts (sub1 n) (eqq2 n) (Y2 (S n)))
    ; intros HH.
    apply almostR2_prob_space_sa_sub_lift in HH.

    transitivity (FiniteConditionalExpectation prts (transitivity (eqq2 n) (sub1 n))
                                               (FiniteConditionalExpectation prts (sub1 n) (Y2 (S n)))).
    - generalize (FiniteCondexp_ale prts (sub2 n) _ _ (mart' n))
      ; intros HH2.
      apply almostR2_prob_space_sa_sub_lift in HH2.
      transitivity (FiniteConditionalExpectation prts (sub2 n) (Y2 n)).
      + eapply almostR2_subrelation.
        * apply eq_subrelation.
          typeclasses eauto.
        * apply all_almost; intros ?.
          symmetry.
          apply FiniteCondexp_id; trivial.
      + rewrite HH2.
        eapply almostR2_subrelation.
        * apply eq_subrelation.
          typeclasses eauto.
        * eapply (almostR2_prob_space_sa_sub_lift prts (sub2 n)).
          eapply FiniteCondexp_all_proper; reflexivity.
    - eapply almostR2_subrelation.
      + apply eq_subrelation.
        typeclasses eauto.
      + rewrite HH.
        symmetry.
        eapply (almostR2_prob_space_sa_sub_lift prts (sub2 n)).
        eapply FiniteCondexp_all_proper; reflexivity.
  Qed.
  
  Lemma is_super_martingale_proper 
        (Y1 Y2 : nat -> Ts -> R) (sas1 sas2 : nat -> SigmaAlgebra Ts)
        {rv1:forall n, RandomVariable dom borel_sa (Y1 n)}
        {rv2:forall n, RandomVariable dom borel_sa (Y2 n)}
        {isfe1:forall n, IsFiniteExpectation prts (Y1 n)}
        {isfe2:forall n, IsFiniteExpectation prts (Y2 n)}
        {adapt1:IsAdapted borel_sa Y1 sas1}
        {adapt2:IsAdapted borel_sa Y2 sas2}
        {filt1:IsFiltration sas1}
        {filt2:IsFiltration sas2}
        {sub1:IsSubAlgebras dom sas1}
        {sub2:IsSubAlgebras dom sas2} :
    (forall n, almostR2 prts eq (Y1 n) (Y2 n)) ->
    (forall n, sa_sub (sas2 n) (sas1 n)) ->
    IsMartingale Rge Y1 sas1 -> IsMartingale Rge Y2 sas2.
  Proof.
    intros eqq1 eqq2 mart.
    apply is_sub_martingale_neg.
    apply is_sub_martingale_neg in mart.
    revert mart.
    eapply is_sub_martingale_proper; eauto.
    intros.
    now apply almostR2_eq_opp_proper.
  Qed.

  Lemma is_martingale_proper 
        (Y1 Y2 : nat -> Ts -> R) (sas1 sas2 : nat -> SigmaAlgebra Ts)
        {rv1:forall n, RandomVariable dom borel_sa (Y1 n)}
        {rv2:forall n, RandomVariable dom borel_sa (Y2 n)}
        {isfe1:forall n, IsFiniteExpectation prts (Y1 n)}
        {isfe2:forall n, IsFiniteExpectation prts (Y2 n)}
        {adapt1:IsAdapted borel_sa Y1 sas1}
        {adapt2:IsAdapted borel_sa Y2 sas2}
        {filt1:IsFiltration sas1}
        {filt2:IsFiltration sas2}
        {sub1:IsSubAlgebras dom sas1}
        {sub2:IsSubAlgebras dom sas2} :
    (forall n, almostR2 prts eq (Y1 n) (Y2 n)) ->
    (forall n, sa_sub (sas2 n) (sas1 n)) ->
    IsMartingale eq Y1 sas1 -> IsMartingale eq Y2 sas2.
  Proof.
    intros.
    apply is_martingale_sub_super_eq.
    - apply (is_martingale_eq_any Rle) in H1.
      revert H1.
      eapply is_sub_martingale_proper; eauto.
    - apply (is_martingale_eq_any Rge) in H1.
      revert H1.
      eapply is_super_martingale_proper; eauto.
  Qed.

  Corollary is_sub_martingale_natural
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas} :
    IsMartingale Rle Y sas ->
    IsMartingale Rle Y (filtration_history_sa Y).
  Proof.
    apply is_sub_martingale_proper; try reflexivity.
    now apply filtration_history_sa_is_least.
  Qed.

  Corollary is_super_martingale_natural
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas} :
    IsMartingale Rge Y sas ->
    IsMartingale Rge Y (filtration_history_sa Y).
  Proof.
    apply is_super_martingale_proper; try reflexivity.
    now apply filtration_history_sa_is_least.
  Qed.

  Corollary is_martingale_natural
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas} :
    IsMartingale eq Y sas ->
    IsMartingale eq Y (filtration_history_sa Y).
  Proof.
    apply is_martingale_proper; try reflexivity.
    now apply filtration_history_sa_is_least.
  Qed.

  Lemma is_sub_martingale_lt
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rle Y sas} :
    forall s t, (s < t)%nat ->
           almostR2 prts Rle (Y s) (FiniteConditionalExpectation prts (sub s) (Y t)).
  Proof.
    intros.
    destruct t; try lia.
    assert (s <= t)%nat by lia; clear H.
    induction H0.
    - apply mart.
    - generalize (mart (S m)); intros eqq.
      assert (RandomVariable dom borel_sa (FiniteConditionalExpectation prts (sub (S m)) (Y (S (S m))))).
      {
        generalize (FiniteCondexp_rv prts (sub (S m)) (Y (S (S m)))).
        now apply RandomVariable_sa_sub.
      }         
        
      generalize (FiniteCondexp_ale _ (sub s) _ _ eqq)
      ; intros eqq2.
      apply almostR2_prob_space_sa_sub_lift in eqq2.
      rewrite IHle, eqq2.

      assert (RandomVariable dom borel_sa (FiniteConditionalExpectation prts (sub (S s)) (Y (S (S m))))).
      { 
        generalize (FiniteCondexp_rv prts (sub (S s)) (Y (S (S m)))).
        now apply RandomVariable_sa_sub.
      }         

      assert (sa_sub (sas s) (sas (S m))).
      {
        apply is_filtration_le; trivial.
        lia.
      } 
      generalize (FiniteCondexp_tower' prts (sub (S m)) H2  (Y (S (S m))))
      ; intros HH.
      apply almostR2_prob_space_sa_sub_lift in HH.
      eapply almostR2_subrelation.
      + apply eq_subrelation.
        typeclasses eauto.
      + transitivity (FiniteConditionalExpectation prts (transitivity H2 (sub (S m))) (Y (S (S m)))).
        * rewrite <- HH.
          eapply (almostR2_prob_space_sa_sub_lift prts (sub s)).
          apply (FiniteCondexp_all_proper _ _ _); try reflexivity.
        * symmetry.
          eapply (almostR2_prob_space_sa_sub_lift prts (sub s)).
          apply (FiniteCondexp_all_proper _ _ _); reflexivity.
  Qed.

  Lemma is_super_martingale_lt
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rge Y sas} :
    forall s t, (s < t)%nat ->
           almostR2 prts Rge (Y s) (FiniteConditionalExpectation prts (sub s) (Y t)).
  Proof.
    intros.
    apply is_sub_martingale_neg in mart.
    eapply is_sub_martingale_lt in mart; try eapply H.
    revert mart; apply almost_impl.
    generalize (FiniteCondexp_opp prts (sub s) (Y t)); intros HH
    ; apply almostR2_prob_space_sa_sub_lift in HH
    ; revert HH
    ; apply almost_impl.
    apply all_almost; intros ???.
    unfold rvopp, rvscale in *.
    lra.
  Qed.

  Lemma is_martingale_lt
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale eq Y sas} :
    forall s t, (s < t)%nat ->
           almostR2 prts eq (Y s) (FiniteConditionalExpectation prts (sub s) (Y t)).
  Proof.
    intros.
    apply antisymmetry.
    - eapply is_sub_martingale_lt; trivial.
      now eapply is_martingale_eq_any.
    - eapply almostR2_Rge_le.
      eapply is_super_martingale_lt; trivial.
      now eapply is_martingale_eq_any.
  Qed.
  
  Lemma is_sub_martingale_expectation
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rle Y sas}
    :
      forall s t, (s <= t)%nat ->
             FiniteExpectation prts (Y s) <= FiniteExpectation prts (Y t).
  Proof.
    intros s t sltt.
    destruct (le_lt_or_eq _ _ sltt).
    - eapply is_sub_martingale_lt in mart; try eapply H.
      assert (rv1:RandomVariable dom borel_sa (FiniteConditionalExpectation prts (sub s) (Y t))).
      {
        apply (RandomVariable_sa_sub (sub s)).
        typeclasses eauto.
      }
      generalize (FiniteExpectation_ale prts _ _ mart).
      now rewrite FiniteCondexp_FiniteExpectation.
    - subst; reflexivity.
  Qed.

  Lemma is_super_martingale_expectation
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rge Y sas}
    :
      forall s t, (s <= t)%nat ->
             FiniteExpectation prts (Y s) >= FiniteExpectation prts (Y t).
  Proof.
    intros s t sltt.
    apply is_sub_martingale_neg in mart.
    generalize (is_sub_martingale_expectation _ _ (mart:=mart) _ _ sltt).
    repeat rewrite FiniteExpectation_opp.
    lra.
  Qed.
  
  Lemma is_martingale_expectation
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale eq Y sas}
    :
      forall s t, FiniteExpectation prts (Y s) = FiniteExpectation prts (Y t).
  Proof.
    intros.
    cut (forall s t, (s <= t)%nat -> FiniteExpectation prts (Y s) = FiniteExpectation prts (Y t)).
    {
      intros.
      destruct (NPeano.Nat.le_ge_cases s t).
      - now apply H.
      - symmetry; now apply H.
    } 
    intros.
    apply antisymmetry.
    - eapply is_sub_martingale_expectation; trivial.
      now apply is_martingale_eq_any.
    - apply Rge_le.
      eapply is_super_martingale_expectation; trivial.
      now apply is_martingale_eq_any.
  Qed.

  Definition is_predictable {Td} {saD:SigmaAlgebra Td} (Y : nat -> Ts -> Td) (sas : nat -> SigmaAlgebra Ts)
    := IsAdapted saD (fun x => Y (S x)) sas.

  Lemma is_adapted_filtration_pred {Td} {saD:SigmaAlgebra Td}
        (Y : nat -> Ts -> Td) (sas : nat -> SigmaAlgebra Ts)
        {filt:IsFiltration sas}
        {adapt:IsAdapted saD Y (fun n => sas (pred n))} :
    IsAdapted saD Y sas.
  Proof.
    intros n.
    generalize (adapt n).
    eapply RandomVariable_proper_le; try reflexivity.
    destruct n; simpl.
    - reflexivity.
    - apply filt.
  Qed.

  Lemma is_adapted_filtration_pred_predictable
        {Td} {saD:SigmaAlgebra Td}
        (Y : nat -> Ts -> Td) (sas : nat -> SigmaAlgebra Ts)
        {filt:IsFiltration sas}
        {adapt:IsAdapted saD Y (fun n => sas (pred n))} :
    is_predictable Y sas.
  Proof.
    intros n.
    apply (adapt (S n)).
  Qed.

  Lemma is_adapted_filtration_shift
        {Td} {saD:SigmaAlgebra Td}
        k (Y : nat -> Ts -> Td) (sas : nat -> SigmaAlgebra Ts)
        {filt:IsFiltration sas}
        {adapt:IsAdapted saD Y (fun n => sas (n - k)%nat)} :
    IsAdapted saD Y sas.
  Proof.
    intros n.
    generalize (adapt n).
    eapply RandomVariable_proper_le; try reflexivity.
    apply is_filtration_le; trivial; lia.
  Qed.

  Theorem doob_meyer_decomposition
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rle Y sas} :
    { M : nat -> Ts -> R |
      let A := fun n => rvminus (Y n) (M n) in
      exists (rvM:forall n, RandomVariable dom borel_sa (M n))
        (isfeM:forall n, IsFiniteExpectation prts (M n))
        (adaptM:IsAdapted borel_sa M sas),
        IsMartingale eq M sas
        /\ IsAdapted borel_sa A (fun n => sas (pred n))
        /\ (forall n, RandomVariable dom borel_sa (A n))
        /\ (forall n, IsFiniteExpectation prts (A n))
        /\ (forall n, almostR2 prts Rle (A n) (A (S n)))}.
  Proof.
    pose (dn := fun n => FiniteConditionalExpectation prts (sub n) (rvminus (Y (S n)) (Y n))).
    pose (An := fun n => match n with
                      | 0 => const 0
                      | S k => rvsum (fun i => dn i) k
                      end).
    exists (fun n => rvminus (Y n) (An n)).
    intros A.

    assert (Aeq: pointwise_relation _ rv_eq A An).
    {
      unfold A.
      intros ??.
      rv_unfold; lra.
    } 

    assert (rvdn:(forall n : nat, RandomVariable dom borel_sa (dn n))).
    {
      unfold dn; intros.
      apply FiniteCondexp_rv'.
    } 

    assert (isfedn:forall n : nat, IsFiniteExpectation prts (dn n)).
    {
      unfold dn; intros.
      unfold IsFiniteExpectation.
      rewrite FiniteCondexp_Expectation.
      now apply IsFiniteExpectation_minus.
    } 
    
    assert (rvAn:(forall n : nat, RandomVariable dom borel_sa (An n))).
    {
      unfold An.
      intros [|?]; simpl
      ; try apply rvconst.
      now apply rvsum_rv.
    } 
        
    assert (isfeAn:forall n : nat, IsFiniteExpectation prts (An n)).
    {
      unfold An.
      intros [|?]; simpl.
      - apply IsFiniteExpectation_const.
      - now apply IsFiniteExpectation_sum.
    }

    assert (adaptdn:IsAdapted borel_sa dn sas)
      by (intros n; apply FiniteCondexp_rv).

    assert (adaptSAn:IsAdapted borel_sa An (fun n => sas (pred n))).
    { 
      unfold An.
      intros [|?]; simpl.
      - typeclasses eauto.
      - apply rvsum_rv_loc; intros.
        unfold dn.
        generalize (adaptdn m).
        eapply RandomVariable_proper_le; trivial; try reflexivity.
        apply is_filtration_le; trivial.
    }

    assert (adaptAn:IsAdapted borel_sa An sas).
    {
      now apply is_adapted_filtration_pred.
    } 

    exists _, _, _.

    assert (dnnneg : forall n, almostR2 prts Rle (const 0) (dn n)).
    {
      intros n.
      unfold dn.
      generalize (FiniteCondexp_minus prts (sub n) (Y (S n)) (Y n))
      ; intros HH.
      apply (almostR2_prob_space_sa_sub_lift prts) in HH.
      generalize (adapt n); intros HH2.
      generalize (mart n); apply almost_impl.
      revert HH; apply almost_impl.
      apply all_almost; intros ???.
      rewrite H.
      rv_unfold.
      rewrite (FiniteCondexp_id prts (sub n) (Y n)).
      lra.
    } 
    repeat split.
    - intros n.
      generalize (FiniteCondexp_minus prts (sub n) (Y (S n)) (An (S n)))
      ; intros HH1.
      apply (almostR2_prob_space_sa_sub_lift prts) in HH1.
      rewrite HH1.
      generalize (adaptSAn (S n)); intros HH2.
      simpl pred in HH2.
      generalize (FiniteCondexp_id prts (sub n) (An (S n)))
      ; intros HH3.
      eapply almostR2_eq_subr in HH3.
      rewrite HH3.

      clear HH1 HH3.
      destruct n as [|?]; simpl in *.
      + unfold dn.
        generalize (FiniteCondexp_minus prts (sub 0)%nat (Y 1%nat) (Y 0%nat))
        ; intros HH.
        apply (almostR2_prob_space_sa_sub_lift prts) in HH.
        revert HH.
        apply almost_impl.
        apply all_almost; intros ??.
        rv_unfold; unfold rvsum.
        rewrite Hierarchy.sum_O.
        rewrite H.
        generalize (adapt 0%nat); intros.
        rewrite (FiniteCondexp_id _ _ (Y 0%nat)).
        lra.
      +
        generalize (FiniteCondexp_minus prts (sub (S n)) (Y (S (S n))) (Y (S n)))
        ; intros HH.
        apply (almostR2_prob_space_sa_sub_lift prts) in HH.
        revert HH.
        apply almost_impl.
        apply all_almost; intros ??.
        rv_unfold; unfold rvsum.
        rewrite Hierarchy.sum_Sn.
        unfold Hierarchy.plus; simpl.
        unfold dn.
        rewrite H.
        field_simplify.
        generalize (adapt (S n)); intros.
        rewrite (FiniteCondexp_id _ _ (Y (S n))).
        lra.
    - now intros; rewrite Aeq.
    - now intros; rewrite Aeq.
    - now intros; rewrite Aeq.
    - intros n.
      cut (almostR2 prts Rle (An n) (An (S n))).
      {
        apply almost_impl; apply all_almost; intros ??.
        now repeat rewrite Aeq.
      }
      unfold An.
      unfold rvsum.
      destruct n.
      + simpl.
        generalize (dnnneg 0%nat); apply almost_impl.
        apply all_almost; intros ??; simpl.
        now rewrite Hierarchy.sum_O.
      + simpl.
        generalize (dnnneg (S n)); apply almost_impl.
        apply all_almost; intros ??; simpl.
        rewrite Hierarchy.sum_Sn.
        unfold Hierarchy.plus; simpl.
        replace (n - 0)%nat with n by lia.
        unfold const in H.
        lra.
  Qed.

  Instance is_adapted_convex  (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts) (phi:R->R)
           {adapt:IsAdapted borel_sa Y sas}:
    (forall c x y, convex phi c x y) ->
    IsAdapted borel_sa (fun (n : nat) (omega : Ts) => phi (Y n omega)) sas.
  Proof.
    intros ??.
    apply continuous_compose_rv.
    - apply adapt.
    - intros ?.
      now apply convex_continuous.
  Qed.

  Lemma is_martingale_convex
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts) (phi:R->R)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale eq Y sas}
        {rvphi : forall n, RandomVariable dom borel_sa (fun x => phi (Y n x))} 
        {isfephi : forall n, IsFiniteExpectation prts (fun x => phi (Y n x))}
        {adaptphi:IsAdapted borel_sa (fun (n : nat) (omega : Ts) => phi (Y n omega)) sas}
    : 
    (forall c x y, convex phi c x y) ->
    IsMartingale Rle (fun n omega => (phi (Y n omega))) sas.
  Proof.
    intros c ?.
    specialize (mart n).
    generalize (FiniteCondexp_Jensen prts (sub n) (Y (S n)) phi c)
    ; intros HH.
    apply (almostR2_prob_space_sa_sub_lift prts) in HH.
    rewrite <- HH.
    eapply almostR2_subrelation.
    - apply eq_subrelation.
      typeclasses eauto.
    - now apply almost_f_equal.
  Qed.
  
  Lemma is_sub_martingale_incr_convex
        (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts) (phi:R->R)
        {rv:forall n, RandomVariable dom borel_sa (Y n)}
        {isfe:forall n, IsFiniteExpectation prts (Y n)}
        {adapt:IsAdapted borel_sa Y sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rle Y sas}
        {rvphi : forall n, RandomVariable dom borel_sa (fun x => phi (Y n x))} 
        {isfephi : forall n, IsFiniteExpectation prts (fun x => phi (Y n x))}
        {adaptphi:IsAdapted borel_sa (fun (n : nat) (omega : Ts) => phi (Y n omega)) sas}
    : 
    (forall c x y, convex phi c x y) ->
    (forall x y, x <= y -> phi x <= phi y) ->
    IsMartingale Rle (fun n omega => (phi (Y n omega))) sas.
  Proof.
    intros c incr ?.
    specialize (mart n).
    generalize (FiniteCondexp_Jensen prts (sub n) (Y (S n)) phi c)
    ; intros HH.
    apply (almostR2_prob_space_sa_sub_lift prts) in HH.
    rewrite <- HH.
    revert mart.
    apply almost_impl.
    apply all_almost; intros ??.
    now apply incr in H.
  Qed.

  Section stopping_times.

    (* This definition is commonly used when the index set is nat *)
    Definition stopping_time_pre_event (rt:Ts->option nat) (n:nat) : pre_event Ts
      := fun x => rt x = Some n.

    (* This definition is commonly used for more general (including positive real valued) index sets *)
    Definition stopping_time_pre_event_alt (rt:Ts->option nat) (n:nat) : pre_event Ts
      := (fun x => match rt x with
                | None => False
                | Some a => (a <= n)%nat
                end).

    Lemma stopping_time_pre_event_dec (rt:Ts->option nat) (n:nat) :
      dec_pre_event (stopping_time_pre_event rt n).
    Proof.
      intros ?.
      unfold stopping_time_pre_event.
      destruct (rt x).
      - destruct (Nat.eq_dec n0 n).
        + left; congruence.
        + right; congruence.
      - right; congruence.
    Defined.

    Definition stopping_time_pre_event_alt_dec (rt:Ts->option nat) (n:nat) :
      dec_pre_event (stopping_time_pre_event_alt rt n)
      := (fun x => match rt x as aa
                        return {match aa with
                                | None => False
                                | Some a => (a <= n)%nat
                                end} + {~ match aa with
                                          | None => False
                                          | Some a => (a <= n)%nat
                                          end}
                  with
                  | None => right (fun x => x)
                  | Some a => le_dec a n
                end).


    Definition is_stopping_time (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts)
      := forall n, sa_sigma (SigmaAlgebra := sas n) (stopping_time_pre_event rt n).

    Definition is_stopping_time_alt (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts)
      := forall n, sa_sigma (SigmaAlgebra := sas n) (stopping_time_pre_event_alt rt n).

    (* For filtrations, the two definitions coincide *)
    Lemma is_stopping_time_as_alt  (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts) {filt:IsFiltration sas}:
      is_stopping_time rt sas <-> is_stopping_time_alt rt sas.
    Proof.
      unfold is_stopping_time, stopping_time_pre_event, is_stopping_time_alt, stopping_time_pre_event_alt.
      split; intros HH n.
      - assert (pre_event_equiv
                  (fun x : Ts => match rt x with
                              | Some a => (a <= n)%nat
                              | None => False
                              end)
                  (pre_list_union (map (fun k => (fun x : Ts => rt x = Some k)) (seq 0 (S n))))).
        {
          unfold pre_list_union.
          split; intros ?.
          - match_option_in H; [| tauto].
            exists (fun x0 => rt x0 = Some n0).
            split; trivial.
            apply in_map_iff.
            eexists; split; trivial.
            apply in_seq.
            lia.
          - destruct H as [? [??]].
            apply in_map_iff in H.
            destruct H as [?[??]].
            apply in_seq in H1.
            subst.
            rewrite H0.
            lia.
        }
        eapply sa_proper; try eapply H.
        apply sa_pre_list_union; intros.
        apply in_map_iff in H0.
        destruct H0 as [? [??]].
        apply in_seq in H1.
        subst.
        eapply (is_filtration_le _ x0).
        + lia.
        + apply HH.
      - destruct n.
        + eapply sa_proper; try eapply HH; intros ?.
          destruct (rt x); try intuition congruence.
          split; intros HH2.
          * invcs HH2.
            reflexivity.
          * apply le_n_0_eq in HH2; congruence.
        + generalize (HH (S n)); intros HH1.
          generalize (HH n); intros HH2.
          apply sa_complement in HH2.
          apply filt in HH2.
          eapply sa_proper; [| eapply sa_inter; [exact HH1 | exact HH2]].
          intros ?.
          unfold pre_event_inter, pre_event_complement.
          destruct (rt x); split; intros HH3.
          * invcs HH3; lia.
          * f_equal.
            lia.
          * discriminate.
          * tauto.
    Qed.

    Example is_stopping_time_constant (c:option nat) (sas: nat -> SigmaAlgebra Ts)
      : is_stopping_time (const c) sas.
    Proof.
      intros ?.
      unfold stopping_time_pre_event, const.
      apply sa_sigma_const.
      destruct c.
      - destruct (le_dec n0 n); try tauto.
      - tauto.
    Qed.
    
    Lemma is_stopping_time_adapted (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts) :
      is_stopping_time rt sas ->
      IsAdapted borel_sa (fun n => EventIndicator (stopping_time_pre_event_dec rt n)) sas.
    Proof.
      intros ??.
      apply EventIndicator_pre_rv.
      apply H.
    Qed.    

    Lemma is_adapted_stopping_time (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts) :
      IsAdapted borel_sa (fun n => EventIndicator (stopping_time_pre_event_dec rt n)) sas ->
      is_stopping_time rt sas.
    Proof.
      intros ??.
      specialize (H n).
      red in H.
      generalize (H (exist _ _ (borel_singleton 1))).
      apply sa_proper; intros ?.
      unfold EventIndicator.
      unfold event_preimage; simpl.
      unfold pre_event_singleton.
      destruct (stopping_time_pre_event_dec rt n x)
      ; intuition lra.
    Qed.

    Definition lift2_min (x y : option nat)
      := match x, y with
         | None, None => None
         | Some a, None => Some a
         | None, Some b => Some b
         | Some a, Some b => Some (min a b)
         end.
    
    Lemma is_stopping_time_min
          (rt1 rt2:Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          {filt:IsFiltration sas}:
      is_stopping_time rt1 sas ->
      is_stopping_time rt2 sas ->
      is_stopping_time (fun x => lift2_min (rt1 x) (rt2 x)) sas.
    Proof.
      intros s1 s2.
      apply is_stopping_time_as_alt in s1; trivial.
      apply is_stopping_time_as_alt in s2; trivial.
      apply is_stopping_time_as_alt; trivial; intros n.
      unfold is_stopping_time_alt in *.
      specialize (s1 n); specialize (s2 n); intros.
      eapply sa_proper; [| eapply sa_union; [exact s1 | exact s2]].
      intros ?.
      unfold stopping_time_pre_event_alt, pre_event_inter, pre_event_union.
      destruct (rt1 x); destruct (rt2 x); simpl; try tauto.
      destruct (Nat.min_spec_le n0 n1) as [[??]|[??]]; rewrite H0
      ; intuition.
    Qed.

    Lemma is_stopping_time_max
          (rt1 rt2:Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          {filt:IsFiltration sas}:
      is_stopping_time rt1 sas ->
      is_stopping_time rt2 sas ->
      is_stopping_time (fun x => lift2 max (rt1 x) (rt2 x)) sas.
    Proof.
      intros s1 s2.
      apply is_stopping_time_as_alt in s1; trivial.
      apply is_stopping_time_as_alt in s2; trivial.
      apply is_stopping_time_as_alt; trivial; intros n.
      unfold is_stopping_time_alt in *.
      specialize (s1 n); specialize (s2 n); intros.
      eapply sa_proper; [| eapply sa_inter; [exact s1 | exact s2]].
      intros ?.
      unfold stopping_time_pre_event_alt, pre_event_inter, pre_event_union.
      destruct (rt1 x); destruct (rt2 x); simpl; try tauto.
      destruct (Nat.max_spec_le n0 n1) as [[??]|[??]]; rewrite H0
      ; intuition.
    Qed.

    Lemma is_stopping_time_plus
          (rt1 rt2:Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          {filt:IsFiltration sas}:
      is_stopping_time rt1 sas ->
      is_stopping_time rt2 sas ->
      is_stopping_time (fun x => lift2 plus (rt1 x) (rt2 x)) sas.
    Proof.
      intros s1 s2 n.
      unfold is_stopping_time, stopping_time_pre_event in *.

      assert (pre_event_equiv (fun x : Ts => lift2 Init.Nat.add (rt1 x) (rt2 x) = Some n)
                              (pre_list_union (map (fun k => (pre_event_inter
                                                             (fun x : Ts => rt1 x = Some k)
                                                             (fun x : Ts => rt2 x = Some (n-k)%nat)))
                                                   (seq 0 (S n))))).
      {
        split; intros HH.
        - red.
          unfold lift2 in HH.
          repeat match_option_in HH.
          invcs HH.
          exists ((fun k : nat =>
                pre_event_inter (fun x0 : Ts => rt1 x0 = Some k)
                                (fun x0 : Ts => rt2 x0 = Some (n0 + n1 - k)%nat)) n0).
          split.
          + apply in_map_iff.
            eexists; split; [reflexivity |].
            apply in_seq.
            lia.
          + red.
            split; trivial.
            rewrite eqq0.
            f_equal.
            lia.
        - destruct HH as [? [??]].
          apply in_map_iff in H.
          destruct H as [? [??]]; subst.
          apply in_seq in H1.
          destruct H0 as [??].
          rewrite H, H0; simpl.
          f_equal; lia.
      }
      eapply sa_proper; try apply H.
      apply sa_pre_list_union; intros.
      apply in_map_iff in H0.
      destruct H0 as [? [??]]; subst.
      apply in_seq in H1.
      apply sa_inter.
      + eapply (is_filtration_le _ x0); [lia | eauto].
      + eapply (is_filtration_le _ (n - x0)); [lia | eauto].
    Qed.

    Definition past_before_sa_sigma (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts)
               (a:pre_event Ts) : Prop
      := forall n, sa_sigma (SigmaAlgebra:=sas n) (pre_event_inter a (stopping_time_pre_event rt n)).

    Program Global Instance past_before_sa  (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts)
            (stop:is_stopping_time rt sas)
      :
      SigmaAlgebra Ts
      := {|
        sa_sigma := past_before_sa_sigma rt sas
      |} .
    Next Obligation.
      intros n.
      rewrite pre_event_inter_comm.
      rewrite pre_event_inter_countable_union_distr.
      apply sa_countable_union; intros.
      rewrite pre_event_inter_comm.
      apply H.
    Qed.
    Next Obligation.
      intros n.

      assert (eqq:pre_event_equiv (pre_event_inter (pre_event_complement A) (stopping_time_pre_event rt n))
                              (pre_event_diff (stopping_time_pre_event rt n) (pre_event_inter A (stopping_time_pre_event rt n))))
             by firstorder.
      rewrite eqq.
      apply sa_diff.
      - apply stop.
      - apply H.
    Qed.
    Next Obligation.
      intros ?.
      rewrite pre_event_inter_true_l.
      apply stop.
    Qed.
    
    Lemma past_before_stopping_sa_sigma
          (rt:Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          (stop:is_stopping_time rt sas) :
      forall n, sa_sigma (SigmaAlgebra:=past_before_sa rt sas stop) (stopping_time_pre_event rt n).
    Proof.
      intros n k.
      destruct (Nat.eq_dec n k).
      - specialize (stop n).
        subst.
        now rewrite pre_event_inter_self.
      - eapply sa_proper; try eapply sa_none.
        unfold pre_event_inter, pre_event_none.
        intros ?.
        split; [| tauto].
        unfold stopping_time_pre_event, stopping_time_pre_event.
        intros [??]; congruence.
    Qed.

    Lemma past_before_sa_le (rt1 rt2:Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          {filt: IsFiltration sas}
          (stop1:is_stopping_time rt1 sas)
          (stop2:is_stopping_time rt2 sas) :
      (forall x, match rt1 x, rt2 x with
           | Some a, Some b => (a <= b)%nat
           | Some _, None => True
           | None, Some _ => False
           | None, None => True
            end) ->
      sa_sub (past_before_sa rt1 sas stop1) (past_before_sa rt2 sas stop2).
    Proof.
      intros rtle x.
      simpl; unfold past_before_sa_sigma; intros sax n.
      assert (eqq:pre_event_equiv
                    (pre_event_inter x (stopping_time_pre_event rt2 n))
                    (pre_list_union (map (fun k =>
                                            (pre_event_inter
                                               x
                                               (pre_event_inter
                                                  (stopping_time_pre_event rt1 k)
                                                  (stopping_time_pre_event rt2 n))))
                                         (seq 0 (S n))))).
      {
        intros ?.
        split.
        - intros [??].
          red.
          specialize (rtle x0).
          repeat match_option_in rtle; try congruence; try tauto.
          red in H0.
          rewrite eqq0 in H0.
          invcs H0.

          exists ((fun k : nat =>
                pre_event_inter
                  x
                  (pre_event_inter
                     (stopping_time_pre_event rt1 k)
                     (stopping_time_pre_event rt2 n))) n0).
          split.
          + apply in_map_iff.
            eexists; split; trivial.
            apply in_seq; lia.
          + red.
            split; trivial.
            split; trivial.
        - intros [? [??]].
          apply in_map_iff in H.
          destruct H as [? [??]]; subst.
          destruct H0 as [?[??]].
          split; trivial.
      }
      rewrite eqq.
      apply sa_pre_list_union; intros ??.
      apply in_map_iff in H.
      destruct H as [? [??]]; subst.
      apply in_seq in H0.
      rewrite pre_event_inter_assoc.
      apply sa_inter.
      - generalize (sax x1).
        apply is_filtration_le; trivial.
        lia.
      - apply stop2.
    Qed.

    Lemma past_before_sa_eq_in (rt1 rt2:Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          {filt: IsFiltration sas}
          (stop1:is_stopping_time rt1 sas)
          (stop2:is_stopping_time rt2 sas) :
      sa_sigma (SigmaAlgebra:=past_before_sa rt1 sas stop1) (fun x => rt1 x = rt2 x).
    Proof.
      simpl.
      red; intros n.
      assert (eqq: pre_event_equiv
                     (pre_event_inter (fun x : Ts => rt1 x = rt2 x) (stopping_time_pre_event rt1 n))
                     (pre_event_inter
                        (stopping_time_pre_event rt1 n)
                        (stopping_time_pre_event rt2 n))).
      {
        unfold pre_event_inter, stopping_time_pre_event.
        intros ?; intuition congruence.
      }
      rewrite eqq.
      apply sa_inter.
      - apply stop1.
      - apply stop2.
    Qed.

    Lemma past_before_sa_eq_in' (rt1 rt2:Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          {filt: IsFiltration sas}
          (stop1:is_stopping_time rt1 sas)
          (stop2:is_stopping_time rt2 sas) :
      sa_sigma (SigmaAlgebra:=past_before_sa rt2 sas stop2) (fun x => rt1 x = rt2 x).
    Proof.
      generalize (past_before_sa_eq_in rt2 rt1 sas stop2 stop1).
      apply sa_proper.
      intros ?; intuition.
    Qed.

    Definition opt_nat_as_Rbar (n:option nat) : Rbar.Rbar
      := match n with
         | Some a => Rbar.Finite (INR a)
         | None => Rbar.p_infty
         end.

    Lemma Rabs_INR_lt_1_eq a b :
      Rabs (INR a - INR b) < 1 -> a = b.
    Proof.
      unfold Rabs.
      match_destr; intros.
      - assert (INR a < INR b) by lra.
        apply INR_lt in H0.
        assert (INR b < INR a + 1) by lra.
        rewrite <- S_INR in H1.
        apply INR_lt in H1.
        lia.
      - assert (INR b <= INR a) by lra.
        apply INR_le in H0.
        assert (INR a < INR b + 1) by lra.
        rewrite <- S_INR in H1.
        apply INR_lt in H1.
        lia.
    Qed.

    Lemma is_stopping_time_lim (rtn:nat->Ts->option nat)
          (sas: nat -> SigmaAlgebra Ts)
          {filt: IsFiltration sas}
          (stop:forall n, is_stopping_time (rtn n) sas)
          (rt:Ts->option nat) :
      (forall omega, is_Elim_seq (fun n => (opt_nat_as_Rbar (rtn n omega))) (opt_nat_as_Rbar (rt omega))) ->
      is_stopping_time rt sas.
    Proof.
      intros islim n.
      unfold is_stopping_time in stop.
      unfold stopping_time_pre_event in *.
      generalize (fun k => stop k n); intros stop'.

      assert (eqq1:pre_event_equiv
                (fun x : Ts => rt x = Some n)
                (fun x => Hierarchy.eventually (fun k => rtn k x = Some n))).
      {
        intros x.
        specialize (islim x).
        apply is_Elim_seq_spec in islim.
        split; intros HH.
        + rewrite HH in islim.
          simpl in islim.
          specialize (islim posreal_one).
          revert islim.
          apply eventually_impl.
          apply all_eventually; intros ?.
          case_eq (rtn x0 x); simpl; intros; try tauto.
          f_equal.
          now apply Rabs_INR_lt_1_eq.
        + case_eq (rt x); intros; rewrite H in islim; simpl in *.
          * f_equal.
            specialize (islim posreal_one).
            generalize (eventually_and _ _ islim HH)
            ; intros [??].
            specialize (H0 _ (reflexivity _)).
            destruct H0 as [HH2 eqq].
            rewrite eqq in HH2.
            simpl in HH2.
            symmetry.
            now apply Rabs_INR_lt_1_eq.
          * specialize (islim (INR n)).
            generalize (eventually_and _ _ islim HH)
            ; intros [??].
            specialize (H0 _ (reflexivity _)).
            destruct H0 as [HH2 eqq].
            rewrite eqq in HH2.
            simpl in HH2.
            lra.
      }
      rewrite eqq1; clear eqq1.
      unfold Hierarchy.eventually.
      apply sa_countable_union; intros.
      apply sa_pre_countable_inter; intros.

      assert (eqq2:pre_event_equiv
                (fun x : Ts => (n0 <= n1)%nat -> rtn n1 x = Some n)
                (pre_event_union (pre_event_complement (fun _ => n0 <= n1))%nat (fun x => rtn n1 x = Some n))).
      {
        intros ?.
        unfold pre_event_union, pre_event_complement.
        split; intros.
        - destruct (le_dec n0 n1); eauto.
        - destruct H; tauto.
      }
      rewrite eqq2; clear eqq2.
      apply sa_union.
      - apply sa_complement.
        apply sa_sigma_const.
        destruct (le_dec n0 n1); tauto.
      - apply stop'.
    Qed.
    
  End stopping_times.

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

  Definition martingale_transform (H X : nat -> Ts -> R) (n:nat) : Ts -> R
    := match n with
       | 0%nat => const 0
       | S m => rvsum (fun k => rvmult (H (S k)) (rvminus (X (S k)) (X k))) m
       end.

  Global Instance martingale_transform_rv  (H X : nat -> Ts -> R)
         {rvH:forall n, RandomVariable dom borel_sa (H n)}
         {rvX:forall n, RandomVariable dom borel_sa (X n)} : 
    forall n : nat, RandomVariable dom borel_sa (martingale_transform H X n).
  Proof.
    intros [| n]; simpl; 
    typeclasses eauto.
  Qed.

  Global Instance martingale_transform_isfe  (H X : nat -> Ts -> R)
         {isfe0:IsFiniteExpectation prts (X 0%nat)}
         {isfe:forall n, IsFiniteExpectation prts (rvmult (H (S n)) (rvminus (X (S n)) (X n)))}
         {rvH:forall n, RandomVariable dom borel_sa (H n)}
         {rvX:forall n, RandomVariable dom borel_sa (X n)} :
    forall n : nat, IsFiniteExpectation prts (martingale_transform H X n).
  Proof.
    intros [| n]; simpl; trivial.
    typeclasses eauto.
    apply IsFiniteExpectation_sum; trivial.
    typeclasses eauto.
  Qed.

  Global Instance martingale_transform_adapted (H X : nat -> Ts -> R) sas
         {adapt:IsAdapted borel_sa X sas}
         {filt:IsFiltration sas} :
    is_predictable H sas ->
    IsAdapted borel_sa (martingale_transform H X) sas.
  Proof.
    intros is_pre [|n]; simpl.
    - typeclasses eauto. 
    - apply rvsum_rv_loc; intros.
      apply rvmult_rv.
      + generalize (is_pre m).
        apply RandomVariable_proper_le; try reflexivity.
        apply is_filtration_le; trivial.
        lia.
      + apply rvminus_rv.
        * generalize (adapt (S m)).
          apply RandomVariable_proper_le; try reflexivity.
          apply is_filtration_le; trivial.
          lia.
        * generalize (adapt m).
          apply RandomVariable_proper_le; try reflexivity.
          apply is_filtration_le; trivial.
          lia.
  Qed.

  Lemma martingale_transform_predictable_martingale
        (H X : nat -> Ts -> R) (sas:nat->SigmaAlgebra Ts)
        {adaptX:IsAdapted borel_sa X sas}
        {filt:IsFiltration sas}
        {sub : IsSubAlgebras dom sas}
        {rvH:forall n, RandomVariable dom borel_sa (H n)}
        {rvX:forall n, RandomVariable dom borel_sa (X n)}
        {rv:forall n : nat, RandomVariable dom borel_sa (martingale_transform H X n)}
        {isfeX:forall n, IsFiniteExpectation prts (X n)}
        {isfeS:forall n, IsFiniteExpectation prts (rvmult (H (S n)) (rvminus (X (S n)) (X n)))}
        {isfe : forall n : nat, IsFiniteExpectation prts (martingale_transform H X n)}
        {adapt:IsAdapted borel_sa (martingale_transform H X) sas}
        (predict: is_predictable H sas)
        {mart:IsMartingale eq X sas} :
    IsMartingale eq (martingale_transform H X) sas.
  Proof.
    intros [|n]; simpl.
    - cut (almostR2 prts eq (const 0)
                    (FiniteConditionalExpectation prts (sub 0%nat)
                                                  (rvmult (H 1%nat) (rvminus (X 1%nat) (X 0%nat))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub 0%nat)).
        apply FiniteCondexp_proper.
        apply all_almost; intros ?; unfold rvsum; simpl.
        now rewrite Hierarchy.sum_O.
      }

      cut (almostR2 prts eq (const 0)
                    (rvmult (H 1%nat) (FiniteConditionalExpectation prts (sub 0%nat)
                                                  (rvminus (X 1%nat) (X 0%nat))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub 0%nat)).
        now rewrite FiniteCondexp_factor_out_l.
      }

      cut (almostR2 prts eq (const 0)
                    (rvmult (H 1%nat) (rvminus (FiniteConditionalExpectation prts (sub 0%nat) (X 1%nat))
                                             (FiniteConditionalExpectation prts (sub 0%nat) (X 0%nat))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub 0%nat)).
        apply almostR2_eq_mult_proper; try reflexivity.
        now rewrite FiniteCondexp_minus.
      } 

      rewrite <- (mart 0%nat).
      apply all_almost; intros ?.
      rv_unfold.
      rewrite (FiniteCondexp_id prts (sub 0%nat) (X 0%nat) (rv2:=adaptX 0%nat)).
      lra.
    - cut (almostR2 prts eq (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                    (FiniteConditionalExpectation prts (sub (S n))
                                                  (rvplus (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n) (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n))))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        apply FiniteCondexp_proper.
        apply all_almost; intros ?; unfold rvsum; simpl.
        rewrite Hierarchy.sum_Sn.
        unfold Hierarchy.plus; simpl.
        reflexivity.
      }
      cut (almostR2 prts eq (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                    (rvplus
                       (FiniteConditionalExpectation
                          prts (sub (S n))
                          (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n))
                       (FiniteConditionalExpectation
                          prts (sub (S n))
                          (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n))))))).
      {
        intros HH; etransitivity; try eapply HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        now rewrite FiniteCondexp_plus.
      }

      cut (almostR2 prts eq (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                    (rvplus
                       (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                       (FiniteConditionalExpectation
                          prts (sub (S n))
                          (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n))))))).
      {
        intros HH; etransitivity; try eapply HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        apply almostR2_eq_plus_proper; try reflexivity.
        apply all_almost; intros ?.
        symmetry.
        apply FiniteCondexp_id.
        apply rvsum_rv_loc; intros.
        apply rvmult_rv.
        - generalize (predict m).
          eapply RandomVariable_proper_le; try reflexivity.
          apply is_filtration_le; trivial.
          lia.
        - apply rvminus_rv.
          + generalize (adaptX (S m)).
            eapply RandomVariable_proper_le; try reflexivity.
            apply is_filtration_le; trivial.
            lia.
          + generalize (adaptX m).
            eapply RandomVariable_proper_le; try reflexivity.
            apply is_filtration_le; trivial.
            lia.
      }

      cut (almostR2 prts eq (const 0)
                    (FiniteConditionalExpectation prts (sub (S n))
                                                  (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n)))))).
      {
        apply almost_impl; apply all_almost; intros ??; rv_unfold; lra.
      }

      cut (almostR2 prts eq (const 0)
               (rvmult (H (S (S n))) (FiniteConditionalExpectation prts (sub (S n))
                                                                   (rvminus (X (S (S n))) (X (S n)))))).
      {
        intros HH; etransitivity; try eapply HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        now rewrite FiniteCondexp_factor_out_l.
      }

      cut (almostR2 prts eq (const 0)
                    (rvmult (H (S (S n))) (rvminus (FiniteConditionalExpectation prts (sub (S n)) (X (S (S n))))
                                             (FiniteConditionalExpectation prts (sub (S n)) (X (S n)))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n))).
        apply almostR2_eq_mult_proper; try reflexivity.
        now rewrite FiniteCondexp_minus.
      } 

      rewrite <- (mart (S n)).
      apply all_almost; intros ?.
      rv_unfold.
      rewrite (FiniteCondexp_id prts (sub (S n)) (X (S n)) (rv2:=adaptX (S n))).
      lra.
  Qed.

    Lemma martingale_transform_predictable_sub_martingale
        (H X : nat -> Ts -> R) (sas:nat->SigmaAlgebra Ts)
        {adaptX:IsAdapted borel_sa X sas}
        {filt:IsFiltration sas}
        {sub : IsSubAlgebras dom sas}
        {rvH:forall n, RandomVariable dom borel_sa (H n)}
        {rvX:forall n, RandomVariable dom borel_sa (X n)}
        {rv:forall n : nat, RandomVariable dom borel_sa (martingale_transform H X n)}
        {isfeX:forall n, IsFiniteExpectation prts (X n)}
        {isfeS:forall n, IsFiniteExpectation prts (rvmult (H (S n)) (rvminus (X (S n)) (X n)))}
        {isfe : forall n : nat, IsFiniteExpectation prts (martingale_transform H X n)}
        {adapt:IsAdapted borel_sa (martingale_transform H X) sas}
        (predict: is_predictable H sas)
        (Hpos: forall n, almostR2 prts Rle (const 0) (H n))
        {mart:IsMartingale Rle X sas} :
    IsMartingale Rle (martingale_transform H X) sas.
  Proof.
    intros [|n]; simpl.
    - cut (almostR2 prts Rle (const 0)
                    (FiniteConditionalExpectation prts (sub 0%nat)
                                                  (rvmult (H 1%nat) (rvminus (X 1%nat) (X 0%nat))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub 0%nat)).
        apply FiniteCondexp_ale.
        apply all_almost; intros ?; unfold rvsum; simpl.
        now rewrite Hierarchy.sum_O.
      }

      cut (almostR2 prts Rle (const 0)
                    (rvmult (H 1%nat) (FiniteConditionalExpectation prts (sub 0%nat)
                                                  (rvminus (X 1%nat) (X 0%nat))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub 0%nat)).
        eapply almostR2_subrelation; [apply eq_subrelation; typeclasses eauto| ].
        now rewrite FiniteCondexp_factor_out_l.
      }

      cut (almostR2 prts Rle (const 0)
                    (rvmult (H 1%nat) (rvminus (FiniteConditionalExpectation prts (sub 0%nat) (X 1%nat))
                                             (FiniteConditionalExpectation prts (sub 0%nat) (X 0%nat))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub 0%nat)).
        eapply almostR2_subrelation; [apply eq_subrelation; typeclasses eauto| ].
        apply almostR2_eq_mult_proper; try reflexivity.
        now rewrite FiniteCondexp_minus.
      }

      cut (almostR2 prts Rle (const 0)
                    (rvmult (H 1%nat)
                            (rvminus (FiniteConditionalExpectation prts (sub 0%nat) (X 1%nat))
                                     (X 0%nat)))).
      { 
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub 0%nat)).
        eapply almostR2_subrelation; [apply eq_subrelation; typeclasses eauto| ].
        apply almostR2_eq_mult_proper; try reflexivity.
        apply almostR2_eq_minus_proper; try reflexivity.
        apply all_almost; intros ?.
        now rewrite (FiniteCondexp_id prts (sub 0%nat) (X 0%nat) (rv2:=adaptX 0%nat)).
      }
      
      generalize (mart 0%nat); apply almost_impl.
      generalize (Hpos 1%nat); apply almost_impl.
      apply all_almost; intros ???.
      rv_unfold.
      apply Rmult_le_pos; trivial.
      lra.
    - cut (almostR2 prts Rle (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                    (FiniteConditionalExpectation prts (sub (S n))
                                                  (rvplus (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n) (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n))))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        apply FiniteCondexp_ale.
        apply all_almost; intros ?; unfold rvsum; simpl.
        rewrite Hierarchy.sum_Sn.
        unfold Hierarchy.plus; simpl.
        reflexivity.
      }
      cut (almostR2 prts Rle (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                    (rvplus
                       (FiniteConditionalExpectation
                          prts (sub (S n))
                          (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n))
                       (FiniteConditionalExpectation
                          prts (sub (S n))
                          (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n))))))).
      {
        intros HH; etransitivity; try eapply HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        eapply almostR2_subrelation; [apply eq_subrelation; typeclasses eauto| ].
        now rewrite FiniteCondexp_plus.
      }

      cut (almostR2 prts Rle (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                    (rvplus
                       (rvsum (fun k : nat => rvmult (H (S k)) (rvminus (X (S k)) (X k))) n)
                       (FiniteConditionalExpectation
                          prts (sub (S n))
                          (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n))))))).
      {
        intros HH; etransitivity; try eapply HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        eapply almostR2_subrelation; [apply eq_subrelation; typeclasses eauto| ].

        apply almostR2_eq_plus_proper; try reflexivity.
        apply all_almost; intros ?.
        symmetry.
        apply FiniteCondexp_id.
        apply rvsum_rv_loc; intros.
        apply rvmult_rv.
        - generalize (predict m).
          eapply RandomVariable_proper_le; try reflexivity.
          apply is_filtration_le; trivial.
          lia.
        - apply rvminus_rv.
          + generalize (adaptX (S m)).
            eapply RandomVariable_proper_le; try reflexivity.
            apply is_filtration_le; trivial.
            lia.
          + generalize (adaptX m).
            eapply RandomVariable_proper_le; try reflexivity.
            apply is_filtration_le; trivial.
            lia.
      }

      cut (almostR2 prts Rle (const 0)
                    (FiniteConditionalExpectation prts (sub (S n))
                                                  (rvmult (H (S (S n))) (rvminus (X (S (S n))) (X (S n)))))).
      {
        apply almost_impl; apply all_almost; intros ??; rv_unfold; lra.
      }

      cut (almostR2 prts Rle (const 0)
               (rvmult (H (S (S n))) (FiniteConditionalExpectation prts (sub (S n))
                                                                   (rvminus (X (S (S n))) (X (S n)))))).
      {
        intros HH; etransitivity; try eapply HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n)%nat)).
        eapply almostR2_subrelation; [apply eq_subrelation; typeclasses eauto| ].
        now rewrite FiniteCondexp_factor_out_l.
      }

      cut (almostR2 prts Rle (const 0)
                    (rvmult (H (S (S n))) (rvminus (FiniteConditionalExpectation prts (sub (S n)) (X (S (S n))))
                                             (FiniteConditionalExpectation prts (sub (S n)) (X (S n)))))).
      {
        intros HH; rewrite HH.
        apply (almostR2_prob_space_sa_sub_lift prts (sub (S n))).
        eapply almostR2_subrelation; [apply eq_subrelation; typeclasses eauto| ].
        apply almostR2_eq_mult_proper; try reflexivity.
        now rewrite FiniteCondexp_minus.
      } 

      generalize (mart (S n)); apply almost_impl.
      generalize (Hpos (S (S n))); apply almost_impl.
      apply all_almost; intros ???.
      rv_unfold.
      rewrite (FiniteCondexp_id prts (sub (S n)) (X (S n)) (rv2:=adaptX (S n))).
      apply Rmult_le_pos; trivial.
      lra.
  Qed.

  Lemma martingale_transform_plus (H1 H2 X : nat -> Ts -> R) (k:nat) :
    rv_eq (rvplus (martingale_transform H1 X k) (martingale_transform H2 X k))
          (martingale_transform (fun k' => (rvplus (H1 k') (H2 k'))) X k).
  Proof.
    intros ?.
    unfold martingale_transform.
    rv_unfold.
    unfold rvsum.
    destruct k; simpl.
    - lra.
    - generalize (@Hierarchy.sum_n_plus Hierarchy.R_AbelianGroup
                 (fun n0 : nat => H1 (S n0) a * (X (S n0) a + -1 * X n0 a))
                 (fun n0 : nat => H2 (S n0) a * (X (S n0) a + -1 * X n0 a))
                 k); intros eqq.
      unfold Hierarchy.plus in eqq; simpl in eqq.
      rewrite <- eqq.
      apply (@Hierarchy.sum_n_ext Hierarchy.R_AbelianGroup); intros.
      lra.
  Qed.

  Global Instance martingale_transform_proper :
    Proper (pointwise_relation _ rv_eq ==> pointwise_relation _ rv_eq ==> pointwise_relation _ rv_eq) martingale_transform.
  Proof.
    intros ?? eqq1 ?? eqq2 k ?.
    unfold martingale_transform.
    destruct k; trivial.
    unfold rvsum; simpl.
    apply (@Hierarchy.sum_n_ext Hierarchy.R_AbelianGroup); intros.
    rv_unfold.
    now rewrite eqq1, eqq2.
  Qed.

  Lemma martingale_transform_1 Y n : 
    rv_eq (martingale_transform (fun _ : nat => const 1) Y n) (rvminus (Y n) (Y 0%nat)).
  Proof.
    intros ?.
    unfold martingale_transform.
    rv_unfold; unfold rvsum.
    destruct n.
    - lra.
    - induction n; simpl.
      + rewrite Hierarchy.sum_O.
        lra.
      + rewrite Hierarchy.sum_Sn.
        rewrite IHn.
        unfold Hierarchy.plus; simpl.
        lra.
  Qed.   
  
  Definition hitting_time
             (X : nat -> Ts -> R)
             (B:event borel_sa)
             (a:Ts) : option nat
    := classic_min_of (fun k => B (X k a)).

  Global Instance hitting_time_proper :
      Proper (pointwise_relation _ (pointwise_relation _ eq) ==> event_equiv ==> pointwise_relation _ eq)
             hitting_time.
    Proof.
      intros ???????.
      unfold hitting_time.
      apply classic_min_of_proper; intros ?.
      rewrite H.
      apply H0.
    Qed.

  Lemma hitting_time_is_stop
        (X : nat -> Ts -> R) (sas:nat->SigmaAlgebra Ts)
        {filt:IsFiltration sas}
        {adaptX:IsAdapted borel_sa X sas}
        (B:event borel_sa) : is_stopping_time (hitting_time X B) sas.
  Proof.
    unfold hitting_time.
    intros ?.
    unfold stopping_time_pre_event.
    apply (sa_proper _ (fun x => B (X n x) /\
                                forall k, (k < n)%nat -> ~ B (X k x))).
    - intros ?.
      split; intros HH.
      + case_eq (classic_min_of (fun k : nat => B (X k x))); intros.
        * destruct HH as [??].
          f_equal.
          apply antisymmetry
          ; apply not_lt
          ; intros HH.
          -- eapply classic_min_of_some_first in H; eauto.
          -- specialize (H1 _ HH).
             apply classic_min_of_some in H; eauto.
        * eapply classic_min_of_none in H.
          elim H.
          apply HH.
      + split.
        * now apply classic_min_of_some in HH.
        * now apply classic_min_of_some_first.
    - apply sa_inter.
      + apply adaptX.
      + apply sa_pre_countable_inter; intros.
        destruct (lt_dec n0 n).
        * apply (sa_proper _ (fun x => ~ B (X n0 x))).
          -- intros ?; tauto.
          -- apply sa_complement.
             generalize (adaptX n0 B).
             eapply is_filtration_le; trivial.
             lia.
        * apply (sa_proper _ pre_Ω).
          -- unfold pre_Ω ; intros ?.
             split; try tauto.
          -- apply sa_all.
  Qed.

  Fixpoint hitting_time_n
             (X : nat -> Ts -> R)
             (B:event borel_sa)
             (n:nat)
             (a:Ts) : option nat
    := match n with
       | 0 => hitting_time X B a
       | S m => match hitting_time_n X B m a with
               | None => None
               | Some hitk =>
                   match classic_min_of (fun k => B (X (k + S hitk)%nat a)) with
                   | None => None
                   | Some a => Some (a + S hitk)%nat
                   end
               end
       end.


  Lemma hitting_time_n_is_stop
        (X : nat -> Ts -> R) (sas:nat->SigmaAlgebra Ts)
        {filt:IsFiltration sas}
        {adaptX:IsAdapted borel_sa X sas}
        (B:event borel_sa) n : is_stopping_time (hitting_time_n X B n) sas.
  Proof.
    induction n; simpl.
    - now apply hitting_time_is_stop.
    - intros a.
      unfold stopping_time_pre_event.
      apply (sa_proper _ (fun x =>
                            (exists hitk,
                                (hitk < a)%nat /\
                                 hitting_time_n X B n x = Some hitk /\
                                   classic_min_of (fun k : nat => B (X (k + S hitk)%nat x)) = Some (a-S hitk)%nat))).
      + intros ?.
        split; intros HH.
        * destruct HH as [?[?[??]]].
          rewrite H0, H1.
          f_equal.
          lia.
        * match_option_in HH.
          match_option_in HH.
          invcs HH.
          exists n0; repeat split; trivial.
          -- lia.
          -- rewrite eqq0.
             f_equal; lia.
      + apply sa_countable_union; intros.
        unfold is_stopping_time, stopping_time_pre_event in IHn.
        * destruct (lt_dec n0 a).
          -- apply sa_inter.
             ++ apply sa_sigma_const.
                now left.
             ++ apply sa_inter.
                ** generalize (IHn n0).
                   apply is_filtration_le; trivial.
                   lia.
                ** assert (IsFiltration (fun k : nat => sas (k + S n0)%nat)).
                   {
                     intros ?; apply filt.
                   }
                   assert (IsAdapted borel_sa (fun k : nat => X (k + S n0)%nat) (fun k : nat => sas (k + S n0)%nat)).
                   {
                     intros ?; apply adaptX.
                   } 

                   generalize (hitting_time_is_stop (fun k => X (k + S n0)) (fun k => (sas (k + S n0))) B)%nat
                   ; intros HH.
                   red in HH.
                   unfold is_stopping_time, stopping_time_pre_event, hitting_time in HH.
                   generalize (HH (a - S n0)%nat).
                   assert ((Init.Nat.add (Init.Nat.sub a (S n0)) (S n0)) = a) by lia.
                   now rewrite H1.
          -- apply (sa_proper _ pre_event_none).
             ++ unfold pre_event_none; intros ?; tauto.
             ++ auto with prob.
  Qed.

    Lemma is_stopping_time_compose_incr (sas : nat -> SigmaAlgebra Ts) (t1: Ts -> option nat) (t2 : nat -> Ts -> option nat)
          {filt:IsFiltration sas} :

      is_stopping_time t1 sas ->
      (forall old, is_stopping_time (t2 old) sas) ->
      (forall old n ts, t2 old ts = Some n -> old <= n)%nat ->
      is_stopping_time (fun ts =>
                          match (t1 ts) with
                          | Some old => t2 old ts
                          | None => None
                          end
                       ) sas.
    Proof.
      intros stop1 stop2 incr2 n.
      unfold stopping_time_pre_event.
      apply (sa_proper _ (fun x => exists old, old <= n /\ t1 x = Some old /\ t2 old x = Some n)%nat).
      - intros ?.
        match_destr.
        + split.
          * intros [?[?[??]]].
            now invcs H0.
          * eauto. 
        + split; [| congruence].
          intros [?[?[??]]]; congruence.
      - apply sa_countable_union; intros old.
        destruct (le_dec old n).
        + apply sa_inter.
          * eapply sa_proper; try eapply sa_all.
            firstorder.
          * apply sa_inter.
            -- generalize (stop1 old).
               now apply is_filtration_le.
            -- apply stop2.
        + eapply sa_proper; try eapply sa_none.
          firstorder.
    Qed.
    
    Definition hitting_time_from
               (X : nat -> Ts -> R)
               (old:nat)
               (B:event borel_sa)
               (a:Ts) : option nat
      := match hitting_time (fun k => X (k + old)%nat) B a with
         | None => None
         | Some k => Some (k + old)%nat
         end.

    Global Instance hitting_time_from_proper :
      Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> event_equiv ==> pointwise_relation _ eq)
             hitting_time_from.
    Proof.
      intros ??????????.
      unfold hitting_time_from.
      subst.
      erewrite hitting_time_proper.
      - reflexivity.
      - intros ?; apply H.
      - trivial.
    Qed.

    Lemma hitting_time_from0
          (X : nat -> Ts -> R)
          (B:event borel_sa)
          (a:Ts) :
      hitting_time_from X 0%nat B a = hitting_time X B a.
    Proof.
      unfold hitting_time_from.
      erewrite hitting_time_proper.
      shelve.
      {
        intros ?.
        rewrite plus_0_r.
        reflexivity.
      }
      {
        reflexivity.
      }
      Unshelve.
      match_destr.
      now rewrite plus_0_r.
    Qed.
    
    Lemma hitting_time_from_is_stop
          (X : nat -> Ts -> R) (old:nat) (sas:nat->SigmaAlgebra Ts)
          {filt:IsFiltration sas}
          {adaptX:IsAdapted borel_sa X sas}
          (B:event borel_sa) : is_stopping_time (hitting_time_from X old B) sas.
    Proof.
    unfold hitting_time_from, hitting_time.
    intros ?.
    unfold stopping_time_pre_event.
    destruct (le_dec old n).
    - apply (sa_proper _ (fun x => B (X (n)%nat x) /\
                                forall k, (old <= k < n)%nat -> ~ B (X k x))).
      {
        intros ?.
        split; intros HH.
        - case_eq (classic_min_of (fun k : nat => B (X (k+old)%nat x))); intros.
          + destruct HH as [??].
            f_equal.
            apply antisymmetry
            ; apply not_lt
            ; intros HH.
            * apply (classic_min_of_some_first _ _ H (n-old)); [lia |].
              now replace (n - old + old)%nat with n by lia.
            * specialize (H1 (n0 + old)%nat).
              cut_to H1; [| lia].
             apply classic_min_of_some in H; eauto.
          + eapply classic_min_of_none with (k:=(n-old)%nat) in H.
            elim H.
              replace (n - old + old)%nat with n by lia.
              apply HH.
        - match_option_in HH.
          invcs HH.
          split.
          + now apply classic_min_of_some in eqq.
          + intros.
            generalize (classic_min_of_some_first _ _ eqq (k-old)%nat); intros HH.
            replace (k - old + old)%nat with k in HH by lia.
            apply HH.
            lia.
      }
      apply sa_inter.
      + apply adaptX.
      + apply sa_pre_countable_inter; intros.
        destruct (le_dec old n0).
        {
          destruct (lt_dec n0 n).
          - apply (sa_proper _ (fun x => ~ B (X n0 x))).
            + intros ?; tauto.
            + apply sa_complement.
             generalize (adaptX n0 B).
             eapply is_filtration_le; trivial.
             lia.
          - apply (sa_proper _ pre_Ω).
            + unfold pre_Ω ; intros ?.
              split; try tauto.
            + apply sa_all.
        }
        apply (sa_proper _ pre_Ω).
        * unfold pre_Ω ; intros ?.
          split; try tauto.
        * apply sa_all.
    - apply (sa_proper _ event_none).
      + intros ?.
        split; intros HH; [red in HH; tauto |].
        match_destr_in HH.
        invcs HH.
        lia.
      + apply sa_none.
    Qed.

    Lemma hitting_time_from_ge
          (X : nat -> Ts -> R) (old:nat) (sas:nat->SigmaAlgebra Ts)
          {filt:IsFiltration sas}
          {adaptX:IsAdapted borel_sa X sas}
          (B:event borel_sa) ts (n:nat) :
      hitting_time_from X old B ts = Some n ->
      (old <= n)%nat.
    Proof.
      unfold hitting_time_from.
      match_destr.
      intros HH; invcs HH.
      lia.
    Qed.

    Section doob_upcrossing_times.
      
      Context
        (M : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (M n)}
        {isfe:forall n, IsFiniteExpectation prts (M n)}
        {adapt:IsAdapted borel_sa M sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rle M sas}.
 
    Fixpoint upcrossing_times a b (n:nat) : Ts -> option nat
               := fun ts =>
                    match n with
                    | 0%nat => Some 0%nat
                    | 1%nat => hitting_time M (event_le _ id a) ts
                    | S m => match upcrossing_times a b m ts with
                            | None => None
                            | Some old => if Nat.even m
                                         then hitting_time_from M (S old) (event_le _ id a) ts
                                         else hitting_time_from M (S old) (event_ge _ id b) ts
                                                   
                            end
                    end.

    Lemma upcrossing_times_is_stop a b n : is_stopping_time (upcrossing_times a b n) sas.
    Proof.
      destruct n; simpl.
      - apply is_stopping_time_constant.
      - induction n; simpl.
        + now apply hitting_time_is_stop.
        + apply is_stopping_time_compose_incr; trivial.
          * intros.
            match_destr; apply hitting_time_from_is_stop; trivial.
          * intros.
            match_destr_in H
            ; eapply hitting_time_from_ge in H; eauto; lia.
    Qed.

    (* sup {k | upcrossing_times a b (2*k) <= n} *)
    (* Since upcrossing_times is increasing, 
       and returns an integer, we only need to search the first n items 
       (actually less, but any upper bound works *)
 
    Definition upcrossing_var_expr a b n ts k
      := match upcrossing_times a b (2*k) ts with
         | None => 0%nat
         | Some upn => if le_dec upn n then k else 0%nat
         end.
    
    Definition upcrossing_var a b n (ts:Ts) : R
      := Rmax_list (map INR (map (upcrossing_var_expr a b n ts) (seq 0 n))).

    Global Instance upcrossing_var_nneg a b n : NonnegativeFunction (upcrossing_var a b n).
    Proof.
      unfold upcrossing_var; intros ?.
      destruct n; simpl; try reflexivity.
      match_destr; try reflexivity.
      apply Rmax_l.
    Qed.

    Lemma upcrossing_var_is_nat a b n ts :
      { x | INR x = upcrossing_var a b n ts}.
    Proof.
      unfold upcrossing_var.
      generalize (upcrossing_var_expr a b n ts); intros.
      induction n.
      - simpl.
        exists 0%nat; simpl; trivial.
      - rewrite seq_Sn.
        destruct IHn.
        simpl.
        rewrite map_app; simpl.
        destruct n; [simpl; eauto |].
        rewrite Rmax_list_app.
        + rewrite <- e.
          unfold Rmax.
          match_destr; eauto.
        + simpl; congruence.
    Qed.

    Definition upcrossing_var_nat a b n ts : nat
      := proj1_sig (upcrossing_var_is_nat a b n ts).

(*    Lemma upcrossing_var_times_le a b n :
      forall ts, upcrossing_times a b (2 * (upcrossing_var_nat a b n ts)) <= n.
*)

    Definition upcrossing_bound a b m : Ts -> R
      := EventIndicator 
           (classic_dec
              (pre_union_of_collection
                 (fun k x => (match upcrossing_times a b (2 * k - 1) x with
                                 | Some x => (x < m)%nat
                                 | None => False
                                  end /\
                                   match upcrossing_times a b (2 * k) x with
                                   | Some x => (m <= x)%nat
                                   | None => True
                                   end)))).
            
    Lemma upcrossing_bound_is_predictable a b :
      is_predictable (upcrossing_bound a b) sas.
    Proof.
      intros m.
      unfold upcrossing_bound.
      apply EventIndicator_pre_rv.
      apply sa_countable_union; intros n.
      apply sa_inter.
      +
        apply (sa_proper _
                         (fun x =>
                            exists y, (upcrossing_times a b (2 * n - 1) x) = Some y /\
                                   y <= m)%nat).
        * intros ?.
          { split.
            - intros [? [eqq ?]].
              rewrite eqq; simpl.
              lia.
            - destruct (upcrossing_times a b (2 * n - 1) x); simpl; intros HH.
              + eexists; split; [reflexivity | ]; lia.
              + tauto.
          } 
        * apply sa_countable_union; intros.
          {
            destruct (le_dec n0 m)%nat.
            - apply sa_inter.
              + generalize (upcrossing_times_is_stop a b (2 * n - 1) n0); unfold is_stopping_time, stopping_time_pre_event.
                eapply is_filtration_le; trivial.
              + apply sa_sigma_const; eauto.
            - eapply sa_proper; try eapply sa_none.
              intros ?.
              split; intros; tauto.
          } 
      + apply (sa_proper _
                         (pre_event_complement
                            (fun x =>
                               exists y, (upcrossing_times a b (2 * n) x) = Some y /\
                                      y <= m)%nat)).
        * intros ?.
          { unfold pre_event_complement.
            split.
            - match_destr.
              intros HH.
              destruct (le_dec (S m) n0)%nat; trivial.
              elim HH.
              eexists; split; [reflexivity |].
              lia.
            - destruct (upcrossing_times a b (2 * n) x); simpl; intros HH.
              + intros [? [??]].
                invcs H.
                lia.
              + intros [? [??]]; congruence.
          } 
        *
          apply sa_complement.
          apply sa_countable_union; intros.
          {
           (* generalize (upcrossing_times_is_stop a b (2 * n) n0); unfold is_stopping_time, stopping_time_pre_event. *)
            
            destruct (le_dec n0 m)%nat.
            - apply sa_inter.
              + generalize (upcrossing_times_is_stop a b (2 * n) n0); unfold is_stopping_time, stopping_time_pre_event.
                eapply is_filtration_le; trivial.
              + apply sa_sigma_const; lia.
            - eapply sa_proper; try eapply sa_none.
              intros ?.
              split; intros; try tauto.
          } 
    Qed.


    Global Instance upcrossing_bound_rv a b n :
      RandomVariable dom borel_sa (upcrossing_bound a b n).
    Proof.
      destruct n.
      - unfold upcrossing_bound; simpl.
        apply EventIndicator_pre_rv.
        apply sa_countable_union; intros.
        apply sa_inter.
        + eapply sa_proper; try apply sa_none.
          intros ?; split; unfold pre_event_none; try tauto.
          match_destr; lia.
        + eapply sa_proper; try apply sa_all.
          intros ?; split; unfold pre_Ω; try tauto.
          match_destr; lia.
      - generalize (upcrossing_bound_is_predictable a b n).
        apply RandomVariable_proper_le; try reflexivity.
        apply sub.
    Qed.      

    Lemma plus_self_even x : Nat.even (x + x)%nat = true.
    Proof.
      induction x; simpl; trivial.
      destruct x; simpl; trivial.
      rewrite <- IHx.
      f_equal.
      lia.
    Qed.

    Lemma plus_self_and_one_odd x : Nat.even (x + S x)%nat = false.
    Proof.
      replace (x + S x)%nat with (S (x + x))%nat by lia.
      rewrite Nat.even_succ.
      rewrite <- NPeano.Nat.negb_even.
      now rewrite plus_self_even.
    Qed.

    (*
    Lemma upcrossing_transform_part_nneg a b a0 :
      a < b ->
      forall n0,
        0 <= upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0).
    Proof.
      intros altb; intros.
      unfold upcrossing_bound.
      unfold EventIndicator.
      match_destr; [| lra].
      field_simplify.
      destruct p as [? [??]].
      match_option_in H; [| tauto].
      destruct x; [simpl in *; lia |].
      replace (2 * S x - 1)%nat with (x + S x)%nat in eqq by lia.
      replace (2 * S x)%nat with  (S (x + S x))%nat in H0 by lia.
      simpl in H0.
      rewrite eqq in H0.
      rewrite plus_self_and_one_odd in H0.
      rewrite NPeano.Nat.add_succ_r in H0, eqq.
      simpl in H0, eqq.
      destruct x; simpl in eqq.
      - unfold hitting_time, classic_min_of in eqq.
        match_destr_in eqq.
        destruct s as [?[??]].
        simpl in *.
        invcs eqq.
        unfold id in *.
        unfold hitting_time_from, hitting_time, classic_min_of in H0.
        destruct (classic_min_of_sumbool
                    (fun k : nat => event_ge borel_sa (fun x : R => x) b (M (k + S n) a0))).
        + destruct s as [? [??]]; simpl in *.
          assert (n <= n0 <= x + n)%nat by lia.
          destruct (Nat.eq_dec n n0).
          * subst.
          destruct x; simpl in *.
          * admit.
          * specialize (n2 (n0- S n))%nat.
            cut_to n2; try lia.
            replace (n0 - S n + S n)%nat with n0 in n2.
            

          
        
        match_option_in H0.
        + unfold hitting_time_from in eqq.
          match_option_in eqq.
          invcs eqq.
          unfold hitting_time, classic_min_of in eqq0.
          match_destr_in eqq0.
          destruct s as [? [??]]; simpl in *.
          invcs eqq0.
          specialize (n2 (n0 - S n))%nat.
          assert (n0 <= n3 + n)%nat by lia.
          admit.
          assert (n <= n0)%nat by lia.
          
          

          
          n0 - n3 <= n <= n0
                          
                          destruct n3.
          -- simpl in *.
             assert (n = n0) by lia.
             subst.
             lra.
          -- specialize (n2 (n0 - S n))%nat.
             cut_to n2; try lia.
             replace (n0 - S n + S n)%nat with n0 in n2.
             
             
             
      - rewrite plus_self_and_one_odd in H0.
        unfold hitting_time_from, hitting_time, classic_min_of in H0.
        destruct (classic_min_of_sumbool (fun k : nat => event_ge borel_sa id b (M (k + S n) a0))).
        + destruct s as [? [??]]; simpl in *.
          unfold id in *.
          replace (x + S x)%nat with (S (x + x))%nat in eqq by lia.
          match_option_in eqq.
          match_option_in eqq0.
          rewrite plus_self_even in eqq.
          rewrite Nat.even_succ, <- NPeano.Nat.negb_even, plus_self_even in eqq0.
          simpl in eqq0.

          rewrite 
     *)

    Lemma upcrossing_times_even_ge_some a b k0 a0 :
      match upcrossing_times a b (2 * S k0) a0 with
      | Some x => M x a0 >= b
      | None => True
      end.
    Proof.
      intros.
      induction k0.
      - match_case; intros.
        + replace (2 * 1)%nat with (2)%nat in H by lia.
          simpl in H.
          match_case_in H; intros; rewrite H0 in H; try congruence.
          unfold hitting_time_from in H.
          match_case_in H; intros; rewrite H1 in H; try congruence.
          invcs H.
          unfold hitting_time in H1.
          apply classic_min_of_some in H1.
          simpl in H1.
          now unfold id in H1.
      - match_case; intros; simpl in H; match_case_in H; intros;rewrite H0 in H; try congruence.
        + match_case_in H; intros.
          * match_case_in H1; intros; try lia.
            rewrite H2 in H1.
            replace (k0 + S (S (k0 + 0)))%nat with (S (S (2 * k0)))%nat in H2 by lia.
            invcs H2.
            replace (k0 + (k0 + 0))%nat with (k0 + k0)%nat in H1 by lia.
            rewrite Nat.even_succ in H1.
            unfold Nat.odd in H1.
            generalize (plus_self_even k0); intros.
            now rewrite H2 in H1.
          * rewrite H1 in H.
            unfold hitting_time_from in H.
            match_case_in H; intros; rewrite H2 in H; try congruence.
            invcs H.
            unfold hitting_time in H2.
            apply classic_min_of_some in H2.
            simpl in H2.
            now unfold id in H2.
    Qed.

    Lemma upcrossing_times_odd_le_some a b k0 a0 :
      match upcrossing_times a b (2 * S k0 - 1) a0 with
      | Some x => M x a0 <= a
      | None => True
      end.
    Proof.
      intros.
      induction k0.
      - match_case; intros.
        + replace (2 * 1)%nat with (2)%nat in H by lia.
          simpl in H.
          unfold hitting_time in H.
          apply classic_min_of_some in H.
          simpl in H.
          now unfold id in H.
      - match_case; intros; simpl in H; match_case_in H; intros;rewrite H0 in H; try congruence.
        + unfold hitting_time in H.
          apply classic_min_of_some in H.
          simpl in H.
          now unfold id in H.
        + replace  (k0 + S (S (k0 + 0)))%nat with ((S k0) + (S k0))%nat in H0 by lia.
          match_case_in H; intros; rewrite H1 in H; try congruence.
          rewrite <- H0 in H.
          generalize (plus_self_even (S k0)); intros.
          rewrite H2 in H.
          unfold hitting_time_from in H.
          match_case_in H; intros; rewrite H3 in H; try congruence.
          invcs H.
          unfold hitting_time in H3.
          apply classic_min_of_some in H3.
          simpl in H3.
          now unfold id in H3.
    Qed.

    Lemma upcrossing_times_even_ge a b k0 a0 n :
      (upcrossing_var_expr a b (S n) a0 (S k0) > 0)%nat ->
      match upcrossing_times a b (2 * S k0) a0 with
      | Some x => M x a0 >= b
      | None => False
      end.
    Proof.
      intros.
      generalize (upcrossing_times_even_ge_some a b k0 a0); intros.
      match_case; intros.
      - now rewrite H1 in H0.
      - unfold upcrossing_var_expr in H.
        match_case_in H; intros; rewrite H1 in H; lia.
    Qed.
    
    Lemma upcrossing_times_none a b k a0 :
      upcrossing_times a b k a0 = None ->
      upcrossing_times a b (S k) a0 = None.
    Proof.
      intros.
      simpl.
      rewrite H.
      match_destr; try lia.
    Qed.

    Lemma upcrossing_times_none_plus a b k h a0 :
      upcrossing_times a b k a0 = None ->
      upcrossing_times a b (S k + h)%nat a0 = None.
    Proof.
      intros.
      induction h.
      - replace (S k + 0)%nat with (S k) by lia.
        now apply upcrossing_times_none.
      - replace (S k + S h)%nat with (S (S k + h)) by lia.
        apply upcrossing_times_none; try lia; easy.
    Qed.

    Lemma upcrossing_times_some a b k a0 n0 n1:
      (k > 0)%nat ->
      upcrossing_times a b k a0 = Some n0 ->
      upcrossing_times a b (S k) a0 = Some n1 ->
      (n0 < n1)%nat.
    Proof.
      intros.
      simpl in *.
      destruct k; try lia.
      rewrite H0 in H1.
      match_destr_in H1; unfold hitting_time_from in H1;
        match_destr_in H1; invcs H1; lia.
    Qed.

    Lemma upcrossing_times_some_plus a b k a0 n0 h:
      (k > 0)%nat ->
      upcrossing_times a b k a0 = Some n0 ->
      match upcrossing_times a b (S k + h)%nat a0 with
      | Some n1 => (n0 < n1)%nat
      | _ => True
      end.
    Proof.
      intros.
      induction h.
      - replace (S k + 0)%nat with (S k) by lia.
        match_case; intros.
        apply (upcrossing_times_some a b k a0); trivial.
      - replace (S k + S h)%nat with (S (S k + h)) by lia.
        match_case; intros.
        match_case_in IHh; intros.
        + rewrite H2 in IHh.
          eapply lt_trans.
          apply IHh.
          apply upcrossing_times_some with (n0 := n1) in H1; trivial; try lia.
        + apply  upcrossing_times_none in H2; try lia.
          congruence.
    Qed.                                                  

    Lemma upcrossing_times_some_S a b k a0 n0:
      (k > 0)%nat ->
      upcrossing_times a b (S k) a0 = Some n0 ->
      exists n1,
        upcrossing_times a b k a0 = Some n1.
    Proof.
      intros.
      simpl in H0.
      match_destr_in H0; try lia.
      match_destr_in H0.
      now exists n.
    Qed.

    Lemma upcrossing_times_some2 a b k a0 n0 n1:
      (k > 0)%nat ->
      upcrossing_times a b k a0 = Some n0 ->
      upcrossing_times a b (S (S k)) a0 = Some n1 ->
      (n0 < n1)%nat.
    Proof.
      intros.
      generalize (upcrossing_times_some_S a b (S k) a0 n1); intros.
      cut_to H2; try lia; trivial.
      destruct H2.
      generalize (upcrossing_times_some a b k a0 n0 x H H0 H2); intros.
      generalize (upcrossing_times_some a b (S k) a0 x n1); intros.
      cut_to H4; try lia; trivial.      
    Qed.

    Lemma upcrossing_times_odd_le a b k0 a0 n :
      (upcrossing_var_expr a b (S n) a0 (S k0) > 0)%nat ->
      match upcrossing_times a b (2 * S k0 - 1) a0 with
      | Some x => M x a0 <= a
      | None => False
      end.
    Proof.
      intros.
      generalize (upcrossing_times_odd_le_some a b k0 a0); intros.      
      match_case; intros.
      - now rewrite H1 in H0.
      - unfold upcrossing_var_expr in H.
        match_case_in H; intros; rewrite H2 in H; try lia.
        apply upcrossing_times_none in H1; try lia.
        replace (S (2 * S k0 - 1)) with (2 * S k0)%nat in H1 by lia.
        congruence.
    Qed.

    Lemma upcrossing_var_expr_0 a b n a0 k :
      (0 < k)%nat ->
      (upcrossing_var_expr a b (S n) a0 k = 0)%nat ->
      (upcrossing_var_expr a b (S n) a0 (S k) = 0)%nat.
    Proof.
      intros.
      unfold upcrossing_var_expr in *.
      match_case_in H0; intros; rewrite H1 in H0.
      - match_case_in H0; intros; rewrite H2 in H0; try lia.
        assert (n0 > S n)%nat by lia.
        match_case; intros.
        generalize (upcrossing_times_some2 a b (2 * k)%nat a0 n0 n2); intros.
        replace (S (S (2 * k))) with (2 * S k)%nat in H5 by lia.
        cut_to H5; try lia; trivial.
        match_destr; try lra; try lia.
      - generalize (upcrossing_times_none a b (2 * k)%nat a0); intros.
        cut_to H2; try lia; trivial.
        generalize (upcrossing_times_none a b (S (2 * k)) a0); intros.
        cut_to H3; try lia; trivial.
        replace (2 * S k)%nat with (S (S (2 * k))) by lia.
        now rewrite H3.
   Qed.

    Lemma upcrossing_var_expr_gt0 a b n a0 k :
      (upcrossing_var_expr a b (S n) a0 (S k) > 0)%nat ->
      forall h,
        (S h <= S k)%nat ->
        (upcrossing_var_expr a b (S n) a0 (S h) > 0)%nat.
    Proof.
      intros.
      case_eq (upcrossing_var_expr a b (S n) a0 (S h)); intros; try lia.
      assert (forall hh, (upcrossing_var_expr a b (S n) a0 ((S h)+hh)%nat = 0)%nat).
      {
        intros; induction hh.
        - now replace (S h + 0)%nat with (S h) by lia.
        - replace (S h + S hh)%nat with (S (S h + hh)) by lia.
          apply upcrossing_var_expr_0; try lia.
      }
      specialize (H2 (S k - S h)%nat).
      replace (S h + (S k - S h))%nat with (S k) in H2 by lia.
      lia.
    Qed.

    Lemma upcrossing_bound_range a b a0 k :
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        forall n, (N1 < n <= N2)%nat ->
                  upcrossing_bound a b n a0 = 1
      | _, _ => True
      end.
     Proof.
       match_case; intros.
       match_case; intros.       
       unfold upcrossing_bound.
       unfold EventIndicator.
       match_destr.
       unfold pre_union_of_collection in n2.
       assert (
          (exists n : nat,
          match upcrossing_times a b (2 * n - 1) a0 with
          | Some x => (x < n1)%nat
          | None => False
          end /\
          match upcrossing_times a b (2 * n) a0 with
          | Some x => (n1 <= x)%nat
          | None => True
          end)).
       {
         exists k.
         rewrite H.
         split; try lia.
         rewrite H0; try lia.
       }
       easy.
     Qed.

     Lemma upcrossing_times_monotonic_l a b a0 n0 n1 m0 m1 :
       (m0 > 0)%nat ->
       upcrossing_times a b m0 a0 = Some n0 ->
       upcrossing_times a b m1 a0 = Some n1 ->
       (m0 < m1)%nat -> (n0 < n1)%nat.
     Proof.
       intros.
       generalize (upcrossing_times_some_plus a b m0 a0 n0 (m1-m0-1) H H0); intros.
       match_case_in H3; intros; rewrite H4 in H3.
       - replace (S m0 + (m1 - m0 - 1))%nat with (m1) in H4 by lia.
         rewrite H4 in H1.
         now invcs H1.
      - replace (S m0 + (m1 - m0 - 1))%nat with (m1) in H4 by lia.
        congruence.
     Qed.

     Lemma upcrossing_times_monotonic a b a0 n0 n1 m0 m1 :
       (m0 > 0)%nat -> (m1 > 0)%nat ->
       upcrossing_times a b m0 a0 = Some n0 ->
       upcrossing_times a b m1 a0 = Some n1 ->
       (m0 < m1)%nat <-> (n0 < n1)%nat.
     Proof.
       intros.
       split.
       - now apply (upcrossing_times_monotonic_l a b a0).
       - contrapose.
         intros.
         assert (m1 <= m0)%nat by lia.
         destruct (lt_dec m1 m0).
         + generalize (upcrossing_times_monotonic_l a b a0 n1 n0 m1 m0 ); intros.
           cut_to H5; trivial.
           lia.
         + assert (m1 = m0)%nat by lia.
           rewrite H5 in H2.
           rewrite H2 in H1.
           invcs H1.
           lia.
    Qed.

    Lemma upcrossing_bound_range0 a b a0 k :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k) a0, upcrossing_times a b (2 * k + 1) a0 with 
      | Some N2, Some N1 =>
        forall n, (n > N2)%nat /\ (n <= N1)%nat ->
                  upcrossing_bound a b n a0 = 0
      | Some N2, None =>
        forall n, (n > N2)%nat ->
                  upcrossing_bound a b n a0 = 0                                                
      | _, _ => True
      end.
    Proof.
      intros.
      unfold upcrossing_bound, EventIndicator.
      match_case; intros.
      match_case; intros.
      - match_destr.
        destruct p as [? [? ?]].
        destruct H2.
        match_case_in H3; intros; rewrite H6 in H3; try easy.
        assert (n2 < n0)%nat by lia.
        assert (2 * x - 1 < 2 * k + 1)%nat.
        {
          generalize (upcrossing_times_monotonic a b a0 n2 n0); intros; trivial; try lia.
          specialize (H8 (2 * x - 1)%nat (2 * k + 1)%nat).
          apply H8; trivial; try lia.
          admit.
        }
        match_case_in H4; intros; rewrite H9 in H4.
        + assert (n < n3)%nat by lia.
          assert (2 * k < 2 * x)%nat.
          {
            generalize (upcrossing_times_monotonic a b a0 n n3); intros; trivial; try lia.
            specialize (H11 (2 * k)%nat (2 * x)%nat).
            apply H11; trivial; try lia.
            admit.
          }
          lia.
        + assert (2 * x < 2 * k + 1)%nat by lia.
          apply upcrossing_times_none_plus with (h := (2 * k - 2 * x)%nat) in H9.
          replace (S (2 * x) + (2 * k - 2*x))%nat with (2 * k + 1)%nat in H9 by lia.
          congruence.
     - match_destr.
       destruct p as [? [? ?]].
       match_case_in H3; intros; rewrite H5 in H3; try easy.
       match_case_in H4; intros; rewrite H6 in H4.
       + assert (n < n2)%nat by lia.
         assert (2 * k < 2 * x)%nat.
         {
           generalize (upcrossing_times_monotonic a b a0 n n2); intros.
           specialize (H8 (2 * k)%nat (2 * x)%nat).
           apply H8; trivial; try lia.
           admit.
         }
         assert (2 * k + 1 < 2*x)%nat by lia.
         apply upcrossing_times_none_plus with (h := (2 * x - 2 * k - 2)%nat) in H1; try lia.
         replace (S (2 * k + 1) + (2 * x - 2 * k - 2))%nat with (2 * x)%nat in H1 by lia.
         congruence.
       + destruct (lt_dec (2 * x)%nat (2 *  k)%nat).
         * apply upcrossing_times_none_plus with (h := (2 * k - 2 * x - 1)%nat) in H6.
           replace (S (2 * x) + (2 * k - 2* x-1))%nat with (2 * k)%nat in H6 by lia.
           congruence.
         * destruct (lt_dec (2 * k)%nat (2 * x)%nat).
           -- assert (2 * k + 1 <= 2 * x - 1)%nat by lia.
              destruct (lt_dec (2 * k + 1)%nat (2 * x - 1)%nat).
              ++ apply upcrossing_times_none_plus with (h := (2 * x - 2 * k - 3)%nat) in H1; try lia.
                 replace (S (2 * k + 1) + (2 * x - 2* k - 3))%nat with (2 * x - 1)%nat in H1 by lia.
                 congruence.
              ++ assert ( 2 * k + 1 = 2  * x - 1)%nat by lia.
                 rewrite H8 in H1; congruence.
           -- assert (2 * x = 2 * k)%nat by lia.
              rewrite H7 in H6; congruence.
       Admitted.

    Lemma upcrossing_bound_range0_init a b a0 :
      match upcrossing_times a b (1%nat) a0 with
      | Some N1 =>
        forall n, (n <= N1)%nat ->
                  upcrossing_bound a b n a0 = 0
      | None =>
        forall n, upcrossing_bound a b n a0 = 0                                                
      end.
    Proof.
      match_case; intros.
      - unfold upcrossing_bound, EventIndicator.
        match_destr.
        destruct p as [? [? ?]].
        match_case_in H1; intros; rewrite H3 in H1; try easy.
        match_case_in H2; intros; rewrite H4 in H2.
        + assert (n1 < n)%nat by lia.
          assert (2 * x - 1 < 1)%nat.
          {
            generalize (upcrossing_times_monotonic a b a0 n1 n); intros.
            specialize (H6 (2 * x - 1)%nat 1%nat).
            apply H6; trivial; try lia.
            admit.
          }
          assert (x = 0)%nat by lia.
          replace (2 * x)%nat with (0%nat) in H4 by lia.
          replace (2 * x - 1)%nat with (0%nat) in H3 by lia.
          assert (n1 < n2)%nat by lia.
          rewrite H3 in H4.
          invcs H4.
          lia.
        + assert (n1 < n)%nat by lia.
          assert (2 * x - 1 < 1)%nat.
          {
             generalize (upcrossing_times_monotonic a b a0 n1 n); intros.
             specialize (H6 (2 * x - 1)%nat 1%nat).
             apply H6; trivial; try lia.
             admit.
          }
          assert (x = 0)%nat by lia.
          replace (2 * x)%nat with (0%nat) in H4 by lia.
          replace (2 * x - 1)%nat with (0%nat) in H3 by lia.
          congruence.
     -  unfold upcrossing_bound, EventIndicator.
        match_destr.
        destruct p as [? [? ?]].
        match_case_in H0; intros; rewrite H2 in H0; try easy.
        match_case_in H1; intros; rewrite H3 in H1.
        + destruct x.
          * replace (2 * 0 - 1)%nat with (0%nat) in H2 by lia.
            replace (2 * 0)%nat with (0%nat) in H3 by lia.
            rewrite H3 in H2.
            assert (n0 < n1)%nat by lia.
            invcs H2.
            lia.
          * apply upcrossing_times_none_plus with (h := (2 * S x - 2)%nat) in H; try lia.
            replace (2 + ( 2*S x - 2))%nat with (2 * S x)%nat in H by lia.
            congruence.
        + destruct x.
          * replace (2 * 0)%nat with (0%nat) in H3 by lia.
            replace (2 * 0 - 1)%nat with (0%nat) in H2 by lia.
            congruence.
          * destruct x.
            -- replace (2 * 1 - 1)%nat with (1)%nat in H2 by lia.
               congruence.
            -- apply upcrossing_times_none_plus with (h := (2 * S (S x) - 3)%nat) in H; try lia.
               replace (2 + (2 * S (S x) - 3))%nat with (2 * S (S x) - 1)%nat in H by lia.
               congruence.
    Admitted.

    Lemma upcrossing_bound_range10 a b a0 n :
      (forall k,
        match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
        | Some N1, Some N2 =>
          (n <= N1)%nat /\ (n > N2)%nat
        | _, _ => False
        end) -> upcrossing_bound a b n a0 = 0.
     Proof.
       intros.
       unfold upcrossing_bound, EventIndicator.
       match_destr.
       unfold pre_union_of_collection in p.
       destruct p as [? [? ?]].
       specialize (H x).
       match_case_in H0; intros; rewrite H2 in H0; rewrite H2 in H.
       - match_case_in H1; intros; rewrite H3 in H1.
         + rewrite H3 in H.
           lia.
         + rewrite H3 in H; easy.
       - match_case_in H1; intros; rewrite H3 in H1; easy.
     Qed.



     Lemma telescope_sum (f : nat -> R) n h :
       @Hierarchy.sum_n_m 
         Hierarchy.R_AbelianGroup
         (fun n1 : nat => f (S n1) + -1 * f n1) n (n + h)%nat = f (n + (S h))%nat - f n.
     Proof.
       induction h.
       - replace (n + 0)%nat with (n) by lia.
         rewrite Hierarchy.sum_n_n.
         replace (n + 1)%nat with (S n) by lia.
         lra.
       - replace (n + S h)%nat with (S (n + h)) by lia.
         rewrite Hierarchy.sum_n_Sm; try lia.
         rewrite IHh.
         unfold Hierarchy.plus; simpl.
         replace (S (n + h)) with (n + S h)%nat by lia.
         replace (S (n + S h)) with (n + S (S h))%nat by lia.
         lra.
      Qed.
         
    Lemma transform_upcrossing a b a0 k :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N2-1)%nat = M N2 a0 - M N1 a0
      | _, _ => True
      end.
    Proof.
      intros.
       match_case; intros.
       match_case; intros.
       assert (up: (n < n0)%nat).
       {
         apply (upcrossing_times_some a b (2 * k - 1) a0); try lia; trivial.
         now replace (S (2 * k - 1)) with (2 * k)%nat by lia.
       }
       rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
           (b := fun n1 => M (S n1) a0 + -1 * M n1 a0).
       - pose (h := (n0 - 1 - n)%nat).
         replace (n0-1)%nat with (n + h)%nat by lia.
         rewrite (telescope_sum (fun n => M n a0)).
         now replace (n + S h)%nat with n0 by lia.
       - intros.
         generalize (upcrossing_bound_range a b a0 k); intros.
         rewrite H0, H1 in H3.
         specialize (H3 (S k0)).
         rewrite H3; try lra; try lia.
     Qed.
      
    Lemma transform_upcrossing2 a b a0 k N3 :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        (N1 < N3 <= N2)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N3-1)%nat = M N3 a0 - M N1 a0
      | _, _ => True
      end.
    Proof.
      intros.
       match_case; intros.
       match_case; intros.
       assert (up: (n < n0)%nat).
       {
         apply (upcrossing_times_some a b (2 * k - 1) a0); try lia; trivial.
         now replace (S (2 * k - 1)) with (2 * k)%nat by lia.
       }
       rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
           (b := fun n1 => M (S n1) a0 + -1 * M n1 a0).
       - pose (h := (N3 - 1 - n)%nat).
         replace (N3-1)%nat with (n + h)%nat by lia.
         rewrite (telescope_sum (fun n => M n a0)).
         now replace (n + S h)%nat with N3 by lia.
       - intros.
         generalize (upcrossing_bound_range a b a0 k); intros.
         rewrite H0, H1 in H4.
         specialize (H4 (S k0)).
         rewrite H4; try lra; try lia.
     Qed.

    Lemma transform_upcrossing_pos a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        (N1 < N3 <= N2)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N3-1)%nat >= 0
      | _, _ => True
      end.
    Proof.
      intros.
      generalize (transform_upcrossing2 a b a0 k N3 H); intros.
      match_case; intros.
      match_case; intros.
      rewrite H2, H3 in H1.
      rewrite H1; trivial.
      assert (M n a0 = a).
      {
        generalize (upcrossing_times_odd_le_some a b (k-1)%nat a0); intros.
        replace (S (k - 1)) with k in H5 by lia.
        rewrite H2 in H5.
        specialize (H0 n a0).
        lra.
      }
      specialize (H0 N3 a0); lra.
    Qed.

    Lemma upcrossing_bound_transform_ge_Sn a b n : 
      a < b ->
      (forall m x, M m x >= a) ->
      rv_le (rvscale (b-a) (upcrossing_var a b (S n))) (martingale_transform (upcrossing_bound a b) M (S n)).
    Proof.
      intros altb Mgea ?.
      unfold martingale_transform.
      rv_unfold.
      generalize (Rmax_list_In (map INR (map (upcrossing_var_expr a b (S n) a0) (seq 0 (S n)))))
      ; intros HH.
      cut_to HH; [| simpl; congruence].
      generalize (Rmax_spec_map (map (upcrossing_var_expr a b (S n) a0) (seq 0 (S n))) INR)
      ; intros Hin'.
      apply in_map_iff in HH.
      destruct HH as [kk [??]].
      rewrite <- H in Hin'.
      unfold upcrossing_var.
      rewrite <- H.
      apply in_map_iff in H0.
      destruct H0 as [k [??]].
      apply in_seq in H1.
      destruct H1 as [_ ?].
      assert (k <= n)%nat by lia; clear H1.
      assert (Hin : forall x1,
                 (x1 <= n)%nat ->
                 (upcrossing_var_expr a b (S n) a0 x1 <= kk)%nat).
      {
        intros.
        apply INR_le.
        subst.
        apply Hin'.
        apply in_map.
        apply in_seq; lia.
      }
      clear Hin' H.
      subst.
      unfold rvsum.
      assert (forall k0 n,
               (upcrossing_var_expr a b (S n) a0 (S k0) > 0)%nat ->                 
               match upcrossing_times a b (2 * (S k0)) a0, upcrossing_times a b (2 * (S k0) - 1) a0 with
               | Some N2, Some N1 => M N2 a0 - M N1 a0 >= b-a
               | _, _ => False
               end) .
      {
        intros.
        generalize (upcrossing_times_even_ge a b k0 a0 n0 H)
        ; generalize (upcrossing_times_odd_le a b k0 a0 n0 H).
        repeat match_option.
        lra.
      }
      assert ( 
          @Hierarchy.sum_n 
            Hierarchy.R_AbelianGroup
            (fun n0 : nat => 
                             upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0)) n
          >=
          @Hierarchy.sum_n_m 
            Hierarchy.R_AbelianGroup
            (fun k0 =>
               match upcrossing_times a b (2 * k0) a0, upcrossing_times a b (2 * k0 - 1) a0 with
              | Some N2, Some N1 => M N2 a0 - M N1 a0
              | _, _ => 0
              end) 
            1 
            (upcrossing_var_expr a b (S n) a0 k)).
      {
        unfold upcrossing_bound.
        
        admit.
      }
      apply Rge_le.
      eapply Rge_trans.
      apply H0.
      destruct k.
      - simpl.
        unfold upcrossing_var_expr.
        replace (2  * 0)%nat with (0)%nat by lia.
        simpl.
        rewrite Hierarchy.sum_n_m_zero; try lia.
        unfold Hierarchy.zero; simpl.
        lra.
      - destruct  (le_dec 1 (upcrossing_var_expr a b (S n) a0 (S k))).
        + transitivity
            (@Hierarchy.sum_n_m Hierarchy.R_AbelianGroup
                                (fun _ => b - a)
                                1 (upcrossing_var_expr a b (S n) a0 (S k))).
          * apply Rle_ge.
            apply sum_n_m_le_loc; trivial.
            intros.
            specialize (H (n0-1)%nat n).
            replace (S (n0 -1)) with (n0) in H by lia.
            assert (upcrossing_var_expr a b (S n) a0 n0 > 0)%nat.
            {
              unfold upcrossing_var_expr in H1.
              match_destr_in H1 ; try lia.
              match_destr_in H1; try lia.
              replace (n0) with (S (n0 - 1)) by lia.
              apply upcrossing_var_expr_gt0 with (k := k); try lia.
            }
            specialize (H H3).
            match_option.
            -- rewrite eqq in H.
               match_option.
               ++ rewrite eqq0 in H.
                  lra.
               ++ now rewrite eqq0 in H.
            -- now rewrite eqq in H.
          * rewrite Hierarchy.sum_n_m_const.
            replace (S (upcrossing_var_expr a b (S n) a0 (S k)) - 1)%nat with (upcrossing_var_expr a b (S n) a0 (S k)) by lia.
            lra.
        + assert ((upcrossing_var_expr a b (S n) a0 (S k))%nat = 0%nat) by lia.
          rewrite H1.
          simpl.
          rewrite Rmult_0_r.
          rewrite Hierarchy.sum_n_m_zero; try lia.
          unfold Hierarchy.zero; simpl; lra.
    Admitted.

    Lemma upcrossing_bound_transform_ge a b n : a < b ->
      (forall m x, M m x >= a) -> 
      rv_le (rvscale (b-a) (upcrossing_var a b n)) (martingale_transform (upcrossing_bound a b) M n).
    Proof.
      intros Mgea ??.
      destruct n.
      - simpl.
        unfold upcrossing_var; simpl.
        rv_unfold; lra.
      - now apply upcrossing_bound_transform_ge_Sn.
    Qed.

    End doob_upcrossing_times.

    Section doob_upcrossing_ineq.

      Local Existing Instance Rbar_le_pre.

      Context
        (M : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (M n)}
        {isfe:forall n, IsFiniteExpectation prts (M n)}
        {adapt:IsAdapted borel_sa M sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rle M sas}.

      Theorem upcrossing_inequality a b n :
        a < b ->
        Rbar_le (Rbar_mult (b-a) (NonnegExpectation (upcrossing_var M a b (S n))))
                (Rbar_minus (NonnegExpectation (pos_fun_part (rvminus (M (S n)) (const a))))
                            (NonnegExpectation (pos_fun_part (rvminus (M 0%nat) (const a))))).
      Proof.
        intros altb.
      pose (ϕ x := Rmax (x - a) 0 + a).
      pose (Y n := fun x => ϕ (M n x)).

      assert (ϕconvex:(forall c x y : R, convex ϕ c x y)).
      {
        unfold ϕ.
        intros ????.
        unfold Rmax.
        repeat match_destr; try lra.
        - field_simplify.
          replace (y-a+a) with y by lra.
          assert (a < y) by lra.
          transitivity (c*a + (1-c)*a); try lra.
          apply Rplus_le_compat_l.
          apply Rmult_le_compat_l; try lra.
        - field_simplify.
          replace (x-a+a) with x by lra.
          assert (a < x) by lra.
          transitivity (c*a + (1-c)*a); try lra.
          apply Rplus_le_compat_r.
          apply Rmult_le_compat_l; try lra.
        - replace (x-a+a) with x by lra.
          replace (y-a+a) with y by lra.
          assert (a < x) by lra.
          assert (a < y) by lra.
          transitivity (c*a + (1-c)*a); try lra.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; try lra.
          + apply Rmult_le_compat_l; try lra.
        - rewrite Rplus_0_l.
          unfold Rminus.
          rewrite Rplus_assoc.
          rewrite Rplus_opp_l.
          rewrite Rplus_0_r.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; lra.
          + apply Rmult_le_compat_l; lra.
        - rewrite Rplus_0_l.
          unfold Rminus.
          repeat rewrite Rplus_assoc.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; lra.
          + rewrite Rplus_opp_l.
            lra.
        - rewrite Rplus_0_l.
          unfold Rminus.
          repeat rewrite Rplus_assoc.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; lra.
          + rewrite Rplus_opp_l.
            rewrite Rplus_0_r.
            apply Rmult_le_compat_l; lra.
      } 

      assert (ϕincr : forall x y : R, x <= y -> ϕ x <= ϕ y).
      {
        unfold ϕ.
        intros ???.
        unfold Rmax.
        repeat match_destr; lra.
      }

      assert (adaptY:IsAdapted borel_sa Y sas).
      {
        apply is_adapted_convex; trivial.
      } 

      assert (rvY:forall n : nat, RandomVariable dom borel_sa (Y n)).
      {
        intros m.
        generalize (adaptY m).
        apply RandomVariable_proper_le; try reflexivity.
        apply sub.
      } 

      assert (isfeY:forall n : nat, IsFiniteExpectation prts (Y n)).
      {
        intros m.
        unfold Y, ϕ.
        assert (rv1:RandomVariable dom borel_sa (fun x : Ts => M m x - a)).
        {
          apply rvplus_rv.
          - generalize (adapt m).
            apply RandomVariable_proper_le; try reflexivity.
            apply sub.
          - apply rvconst.
        } 

        apply IsFiniteExpectation_plus.
        - apply positive_part_rv; trivial.
        - apply rvconst.
        - apply IsFiniteExpectation_max; trivial.
          + apply rvconst.
          + apply IsFiniteExpectation_plus; trivial.
            * apply rvconst.
            * apply IsFiniteExpectation_const.
          + apply IsFiniteExpectation_const.
        - apply IsFiniteExpectation_const.
      } 

      assert (martY:IsMartingale Rle Y sas).
      {
        eapply is_sub_martingale_incr_convex; eauto.
      } 

      assert (upcross_same:forall m, rv_eq (upcrossing_var Y a b m) (upcrossing_var M a b m)).
      {
        intros m ts.
        unfold Y, ϕ.
        unfold upcrossing_var.
        f_equal.
        repeat rewrite map_map.
        apply map_ext_in; intros c ?.
        apply in_seq in H.
        assert (c < m)%nat by lia.
        f_equal.

        unfold upcrossing_var_expr.

        assert (eqq:forall c, upcrossing_times Y a b c ts = upcrossing_times M a b c ts).
        {

          assert (forall old, hitting_time_from Y old (event_ge borel_sa id b) ts =
                           hitting_time_from M old (event_ge borel_sa id b) ts).
          {
            unfold hitting_time_from; intros.
            unfold hitting_time.
            repeat match_option.
            - do 2 f_equal.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id; intros HHM1.
              generalize (classic_min_of_some_first _ _ eqq); simpl; unfold id; intros HHY2.
              generalize (classic_min_of_some_first _ _ eqq0); simpl; unfold id; intros HHM2.
              apply antisymmetry
              ; apply not_lt
              ; intros HH.
              + apply (HHY2 _ HH).
                unfold Y, ϕ.
                unfold Rmax.
                match_destr; lra.
              + apply (HHM2 _ HH).
                unfold Y, ϕ in HHY1.
                unfold Rmax in HHY1.
                match_destr_in HHY1; lra.
            - generalize (classic_min_of_none _ eqq0 n0); simpl; unfold id
              ; intros HHM.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              match_destr_in HHY1; try lra.
            - generalize (classic_min_of_none _ eqq n0); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id
              ; intros HHM1.
              match_destr_in HHY1; try lra.
          }
          
          assert (forall old, hitting_time_from Y old (event_le borel_sa id a) ts =
                           hitting_time_from M old (event_le borel_sa id a) ts).
          {
            unfold hitting_time_from; intros.
            unfold hitting_time.
            repeat match_option.
            - do 2 f_equal.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id; intros HHM1.
              generalize (classic_min_of_some_first _ _ eqq); simpl; unfold id; intros HHY2.
              generalize (classic_min_of_some_first _ _ eqq0); simpl; unfold id; intros HHM2.
              apply antisymmetry
              ; apply not_lt
              ; intros HH.
              + apply (HHY2 _ HH).
                unfold Y, ϕ.
                unfold Rmax.
                match_destr; lra.
              + apply (HHM2 _ HH).
                unfold Y, ϕ in HHY1.
                unfold Rmax in HHY1.
                match_destr_in HHY1; lra.
            - generalize (classic_min_of_none _ eqq0 n0); simpl; unfold id
              ; intros HHM.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              match_destr_in HHY1; try lra.
            - generalize (classic_min_of_none _ eqq n0); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id
              ; intros HHM1.
              match_destr_in HHY1; try lra.
          } 
          intros x; destruct x; simpl; trivial.
          induction x; simpl.
          - specialize (H2 0%nat).
            now repeat rewrite hitting_time_from0 in H2.
          - rewrite IHx.
            destruct (match x with
                      | 0%nat => hitting_time M (event_le borel_sa id a) ts
                      | S _ =>
                          match upcrossing_times M a b x ts with
                          | Some old =>
                              if Nat.even x
                              then hitting_time_from M (S old) (event_le borel_sa id a) ts
                              else hitting_time_from M (S old) (event_ge borel_sa id b) ts
                          | None => None
                          end
                      end); trivial.
            destruct (match x with
                      | 0%nat => false
                      | S n' => Nat.even n'
                      end); auto.
        }
        now rewrite eqq.
      }

      apply (Rbar_le_trans _ (Rbar_mult (b - a) (NonnegExpectation (upcrossing_var Y a b (S n))))).
      {
        apply Rbar_mult_le_compat_l; [simpl; lra |].
        apply refl_refl.
        now apply NonnegExpectation_ext.
      }

       assert (isfeb:forall n : nat,
                  IsFiniteExpectation prts
                                      (rvmult (upcrossing_bound Y a b (S n)) (rvminus (Y (S n)) (Y n)))).
      {
        intros.
        unfold upcrossing_bound.
        rewrite rvmult_comm.
        apply IsFiniteExpectation_indicator.
        - typeclasses eauto.
        - 
          generalize (upcrossing_bound_rv Y sas a b (S n0) (event_singleton _ (borel_singleton 1))).
          apply sa_proper.
          intros ?.
          unfold event_preimage, upcrossing_bound; simpl.
          unfold pre_event_singleton, EventIndicator.
          match_destr.
          + tauto.
          + split; try tauto.
            lra.
        - typeclasses eauto.
      } 

      assert (IsAdapted borel_sa (martingale_transform (upcrossing_bound Y a b) Y) sas).
      {
        apply martingale_transform_adapted; trivial.
        now apply upcrossing_bound_is_predictable.
      } 

      generalize (martingale_transform_predictable_sub_martingale
                    (upcrossing_bound Y a b)
                    Y
                    sas); intros martT.
      { cut_to martT.
        shelve.
        - now apply upcrossing_bound_is_predictable.
        - intros.
          apply all_almost; intros.
          unfold const.
          unfold upcrossing_bound, EventIndicator; simpl.
          match_destr; lra.
        - trivial.
      }
      Unshelve.
      assert (Ygea: forall m x, Y m x >= a).
      {
        intros.
        unfold Y, ϕ.
        unfold Rmax.
        match_destr; lra.
      }
      generalize (upcrossing_bound_transform_ge Y sas a b (S n) altb Ygea); intros leup.
      assert (nneg1:NonnegativeFunction (rvscale (b - a) (upcrossing_var Y a b (S n)))).
      {
        apply scale_nneg_nnf.
        - typeclasses eauto.
        - lra.
      }

      generalize (NonnegativeFunction_le_proper _ _ leup nneg1); intros nneg2.
      generalize (NonnegExpectation_le _ _ leup)
      ; intros le2.
      rewrite (NonnegExpectation_scale' _ _) in le2; try lra.
      eapply Rbar_le_trans; try apply le2.

      assert (eqq1:rv_eq (rvminus (Y (S n)) (Y 0%nat))
                    (rvplus
                       ((martingale_transform (fun k => rvminus (const 1) (upcrossing_bound Y a b k)) Y) (S n))
                       ((martingale_transform (upcrossing_bound Y a b) Y) (S n)))).
      {
        rewrite martingale_transform_plus.
        transitivity (martingale_transform
                        (fun k' : nat =>
                           (const 1)) Y 
                        (S n)).
        - rewrite martingale_transform_1.
          reflexivity.
        - apply martingale_transform_proper; try reflexivity.
          intros ??.
          rv_unfold.
          lra.
      }

      assert (isfe2:IsFiniteExpectation _ (rvplus
              (martingale_transform
                 (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y 
                 (S n)) (martingale_transform (upcrossing_bound Y a b) Y (S n)))).
      {
        eapply IsFiniteExpectation_proper.
        - symmetry; apply eqq1.
        - typeclasses eauto.
      } 
      generalize (FiniteExpectation_ext _ _ _ eqq1); intros eqq2.
      rewrite FiniteExpectation_minus in eqq2.
      unfold Y in eqq2 at 1 2.
      unfold ϕ in eqq2 at 1 2.
      assert (isfe3:forall n, IsFiniteExpectation prts (pos_fun_part (rvminus (M n) (const a)))).
      {
        intros.
        - apply IsFiniteExpectation_max; trivial.
          + typeclasses eauto.
          + apply rvconst.
          + apply IsFiniteExpectation_minus; trivial.
            * apply rvconst.
            * apply IsFiniteExpectation_const.
          + apply IsFiniteExpectation_const.
      }
                                                
      assert (eqq3:FiniteExpectation prts (fun x : Ts => Rmax (M (S n) x - a) 0 + a) =
                FiniteExpectation prts (rvplus (pos_fun_part (rvminus (M (S n)) (const a)))
                                               (const a))).
      {
        apply FiniteExpectation_ext; intros ?.
        unfold rvminus, rvplus, rvopp, pos_fun_part, const, rvscale; simpl.
        f_equal.
        f_equal.
        lra.
      }
      rewrite eqq3 in eqq2.
      rewrite (FiniteExpectation_plus _ _) in eqq2. 
      assert (eqq4:FiniteExpectation prts (fun x : Ts => Rmax (M 0 x - a) 0 + a) =
                FiniteExpectation prts (rvplus (pos_fun_part (rvminus (M 0) (const a)))
                                               (const a))).
      {
        apply FiniteExpectation_ext; intros ?.
        unfold rvminus, rvplus, rvopp, pos_fun_part, const, rvscale; simpl.
        f_equal.
        f_equal.
        lra.
      }
      rewrite eqq4 in eqq2.
      rewrite (FiniteExpectation_plus _ _) in eqq2. 
      field_simplify in eqq2.
      rewrite (FiniteNonnegExpectation _ _) in eqq2.
      rewrite (FiniteNonnegExpectation _ _) in eqq2.

      match type of eqq2 with
        ?x = ?y =>
          match goal with
          | [|- Rbar_le ?a ?b] => assert (eqq5:b = x)
          end
      end.
      {
        assert (isfin:forall n, is_finite
                  (NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M n) (const a)) x))).
        {
          intros.
          apply IsFiniteNonnegExpectation.
          typeclasses eauto.
        }
        rewrite <- (isfin (S n)).
        rewrite <- (isfin 0)%nat.
        simpl.
        reflexivity.
      }
      rewrite eqq5, eqq2.

      assert (isfe4:IsFiniteExpectation prts (martingale_transform (upcrossing_bound Y a b) Y (S n))).
      {
        typeclasses eauto.
      } 

      assert (isfe5a: forall n0 : nat,
                 IsFiniteExpectation prts
                                     (rvmult (rvminus (const 1) (upcrossing_bound Y a b (S n0))) (rvminus (Y (S n0)) (Y n0)))).
      { 
        - intros.
          cut (IsFiniteExpectation prts
                                   (rvminus (rvminus (Y (S n0)) (Y n0))
                                            
                                            (rvmult (upcrossing_bound Y a b (S n0)) (rvminus (Y (S n0)) (Y n0))))).
          + apply IsFiniteExpectation_proper; intros ?.
            unfold rvmult, rvminus, rvplus, rvopp, rvscale, const.
            lra.
          + typeclasses eauto.
      } 
      
      assert (isfe5:IsFiniteExpectation
                      prts
                      (martingale_transform
                         (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y 
                         (S n))).
      {
        apply martingale_transform_isfe; trivial.
        - intros.
          typeclasses eauto.
      }
      
      rewrite (FiniteExpectation_plus' _ _ _).
      rewrite (FiniteNonnegExpectation _
                                       (martingale_transform (upcrossing_bound Y a b) Y (S n))).
      cut (Rbar_le
             (Rbar_plus 0
                        (NonnegExpectation (martingale_transform (upcrossing_bound Y a b) Y (S n))))
             (Rbar_plus
                (FiniteExpectation prts
                                   (martingale_transform
                                      (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y 
                                      (S n)))
                (real (NonnegExpectation (martingale_transform (upcrossing_bound Y a b) Y (S n)))))).
      {
        rewrite Rbar_plus_0_l.
        now simpl.
      } 
      apply Rbar_plus_le_compat
      ; [| now rewrite IsFiniteNonnegExpectation; try reflexivity].

      assert (ispredminus1:is_predictable (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) sas).
      {
        red.
        apply is_adapted_minus.
        - apply is_adapted_const.
        - now apply upcrossing_bound_is_predictable.
      } 

      assert (IsAdapted borel_sa
                        (martingale_transform (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y)
                        sas).
      {
        apply martingale_transform_adapted; trivial.
      } 
 

      generalize (martingale_transform_predictable_sub_martingale
                    (fun k => (rvminus (const 1) (upcrossing_bound Y a b k)))
                    Y
                    sas); intros martT1.
      { cut_to martT1.
        shelve.
        - trivial.
        - intros.
          apply all_almost; intros.
          rv_unfold.
          unfold upcrossing_bound, EventIndicator; simpl.
          match_destr; lra.
        - trivial.
      }
      Unshelve.
      generalize (is_sub_martingale_expectation
                    (martingale_transform
                       (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y)
                    sas
                    0
                    (S n)); intros HH.
      cut_to HH; [| lia].
      unfold Rbar_le.
      etransitivity; [etransitivity |]; [| apply HH |].
        - simpl.
          erewrite FiniteExpectation_pf_irrel; try rewrite FiniteExpectation_const.
          reflexivity.
        - right.
          apply FiniteExpectation_pf_irrel.
     Qed.
  End doob_upcrossing_ineq.

  Section mart_conv.

    Local Existing Instance Rbar_le_pre.
    
    Context
      (M : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
      {rv:forall n, RandomVariable dom borel_sa (M n)}
      {isfe:forall n, IsFiniteExpectation prts (M n)}
      {adapt:IsAdapted borel_sa M sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale Rle M sas}.


(*    Lemma upcrossing_var_lim_isfe K a b :
      is_ELimSup_seq (fun n => NonnegExpectation (pos_fun_part (M n))) K ->
      a < b ->
      IsFiniteExpectation prts (rvlim (upcrossing_var M a b)).
    Proof.
      intros.
      unfold rvlim.

      generalize (Fatou (upcrossing_var M a b) _); intros HH.
      
      assert Rbar_le (Rbar_mult (b-a) (NonnegExpectation (upcrossing_var M a b (S n))))
                        (K + Rabs a)).
      {

      U∞[a, b] := limn→∞ Un[a, b].
      
      assert (HH:forall a b n, a < b ->
                Rbar_le (Rbar_mult (b-a) (NonnegExpectation (upcrossing_var M a b (S n))))
                        (K + Rabs a)).
      {
        intros a b n altb.
        rewrite (upcrossing_inequality M sas a b n altb).
        transitivity ((NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M (S n)) (const a)) x))).
        {
          rewrite <- (Rbar_plus_0_r (NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M (S n)) (const a)) x))) at 2.
          apply Rbar_plus_le_compat; try reflexivity.
          rewrite <- Rbar_opp_le.
          rewrite Rbar_opp_involutive.
          simpl Rbar_opp; rewrite Ropp_0.
          apply NonnegExpectation_pos.
        }
        transitivity (NonnegExpectation (rvplus (pos_fun_part (M (S n))) (rvabs (const a)))).
        {
          apply NonnegExpectation_le; intros ?.
          rv_unfold; simpl.
          
          unfold Rmax.
          generalize (Rabs_pos a); intros.
          repeat match_destr; simpl; try lra
          ; unfold Rabs
          ; match_destr; try lra.
        }
        rewrite NonnegExpectation_sum by try typeclasses eauto.
        unfold rvabs, const.
        assert (eqq:(NonnegExpectation (fun _ : Ts => Rabs a)) = Rabs a).
        {
          rewrite <- (NonnegExpectation_const (Rabs a)) with (nnc:=Rabs_pos a).
          apply NonnegExpectation_ext; reflexivity.
        }
        rewrite eqq.
        replace (Finite (K + Rabs a)) with (Rbar_plus K (Rabs a)) by reflexivity.
        apply Rbar_plus_le_compat; try reflexivity.
        red in sup.
        admit.
      }

      
    Theorem martingale_convergence (K:R) :
      is_ELimSup_seq (fun n => NonnegExpectation (pos_fun_part (M n))) K ->
      exists (Minf : Ts -> R),
        RandomVariable dom borel_sa Minf /\
        IsFiniteExpectation prts Minf /\
          almost prts (fun omega => is_Elim_seq (fun n => M n omega) (Minf omega)).
    Proof.
      intros sup.


      assert (isfeU:forall a b, a < b ->
                           IsFiniteExpectation prts (rvlim (upcrossing_var M a b))).
      { 
      
                Rbar_le (Rbar_mult (b-a) (NonnegExpectation (upcrossing_var M a b (S n))))
                        (K + Rabs a)).
      {

      U∞[a, b] := limn→∞ Un[a, b].
      
      assert (HH:forall a b n, a < b ->
                Rbar_le (Rbar_mult (b-a) (NonnegExpectation (upcrossing_var M a b (S n))))
                        (K + Rabs a)).
      {
        intros a b n altb.
        rewrite (upcrossing_inequality M sas a b n altb).
        transitivity ((NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M (S n)) (const a)) x))).
        {
          rewrite <- (Rbar_plus_0_r (NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M (S n)) (const a)) x))) at 2.
          apply Rbar_plus_le_compat; try reflexivity.
          rewrite <- Rbar_opp_le.
          rewrite Rbar_opp_involutive.
          simpl Rbar_opp; rewrite Ropp_0.
          apply NonnegExpectation_pos.
        }
        transitivity (NonnegExpectation (rvplus (pos_fun_part (M (S n))) (rvabs (const a)))).
        {
          apply NonnegExpectation_le; intros ?.
          rv_unfold; simpl.
          
          unfold Rmax.
          generalize (Rabs_pos a); intros.
          repeat match_destr; simpl; try lra
          ; unfold Rabs
          ; match_destr; try lra.
        }
        rewrite NonnegExpectation_sum by try typeclasses eauto.
        unfold rvabs, const.
        assert (eqq:(NonnegExpectation (fun _ : Ts => Rabs a)) = Rabs a).
        {
          rewrite <- (NonnegExpectation_const (Rabs a)) with (nnc:=Rabs_pos a).
          apply NonnegExpectation_ext; reflexivity.
        }
        rewrite eqq.
        replace (Finite (K + Rabs a)) with (Rbar_plus K (Rabs a)) by reflexivity.
        apply Rbar_plus_le_compat; try reflexivity.
        red in sup.
        admit.
      }
      assert (ps_P (fun omega => (ELimInf_seq (fun n => (M n omega))) < (ELimSup_seq (fun n => (M n omega))) )).
          

      
            Theorem upcrossing_inequality a b n :
        a < b ->
        Rbar_le (Rbar_mult (b-a) (NonnegExpectation (upcrossing_var M a b (S n))))
                (Rbar_minus (NonnegExpectation (pos_fun_part (rvminus (M (S n)) (const a))))
                            (NonnegExpectation (pos_fun_part (rvminus (M 0%nat) (const a))))).
      Proof.

        


                (b − a) E Un(a, b) 􏰁 E(Mn − a)+ 􏰁 E Mn+ + a 􏰁 K + a.
      
      
      
    Qed.
    *)
    End mart_conv.

End martingale.

Section levy.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Context (X:Ts -> R)
          {rv:RandomVariable dom borel_sa X}
          {isfe:IsFiniteExpectation prts X}
          (sas : nat -> SigmaAlgebra Ts)
          {sub:IsSubAlgebras dom sas}.

  Definition levy_martingale
    : nat -> Ts -> R
    := fun n => FiniteConditionalExpectation prts (sub n) X.

  Global Instance levy_martingale_rv :
    forall n : nat, RandomVariable dom borel_sa (levy_martingale n).
  Proof.
    intros n.
    unfold levy_martingale.
    generalize (FiniteCondexp_rv prts (sub n) X).
    apply RandomVariable_sa_sub.
    apply sub.
  Qed.


  Global Instance levy_martingale_is_adapted : IsAdapted borel_sa levy_martingale sas.
  Proof.
    intros n.
    unfold levy_martingale.
    apply FiniteCondexp_rv.
  Qed.

  Global Instance levy_martingale_is_martingale {filt:IsFiltration sas} :
    IsMartingale prts eq levy_martingale sas.
  Proof.
    intros n.
    unfold levy_martingale.
    generalize (FiniteCondexp_tower' prts (sub (S n)) (filt n) X)
    ; intros HH.
    apply almostR2_prob_space_sa_sub_lift in HH.
    transitivity (FiniteConditionalExpectation prts (transitivity (filt n) (sub (S n))) X).
    - eapply (almostR2_prob_space_sa_sub_lift prts (sub n)).
      apply (FiniteCondexp_all_proper _ _ _); reflexivity.
    - rewrite <- HH.
      symmetry.
      eapply (almostR2_prob_space_sa_sub_lift prts (sub n)).
      apply (FiniteCondexp_all_proper _ _ _); reflexivity.
  Qed.        

End levy.

Section MartingaleDifferenceSeq.

  Class IsMDS {Ts:Type}
          {dom: SigmaAlgebra Ts}
          {prts: ProbSpace dom} (sas : nat -> SigmaAlgebra Ts) (X : nat -> Ts -> R)
          {adapt : IsAdapted borel_sa X sas}
          {isfe : forall n, IsFiniteExpectation prts (X n)}
          {rv : forall n, RandomVariable dom borel_sa (X n)}
          {filt:IsFiltration sas}
          {sub:IsSubAlgebras dom sas}
    :={
    is_mds : forall n : nat, almostR2 prts eq (const 0%R)
                               (FiniteConditionalExpectation prts (sub n) (X (S n)))
      }.

  Context  {Ts:Type}
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom) (X : nat -> Ts -> R)
          (sas : nat -> SigmaAlgebra Ts)
          {adapt : IsAdapted borel_sa X sas}
          {rv: forall n, RandomVariable dom borel_sa (X n)}
          {isfe:forall n, IsFiniteExpectation prts (X n)}
          {sub:IsSubAlgebras dom sas}
          {filt : IsFiltration sas}.

  Lemma Martingale_diff_IsMDS (Y : nat -> Ts -> R) (rvy : forall n : nat, RandomVariable dom borel_sa (Y n))
        (isfey : forall n : nat, IsFiniteExpectation prts (Y n))
        (adapty : IsAdapted borel_sa Y sas)
        (hy : IsMartingale prts eq Y sas) :
    (forall n : nat, almostR2 prts eq (X (S n)) (rvminus (Y (S n)) (Y n))) ->
    IsMDS sas X.
  Proof.
    intros Hn.
    constructor.
    intros n.
    specialize (Hn n).
    eapply FiniteCondexp_proper with (sub0 := sub n)
                                    (rv1 := rv (S n))
                                    (isfe1 := isfe (S n))
      in Hn.
    apply almost_prob_space_sa_sub_lift in Hn.
    assert (almostR2 (prob_space_sa_sub prts (sub n)) eq
                     (FiniteConditionalExpectation prts (sub n) (rvminus (Y (S n)) (Y n)))
                     (rvminus (FiniteConditionalExpectation prts (sub n) (Y (S n)))
                              (FiniteConditionalExpectation prts (sub n) (Y n)))) by
      apply FiniteCondexp_minus.
    apply almost_prob_space_sa_sub_lift in H.
    unfold IsMartingale in hy.
    specialize (hy n).
    revert hy; apply almost_impl.
    revert Hn; apply almost_impl.
    revert H; apply almost_impl, all_almost; intros ??.
    unfold impl; intros.
    rewrite H0.
    rewrite H.
    rv_unfold. rewrite <- H1.
    rewrite FiniteCondexp_id; try lra; trivial.
  Qed.

End MartingaleDifferenceSeq.

  
