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

  Lemma is_adapted_filtration_pred (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {filt:IsFiltration sas}
        {adapt:IsAdapted borel_sa Y (fun n => sas (pred n))} :
    IsAdapted borel_sa Y sas.
  Proof.
    intros n.
    generalize (adapt n).
    eapply RandomVariable_proper_le; try reflexivity.
    destruct n; simpl.
    - reflexivity.
    - apply filt.
  Qed.

  Lemma is_adapted_filtration_shift k (Y : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {filt:IsFiltration sas}
        {adapt:IsAdapted borel_sa Y (fun n => sas (n - k)%nat)} :
    IsAdapted borel_sa Y sas.
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

    Definition stopping_time_pre_event (rt:Ts->option nat) (n:nat) : pre_event Ts
      := (fun x => match rt x with
                | None => False
                | Some a => (a <= n)%nat
                end).

    Definition stopping_time_pre_event_alt (rt:Ts->option nat) (n:nat) : pre_event Ts
      := fun x => rt x = Some n.

    (*
    Lemma stopping_time_pre_event_alt (rt:Ts->option nat) (n:nat) :
      pre_event_equiv (stopping_time_pre_event rt n)
                      (pre_event_union (fun x => rt x = None)
                                       (pre_union_of_collection
                                          (fun a => (fun x => rt x = Some a /\ a <= n))%nat)).
    Proof.
      unfold stopping_time_pre_event, pre_union_of_collection.
      intros ?.
      split; intros ?.
      - match_case_in H; intros.
        + right.
          rewrite H0 in H.
          eauto.
        + rewrite H0 in H.
          now left.
      - destruct H.
        + destruct (rt x).
        + destruct H as [? [??]].
          now rewrite H.
    Qed.
     *)
    
    Definition stopping_time_pre_event_dec (rt:Ts->option nat) (n:nat) :
      dec_pre_event (stopping_time_pre_event rt n)
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

    Lemma stopping_time_pre_event_alt_dec (rt:Ts->option nat) (n:nat) :
      dec_pre_event (stopping_time_pre_event_alt rt n).
    Proof.
      intros ?.
      unfold stopping_time_pre_event_alt.
      destruct (rt x).
      - destruct (Nat.eq_dec n0 n).
        + left; congruence.
        + right; congruence.
      - right; congruence.
    Defined.

    Definition is_stopping_time (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts)
      := forall n, sa_sigma (SigmaAlgebra := sas n) (stopping_time_pre_event rt n).

    Definition is_stopping_time_alt (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts)
      := forall n, sa_sigma (SigmaAlgebra := sas n) (stopping_time_pre_event_alt rt n).

    Lemma is_stopping_time_as_alt  (rt:Ts->option nat) (sas: nat -> SigmaAlgebra Ts) {filt:IsFiltration sas}:
      is_stopping_time rt sas <-> is_stopping_time_alt rt sas.
    Proof.
      unfold is_stopping_time, stopping_time_pre_event, is_stopping_time_alt, stopping_time_pre_event_alt.
      split; intros HH n.
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
    
    Lemma is_stopping_time_min (rt1 rt2:Ts->option nat) (sas: nat -> SigmaAlgebra Ts) :
      is_stopping_time rt1 sas ->
      is_stopping_time rt2 sas ->
      is_stopping_time (fun x => match rt1 x, rt2 x with
                              | None, None => None
                              | Some a, None => Some a
                              | None, Some b => Some b
                              | Some a, Some b => Some (min a b)
                              end) sas.
    Proof.
      intros s1 s2 ?.
      unfold is_stopping_time in *.
      specialize (s1 n); specialize (s2 n).
      eapply sa_proper; [| eapply sa_union; [exact s1 | exact s2]].
      intros ?.
      unfold stopping_time_pre_event, pre_event_inter, pre_event_union.
      destruct (rt1 x); destruct (rt2 x); simpl; try tauto.
      destruct (Nat.min_spec_le n0 n1) as [[??]|[??]]; rewrite H0
      ; intuition.
    Qed.

    Lemma is_stopping_time_max (rt1 rt2:Ts->option nat) (sas: nat -> SigmaAlgebra Ts) :
      is_stopping_time rt1 sas ->
      is_stopping_time rt2 sas ->
      is_stopping_time (fun x => lift2 max (rt1 x) (rt2 x)) sas.
    Proof.
      intros s1 s2 ?.
      unfold is_stopping_time in *.
      specialize (s1 n); specialize (s2 n).
      eapply sa_proper; [| eapply sa_inter; [exact s1 | exact s2]].
      intros ?.
      unfold stopping_time_pre_event, pre_event_inter, pre_event_union.
      destruct (rt1 x); destruct (rt2 x); simpl; try tauto.
      destruct (Nat.max_spec_le n0 n1) as [[??]|[??]]; rewrite H0
      ; intuition.
    Qed.


    Lemma is_stopping_time_plus (rt1 rt2:Ts->option nat) (sas: nat -> SigmaAlgebra Ts) {filt:IsFiltration sas}:
      is_stopping_time rt1 sas ->
      is_stopping_time rt2 sas ->
      is_stopping_time (fun x => lift2 plus (rt1 x) (rt2 x)) sas.
    Proof.
      intros s1 s2.
      apply is_stopping_time_as_alt in s1; trivial.
      apply is_stopping_time_as_alt in s2; trivial.
      apply is_stopping_time_as_alt; trivial.
      unfold is_stopping_time_alt, stopping_time_pre_event_alt in *.
      intros n.

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

    End stopping_times.
    
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
