Require Import Program.Basics.
Require Import Coquelicot.Coquelicot.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.
Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec.
Require Import Equivalence.
Require Import Classical ClassicalFacts ClassicalChoice.
Require Ensembles.

Require Import Utils DVector.
Import ListNotations.
Require Export Event SigmaAlgebras ProbSpace.
Require Export RandomVariable VectorRandomVariable.
Require Import ClassicalDescription.
Require Import Measures.
Require Import DiscreteProbSpace.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

Section measure_product.

  Context {X Y:Type}.
  Context {A:SigmaAlgebra X}.
  Context {B:SigmaAlgebra Y}.

  Context (α : event A -> Rbar) (meas_α : is_measure α).
  Context (β : event B -> Rbar) (meas_β : is_measure β).
  
  Definition is_measurable_rectangle (ab : pre_event (X*Y)) : Prop
    := exists (a:event A) (b:event B), forall x y, ab (x,y) <-> a x /\ b y.

  Lemma is_measurable_rectangle_none : is_measurable_rectangle pre_event_none.
  Proof.
    exists event_none, event_none.
    unfold event_none, pre_event_none; simpl; tauto.
  Qed.
  
  Program Instance PairSemiAlgebra : SemiAlgebra (X*Y)
    := {|
      salg_in (x:pre_event (X*Y)) := is_measurable_rectangle x
    |}.
  Next Obligation.
    exists pre_Ω.
    exists Ω, Ω; intros; unfold Ω, pre_Ω; simpl.
    tauto.
  Qed.
  Next Obligation.
    destruct H as [a1[b1 ?]]; destruct H0 as [a2[b2 ?]].
    exists (event_inter a1 a2).
    exists (event_inter b1 b2).
    intros.
    split; intros [??].
    - apply H in H1.
      apply H0 in H2.
      repeat split; try apply H1; try apply H2.
    - destruct H1.
      destruct H2.
      split.
      + apply H.
        split; trivial.
      + apply H0.
        split; trivial.
  Qed.
  Next Obligation.
    destruct H as [a1[b1 ?]].
    exists ([(fun ab => event_complement a1 (fst ab) /\ b1 (snd ab))
        ; (fun ab => a1 (fst ab) /\ event_complement b1 (snd ab))
        ; (fun ab => event_complement a1 (fst ab) /\ event_complement b1 (snd ab))]).
    split;[ | split].
    - intros [x y].
      destruct a1; destruct b1; simpl.
      unfold pre_list_union, pre_event_complement.
      specialize (H x y).
      apply not_iff_compat in H.
      simpl in *; split.
      + intros ?.
        apply H in H0.
        apply not_and_or in H0.
        destruct H0.
        * destruct (classic (x1 y)).
          -- eexists; split; [left; reflexivity |].
             now simpl.
          -- eexists; split; [right; right; left; reflexivity |].
             now simpl.
        * destruct (classic (x0 x)).
          -- eexists; split; [right; left; reflexivity |].
             now simpl.
          -- eexists; split; [right; right; left; reflexivity |].
             now simpl.
      + intros [??].
        apply H.
        repeat destruct H0; simpl in *; tauto.
    - repeat constructor; intros ???
      ; destruct a1; destruct b1; simpl in *; firstorder.
    - repeat constructor.
      + exists (event_complement a1), b1; intros; tauto.
      + exists a1, (event_complement b1); intros; tauto.
      + exists (event_complement a1), (event_complement b1); intros; tauto.
  Qed.

  (* this is very classic *)
  Definition measurable_rectangle_pm (ab:salg_set PairSemiAlgebra) : Rbar.
  Proof.
    destruct ab as [? HH].
    simpl in HH.
    unfold is_measurable_rectangle in HH.
    apply IndefiniteDescription.constructive_indefinite_description in HH.
    destruct HH as [a HH].
    apply IndefiniteDescription.constructive_indefinite_description in HH.
    destruct HH as [b HH].
    exact (Rbar_mult (α a) (β b)).
  Defined.

  (* well, at least the definition is meaningful and proper *)
  Lemma measurable_rectangle_pm_proper' ab ab2
        (pf1:is_measurable_rectangle ab) (pf2:is_measurable_rectangle ab2) :
    pre_event_equiv ab ab2 ->
    measurable_rectangle_pm (exist _ ab pf1) = measurable_rectangle_pm (exist _ ab2 pf2).
  Proof.
    intros eqq.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    destruct e as [??].
    destruct e0 as [??].
    destruct pf1 as [? [??]].
    destruct pf2 as [? [??]].

    destruct (classic_event_none_or_has x) as [[??]|?].
    - destruct (classic_event_none_or_has x0) as [[??]|?].
      + destruct (i x9 x10) as [_ ?].
        cut_to H5; [| tauto].
        apply eqq in H5.
        apply i0 in H5.
        destruct H5.
        f_equal.
        * apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i c x10).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i0 in H7.
             tauto.
          -- specialize (i0 c x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i in H7.
             tauto.
        * apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i x9 c).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i0 in H7.
             tauto.
          -- specialize (i0 x9 c).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i in H7.
             tauto.
      + rewrite H4.
        destruct (classic_event_none_or_has x2) as [[??]|?].
        * destruct (classic_event_none_or_has x1) as [[??]|?].
          -- specialize (i0 x11 x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i in H7.
             destruct H7 as [_ HH].
             apply H4 in HH.
             red in HH; tauto.
          -- rewrite H6.
             repeat rewrite measure_none.
             now rewrite Rbar_mult_0_l, Rbar_mult_0_r.
        * rewrite H5.
          repeat rewrite measure_none.
          now repeat rewrite Rbar_mult_0_r.
    - rewrite H3.
      destruct (classic_event_none_or_has x1) as [[??]|?].
      + destruct (classic_event_none_or_has x2) as [[??]|?].
        * destruct (i0 x9 x10) as [_ ?].
          cut_to H6; [| tauto].
          apply eqq in H6.
          apply i in H6.
          destruct H6 as [HH _].
          apply H3 in HH.
          red in HH; tauto.
        * rewrite H5.
          repeat rewrite measure_none.
          now rewrite Rbar_mult_0_l, Rbar_mult_0_r.
      + rewrite H4.
        repeat rewrite measure_none.
        now repeat rewrite Rbar_mult_0_l.
  Qed.
  
  Global Instance measurable_rectangle_pm_proper : Proper (salg_equiv ==> eq) measurable_rectangle_pm.
  Proof.
    intros ???.
    destruct x; destruct y.
    red in H; simpl in H.
    now apply measurable_rectangle_pm_proper'.
  Qed.

  Lemma measurable_rectangle_pm_nneg ab :
    Rbar_le 0 (measurable_rectangle_pm ab).
  Proof.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    apply Rbar_mult_nneg_compat; apply measure_nneg.
  Qed.

  Lemma measurable_rectangle_pm_none :
    measurable_rectangle_pm (exist _ _ is_measurable_rectangle_none) = 0.
  Proof.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    destruct (classic_event_none_or_has x) as [[??]|?].
    - destruct (classic_event_none_or_has x0) as [[??]|?].
      + destruct (i x1 x2) as [_ HH].
        cut_to HH; [| tauto].
        now red in HH.
      + rewrite H0.
        now rewrite measure_none, Rbar_mult_0_r.
    - rewrite H.
      now rewrite measure_none, Rbar_mult_0_l.
  Qed.

  
End measure_product.

