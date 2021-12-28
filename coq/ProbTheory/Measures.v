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
Require Import DiscreteProbSpace.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

Section measure.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Context {T:Type}.
  Context {σ:SigmaAlgebra T}.

  Class is_measure (μ:event σ -> Rbar)
    := mk_measure {
        measure_proper :> Proper (event_equiv ==> eq) μ
      ; measure_none : μ event_none = 0%R
      ; measure_nneg a : Rbar_le 0 (μ a)
      ; measure_countable_disjoint_union (B:nat->event σ) :
        collection_is_pairwise_disjoint B ->
        μ (union_of_collection B) = (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i))
      }.
  
  Lemma measure_list_disjoint_union (μ:event σ -> Rbar) {μ_meas:is_measure μ} (l: list (event σ)) :
    (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
    ForallOrdPairs event_disjoint l ->
    μ (list_union l) = list_Rbar_sum (map μ l).
  Proof.
    intros Hd.
    generalize (measure_countable_disjoint_union (list_collection l ∅)); intros HH.
    cut_to HH.
    - unfold sum_of_probs_equals in HH.
      erewrite measure_proper in HH; [| eapply list_union_union ].
      rewrite HH.
      unfold list_collection.
      apply (seq_sum_list_sum _ _ ∅).
      apply measure_none.
    - apply list_collection_disjoint; trivial.
  Qed.

  Lemma measure_disjoint_union (μ:event σ -> Rbar) {μ_meas:is_measure μ} (a b: event σ) :
    (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
    event_disjoint a b ->
    μ (a ∪ b) = Rbar_plus (μ a) (μ b).
  Proof.
    intros Hd.
    generalize (measure_list_disjoint_union μ [a; b]); intros HH.
    rewrite list_union_cons, list_union_singleton in HH.
    simpl in HH.
    rewrite Rbar_plus_0_r in HH.
    apply HH.
    now repeat constructor.
  Qed.    
  
  Global Instance measure_monotone (μ:event σ -> Rbar) {μ_meas:is_measure μ} :
    Proper (event_sub ==> Rbar_le) μ.
  Proof.
    intros ???.
    rewrite (sub_diff_union _ _ H).
    rewrite measure_disjoint_union; trivial.
    - rewrite <- (Rbar_plus_0_l (μ x)) at 1.
      apply Rbar_plus_le_compat; try reflexivity.
      apply measure_nneg.
    - firstorder.
  Qed.

  Lemma measure_countable_sub_union (μ:event σ -> Rbar) {μ_meas:is_measure μ} (B:nat->event σ) :
    Rbar_le (μ (union_of_collection B)) (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i)).
  Proof.
    rewrite make_collection_disjoint_union.
    rewrite measure_countable_disjoint_union.
    - intros.
      apply ELim_seq_le; intros.
      apply sum_Rbar_n_monotone; trivial; intros ?.
      apply measure_monotone; trivial.
      apply make_collection_disjoint_sub.
    - apply make_collection_disjoint_disjoint.
  Qed.
  
  Lemma measure_all_one_ps_le1 (μ:event σ -> Rbar) {μ_meas:is_measure μ}
        (measure_all:μ Ω = R1) A : Rbar_le (μ A) R1.
  Proof.
    rewrite <- measure_all.
    apply measure_monotone; firstorder.
  Qed.

  Lemma measure_all_one_ps_fin (μ:event σ -> Rbar) {μ_meas:is_measure μ}
        (measure_all:μ Ω = R1) A : is_finite (μ A).
  Proof.
    eapply bounded_is_finite.
    - apply measure_nneg.
    - apply measure_all_one_ps_le1; trivial.
  Qed.

  Lemma is_measure_ex_Elim_seq
        (μ:event σ -> Rbar) {μ_meas:is_measure μ} (E:nat->event σ) :
    ex_Elim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (E n)) i).
  Proof.
    apply ex_Elim_seq_incr; intros.
    apply sum_Rbar_n_pos_incr; intros.
    apply measure_nneg.
  Qed.

  Program Instance measure_all_one_ps (μ:event σ -> Rbar) {μ_meas:is_measure μ}
           (measure_all:μ Ω = R1) :
    ProbSpace σ
    := {|
      ps_P x := real (μ x)
    |}.
  Next Obligation.
    intros ???.
    now rewrite H.
  Qed.
  Next Obligation.
    unfold sum_of_probs_equals.
    apply infinite_sum_infinite_sum'.
    apply infinite_sum_is_lim_seq.
    rewrite measure_countable_disjoint_union; trivial.
    apply is_Elim_seq_fin.

    assert (isfin:is_finite (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (collection n)) i))).
    {
      cut (ex_finite_Elim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (collection n)) i))
      ; [ now intros [??] |].
      eapply ex_finite_Elim_seq_incr with (M:=Finite 1) (m:=0%nat).
      - intros.
        apply sum_Rbar_n_pos_incr.
        intros; apply measure_nneg.
      - intros.
        unfold sum_Rbar_n.
        rewrite <- map_map.
        rewrite <- measure_list_disjoint_union; trivial.
        + replace 1 with R1 by lra; simpl.
          rewrite <- measure_all.
          apply measure_monotone; trivial.
          firstorder.
        + now apply collection_take_preserves_disjoint.
      - now unfold sum_Rbar_n; simpl.
    }         
    rewrite isfin.
    rewrite <- ELim_seq_incr_1.
    erewrite ELim_seq_ext; try eapply ELim_seq_correct.
    - apply ex_Elim_seq_incr; intros.
      apply sum_f_R0_pos_incr.
      intros.
      generalize (measure_nneg (collection i)); simpl.
      match_destr; simpl; try tauto; try lra.
    - intros; simpl.
      rewrite sum_f_R0_sum_f_R0'.
      rewrite sum_f_R0'_as_fold_right.
      unfold sum_Rbar_n, list_Rbar_sum.
      rewrite fold_right_map.
      induction (seq 0 (S n)); simpl; trivial.
      rewrite IHl.
      rewrite <- measure_all_one_ps_fin; trivial.
  Qed.
  Next Obligation.
    now rewrite measure_all.
  Qed.
  Next Obligation.
    generalize (measure_nneg A); simpl.
    match_destr; simpl; try tauto; try lra.
  Qed.

  Lemma ps_measure (ps:ProbSpace σ) : is_measure ps_P.
  Proof.
    constructor.
    - intros ???.
      f_equal.
      now apply ps_proper.
    - f_equal.
      apply ps_none.
    - intros; simpl.
      apply ps_pos.
    - intros.
      generalize (ps_countable_disjoint_union B H); intros HH.
      unfold sum_of_probs_equals in HH.
      apply infinite_sum_infinite_sum' in HH.
      apply infinite_sum_is_lim_seq in HH.
      apply is_Elim_seq_fin in HH.
      apply is_Elim_seq_unique in HH.
      rewrite <- ELim_seq_incr_1.
      rewrite <- HH.
      apply ELim_seq_ext; intros.
      rewrite sum_f_R0_sum_f_R0'.
      rewrite sum_f_R0'_as_fold_right.
      unfold sum_Rbar_n, list_Rbar_sum.
      rewrite fold_right_map.
      induction (seq 0 (S n)); simpl; trivial.
      now rewrite <- IHl; simpl.
  Qed.

  Class is_complete_measure (μ:event σ -> Rbar) {μ_meas:is_measure μ}
    := measure_is_complete : forall a b, pre_event_sub a (event_pre b) -> μ b = 0 -> sa_sigma a.

End measure.


Section outer_measure.
  Context {T:Type}.

  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.
                                                              
  Class is_outer_measure (μ:pre_event T -> Rbar)
    := mk_outer_measure {
        outer_measure_proper :> Proper (pre_event_equiv ==> eq) μ
      ; outer_measure_none : μ pre_event_none = 0%R
      ; outer_measure_nneg a : Rbar_le 0 (μ a)
      ; outer_measure_countable_subadditive (A:pre_event T) (B:nat->pre_event T) :
        pre_event_sub A (pre_union_of_collection B) ->
        Rbar_le (μ A) (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i))
      }.

    Class is_outer_measure_alt (μ:pre_event T -> Rbar)
    := mk_outer_measure_alt {
        outer_measure_alt_none : μ pre_event_none = 0%R
      ; outer_measure_alt_nneg a : Rbar_le 0 (μ a)
      ; outer_measure_alt_monotone :> Proper (pre_event_sub ==> Rbar_le) μ
      ; outer_measure_alt_countable_union (B:nat->pre_event T) :
        Rbar_le (μ (pre_union_of_collection B)) (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i))
      }.

  Hint Resolve outer_measure_nneg : prob.
  Hint Resolve Rbar_plus_nneg_compat : prob.

  Global Instance outer_measure_alt_proper (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure_alt μ}: Proper (pre_event_equiv ==> eq) μ.
  Proof.
    intros ???.
    apply antisymmetry
    ; apply outer_measure_alt_monotone; firstorder.
  Qed.

    (* The infinite sum is always defined, since the values are all nonnegative *)
  Lemma is_outer_measure_ex_Elim_seq
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat->pre_event T) :
    ex_Elim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (E n)) i).
  Proof.
    apply ex_Elim_seq_incr; intros.
    apply sum_Rbar_n_pos_incr; auto with prob.
  Qed.

  Lemma outer_measure_list_subadditive
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ}
        (A:pre_event T) (B:list (pre_event T)) :
        pre_event_sub A (pre_list_union B) ->
        Rbar_le (μ A) (list_Rbar_sum (map μ B)).
  Proof.
    intros.
    rewrite <- (seq_sum_list_sum _ _ pre_event_none).
    - apply outer_measure_countable_subadditive.
      generalize (pre_list_union_union B).
      unfold pre_list_collection; intros HH.
      now rewrite HH.
    - apply outer_measure_none.
  Qed.

  Global Instance is_outer_measure_is_alt
         (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    is_outer_measure_alt μ.
  Proof.
    - constructor; try solve [destruct μ_outer; trivial].
      + intros A B sub.
        generalize (outer_measure_list_subadditive μ A (B::nil)).
        simpl.
        rewrite Rbar_plus_0_r.
        intros HH2; apply HH2.
        now rewrite pre_list_union_singleton.
      + intros.
        now apply (outer_measure_countable_subadditive _ B).
  Qed.
  
  Lemma is_outer_measure_alt_iff (μ:pre_event T -> Rbar) :
    is_outer_measure μ <-> is_outer_measure_alt μ.
  Proof.
    split; intros HH.
    - now apply is_outer_measure_is_alt.
    - constructor; try solve [destruct HH; trivial].
      + now apply outer_measure_alt_proper.
      + intros.
        rewrite H.
        now apply outer_measure_alt_countable_union.
  Qed.

  Definition μ_measurable (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T)
    := forall (A:pre_event T), μ A = Rbar_plus (μ (pre_event_inter A E)) (μ (pre_event_diff A E)).

  Global Instance μ_measurable_proper (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    Proper (pre_event_equiv ==> iff) (μ_measurable μ).
  Proof.
    unfold μ_measurable.
    intros ???.
    split; intros ??.
    - now rewrite <- H.
    - now rewrite H.
  Qed.

  Lemma μ_measurable_simpl (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T)
    : (forall (A:pre_event T),
          Rbar_le (Rbar_plus (μ (pre_event_inter A E))
                             (μ (pre_event_diff A E)))
                  (μ A)) -> μ_measurable μ E.
  Proof.
    intros ??.
    apply antisymmetry; trivial.
    generalize (outer_measure_list_subadditive μ A [(pre_event_inter A E); (pre_event_diff A E)])
    ; simpl; intros HH.
    rewrite Rbar_plus_0_r in HH.
    apply HH.
    intros ??.
    red.
    simpl.
    destruct (classic (E x)).
    - exists (pre_event_inter A E); split; eauto.
      firstorder.
    - exists (pre_event_diff A E); split; eauto.
      firstorder.
  Qed.

  Lemma μ_measurable_complement (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T) :
    μ_measurable μ E -> μ_measurable μ (pre_event_complement E).
  Proof.
    unfold μ_measurable; intros.
    rewrite pre_event_diff_derived.
    rewrite pre_event_not_not; [| intros ?; apply classic].
    rewrite <- pre_event_diff_derived.
    rewrite Rbar_plus_comm.
    apply H.
  Qed.

  Lemma μ_measurable_complement_b (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T) :
   μ_measurable μ (pre_event_complement E) -> μ_measurable μ E.
  Proof.
    intros.
    rewrite <- (pre_event_not_not E); try (intros ?; apply classic).
    now apply μ_measurable_complement.
  Qed.

  Hint Resolve ex_Rbar_plus_pos : prob.

  Lemma measure_ex_Rbar_plus (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} x y :
    ex_Rbar_plus (μ x) (μ y).
  Proof.
    auto with prob.
  Qed.

  Hint Resolve measure_ex_Rbar_plus : prob.
  
  Lemma measure_fold_right_Rbar_plus_nneg
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} l :
    Rbar_le 0 (fold_right Rbar_plus 0 (map μ l)).
  Proof.
    apply nneg_fold_right_Rbar_plus_nneg.
    apply Forall_map.
    apply Forall_forall; intros.
    auto with prob.
  Qed.
  
  Lemma list_Rbar_sum_measure_perm (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} {l1 l2} :
    Permutation l1 l2 ->
    list_Rbar_sum (map μ l1) = list_Rbar_sum (map μ l2).
  Proof.
    intros.
    apply list_Rbar_sum_nneg_perm
    ; try solve [ apply Forall_map; apply Forall_forall; intros; auto with prob].
    now apply Permutation_map.
  Qed.

  (* Note that A does not need to be measurable *)
  Lemma μ_measurable_list_inter_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (A:pre_event T) (l : list (pre_event T)) :
    Forall (μ_measurable μ) l ->
    ForallOrdPairs pre_event_disjoint l ->
    μ (pre_list_union (map (pre_event_inter A) l)) = list_Rbar_sum (map μ (map (pre_event_inter A) l)).
  Proof.
    intros meas disj.
    induction l; simpl.
    - rewrite pre_list_union_nil.
      apply outer_measure_none.
    - invcs meas.
      invcs disj.
      specialize (IHl H2 H4).
      rewrite H1.
      rewrite pre_event_inter_comm.
      rewrite pre_event_inter_pre_list_union_distr.
      rewrite pre_event_union_diff_distr; simpl.
      repeat rewrite pre_list_union_cons.
      rewrite pre_event_inter_comm, <- pre_event_inter_assoc, pre_event_inter_self.
      rewrite <- pre_event_inter_diff, pre_event_diff_self.
      rewrite pre_event_inter_false_r.
      rewrite pre_event_union_false_l.
      assert (eqq1: Forall2 pre_event_equiv (map (pre_event_inter a) (map (pre_event_inter A) l))
                            (map (fun _ => pre_event_none) l)).
      {
        rewrite map_map.
        apply Forall2_map_f.
        apply Forall2_refl_in.
        apply Forall_forall; intros.
        rewrite Forall_forall in H3.
        specialize (H3 _ H).
        firstorder.
      } 
      rewrite eqq1.
      rewrite pre_list_union_map_none.
      rewrite pre_event_union_false_r.
      assert (eqq2:Forall2 pre_event_equiv
                           (map (fun x => pre_event_diff x a) (map (pre_event_inter A) l))
                           (map (pre_event_inter A) l)).
      {
        rewrite <- (map_id (map (pre_event_inter A) l)) at 2.
        apply Forall2_map_f.
        apply Forall2_refl_in.
        apply Forall_forall; intros.
        rewrite Forall_forall in H3.
        apply in_map_iff in H.
        destruct H as [? [??]]; subst.
        specialize (H3 _ H0).
        firstorder.
      } 
      rewrite eqq2.
      now rewrite IHl; simpl.
  Qed.

  Lemma μ_measurable_list_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (l : list (pre_event T)) :
    Forall (μ_measurable μ) l ->
    ForallOrdPairs pre_event_disjoint l ->
    μ (pre_list_union l) = list_Rbar_sum (map μ l).
  Proof.
    intros meas disj.
    assert (eqq1: Forall2 pre_event_equiv (map (pre_event_inter pre_Ω) l) l).
    {
      symmetry.
      apply Forall2_map_Forall.
      apply Forall_forall; intros.
      now rewrite pre_event_inter_true_l.
    }
    etransitivity; [etransitivity |]
    ; [| apply (μ_measurable_list_inter_disjoint_additivity μ pre_Ω l meas disj) | ].
    - now rewrite eqq1.
    - f_equal.
      rewrite map_map.
      apply map_ext; intros.
      now rewrite pre_event_inter_true_l.
  Qed.      

  Lemma μ_measurable_list_inter_take_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (A:pre_event T) (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    forall n, μ (pre_list_union (map (pre_event_inter A) (collection_take E n))) = 
           sum_Rbar_n (fun i : nat => μ (pre_event_inter A (E i))) n.
  Proof.
    intros.
    rewrite (μ_measurable_list_inter_disjoint_additivity μ A).
    - unfold sum_Rbar_n.
      unfold collection_take.
      now repeat rewrite map_map.
    - apply Forall_forall; intros.
      apply In_collection_take in H1.
      destruct H1 as [? [??]]; subst.
      auto.
    - now apply pre_collection_take_preserves_disjoint.
  Qed.

  Lemma μ_measurable_list_take_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    forall n, μ (pre_list_union (collection_take E n)) = 
           sum_Rbar_n (fun i : nat => μ (E i)) n.
  Proof.
    intros.
    rewrite (μ_measurable_list_disjoint_additivity μ).
    - unfold sum_Rbar_n.
      unfold collection_take.
      now rewrite map_map.
    - apply Forall_forall; intros.
      apply In_collection_take in H1.
      destruct H1 as [? [??]]; subst.
      auto.
    - now apply pre_collection_take_preserves_disjoint.
  Qed.

  Theorem μ_measurable_countable_inter_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (A:pre_event T) (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    μ (pre_union_of_collection (fun n => pre_event_inter A (E n))) = ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (pre_event_inter A (E n))) i).
  Proof.
    intros meas disj.
    apply antisymmetry.
    - apply outer_measure_alt_countable_union.
    - assert (eqqn:forall n, μ (pre_list_union  (map (pre_event_inter A) (collection_take E n))) = 
                          sum_Rbar_n (fun i : nat => μ (pre_event_inter A (E i))) n)
        by (intros; eapply μ_measurable_list_inter_take_disjoint_additivity; eauto).

      assert (le1:forall n, Rbar_le (μ (pre_list_union  (map (pre_event_inter A) (collection_take E n)))) (μ (pre_union_of_collection  (fun n => pre_event_inter A (E n))))).
      {
        intros.
        apply outer_measure_alt_monotone.
        rewrite <- pre_list_union_take_collection_sub.
        unfold collection_take.
        now rewrite map_map.
      } 
      rewrite <- (ELim_seq_const  (μ (pre_union_of_collection (fun n : nat => pre_event_inter A (E n))))).
      apply ELim_seq_le; intros.
      now rewrite <- eqqn.
  Qed.

  Theorem μ_measurable_countable_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    (μ (pre_union_of_collection E)) = ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (E n)) i).
  Proof.
    intros meas disj.
    apply antisymmetry.
    - apply outer_measure_alt_countable_union.
    - assert (eqqn:forall n, μ (pre_list_union (collection_take E n)) = 
                          sum_Rbar_n (fun i : nat => μ (E i)) n)
        by (intros; eapply μ_measurable_list_take_disjoint_additivity; eauto).

      assert (le1:forall n, Rbar_le (μ (pre_list_union (collection_take E n))) (μ (pre_union_of_collection E))).
      {
        intros.
        apply outer_measure_alt_monotone.
        apply pre_list_union_take_collection_sub.
      } 
      rewrite <- (ELim_seq_const  (μ (pre_union_of_collection E))).
      apply ELim_seq_le; intros.
      now rewrite <- eqqn.
  Qed.

  Theorem μ_measurable_0 (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T) :
    μ E = 0 -> μ_measurable μ E.
  Proof.
    intros.
    apply μ_measurable_simpl; intros.
    replace (μ (pre_event_inter A E)) with (Finite 0).
    - rewrite Rbar_plus_0_l.
      apply outer_measure_alt_monotone.
      apply pre_event_diff_sub.
    - apply antisymmetry.
      + apply outer_measure_alt_nneg.
      + rewrite <- H.
        apply outer_measure_alt_monotone.
        apply pre_event_inter_sub_r.
  Qed.

  Lemma μ_measurable_none (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    μ_measurable μ pre_event_none.
  Proof.
    apply μ_measurable_0.
    apply outer_measure_none.
  Qed.

  Hint Resolve μ_measurable_none : prob.

  Lemma μ_measurable_Ω (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    μ_measurable μ pre_Ω.
  Proof.
    rewrite <- pre_event_not_none.
    apply μ_measurable_complement.
    apply μ_measurable_none.
  Qed.

  Hint Resolve μ_measurable_Ω : prob.

  Lemma μ_measurable_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (a b : pre_event T) :
    μ_measurable μ a ->
    μ_measurable μ b ->
    μ_measurable μ (pre_event_union a b).
  Proof.
    intros.
    apply μ_measurable_simpl; intros.
    rewrite (H A).
    rewrite (H0 (pre_event_inter A a)).
    rewrite (H0 (pre_event_diff A a)).
    rewrite pre_event_diff_diff_l.
    rewrite <- Rbar_plus_assoc by auto with prob.
    apply Rbar_plus_le_compat; try reflexivity.
    generalize (outer_measure_list_subadditive μ
                                               (pre_event_inter A (pre_event_union a b))
                                               [(pre_event_inter (pre_event_inter A a) b)
                                                ; (pre_event_diff (pre_event_inter A a) b)
                                                ;  (pre_event_inter (pre_event_diff A a) b)])
    ; intros HH.
    simpl in HH.
    rewrite Rbar_plus_0_r in HH.
    rewrite Rbar_plus_assoc by auto with prob.
    apply HH.
    intros ?[??].
    unfold pre_list_union; simpl.
    destruct H2.
    - destruct (classic (b x)).
      + exists (pre_event_inter (pre_event_inter A a) b); firstorder.
      + exists (pre_event_diff (pre_event_inter A a) b); firstorder.
    - destruct (classic (a x)).
      + exists (pre_event_inter (pre_event_inter A a) b); firstorder.
      + exists (pre_event_inter (pre_event_diff A a) b); firstorder.
  Qed.

  Hint Resolve μ_measurable_union μ_measurable_complement : prob.
  
  Corollary μ_measurable_inter (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (a b : pre_event T) :
    μ_measurable μ a ->
    μ_measurable μ b ->
    μ_measurable μ (pre_event_inter a b).
  Proof.
    intros.
    apply μ_measurable_complement_b.
    rewrite pre_event_complement_inter.
    auto with prob.
  Qed.

  Hint Resolve μ_measurable_inter : prob.

  Corollary μ_measurable_diff (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (a b : pre_event T) :
    μ_measurable μ a ->
    μ_measurable μ b ->
    μ_measurable μ (pre_event_diff a b).
  Proof.
    intros.
    rewrite pre_event_diff_derived.
    auto with prob.
  Qed.

  Hint Resolve μ_measurable_inter : prob.  

  Lemma μ_measurable_list_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (l:list (pre_event T)) :
    Forall (μ_measurable μ) l ->
    μ_measurable μ (pre_list_union l).
  Proof.
    intros meas.
    induction meas; simpl.
    - rewrite pre_list_union_nil.
      apply μ_measurable_none.
    - rewrite pre_list_union_cons.
      now apply μ_measurable_union.
  Qed.    

  Lemma μ_measurable_disjoint_countable_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    μ_measurable μ (pre_union_of_collection E).
  Proof.
    intros meas disj.
    apply μ_measurable_simpl; intros.

    rewrite pre_event_inter_countable_union_distr.
    rewrite (μ_measurable_countable_inter_disjoint_additivity μ); trivial.

    rewrite <- (ELim_seq_const (μ (pre_event_diff A (pre_union_of_collection E)))).
    rewrite <- ELim_seq_plus.
    - rewrite <- (ELim_seq_const (μ A)).
      apply ELim_seq_le; intros.
      etransitivity.
      + eapply Rbar_plus_le_compat.
        * reflexivity.
        * apply (outer_measure_alt_monotone
                   (pre_event_diff A (pre_union_of_collection E))
                   (pre_event_diff A (pre_list_union (collection_take E n)))).
          now rewrite pre_list_union_take_collection_sub.
      + assert (measu:μ_measurable μ (pre_list_union (collection_take E n))).
        {
          apply μ_measurable_list_union.
          apply Forall_forall; intros ? inn.
          apply In_collection_take in inn.
          destruct inn as [?[??]]; subst.
          auto.
        }
        rewrite (measu A).
        apply Rbar_plus_le_compat; try reflexivity.
        rewrite pre_event_inter_pre_list_union_distr.
        rewrite <- (μ_measurable_list_inter_take_disjoint_additivity μ); trivial.
        reflexivity.
    - now apply is_outer_measure_ex_Elim_seq. 
    - apply ex_Elim_seq_const.
    - apply ex_Rbar_plus_pos.
      + rewrite <- (ELim_seq_const 0).
        apply ELim_seq_le; intros.
        unfold sum_Rbar_n.
        unfold list_Rbar_sum.
        rewrite <- map_map.
        now apply measure_fold_right_Rbar_plus_nneg.
      + rewrite ELim_seq_const.
        auto with prob.
  Qed.

  Lemma μ_measurable_make_disjoint (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    forall n, μ_measurable μ (make_pre_collection_disjoint E n).
  Proof.
    unfold make_pre_collection_disjoint; intros.
    apply μ_measurable_diff; trivial.
    induction n.
    - simpl.
      rewrite pre_union_of_collection_const.
      auto with prob.
    - rewrite pre_union_of_collection_lt_S.
      auto with prob.
  Qed.
    
  Theorem μ_measurable_countable_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) -> μ_measurable μ (pre_union_of_collection E).
  Proof.
    intros.
    rewrite (make_pre_collection_disjoint_union E).
    apply μ_measurable_disjoint_countable_union.
    - intros.
      now apply μ_measurable_make_disjoint.
    - apply make_pre_collection_disjoint_disjoint.
  Qed.

  (* These results are also called Caratheodory’s Theorem *)
  Instance μ_measurable_sa (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    SigmaAlgebra T
    := {|
      sa_sigma E := μ_measurable μ E
    ; sa_countable_union := μ_measurable_countable_union μ
    ; sa_complement := μ_measurable_complement μ
    ; sa_all := μ_measurable_Ω μ
    |}.

  Global Instance μ_measurable_sa_measure (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    is_measure (σ:=μ_measurable_sa μ) μ.
  Proof.
    constructor.
    - intros ???.
      red in H.
      now rewrite H.
    - apply outer_measure_none.
    - intros.
      apply outer_measure_nneg.
    - intros.
      apply (μ_measurable_countable_disjoint_additivity μ); trivial.
      intros.
      now destruct (B n); simpl.
  Qed.

  Global Instance μ_measurable_sa_complete_measure (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    is_complete_measure (σ:=μ_measurable_sa μ) μ.
  Proof.
    intros ????.
    apply μ_measurable_0. 
    rewrite <- H0.
    apply antisymmetry.
    - now rewrite H.
    - rewrite H0.
      apply outer_measure_nneg.
  Qed.
  
End outer_measure.

Section algebra.

  Class Algebra (T:Type) :=
    {
      alg_in : pre_event T -> Prop;
      
      alg_in_list_union (l: list (pre_event T)) : Forall alg_in l -> alg_in (pre_list_union l);
      
      alg_in_complement (A:pre_event T) : alg_in A -> alg_in (pre_event_complement A) ;
    
      alg_in_all : alg_in pre_Ω 
                        
    }.

  Global Instance alg_proper {T} (s: Algebra T) : Proper (pre_event_equiv ==> iff) alg_in.
  Proof.
    intros ?? eqq.
    red in eqq.
    cut (x = y); [intros; subst; intuition | ].
    apply Ensembles.Extensionality_Ensembles.
    unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In.
    firstorder.
  Qed.

  Lemma alg_in_none {T} (s: Algebra T) : alg_in pre_event_none.
  Proof.
    rewrite <- pre_event_not_all.
    apply alg_in_complement.
    apply alg_in_all.
  Qed.
  
  Lemma alg_in_list_inter {T} {alg:Algebra T}
        (l: list (pre_event T)) :
    Forall alg_in l ->
    alg_in (pre_list_inter l).
  Proof.
    intros.
    cut (alg_in (pre_event_complement (pre_list_union (map pre_event_complement l)))).
    - apply alg_proper; intros ?.
      unfold pre_list_inter, pre_event_complement, pre_list_union.
      split.
      + intros ? [?[??]].
        apply in_map_iff in H1.
        destruct H1 as [?[??]]; subst.
        apply H2.
        apply (H0 _ H3).
      + intros ???.
        generalize (not_ex_all_not _ _ H0); intros HH.
        apply NNPP; intros ?.
        apply (HH (pre_event_complement a)).
        split; trivial.
        now apply in_map.
    - apply alg_in_complement.
      apply alg_in_list_union.
      apply Forall_map.
      revert H.
      apply Forall_impl; intros.
      now apply alg_in_complement.
  Qed.

  Lemma alg_in_union {T} {alg:Algebra T}
        (a b : pre_event T) :
    alg_in a -> alg_in b ->
    alg_in (pre_event_union a b).
  Proof.
    intros.
    generalize (alg_in_list_union [a;b]); simpl.
    rewrite pre_list_union_cons.
    rewrite pre_list_union_singleton.
    intros HH; apply HH.
    now repeat constructor.
  Qed.

  Lemma alg_in_inter {T} {alg:Algebra T}
        (a b : pre_event T) :
    alg_in a -> alg_in b ->
    alg_in (pre_event_inter a b).
  Proof.
    intros.
    generalize (alg_in_list_inter [a;b]); simpl.
    rewrite pre_list_inter_cons.
    rewrite pre_list_inter_singleton.
    intros HH; apply HH.
    now repeat constructor.
  Qed.

  Lemma alg_in_diff {T} {alg:Algebra T}
        (a b : pre_event T) :
    alg_in a -> alg_in b ->
    alg_in (pre_event_diff a b).
  Proof.
    intros.
    rewrite pre_event_diff_derived.
    apply alg_in_inter; trivial.
    now apply alg_in_complement.
  Qed.

  Definition alg_set {T} (A:Algebra T): Type := {x | alg_in x}.
  Definition alg_pre {T} {A:Algebra T} : alg_set A -> (T->Prop)
    := fun e => proj1_sig e.

  Lemma alg_set_in {T} {Alg:Algebra T} (a:alg_set Alg) : alg_in (alg_pre a).
  Proof.
    now destruct a.
  Qed.
  
  Definition alg_sub {T} {Alg:Algebra T} (x y:alg_set Alg) :=
    pre_event_sub (proj1_sig x) (proj1_sig y).

  Definition alg_equiv {T} {Alg:Algebra T} (x y:alg_set Alg) :=
    pre_event_equiv (proj1_sig x) (proj1_sig y).

  Global Instance alg_equiv_equiv {T} {Alg:Algebra T} : Equivalence alg_equiv.
  Proof.
    firstorder.
  Qed.
  
  Global Instance alg_equiv_sub {T} {Alg:Algebra T}  : subrelation alg_equiv alg_sub.
  Proof.
    firstorder.
  Qed.

  Global Instance alg_sub_pre {T} {Alg:Algebra T}  : PreOrder alg_sub.
  Proof.
    firstorder.
  Qed.

  Global Instance alg_sub_part {T} {Alg:Algebra T}  : PartialOrder alg_equiv alg_sub.
  Proof.
    firstorder.
  Qed.

  Coercion alg_pre : alg_set >-> Funclass.

  Definition alg_none {T} {Alg : Algebra T} : alg_set Alg
    := exist _ _ (alg_in_none _).

  Definition alg_all {T} {Alg : Algebra T} : alg_set Alg
    := exist _ _ alg_in_all.

  Program Definition alg_list_union {T} {Alg:Algebra T} (l: list (alg_set Alg)) :
    alg_set Alg
    := exist _ (pre_list_union (map alg_pre l)) _.
  Next Obligation.
    apply alg_in_list_union.
    apply Forall_map.
    apply Forall_forall; intros.
    apply alg_set_in.
  Qed.

  Program Definition alg_list_inter {T} {Alg:Algebra T} (l: list (alg_set Alg)) :
    alg_set Alg
    := exist _ (pre_list_inter (map alg_pre l)) _.
  Next Obligation.
    apply alg_in_list_inter.
    apply Forall_map.
    apply Forall_forall; intros.
    apply alg_set_in.
  Qed.

  Definition alg_union {T} {Alg:Algebra T} (a b : alg_set Alg) : alg_set Alg
    := exist _ (pre_event_union a b) (alg_in_union _ _ (alg_set_in a) (alg_set_in b)).

  Definition alg_inter {T} {Alg:Algebra T} (a b : alg_set Alg) : alg_set Alg
    := exist _ (pre_event_inter a b) (alg_in_inter _ _ (alg_set_in a) (alg_set_in b)).

  Definition alg_diff {T} {Alg:Algebra T} (a b : alg_set Alg) : alg_set Alg
    := exist _ (pre_event_diff a b) (alg_in_diff _ _ (alg_set_in a) (alg_set_in b)).

  Context {T} {Alg:Algebra T}.

  Global Instance alg_union_proper : Proper (alg_equiv ==> alg_equiv ==> alg_equiv) alg_union.
  Proof.
    intros ???????; simpl.
    red in H, H0.
    now apply pre_event_union_proper.
  Qed.
    
  Global Instance alg_inter_proper : Proper (alg_equiv ==> alg_equiv ==> alg_equiv) alg_inter.
  Proof.
    intros ???????; simpl.
    red in H, H0.
    now apply pre_event_inter_proper.
  Qed.

  Global Instance alg_diff_proper : Proper (alg_equiv ==> alg_equiv ==> alg_equiv) alg_diff.
  Proof.
    intros ???????; simpl.
    red in H, H0.
    now apply pre_event_diff_proper.
  Qed.
  
  Lemma alg_sub_diff_union (A B : alg_set Alg) :
    alg_sub B A ->
    alg_equiv A (alg_union (alg_diff A B) B).
  Proof.
    unfold alg_union, alg_diff, alg_inter, alg_equiv, alg_sub; simpl.
    unfold pre_event_union, pre_event_diff, pre_event_inter, pre_event_sub.
    repeat red; simpl; intros.
    split; intros.
    - destruct (classic (proj1_sig B x)); tauto.
    - intuition.
  Qed.

  Lemma alg_list_union_nil :
    alg_equiv (alg_list_union []) alg_none.
  Proof.
    firstorder.
  Qed.

  Lemma alg_list_union_cons  (x1 : alg_set Alg) (l:list (alg_set Alg)):
    alg_equiv (alg_list_union (x1::l)) (alg_union x1 (alg_list_union l)).
  Proof.
    apply pre_list_union_cons.
  Qed.

  Lemma alg_list_union_singleton  (En:alg_set Alg) :
    alg_equiv (alg_list_union [En]) En.
  Proof.
    rewrite alg_list_union_cons, alg_list_union_nil.
    red. unfold alg_union; simpl.
    now rewrite pre_event_union_false_r.
  Qed.

End algebra.

Section premeasure.

  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Context {T:Type}.
  Context {Alg:Algebra T}.

  (* we could generalize events, but that is too much work for now :-) *)
  Class is_premeasure (λ:alg_set Alg -> Rbar)
    := mk_premeasure {
        premeasure_proper :> Proper (alg_equiv ==> eq) λ 
      ; premeasure_none : λ alg_none = 0%R
      ; premeasure_nneg a : Rbar_le 0 (λ a)
      ; premeasure_countable_disjoint_union (B:nat->alg_set Alg) :
        pre_collection_is_pairwise_disjoint (fun x => B x) ->
        forall (pf:alg_in (pre_union_of_collection (fun x => B x))),
        λ (exist _ _ pf) = (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => λ (B n)) i))
      }.

  Section props.
    Context (λ:alg_set Alg -> Rbar) {μ_meas:is_premeasure λ}.

    Lemma premeasure_list_disjoint_union (a: list (alg_set Alg)) :
      ForallOrdPairs pre_event_disjoint (map alg_pre a) ->
      λ (alg_list_union a) = list_Rbar_sum (map λ a).
    Proof.
      intros Hd.
      generalize (premeasure_countable_disjoint_union (fun n => nth n a alg_none)); intros HH.
      cut_to HH.
      - assert (pf : alg_in (pre_union_of_collection (fun x : nat => nth x a alg_none))).
        {
          generalize (pre_list_union_union (map alg_pre a))
          ; intros eqq.
          unfold pre_list_collection in eqq.
          case_eq (alg_list_union a).
          unfold alg_list_union; simpl; intros ???; invcs H.
          rewrite <- eqq in a0.
          revert a0.
          apply alg_proper; intros ?.
          apply pre_union_of_collection_proper; intros ??.
          now rewrite <- map_nth.
        }
        specialize (HH pf).
        erewrite premeasure_proper; try rewrite HH.
        + apply (seq_sum_list_sum _ _ alg_none).
          apply premeasure_none.
        + intros ?; simpl.
          rewrite <- (pre_list_union_union (map alg_pre a) x).
          apply pre_union_of_collection_proper; intros ??.
          now rewrite <- map_nth.
      - apply pre_list_collection_disjoint in Hd.
        revert Hd.
        apply pre_collection_is_pairwise_disjoint_pre_event_equiv_proper; intros ??.
        unfold pre_list_collection.
        now rewrite <- map_nth.
    Qed.

    Lemma premeasure_disjoint_union (a b: alg_set Alg) :
      pre_event_disjoint a b ->
      λ (alg_union a b) = Rbar_plus (λ a) (λ b).
    Proof.
      intros Hd.
      generalize (premeasure_list_disjoint_union [a; b]); simpl; intros HH.
      rewrite alg_list_union_cons, alg_list_union_singleton in HH.
      rewrite Rbar_plus_0_r in HH.
      apply HH.
      now repeat constructor.
    Qed.    

    Global Instance premeasure_monotone  :
      Proper (alg_sub ==> Rbar_le) λ.
    Proof.
      intros ???.
      rewrite (alg_sub_diff_union _ _ H).
      rewrite premeasure_disjoint_union; trivial.
      - rewrite <- (Rbar_plus_0_l (λ x)) at 1.
        apply Rbar_plus_le_compat; try reflexivity.
        apply premeasure_nneg.
      - simpl; firstorder.
    Qed.

    Definition alg_make_collection_disjoint (coll:nat->alg_set Alg) : nat -> alg_set Alg
      := fun x => alg_diff (coll x) (alg_list_union
                                    (collection_take coll x)).

    Lemma alg_make_collection_disjoint_sub (En:nat -> alg_set Alg) n :
      alg_sub (alg_make_collection_disjoint En n) (En n).
    Proof.
      now intros x [??].
    Qed.

    Lemma alg_make_collection_disjoint_in (coll:nat->alg_set Alg) (x:nat) (e:T) :
      proj1_sig (alg_make_collection_disjoint coll x) e <->
        (proj1_sig (coll x) e /\ forall y, (y < x)%nat -> ~ proj1_sig (coll y) e).
    Proof.
      split.
      - unfold alg_make_collection_disjoint; intros HH.
        destruct HH as [H1 H2].
        split; trivial.
        intros y ylt cy.
        apply H2.
        exists (coll y).
        split; trivial.
        apply in_map.
        unfold collection_take.
        apply in_map.
        apply in_seq.
        lia.
      - intros [ce fce].
        unfold make_collection_disjoint.
        split; trivial.
        intros [n [Hn ?]].
        apply in_map_iff in Hn.
        destruct Hn as [? [??]]; subst.
        apply In_collection_take in H1.
        destruct H1 as [? [??]]; subst.
        eapply fce; eauto.
    Qed.
    
    Lemma alg_make_collection_disjoint_disjoint (coll:nat->alg_set Alg) :
      pre_collection_is_pairwise_disjoint (alg_make_collection_disjoint coll).
    Proof.
      intros x y xyneq e e1 e2.
      apply alg_make_collection_disjoint_in in e1.
      apply alg_make_collection_disjoint_in in e2.
      destruct e1 as [H11 H12].
      destruct e2 as [H21 H22].
      destruct (not_eq _ _ xyneq) as [xlt|ylt].
      - eapply H22; eauto.
      - eapply H12; eauto.
    Qed.

    Lemma pre_alg_make_collection_disjoint_union (coll:nat->alg_set Alg)  :
      pre_event_equiv (pre_union_of_collection (fun x : nat => coll x))
        (pre_union_of_collection (alg_make_collection_disjoint coll)).
    Proof.
      unfold pre_union_of_collection.
      intros t.
      split; intros [n Hn].
      - simpl.
        generalize (excluded_middle_entails_unrestricted_minimization classic (fun n => proj1_sig (coll n) t))
        ; intros HH.
        specialize (HH _ Hn).
        destruct HH as [m mmin].
        exists m.
        destruct mmin.
        unfold make_collection_disjoint.
        split; trivial.
        unfold union_of_collection.
        intros [nn Hnn].
        unfold collection_take in Hnn.
        rewrite map_map in Hnn.
        destruct Hnn as [??].
        apply in_map_iff in H1.
        destruct H1 as [?[??]]; subst.
        apply in_seq in H3.
        specialize (H0 _ H2).
        lia.
      - apply alg_make_collection_disjoint_in in Hn.
        exists n; tauto.
  Qed.

    Lemma alg_make_collection_disjoint_union (coll:nat->alg_set Alg) 
      (pf1:alg_in (pre_union_of_collection (fun x : nat => coll x)))
        (pf2:alg_in (pre_union_of_collection (alg_make_collection_disjoint coll))) :
      alg_equiv (exist _ _ pf1) (exist _ _ pf2).
    Proof.
      red; simpl.
      apply pre_alg_make_collection_disjoint_union.
    Qed.

    Lemma alg_make_collection_disjoint_union_alg_in (coll:nat->alg_set Alg) 
      (pf1:alg_in (pre_union_of_collection (fun x : nat => coll x))) :
      alg_in (pre_union_of_collection (alg_make_collection_disjoint coll)).
    Proof.
      revert pf1.
      apply alg_proper.
      symmetry.
      apply pre_alg_make_collection_disjoint_union.
    Qed.

    Lemma alg_make_collection_disjoint_union' (coll:nat->alg_set Alg) 
          (pf1:alg_in (pre_union_of_collection (fun x : nat => coll x))) :
      alg_equiv (exist _ _ pf1) (exist _ _ (alg_make_collection_disjoint_union_alg_in _ pf1)).
    Proof.
      red; simpl.
      apply pre_alg_make_collection_disjoint_union.
    Qed.

    Lemma premeasure_countable_sub_union (B:nat->alg_set Alg) :
        forall (pf:alg_in (pre_union_of_collection (fun x => B x))),
          Rbar_le (λ (exist _ _ pf)) (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => λ (B n)) i)).
    Proof.
      intros.
      rewrite alg_make_collection_disjoint_union'.
      rewrite premeasure_countable_disjoint_union.
    - intros.
      apply ELim_seq_le; intros.
      apply sum_Rbar_n_monotone; trivial; intros ?.
      apply premeasure_monotone; trivial.
      apply alg_make_collection_disjoint_sub.
    - apply alg_make_collection_disjoint_disjoint.
  Qed.

  End props.
  
End premeasure.

Section omf.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.


  Context {T:Type}.
  Context {Alg:Algebra T}.
  Context (λ:alg_set Alg -> Rbar).
  Context {λ_meas:is_premeasure λ}.

  Definition outer_λ_of_covers (an:nat->alg_set Alg) : Rbar :=
    ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => λ (an n)) i).
  
  Definition outer_λ (A:pre_event T) : Rbar
    := Rbar_glb (fun (x : Rbar) =>
                   exists (an:nat->alg_set Alg),
                     pre_event_sub A (pre_union_of_collection an) /\
                       x = outer_λ_of_covers an).

  Lemma outer_λ_nneg (A:pre_event T) 
    : Rbar_le 0 (outer_λ A).
  Proof.
    unfold outer_λ.
    unfold Rbar_glb, proj1_sig; match_destr; destruct r as [lb glb].
    apply glb; intros ?[?[??]]; subst.
    apply ELim_seq_nneg; intros.
    apply sum_Rbar_n_nneg_nneg; intros.
    apply premeasure_nneg.
  Qed.

  Lemma outer_λ_of_covers_nneg (an:nat->alg_set Alg) :
    Rbar_le 0 (outer_λ_of_covers an).
  Proof.
    apply ELim_seq_nneg; intros.
    apply sum_Rbar_n_nneg_nneg; intros.
    apply premeasure_nneg.
  Qed.
  
  Global Instance outer_λ_of_covers_monotone : Proper (pointwise_relation _ alg_sub ==> Rbar_le) outer_λ_of_covers.
  Proof.
    intros ???.
    apply ELim_seq_le; intros.
    apply sum_Rbar_n_monotone; trivial.
    intros ?.
    now apply premeasure_monotone.
  Qed.

  Global Instance outer_λ_outer_measure : is_outer_measure outer_λ.
  Proof.
    unfold outer_λ.
    apply is_outer_measure_alt_iff.
    constructor.
    - apply antisymmetry; try apply outer_λ_nneg.
      unfold Rbar_glb, proj1_sig; match_destr; destruct r as [lb glb].
      apply lb.
      exists (fun _ => alg_none).
      split.
      + simpl.
        rewrite pre_union_of_collection_const.
        reflexivity.
      + rewrite <- (ELim_seq_const 0).
        apply ELim_seq_ext; intros.
        unfold sum_Rbar_n.
        induction (seq 0 n); simpl; trivial.
        rewrite IHl, premeasure_none; simpl.
        now rewrite Rbar_plus_0_l.
    - intros.
      apply outer_λ_nneg.
    - intros ???.
      apply Rbar_glb_subset
      ; intros ? [? [??]].
      exists x1.
      split; trivial.
      now rewrite H.
    - intros B.
      assert (lim_seq_nneg:
               Rbar_le 0
                       (ELim_seq
                          (fun i : nat =>
                             sum_Rbar_n
                               (fun n : nat =>
                                  Rbar_glb
                                    (fun x : Rbar =>
                                       exists an : nat -> alg_set Alg,
                                         pre_event_sub (B n) (pre_union_of_collection an) /\ x = outer_λ_of_covers an)) i))).
      {
        apply ELim_seq_nneg; intros.
        apply sum_Rbar_n_nneg_nneg; intros k klt.
        apply Rbar_glb_ge; intros ? [?[??]]; subst.
        apply outer_λ_of_covers_nneg.
      } 
      case_eq (ELim_seq
       (fun i : nat =>
        sum_Rbar_n
          (fun n : nat =>
           Rbar_glb
             (fun x : Rbar =>
                exists an : nat -> alg_set Alg,
                pre_event_sub (B n) (pre_union_of_collection an) /\ x = outer_λ_of_covers an)) i)).
      + (* finite *)
        intros ??.

        assert (isnneg : forall n,
                   Rbar_le 0
                           (Rbar_glb
                              (fun x : Rbar =>
                                 exists an : nat -> alg_set Alg,
                                   pre_event_sub (B n) (pre_union_of_collection an) /\
                                     x = outer_λ_of_covers an))).
        {
          intros.
          apply Rbar_glb_ge; intros ? [?[??]]; subst.
          apply outer_λ_of_covers_nneg.
        } 

        assert (isfin : forall n,
                   is_finite (Rbar_glb
                                (fun x : Rbar =>
                                   exists an : nat -> alg_set Alg,
                                     pre_event_sub (B n) (pre_union_of_collection an) /\
                                       x = outer_λ_of_covers an))).
        {
          apply (Elim_seq_sum_pos_fin_n_fin _ _ isnneg H).
        }

        apply Rbar_le_forall_Rbar_le; intros eps.

        assert (p:forall n,
                 exists (en:nat -> alg_set Alg),
                   pre_event_sub (B n) (pre_union_of_collection en) /\
                     Rbar_le (outer_λ_of_covers en)
                             (Rbar_plus (
                                  outer_λ (B n))
                                        (eps/(pow 2 (S n))))).
        {
          intros n.
          specialize (isfin n).
          unfold outer_λ, Rbar_glb, proj1_sig in *; match_destr.
          rewrite <- isfin in r0.
          assert (posdiv: 0 < (eps / 2 ^ (S n))).
          {
            apply Rdiv_lt_0_compat.
            - apply cond_pos.
            - apply pow_lt; lra.
          } 
          destruct (Rbar_is_glb_fin_close_classic (mkposreal _ posdiv) r0) as [? [[?[??]] ?]]; subst.
          exists x1.
          simpl.
          split; trivial.
          simpl in H2.
          rewrite <- isfin; simpl.
          trivial.
        }
 
        apply choice in p; trivial.
        
        destruct p as [an HH].

        rewrite <- H.

        assert (le1:
                 Rbar_le
                   (ELim_seq
                      (fun i : nat =>
                         sum_Rbar_n
                           (fun x : nat => outer_λ_of_covers (an x)) i))
                   (ELim_seq
                      (fun i : nat =>
                         sum_Rbar_n
                           (fun x : nat => (Rbar_plus (outer_λ (B x)) (eps / 2 ^ S x))) i))).
        {
          apply ELim_seq_le; intros.
          apply sum_Rbar_n_monotone; trivial; intros ?.
          apply HH.
        }
        rewrite ELim_seq_sum_eps2n in le1; trivial
        ; try solve [destruct eps; simpl; lra].
        etransitivity
        ; [etransitivity |]
        ; [ | apply le1 | ].
        * unfold Rbar_glb, proj1_sig; match_destr.
          apply r0.
          exists (fun n => let '(a,b) := iso_b (Isomorphism:=nat_pair_encoder) n in an a b).
          split.
          -- intros ? [??].
             destruct (HH x1).
             destruct (H1 x0 H0).
             exists (iso_f (Isomorphism:=nat_pair_encoder) (x1, x2)).
             now rewrite iso_b_f.
          -- unfold outer_λ_of_covers.
             transitivity (ELim_seq
                             (fun i : nat =>
                                sum_Rbar_n (fun n : nat => (let '(a, b) := iso_b n in λ (an a b))) i)).
             ++ apply ELim_seq_Elim_seq_pair; intros.
                apply premeasure_nneg.
             ++ apply ELim_seq_ext; intros ?.
                unfold sum_Rbar_n.
                f_equal.
                apply map_ext; intros ?.
                now destruct (iso_b a).
        * reflexivity.
      + intros H.
        unfold Rbar_le; match_destr.
      + intros H. rewrite H in lim_seq_nneg.
        now simpl in lim_seq_nneg.
  Qed.
  
  Lemma outer_λ_is_measurable (A:alg_set Alg) : μ_measurable outer_λ A.
  Proof.
    apply μ_measurable_simpl; intros B.
    unfold outer_λ.
    unfold Rbar_glb, proj1_sig.
    repeat match_destr.
    destruct r as [lb1 glb1].    
    destruct r0 as [lb2 glb2].
    destruct r1 as [lb0 glb0].
    apply glb0; intros ? [?[??]].
    rewrite H0; clear x2 H0.
    unfold is_lb_Rbar in *.
    assert (nneg:Rbar_le 0 (outer_λ_of_covers x3)).
    {
      apply outer_λ_of_covers_nneg.
    } 
    case_eq (outer_λ_of_covers x3); simpl.
    - (* finite *)
      intros ? eqq1.
      specialize (lb1 (outer_λ_of_covers (fun n => alg_inter (x3 n) A))).
      cut_to lb1.
      + specialize (lb2 (outer_λ_of_covers (fun n => alg_diff (x3 n) A))).
        cut_to lb2.
        * {
          etransitivity.
          - eapply Rbar_plus_le_compat; try eassumption.
          - unfold outer_λ_of_covers.
            rewrite <- ELim_seq_plus.
            + rewrite <- eqq1.
              unfold outer_λ_of_covers.
              apply ELim_seq_le; intros.
              rewrite <- sum_Rbar_n_nneg_plus by (intros; apply premeasure_nneg).
              apply sum_Rbar_n_monotone; trivial; intros ?.
              rewrite <- premeasure_disjoint_union; trivial.
              * apply premeasure_monotone; trivial.
                intros ?; simpl; firstorder.
              * intros ?; simpl; firstorder.
            + apply ex_Elim_seq_incr; intros.
              apply sum_Rbar_n_pos_incr; intros.
              apply premeasure_nneg.
            + apply ex_Elim_seq_incr; intros.
              apply sum_Rbar_n_pos_incr; intros.
              apply premeasure_nneg.
            + apply ex_Rbar_plus_pos
              ; apply outer_λ_of_covers_nneg.
        } 
        * 
          eexists; split; try reflexivity.
          rewrite H.
          repeat rewrite pre_of_union_of_collection.
          now rewrite pre_event_countable_union_diff_distr.
      + 
        eexists; split; try reflexivity.
        rewrite H.
        repeat rewrite pre_of_union_of_collection.
        rewrite pre_event_inter_comm.
        rewrite pre_event_inter_countable_union_distr.
        apply pre_union_of_collection_sub_proper; intros ?.
        rewrite pre_event_inter_comm.
        reflexivity.
    - intros; simpl.
      unfold Rbar_le; match_destr.
    - intros HH; rewrite HH in nneg; simpl in nneg; contradiction.
  Qed.

  Lemma outer_λ_λ (A:alg_set Alg) : outer_λ A = λ A.
  Proof.
    unfold outer_λ.
    unfold Rbar_glb, proj1_sig; match_destr.
    destruct r as [lb glb].
    unfold is_lb_Rbar in *.
    apply antisymmetry.
    - case_eq (λ A); simpl.
      + intros.
        apply lb.
        exists (fun n => nth n [A] alg_none).
        split.
        * intros ??.
          now (exists 0%nat; simpl).
        * unfold outer_λ_of_covers.
          rewrite seq_sum_list_sum.
          -- simpl.
             now rewrite Rbar_plus_0_r.
          -- apply premeasure_none.
      + intros; now destruct x.
      + intros.
        generalize (premeasure_nneg A); rewrite H.
        now destruct x.
    - apply glb; intros ? [? [??]].
      rewrite H0.
      pose (B n := alg_inter A (alg_make_collection_disjoint x1 n)).
      assert (eqq1:pre_event_equiv A (pre_union_of_collection B)).
      {
        unfold B.
        transitivity (pre_union_of_collection (fun n : nat => pre_event_inter A (alg_make_collection_disjoint x1 n)))
        ; try reflexivity.

        rewrite <- pre_event_inter_countable_union_distr.
        rewrite <- pre_alg_make_collection_disjoint_union.
        firstorder.
      } 
      assert (pf:alg_in (pre_union_of_collection (fun n : nat => B n))).
      {
        rewrite <- eqq1.
        apply alg_set_in.
      }
      assert (eqq2:alg_equiv A (exist _ _ pf)) by apply eqq1.
      rewrite eqq2.
      rewrite premeasure_countable_disjoint_union.
      + apply ELim_seq_le; intros.
        apply sum_Rbar_n_monotone; trivial; intros ?.
        apply premeasure_monotone; trivial; intros ? [??].
        apply alg_make_collection_disjoint_in in H2.
        now destruct H2 as [??].
      + apply pre_collection_is_pairwise_disjoint_inter.
        apply alg_make_collection_disjoint_disjoint.
  Qed.

End omf.

Section semi_algebra.

  Class SemiAlgebra (T:Type) :=
    {
      salg_in : pre_event T -> Prop;

      salg_nempty : exists a, salg_in a;      

      salg_in_inter (a b:pre_event T) : salg_in a -> salg_in b -> salg_in (pre_event_inter a b);

      salg_in_complement (a:pre_event T) :
      salg_in a ->
      exists l,
        pre_event_equiv (pre_event_complement a) (pre_list_union l) /\
          ForallOrdPairs pre_event_disjoint l /\
          Forall salg_in l
    }.

  Global Instance salg_proper {T} (s: SemiAlgebra T) : Proper (pre_event_equiv ==> iff) salg_in.
  Proof.
    intros ?? eqq.
    red in eqq.
    cut (x = y); [intros; subst; intuition | ].
    apply Ensembles.Extensionality_Ensembles.
    unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In.
    firstorder.
  Qed.

  Lemma pre_list_disjoint_concat_from_parts {A B} (f:A->list (pre_event B)) l:
    Forall (fun x  => ForallOrdPairs pre_event_disjoint (f x)) l ->
    ForallOrdPairs pre_event_disjoint (map pre_list_union (map f l)) ->
    ForallOrdPairs pre_event_disjoint (concat (map f l)).
  Proof.
    intros.
    induction l; simpl; trivial.
    invcs H; invcs H0.
    cut_to IHl; trivial.
    induction (f a); simpl; trivial.
    invcs H3.
    cut_to IHl0; trivial.
    - constructor; trivial.
      apply Forall_app; trivial.
      rewrite Forall_forall; intros ??.
      rewrite Forall_forall in H2.
      apply in_concat in H.
      destruct H as [?[??]].
      apply in_map_iff in H.
      destruct H as [?[??]]; subst.
      specialize (H2 (pre_list_union (f x1))).
      cut_to H2.
      + intros b ??.
        apply (H2 b)
        ; red; simpl; eauto.
      + apply in_map.
        now apply in_map.
    - revert H2.
      apply Forall_impl; intros.
      rewrite pre_list_union_cons in H.
      intros ???.
      eapply H; try eapply H2.
      red; eauto.
  Qed.
  
  Definition salgebra_algebra_in {T} (s: SemiAlgebra T) (x:pre_event T) :=
    exists (l:list (pre_event T)),
      Forall salg_in l /\
        ForallOrdPairs pre_event_disjoint l /\
        pre_event_equiv x (pre_list_union l).

  Lemma salgebra_algebra_none {T:Type} (s:SemiAlgebra T) :
    salgebra_algebra_in s pre_Ω.
  Proof.
    destruct salg_nempty as [X inX].
    destruct (salg_in_complement X inX) as [? [?[??]]].
    exists (X::x).
    split; [| split].
    - constructor; trivial.
    - repeat constructor; trivial.
      apply Forall_forall; intros ?????.
      assert (HH:pre_list_union x x1) by (red; eauto).
      apply H in HH.
      now apply HH.
    - rewrite pre_list_union_cons.
      rewrite <- H.
      rewrite pre_event_union_complement.
      + reflexivity.
      + apply sa_pre_dec.
  Qed.

    (* semi-algebras provide just enough structure to pull the make disjoint trick, although
     doing so is somewhat more painful *)
  Lemma salgebra_algebra_simpl {T:Type} (s:SemiAlgebra T) x :
    (exists (l:list (pre_event T)),
        Forall salg_in l /\
          pre_event_equiv x (pre_list_union l)) <->
      (exists (l:list (pre_event T)),
          Forall salg_in l /\
            ForallOrdPairs pre_event_disjoint l /\
            pre_event_equiv x (pre_list_union l)).
  Proof.
    split.
    - intros [l [??]].
      cut (exists l' : list (pre_event T),
              Forall salg_in l' /\ ForallOrdPairs pre_event_disjoint l' /\ pre_event_equiv (pre_list_union l') (pre_list_union l)).
      {
        intros [l' [?[??]]].
        exists l'.
        rewrite H3.
        tauto.
      } 
      clear x H0.
      induction H.
      + exists nil.
        repeat split; trivial; constructor.
      + destruct IHForall as [l' [?[??]]].

        cut (exists l'0 : list (pre_event T),
                Forall salg_in l'0 /\
                  ForallOrdPairs pre_event_disjoint l'0 /\ pre_event_equiv (pre_list_union l'0) (pre_list_union (x :: l'))).
        {
          intros [ll [?[??]]].
          exists ll.
          split; trivial.
          split; trivial.
          rewrite H6.
          repeat rewrite pre_list_union_cons.
          now rewrite H3.
        } 
        clear l H0 H3.
        destruct (salg_in_complement _ H) as [ll2 [?[??]]].
        exists (x :: (concat (map (fun e => (map (pre_event_inter e) ll2)) l'))).
        {
          split; [| split].
          - constructor; trivial.
            induction l'; simpl; trivial.
            apply Forall_app.
            + apply Forall_map.
              apply Forall_forall; intros.
              invcs H1.
              apply salg_in_inter; trivial.
              rewrite Forall_forall in H4; auto.
            + invcs H1; invcs H2.
              apply IHl'; auto.
          - constructor.
            + apply Forall_forall; intros ? inn.
              apply in_concat in inn.
              destruct inn as [? [??]].
              apply in_map_iff in H5.
              destruct H5 as [?[??]]; subst.
              apply in_map_iff in H6.
              destruct H6 as [?[??]]; subst.
              apply pre_event_complement_proper in H0.
              rewrite pre_event_not_not in H0; [| apply sa_pre_dec].
              intros ??[??].
              apply H0 in H5.
              apply H5.
              red; eauto.
            + apply pre_list_disjoint_concat_from_parts.
              * apply Forall_forall; intros ? inn.
                now apply pre_list_disjoint_inter.
              * rewrite map_map.
                induction H2; simpl; [constructor |].
                constructor.
                -- apply Forall_map.
                   revert H2.
                   apply Forall_impl; intros ??.
                   repeat rewrite <-  pre_event_inter_pre_list_union_distr.
                   firstorder.
                -- invcs H1; auto.
          - repeat rewrite pre_list_union_cons.
            rewrite pre_list_union_concat.
            split.
            + intros [?|?].
              * now left.
              * destruct H5 as [? [??]].
                apply in_map_iff in H5.
                destruct H5 as [? [??]]; subst.
                apply in_map_iff in H7.
                destruct H7 as [? [??]]; subst.
                destruct H6 as [? [??]].
                apply in_map_iff in H5.
                destruct H5 as [? [??]]; subst.
                destruct H6.
                right.
                exists x1; eauto.
            + intros [?|?].
              * now left.
              * red.
                destruct H5 as [? [??]].
                classical_right.
                red.
                rewrite map_map.
                exists (pre_list_union (map (pre_event_inter x1) ll2)).
                split.
                -- apply in_map_iff.
                   eauto.
                -- red.
                   assert (pre_list_union ll2 x0).
                   {
                     apply H0.
                     apply H7.
                   }
                   destruct H8 as [? [??]].
                   exists (pre_event_inter x1 x2).
                   split.
                   ++ now apply in_map.
                   ++ red; tauto.
        }
    - intros [? [?[??]]]; eauto.
  Qed.

  Program Instance SemiAlgebra_Algebra {T:Type} (s:SemiAlgebra T) : Algebra T
    := {|
      alg_in (x:pre_event T) := salgebra_algebra_in s x
    |}.
  Next Obligation.
    apply salgebra_algebra_simpl.
    induction H.
    - exists nil.
      split; [constructor | reflexivity].
    - destruct H as [l1 [?[??]]].
      destruct IHForall as [l2 [??]].
      exists (l1 ++ l2).
      split.
      + now apply Forall_app.
      + rewrite pre_list_union_cons, pre_list_union_app.
        rewrite H2, H4.
        reflexivity.
  Qed.
  Next Obligation.
    apply salgebra_algebra_simpl.
    apply salgebra_algebra_simpl in H.
    destruct H as [ll [??]].
    cut (exists l : list (pre_event T),
            Forall salg_in l /\ pre_event_equiv (pre_list_inter (map pre_event_complement ll)) (pre_list_union l)).
    {
      intros [l [??]].
      exists l.
      split; trivial.
      rewrite H0.
      now rewrite pre_event_complement_list_union.
    }
    clear A H0.
    induction H.
    - simpl.
      destruct (salgebra_algebra_none s) as [?[??]].
      exists x.
      split; trivial.
      now rewrite pre_list_inter_nil.
    - destruct IHForall as [l0 [??]].
      simpl.
      destruct (salg_in_complement x) as [lx [? [??]]]; trivial.
      exists (concat (map (fun x => (map (pre_event_inter x) lx)) l0)).
      split.
      + apply Forall_forall; intros ? inn.
        apply in_concat in inn.
        destruct inn as [? [inn1 inn2]].
        apply in_map_iff in inn1.
        destruct inn1 as [? [? inn1]]; subst.
        apply in_map_iff in inn2.
        destruct inn2 as [? [? inn2]]; subst.
        rewrite Forall_forall in H1, H5.
        apply salg_in_inter; auto.
      + rewrite pre_list_inter_cons.
        rewrite H3, H2.
        rewrite pre_event_inter_pre_list_union_distr.
        rewrite pre_list_union_concat.
        apply pre_list_union_proper.
        rewrite map_map.
        apply Forall2_map_f.
        apply Forall2_refl.
        intros ?.
        rewrite pre_event_inter_comm.
        now rewrite pre_event_inter_pre_list_union_distr.
  Qed.
  Next Obligation.
    apply salgebra_algebra_none.
  Qed.

  Lemma SemiAlgebra_in_algebra {T} (s:SemiAlgebra T):
    pre_event_sub salg_in (alg_in (Algebra:=SemiAlgebra_Algebra s)).
  Proof.
    intros ab ?.
    apply salgebra_algebra_simpl.
    exists [ab].
    split.
    - now repeat constructor.
    - now rewrite pre_list_union_singleton.
  Qed.

  Lemma SemiAlgebra_Algebra_generates_same {T} (s:SemiAlgebra T):
    sa_equiv (generated_sa (alg_in (Algebra:=SemiAlgebra_Algebra s)))
             (generated_sa salg_in).
  Proof.
    apply sa_equiv_subs; split.
    - apply generated_sa_sub_sub; intros ????.
      red in H0.
      destruct H as [?[?[_ ?]]].
      rewrite H1.
      apply sa_pre_list_union; intros.
      apply H0.
      rewrite Forall_forall in H; auto.
    - apply generated_sa_sub_proper.
      intros ??.
      now apply SemiAlgebra_in_algebra.
  Qed.
  
  Definition salg_set {T} (A:SemiAlgebra T): Type := {x | salg_in x}.
  Definition salg_pre {T} {A:SemiAlgebra T} : salg_set A -> (T->Prop)
    := fun e => proj1_sig e.

  Lemma salg_set_in {T} {SAlg:SemiAlgebra T} (a:salg_set SAlg) : salg_in (salg_pre a).
  Proof.
    now destruct a.
  Qed.
  
  Definition salg_sub {T} {SAlg:SemiAlgebra T} (x y:salg_set SAlg) :=
    pre_event_sub (proj1_sig x) (proj1_sig y).

  Definition salg_equiv {T} {SAlg:SemiAlgebra T} (x y:salg_set SAlg) :=
    pre_event_equiv (proj1_sig x) (proj1_sig y).

  Global Instance salg_equiv_equiv {T} {SAlg:SemiAlgebra T} : Equivalence salg_equiv.
  Proof.
    firstorder.
  Qed.
  
  Global Instance salg_equiv_sub {T} {SAlg:SemiAlgebra T}  : subrelation salg_equiv salg_sub.
  Proof.
    firstorder.
  Qed.

  Global Instance salg_sub_pre {T} {SAlg:SemiAlgebra T}  : PreOrder salg_sub.
  Proof.
    firstorder.
  Qed.

  Global Instance salg_sub_part {T} {SAlg:SemiAlgebra T}  : PartialOrder salg_equiv salg_sub.
  Proof.
    firstorder.
  Qed.

  Coercion salg_pre : salg_set >-> Funclass.

  Definition salg_inter {T} {SAlg:SemiAlgebra T} (a b : salg_set SAlg) : salg_set SAlg
    := exist _ (pre_event_inter a b) (salg_in_inter _ _ (salg_set_in a) (salg_set_in b)).

  Context {T} {SAlg:SemiAlgebra T}.

  Global Instance salg_inter_proper : Proper (salg_equiv ==> salg_equiv ==> salg_equiv) salg_inter.
  Proof.
    intros ???????; simpl.
    red in H, H0.
    now apply pre_event_inter_proper.
  Qed.

End semi_algebra.

Section semi_premeasure.
  
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Context {T:Type}.
  Context {SAlg:SemiAlgebra T}.

  Class is_semipremeasure (λ:salg_set SAlg -> Rbar)
    := mk_semipremeasure {
        semipremeasure_proper :> Proper (salg_equiv ==> eq) λ 
      ; semipremeasure_nneg a : Rbar_le 0 (λ a)
                                    
      ; semipremeasure_list_disjoint_union (B:list (salg_set SAlg)) :
        ForallOrdPairs pre_event_disjoint (map salg_pre B) ->
        forall (pf:salg_in (pre_list_union (map salg_pre B))),
        λ (exist _ _ pf) = list_Rbar_sum (map λ B)

      ; semipremeasure_countable_disjoint_union (B:nat->salg_set SAlg) :
        pre_collection_is_pairwise_disjoint (fun x => B x) ->
        forall (pf:salg_in (pre_union_of_collection (fun x => B x))),
        λ (exist _ _ pf) = (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => λ (B n)) i))

      }.

  (* If the semialgebra containts ∅, and the function assigns 0 to it, then
     the list condition is implied by the countable condition 
   *)
  
  Lemma semipremeasure_with_zero_simpl (λ:salg_set SAlg -> Rbar)
        (proper : Proper (salg_equiv ==> eq) λ)
        (nneg : forall a, Rbar_le 0 (λ a))
        (has_none : salg_in pre_event_none)
        (none: λ (exist _ _ has_none) = 0)
        (countable_disjoint_union : forall (B:nat->salg_set SAlg),
        pre_collection_is_pairwise_disjoint (fun x => B x) ->
        forall (pf:salg_in (pre_union_of_collection (fun x => B x))),
        λ (exist _ _ pf) = (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => λ (B n)) i))) :
    is_semipremeasure λ.
  Proof.
    apply mk_semipremeasure; trivial.
    intros.
    specialize (countable_disjoint_union (fun n => nth n B (exist salg_in pre_event_none has_none))).
    cut_to countable_disjoint_union.
    - assert (pff : salg_in
                       (pre_union_of_collection
                          (fun x : nat =>
                             (fun n : nat => nth n B (exist salg_in pre_event_none has_none)) x))).
      {
        eapply salg_proper.
        - apply pre_union_of_collection_proper; intros ?.
          rewrite map_nth; simpl.
          reflexivity.
        - simpl.
          rewrite <- pre_list_union_union in pf.
          apply pf.
      }
      etransitivity; [etransitivity |]
      ; [ | apply (countable_disjoint_union pff) |].
      + apply proper; simpl.
        red; simpl.
        rewrite <- pre_list_union_union.
        apply pre_union_of_collection_proper.
        unfold pre_list_collection.
        intros ??.
        rewrite <- map_nth.
        simpl.
        reflexivity.
      + apply seq_sum_list_sum.
        apply none.
    - apply pre_list_collection_disjoint in H.
      intros ??????.
      specialize (H _ _ H0 x).
      rewrite <- map_nth in H1.
      rewrite <- map_nth in H2.
      simpl in *.
      eauto.
  Qed.

  Lemma semipremeasure_disjoint_list_irrel (λ:salg_set SAlg -> Rbar) {meas:is_semipremeasure λ}
        (R S:list (salg_set SAlg)):
    ForallOrdPairs pre_event_disjoint (map salg_pre R) ->
    ForallOrdPairs pre_event_disjoint (map salg_pre S) ->
    pre_event_equiv (pre_list_union (map salg_pre R)) (pre_list_union (map salg_pre S)) ->
    list_Rbar_sum (map λ R) = list_Rbar_sum (map λ S).
  Proof.
      intros disjR disjS eqq.

      assert (eqqr:forall Ri, In Ri R ->
                         λ Ri =
                           list_Rbar_sum (map λ (map (fun s => salg_inter Ri s) S))).
      {
        intros.

        assert (eqq':Forall2 pre_event_equiv
                             (map (fun s : salg_set SAlg => pre_event_inter Ri s) S)
                             (map (pre_event_inter Ri) (map salg_pre S))).
        {
          rewrite map_map.
          apply Forall2_map_f.
          now apply Forall2_refl; intros ?.
        }
        assert (eqqi:pre_event_equiv
                       (pre_list_union (map salg_pre (map (fun s : salg_set SAlg => salg_inter Ri s) S)))
                       Ri).
        {
          unfold salg_inter.
          rewrite map_map; simpl.
          rewrite eqq'.
          rewrite <- pre_event_inter_pre_list_union_distr.
          rewrite <- eqq.
          apply pre_event_inter_sub_l_equiv.
          intros ??.
          eexists; split; try apply H0.
          apply in_map_iff; eauto.
        }           
      
        assert (pf:salg_in (pre_list_union (map salg_pre (map (fun s : salg_set SAlg => salg_inter Ri s) S)))).
        {
          rewrite eqqi.
          now destruct Ri; simpl.
        }
        
        rewrite <- semipremeasure_list_disjoint_union with (pf0:=pf).
        - apply semipremeasure_proper.
          now red.
        - apply pre_list_disjoint_inter with (a:=Ri) in disjS.
          rewrite map_map in disjS.
          now rewrite map_map.
      }

      assert (eqqs:forall Si, In Si S ->
                 λ Si =
                   list_Rbar_sum (map λ (map (fun r => salg_inter r Si) R))).
      {
        intros.

        assert (eqq':Forall2 pre_event_equiv
                             (map (fun x : salg_set SAlg => pre_event_inter x Si) R)
                             (map (pre_event_inter Si) (map salg_pre R))).
        {
          rewrite map_map.
          apply Forall2_map_f.
          apply Forall2_refl; intros ?.
          apply pre_event_inter_comm.
        }
        assert (eqqi:pre_event_equiv
                       (pre_list_union (map salg_pre (map (fun r : salg_set SAlg => salg_inter r Si) R)))
                       Si).
        {
          unfold salg_inter.
          rewrite map_map; simpl.
          rewrite eqq'.
          rewrite <- pre_event_inter_pre_list_union_distr.
          rewrite eqq.
          apply pre_event_inter_sub_l_equiv.
          intros ??.
          eexists; split; try apply H0.
          apply in_map_iff; eauto.
        }           
      
        assert (pf:salg_in (pre_list_union (map salg_pre (map (fun r : salg_set SAlg => salg_inter r Si) R)))).
        {
          rewrite eqqi.
          now destruct Si; simpl.
        } 
        rewrite <- semipremeasure_list_disjoint_union with (pf0:=pf).
        - apply semipremeasure_proper.
          now red.
        - apply pre_list_disjoint_inter with (a:=Si) in disjR.
          rewrite map_map in disjR.
          rewrite map_map.
          revert disjR.
          apply (ForallOrdPairs_Forall2_prop pre_event_equiv).
          + intros ???????. eapply pre_event_disjoint_eq_proper; eauto; symmetry; eauto.
          + apply Forall2_map_f.
            apply Forall2_refl.
            intros ?; simpl.
            apply pre_event_inter_comm.
      }

      assert (eqq1:list_Rbar_sum (map λ R) = list_Rbar_sum (map (fun Ri => list_Rbar_sum (map λ (map (fun s : salg_set SAlg => salg_inter Ri s) S))) R)).
      {
        f_equal.
        apply map_ext_in; intros.
        now apply eqqr.
      }

      assert (eqq2:list_Rbar_sum (map λ S) = list_Rbar_sum (map (fun Si => list_Rbar_sum (map λ (map (fun r : salg_set SAlg => salg_inter r Si) R))) S)).
      {
        f_equal.
        apply map_ext_in; intros.
        now apply eqqs.
      }
      rewrite eqq1, eqq2.
      erewrite map_ext
      ; [| intros; rewrite map_map; reflexivity].
      rewrite list_Rbar_sum_nneg_nested_swap.
      - f_equal.
        apply map_ext; intros.
        now rewrite map_map.
      - intros.
        apply semipremeasure_nneg.
  Qed.

    Lemma semipremeasure_disjoint_list_countable_irrel (λ:salg_set SAlg -> Rbar) {meas:is_semipremeasure λ}
          (R:list (salg_set SAlg))
          (S:nat -> salg_set SAlg):
    ForallOrdPairs pre_event_disjoint (map salg_pre R) ->
    pre_collection_is_pairwise_disjoint (fun x => S x) ->
    pre_event_equiv (pre_list_union (map salg_pre R))  (pre_union_of_collection S) ->
    list_Rbar_sum (map λ R) = ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => λ (S n)) i).
    Proof.
      intros disjR disjS eqq.

      assert (eqqr:forall Ri, In Ri R ->
                    λ Ri =
                      ELim_seq (sum_Rbar_n (fun j : nat => λ (salg_inter Ri (S j))))).
      {
        intros.

        assert (eqqi:pre_event_equiv
                  (pre_union_of_collection (fun x : nat => salg_inter Ri (S x)))
                  Ri).
        {
          unfold salg_inter; simpl.
          rewrite <- pre_event_inter_countable_union_distr.
          rewrite <- eqq.
          apply pre_event_inter_sub_l_equiv.
          intros ??.
          eexists; split; try apply H0.
          now apply in_map.
        }           
      
        assert (pf:salg_in (pre_union_of_collection (fun x : nat => salg_inter Ri (S x)))).
        {
          rewrite eqqi.
          now destruct Ri; simpl.
        } 
        rewrite <- semipremeasure_countable_disjoint_union with (pf0:=pf).
        - apply semipremeasure_proper.
          now red.
        - now apply pre_collection_is_pairwise_disjoint_inter.
      }

      assert (eqqs:forall j, 
                 λ (S j) =
                   list_Rbar_sum (map λ (map (fun r => salg_inter r (S j)) R))).
      {
        intros.

        assert (eqq':Forall2 pre_event_equiv
                             (map (fun x : salg_set SAlg => pre_event_inter x (S j)) R)
                             (map (pre_event_inter (S j)) (map salg_pre R))).
        {
          rewrite map_map.
          apply Forall2_map_f.
          apply Forall2_refl; intros ?.
          apply pre_event_inter_comm.
        }
        assert (eqqi:pre_event_equiv
                       (pre_list_union (map salg_pre (map (fun r : salg_set SAlg => salg_inter r (S j)) R)))
                       (S j)).
        {
          unfold salg_inter.
          rewrite map_map; simpl.
          rewrite eqq'.
          rewrite <- pre_event_inter_pre_list_union_distr.
          rewrite eqq.
          apply pre_event_inter_sub_l_equiv.
          intros ??.
          red; eauto.
        }           
      
        assert (pf:salg_in (pre_list_union (map salg_pre (map (fun r : salg_set SAlg => salg_inter r (S j)) R)))).
        {
          rewrite eqqi.
          now destruct (S j); simpl.
        } 
        rewrite <- semipremeasure_list_disjoint_union with (pf0:=pf).
        - apply semipremeasure_proper.
          now red.
        - apply pre_list_disjoint_inter with (a:=S j) in disjR.
          rewrite map_map in disjR.
          rewrite map_map.
          revert disjR.
          apply (ForallOrdPairs_Forall2_prop pre_event_equiv).
          + intros ???????. eapply pre_event_disjoint_eq_proper; eauto; symmetry; eauto.
          + apply Forall2_map_f.
            apply Forall2_refl.
            intros ?; simpl.
            apply pre_event_inter_comm.
      }

      assert (eqq1:list_Rbar_sum (map λ R) = list_Rbar_sum (map (fun Ri => ELim_seq (sum_Rbar_n (fun j : nat => λ (salg_inter Ri (S j))))) R)).
      {
        f_equal.
        apply map_ext_in; intros.
        now apply eqqr.
      }

      assert (eqq2:  ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => λ (S n)) i) =
                       ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat =>
                                                         list_Rbar_sum (map λ (map (fun r : salg_set SAlg => salg_inter r (S n)) R))) i)).
      {
        apply ELim_seq_ext; intros.
        unfold sum_Rbar_n; f_equal.
        apply map_ext; intros.
        apply eqqs.
      } 

      rewrite eqq1, eqq2.
      rewrite list_Rbar_ELim_seq_nneg_nested_swap.
      - apply ELim_seq_ext; intros.
        unfold sum_Rbar_n.
        f_equal.
        apply map_ext; intros.
        now rewrite map_map.
      - intros.
        apply semipremeasure_nneg.
    Qed.

    Ltac nth_destr_in H
      := match type of H with
         | context [nth ?a ?b ?c] => let HH := fresh "ntheq" in
                                    destruct (nth_in_or_default a b c) as [HH|HH]
                                    ; [| rewrite HH in H]
         end.

    (* this should be true without needing none
       but that is a bit of a pain to show
       and in practice we have none, so it it not needed for now *)
    Lemma semipremeasure_disjoint_list_countable_list_irrel_with_default
          (λ:salg_set SAlg -> Rbar) {meas:is_semipremeasure λ}
          (has_none : salg_in pre_event_none)
          (none: λ (exist _ _ has_none) = 0)
          (R:list (salg_set SAlg))
          (S:nat -> list (salg_set SAlg)):
      ForallOrdPairs pre_event_disjoint (map salg_pre R) ->
      pre_collection_is_pairwise_disjoint (fun x => pre_list_union (map salg_pre (S x))) ->
      (forall n, ForallOrdPairs pre_event_disjoint (map salg_pre (S n))) ->
      pre_event_equiv (pre_list_union (map salg_pre R)) (pre_union_of_collection (fun x => (pre_list_union (map salg_pre (S x))))) ->
      list_Rbar_sum (map λ R) = ELim_seq (sum_Rbar_n (fun n : nat => (list_Rbar_sum (map λ (S n))))).
    Proof.
      intros.
      transitivity (
          ELim_seq (sum_Rbar_n (fun n : nat =>
                                  ELim_seq (fun i : nat => sum_Rbar_n (fun k : nat => λ (nth k (S n) (exist _ _ has_none))) i)))).
      - rewrite ELim_seq_Elim_seq_pair.
        + transitivity (
              ELim_seq
                (fun i : nat =>
                   sum_Rbar_n (fun n : nat => λ (nth (snd (iso_b n)) (S (fst (iso_b n))) (exist salg_in pre_event_none has_none)))
                              i)).
          * apply semipremeasure_disjoint_list_countable_irrel; trivial.
            -- red in H0.
               intros ??????.
               nth_destr_in H4; [| red in H4; tauto].
               nth_destr_in H5; [| red in H5; tauto].
               destruct (Nat.eq_dec (fst (iso_b n1)) (fst (iso_b n2))).
               ++ rewrite e in *.
                  specialize (H1 (fst (iso_b n2))).
                  apply pre_list_collection_disjoint in H1.
                  destruct (Nat.eq_dec (snd (iso_b n1)) (snd (iso_b n2))).
                  ** assert (iso_b (Isomorphism:=nat_pair_encoder) n1 = iso_b (Isomorphism:=nat_pair_encoder) n2).
                     { apply injective_projections; trivial. }
                     apply (f_equal (iso_f (Isomorphism:=nat_pair_encoder))) in H6.
                     repeat rewrite iso_f_b in H6.
                     auto.
                  ** apply (H1 _ _ n x).
                     --- red.
                         now rewrite <- map_nth in H4.
                     --- red.
                         now rewrite <- map_nth in H5.
               ++ apply (H0 _ _ n x).
                  ** eexists; split; try apply H4.
                     now apply in_map.
                  ** eexists; split; try apply H5.
                     now apply in_map.
            -- rewrite H2; intros x.
               { 
                 split.
                 - intros [?[?[??]]].
                   red.
                   apply in_map_iff in H3.
                   destruct H3 as [?[??]]; subst.
                   apply In_nth with (d:=(exist salg_in pre_event_none has_none)) in H5.
                   destruct H5 as [?[??]]; subst.
                   exists (iso_f (x0, x1)).
                   now repeat rewrite iso_b_f; simpl.
                 - intros [??].
                   red.
                   nth_destr_in H3; [| red in H3; tauto].
                   exists (fst (iso_b x0)).
                   eexists; split; try apply H3.
                   apply in_map_iff; eauto.
               } 
          * apply ELim_seq_ext; intros.
            unfold sum_Rbar_n; f_equal; intros.
            apply map_ext; intros.
            match_destr.
        + intros.
          apply semipremeasure_nneg.
      - apply ELim_seq_ext; intros.
        unfold sum_Rbar_n at 1 3; f_equal.
        apply map_ext; intros.
        now rewrite seq_sum_list_sum.
    Qed.

  (* Now, we can extend a semipremeasure on a semialgebra to a premeasure on the generated algebra *)

  (* very classic *)
  Definition premeasure_of_semipremeasure (λ:salg_set SAlg -> Rbar) :
    (alg_set (SemiAlgebra_Algebra SAlg) -> Rbar).
  Proof.
    intros [x xin].
    simpl in xin.
    apply IndefiniteDescription.constructive_indefinite_description in xin.
    destruct xin as [a [Fin eqq]].
    exact (list_Rbar_sum (map λ (list_dep_zip _ Fin))).
  Defined.

  (* but, at least it is well defined *)
  Global Instance premeasure_of_semipremeasure_proper (λ:salg_set SAlg -> Rbar) {meas:is_semipremeasure λ} :
    Proper (alg_equiv ==> eq) (premeasure_of_semipremeasure λ).
  Proof.
    unfold premeasure_of_semipremeasure.
    intros ???.
    destruct x; destruct y; simpl in *.
    red in H; simpl in H.
    repeat match_destr.
    destruct a1; destruct a2.
    apply semipremeasure_disjoint_list_irrel; trivial.
    - unfold salg_pre, salg_set; simpl.
      now rewrite list_dep_zip_map1.
    - unfold salg_pre, salg_set; simpl.
      now rewrite list_dep_zip_map1.
    - unfold salg_pre, salg_set; simpl.
      repeat rewrite list_dep_zip_map1.
      now rewrite <- H1, <- H3.
  Qed.

  Global Instance premeasure_of_semipremeasure_premeasure
         (λ:salg_set SAlg -> Rbar) {meas:is_semipremeasure λ}
         (has_none : salg_in pre_event_none)
         (none: λ (exist _ _ has_none) = 0)
    :
    is_premeasure (premeasure_of_semipremeasure λ).
  Proof.
    constructor.
    - now apply premeasure_of_semipremeasure_proper.
    - unfold premeasure_of_semipremeasure.
      unfold alg_none.
      repeat match_destr.
      destruct a.
      rewrite (semipremeasure_disjoint_list_irrel _ _ nil).
      + now simpl.
      + unfold salg_pre, salg_set; simpl.
        now rewrite list_dep_zip_map1.
      + simpl; constructor.
      + unfold salg_pre, salg_set; simpl.
        rewrite list_dep_zip_map1.
        rewrite pre_list_union_nil.
        now symmetry.
    - intros.
      unfold premeasure_of_semipremeasure.
      destruct a.
      repeat match_destr.
      apply list_Rbar_sum_nneg_nneg; intros.
      apply in_map_iff in H.
      destruct H as [? [??]]; subst.
      apply semipremeasure_nneg.
    - intros.
      unfold premeasure_of_semipremeasure at 1.
      repeat match_destr.
      destruct a as [??].
      assert (forall i, exists S,
                   ForallOrdPairs pre_event_disjoint S /\
                   pre_event_equiv (B i) (pre_list_union S) /\
                   exists (F:Forall salg_in S),
                     premeasure_of_semipremeasure λ (B i) =
                       (list_Rbar_sum (map λ (list_dep_zip _ F)))).
      {
        intros.
        unfold premeasure_of_semipremeasure.
        repeat match_destr.
        destruct a0.
        eauto.
      } 
      apply choice in H2.
      destruct H2 as [l HH].

      assert (forall x, exists F : Forall salg_in (l x),
                 premeasure_of_semipremeasure λ (B x) = list_Rbar_sum (map λ (list_dep_zip (l x) F))).
      {
        intros a.
        destruct (HH a); tauto.
      }
      apply (Coq.Logic.ChoiceFacts.non_dep_dep_functional_choice choice) in H2.
      destruct H2 as [??].
      transitivity (ELim_seq (sum_Rbar_n (fun n : nat =>
                                            list_Rbar_sum (map λ (list_dep_zip (l n) (x0 n)))))).
      + apply (semipremeasure_disjoint_list_countable_list_irrel_with_default _ has_none none); trivial.
        * unfold salg_pre, salg_set; simpl.
          now rewrite list_dep_zip_map1.
        * unfold salg_pre, salg_set; simpl.
          eapply pre_collection_is_pairwise_disjoint_pre_event_sub_proper
          ; try eapply H.
          intros ?.
          rewrite list_dep_zip_map1.
          destruct (HH a) as [?[??]].
          rewrite H4.
          reflexivity.
        * intros.
          unfold salg_pre, salg_set; simpl.
          rewrite list_dep_zip_map1.
          now destruct (HH n).
        * unfold salg_pre, salg_set; simpl.
          repeat rewrite list_dep_zip_map1.
          intros ?.
          split.
          -- intros HH2.
             apply H1 in HH2.
             destruct HH2 as [n HH2].
             exists n.
             rewrite list_dep_zip_map1.
             destruct (HH n) as [_ [HH3 _]].
             now apply HH3.
          -- intros [?[?[??]]].
             rewrite list_dep_zip_map1 in H3.
             destruct (HH x2) as [_ [HH3 _]].
             apply H1.
             exists x2.
             apply HH3.
             red; eauto.
      + apply ELim_seq_ext; intros.
        unfold sum_Rbar_n; f_equal.
        apply map_ext; intros.
        auto.
  Qed.

    Lemma premeasure_of_semipremeasure_same
        (λ : salg_set SAlg -> Rbar)
        {meas : is_semipremeasure λ}
        x
        (pf1 : salg_in x)
        (pf2 : alg_in (Algebra:=(SemiAlgebra_Algebra SAlg)) x) :
      premeasure_of_semipremeasure λ (exist _ x pf2) = λ (exist _ x pf1).
    Proof.
      unfold premeasure_of_semipremeasure.
      repeat match_destr.
      destruct a.
      assert (pf:salg_in (pre_list_union (map salg_pre (list_dep_zip x0 f)))).
      {
        unfold salg_pre, salg_set.
        rewrite list_dep_zip_map1.
        now rewrite <- H0.
      }
      rewrite <- (semipremeasure_list_disjoint_union ((list_dep_zip x0 f))) with (pf0:=pf).
      - eapply semipremeasure_proper; red; simpl.
        unfold salg_pre, salg_set.
        rewrite list_dep_zip_map1.
        now symmetry.
      - unfold salg_pre, salg_set.
        now rewrite list_dep_zip_map1.
    Qed.

End semi_premeasure.

Section caratheodory_semi.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Context {T:Type}.
  Context {SAlg:SemiAlgebra T}.
  Context (has_none : salg_in pre_event_none).
  Context (λ:salg_set SAlg -> Rbar).
  Context {meas:is_semipremeasure λ}.
  Context (none: λ (exist _ _ has_none) = 0).

  Instance semi_σ : SigmaAlgebra T
    := μ_measurable_sa (μ_outer:=outer_λ_outer_measure _
                                       (λ_meas:=premeasure_of_semipremeasure_premeasure
                                                  _ has_none none))
                       (outer_λ (premeasure_of_semipremeasure λ)).

  Lemma semi_σ_in : pre_event_sub salg_in (sa_sigma (SigmaAlgebra:=semi_σ)).
  Proof.
    intros ??.
    simpl.
    apply SemiAlgebra_in_algebra in H.
    generalize (outer_λ_is_measurable (Alg:=SemiAlgebra_Algebra SAlg))
    ; intros HH.
    specialize (HH _ (premeasure_of_semipremeasure_premeasure _ has_none none)).
    specialize (HH (exist _ _ H)).
    now simpl in HH.
  Qed.

  Lemma semi_σ_sa_sigma (x:salg_set SAlg) : sa_sigma x.
  Proof.
    destruct x; simpl.
    now apply semi_σ_in.
  Qed.

  Definition semi_as_semi_σ (x:salg_set SAlg) : event semi_σ
    := exist _ _ (semi_σ_sa_sigma x).
  
  Definition semi_μ : pre_event T -> Rbar
    := outer_λ ((premeasure_of_semipremeasure λ)).

  Instance semi_μ_measurable : is_measure (σ:=semi_σ) semi_μ.
  Proof.
    apply μ_measurable_sa_measure.
  Qed.

  Lemma semi_μ_λ (x:salg_set SAlg) : semi_μ x = λ x.
  Proof.
    unfold semi_μ.
    destruct x; simpl.

    generalize (outer_λ_λ (Alg:=SemiAlgebra_Algebra SAlg))
    ; intros HH.
    specialize (HH _ (premeasure_of_semipremeasure_premeasure _ has_none none)).
    assert (alg_in (Algebra:=SemiAlgebra_Algebra SAlg) x)
      by (now apply SemiAlgebra_in_algebra).
    specialize (HH (exist _ _ H)).
    simpl alg_pre in HH.
    rewrite HH.
    now apply premeasure_of_semipremeasure_same.
  Qed.

End caratheodory_semi.
  
(*
Section measure_product.

  Context {X Y:Type}.
  Context {A:SigmaAlgebra X}.
  Context {B:SigmaAlgebra Y}.

  Context (α : event A -> Rbar) (meas_α : is_measure α).
  Context (β : event B -> Rbar) (meas_β : is_measure β).
  
  Definition is_measurable_rectangle (ab : pre_event (X*Y)) : Prop
    := exists (a:event A) (b:event B), forall x y, ab (x,y) <-> a x /\ b y.

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

  (*
  Program Instance PairAlgebra : Algebra (X*Y)
    := {|
      alg_in (x:pre_event (X*Y)) := exists (l:list (pre_event (X*Y))),
        Forall is_measurable_rectangle l /\
        pre_event_equiv x (pre_list_union l)
  |}.
  Next Obligation.
    induction H.
    - exists nil.
      split; [constructor | reflexivity].
    - destruct H as [l1 [??]].
      destruct IHForall as [l2 [??]].
      exists (l1 ++ l2).
      split.
      + now apply Forall_app.
      + rewrite pre_list_union_cons, pre_list_union_app.
        rewrite H1, H3.
        reflexivity.
  Qed.
  Next Obligation.
    cut (exists l : list (pre_event (X * Y)),
            Forall is_measurable_rectangle l /\ pre_event_equiv (pre_list_inter (map pre_event_complement H)) (pre_list_union l)).
    {
      intros [l [??]].
      exists l.
      split; trivial.
      rewrite H1.
      now rewrite pre_event_complement_list_union.
    }
    clear A0 H1.
    induction H0.
    - exists [pre_Ω].
      split.
      + repeat constructor.
        apply is_measurable_rectangle_all.
      + simpl. rewrite pre_list_inter_nil, pre_list_union_singleton.
        reflexivity.
    - destruct IHForall as [l0 [??]].
      simpl.
      destruct (is_union_measurable_rectangle_complement x) as [lx [??]]; trivial.
      exists (concat (map (fun x => (map (pre_event_inter x) lx)) l0)).
      split.
      + apply Forall_forall; intros ? inn.
        apply in_concat in inn.
        destruct inn as [? [inn1 inn2]].
        apply in_map_iff in inn1.
        destruct inn1 as [? [? inn1]]; subst.
        apply in_map_iff in inn2.
        destruct inn2 as [? [? inn2]]; subst.
        rewrite Forall_forall in H1, H3.
        apply is_measurable_rectangle_inter; auto.
      + rewrite pre_list_inter_cons.
        rewrite H4, H2.
        rewrite pre_event_inter_pre_list_union_distr.
        rewrite pre_list_union_concat.
        apply pre_list_union_proper.
        rewrite map_map.
        apply Forall2_map_f.
        apply Forall2_refl.
        intros ?.
        rewrite pre_event_inter_comm.
        now rewrite pre_event_inter_pre_list_union_distr.
  Qed.
  Next Obligation.
    exists [pre_Ω].
    split.
    - repeat constructor.
      apply is_measurable_rectangle_all.
    - now rewrite pre_list_union_singleton.
  Qed.

  Lemma measurable_rectangle_in_pair_algebra :
    pre_event_sub is_measurable_rectangle (alg_in (Algebra:=PairAlgebra)).
  Proof.
    intros ab ?.
    exists [ab].
    split.
    - now repeat constructor.
    - now rewrite pre_list_union_singleton.
  Qed.
*)

  (*
  (* the SigmaAlgebra generated from the PairAlgebra is the same as that generated
     directly from the underlying measurable rectangles relation *)
  Lemma PairAlgebra_generates_same :
    sa_equiv (generated_sa (alg_in (Algebra:=PairAlgebra)))
             (generated_sa is_measurable_rectangle).
  Proof.
    apply sa_equiv_subs; split.
    - apply generated_sa_sub_sub; intros ????.
      red in H0.
      destruct H as [?[??]].
      rewrite H1.
      apply sa_pre_list_union; intros.
      apply H0.
      rewrite Forall_forall in H; auto.
    - apply generated_sa_sub_proper.
      apply measurable_rectangle_in_pair_algebra.
  Qed.
*)
  (* this is very classic *)
  Definition measurable_rectangle_product_λ ab :
    is_measurable_rectangle ab -> Rbar.
  Proof.
    unfold is_measurable_rectangle.
    intros HH.
    apply IndefiniteDescription.constructive_indefinite_description in HH.
    destruct HH as [a HH].
    apply IndefiniteDescription.constructive_indefinite_description in HH.
    destruct HH as [b HH].
    exact (Rbar_mult (α a) (β b)).
  Defined.

  (* well, at least the definition is meaningful *)
  Lemma measurable_rectangle_product_λ_ext ab
        (pf1 pf2:is_measurable_rectangle ab) :
    measurable_rectangle_product_λ ab pf1 = measurable_rectangle_product_λ ab pf2.
  Proof.
    unfold measurable_rectangle_product_λ.
    repeat match_destr.
    destruct e as [??].
    destruct e0 as [??].
    destruct pf1 as [? [??]].
    destruct pf2 as [? [??]].

    destruct (classic_event_none_or_has x) as [[??]|?].
    - destruct (classic_event_none_or_has x0) as [[??]|?].
      + destruct (i x9 x10) as [_ ?].
          cut_to H5; [| tauto].
          apply i0 in H5.
          destruct H5.
          f_equal.
        * apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i c x10).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             apply i0 in H7.
             tauto.
          -- specialize (i0 c x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply i in H7.
             tauto.
        * apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i x9 c).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             apply i0 in H7.
             tauto.
          -- specialize (i0 x9 c).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply i in H7.
             tauto.
      + rewrite H4.
        destruct (classic_event_none_or_has x2) as [[??]|?].
        * destruct (classic_event_none_or_has x1) as [[??]|?].
          -- specialize (i0 x11 x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
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

  Lemma measurable_rectangle_product_λ_nneg ab (pf:is_measurable_rectangle ab) :
    Rbar_le 0 (measurable_rectangle_product_λ ab pf).
  Proof.
    unfold measurable_rectangle_product_λ.
    repeat match_destr.
    apply Rbar_mult_nneg_compat; apply measure_nneg.
  Qed.
  
  Lemma measurable_rectangle_product_λ_additive (c:nat -> pre_event (X * Y))
    (disj:pre_collection_is_pairwise_disjoint c)
    (measn:forall n, is_measurable_rectangle (c n)) 
    (meas:is_measurable_rectangle (pre_union_of_collection c)) :
    measurable_rectangle_product_λ (pre_union_of_collection c) meas = 
      ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => measurable_rectangle_product_λ (c n) (measn n)) i).
  Proof.y

    assert (
    
    
    intros.
      
    measure_countable_disjoint_union (B:nat->event σ) :
      collection_is_pairwise_disjoint B ->
      μ (union_of_collection B) = (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i))

    measurable_rectangle_product_λ ab pf1 = measurable_rectangle_product_λ ab pf2.

  
End measure_product.
*)
