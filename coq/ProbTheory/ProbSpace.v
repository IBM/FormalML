Require Import Program.Basics.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.

Require Import Classical ClassicalFacts.
Require Import ClassicalChoice.
Require Import ProofIrrelevance.
Require Ensembles.
Require Import hilbert.

Require Import utils.Utils DVector.
Import ListNotations.
Require Export Event.

Require Import SigmaAlgebras.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

(* Prop: the sum of probabilities for everything in the collection == R. *)
Definition sum_of_probs_equals {T:Type} {σ:SigmaAlgebra T}
           (p : event σ -> R)
           (collection: nat -> event σ) (result: R) :=
  infinite_sum' (fun n:nat => p (collection n)) result.

Class ProbSpace {T:Type} (σ:SigmaAlgebra T) :=
  {
    ps_P : event σ -> R;
    ps_proper :> Proper (event_equiv ==> eq) ps_P ;
    
    ps_countable_disjoint_union (collection: nat -> event σ) :
      (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
      collection_is_pairwise_disjoint collection ->
      sum_of_probs_equals ps_P collection (ps_P (union_of_collection collection));
    
    ps_one : ps_P Ω = R1;
    
    ps_pos (A:event σ): (0 <= ps_P A)%R
  }.

Lemma ps_all {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) : ps_P Ω = R1.
Proof.
  apply ps_one.
Qed.

(* P numbers are as per https://www.stat.washington.edu/~nehemyl/files/UW_MATH-STAT394_axioms-proba.pdf *)
(* P1.1 *)
Lemma ps_none {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) : ps_P ∅ = R0.
Proof.
  generalize (ps_countable_disjoint_union
                (fun n => match n with
                          | 0 => Ω
                          | _ => ∅
                          end))
  ; intros HH.
  cut_to HH.
  - simpl in HH.
    red in HH.
    apply (infinite_sum'_split 1) in HH.
    simpl in HH.

    apply (infinite_sum'_ext (fun x : nat => ps_P match (x + 1)%nat with
                                                  | 0%nat => Ω
                                                  | S _ => ∅
                                                  end)
                             (fun x : nat => ps_P ∅)) in HH.
    + rewrite (@ps_proper _ _ _ (union_of_collection
                           (fun n : nat => match n with
                                           | 0%nat => Ω
                                           | S _ => ∅
                                           end)) (Ω)) in HH.
      * replace (ps_P (ProbSpace:=ps) Ω) with R1 in HH
          by (symmetry; apply ps_one).
        replace (R1 - (0 + R1))%R with R0 in HH by lra.
        eapply infinite_sum'_const1; eauto.
      * unfold event_equiv, pre_event_equiv, Ω, pre_Ω; simpl; intuition.
        exists 0%nat; trivial.
    + destruct x; simpl; trivial.
  - unfold collection_is_pairwise_disjoint; intros.
    repeat match_destr; repeat red; tauto.
Qed.

Hint Rewrite @ps_none @ps_all : prob.

Local Open Scope R.

(* P1.2 *)
Lemma ps_list_disjoint_union {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (l: list (event σ)) :
  (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
  ForallOrdPairs event_disjoint l ->
  ps_P (list_union l) = fold_right Rplus 0 (map ps_P l).
Proof.
  intros Hd.
  generalize (ps_countable_disjoint_union (list_collection l ∅)); intros HH.
  cut_to HH.
  - unfold sum_of_probs_equals in HH.
    erewrite ps_proper in HH; [| eapply list_union_union ].
    apply (infinite_sum'_split (length l)) in HH.
    apply (infinite_sum'_ext  (fun x : nat => ps_P (list_collection l ∅ (x + length l)))
                              (fun x : nat => 0)) in HH.
    + apply infinite_sum'_const2 in HH.
      apply Rminus_diag_uniq in HH.
      rewrite HH.
      clear.
      unfold list_collection.
      rewrite sum_f_R0'_as_fold_right.
      rewrite (list_as_nthseq l ∅) at 2.
      rewrite map_map.
      rewrite fold_right_map; trivial.
    + intros.
      erewrite ps_proper; [eapply ps_none | ]; intros.
      unfold list_collection.
      rewrite nth_overflow; intuition.
  - apply list_collection_disjoint; trivial.
Qed.

Lemma ps_disjoint_union {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (x1 x2: event σ) :
  (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
  event_disjoint x1 x2 ->
  ps_P (x1 ∪ x2) = ps_P x1 + ps_P x2.
Proof.
  intros disj.
  rewrite <- list_union2.
  rewrite ps_list_disjoint_union; simpl.
  - lra.
  - repeat constructor; trivial.
Qed.

(* P1.3 *)
Lemma ps_sub {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A B: event σ) :
  A ≤ B -> ps_P A <= ps_P B.
Proof.
  intros impl.
  generalize (ps_disjoint_union ps
                                A (B \ A)); intros HH.
  rewrite event_union_diff_sub in HH; trivial.
  - rewrite HH.
    + generalize (ps_pos (B \ A)); intros.
      lra.
    + apply event_disjoint_diff.
  - apply sa_dec.
Qed.

(* C1.1 *)
Lemma ps_le1 {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A: event σ)
  : ps_P A <= R1.
Proof.
  intros.
  rewrite <- ps_one.
  apply ps_sub.
  apply event_sub_true.
Qed.

 Lemma ps_P_sub_zero {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ)
       (E1 E2 : event  σ) :
   event_sub E1 E2 -> ps_P E2 = 0 -> ps_P E1 = 0.
 Proof.
   intros.
   generalize (ps_sub _ E1 E2 H); intros.
   rewrite H0 in H1.
   generalize (ps_pos E1); intros.
   lra.
 Qed.



(* P1.4 *)
Lemma ps_countable_total {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A:event σ) (coll:nat -> event σ) :
  collection_is_pairwise_disjoint coll ->
  union_of_collection coll === Ω ->
  infinite_sum' (fun i => ps_P (A ∩ (coll i))) (ps_P A).
Proof.
  intros disjC partC.
  rewrite <- (event_inter_true_r A).
  rewrite <- partC.
  rewrite event_inter_countable_union_distr.
  apply ps_countable_disjoint_union.
  - apply collection_is_pairwise_disjoint_sub; auto with prob.
Qed.

Lemma ps_list_total {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A:event σ) (l: list (event σ)) :
  ForallOrdPairs event_disjoint l ->
  list_union l === Ω ->
  ps_P A = fold_right Rplus 0 (map ps_P (map (event_inter A) l)).
Proof.
  intros.
  rewrite <- ps_list_disjoint_union.
  - rewrite <- event_inter_list_union_distr.
    rewrite H0.
    autorewrite with prob.
    trivial.
  - apply ForallOrdPairs_impl; trivial.
    apply ForallPairs_ForallOrdPairs.
    firstorder.
Qed.

Lemma ps_total {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A B C:event σ) :
  event_disjoint B C ->
  B ∪ C === Ω ->
  ps_P A = ps_P (A ∩ B) + ps_P (A ∩ C).
Proof.
  intros.
  intros.
  rewrite (ps_list_total ps A [B;C]); trivial.
  - simpl; lra.
  - repeat constructor; trivial.
  - rewrite list_union2; trivial.
Qed.

(* P1.5 *)
Lemma ps_complement {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A: event σ) :
  ps_P (¬ A) = 1 - ps_P A.
Proof.
  generalize (ps_total ps Ω A (¬ A)); intros HH.
  cut_to HH; eauto with prob.
  rewrite ps_one in HH.
  autorewrite with prob in HH.
  lra.
Qed.

(* P1.6 *)
Lemma ps_union {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A B: event σ) :
  ps_P (A ∪ B) = ps_P A + ps_P B - ps_P (A ∩ B).
Proof.
  rewrite <- ps_event_union_diff.
  rewrite ps_disjoint_union by eauto with prob.
  rewrite (ps_total ps B A (¬ A)) by eauto with prob.
  rewrite event_diff_derived.  
  rewrite (event_inter_comm A B).
  lra.
Qed.

Lemma ps_inter_bound {T:Type} {σ:SigmaAlgebra T} 
      (A B : event σ) (prts : ProbSpace σ) :
  ps_P (event_inter A B) >= ps_P A + ps_P B - 1.
Proof.
  generalize (ps_union prts A B); intros.
  assert (ps_P (event_union A B) <= 1) by apply ps_le1.
  lra.
Qed.

(* P1.7 inclusion/exclusion identity should not be hard to prove, 
   but is somewhat painful to state so it is omitted for now.
   We state and prove the case for n=3 for fun
 *)

Lemma ps_union3 {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A B C: event σ) :
  ps_P (A ∪ B ∪ C) =
  ps_P A + ps_P B + ps_P C
                    - ps_P (A ∩ B) - ps_P (A ∩ C) - ps_P (B ∩ C)
  + ps_P (A ∩ B ∩ C).
Proof.
  rewrite (ps_union ps (A ∪ B) C) by auto with prob.
  rewrite (ps_union ps A B) by auto with prob.
  rewrite (event_inter_comm (A ∪ B) C).
  rewrite event_inter_union_distr.
  rewrite (ps_union ps (C ∩ A) (C ∩ B)) by auto with prob.
  rewrite (event_inter_comm A C).
  rewrite (event_inter_comm B C).
  cut ((C ∩ A) ∩ (C ∩ B) === (A ∩ B) ∩ C).
  { intros eqq; rewrite eqq; lra. }
  rewrite event_inter_assoc.
  rewrite (event_inter_comm (C ∩ A) C).
  rewrite event_inter_assoc.
  autorewrite with prob.
  rewrite (event_inter_comm C A).
  rewrite <- event_inter_assoc.
  rewrite (event_inter_comm C B).
  rewrite event_inter_assoc.
  reflexivity.
Qed.

Lemma ps_boole_inequality {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ)
      (l: list (event σ)) :
  ps_P (list_union l) <= fold_right Rplus 0 (map ps_P l).
Proof.
  intros.
  induction l; simpl.
  - autorewrite with prob.
    lra.
  - autorewrite with prob.
    rewrite ps_union; trivial.
    generalize ( ps_pos (a ∩ list_union l)); intros.
    lra.
Qed.    

Definition make_collection_disjoint {T:Type} {σ:SigmaAlgebra T} (coll:nat->event σ) : nat -> event σ
  := fun x => coll x \ (union_of_collection (fun y =>
                                               if lt_dec y x
                                               then coll y
                                               else ∅)).

Lemma make_collection_disjoint_sub {T:Type} {σ:SigmaAlgebra T} (En:nat -> event σ) n : event_sub (make_collection_disjoint En n) (En n).
Proof.
  now intros x [??].
Qed.

Lemma make_collection_disjoint0 {T:Type} {σ:SigmaAlgebra T} (En:nat -> event σ) :
  event_equiv (make_collection_disjoint En 0) (En 0%nat).
Proof.
  unfold make_collection_disjoint.
  red; intros.
  split; intros.
  - destruct H; trivial.
  - split; trivial.
    unfold union_of_collection.
    intros [? HH].
    match_destr_in HH.
    lia.
Qed.

Hint Rewrite @make_collection_disjoint0 : prob.

Lemma make_collection_disjoint_in {T:Type} {σ:SigmaAlgebra T} (coll:nat->event σ) (x:nat) (e:T) :
  proj1_sig (make_collection_disjoint coll x) e <->
  (proj1_sig (coll x) e /\ forall y, (y < x)%nat -> ~ proj1_sig (coll y) e).
Proof.
  split.
  - unfold make_collection_disjoint; intros HH.
    destruct HH as [H1 H2].
    split; trivial.
    intros y ylt cy.
    apply H2.
    exists y.
    destruct (lt_dec y x); intuition.
  - intros [ce fce].
    unfold make_collection_disjoint.
    split; trivial.
    unfold union_of_collection.
    intros [n Hn].
    destruct (lt_dec n x); trivial.
    eapply fce; eauto.
Qed.
  
Lemma make_collection_disjoint_disjoint {T:Type} {σ:SigmaAlgebra T} (coll:nat->event σ) :
  collection_is_pairwise_disjoint (make_collection_disjoint coll).
Proof.
  intros x y xyneq e e1 e2.
  apply make_collection_disjoint_in in e1.
  apply make_collection_disjoint_in in e2.
  destruct e1 as [H11 H12].
  destruct e2 as [H21 H22].
  destruct (not_eq _ _ xyneq) as [xlt|ylt].
  - eapply H22; eauto.
  - eapply H12; eauto.
Qed.

Lemma union_of_make_collection_disjoint {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (coll:nat->event σ) :
  sum_of_probs_equals ps_P  (make_collection_disjoint coll) (ps_P (union_of_collection  (make_collection_disjoint coll))).
Proof.
  intros.
  apply ps_countable_disjoint_union.
  apply make_collection_disjoint_disjoint.
Qed.

Lemma ps_diff_sub {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (A B : event σ) :
  event_sub B A ->
  ps_P (event_diff A B) = ps_P A - ps_P B.
Proof.
  intros.
  generalize (ps_disjoint_union ps (event_diff A B) B); intros.
  cut_to H0.
  - rewrite <- sub_diff_union in H0; trivial.
    lra.
  - firstorder.
Qed.


Require Import Classical ClassicalFacts.

Section classic.
  
  Lemma make_collection_disjoint_union {T:Type} {σ:SigmaAlgebra T} (coll:nat->event σ) :
    union_of_collection coll
                        ===
                        union_of_collection (make_collection_disjoint coll).
  Proof.
    unfold union_of_collection.
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
      destruct (lt_dec nn m); [ | tauto].
      specialize (H0 _ Hnn).
      lia.
    - apply make_collection_disjoint_in in Hn.
      exists n; tauto.
  Qed.

  Lemma ps_diff_le {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) x y :
    ps_P (x \ y) <= ps_P x.
  Proof.
    intros.
    apply ps_sub; auto with prob.
  Qed.
  
  Lemma make_collection_disjoint_le {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ)
        (coll: nat -> event σ) :
    forall n, ps_P (make_collection_disjoint coll n) <= ps_P (coll n).
  Proof.
    intros n.
    unfold make_collection_disjoint.
    apply ps_diff_le; auto 2.
  Qed.
  
  Theorem ps_countable_boole_inequality {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ)
          (coll: nat -> event σ) sum :
    infinite_sum' (fun n => ps_P (coll n)) sum ->
    ps_P (union_of_collection coll) <= sum.
  Proof.
    rewrite make_collection_disjoint_union.
    generalize (union_of_make_collection_disjoint ps coll); intros.
    unfold sum_of_probs_equals in H.
    eapply infinite_sum'_le; eauto.
    intros n; simpl.
    apply make_collection_disjoint_le; trivial.
  Qed.

  Lemma classic_event_none_or_has {A} {σ:SigmaAlgebra A} (p:event σ) : (exists y, proj1_sig p y) \/ event_equiv p event_none.
  Proof.
    destruct (classic (exists y, proj1_sig p y)).
    - eauto.
    - right; intros x.
      destruct p; simpl.
      unfold pre_event_none.
      split; [| tauto].
      intros px.
      apply H.
      eauto.
  Qed.

End classic.

Section take.
  Lemma sum_prob_fold_right {T} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (E : nat -> event σ) n :
        sum_n (fun n0 : nat => ps_P (E n0)) n =
        fold_right Rplus 0 (map ps_P (collection_take E (S n))).
  Proof.
    rewrite sum_n_fold_right_seq.
    f_equal.
    unfold collection_take.
    now rewrite map_map.
  Qed.    
  

End take.

Hint Rewrite @collection_take_Sn @collection_take1 : prob.

Section ascending.
  (* Define properties of ascending collections *)

  Context {T: Type} {σ:SigmaAlgebra T}.
 Definition ascending_collection (En:nat -> event σ) := (forall (n:nat), event_sub (En n) (En (S n))).

 Lemma ascending_collection_le (En:nat -> event σ) :
   ascending_collection En ->
   (forall m n, (m <= n)%nat -> event_sub (En m) (En n)).
 Proof.
   intros asc.
   induction n; simpl.
   - intros.
     replace m with (0%nat) by lia.
     reflexivity.
   - intros.
     apply le_lt_or_eq in H.
     destruct H.
     + red in asc.
       rewrite <- asc.
       apply IHn.
       lia.
     + subst; reflexivity.
 Qed.
 
 Lemma ascending_collection_take_union (En:nat -> event σ)  :
   ascending_collection En ->
   forall n, event_equiv (list_union (collection_take En (S n))) (En n).
 Proof.
   intros.
   induction n; simpl.
   - rewrite collection_take1, list_union_singleton.
     reflexivity.
   - rewrite collection_take_Sn.
     rewrite list_union_app.
     rewrite IHn.
     red in H.
     autorewrite with prob.
     rewrite event_union_sub_r; trivial.
     reflexivity.
 Qed.

 Lemma ascending_make_disjoint_collection_take_union (En:nat -> event σ) :
   ascending_collection En ->
   forall n, event_equiv (list_union (collection_take (make_collection_disjoint En) (S n))) (En n).
 Proof.
   intros asc n.
   induction n; simpl.
   - autorewrite with prob.
     reflexivity.
   - autorewrite with prob.
     autorewrite with prob in IHn.
     rewrite IHn.
     intros a.
     split; intros HH.
     + destruct HH.
       * now apply asc.
       * now apply make_collection_disjoint_sub.
     + red.
       unfold make_collection_disjoint.
       destruct (classic (proj1_sig (union_of_collection (fun y : nat => if lt_dec y (S n) then En y else event_none)) a)).
       * destruct H as [x HH2].
         match_destr_in HH2; [ | red in HH2; tauto].
         left.
         red in asc.
         eapply (ascending_collection_le _ asc x); trivial.
         lia.
       * simpl.
         unfold pre_event_diff, pre_event_union; simpl.
         tauto.
 Qed.

  Lemma is_lim_ascending (ps:ProbSpace σ) (E : nat -> event σ) :
    ascending_collection E ->
    is_lim_seq (fun n => ps_P (E n)) (ps_P (union_of_collection E)).
  Proof.
    intros asc.
    generalize (union_of_make_collection_disjoint ps E); intros HH.
    unfold sum_of_probs_equals in HH.
    rewrite <- make_collection_disjoint_union in HH.
    rewrite <- infinite_sum_infinite_sum' in HH.
    rewrite <- is_series_Reals in HH.
    generalize (ex_series_is_lim_seq  (fun n : nat => ps_P (make_collection_disjoint E n)))
    ; intros HH2.
    cut_to HH2; [| eexists; eauto].
    apply is_lim_seq_ext with (v  := fun n => ps_P (E n)) in HH2.
    - replace (Series (fun n : nat => ps_P (make_collection_disjoint E n)))
        with (ps_P (union_of_collection E)) in HH2; trivial.
      apply is_series_unique in HH.
      auto.
    - intros.
      rewrite sum_prob_fold_right.
      rewrite <- ascending_make_disjoint_collection_take_union by trivial.
      rewrite ps_list_disjoint_union; trivial.
      apply collection_take_preserves_disjoint.
      apply make_collection_disjoint_disjoint.
  Qed.
    
  Lemma lim_ascending (ps:ProbSpace σ) (E : nat -> event σ) :
    ascending_collection E ->
    Lim_seq (fun n => ps_P (E n)) =  (ps_P (union_of_collection E)).
  Proof.
    intros asc.
    apply is_lim_seq_unique.
    now apply is_lim_ascending.
  Qed.

    Lemma event_sub_descending (ps:ProbSpace σ) (E : nat -> event σ) :
    (forall n, event_sub (E (S n)) (E n)) ->
    forall n, event_sub (E n) (E 0%nat).
  Proof.
    induction n.
    intro x.
    tauto.
    now eapply transitivity.
  Qed.

  Lemma is_lim_descending (ps:ProbSpace σ) (E : nat -> event σ) :
    (forall n, event_sub (E (S n)) (E n)) ->
    is_lim_seq (fun n => ps_P (E n)) (ps_P (inter_of_collection E)).
  Proof.
    intros desc.
    generalize (is_lim_ascending ps (fun n => event_diff (E 0%nat) (E n))); intros asc.
    cut_to asc.
    - apply is_lim_seq_ext with (v := (fun n => (ps_P (E 0%nat)) - (ps_P (E n)))) in asc.
      + rewrite union_diff_inter in asc. 
        rewrite ps_diff_sub in asc.
        * generalize (is_lim_seq_const (ps_P (E 0%nat))); intros lim2.

          generalize (is_lim_seq_minus' _ _ _ _ asc lim2)
          ; intros lim3.
          apply is_lim_seq_opp in lim3.
          simpl in lim3.
          replace  (- (ps_P (E 0%nat) - ps_P (inter_of_collection E) - ps_P (E 0%nat)))
            with (ps_P (inter_of_collection E)) in lim3 by lra.
          eapply is_lim_seq_ext; try eapply lim3.
          intros; simpl; lra.
        * intros ? HH.
          apply (HH 0%nat).
      + intros.
        apply ps_diff_sub; trivial.
        now apply event_sub_descending.
    - unfold ascending_collection; intros.
      apply event_diff_sub_proper.
      + reflexivity.
      + apply desc.
  Qed.

  Lemma lim_descending (ps:ProbSpace σ) (E : nat -> event σ) :
    (forall n, event_sub (E (S n)) (E n)) ->
    Lim_seq (fun n => ps_P (E n)) = (ps_P (inter_of_collection E)).
  Proof.
    intros.
    apply is_lim_seq_unique.
    now apply is_lim_descending.
  Qed.

End ascending.

Hint Resolve ps_none ps_one : prob.

  Lemma event_complement_union {T: Type} {σ:SigmaAlgebra T} (E1 E2:event σ) :
    event_equiv (¬ (E1 ∪ E2))
                (¬ E1 ∩ ¬ E2).
  Proof.
    unfold event_complement, event_inter, event_union.
    red; intros.
    split; intros.
    - now apply not_or_and.
    - now apply and_not_or.
  Qed.

  Lemma event_complement_inter {T: Type} {σ:SigmaAlgebra T} (E1 E2:event σ) :
    event_equiv (¬ (E1 ∩ E2))
                (¬ E1 ∪ ¬ E2).
  Proof.
    unfold event_complement, event_inter, event_union.
    red; intros.
    split; intros.
    - now apply not_and_or.
    - now apply or_not_and.
  Qed.

  Lemma event_complement_list_union {T: Type} {σ:SigmaAlgebra T} (l:list (event σ)) :
    event_equiv (event_complement (list_union l)) (list_inter (map event_complement l)).
  Proof.
    induction l; simpl.
    - firstorder.
    - rewrite list_union_cons, event_complement_union, list_inter_cons.
      now rewrite IHl.
  Qed.

  Lemma ps_zero_union {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
    E1 E2 :
    ps_P E1 = 0 ->
    ps_P E2 = 0 ->
    ps_P (E1 ∪ E2) = 0.
  Proof.
    intros p1 p2.
    rewrite ps_union by auto with prob.
    rewrite p1, p2.
    ring_simplify.
    apply Ropp_eq_0_compat.

    assert (HH:event_sub ((event_inter E1 E2)) E1)
      by auto with prob.

    apply (ps_sub prts) in HH
    ; auto with prob.
    rewrite p1 in HH.
    apply Rle_antisym; trivial.
    apply ps_pos.
  Qed.
  
  Lemma ps_one_inter {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
    E1 E2 :
    ps_P (E1)=1 -> ps_P (E2)=1 -> ps_P (E1 ∩ E2)=1.
  Proof.
    intros p1 p2.
    cut (1-ps_P (event_inter E1 E2) = 0); [lra |].
    rewrite <- ps_complement by auto with prob.    
    rewrite event_complement_inter.
    apply ps_zero_union; auto with prob.
    - rewrite ps_complement; auto with prob.
      rewrite p1.
      lra.
    - rewrite ps_complement; auto with prob.
      rewrite p2.
      lra.
  Qed.

  Lemma ps_inter_r1 {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {A B} :
    ps_P B = 1 ->
    ps_P (A ∩ B) = ps_P A.
  Proof.
    intros HH.
    generalize (ps_union prts A B)
    ; intros HH2.
    rewrite HH in HH2.
    assert ( ps_P (A ∪ B) = 1).
    {
      apply Rle_antisym.
      - apply ps_le1.
      - rewrite <- HH.
        apply ps_sub.
        eauto with prob.
    }
    rewrite H in HH2.
    lra.
  Qed.

  Lemma ps_inter_l1 {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {A B} :
    ps_P A = 1 ->
    ps_P (A ∩ B) = ps_P B.
  Proof.
    intros.
    rewrite event_inter_comm.
    now apply ps_inter_r1.
  Qed.

  Lemma ps_union_r0 {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {A B} :
    ps_P B = 0 ->
    ps_P (A ∪ B) = ps_P A.
  Proof.
    intros HH.
    rewrite (ps_union prts A B).
    rewrite HH.
    assert ( ps_P (A ∩ B) = 0).
    {
      rewrite <- HH.
      apply Rle_antisym.
      - apply ps_sub.
        auto with prob.
      - rewrite HH.
        apply ps_pos.
    }
    rewrite H.
    lra.
  Qed.

  Lemma ps_union_l0 {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {A B} :
    ps_P A = 0 ->
    ps_P (A ∪ B) = ps_P B.
  Proof.
    intros.
    rewrite event_union_comm.
    now apply ps_union_r0.
  Qed.

  Lemma ps_union_sub 
        {T : Type} {σ : SigmaAlgebra T} (ps : ProbSpace σ) (A B : event σ) :
    ps_P A <= ps_P (A ∪ B).
  Proof.
    apply ps_sub.
    auto with prob.
  Qed.

  Lemma ps_zero_countable_union {T:Type} 
        {dom:SigmaAlgebra T} (prts:ProbSpace dom)
        (coll: nat -> event dom) :
    (forall (n:nat), ps_P (coll n) = 0) ->
    ps_P (union_of_collection coll) = 0.
  Proof.
    generalize (ps_countable_boole_inequality prts coll); intros.
    specialize (H 0).
    apply Rle_antisym.
    - apply H.
      apply infinite_sum'_ext with (s1 := fun _ => 0).
      + intros; symmetry; apply H0.
      + apply infinite_sum'0.
    - apply ps_pos.
 Qed.

  Lemma ps_union_countable_union_iff {T:Type} {dom : SigmaAlgebra T}
        (prts: ProbSpace dom) (coll : nat -> event dom):
  (forall n, ps_P (coll n) = 0) <-> (ps_P (union_of_collection coll) = 0).
  Proof.
    split; intros H.
    + now apply ps_zero_countable_union.
    + intros n.
      assert (H1 : 0 <= ps_P (coll n)) by (apply ps_pos).
      assert (H2 : ps_P (coll n) <= ps_P (union_of_collection coll)).
      {
        apply ps_sub.
        apply union_of_collection_sup.
      }
      rewrite H in H2.
      lra.
  Qed.

  Lemma ps_one_countable_inter {T:Type} 
        {dom:SigmaAlgebra T} (prts:ProbSpace dom)
        (coll: nat -> event dom) :
    (forall (n:nat), ps_P (coll n) = 1) ->
    ps_P (inter_of_collection coll) = 1.
  Proof.
    intros.
    assert (event_equiv (inter_of_collection coll)
                        (event_complement 
                           (union_of_collection 
                              (fun n => event_complement (coll n))))).
    {
      intro x.
      simpl.
      intuition firstorder.
      specialize (H0 n).
      tauto.
    }      
    rewrite H0.
    rewrite ps_complement, ps_zero_countable_union; try lra.
    intros.
    rewrite ps_complement, H.
    lra.
  Qed.

  Lemma double_countable_inter_ps_one {T:Type} 
        {dom:SigmaAlgebra T} (prts:ProbSpace dom)
        (f : nat -> nat -> T -> Prop) :
    (forall (n m : nat), 
        exists (P : event dom),
          ps_P P = 1 /\ forall (x : T), P x -> f n m x) ->
    exists (P : event dom),
      ps_P P = 1 /\ forall (n m : nat), forall (x : T), P x -> f n m x.
  Proof.
    intros.

    assert (HH: forall (nm:nat),
               exists P : event dom, ps_P P = 1 /\ (forall x : T, P x -> (let '(n,m) := iso_b nm in f n m x))).
    {
      intros.
      specialize (H (fst (iso_b nm)) (snd (iso_b nm))).
      match_destr.
    } 

    destruct (choice _ HH) as [coll collp].
    exists (inter_of_collection coll).
    split.
    - apply ps_one_countable_inter.
      intros n.
      now destruct (collp n).
    - intros n m x ic.
      destruct (collp (iso_f (n,m))) as [_ HH2].
      match_case_in HH2.
      intros ?? eqq1.
      rewrite eqq1 in HH2.
      rewrite iso_b_f in eqq1.
      invcs eqq1.
      apply HH2.
      apply ic.
  Qed.

Section conditional_probability.

  Context {T: Type} {σ:SigmaAlgebra T} (Ψ: ProbSpace σ).

  Definition cond_prob
               (A B : event σ) 
    := ps_P (A ∩ B)/ps_P(B).

  Lemma infinite_sum'_scal_r {f1 : nat -> R} {sum1 : R} (c : R) :
    infinite_sum' f1 sum1 ->
    infinite_sum' (fun x : nat => f1 x * c) (sum1 * c).
  Proof.
    intros.
    rewrite Rmult_comm.
    erewrite infinite_sum'_ext
    ; [| intros; rewrite Rmult_comm; reflexivity].
    now apply infinite_sum'_mult_const.
  Qed.

  Lemma infinite_sum'_scal_div {f1 : nat -> R} {sum1 : R} (c : R) :
    infinite_sum' f1 sum1 ->
    infinite_sum' (fun x : nat => f1 x / c) (sum1 / c).
  Proof.
    apply infinite_sum'_scal_r.
  Qed.

  Global Program Instance cond_prob_space (B:event σ) (pf:0 < ps_P B) : ProbSpace σ
    := {
    ps_P A := cond_prob A B
      }.
  Next Obligation.
    intros ?? eqq.
    unfold cond_prob.
    now rewrite eqq.
  Qed.
  Next Obligation.
    unfold cond_prob.
    red.
    apply infinite_sum'_scal_div.
    rewrite event_inter_countable_union_distr_r.
    apply ps_countable_disjoint_union.
    apply collection_is_pairwise_disjoint_sub with (f:=fun e => e ∩ B); trivial.
    intros.
    eauto with prob.
  Qed.
  Next Obligation.
    unfold cond_prob.
    autorewrite with prob.
    field_simplify; lra.
  Qed.
  Next Obligation.
    unfold cond_prob.
    apply Rmult_le_pos.
    - apply ps_pos.
    - left.
      now apply Rinv_0_lt_compat.
  Qed.

  Definition event_restricted_domain (e:event σ) : Type
    := { x : T | e x }.

  Lemma event_restricted_domain_ext (e1 e2:event σ) :
    proj1_sig e1 = proj1_sig e2 -> e1 = e2.
  Proof.
    intros.
    destruct e1; destruct e2; simpl in *.
    now apply subset_eq_compat.
  Qed.
  
  Global Program Instance event_restricted_sigma (e:event σ) : SigmaAlgebra (event_restricted_domain e)
    := {
    sa_sigma (A:pre_event (event_restricted_domain e)) 
    := sa_sigma _ (fun a:T => exists (a':event_restricted_domain e), proj1_sig a' = a /\ A (a'))
      }.
  Next Obligation.
    apply sa_countable_union in H.
    eapply sa_proper; try eapply H.
    intros x.
    split.
    - intros [?[?[n ?]]]; subst.
      exists n; simpl.
      eauto.
    - intros [n [? [? HH]]]; subst.
      exists x0.
      split; trivial.
      red; eauto.
  Qed.
  Next Obligation.
    apply sa_complement in H.
    generalize (sa_inter H (proj2_sig e)); clear H.
    eapply sa_proper.
    intros x.
    split.
    - intros [[??][??]]; subst.
      unfold pre_event_complement, pre_event_inter; simpl in *.
      split; trivial.
      intros [[??][??]]; simpl in *.
      apply H0.
      eapply subset_eq_compat in H.
      rewrite <- H.
      eapply H1.
    - intros HH.
      red in HH.
      unfold pre_event_complement in HH.
      destruct HH as [HH1 HH2].
      exists (exist _ _ HH2).
      simpl.
      split; trivial.
      intros HH3; simpl in *.
      apply HH1.
      eexists; split; try apply HH3.
      reflexivity.
  Qed.
  Next Obligation.
    eapply sa_proper; try eapply (proj2_sig e).
    unfold pre_Ω; simpl.
    intros x; simpl.
    split.
    - intros [[??][??]]; simpl; subst.
      simpl.
      apply e0.
    - intros.
      exists (exist _ _ H); simpl.
      tauto.
  Qed.

  Definition pre_event_restricted_pre_event_lift  (e:event σ) (A:pre_event (event_restricted_domain e)) : pre_event T
    := (fun a:T => exists (a':event_restricted_domain e), proj1_sig a' = a /\ A (a')).

  Lemma sa_pre_event_restricted_event_lift  (e:event σ) (A:event (event_restricted_sigma e)) 
    : sa_sigma _ (fun a:T => exists (a':event_restricted_domain e), proj1_sig a' = a /\ A (a')).
  Proof.
    apply (proj2_sig A).
  Qed.

  Definition event_restricted_event_lift  (e:event σ) (A:event(event_restricted_sigma e)) :
    event σ
    := exist _ _ (sa_pre_event_restricted_event_lift e A).

  Definition event_restricted_pre_event (e f:event σ) : pre_event (event_restricted_domain e)
    := fun (a':event_restricted_domain e) => f (proj1_sig a').

  Lemma sa_pre_event_restricted_event (e f :event σ) : 
    sa_sigma _ (event_restricted_pre_event e f).
  Proof.
    unfold sa_sigma; simpl.
    apply sa_proper with (x := event_inter e f).
    {
      split; intros.
      - unfold event_inter, pre_event_inter in H.
        destruct H.
        exists (exist _ _ H).
        now simpl.
      - destruct H as [? [? ?]].
        unfold event_restricted_pre_event in H0.
        unfold event_restricted_domain in x0.
        unfold event_inter, pre_event_inter.
        simpl.
        rewrite <- H.
        split; trivial.
        apply (proj2_sig x0).
    }
    apply sa_inter.
    apply (proj2_sig e).
    apply (proj2_sig f).
  Qed.

  Definition event_restricted_event (e f:event σ) : event(event_restricted_sigma e)
    := exist _ _ (sa_pre_event_restricted_event e f).

  Definition event_restricted_function {Td:Type} (e:event σ) (f : T -> Td) : 
    (event_restricted_domain e) -> Td 
    := fun a' => f (proj1_sig a').

  Instance event_restricted_event_lift_proper e : Proper (event_equiv ==> event_equiv) (event_restricted_event_lift e).
  Proof.
    intros ?? eqq x.
    unfold event_restricted_event_lift, pre_event_restricted_pre_event_lift.
    simpl.
    destruct x0; destruct y.
    red in eqq.
    simpl in *.
    red in eqq.
    firstorder.
  Qed.

  Lemma event_restricted_event_lift_disjoint e collection :
    collection_is_pairwise_disjoint collection ->  
    collection_is_pairwise_disjoint (fun n : nat => event_restricted_event_lift e (collection n)).
  Proof.
    unfold event_restricted_event_lift, pre_event_restricted_pre_event_lift.
    intros disj n1 n2 neq x [[x1 ?] [??]] [[x2 ?] [??]]; simpl in *.
    eapply disj; try eapply neq; subst x.
    - eapply H0.
    - eapply subset_eq_compat in H1.
      rewrite <- H1.
      eauto.
  Qed.

  Lemma event_restricted_event_lift_collection e collection :
    event_equiv (event_restricted_event_lift e (union_of_collection collection))
                (union_of_collection (fun n : nat => event_restricted_event_lift e (collection n))).
  Proof.
    unfold event_restricted_event_lift, pre_event_restricted_pre_event_lift.
    unfold union_of_collection, pre_union_of_collection.
    intros x; simpl.
    split.
    - intros [[??][?[n ?]]]; simpl in *; subst.
      exists n.
      exists ((exist (fun x : T => e x) x e0)); simpl; eauto.
    - intros [n [[a' ?] [??]]]; simpl in *.
      subst.
      exists (exist (fun x : T => e x) x e0); simpl.
      eauto.
  Qed.

  Lemma event_restricted_event_lift_Ω e :
    event_equiv (event_restricted_event_lift e Ω) e.
  Proof.
    intros x.
    split.
    - intros [[??][??]]; simpl in *; subst; trivial.
    - intros.
      unfold event_restricted_event_lift; simpl.
      exists (exist _ _ H); simpl.
      unfold pre_Ω.
      tauto.
  Qed.

  Global Program Instance event_restricted_prob_space (e:event σ) (pf:0 < ps_P e) :
    ProbSpace (event_restricted_sigma e)
    := {
    ps_P A := cond_prob (event_restricted_event_lift e A) e
      }.
  Next Obligation.
    intros ?? eqq.
    unfold cond_prob.
    
    now rewrite eqq.
  Qed.
  Next Obligation.
    unfold cond_prob.
    red.
    apply infinite_sum'_scal_div.
    generalize (ps_countable_disjoint_union
                  (fun x : nat => event_restricted_event_lift e (collection x) ∩ e))
    ; intros HH.
    unfold sum_of_probs_equals in HH.

    assert (eqq: event_equiv
              (event_restricted_event_lift e (union_of_collection collection) ∩ e)
              (union_of_collection (fun x : nat => event_restricted_event_lift e (collection x) ∩ e))).
    - rewrite <- event_inter_countable_union_distr_r.
      rewrite event_restricted_event_lift_collection.
      reflexivity.
    - rewrite eqq.
      apply HH.
      apply collection_is_pairwise_disjoint_sub with (f:=fun x => x ∩ e); trivial.
      + intros.
        eauto with prob.
      + now apply event_restricted_event_lift_disjoint.
  Qed.
  Next Obligation.
    unfold cond_prob.
    rewrite event_restricted_event_lift_Ω.
    rewrite event_inter_self.
    apply Rinv_r.
    lra.
  Qed.
  Next Obligation.
    unfold cond_prob.
    apply Rmult_le_pos.
    - apply ps_pos.
    - left.
      now apply Rinv_0_lt_compat.
  Qed.

End conditional_probability.

Section sa_sub.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).
  
  Instance prob_space_sa_sub : ProbSpace dom2.
  Proof.
    exists (fun x => ps_P (event_sa_sub sub x)).
    - repeat red; intros.
      now rewrite H.
    - intros.
      generalize (ps_countable_disjoint_union (fun n => event_sa_sub sub (collection n)))
      ; intros HH.
      cut_to HH.
      + rewrite union_of_collection_sa_sub.
        unfold sum_of_probs_equals in *.
        apply HH.
      + now apply collection_is_pairwise_disjoint_sa_sub.
    - erewrite ps_proper; try eapply ps_one.
      unfold Ω, pre_Ω.
      repeat red; intros; simpl; tauto.
    - intros.
      apply ps_pos.
  Defined.

End sa_sub.

Section indep.
  Local Open Scope R.
  Local Open Scope prob.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom).

  Definition independent_events (A B : event dom)
    := ps_P (A ∩ B) = ps_P A * ps_P B.

  Definition independent_event_collection {Idx} (A:Idx->event dom)
    := forall (l:list Idx),
      NoDup l ->
      ps_P (list_inter (map A l)) =
        fold_right Rmult 1 (map ps_P (map A l)).
  
  Definition pairwise_independent_event_collection {Idx} (A:Idx->event dom)
    := forall i j, i <> j ->
              independent_events (A i) (A j).

  Lemma independent_event_collection_pairwise_independent {Idx} (A:Idx -> event dom) :
    independent_event_collection A -> pairwise_independent_event_collection A.
  Proof.
    intros ind i j ijne.
    specialize (ind [i; j]).
    cut_to ind.
    - simpl in ind.
      autorewrite with prob in ind.
      now rewrite Rmult_1_r in ind.
    - repeat constructor; simpl; intuition.
  Qed.

  Notation "a ⟂ b" := (independent_events a b) (at level 50) : prob. (* \perp *)

  Global Instance independent_events_symm : Symmetric independent_events.
  Proof.
    unfold independent_events; intros ???.
    rewrite event_inter_comm.
    lra.
  Qed.

  Global Instance independent_events_proper : Proper (event_equiv ==> event_equiv ==> iff) independent_events.
  Proof.
    intros ??????.
    unfold independent_events.
    rewrite H, H0.
    reflexivity.
  Qed.

  Global Instance independent_event_collection_proper {Idx} :
    Proper (pointwise_relation _ event_equiv ==> iff) (@independent_event_collection Idx).
  Proof.
    intros ???.
    unfold independent_event_collection.
    split; intros HH l nd; specialize (HH l nd)
    ; (etransitivity; [etransitivity |]; [| apply HH |])
    ; clear HH nd.
    - apply ps_proper.
      induction l; simpl; try reflexivity.
      repeat rewrite list_inter_cons.
      now rewrite IHl, (H a).
    - f_equal; repeat rewrite map_map; apply map_ext; intros.
      now rewrite (H a).
    - apply ps_proper.
      induction l; simpl; try reflexivity.
      repeat rewrite list_inter_cons.
      now rewrite IHl, (H a).
    - f_equal; repeat rewrite map_map; apply map_ext; intros.
      now rewrite (H a).
  Qed.

  Global Instance pairwise_independent_event_collection_proper {Idx} :
    Proper (pointwise_relation _ event_equiv ==> iff) (@pairwise_independent_event_collection Idx).
  Proof.
    intros ???.
    unfold pairwise_independent_event_collection.
    split; intros HH i j neq; specialize (HH i j neq).
    - now rewrite <- H.
    - now rewrite H.
  Qed.
  
  Lemma independent_events_complement_r (A B : event dom) :
    A ⟂ B -> A ⟂ ¬ B.
  Proof.
    unfold independent_events; intros.
    assert (eqq1:A === (A ∩ B) ∪ (A ∩ ¬ B)).
    {
      intros ?; simpl.
      split; [| firstorder].
      intros.
      destruct (classic (proj1_sig B x)); firstorder.
    }
    generalize (ps_proper _ _ eqq1); intros eqq2.
    rewrite ps_disjoint_union in eqq2 by firstorder.
    assert (eqq3:ps_P (A ∩ ¬ B) = ps_P A - ps_P (A ∩ B)) by lra.
    rewrite eqq3, H.
    rewrite ps_complement.
    lra.
  Qed.

  Lemma independent_events_complement_l (A B : event dom) :
    A ⟂ B -> ¬ A ⟂ B.
  Proof.
    intros.
    apply independent_events_symm.
    apply independent_events_complement_r.
    now apply independent_events_symm.
  Qed.    

  Lemma independent_events_complement_lr (A B : event dom) :
    A ⟂ B -> ¬ A ⟂ ¬ B.
  Proof.
    intros.
    apply independent_events_complement_l.
    now apply independent_events_complement_r.
  Qed.

  Lemma independent_events_all_r (A : event dom) : A ⟂ Ω.
  Proof.
    red.
    now rewrite ps_all, event_inter_true_r, Rmult_1_r.
  Qed.

  Lemma independent_events_all_l (A : event dom) : Ω ⟂ A.
  Proof.
    red.
    now rewrite ps_all, event_inter_true_l, Rmult_1_l.
  Qed.

  Lemma independent_events_none_r (A : event dom) : A ⟂ ∅.
  Proof.
    red.
    now rewrite event_inter_false_r, ps_none, Rmult_0_r.
  Qed.

  Lemma independent_events_none_l (A : event dom) : ∅ ⟂ A.
  Proof.
    red.
    now rewrite event_inter_false_l, ps_none, Rmult_0_l.
  Qed.

  Lemma independent_events_self (A : event dom) :
    A ⟂ A ->
    ps_P A = 0 \/ ps_P A = 1.
  Proof.
    unfold independent_events.
    rewrite event_inter_self.
    intros.
    destruct (Req_EM_T (ps_P A) 0); try tauto.
    apply (f_equal (fun x => x * / ps_P A)) in H.
    rewrite Rmult_assoc in H.
    repeat rewrite Rinv_r in H by trivial.
    lra.
  Qed.

  Lemma independent_events_disjoint_countable_union (e : nat -> event dom) (B : event dom)
        (indeps: forall x : nat, independent_events (e x) B)
        (disj : collection_is_pairwise_disjoint e) :
    independent_events (union_of_collection e) B.
  Proof.
    unfold independent_events in *.
    rewrite Event.event_inter_countable_union_distr_r.
    generalize (ps_countable_disjoint_union (fun n : nat => e n) disj)
    ; intros HH.
    red in HH.
    generalize (infinite_sum'_scal_r (ps_P B) HH); intros HH2.
    assert (disj' : collection_is_pairwise_disjoint (fun n : nat => e n ∩ B)).
    {
      apply -> collection_is_pairwise_disjoint_pre in disj.
      apply <- collection_is_pairwise_disjoint_pre.
      unfold collection_pre in *.
      generalize (pre_collection_is_pairwise_disjoint_inter e B disj).
      apply pre_collection_is_pairwise_disjoint_pre_event_equiv_proper; intros ?.
      now rewrite pre_event_inter_comm.
    }       
    generalize (ps_countable_disjoint_union (fun n : nat => e n ∩ B) disj')
    ; intros HH3.
    red in HH3.
    assert (HH4:infinite_sum'
              (fun n : nat => ps_P (e n) * ps_P B)
              (ps_P (union_of_collection (fun n : nat => e n ∩ B)))).
    {
      revert HH3.
      now apply infinite_sum'_ext.
    }
    generalize (infinite_sum'_unique HH2 HH4).
    auto.
  Qed.

End indep.

Section iso.

  Program Instance iso_ps {A B: Type}
          {σ:SigmaAlgebra A}
          (prts:ProbSpace σ)
          (iso:Isomorphism A B) :
    ProbSpace (iso_sa σ)
    := {|
      ps_P e := ps_P (iso_event_b e)
    |}.
  Next Obligation.
    intros ???.
    apply ps_proper.
    now apply iso_event_b_proper.
  Qed.
  Next Obligation.
    rewrite iso_event_b_union.
    apply ps_countable_disjoint_union.
    now apply iso_event_b_disjoint.
  Qed.
  Next Obligation.
    rewrite <- ps_one.
    apply ps_proper.
    firstorder.
  Qed.
  Next Obligation.
    apply ps_pos.
  Qed.

End iso.

Lemma ProbSpace_Ω_nempty {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) : ~ event_equiv Ω ∅.
Proof.
  intros HH.
  generalize ps_one.
  rewrite HH.
  rewrite ps_none.
  lra.
Qed.

Lemma ProbSpace_inhabited {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) : inhabited T.
Proof.
  destruct (classic_event_none_or_has Ω).
  - destruct H; eauto.
  - apply ProbSpace_Ω_nempty in H; tauto.
Qed.
