Require Import Program.Basics.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.

Require Import Classical ClassicalFacts.
Require Ensembles.

Require Import Utils DVector.
Import ListNotations.
Require Export Event SigmaAlgebras ProbSpace.
Require Import ClassicalDescription.
Require Import Coquelicot.Coquelicot.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

Section discrete.

  Record prob_mass_fun {A:Type} (σ:SigmaAlgebra A) : Type
    := {
    (* a countable set of points *)
    pmf_points : nat -> option A
    (* we require that the points be distinct *)
    ; pmf_points_inj n1 n2 a :
        pmf_points n1 = Some a ->
        pmf_points n2 = Some a ->
        n1 = n2
    ; pmf_sa (e:event σ) :
        pre_event_sub e
                      (pre_union_of_collection (fun n => match pmf_points n with
                                                      | Some a => pre_event_singleton a
                                                      | None => pre_event_none
                                                      end))
        \/ pre_event_sub (pre_event_complement e)
                        (pre_union_of_collection (fun n => match pmf_points n with
                                                        | Some a => pre_event_singleton a
                                                        | None => pre_event_none
                                                        end))

    ; pmf_pmf : nat -> R
    ; pmf_valid (n:nat) : pmf_points n = None -> pmf_pmf n = 0
    ; pmf_points_sa (n:nat) (x:A) : pmf_points n = Some x -> sa_sigma (pre_event_singleton x)
    ; pmf_pmf_pos n : 0 <= pmf_pmf n
    ; pmf_pmf_one : infinite_sum' pmf_pmf 1
                                  
      }.

  Global Arguments pmf_points {A} {σ}.
  Global Arguments pmf_points_inj {A} {σ}.
  Global Arguments pmf_sa {A} {σ}.
  Global Arguments pmf_pmf {A} {σ}.
  Global Arguments pmf_valid {A} {σ}.
  Global Arguments pmf_points_sa {A} {σ}.
  Global Arguments pmf_pmf_pos {A} {σ}.
  Global Arguments pmf_pmf_one {A} {σ}.

  (* TODO: move *)
  Lemma is_countable_singleton {A:Type} {σ:SigmaAlgebra A} x pf :
    is_countable (event_singleton x pf).
  Proof.
    red.
    exists (fun n => match n with
             | 0 => fun x' => x = x'
             | _ => pre_event_none
             end
      ).
    split.
    - intros ??? s1 s2.
      match_destr_in s1; [congruence|].
      red in s1; tauto.
    - intros ?.
      simpl.
      unfold pre_event_singleton.
      split.
      + intros; subst.
        exists 0%nat; trivial.
      + intros [? s1].
        match_destr_in s1.
        * eauto.
        * red in s1; tauto.
  Qed.

  Section pmf_descr.

    Context {A:Type} {σ:SigmaAlgebra A} (PMF:prob_mass_fun σ).

    Definition pmf_singleton {n:nat} {x:A} (pf:PMF.(pmf_points) n = Some x) : event σ
      := event_singleton x (PMF.(pmf_points_sa) _ _ pf).


    Lemma pmf_singleton_countable {n:nat} {x:A} (pf:PMF.(pmf_points) n = Some x) :
      is_countable (pmf_singleton pf).
    Proof.
      unfold pmf_singleton.
      apply is_countable_singleton.
    Qed.

    Lemma pmf_sigma_countable (x:event σ) :
      is_countable x \/ is_countable (event_complement x).
    Proof.
      destruct (PMF.(pmf_sa) x).
      - left.
        red.
        exists (fun n a => PMF.(pmf_points) n = Some a /\ x a).
        split.
        + intros ??? [??] [??].
          congruence.
        + intros ?.
          split.
          * intros xx.
            specialize (H _ xx).
            destruct H.
            match_option_in H.
            -- red in H; subst.
               eauto.
            -- red in H; tauto.
          * now intros [? [??]].
      - right.
        red.
        exists (fun n a => (PMF.(pmf_points) n = Some a /\ ~ x a)).
        split.
        + intros ??? [??] [??].
          congruence.
        + intros ?.
          split.
          * intros xx.
            specialize (H _ xx).
            destruct H.
            match_option_in H.
            -- red in H; subst.
               eauto.
            -- red in H; tauto.
          * now intros [? [??]].
    Qed.

    Definition series_of_pmf_points (x:event σ) : nat -> R
      := fun n => match PMF.(pmf_points) n with
               | Some a => if excluded_middle_informative (x a)
                          then PMF.(pmf_pmf) n
                          else 0
               | None => 0
               end.
    Instance series_of_pmf_points_proper : Proper (event_equiv ==> eq ==> eq) series_of_pmf_points.
    Proof.
      intros ?? eqq ???; subst.
      unfold series_of_pmf_points; simpl.
      match_destr.
      destruct (eqq a).
      repeat match_destr; tauto.
    Qed.

    (* TODO: Move these *)
    Lemma infinite_sum'_pos_prefix_le f l n:
      infinite_sum' f l ->
      (forall n, 0 <= f n) ->
      sum_f_R0' f n <= l.
    Proof.
      intros.
      apply (infinite_sum'_split n f l) in H.
      apply infinite_sum'_pos in H.
      - lra.
      - auto.
    Qed.

    Lemma infinite_sum'_pos_one_le f l n:
      infinite_sum' f l ->
      (forall n, 0 <= f n) ->
      f n <= l.
    Proof.
      intros.
      apply (infinite_sum'_pos_prefix_le _ _ (S n)) in H; trivial.
      simpl in H.
      generalize (sum_f_R0'_le f n H0).
      lra.
    Qed.

    Lemma pmf_pmf_le1 n : (PMF.(pmf_pmf) n <= 1).
    Proof.
      generalize (PMF.(pmf_pmf_one)); intros HH.
      apply (infinite_sum'_pos_one_le _ _ n) in HH; trivial.
      intros.
      apply pmf_pmf_pos.
    Qed.

    Lemma series_of_pmf_points_pos (x:event σ) (n:nat) :
      0 <= series_of_pmf_points x n.
    Proof.
      unfold series_of_pmf_points.
      match_case; intros; [| lra].
      match_destr; [| lra].
      apply pmf_pmf_pos.
    Qed.

    Lemma sum_series_of_pmf_points_partial_incr (x:event σ) (n:nat) :
      sum_f_R0 (series_of_pmf_points x) n <= sum_f_R0 (series_of_pmf_points x) (S n).
    Proof.
      intros.
      simpl.
      generalize (series_of_pmf_points_pos x (S n)).
      lra.
    Qed.

    Lemma sum_pmf_pmf_partial_incr (n:nat) :
          sum_f_R0 (PMF.(pmf_pmf)) n <= sum_f_R0 (PMF.(pmf_pmf)) (S n).
    Proof.
      intros.
      simpl.
      generalize (PMF.(pmf_pmf_pos) (S n)).
      lra.
    Qed.

    Lemma sum_series_of_pmf_points_le1 x (n : nat) : sum_f_R0 (series_of_pmf_points x) n <= 1.
    Proof.
      intros.
      generalize (PMF.(pmf_pmf_one)); intros HH.
      eapply Rle_trans.
      - apply (PartSum.sum_growing _ (PMF.(pmf_pmf))); intros.
        unfold series_of_pmf_points.
        match_case; intros.
        + match_destr; [lra |].
          apply pmf_pmf_pos.
        + apply pmf_pmf_pos.
      - rewrite sum_f_R0_sum_f_R0'.
        eapply infinite_sum'_pos_prefix_le; trivial.
        apply pmf_pmf_pos.
    Qed.

     Lemma ex_sum_series_of_pmf_points (x:event σ) :
      {r | infinite_sum' (series_of_pmf_points x) r}.
    Proof.
      exists (Lim_seq (fun i : nat => sum_f_R0 (series_of_pmf_points x) i)).
      rewrite <- infinite_sum_infinite_sum'.
      rewrite <- infinite_sum_is_lim_seq.
      apply Lim_seq_correct'.
      apply (ex_finite_lim_seq_incr _ 1).
      - apply sum_series_of_pmf_points_partial_incr. 
      - apply sum_series_of_pmf_points_le1.
    Qed.

    Definition sum_pmf_points (x:event σ)
      := proj1_sig (ex_sum_series_of_pmf_points x).

    Instance sum_pmf_points_proper : Proper (event_equiv ==> eq) sum_pmf_points.
    Proof.
      intros ?? eqq.
      unfold sum_pmf_points, proj1_sig.
      repeat match_destr.
      eapply infinite_sum'_ext in i.
      - eapply infinite_sum'_unique; eauto.
      - intros.
        apply series_of_pmf_points_proper; trivial.
        now symmetry.
    Qed.

    Lemma series_of_pmf_points_all : rv_eq (series_of_pmf_points Ω) PMF.(pmf_pmf).
    Proof.
      intros ?.
      unfold series_of_pmf_points.
      match_option.
      - match_destr.
        unfold Ω, pre_Ω in n; simpl in n; tauto.
      - apply pmf_valid in eqq; auto.
    Qed.

    Lemma series_of_pmf_points_none : rv_eq (series_of_pmf_points ∅) (const 0).
    Proof.
      intros ?.
      unfold series_of_pmf_points.
      match_option.
      match_destr.
      unfold event_none, pre_event_none in e; simpl in e; tauto.
    Qed.

    Lemma sum_pmf_points_all : sum_pmf_points Ω = 1.
    Proof.
      unfold sum_pmf_points, proj1_sig.
      match_destr.
      generalize (pmf_pmf_one PMF); intros.
      eapply infinite_sum'_unique; try eapply i.
      erewrite infinite_sum'_ext; try eapply H.
      apply series_of_pmf_points_all.
    Qed.

    Lemma sum_pmf_points_none : sum_pmf_points ∅ = 0.
    Proof.
      unfold sum_pmf_points, proj1_sig.
      match_destr.
      rewrite (infinite_sum'_ext _ (const 0)) in i; try eapply H.
      - now apply infinite_sum'_const0 in i.
      - apply series_of_pmf_points_none.
    Qed.

    Lemma sum_pmf_points_pos x : 0 <= sum_pmf_points x.
    Proof.
      unfold sum_pmf_points, proj1_sig.
      match_destr.
      eapply infinite_sum'_pos; eauto.
      apply series_of_pmf_points_pos.
    Qed.

    Lemma sum_pmf_points_le1 x : sum_pmf_points x <= 1.
    Proof.
      unfold sum_pmf_points, proj1_sig.
      match_destr.
      eapply infinite_sum'_le; eauto.
      - apply PMF.(pmf_pmf_one).
      - intros.
        unfold series_of_pmf_points.
        match_destr; try apply pmf_pmf_pos.
        match_destr; try apply pmf_pmf_pos.
        now right.
    Qed.

    Definition ps_of_pmf (x:event σ) : R
      := if (excluded_middle_informative (is_countable x))
         then sum_pmf_points x
         else 1 - sum_pmf_points (¬ x).

    Lemma ps_of_pmf_singleton n (x:A) (pf:PMF.(pmf_points) n = Some x) :
      ps_of_pmf (pmf_singleton pf) = PMF.(pmf_pmf) n.
    Proof.
      unfold ps_of_pmf.
      match_destr.
      - unfold sum_pmf_points, proj1_sig.
        match_destr.
        eapply (infinite_sum'_one _ n) in i0.
        + unfold series_of_pmf_points in i0.
          subst.
          clear i.
          generalize pf; intros.
          rewrite pf.
          match_destr.
          elim n0.
          reflexivity.
        + intros.
          clear H.
          unfold series_of_pmf_points.
          match_option.
          match_destr.
          vm_compute in e.
          subst.
          elim H0.
          apply (PMF.(pmf_points_inj) n' n x); trivial.
      - elim n0.
        apply pmf_singleton_countable.
    Qed.
    
    Program Instance discrete_ProbSpace : ProbSpace σ
      := {|
      ps_P := ps_of_pmf
        |}.
    Next Obligation.
      unfold ps_of_pmf.
      intros ?? eqq.
      repeat match_destr 
      ; try solve [now rewrite eqq
                  | apply (is_countable_proper _ _ eqq) in i; tauto].
    Qed.      
    Next Obligation.
      unfold sum_of_probs_equals.
      unfold ps_of_pmf.
      match_destr.
      - assert (inf:infinite_sum' (fun n => sum_pmf_points (collection n))
                              (sum_pmf_points (union_of_collection collection))).
        {
          unfold sum_pmf_points, proj1_sig.
          match_destr.

          
          
          rewrite <- infinite_sum_infinite_sum'.
          rewrite <- infinite_sum_is_lim_seq.


          
          
          unfold series_of_pmf_points in i0.
          simpl in i0.
          admit.
        }
        eapply infinite_sum'_ext; try eapply inf.
        intros.
        match_destr.
        elim n.
        admit.
      - admit.
                       

        
      
      
      
      unfold ps_of_pmf, proj1_sig.
      match_destr.
      - admit.
      - 

      
    Admitted.
    Next Obligation.
      unfold ps_of_pmf, proj1_sig.
      match_destr.
      - apply sum_pmf_points_all.
      - autorewrite with prob.
        rewrite sum_pmf_points_none.
        lra.
    Qed.
    Next Obligation.
      unfold ps_of_pmf.
      match_destr.
      - apply sum_pmf_points_pos.
      - generalize (sum_pmf_points_le1 (¬ A0)); lra.
    Qed.
          
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


  
