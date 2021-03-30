Require Import Program.Basics.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.
Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import FinFun Finite.
Require Import Morphisms EquivDec.
Require Import Equivalence.
Require Import Classical ClassicalFacts.
Require Ensembles.

Require Import Utils DVector.
Import ListNotations.
Require Export Event SigmaAlgebras ProbSpace.
Require Import Coquelicot.Coquelicot.
Require Import ClassicalDescription.


Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

Section discrete.

  Class Countable (A:Type) :=
    { countable_index  : A -> nat
      ; countable_index_inj : Injective countable_index
    }.

  Definition countable_inv {A:Type} {countableA:Countable A} (n:nat) : option A.
  Proof.
    destruct (excluded_middle_informative (exists s, countable_index s = n)).
    - refine (Some (proj1_sig (constructive_definite_description (fun z:A => countable_index z = n) _))).
      destruct e as [a ca].
      exists a.
      split; trivial.
      intros.
      apply countable_index_inj; congruence.
    - exact None.
  Defined.

  Lemma countable_inv_sound {A:Type} {countableA:Countable A} (n:nat) (a:A) :
    countable_inv n = Some a -> countable_index a = n.
  Proof.
    unfold countable_inv; intros HH.
    match_destr_in HH.
    invcs HH.
    unfold proj1_sig.
    match_destr.
  Qed.

  (* completeness *)
  Lemma countable_inv_index {A:Type} {countableA:Countable A} (a:A) :
    countable_inv (countable_index a) = Some a.
  Proof.
    unfold countable_inv.
    match_destr.
    - unfold proj1_sig.
      match_destr.
      apply countable_index_inj in e0.
      congruence.
    - elim n; eauto.
  Qed.
    
  Definition countable_sum {A:Type} {countableA:Countable A}
             (f:A->R) (l:R)
    := infinite_sum' (fun n =>
                        match countable_inv n with
                        | Some a => f a
                        | None => 0
                        end
                     ) l.

  Record prob_mass_fun (A:Type) {countableA:Countable A}  : Type
    := {
    pmf_pmf : A -> R
    ; pmf_pmf_pos n : 0 <= pmf_pmf n
    ; pmf_pmf_one : countable_sum pmf_pmf 1
      }.

  Global Arguments pmf_pmf {A} {countableA}.
  Global Arguments pmf_pmf_pos {A} {countableA}.
  Global Arguments pmf_pmf_one {A} {countableA}.

  Section pmf_descr.

    Context {A:Type} {countableA:Countable A} (PMF:prob_mass_fun A).

    Definition sa_discrete (x:pre_event A) : sa_sigma (SigmaAlgebra:=discrete_sa A) x.
    Proof.
      now vm_compute.
    Qed.
    
    Definition discrete_singleton (x:A) : event (discrete_sa A)
      := event_singleton x (sa_discrete _).
    
    Lemma countable_pre_event_is_countable (e:pre_event A) : is_countable e.
    Proof.
      exists (fun n a => countable_index a = n /\ e a).
      split.
      - intros ??? [??] [??].
        apply countable_index_inj; congruence.
      - intros ?; split.
        + intros.
          eauto.
        + now intros [?[?]].
    Qed.

    Definition pmf_parts (x:event (discrete_sa A)) : nat -> R
      := fun n => match countable_inv n with
               | Some a => if excluded_middle_informative (x a)
                          then PMF.(pmf_pmf) a
                          else 0
               | None => 0
               end.

    Instance pmf_parts_proper : Proper (event_equiv ==> eq ==> eq) pmf_parts.
    Proof.
      intros ?? eqq ???; subst.
      unfold pmf_parts; simpl.
      repeat match_destr
      ; apply eqq in e; tauto.
    Qed.

    Definition ex_pmf_pos a :=
      {r | infinite_sum' (pmf_parts a) r}.
    
    Lemma pmf_pmf_le1 a : (PMF.(pmf_pmf) a <= 1).
    Proof.
      generalize (PMF.(pmf_pmf_one)); intros HH.
      red in HH.
      apply (infinite_sum'_pos_one_le _ _ (countable_index a)) in HH.
      - simpl in HH.
        now rewrite countable_inv_index in HH.
      - intros.
        match_destr.
        + apply pmf_pmf_pos.
        + now right.
    Qed.
    
    Lemma pmf_parts_pos (x:event (discrete_sa A)) (n:nat) :
      0 <= pmf_parts x n.
    Proof.
      unfold pmf_parts.
      match_case; intros; [| lra].
      match_destr; [| lra].
      apply pmf_pmf_pos.
    Qed.

    Lemma sum_pmf_parts_partial_incr (x:event (discrete_sa A)) (n:nat) :
      sum_f_R0 (pmf_parts x) n <= sum_f_R0 (pmf_parts x) (S n).
    Proof.
      intros.
      simpl.
      generalize (pmf_parts_pos x (S n)).
      lra.
    Qed.
    
    Lemma sum_pmf_parts_pos x (n : nat) : 0 <=sum_f_R0 (pmf_parts x) n.
    Proof.
      apply PartSum.cond_pos_sum; intros.
      apply pmf_parts_pos.
    Qed.

    Lemma sum_pmf_parts_le1 x (n : nat) : sum_f_R0 (pmf_parts x) n <= 1.
    Proof.
      intros.
      generalize (PMF.(pmf_pmf_one)); intros HH.
      red in HH.
      eapply Rle_trans.
      - apply (PartSum.sum_growing _
                                   (fun n : nat => match countable_inv n with
                                              | Some a => pmf_pmf PMF a
                                              | None => 0
                                              end)); intros.
        unfold pmf_parts.
        match_destr; [| lra].
        match_destr; [lra |].
        apply pmf_pmf_pos.
      - rewrite sum_f_R0_sum_f_R0'.
        eapply infinite_sum'_pos_prefix_le; trivial.
        intros.
        match_destr; [| lra].
        apply pmf_pmf_pos.
    Qed.

    Lemma ex_ps_of_pmf (x:event (discrete_sa A)) :
      {r | infinite_sum' (pmf_parts x) r}.
    Proof.
      exists (Lim_seq (fun i : nat => sum_f_R0 (pmf_parts x) i)).
      rewrite <- infinite_sum_infinite_sum'.
      rewrite <- infinite_sum_is_lim_seq.
      apply Lim_seq_correct'.
      apply (ex_finite_lim_seq_incr _ 1).
      - apply sum_pmf_parts_partial_incr. 
      - apply sum_pmf_parts_le1.
    Defined.

    Definition ps_of_pmf (x:event (discrete_sa A))
      := proj1_sig (ex_ps_of_pmf x).

    Instance ps_of_pmf_proper : Proper (event_equiv ==> eq) ps_of_pmf.
    Proof.
      intros ?? eqq.
      unfold ps_of_pmf, proj1_sig.
      repeat match_destr.
      eapply infinite_sum'_ext in i.
      - eapply infinite_sum'_unique; eauto.
      - intros.
        apply pmf_parts_proper; trivial.
        now symmetry.
    Qed.

    Lemma pmf_parts_all : rv_eq (pmf_parts Ω)
                                (fun n => match countable_inv n with
                                       | Some a => PMF.(pmf_pmf) a
                                       | None => 0
                                       end).

    Proof.
      intros ?.
      unfold pmf_parts.
      match_option.
      - match_destr.
        unfold Ω, pre_Ω in n; simpl in n; tauto.
    Qed.

    Lemma pmf_parts_none : rv_eq (pmf_parts ∅) (const 0).
    Proof.
      intros ?.
      unfold pmf_parts.
      match_option.
      match_destr.
      unfold event_none, pre_event_none in e; simpl in e; tauto.
    Qed.

    Lemma ps_of_pmf_all : ps_of_pmf Ω = 1.
    Proof.
      unfold ps_of_pmf, proj1_sig.
      match_destr.
      generalize (pmf_pmf_one PMF); intros.
      eapply infinite_sum'_unique; try eapply i.
      erewrite infinite_sum'_ext; try eapply H.
      apply pmf_parts_all.
    Qed.

    Lemma ps_of_pmf_none : ps_of_pmf ∅ = 0.
    Proof.
      unfold ps_of_pmf, proj1_sig.
      match_destr.
      rewrite (infinite_sum'_ext _ (const 0)) in i; try eapply H.
      - now apply infinite_sum'_const0 in i.
      - apply pmf_parts_none.
    Qed.

    Lemma ps_of_pmf_pos x : 0 <= ps_of_pmf x.
    Proof.
      unfold ps_of_pmf, proj1_sig.
      match_destr.
      eapply infinite_sum'_pos; eauto.
      apply pmf_parts_pos.
    Qed.

    Lemma ps_of_pmf_le1 x : ps_of_pmf x <= 1.
    Proof.
      unfold ps_of_pmf, proj1_sig.
      match_destr.
      eapply infinite_sum'_le; eauto.
      - apply PMF.(pmf_pmf_one).
      - intros.
        unfold pmf_parts.
        match_destr; try lra.
        match_destr; try lra.
        apply pmf_pmf_pos.
    Qed.

    Lemma ps_of_pmf_singleton (x:A) :
      ps_of_pmf (discrete_singleton x) = PMF.(pmf_pmf) x.
    Proof.
      unfold ps_of_pmf, proj1_sig.
      match_destr.
      eapply (infinite_sum'_one _ (countable_index x)) in i.
      + unfold pmf_parts in i.
        rewrite countable_inv_index in i.
        match_destr_in i.
        elim n.
        reflexivity.
      + intros.
        clear H.
        unfold pmf_parts, discrete_singleton.
        match_option.
        match_destr.
        vm_compute in e.
        subst.
        apply countable_inv_sound in eqq.
        congruence.
    Qed.

    Lemma sum_series_of_pmf_disjoint_union collection :
      collection_is_pairwise_disjoint collection ->
      forall n2, infinite_sum' (fun n1 : nat => pmf_parts (collection n1) n2)
                          (pmf_parts ((union_of_collection collection)) n2).
    Proof.
      intros.
      unfold pmf_parts; simpl.
      match_destr.
      - match_destr.
        + destruct e as [n na].
          eapply (infinite_sum'_one _ n).
          * intros.
            match_destr.
            elim (H _ _ H0 a); eauto.
          * match_destr.
              elim n0.
              eauto.
        + erewrite infinite_sum'_ext.
          * apply infinite_sum'0. 
          * intros.
            simpl.
            match_destr.
            elim n.
            eauto.
      - apply infinite_sum'0.
    Qed.


Lemma lim_seq_series_of_pmf_disjoint_union collection :
      collection_is_pairwise_disjoint collection ->
      forall n2, Lim_seq (sum_f_R0 (fun n1 : nat => pmf_parts (collection n1) n2)) =
            pmf_parts ((union_of_collection collection)) n2.
    Proof.
      intros.
      unfold pmf_parts; simpl.
      match_destr.
      - match_destr.
        + destruct e as [n na].
          assert (HH:infinite_sum' 
                       (fun n1 : nat => if excluded_middle_informative (collection n1 a) then pmf_pmf PMF a else 0)
                                (pmf_pmf PMF a)).
          {
            eapply (infinite_sum'_one _ n).
            - intros.
              match_destr.
              elim (H _ _ H0 a); eauto.
            - match_destr.
              elim n0.
              eauto.
          }
          rewrite <- infinite_sum_infinite_sum' in HH.
          rewrite <- infinite_sum_is_lim_seq in HH.
          now apply is_lim_seq_unique in HH.
        + erewrite Lim_seq_ext.
          * rewrite Lim_seq_const; reflexivity.
          * intros.
            rewrite sum_f_R0_sum_f_R0'.
            erewrite sum_f_R0'_ext.
            -- rewrite (sum_f_R0'_const 0).
               lra.
            -- intros.
               match_destr.
               elim n.
               eauto.
      - erewrite Lim_seq_ext.
        + rewrite Lim_seq_const; reflexivity.
        + intros.
          rewrite sum_f_R0_sum_f_R0'.
          rewrite sum_f_R0'_const.
          lra.
    Qed.


    Lemma le_incr0 (f : nat -> R) :
      (forall n, f n <= f (S n)) ->
      (forall n k, f n <= f (n + k)%nat).
    Proof.
      intros.
      induction k.
      - replace (n + 0)%nat with n by lia.
        lra.
      - eapply Rle_trans.
        apply IHk.
        replace (n + S k)%nat with (S (n + k)%nat) by lia.
        apply H.
     Qed.

    Lemma le_incr (f : nat -> R) :
      (forall n, f n <= f (S n)) ->
      (forall n m, (n<=m)%nat -> f n <= f m).
    Proof.
      intros.
      replace (m) with (n + (m-n))%nat by lia.
      now apply le_incr0.
    Qed.
      
    Lemma lim_seq_sup_seq_incr (f : nat -> R) (l : Rbar) :
      (forall n, f n <= f (S n)) ->
      is_lim_seq f l <-> is_sup_seq f l.
   Proof.
     intros.
     split; intros.
     apply is_lim_LimSup_seq in H0.
     destruct l.
     - unfold is_LimSup_seq in H0.
       unfold is_sup_seq.
       intros.
       specialize (H0 eps).
       destruct H0.
       simpl.
       split; intros.
       + destruct H1.
         destruct (le_dec x n).
         * now apply H1.
         * assert (n <= x)%nat by lia.
           apply Rle_lt_trans with (r2 := f x).
           now apply le_incr.
           apply H1; lia.
       + specialize (H0 0%nat).
         destruct H0 as [n [? ?]].
         exists n.
         apply H2.
     - unfold is_LimSup_seq in H0.
       unfold is_sup_seq; simpl; intros.
       specialize (H0 M 0%nat).
       destruct H0 as [n [? ?]].
       exists n.
       apply H1.
     - unfold is_LimSup_seq in H0.
       unfold is_sup_seq; simpl; intros.
       specialize (H0 M).
       destruct H0 as [N H0].
       destruct (le_dec N n).
       + now apply H0.
       + assert (n <= N)%nat by lia.
         apply Rle_lt_trans with (r2 := f N).
         * now apply le_incr.
         * apply H0; lia.
     - rewrite <- is_lim_seq_spec.
       destruct l.
       + unfold is_sup_seq in H0.
         unfold is_lim_seq'; intros.
         specialize (H0 eps).
         destruct H0 as [? [n ?]].
         simpl in H1; simpl in H0.
         exists n; intros.
         destruct (Rge_dec (f n0) r).
         * specialize (H0 n0).
           rewrite Rabs_right; lra.
         * assert (f n0 < r) by lra.
           rewrite Rabs_left; [|lra].
           generalize (le_incr f H n n0 H2); intros.
           lra.
       + unfold is_sup_seq in H0.
         unfold is_lim_seq'; intros.
         specialize (H0 M); simpl in H0.
         destruct H0 as [n ?].
         exists n; intros.
         apply Rlt_le_trans with (r2 := f n); trivial.
         now apply le_incr.
       + unfold is_sup_seq in H0.
         unfold is_lim_seq'; intros.
         specialize (H0 M); simpl in H0.
         exists (0%nat); intros.
         apply H0.
    Qed.

   Lemma is_lub_sup_seq (u : nat -> R) (l : Rbar) :
     is_lub_Rbar (fun x => exists n, x = u n) l ->
     is_sup_seq u l.
   Proof.
     intros.
     apply Rbar_is_lub_sup_seq.
     unfold is_lub_Rbar in H.
     unfold Rbar_is_lub.
     destruct H.
     split.
     - unfold Rbar_is_upper_bound.
       unfold is_ub_Rbar in H.
       intros.
       destruct x.
       + apply H.
         destruct H1.
         exists x.
         now rewrite Rbar_finite_eq in H1.
       + destruct H1.
         discriminate.
       + destruct H1.
         discriminate.
     - intros.
       apply H0.
       unfold is_ub_Rbar.
       intros.
       apply H1.
       destruct H2.
       exists x0.
       rewrite H2.
       reflexivity.
   Qed.

   Lemma is_sub_seq_lub_R (u : nat -> R) (l : Rbar) :
     is_sup_seq u l -> is_lub_Rbar (fun x => exists n, x = u n) l.
   Proof.
     intros.
     apply is_sup_seq_lub in H.
     unfold Rbar_is_lub in H.
     unfold is_lub_Rbar.
     destruct H.
     split.
     - unfold Rbar_is_upper_bound in H.
       unfold is_ub_Rbar.
       intros.
       apply H.
       destruct H1.
       exists x0.
       rewrite H1.
       reflexivity.
     - intros.
       apply H0.
       unfold Rbar_is_upper_bound.
       unfold is_ub_Rbar in H1.
       intros.
       destruct x.
       + apply H1.
         destruct H2.
         exists x.
         now rewrite Rbar_finite_eq in H2.
       + destruct H2.
         discriminate.
       + destruct H2.
         discriminate.
   Qed.

    Lemma lim_seq_is_lub_incr (f : nat -> R) (l : Rbar) :
      (forall n, f n <= f (S n)) ->
      (is_lim_seq f l) <-> (is_lub_Rbar (fun x => exists n, x = f n) l).
    Proof.
      intros.
      rewrite lim_seq_sup_seq_incr; trivial.
      split; intros.
      now apply is_sub_seq_lub_R.
      now apply is_lub_sup_seq.
    Qed.

     Lemma one_ser_lub f :
       (forall i, 0 <= f i) ->
       Lim_seq (sum_f_R0 f) = Lub_Rbar (fun x => exists n, x = sum_f_R0 f n).
    Proof.
      intros.
      generalize (lim_seq_is_lub_incr (sum_f_R0 f) (Lub_Rbar (fun x => exists n, x = sum_f_R0 f n))); intros.
      cut_to H0.
      destruct H0.
      cut_to H1.
      now apply is_lim_seq_unique.
      apply Lub_Rbar_correct.
      now apply sum_f_R0_pos_incr.
    Qed.

    Lemma sum_f_R0_one_ser_lub f n :
      (forall i j, 0 <= f i j) ->
      sum_f_R0 (fun n1 => Lim_seq (sum_f_R0 (fun n2 => f n1 n2))) n =
      sum_f_R0 (fun n1 => Lub_Rbar (fun x => exists n, x = sum_f_R0 (fun n2 => f n1 n2) n)) n.
    Proof.
      intros.
      apply sum_f_R0_ext.
      intros.
      generalize (one_ser_lub (fun n2 => f x n2)); intros.
      cut_to H1; trivial.
      now f_equal.
    Qed.

    Lemma Lub_Rbar_nneg (f : nat -> R) :
      (forall i, 0 <= f i) ->
      Rbar_le 0 (Lub_Rbar (fun x => exists n, x = f n)).
    Proof.
      intros.
      Search Lub_Rbar.
      unfold Lub_Rbar.
      destruct (ex_lub_Rbar (fun x : R => exists n : nat, x = f n)).
      unfold proj1_sig.
      unfold is_lub_Rbar in i.
      destruct i.
      unfold is_ub_Rbar in H0.
      apply Rbar_le_trans with (y := f 0%nat).
      apply (H 0%nat).
      apply H0.
      now exists (0%nat).
    Qed.

     Lemma Lub_Rbar_nneg_real (f : nat -> R) :
      (forall i, 0 <= f i) ->
      0  <= Lub_Rbar (fun x => exists n, x = f n).
    Proof.
      intros.
      generalize (Lub_Rbar_nneg f H); intros.
      destruct (Lub_Rbar (fun x : R => exists n : nat, x = f n)).
      apply H0.
      simpl; lra.
      simpl; lra.
    Qed.

    Lemma Lub_Rbar_lim0 (g : nat -> R) (b : Rbar) :
      (forall x : R,
          (exists n : nat, x = g n) -> Rbar_le x b) ->
      Rbar_le
        (Lub_Rbar (fun x2 : R => exists n0 : nat, x2 = g n0))
        b.
    Proof.
      intros.
      unfold Lub_Rbar.
      destruct (ex_lub_Rbar (fun x2 : R => exists n0 : nat, x2 = g n0)).
      unfold proj1_sig.
      unfold is_lub_Rbar in i.
      destruct i.
      unfold is_ub_Rbar in *.
      apply H1.
      intros.
      now apply H.
   Qed.

    Lemma Sup_seq_plus (f g : nat -> R) :
      is_finite (Sup_seq f) ->
      is_finite (Sup_seq g) ->
      (forall n, f n <= f (S n)) ->
      (forall n, g n <= g (S n)) ->
      Sup_seq (fun n0 => (f n0) + (g n0)) =
      Sup_seq (fun n0 => f n0) + Sup_seq (fun n0 => g n0).
    Proof.
      intros fin_f fin_g incr_f incr_g.
      unfold Sup_seq in *.
      destruct (ex_sup_seq (fun x : nat => Finite (f x))).
      destruct (ex_sup_seq (fun x : nat => Finite (g x))).
      destruct  (ex_sup_seq (fun n0 : nat => Finite (Rplus (f n0) (g n0)))).
      destruct (lim_seq_sup_seq_incr f x incr_f); intros.
      specialize (H0 i).
      destruct (lim_seq_sup_seq_incr g x0 incr_g); intros.      
      specialize (H2 i0).
      unfold proj1_sig in *.
      rewrite <- fin_f in H0.
      rewrite <- fin_g in H2.
      generalize (is_lim_seq_plus' _ _ _ _ H0 H2); intros.
      generalize (lim_seq_sup_seq_incr (fun n : nat => f n + g n) (x + x0)); intros.
      cut_to H4.
      rewrite H4 in H3.
      apply is_sup_seq_unique in i1.
      apply is_sup_seq_unique in H3.
      rewrite H3 in i1.
      now symmetry.
      intros.
      specialize (incr_f n).
      specialize (incr_g n).
      lra.
    Qed.

    Lemma Sup_seq_Rbar_plus (f g : nat -> R) :
      (forall n, f n <= f (S n)) ->
      (forall n, g n <= g (S n)) ->
      Sup_seq (fun n0 => (f n0) + (g n0)) =
      Rbar_plus (Sup_seq (fun n0 => f n0)) (Sup_seq (fun n0 => g n0)).
    Proof.
      intros incr_f incr_g.
      unfold Sup_seq in *.
      destruct (ex_sup_seq (fun x : nat => Finite (f x))).
      destruct (ex_sup_seq (fun x : nat => Finite (g x))).
      destruct  (ex_sup_seq (fun n0 : nat => Finite (Rplus (f n0) (g n0)))).
      unfold proj1_sig in *.
      destruct (lim_seq_sup_seq_incr f x incr_f); intros.
      specialize (H0 i).
      destruct (lim_seq_sup_seq_incr g x0 incr_g); intros.      
      specialize (H2 i0).
      generalize (is_lim_seq_plus f g x x0 (Rbar_plus x x0) H0 H2); intros.
      cut_to H3.
      generalize (lim_seq_sup_seq_incr (fun n : nat => f n + g n) (Rbar_plus x x0)); intros.
      cut_to H4.
      rewrite H4 in H3.
      apply is_sup_seq_unique in i1.
      apply is_sup_seq_unique in H3.
      rewrite H3 in i1.
      now symmetry.
      intros.
      specialize (incr_f n).
      specialize (incr_g n).
      lra.
      apply Rbar_plus_correct.
      unfold ex_Rbar_plus.
      destruct x; destruct x0; unfold Rbar_plus'; trivial.
      unfold is_sup_seq in i0.
      specialize (i0 (g 0%nat) 0%nat).
      simpl in i0.
      lra.
      unfold is_sup_seq in i.
      specialize (i (f 0%nat) 0%nat).
      simpl in i.
      lra.
    Qed.
    
    Lemma finite_sup_sum (g : nat -> nat -> R) (x1 : nat) :
      (forall n m, g n m <= g n (S m)) ->
      (forall n1, is_finite (Sup_seq (g n1))) ->
      is_finite (Sup_seq (fun x : nat => sum_f_R0 (fun n1 : nat => g n1 x) x1)).
    Proof.
      intros.
      induction x1.
      - now simpl.
      - simpl.
        rewrite Sup_seq_plus; trivial.
        + rewrite <- IHx1.
          unfold is_finite.
          reflexivity.
        + intros.
          apply sum_f_R0_le.
          intros.
          apply H.
      Qed.
      
    Lemma sum_sup_comm  (g : nat -> nat -> R) (x1 : nat) :
      (forall n m, g n m <= g n (S m)) ->
      (forall n1, is_finite (Sup_seq (g n1))) ->
      (sum_f_R0 (fun n1 : nat => Sup_seq (g n1)) x1) = 
      Sup_seq (fun n0 => sum_f_R0 (fun n1 => g n1 n0) x1).
    Proof.
      intros.
      induction x1.
      - now simpl.
      - simpl.
        rewrite IHx1.
        rewrite Sup_seq_plus; trivial.
        + now apply finite_sup_sum.
        + intros.
          apply sum_f_R0_le.
          intros.
          apply H.
    Qed.

    Lemma Lub_Rbar_Sup_seq  (u : nat -> R) :
      Lub_Rbar (fun x => exists n, x = u n) = Sup_seq u.
    Proof.
      unfold Lub_Rbar, Sup_seq.
      destruct (ex_lub_Rbar (fun x : R => exists n : nat, x = u n)).
      destruct (ex_sup_seq (fun x : nat => u x)).
      unfold proj1_sig.
      apply is_lub_sup_seq in i.
      apply is_sup_seq_unique in i.
      apply is_sup_seq_unique in i0.
      rewrite i0 in i.
      symmetry.
      apply i.
    Qed.      

    Lemma sum_Lub_Rbar_comm  (g : nat -> nat -> R) (x1 : nat) :
      (forall n m, g n m <= g n (S m)) ->
      (forall n1, is_finite (Lub_Rbar (fun x2 : R => exists n0 : nat, x2 = g n1 n0))) ->
      (sum_f_R0 (fun n1 : nat => Lub_Rbar (fun x2 : R => exists n0 : nat, x2 = g n1 n0))
                x1) = 
      Lub_Rbar (fun x2 : R => exists n0 : nat, x2 = sum_f_R0 (fun n1 => g n1 n0) x1).
    Proof.
      intros.
      rewrite Lub_Rbar_Sup_seq.
      rewrite sum_f_R0_ext with
          (f2 := (fun n1 => Sup_seq (g n1))).
      apply sum_sup_comm; trivial.
      intros.
      rewrite is_finite_correct.
      specialize (H0 n1).
      rewrite is_finite_correct in H0.
      destruct H0.
      exists x.
      now rewrite Lub_Rbar_Sup_seq in H0.
      intros.
      rewrite Lub_Rbar_Sup_seq.
      reflexivity.
    Qed.

    Lemma Lub_Rbar_lim1 (g : nat -> nat -> R) (b : Rbar) (x1 : nat) :
      (forall i j, 0 <= g i j) ->
      (forall n m, g n m <= g n (S m)) ->
      (forall n1,  is_finite (Lub_Rbar (fun x2 : R => exists n0 : nat, x2 = g n1 n0))) ->
      (forall x : R,
        (exists n m : nat, x = sum_f_R0 (fun i : nat => g i m) n) -> Rbar_le x b) ->
      Rbar_le
        (sum_f_R0 (fun n1 : nat => Lub_Rbar (fun x2 : R => exists n0 : nat, x2 = g n1 n0))
                  x1) b.
    Proof.
      intros.
      rewrite sum_Lub_Rbar_comm; trivial.
      unfold Lub_Rbar.
      destruct (ex_lub_Rbar (fun x2 : R => exists n0 : nat, x2 = sum_f_R0 (fun n1 : nat => g n1 n0) x1)).
      unfold proj1_sig.
      unfold is_lub_Rbar in i.
      destruct i.
      unfold is_ub_Rbar in *.
      destruct x.
      - apply H4.
        intros.
        apply H2.
        exists x1.
        apply H5.
      - unfold real.
        apply Rbar_le_trans with (y := g 0%nat 0%nat).
        apply H.
        apply H2.
        exists 0%nat.
        now exists 0%nat.
      - unfold real.
        apply Rbar_le_trans with (y := g 0%nat 0%nat).
        apply H.
        apply H2.
        exists 0%nat.
        now exists 0%nat.
    Qed.
    
  Lemma Rplus_le_pos_l (f g : R) :
    0 <= g ->
    f <= f + g.
  Proof.
    intros.
    rewrite <- Rplus_0_r at 1.
    now apply Rplus_le_compat_l.
  Qed.

    Lemma double_ser_lub f :
      (forall i j, 0 <= f i j) ->
      (forall i, ex_finite_lim_seq (sum_f_R0 (fun j => f i j))) ->
      Lim_seq (sum_f_R0
                 (fun n1 =>
                    Lim_seq
                      (sum_f_R0 (fun n2 => f n1 n2)))) =
      Lub_Rbar (fun x => exists (n m : nat), 
                    x = sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) m) n).
    Proof.
      intros.
      symmetry.
      apply is_lub_Rbar_unique.
      unfold is_lub_Rbar.
      split.
      - unfold is_ub_Rbar.
        intros.
        destruct H1 as [n [m H1]].
        rewrite H1.
        + rewrite <- Lim_seq_const.
          apply Lim_seq_le_loc.
          exists (S n); intros.
          rewrite sum_f_R0_split with (n := n0) (m := n); [|lia].
          apply Rle_trans with 
              (r2 := sum_f_R0 (fun n1 : nat => Lim_seq (sum_f_R0 (fun n2 : nat => f n1 n2))) n).
          * apply sum_f_R0_le; intros.
            assert (Rbar_le  (sum_f_R0 (fun j : nat => f i j) m)
                           (Lim_seq (sum_f_R0 (fun n2 : nat => f i n2)))).
            { 
              rewrite <- Lim_seq_const.
              apply Lim_seq_le_loc.
              exists (S m); intros.
              rewrite sum_f_R0_split with (n := n1) (m := m); [|lia].
              apply Rplus_le_pos_l.
              apply sum_f_R0_nneg; intros.
              apply H.
            }
            specialize (H0 i).
            unfold ex_finite_lim_seq in H0.
            destruct H0 as [l H0].
            apply is_lim_seq_unique in H0.
            rewrite H0 in H4; simpl in H4.
            now rewrite H0.
          * apply Rplus_le_pos_l.
            apply sum_f_R0_nneg; intros.
            assert (Rbar_le 0
                            (Lim_seq (sum_f_R0 (fun n2 : nat => f (n1 + S n)%nat n2)))).
            -- rewrite <- Lim_seq_const.
               apply Lim_seq_le_loc.
               exists (0%nat); intros.
               apply sum_f_R0_nneg; intros.
               apply H.
            -- specialize (H0 (n1 + S n)%nat).
               unfold ex_finite_lim_seq in H0.
               destruct H0 as [l H0].
               apply is_lim_seq_unique in H0.
               rewrite H0 in H4; simpl in H4.
               now rewrite H0.
      - intros.
        unfold is_ub_Rbar in H1.
        assert (forall n,
                   sum_f_R0 (fun n1 => Lim_seq (sum_f_R0 (fun n2 => f n1 n2))) n =
                   sum_f_R0 (fun n1 => Lub_Rbar (fun x => exists n, x = sum_f_R0 (fun n2 => f n1 n2) n)) n).
        intros; now apply sum_f_R0_one_ser_lub.
        rewrite Lim_seq_ext with
            (v := sum_f_R0 (fun n1 : nat => Lub_Rbar (fun x : R => exists n0 : nat, x = sum_f_R0 (fun n2 : nat => f n1 n2) n0))); [|apply H2].
        rewrite one_ser_lub.
        unfold Lub_Rbar at 1.
        destruct
          (ex_lub_Rbar
          (fun x : R =>
           exists n : nat,
             x =
             sum_f_R0
               (fun n1 : nat => Lub_Rbar (fun x0 : R => exists n0 : nat, x0 = sum_f_R0 (fun n2 : nat => f n1 n2) n0))
               n)).
        simpl.
        unfold is_lub_Rbar in i.
        destruct i.
        unfold is_ub_Rbar in *.
        apply H4.
        intros.
        destruct H5.
        rewrite H5.
        apply Lub_Rbar_lim1; trivial.
        intros; apply sum_f_R0_nneg.
        intros; apply H.
        intros; simpl.
        now apply Rplus_le_pos_l.
        intros.
        rewrite Lub_Rbar_Sup_seq.
        specialize (H0 n1).
        unfold ex_finite_lim_seq in H0.
        destruct H0.
        rewrite lim_seq_sup_seq_incr in H0.
        apply is_sup_seq_unique in H0.
        now rewrite H0.
        intros; simpl.
        now apply Rplus_le_pos_l.
        intros; apply Lub_Rbar_nneg_real.
        intros; now apply sum_f_R0_nneg.
    Qed.
    
   Lemma finite_sum_exchange f (x0 x1 : nat) :
     sum_f_R0 (fun j : nat => sum_f_R0 (fun i : nat => f i j) x0) x1 =
     sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => f i j) x1) x0.
   Proof.
     induction x0.
     - now simpl.
     - rewrite sum_f_R0_peel.
       rewrite <- IHx0.      
       clear IHx0.
       induction x1.
       + now simpl.
       + rewrite sum_f_R0_peel.
         rewrite IHx1.
         do 3 rewrite sum_f_R0_peel.
         lra.
    Qed.

   Lemma Lub_Rbar_exchange f :
     Lub_Rbar
       (fun x : R =>
          exists n m : nat,
            x = sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => f i j) m) n) =
     Lub_Rbar
       (fun x : R =>
          exists n m : nat,
            x = sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => f j i) m) n).
   Proof.
     apply Lub_Rbar_eqset.
     intros.
     split; intros; destruct H as [n [m H]];
       exists m; exists n; rewrite H;
         apply finite_sum_exchange.
   Qed.

    Lemma Lim_seq_sum_swap f :
      (forall i j, 0 <= f i j) ->
      (forall i, ex_finite_lim_seq (sum_f_R0 (fun j => f i j))) ->
      (forall j, ex_finite_lim_seq (sum_f_R0 (fun i => f i j))) ->
      Lim_seq (sum_f_R0
                 (fun n1 =>
                    Lim_seq
                      (sum_f_R0 (fun n2 => f n1 n2)))) =
      Lim_seq (sum_f_R0
                 (fun n2 =>
                    Lim_seq
                      (sum_f_R0 (fun n1 => f n1 n2)))).
    Proof.
      intros.
      rewrite double_ser_lub; trivial.
      rewrite double_ser_lub; trivial.
      apply Lub_Rbar_exchange.
    Qed.
    
    Lemma Lim_seq_incr_one_le f n :
      (forall i, f i <= f (S i)) ->
      Rbar_le (f n) (Lim_seq f).
    Proof.
      intros.
      generalize (Lim_seq_le_loc (fun _ => f n) f); intros HH.
      rewrite Lim_seq_const in HH.
      apply HH.
      red.
      exists n.
      clear HH.
      intros i ile.
      induction ile.
      - lra.
      - eapply Rle_trans; try eapply IHile.
        eauto.
    Qed.

    Lemma pmf_parts_sub_total collection j n :
      collection_is_pairwise_disjoint collection ->
      sum_f_R0 (fun i0 : nat => pmf_parts (collection i0) j) n <=  
      pmf_parts (union_of_collection collection) j.
    Proof.
      intros disj.
      rewrite sum_f_R0_sum_f_R0'.
      generalize (sum_series_of_pmf_disjoint_union collection disj j)
      ; intros HH.

      apply  (infinite_sum'_pos_prefix_le _ _ (S n) HH).
      intros.
      apply pmf_parts_pos.
    Qed.
    
    Program Instance discrete_ps : ProbSpace (discrete_sa A)
      := {|
      ps_P := ps_of_pmf
        |}.
    Next Obligation.
      unfold sum_of_probs_equals.
      unfold ps_of_pmf.
      - assert (inf:infinite_sum' (fun n => ps_of_pmf (collection n))
                              (ps_of_pmf (union_of_collection collection))).
        {
          unfold ps_of_pmf, proj1_sig.
          match_destr.
          generalize (sum_series_of_pmf_disjoint_union collection H); intros HH.
          rewrite <- infinite_sum_infinite_sum'.
          rewrite <- infinite_sum_is_lim_seq.
          rewrite <- infinite_sum_infinite_sum' in i.
          rewrite <- infinite_sum_is_lim_seq in i.
          assert (Finite x =  Lim_seq (
                                  sum_f_R0
                                    (fun n : nat => Lim_seq (fun i2 : nat => sum_f_R0 (pmf_parts (collection n)) i2)))).
          {
            rewrite Lim_seq_sum_swap.
            - rewrite (Lim_seq_ext _ (
                                     (sum_f_R0
                                        (pmf_parts ((union_of_collection collection)))) )).
              + generalize (is_lim_seq_unique _ _ i); intros.
                erewrite (Lim_seq_ext _  (fun i : nat => sum_f_R0 (pmf_parts (@union_of_collection A (discrete_sa A) collection)) i)) by reflexivity.
                destruct (Lim_seq (fun i1 : nat => sum_f_R0 (pmf_parts (union_of_collection collection)) i1)); subst; simpl; congruence.
              + intros. 
                eapply sum_f_R0_ext; intros.
                generalize (lim_seq_series_of_pmf_disjoint_union collection H x0); intros HH2.
                destruct (Lim_seq (sum_f_R0 (fun n1 : nat => pmf_parts (collection n1) x0)))
                ; simpl; congruence.
            - intros.
              apply pmf_parts_pos.
            - intros.
              apply ex_finite_lim_seq_incr with (M:=1).
              + apply sum_pmf_parts_partial_incr.
              + apply sum_pmf_parts_le1.
            - intros.
              apply ex_finite_lim_seq_incr with (M:=x).
              + intros.
                simpl.
                generalize (pmf_parts_pos (collection (S n)) j).
                lra.
              + intros.
                eapply Rle_trans.
                * now eapply pmf_parts_sub_total.
                * eapply (is_lim_seq_incr_compare) with (n:=j) in i.
                  -- {
                      eapply Rle_trans; try eapply i.
                      destruct j; simpl.
                      - lra.
                      - generalize (sum_pmf_parts_pos (union_of_collection collection) j).
                        lra.
                    }
                  -- apply sum_pmf_parts_partial_incr.
          }                   
          simpl.
          subst.
          rewrite H0 in i.
          rewrite H0.
          apply Lim_seq_correct.
          
          apply (ex_lim_seq_incr _).
          - intros.
            simpl.
            assert (0 <= Lim_seq (fun i1 : nat => sum_f_R0 (pmf_parts (collection (S n))) i1)).
            {
              generalize (Lim_seq_le_loc (fun _ => 0) (fun i1 : nat => sum_f_R0 (pmf_parts (collection (S n))) i1)); intros HH2.
              rewrite Lim_seq_const in HH2.
              simpl in HH2.
              cut_to HH2.
              - match_destr_in HH2.
                + simpl; lra.
                + tauto.
              - exists 0%nat; intros.
                apply PartSum.cond_pos_sum; intros.
                apply pmf_parts_pos.
            }
            lra.
        } 
        eapply infinite_sum'_ext; try eapply inf.
        intros.
        reflexivity.
    Qed.
    Next Obligation.
      apply ps_of_pmf_all.
    Qed.
    Next Obligation.
      apply ps_of_pmf_pos.
    Qed.

  End pmf_descr.

End discrete.

(* TODO? show that which countable instance does not matter *)

Section fin.

  Fixpoint find_index {A:Type} {dec:EqDec A eq} (x:A) (l:list A) : nat
    := match l with
       | nil => 0
       | y::ls=> if y == x
               then 0
               else S (find_index x ls)
       end.

  Lemma nth_find_index {A:Type} {dec:EqDec A eq} (x:A) l :
    nth (find_index x l) l x = x.
  Proof.
    induction l; simpl; trivial.
    now destruct (equiv_dec a x).
  Qed.

  Lemma find_index_le {A:Type} {dec:EqDec A eq} (x:A) l :
    (find_index x l <= length l)%nat.
  Proof.
    induction l; simpl; [lia | intros].
    match_destr; lia.
  Qed.
    
  Lemma find_index_in {A:Type} {dec:EqDec A eq} (x:A) l :
    In x l <->
    (find_index x l < length l)%nat.
  Proof.
    split.
    - induction l; simpl; [tauto|]; intros.
      match_destr.
      + lia.
      + cut_to IHl; [lia |].
        destruct H; congruence.
    - induction l; simpl; intros.
      + lia.
      + match_destr_in H.
        * eauto.
        * eauto with arith.
  Qed.

  Lemma find_index_nin {A:Type} {dec:EqDec A eq} (x:A) l :
    ~ In x l <->
    (find_index x l = length l)%nat.
  Proof.
    generalize (find_index_in x l); intros.
    destruct (le_lt_or_eq _ _ (find_index_le x l))
    ; firstorder.
    - lia.
    - intros inn.
      apply H in inn.
      lia.
  Qed.

  Program Global Instance finite_countable (A:Type) {dec:EqDec A eq}
         {finA:Finite.Finite A} : Countable A
    := {|
    countable_index a := find_index a (Finite.elms)
      |}.
  Next Obligation.
    intros ?? eqq.
    apply (f_equal (fun a => nth a elms x)) in eqq.
    rewrite nth_find_index in eqq.
    erewrite nth_in_default in eqq.
    - now rewrite nth_find_index in eqq.
    - apply find_index_in.
      apply Finite.finite.
  Qed.
     
End fin.

Section countable_products.
  
  Global Program Instance unit_finite : Finite.Finite unit
    := {|
    Finite.elms := tt::nil
      |}.
  Next Obligation.
    destruct x; eauto.
  Qed.

  Global Instance unit_eqdec : EqDec unit eq.
  Proof.
    intros [][]; left; reflexivity.
  Defined.

  Global Instance unit_countable : Countable unit
    := finite_countable unit.

  Global Program Instance prod_countable (A B:Type) {countableA:Countable A} {countableB:Countable B}: Countable (A * B)
    := {|
    countable_index '(a, b) := iso_f (countable_index a, countable_index b)
      |}.
  Next Obligation.
    intros [??] [??]; intros HH.
    cut (iso_f (Isomorphism:=nat_pair_encoder) (countable_index a, countable_index b) = (iso_f (countable_index a0, countable_index b0)))
    ; [| apply HH].
    intros HH2.
    generalize (f_equal (iso_b (Isomorphism:=nat_pair_encoder)) HH2)
    ; intros HH3.
    repeat rewrite iso_b_f in HH3.
    invcs HH3.
    apply countable_index_inj in H0.
    apply countable_index_inj in H1.
    congruence.
  Qed.

  Program Definition unit_pmf : prob_mass_fun unit
    := {|
    pmf_pmf _ := 1
      |}.
  Next Obligation.
    lra.
  Qed.
  Next Obligation.
    red.
    eapply (infinite_sum'_one _ (countable_index tt)).
    - intros.
      generalize (countable_inv_sound n' tt).
      match_destr; intros eqq.
      elim H.
      symmetry.
      apply eqq.
      now destruct u.
    - now rewrite countable_inv_index.
  Qed.

  Lemma countable_prod_inv_some A B {countableA} {countableB} n :
    match @countable_inv (prod A B) (@prod_countable A B countableA countableB) n with
    | Some (a,b) => (let '(n1,n2) := iso_b n in
                    @countable_inv A countableA n1 = Some a /\
                    @countable_inv B countableB n2 = Some b)
    | None => (let '(n1,n2) := iso_b n in
               @countable_inv A countableA n1 = None \/
               @countable_inv B countableB n2 = None)
    end.
  Proof.
    match_case; [intros [??] eqq1 | intros eqq1]
    ; match_case; intros ?? eqq2.
    - unfold countable_inv in eqq1.
      match_destr_in eqq1.
      destruct e as [[??] eqq3]; subst.
      unfold proj1_sig in eqq1.
      match_destr_in eqq1.
      invcs eqq1.
      apply (f_equal (@countable_inv _ (prod_countable A B))) in e.
      repeat rewrite countable_inv_index in e.
      invcs e.
      unfold countable_index, prod_countable in eqq2.
      rewrite iso_b_f in eqq2.
      invcs eqq2.
      repeat rewrite countable_inv_index.
      tauto.
    -  unfold countable_inv in eqq1.
       match_destr_in eqq1.
       case_eq (@countable_inv A countableA n0)
       ; [intros ? eqq3 | intros eqq3]; [| eauto].
       case_eq (@countable_inv B countableB n1)
       ; [intros ? eqq4 | intros eqq4]; [| eauto].
       elim n2.
       exists (a,b).
       unfold countable_index, prod_countable.
       apply countable_inv_sound in eqq3.
       apply countable_inv_sound in eqq4.
       apply (f_equal (iso_f (Isomorphism := nat_pair_encoder))) in eqq2.
       rewrite iso_f_b in eqq2.
       now subst.
  Qed.

  Lemma sum_n_n_pos_incr (f : nat -> nat -> R) :
    (forall i j, 0 <= f i j) ->
    forall n, sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) n) n <=
              sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) (S n)) (S n).
    intros.
    simpl.
    apply Rle_trans with (r2 := sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => f i j) n + f i (S n)) n).
    - apply sum_f_R0_le.
      intros.
      now apply Rplus_le_pos_l.
    - apply Rplus_le_pos_l.
      apply Rplus_le_le_0_compat; trivial.
      now apply sum_f_R0_nneg.
   Qed.

  Lemma lim_sum_n_n_pos (f : nat -> nat -> R) :
    (forall i j, 0 <= f i j) ->
    ex_lim_seq (fun n => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) n) n).
  Proof.
    intros.
    apply ex_lim_seq_incr.
    now apply sum_n_n_pos_incr.
   Qed.

  Lemma lim_sum_n_n_pos_bounded (f : nat -> nat -> R) (C:R):
    (forall i j, 0 <= f i j) ->
    (forall n, sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) n) n <= C) ->
    ex_finite_lim_seq (fun n => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) n) n).
  Proof.
    intros.
    apply ex_finite_lim_seq_incr with (M := C); trivial.
    now apply sum_n_n_pos_incr.
   Qed.

  Lemma cauchy_lim_sum_n_n_pos_bounded (f : nat -> nat -> R) (C:R):
    (forall i j, 0 <= f i j) ->
    (forall n, sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) n) n <= C) ->
    ex_lim_seq_cauchy (fun n => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) n) n).
  Proof.
    intros.
    rewrite <- ex_lim_seq_cauchy_corr.
    now apply lim_sum_n_n_pos_bounded with (C := C).
  Qed.

  Definition double_sum (f : nat -> nat -> R) (n m : nat) :=
     sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) m) n.

  Lemma double_sum_ge (f : nat -> nat -> R) (n1 n2 m1 m2 : nat) :
    (forall n m, 0 <= f n m) ->
    (n1 >= n2)%nat -> (m1 >= m2)%nat ->
    double_sum f n1 m1 - double_sum f n2 m2 >= 0.
  Proof.
    intros.
    apply Rge_minus.
    unfold double_sum.
    destruct (lt_dec n2 n1).
    - rewrite (sum_f_R0_split _ n1 n2); trivial.
      apply Rge_trans with (r2 := sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => f i j) m1) n2).
      + rewrite <- Rplus_0_r.
        apply Rplus_ge_compat_l.
        apply Rle_ge, sum_f_R0_nneg.
        intros.
        apply sum_f_R0_nneg.
        intros; apply H.
      + apply Rle_ge, sum_f_R0_le.
        intros.
        destruct (lt_dec m2 m1).
        * rewrite (sum_f_R0_split _ m1 m2); trivial.
          rewrite <- Rplus_0_r at 1.
          apply Rplus_le_compat_l.
          apply sum_f_R0_nneg.
          intros; apply H.
        * assert (m1 = m2) by lia; subst; lra.
    - assert (n1 = n2) by lia; subst.
      apply Rle_ge, sum_f_R0_le.
      intros.
      destruct (lt_dec m2 m1).
      + rewrite (sum_f_R0_split _ m1 m2); trivial.
        apply Rplus_le_pos_l.
        apply sum_f_R0_nneg.
        intros; apply H.
      + assert (m1 = m2) by lia; subst.
        lra.
   Qed.

  Lemma double_sum_le (f : nat -> nat -> R) (n1 n2 m1 m2 : nat) :
    (forall n m, 0 <= f n m) ->
    (n1 <= n2)%nat -> (m1 <= m2)%nat ->
    double_sum f n1 m1 - double_sum f n2 m2 <= 0.
  Proof.
    intros.
    generalize (double_sum_ge f n2 n1 m2 m1 H); intros.
    cut_to H2; try lia.
    lra.
  Qed.

  Lemma lim_sum_n_m_cauchy (f : nat -> nat -> R) (l:R) (eps : posreal) :
    (forall n m, 0 <= f n m) ->
    is_lim_seq (fun n => double_sum f n n) l ->
    exists (N:nat), forall (m n : nat), 
        (N <= m)%nat -> (N <= n)%nat ->
        Rabs (double_sum f m n - l) < eps.
  Proof.
    intros.
    assert (ex_lim_seq_cauchy (fun n => double_sum f n n)).
    {
      rewrite <- ex_lim_seq_cauchy_corr.
      unfold ex_finite_lim_seq.
      now exists l.
    }
    rewrite <- is_lim_seq_spec in H0.
    unfold is_lim_seq' in H0.
    unfold ex_lim_seq_cauchy in H1.
    assert (eps_half: 0 < eps/2).
    {
    assert (0 < eps) by apply cond_pos.
    lra.
    }
    specialize (H0 (mkposreal _ eps_half)).
    specialize (H1 (mkposreal _ eps_half)).
    destruct H0 as [M H0].
    destruct H1 as [N H1].
    exists (max M N).
    intros.
    specialize (H1 n m).
    cut_to H1; try lia.
    assert (Rabs ((double_sum f m m) - (double_sum f m n)) + 
            Rabs ((double_sum f m n) - (double_sum f n n)) =
            Rabs ((double_sum f m m) - (double_sum f n n))).
    {
      destruct (ge_dec m n)%nat.
      rewrite Rabs_right, Rabs_right, Rabs_right; try lra.
      apply double_sum_ge; trivial; lia.
      apply double_sum_ge; trivial; lia.
      apply double_sum_ge; trivial; lia.    
      rewrite Rabs_left1, Rabs_left1, Rabs_left1; try lra.
      apply double_sum_le; trivial; lia.
      apply double_sum_le; trivial; lia.
      apply double_sum_le; trivial; lia.    
    }
    assert (Rabs ((double_sum f m n) - (double_sum f n n)) < mkposreal _ eps_half).
    {
      rewrite Rabs_minus_sym in H1.
      rewrite <- H4 in H1.
      eapply Rle_lt_trans.
      - rewrite <- Rplus_0_l at 1.
        apply Rplus_le_compat_r.
        apply Rabs_pos.
      - apply H1.
    }
    generalize (Rabs_triang ((double_sum f m n) - (double_sum f n n))
                            ((double_sum f n n) - l)); intros.
    specialize (H0 n).
    cut_to H0; try lia.
    unfold Rminus in H6.
    rewrite Rplus_assoc in H6.
    rewrite <- Rplus_assoc with (r3 := -l) in H6.
    rewrite Rplus_opp_l in H6.
    rewrite Rplus_0_l in H6.
    simpl in *.
    unfold Rminus in *.
    lra.
  Qed.

  Lemma iterated_sum_product (f g : nat -> R) (a b : R) :
    is_lim_seq (sum_f_R0 f) a ->
    is_lim_seq (sum_f_R0 g) b ->
    is_lim_seq (sum_f_R0
                  (fun n1 =>
                     Lim_seq
                       (sum_f_R0 (fun n2 => (f n1)*(g n2))))) (a*b).
  Proof.
    intros.
    apply is_lim_seq_unique in H0.
    apply is_lim_seq_ext with
        (u := fun n => b * sum_f_R0 f n).
    - intros.
      rewrite sum_f_R0_ext with
          (f1 := (fun n1 : nat => Lim_seq (sum_f_R0 (fun n2 : nat => f n1 * g n2))))
          (f2 := fun n1 => (Lim_seq (sum_f_R0 g)) * (f n1)).
      + rewrite sum_f_R0_mult_const.
        now rewrite H0.
      + intros.
        rewrite Lim_seq_ext with (v := (fun n => (f x) * sum_f_R0 g n)).
        * rewrite Lim_seq_scal_l.
          rewrite H0.
          simpl.
          apply Rmult_comm.
        * intros.
          apply sum_f_R0_mult_const.
    - replace (Finite (a * b)) with (Rbar_mult b a).
      now apply is_lim_seq_scal_l.
      simpl.
      rewrite Rmult_comm.
      reflexivity.
  Qed.

  Lemma Lim_seq_nneg_Rbar (f : nat -> R) :
    (forall n, 0 <= f n) ->
    Rbar_le 0 (Lim_seq (sum_f_R0 f)).
  Proof.
    intros.
    apply Rbar_le_trans with (y := (sum_f_R0 f 0)).
    simpl.
    apply H.
    apply Lim_seq_incr_one_le.
    intros.
    rewrite sum_f_R0_peel.
    now apply Rplus_le_pos_l.
  Qed.

  Lemma Lim_seq_nneg (f : nat -> R) :
    (forall n, 0 <= f n) ->
    0 <= Lim_seq (sum_f_R0 f).
  Proof.
    intros.
    generalize (Lim_seq_nneg_Rbar f H); intros.
    destruct (Lim_seq (sum_f_R0 f)).
    apply H0.
    simpl; lra.
    simpl; lra.
 Qed.

  Lemma sum_lim_bound_Rbar (f : nat -> R) :
    (forall n, 0 <= f n) ->
    forall n, Rbar_le (sum_f_R0 f n) (Lim_seq (sum_f_R0 f)).
  Proof.
    intros.
    rewrite <- Lim_seq_const.
    apply Lim_seq_le_loc.
    exists n; intros.
    destruct (lt_dec n n0).
    generalize (sum_f_R0_split f n0 n); intros.
    rewrite H1; try lia.
    apply Rplus_le_pos_l.
    apply sum_f_R0_nneg.
    intros; apply H.
    assert ( n = n0 ) by lia.
    subst.
    lra.
  Qed.

   Lemma sum_lim_bound (f : nat -> R) :
    (forall n, 0 <= f n) ->
    ex_finite_lim_seq (sum_f_R0 f) ->
    forall n, sum_f_R0 f n <= Lim_seq (sum_f_R0 f).
   Proof.
     intros.
     generalize (sum_lim_bound_Rbar f H n); intros.
     unfold ex_finite_lim_seq in H0.
     destruct H0 as [l H0].
     apply is_lim_seq_unique in H0.
     rewrite H0 in H1.
     rewrite H0.
     now simpl in H1.
   Qed.

  Lemma finite_double_sum_lim_bound (f : nat -> nat -> R) :
    (forall n m, 0 <= f n m) ->
    (forall n1, ex_finite_lim_seq (sum_f_R0 (fun n2 => f n1 n2))) ->
    ex_finite_lim_seq (sum_f_R0
                         (fun n1 =>
                            Lim_seq
                              (sum_f_R0 (fun n2 => f n1 n2)))) ->
    forall n m, double_sum f n m <=
                Lim_seq (sum_f_R0
                           (fun n1 =>
                              Lim_seq
                                (sum_f_R0 (fun n2 => f n1 n2)))).
  Proof.
    intros.
    unfold double_sum.
    eapply Rle_trans.
    unfold ex_finite_lim_seq in H1.
    destruct H1 as [l H1].
    apply is_lim_seq_unique in H1.
    apply sum_f_R0_le.
    intros.
    now apply sum_lim_bound.
    apply sum_lim_bound; trivial.
    intros.
    now apply Lim_seq_nneg.
  Qed.

  Lemma sum_product_square_bound (f g : nat -> R) (a b : R) :
    (forall n, 0 <= f n) ->
    (forall n, 0 <= g n) ->
    is_lim_seq (sum_f_R0 f) a ->
    is_lim_seq (sum_f_R0 g) b ->
    forall n m, double_sum (fun i j => (f i)*(g j)) n m <= a*b.
  Proof.
    intros.
    generalize (iterated_sum_product f g a b H1 H2); intros.
    generalize (finite_double_sum_lim_bound (fun i j => (f i)*(g j))); intros.
    cut_to H4.
    apply is_lim_seq_unique in H3.
    replace (a*b) with (real (Finite (a * b))).
    rewrite <- H3.
    apply H4.
    reflexivity.
    intros.
    now apply Rmult_le_pos.
    intros.
    rewrite ex_finite_lim_seq_correct.
    split.
    apply ex_lim_seq_ext with (u := (fun n => (f n1) * (sum_f_R0 g n))).
    intros.
    now rewrite sum_f_R0_mult_const.
    apply ex_lim_seq_scal_l.
    now exists b.
    rewrite Lim_seq_ext with (v := (fun n => (f n1) * (sum_f_R0 g n))).
    rewrite Lim_seq_scal_l.
    apply is_lim_seq_unique in H2.
    rewrite H2.
    simpl.
    unfold is_finite.
    reflexivity.
    intros.
    now rewrite sum_f_R0_mult_const.
    unfold ex_finite_lim_seq.
    now exists (a*b).
  Qed.


  Lemma double_sum_Sn (f : nat -> nat -> R) (n m : nat) :
    double_sum f n (S m) =
    double_sum f n m + sum_f_R0 (fun i => f i (S m)) n.
  Proof.
    unfold double_sum.
    assert (forall i, sum_f_R0 (fun j => f i j) (S m) =
                      sum_f_R0 (fun j => f i j) m + (f i (S m))).
    intros.
    apply sum_f_R0_peel.
    rewrite sum_f_R0_ext with 
        (f2 := fun i =>  sum_f_R0 (fun j : nat => f i j) m + f i (S m)).
    now rewrite sum_plus.
    intros.
    apply sum_f_R0_peel.
  Qed.

  Lemma double_sum_square_incr (f : nat -> nat -> R) :
    (forall n m, 0 <= f n m) ->
    forall n : nat,
      double_sum f n n <= double_sum f (S n) (S n).
  Proof.
    unfold double_sum.
    intros.
    rewrite sum_f_R0_peel.
    generalize (double_sum_Sn f n n); intros.
    unfold double_sum in H0.
    rewrite H0.
    rewrite Rplus_assoc.
    apply Rplus_le_pos_l.
    apply Rplus_le_le_0_compat.
    apply sum_f_R0_nneg.
    intros; apply H.
    apply sum_f_R0_nneg.
    intros; apply H.
  Qed.

  Lemma double_sum_prod (f g : nat -> R) (n m : nat) :
    double_sum (fun i j => (f i)*(g j)) n m =
    (sum_f_R0 f n) * (sum_f_R0 g m).
    Proof.
      unfold double_sum.
      rewrite sum_f_R0_ext with
          (f2 := fun i => (sum_f_R0 g m) * (f i)).
      rewrite sum_f_R0_mult_const.
      apply Rmult_comm.
      intros.
      rewrite sum_f_R0_mult_const.
      apply Rmult_comm.
    Qed.

  Lemma lim_sum_product_square (f g : nat -> R) (a b : R) :
    is_lim_seq (sum_f_R0 f) a ->
    is_lim_seq (sum_f_R0 g) b ->
    is_lim_seq (fun n => double_sum (fun i j => (f i)*(g j)) n n) (a*b).
  Proof.
    intros.
    apply is_lim_seq_ext with
        (u := fun n => (sum_f_R0 f n) * (sum_f_R0 g n)).
    intro; symmetry.
    apply double_sum_prod.
    apply is_lim_seq_mult with (l1 := a) (l2 := b); trivial.
    unfold is_Rbar_mult.
    now simpl.
  Qed.

  Lemma prod_prob_mass_fun_sum_incr (A B:Type) 
        {countableA:Countable A} {countableB:Countable B}
        (pmf1:prob_mass_fun A) (pmf2:prob_mass_fun B) :
     forall n : nat,
  sum_f_R0
    (fun n0 : nat =>
     let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) n0 in
     match countable_inv n1 with
     | Some a => pmf_pmf pmf1 a
     | None => 0
     end * match countable_inv n2 with
           | Some a => pmf_pmf pmf2 a
           | None => 0
           end) n <=
  sum_f_R0
    (fun n0 : nat =>
     let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) n0 in
     match countable_inv n1 with
     | Some a => pmf_pmf pmf1 a
     | None => 0
     end * match countable_inv n2 with
           | Some a => pmf_pmf pmf2 a
           | None => 0
           end) (S n).
    Proof.
      intros.
      rewrite sum_f_R0_peel.
      apply Rplus_le_pos_l; match_destr.
      apply Rmult_le_pos; match_destr; try lra; apply pmf_pmf_pos.
   Qed.

    Lemma sup_seq_squeeze (f g : nat -> R) (l:R) :
      is_sup_seq f l ->
      (forall n, exists m1, g n <= f m1) ->
      (forall n, exists m2, f n <= g m2) ->
      is_sup_seq g l.
    Proof.
      unfold is_sup_seq in *.
      simpl in *; intros.
      destruct (H eps) as [? [N ?]].
      split.
      - intros.
        destruct (H0 n) as [m1 ?].
        specialize (H2 m1).
        lra.
      - destruct (H1 N) as [m2 ?].
        exists m2.
        lra.
    Qed.

    Lemma lim_seq_incr_squeeze (f g : nat -> R) (l:R) :
      (forall n, f n <= f (S n)) ->
      (forall n, g n <= g (S n)) ->
      is_lim_seq f l ->
      (forall n, exists m1, g n <= f m1) ->
      (forall n, exists m2, f n <= g m2) ->
      is_lim_seq g l.
   Proof.
     intros.
     apply lim_seq_sup_seq_incr in H1; trivial.
     apply lim_seq_sup_seq_incr; trivial.
     now apply (sup_seq_squeeze f g l).
   Qed.

   Lemma pair_encode_contains_square (n: nat) :
     exists (c : nat),
     forall (n1 n2 : nat),
       (n1 <= n)%nat -> (n2 <= n)%nat ->
       (iso_f (Isomorphism:=nat_pair_encoder) (n1, n2) <= c)%nat.
   Proof.
     exists (list_max
               (map
                  (iso_f (Isomorphism:=nat_pair_encoder))
                  (list_prod (seq 0 (S n)) (seq 0 (S n))))).
     intros.
     generalize (list_max_upper
                   (map
                      (iso_f (Isomorphism:=nat_pair_encoder))
                      (list_prod (seq 0 (S n)) (seq 0 (S n))))); intros.
     rewrite Forall_forall in H1; apply H1.
     apply in_map.
     apply in_prod; rewrite in_seq; lia.
   Qed.

   Lemma pair_encode_contains_square2 (n: nat) :
     exists m2, 
       incl (list_prod (seq 0 (S n)) (seq 0 (S n))) (map iso_b (seq 0 (S m2))).
   Proof.
     destruct (pair_encode_contains_square n).
     exists x.
     apply incl_Forall_in_iff.
     rewrite Forall_forall.
     intros.
     destruct x0.
     apply in_prod_iff in H0.
     destruct H0.
     apply in_seq in H0.
     apply in_seq in H1.
     assert (n0 <= n)%nat by lia.
     assert (n1 <= n)%nat by lia.
     specialize (H n0 n1 H2 H3).
     assert (In (iso_f  (n0, n1)) (seq 0 (S x))) by (apply in_seq; lia).
     apply in_map with (f := iso_b (Isomorphism:=nat_pair_encoder)) in H4.
     assert (iso_b (iso_f (n0, n1)) = (n0, n1)) by now rewrite iso_b_f.
     rewrite <- H5.
     apply H4.
   Qed.

   Lemma square_contains_pair_encode (c : nat) :
     exists (n : nat),
     forall (c1 : nat), (c1 <= c)%nat ->
        let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) c1 in
        (max n1 n2 <= n)%nat.
   Proof.
     exists (list_max
               (map
                  (fun c1 => 
                     let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) c1 in
                     max n1 n2)
                  (seq 0 (S c)))).
     intros.
     match_case; intros.
     induction c.
     - simpl.
       assert (c1 = 0%nat) by lia.
       subst.
       inversion H0.
       now subst.
     - destruct (le_dec c1 c).
       + specialize (IHc l).
         eapply le_trans.
         apply IHc.
         rewrite seq_S with (len := (S c)).
         rewrite map_app, list_max_app.
         apply Nat.le_max_l.
       + assert (c1 = S c) by lia.
         rewrite seq_S, map_app, list_max_app.
         rewrite Nat.max_le_iff; right.
         replace (0 + S c)%nat with (S c) by lia.
         rewrite H1 in H0.
         rewrite map_cons.
         rewrite H0.
         simpl.
         apply Nat.le_max_l.         
   Qed.

   Lemma square_contains_pair_encode2 (n : nat) :
     exists m1,
       incl (map iso_b (seq 0 (S n))) (list_prod (seq 0 (S m1)) (seq 0 (S m1))).
   Proof.
     destruct (square_contains_pair_encode n).
     exists x.
     apply incl_Forall_in_iff.
     rewrite Forall_forall.
     intros.
     specialize (H (iso_f x0)).
     destruct x0 as (x1, x2).
     cut_to H.
     - apply in_map_iff in H0.
       destruct H0 as [? [? ?]].
       apply in_prod_iff.
       generalize (iso_b_f (x1, x2)); intros.
       rewrite H2 in H.
       split; apply in_seq; lia.
     - apply in_map with (f := iso_f) in H0.
       replace (map iso_f (map iso_b (seq 0 (S n)))) with (seq 0 (S n)) in H0.
       + apply in_seq in H0; lia.
       + rewrite map_map.
         rewrite map_ext with (g := fun u => u).
         * now rewrite map_id.
         * apply iso_f_b.
   Qed.

   Lemma list_sum_nest_prod (f : nat -> nat -> R ) (l1 l2 : list nat) :
     list_sum
       (map (fun i : nat => list_sum (map (fun j : nat => f i j) l2)) l1) =
     list_sum (map (fun '(a, b) => f a b) (list_prod l1 l2)).
   Proof.
     intros.
     induction l1.
     - simpl.
       induction l2.
       + now simpl.
       + simpl; lra.
     - simpl.
       rewrite IHl1, map_app, list_sum_cat.
       apply Rplus_eq_compat_r.
       now rewrite map_map.
    Qed.
   
   Lemma double_sum_list_sum (f : nat -> nat -> R ) (n m : nat) :
     double_sum f n m =
     list_sum (map (fun '(a, b) => f a b) (list_prod (seq 0 (S n)) (seq 0 (S m)))).
   Proof.
     unfold double_sum.
     rewrite sum_f_R0_ext with
         (f2 := (fun i => list_sum (map (fun j => f i j) (seq 0 (S m))))).
     rewrite sum_f_R0_sum_f_R0'.
     rewrite sum_f_R0'_list_sum.
     apply list_sum_nest_prod.
     intros.
     rewrite sum_f_R0_sum_f_R0'.
     now rewrite sum_f_R0'_list_sum.
   Qed.

   Lemma sum_f_R0_pairs_list_sum (f : nat -> nat -> R) (m : nat) :
      sum_f_R0
        (fun n0 : nat =>
           let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) n0 in 
           (f n1 n2)) m =
      list_sum (map (fun '(a, b) => f a b)
                    (map (iso_b (Isomorphism:=nat_pair_encoder)) (seq 0 (S m)))).
   Proof.
     induction m.
     - simpl; lra.
     - rewrite sum_f_R0_peel.
       rewrite IHm.
       rewrite seq_S with (len := (S m)).
       do 2 rewrite map_app.
       rewrite list_sum_cat.
       apply Rplus_eq_compat_l.
       simpl.
       now rewrite Rplus_0_r.
   Qed.

   Lemma iso_sum_le_double_sum (f g : nat -> R) :
     (forall n, 0 <= f n) ->
     (forall n, 0 <= g n) ->
     forall n,
     exists m1 : nat,
       sum_f_R0
         (fun n0 : nat =>
            let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) n0 in 
            (f n1)*(g n2)) n <=
    double_sum
      (fun i j : nat => (f i)*(g j)) m1 m1.
  Proof.
    intros.
    destruct (square_contains_pair_encode2 n) as [m1 ?].
    exists m1.
    rewrite double_sum_list_sum.
    rewrite sum_f_R0_pairs_list_sum.
    generalize (@incl_NoDup_sublist_perm (nat*nat) _  (map iso_b (seq 0 (S n)))
                                         (list_prod (seq 0 (S m1)) (seq 0 (S m1))))
    ; intros.
    cut_to H2; trivial.
    - destruct H2 as [l [? ?]].
      apply Rle_trans with (r2 :=  list_sum (map (fun '(a, b) => f a * g b) l)).
      + right.
        apply list_sum_perm_eq.
        now apply Permutation_map.
      + apply list_sum_pos_sublist_le.
        * intros.
          apply in_map_iff in H4.
          destruct H4 as [x0 [? ?]].
          rewrite <- H4.
          match_destr.
          now apply Rmult_le_pos.
        * now apply sublist_map.
    - apply NoDup_map_inv with (f := iso_f).
      replace (map iso_f (map iso_b (seq 0 (S n)))) with (seq 0 (S n)).
      apply seq_NoDup.
      rewrite map_map.
      rewrite map_ext with (g := fun u => u).
      + now rewrite map_id.
      + apply iso_f_b.
  Qed.

  Lemma NoDup_prod (l1 l2 : list nat) : 
    NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
  Proof.
    intros.
    induction l1.
    - simpl.
      apply NoDup_nil.
    - simpl.
      apply NoDup_cons_iff in H.
      destruct H.
      cut_to IHl1; trivial.
      apply NoDup_app; trivial.
      + unfold disjoint; intros.
        apply in_map_iff in H2.
        destruct H2 as [? [? ?]].
        rewrite <- H2 in H3.
        apply in_prod_iff in H3.
        tauto.
      + apply Injective_map_NoDup; trivial.
        unfold Injective; intros.
        now inversion H2.
  Qed.

  Lemma double_sum_le_iso_sum  (f g : nat -> R) :
     (forall n, 0 <= f n) ->
     (forall n, 0 <= g n) ->
     forall n,
     exists m2 : nat,
       double_sum (fun i j : nat => (f i) * (g j)) n n <=
       sum_f_R0
         (fun n0 : nat =>
            let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) n0 in 
            (f n1) * (g n2)) m2.
  Proof.
    intros.
    destruct (pair_encode_contains_square2 n) as [m2 ?].
    exists m2.
    rewrite double_sum_list_sum.    
    rewrite sum_f_R0_pairs_list_sum.
    generalize (@incl_NoDup_sublist_perm (nat*nat) _  
                                     (list_prod (seq 0 (S n)) (seq 0 (S n)))
                                     (map iso_b (seq 0 (S m2)))); intros.
    cut_to H2; trivial.
    - destruct H2 as [l [? ?]].
      apply Rle_trans with (r2 :=  list_sum (map (fun '(a, b) => f a * g b) l)).
      + right.
        apply list_sum_perm_eq.
        now apply Permutation_map.
      + apply list_sum_pos_sublist_le.
        * intros.
          apply in_map_iff in H4.
          destruct H4 as [x0 [? ?]].
          rewrite <- H4.
          match_destr.
          now apply Rmult_le_pos.
        * now apply sublist_map.
    - apply NoDup_prod; apply seq_NoDup.
  Qed.

  Lemma prod_prob_mass_fun_sum_1  (A B:Type) 
        {countableA:Countable A} {countableB:Countable B}
        (pmf1:prob_mass_fun A) (pmf2:prob_mass_fun B) :
  is_lim_seq
    (fun i : nat =>
     sum_f_R0
       (fun n : nat =>
        let (n1, n2) := iso_b (Isomorphism:=nat_pair_encoder) n in
        match countable_inv n1 with
        | Some a => pmf_pmf pmf1 a
        | None => 0
        end *
        match countable_inv n2 with
        | Some a => pmf_pmf pmf2 a
        | None => 0
        end) i) 1.
  Proof.
    generalize (pmf_pmf_one pmf1); intros.
    unfold countable_sum in H.
    rewrite <- infinite_sum_infinite_sum' in H.
    rewrite <- infinite_sum_is_lim_seq in H.
    generalize (pmf_pmf_one pmf2); intros.    
    unfold countable_sum in H0.
    rewrite <- infinite_sum_infinite_sum' in H0.
    rewrite <- infinite_sum_is_lim_seq in H0.
    
    generalize (prod_prob_mass_fun_sum_incr A B pmf1 pmf2); intros.
    generalize (lim_sum_product_square 
                  (fun n1 => match countable_inv n1 with
                             | Some a => pmf_pmf pmf1 a
                             | None => 0
                             end)
                  (fun n2 => match countable_inv n2 with
                             | Some a => pmf_pmf pmf2 a
                             | None => 0
                             end)
                  1 1 H H0); intros.
    replace (1 * 1) with (1) in H2 by lra.
    eapply (lim_seq_incr_squeeze _ _ 1 _ H1 H2).
    - apply iso_sum_le_double_sum.
      intro; match_destr; try lra; apply pmf_pmf_pos.
      intro; match_destr; try lra; apply pmf_pmf_pos.      
    - apply double_sum_le_iso_sum.
      intro; match_destr; try lra; apply pmf_pmf_pos.
      intro; match_destr; try lra; apply pmf_pmf_pos.      
    Unshelve.
    apply double_sum_square_incr.
    intros.
    apply Rmult_le_pos; match_destr; try lra; apply pmf_pmf_pos.
  Qed.

  Program Definition prod_prob_mass_fun (A B:Type) {countableA:Countable A} {countableB:Countable B}
          (pmf1:prob_mass_fun A) (pmf2:prob_mass_fun B)
    : prob_mass_fun (A*B)
    := {|
    pmf_pmf '(a,b) := pmf1.(pmf_pmf) a * pmf2.(pmf_pmf) b
      |}.
  Next Obligation.
    apply Rmult_le_pos
    ; apply pmf_pmf_pos.
  Qed.
  Next Obligation.
    unfold countable_sum.

    cut (infinite_sum'
           (fun n : nat =>
              let (n1,n2) := iso_b (Isomorphism:=nat_pair_encoder) n in
              match countable_inv n1 with
              | Some a => pmf1.(pmf_pmf) a
              | None => 0
              end * 
              match countable_inv n2 with
              | Some a => pmf2.(pmf_pmf) a
              | None => 0
              end) 1).
    - apply infinite_sum'_ext; intros.
      generalize (countable_prod_inv_some A B x)
      ; intros HH.
      match_destr.
      + match_destr.
        match_destr.
        destruct HH as [HH1 HH2].
        now rewrite HH1, HH2.
      + match_destr.
        destruct HH as [HH|HH]
        ; rewrite HH
        ; lra.
    - rewrite <- infinite_sum_infinite_sum'.
      rewrite <- infinite_sum_is_lim_seq.
      apply prod_prob_mass_fun_sum_1.
  Qed.

  Fixpoint iter_prod (l:list Type) : Type
    := match l with
       | nil => unit
       | x::l' => prod x (iter_prod l')
       end.
  
  Instance iter_prod_countable (l:list Type) (countableL:forall x, In x l -> Countable x) :
    Countable (iter_prod l).
  Proof.
    induction l; simpl.
    - typeclasses eauto.
    - simpl in countableL.
      apply prod_countable; eauto.
  Defined.

  Definition list_prod_prob_mass_fun (l:list Type) (countableL:forall x, In x l -> Countable x)
          (pmfL:forall x (pf:In x l), prob_mass_fun (countableA:=countableL _ pf) x)
    : prob_mass_fun (iter_prod l).
  Proof.
    induction l; simpl in *.
    - apply unit_pmf.
    - apply prod_prob_mass_fun; eauto.
  Defined.
  
End countable_products.

