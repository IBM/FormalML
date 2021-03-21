Require Import Program.Basics.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.

Require Import Lra Lia.
Require Import List.
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

    Lemma sum_f_R0_le (f g : nat -> R) n :
      (forall (i:nat), (i<=n)%nat -> (f i) <= (g i)) ->
      sum_f_R0 f n <= sum_f_R0 g n.
    Proof.
      intros.
      induction n.
      - unfold sum_f_R0.
        simpl.
        apply H.
        lia.
      - do 2 rewrite sum_f_R0_peel.
        eapply Rle_trans.
        + apply Rplus_le_compat_r.
          apply IHn.
          intros.
          apply H.
          lia.
        + apply Rplus_le_compat_l.
          apply H.
          lia.
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
              rewrite <- Rplus_0_r at 1.
              apply Rplus_le_compat_l.
              rewrite <- sum_n_Reals.
              apply sum_n_nneg; intros.
              apply H.
            }
            specialize (H0 i).
            unfold ex_finite_lim_seq in H0.
            destruct H0 as [l H0].
            apply is_lim_seq_unique in H0.
            rewrite H0 in H4; simpl in H4.
            now rewrite H0.
          * rewrite <- Rplus_0_r at 1.
            apply Rplus_le_compat_l.
            rewrite <- sum_n_Reals.
            apply sum_n_nneg; intros.
            assert (Rbar_le 0
                            (Lim_seq (sum_f_R0 (fun n2 : nat => f (n1 + S n)%nat n2)))).
            -- rewrite <- Lim_seq_const.
               apply Lim_seq_le_loc.
               exists (0%nat); intros.
               rewrite <- sum_n_Reals.
               apply sum_n_nneg; intros.
               apply H.
            -- specialize (H0 (n1 + S n)%nat).
               unfold ex_finite_lim_seq in H0.
               destruct H0 as [l H0].
               apply is_lim_seq_unique in H0.
               rewrite H0 in H4; simpl in H4.
               now rewrite H0.
      - intros.
        unfold is_ub_Rbar in H1.
                 
   Admitted.

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
  Admitted.  
  
End countable_products.

