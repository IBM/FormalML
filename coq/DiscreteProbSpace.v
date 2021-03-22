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

    
    (*
    Lemma LimSup_seq_perm (f:nat -> R) (g:nat->nat):
      Bijective g ->
      ex_finite_lim_seq f ->
      LimSup_seq f =
      LimSup_seq (fun n => f (g n)).
    Proof.
      intros.
      unfold LimSup_seq, proj1_sig.
      repeat match_destr.
      unfold is_LimSup_seq in *.
      match_destr_in i; match_destr_in i0.
      - f_equal.
        destruct (Req_EM_T r r0); trivial.
        assert (diffpos:0 < Rabs (r - r0)).
        {
          apply Rabs_pos_lt.
          lra.
        }
        destruct (i (mkposreal _ diffpos)) as [HH1 [? HH2]].
        destruct (i0 (mkposreal _ diffpos)) as [HH3 [? HH4]].
        simpl in *.
        destruct (HH1 (max x x0)) as [?[??]].
        destruct (HH3 (max x x0)) as [?[??]].

        r < f x1 + Rabs (r - r0) < ... f (g n) -  Rabs (r - r0) < r0
        

        
      - 
      
      
    Qed.
     *)


    Lemma sum_f_R0'_list_sum f n :
      sum_f_R0' f n = list_sum (map f (seq 0 n)).
    Proof.
      now rewrite sum_f_R0'_as_fold_right, list_sum_fold_right, fold_right_map.
    Qed.

    Lemma bijective_injective {B C} (f:B->C) : Bijective f -> Injective f.
    Proof.
      intros [g [??]] ?? eqq.
      generalize (f_equal g eqq); intros eqq2.
      now repeat rewrite H in eqq2.
    Qed.

    Lemma list_sum_pos_sublist_le l1 l2 :
      (forall x, In x l2 -> 0 <= x) ->
      sublist l1 l2 ->
      list_sum l1 <= list_sum l2.
    Proof.
      intros pos subl.
      induction subl.
      - lra.
      - simpl.
        apply Rplus_le_compat_l.
        apply IHsubl.
        simpl in *; eauto.
      - simpl.
        replace (list_sum l1) with (0 + list_sum l1) by lra.
        apply Rplus_le_compat.
        + simpl in *.
          eauto.
        + eapply IHsubl.
          simpl in *; eauto.
    Qed.

    Lemma list_sum_Rabs_triangle l :
      Rabs (list_sum l) <= list_sum (map Rabs l).
    Proof.
      induction l; simpl.
      - rewrite Rabs_R0; lra.
      - eapply Rle_trans.
        + apply Rabs_triang.
        + lra.
    Qed.

    Lemma list_max_in l : l <> nil -> In (list_max l) l.
    Proof.
      induction l; simpl; [eauto |]; intros _.
      destruct (Max.max_dec a (list_max l))
      ; rewrite e in *
      ; eauto.
      destruct l.
      - simpl in e.
        rewrite Max.max_0_r in e; simpl
        ; eauto.
      - right; apply IHl; congruence.
    Qed.

    Lemma list_max_upper l :
      List.Forall (fun k : nat => (k <= list_max l)%nat) l.
    Proof.
      apply list_max_le.
      lia.
    Qed.

(*    Lemma NoDup_pigeon l :
      l <> nil ->
      {n | (n >= length l - 2 /\ In n l)%nat}.
    Proof.
      induction l; simpl; [congruence | intros _].
      destruct l; simpl.
      - exists a; split; eauto.
        lia.
      - cut_to IHl; [| congruence].
        destruct IHl as [k [kgeq kin]].
        simpl in *.
        
        
                rewrite minus_n_O.
 *)

    (* Lemma NoDup_pigeon a b l : *)
    (*   NoDup (a :: b :: l) -> *)
    (*   List.Forall (fun k : nat => (k <= length l)%nat) (a :: b :: l) -> *)
    (* Proof. *)
    (*   rewrite Forall_forall. *)
    (*   revert a b. *)
    (*   induction l; simpl; intros. *)
    (*   - assert (a = 0)%nat *)
    (*          by (assert (a <= 0)%nat by eauto; lia). *)
    (*     assert (b = 0)%nat *)
    (*          by (assert (b <= 0)%nat by eauto; lia). *)
    (*     intros nd. *)
    (*     invcs nd. *)
    (*     simpl in H4; eauto. *)
    (*   -  *)

        
    (* Lemma NoDup_pigeon a b l : *)
    (*   List.Forall (fun k : nat => (k <= length l)%nat) (a :: b :: l) -> *)
    (*   ~ NoDup (a :: b :: l). *)
    (* Proof. *)
    (*   rewrite Forall_forall. *)
    (*   revert a b. *)
    (*   induction l; simpl; intros. *)
    (*   - assert (a = 0)%nat *)
    (*          by (assert (a <= 0)%nat by eauto; lia). *)
    (*     assert (b = 0)%nat *)
    (*          by (assert (b <= 0)%nat by eauto; lia). *)
    (*     intros nd. *)
    (*     invcs nd. *)
    (*     simpl in H4; eauto. *)
    (*   -  *)


    Lemma NoDup_list_max_count l :
      NoDup l ->
      (length l <= S (list_max l))%nat.
    Proof.
      intros nd.
      assert (lincl:incl l (seq 0 (S (list_max l)))).
      {
        intros ??.
        apply in_seq.
        split; [lia| ].
        simpl.
        generalize (list_max_upper l).
        rewrite Forall_forall.
        intros HH.
        specialize (HH _ H).
        lia.
      } 
      
      generalize (NoDup_incl_length nd lincl)
      ; intros HH.
      now rewrite seq_length in HH.
    Qed.
    
    (* proof based on 
       https://www.math.ucdavis.edu/~npgallup/m17_mat25/lecture_notes/lecture_15/m17_mat25_lecture_15_notes.pdf *)
    Theorem infinite_sum'_perm (g:nat->nat) (f:nat -> R) l:
      Bijective g ->
      (exists l2, infinite_sum' (fun x => Rabs (f x)) l2) ->
      infinite_sum' f l ->
      infinite_sum' (fun n => f (g n)) l.
    Proof.
      intros bij fabs inf.
      
      assert (cc:Cauchy_crit (sum_f_R0 (fun x => Rabs (f x)))).
      {
        destruct fabs as [? inf2].
        apply CV_Cauchy.
        rewrite <- infinite_sum_infinite_sum' in inf2.
        rewrite  <- infinite_sum_is_lim_seq in inf2.
        rewrite is_lim_seq_Reals in inf2.
        eauto.
      } 

      generalize bij; intros [ginv [ginvg gginv]].

      unfold infinite_sum' in *; intros eps eps_pos.
      assert (eps2_pos : eps / 2 > 0) by lra.
      destruct (inf _ eps2_pos) as [N1 N1_lt].
      destruct (cc _ eps2_pos) as [N2 N2_lt].
      pose (N := S (max N1 N2)).
      pose (M := S (List.list_max (map ginv (seq 0 N)))).
      pose (sN := sum_f_R0' f N).
      assert (MltN:(N <= M)%nat).
      {
        unfold M.
        generalize (NoDup_list_max_count (map ginv (seq 0 N)))
        ; intros HH.
        cut_to HH.
        - now rewrite map_length, seq_length in HH.
        - apply Injective_map_NoDup.
          + intros ???.
            apply (f_equal g) in H.
            now repeat rewrite gginv in H.
          + apply seq_NoDup.
      }
      exists M; intros m mbig.
      unfold R_dist.
      replace (sum_f_R0' (fun n : nat => f (g n)) m - l)
        with ((sum_f_R0' (fun n : nat => f (g n)) m - sN) + (sN - l))
        by lra.
      eapply Rle_lt_trans.
      { eapply Rabs_triang. }
      apply (Rlt_le_trans _ (Rabs (sum_f_R0' (fun n : nat => f (g n)) m - sN) + eps / 2)).
      {
        apply Rplus_lt_compat_l.
        apply N1_lt.
        lia.
      }
      cut (Rabs (sum_f_R0' (fun n : nat => f (g n)) m - sN)   <= eps / 2); [lra|].
      
      unfold sN.
      repeat rewrite sum_f_R0'_list_sum.
      rewrite <- map_map.

      destruct (@incl_NoDup_sublist_perm _ _ (seq 0 N) (map g (seq 0 m)))
        as [gpre [gpre_perm gpre_subl]].
      {
        apply seq_NoDup.
      }
      {
        intros x xinn.
        apply in_seq in xinn.
        destruct xinn as [_ xlt].
        simpl in xlt.
        eapply in_map_iff.
        exists (ginv x).
        rewrite gginv.
        split; trivial.
        apply in_seq.
        split; [lia|].
        simpl.
        eapply lt_le_trans; try apply mbig.
        unfold M.
        unfold lt.
        generalize (list_max_upper (map ginv (seq 0 N))); intros FF.
        rewrite Forall_forall in FF.
        specialize (FF (ginv x)).
        cut_to FF.
        - lia.
        - apply in_map.
          apply in_seq; lia.
      } 
      rewrite gpre_perm.
      destruct (sublist_perm_head gpre_subl) as [l2 l2perm].
      rewrite <- l2perm.
      rewrite map_app.
      rewrite list_sum_cat.
      replace (list_sum (map f gpre) + list_sum (map f l2) - list_sum (map f gpre))
        with (list_sum (map f l2)) by lra.

      assert (ndgl:NoDup (gpre ++ l2)).
      {
        rewrite l2perm.
        apply Injective_map_NoDup.
        - now apply bijective_injective.
        - apply seq_NoDup.
      }

      assert(l2_lower: (forall x, In x l2 -> x >= N)%nat).
      {
        intros.
        destruct (ge_dec x N); trivial.
        apply not_ge in n.
        assert (inn:In x gpre).
        { 
          rewrite <- gpre_perm.
          apply in_seq.
          lia.
        }
        apply NoDup_app_disj in ndgl.
        elim (ndgl x inn H).
      } 
      pose (nn:=List.list_max l2).
      destruct (list_max_le l2 nn) as [l2_upper _].
      specialize (l2_upper (le_refl _)).
      assert (incl1:incl l2 (seq N (S nn-N))).
      {
        intros ? inn.
        apply in_seq.
        split.
        - now specialize (l2_lower _ inn).
        - rewrite Forall_forall in l2_upper.
          specialize (l2_upper _ inn).
          lia.
      }
      apply NoDup_app_inv2 in ndgl.
      destruct (incl_NoDup_sublist_perm ndgl incl1)
        as [l2' [perm2 subl2]].
      rewrite perm2.

      apply (Rle_trans _ (list_sum (map Rabs (map f l2')))).
      {
        apply list_sum_Rabs_triangle.
      } 

      destruct l2.
      {
        apply Permutation_nil in perm2.
        subst; simpl.
        lra.
      } 
      
      eapply (Rle_trans _ (list_sum (map Rabs (map f (seq N (S nn - N)))))).
      { 
        eapply list_sum_pos_sublist_le.
        - intros.
          apply in_map_iff in H.
          destruct H as [?[??]]; subst.
          apply Rabs_pos.
        - now do 2 apply sublist_map.
      }

      assert (Nltnn:(N <= nn)%nat).
      {
        unfold nn.
        simpl.
        transitivity n.
        - simpl in *.
          specialize (l2_lower n).
          cut_to l2_lower; [| eauto].
          lia.
        - apply Nat.le_max_l.
      } 

      rewrite map_map.
      specialize (N2_lt nn (max N1 N2))%nat.
      cut_to N2_lt.
      - unfold R_dist in N2_lt.
        repeat rewrite sum_f_R0_sum_f_R0' in N2_lt.
        repeat rewrite sum_f_R0'_list_sum in N2_lt.
        replace (S nn) with (N + (S nn - N))%nat in N2_lt.
        + rewrite seq_app, map_app, list_sum_cat in N2_lt.
          replace (S (N - 1)) with N in N2_lt by lia.
          rewrite Rplus_minus_cancel1 in N2_lt.
          rewrite plus_O_n in N2_lt.
          rewrite Rabs_pos_eq in N2_lt.
          * lra.
          * apply list_sum_pos_pos'.
            rewrite Forall_forall; intros.
            apply in_map_iff in H.
            destruct H as [?[??]]; subst.
            apply Rabs_pos.
        + apply le_plus_minus_r.
          lia.
      - red.
        transitivity N; lia.
      - lia.
    Qed.
    
(*
    Lemma Lim_seq_perm (f:nat -> R) (g:nat->nat):
      Bijective g ->
      ex_finite_lim_seq f ->
      Lim_seq f =
      Lim_seq (fun n => f (g n)).
    Proof.
      intros.
      unfold Lim_seq.
      
    Qed.
 *)
    
    Lemma Lim_seq_sum_pair (f:nat -> nat -> R) :
      (forall i j, 0 <= f i j) ->
      (forall i, ex_finite_lim_seq (sum_f_R0 (fun j => f i j))) ->
      (forall j, ex_finite_lim_seq (sum_f_R0 (fun i => f i j))) ->
      Lim_seq (sum_f_R0 (fun n1 => Lim_seq (sum_f_R0 (fun n2 : nat => f n1 n2)))) =
      Lim_seq (sum_f_R0 (fun n => let '(a,b) := iso_f n in f a b)).
    Proof.
      intros.
    Admitted.

(*    Lemma infinite_sum'_pair_merge (f:nat -> nat -> R) l :
      infinite_sum' (fun n1 => Lim_seq (sum_f_R0 (fun n2 : nat => f n1 n2))) l ->
      infinite_sum' (fun n => let '(a,b) := iso_f n in f a b) l.
    Proof.
      intros.

    Qed.
*)

    Lemma infinite_sum'_pair_merge (f:nat -> nat -> R) l :
      (forall i j, 0 <= f i j) ->
      (forall i, ex_finite_lim_seq (sum_f_R0 (fun j => f i j))) ->
      (forall j, ex_finite_lim_seq (sum_f_R0 (fun i => f i j))) ->
      infinite_sum' (fun n1 => Lim_seq (sum_f_R0 (fun n2 : nat => f n1 n2))) l ->
      infinite_sum' (fun n => let '(a,b) := iso_f n in f a b) l.
    Proof.
      intros.
    Admitted.

    Lemma infinite_sum'_pair_split (f:nat -> nat -> R) l :
      (forall i j, 0 <= f i j) ->
      (forall i, ex_finite_lim_seq (sum_f_R0 (fun j => f i j))) ->
      (forall j, ex_finite_lim_seq (sum_f_R0 (fun i => f i j))) ->
      infinite_sum' (fun n => let '(a,b) := iso_f n in f a b) l ->
      infinite_sum' (fun n1 => Lim_seq (sum_f_R0 (fun n2 : nat => f n1 n2))) l.
    Proof.
      intros.
    Admitted.

    (*
    Lemma Lim_seq_sum_swap f  l:
      (forall i j, 0 <= f i j) ->
      (forall i, ex_finite_lim_seq (sum_f_R0 (fun j => f i j))) ->
      (forall j, ex_finite_lim_seq (sum_f_R0 (fun i => f i j))) ->
      infinite_sum' 
                 (fun n1 =>
                    Lim_seq
                      (sum_f_R0 (fun n2 => f n1 n2))) l ->
      infinite_sum' 
                 (fun n2 =>
                    Lim_seq
                      (sum_f_R0 (fun n1 => f n1 n2))) l.
    Proof.
      intros.
      generalize (infinite_sum'_pair_merge f l)
      ; intros HH.
      cut_to HH; trivial.
      apply infinite_sum'_pair_split; trivial.

      apply (infinite_sum'_perm (fun n =>
                                        iso_b (snd (iso_f n), fst (iso_f n))))
        in HH.
      - erewrite infinite_sum'_ext; try eapply HH.
        intros.
        cbv beta.
        destruct (iso_f x).
        now rewrite iso_f_b; simpl.
      - exists (fun n => iso_b (snd (iso_f n), fst (iso_f n))).
        erewrite infinite_sum'_ext; try eapply HH.
        intros.
        cbv beta.
        destruct (iso_f x); simpl.
        now rewrite Rabs_pos_eq.
    Qed.
*)

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
      repeat rewrite Lim_seq_sum_pair; trivial.
      assert (ex_lim_seq  (sum_f_R0 (fun n : nat => let '(a, b) := iso_f n in f a b))).
    Admitted.

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
    rewrite <- infinite_sum_infinite_sum'.
    rewrite <- infinite_sum_is_lim_seq.
  Admitted.

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

