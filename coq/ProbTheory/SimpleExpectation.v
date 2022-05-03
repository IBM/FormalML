Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Import NumberIso.
Require Export RealRandomVariable.
Require Import SigmaAlgebras Almost.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section SimpleExpectation_sec.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Local Open Scope prob.

  Definition FiniteRangeFunction_partition_image 
             {rv_X : Ts -> R}
             {rrv : RandomVariable dom borel_sa rv_X}
             (frf : FiniteRangeFunction rv_X) : list (event dom) :=
    map (preimage_singleton rv_X) frf_vals.
  
  Definition SimpleExpectation
             (rv_X : Ts -> R)
             {rv:RandomVariable dom borel_sa rv_X}
             {frf : FiniteRangeFunction rv_X} : R :=
    list_sum (map (fun v => Rmult v (ps_P (preimage_singleton rv_X v)))
                  (nodup Req_EM_T frf_vals)).

  
  Lemma frf_nodup_preimage_list_union
        {Td}
        {cod:SigmaAlgebra Td}
        {has_pre:HasPreimageSingleton cod}
        dec
        {rv_X : Ts -> Td}
        {rv: RandomVariable dom cod rv_X}
        (frf : FiniteRangeFunction rv_X) :
    event_equiv (list_union (map (preimage_singleton rv_X) (nodup dec frf_vals)))  Ω .
  Proof.
    intros x.
    unfold Ω.
    split; trivial; intros _.
    unfold list_union.
    generalize (frf_vals_complete x); intros HH2.
    simpl; red; trivial.
    simpl.
    eexists.
    split.
    - apply in_map.
      apply nodup_In.
      apply frf_vals_complete.
    - reflexivity.
  Qed.
  
  Lemma event_disjoint_preimage_disj
        {Td}
        {cod:SigmaAlgebra Td}
        {has_pre:HasPreimageSingleton cod}
        (f:Ts->Td) l
        {rv: RandomVariable dom cod f}
    :
      NoDup l ->
      ForallOrdPairs event_disjoint (map (preimage_singleton f) l).
  Proof.
    induction l; simpl; intros nd.
    - constructor.
    - invcs nd.
      constructor; auto.
      rewrite Forall_map.
      rewrite Forall_forall.
      intros x xin e ein.
      congruence.
  Qed.

  Lemma SimplePosExpectation_zero_pos_0helper (x : Ts -> R) {rv:RandomVariable dom borel_sa x} l :
    ~ In 0 l ->
    Forall (fun x : R => x = 0)
           (map (fun v : R => v * ps_P (preimage_singleton x v)) l) ->
    
    fold_right Rplus 0 (map ps_P (map (preimage_singleton x) l)) = 0.
  Proof.
    induction l; simpl; intros inn Fl; trivial.
    invcs Fl.
    rewrite IHl; try tauto.
    destruct (Rmult_integral _ _ H1).
    - tauto.
    - lra.
  Qed.

  Lemma SimplePosExpectation_zero_pos
        (x : Ts -> R)
        {rv : RandomVariable dom borel_sa x}
        {pofrf :NonnegativeFunction x} 
        {frf : FiniteRangeFunction x} :
    SimpleExpectation x = 0 ->
    ps_P (preimage_singleton x 0) = 1.
  Proof.
    intros.
    unfold SimpleExpectation in H.
    apply list_sum_all_pos_zero_all_zero in H.
    - generalize (event_disjoint_preimage_disj x (nodup Req_EM_T frf_vals) (NoDup_nodup _ _))
      ; intros HH1.
      generalize (frf_nodup_preimage_list_union Req_EM_T frf)
      ; intros HH2.
      generalize (ps_list_disjoint_union Prts _ HH1)
      ; intros HH3.
      rewrite HH2 in HH3.
      rewrite ps_one in HH3.
      clear HH1 HH2.
      assert (nd:NoDup (nodup Req_EM_T frf_vals)) by (apply NoDup_nodup).
      induction (nodup Req_EM_T frf_vals); simpl in *; [lra | ].
      invcs H.
      invcs nd.
      specialize (IHl H3).
      destruct (Rmult_integral _ _ H2).
      + subst.
        rewrite (SimplePosExpectation_zero_pos_0helper x _ H1 H3) in HH3.
        lra.
      + unfold event_preimage, event_singleton in H.
        rewrite H in HH3.
        apply IHl; trivial.
        lra.
    - rewrite Forall_map.
      apply Forall_nodup.
      rewrite Forall_forall.
      intros.
      generalize (ps_pos  (preimage_singleton x x0)); intros HH.
      destruct (classic_event_none_or_has (preimage_singleton x x0)).
      + destruct H1.
        repeat red in H1; subst.
        specialize (pofrf x1).
        apply Rle_ge.
        now apply Rmult_le_pos.
      + rewrite H1, ps_none.
        lra.
  Qed.
  

  Lemma nodup_scaled (c : R) (frf_vals : list R) :
    c <> 0 -> map (fun v : R => c * v) (nodup Req_EM_T frf_vals) =
              nodup Req_EM_T (map (fun v : R => c * v) frf_vals).
  Proof.
    intros.
    symmetry.
    apply nodup_map_inj; intros.
    apply Rmult_eq_reg_l in H2; trivial.
  Qed.
  
  Lemma scaleSimpleExpectation (c:R)
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X} : 
    (c * SimpleExpectation rv_X)%R = SimpleExpectation (rvscale c rv_X).
  Proof.
    unfold SimpleExpectation, frfscale, rvscale.
    destruct frf.
    unfold RandomVariable.frf_vals.
    simpl.
    destruct (Req_dec c 0).
    - subst.
      case_eq frf_vals.
      + simpl; lra.
      + intros.
        replace  (nodup Req_EM_T (map (fun v : R => 0 * v) (r::l))) with ([0]).
        * simpl; lra.
        * replace  (map (fun v : R => 0 * v) (r :: l)) with
              (map (fun _ : R => 0) (r :: l)).
          apply nodup_const_map.
          apply map_ext; intros.
          lra.
    - rewrite <- list_sum_const_mul.
      f_equal.
      replace (nodup Req_EM_T (map (fun v : R => c * v) frf_vals)) with
          (map (fun v : R => c * v) (nodup Req_EM_T frf_vals)).
      + rewrite map_map.
        apply map_ext; intros.
        rewrite <- Rmult_assoc.
        f_equal.
        apply ps_proper; red; intros; simpl.
        unfold pre_event_preimage, pre_event_singleton.
        split; intros.
        * now subst.
        * apply Rmult_eq_reg_l in H0; trivial.
      + now apply nodup_scaled.
  Qed.

  Lemma RefineSimpleExpectation0
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        (E : event dom) (l : list R):
    sa_sigma _ E ->
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X v)) l) = 
    list_sum
      (map (fun v : R => v * ps_P ((preimage_singleton rv_X v) ∩ E)) l)
    + 
    list_sum
      (map (fun v : R => v * ps_P ((preimage_singleton rv_X v) ∩ ¬ E)) l).
  Proof.
    intro sa_sigmaE.
    rewrite <-list_sum_map_add.
    rewrite (map_ext (fun v : R => v * ps_P (preimage_singleton rv_X v))
                     (fun t : R =>
                        t * ps_P ((preimage_singleton rv_X t) ∩ E) +
                        t * ps_P ((preimage_singleton rv_X t) ∩ ¬ E))); trivial.
    intros.
    rewrite <- Rmult_plus_distr_l.
    apply Rmult_eq_compat_l.
    apply ps_total.
    - apply event_disjoint_complement.
    - apply event_union_complement.
      now apply sa_dec.
  Qed.

  Lemma oppSimpleExpectation
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X} : 
    (- SimpleExpectation rv_X)%R = SimpleExpectation (rvopp rv_X).
  Proof.
    replace (- SimpleExpectation rv_X) with (-1 * SimpleExpectation rv_X) by lra.
    apply scaleSimpleExpectation.
  Qed.

  Lemma rvminus_equiv (f g : Ts -> R) :
    (forall (r:R),  
        (pre_event_equiv (fun omega : Ts => f omega -  g omega <= r)
                         (fun omega : Ts => rvminus f g omega <= r))).
  Proof.
    intros r x.
    unfold rvminus, rvplus, rvopp, rvscale.
    split; lra.
  Qed.

  Lemma equiv_rvminus_eq (f g : Ts -> R) :
    pre_event_equiv (fun omega => f omega = g omega)
                    (fun omega => rvminus f g omega = 0).
    unfold rvminus, rvplus, rvopp, rvscale.
    intro x.
    split; lra.
  Qed.

  Class NonEmpty (A : Type) :=
    ex : A.

  Lemma non_empty_frf_vals 
        (rv_X : Ts -> R)
        (frf : FiniteRangeFunction rv_X) :
    NonEmpty Ts -> frf_vals <> nil.
  Proof.
    intros.
    destruct frf.
    unfold RandomVariable.frf_vals.
    assert (In (rv_X ex) frf_vals) by apply frf_vals_complete.
    intuition.
    now subst.
  Qed.

  Lemma nil_frf_vals_empty_Ts
        {rv_X : Ts -> R}
        (frf : FiniteRangeFunction rv_X) :
    frf_vals = nil -> (forall (x:Ts), False).
  Proof.
    intros.
    destruct frf.
    unfold RandomVariable.frf_vals in *; subst.
    simpl in frf_vals_complete.
    now specialize (frf_vals_complete x).
  Qed.

  Lemma list_union_frf_preimage
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        (frf : FiniteRangeFunction rv_X) :
    event_equiv (list_union (map (preimage_singleton rv_X) frf_vals))  Ω .
  Proof.
    intros x.
    unfold Ω.
    split; trivial; intros _.
    - now repeat red.
    - unfold list_union.
      generalize (frf_vals_complete x); intros HH2.
      simpl.
      eexists.
      split.
      + apply in_map.
        apply frf_vals_complete.
      + reflexivity.
  Qed.    

  Lemma event_disjoint_preimage_and_disj 
        f P l
        {rv : RandomVariable dom borel_sa f} :
    NoDup l ->
    ForallOrdPairs event_disjoint (map (fun x => preimage_singleton f x ∩ P) l).
  Proof.
    induction l; simpl; intros nd.
    - constructor.
    - invcs nd.
      constructor; auto.
      rewrite Forall_map.
      rewrite Forall_forall.
      intros x xin e [??] [??].
      congruence.
  Qed.

  Lemma event_disjoint_and_preimage_disj 
        f P l
        {rv : RandomVariable dom borel_sa f} :
    NoDup l ->
    ForallOrdPairs event_disjoint (map (fun x => P ∩ preimage_singleton f x)  l).
  Proof.
    induction l; simpl; intros nd.
    - constructor.
    - invcs nd.
      constructor; auto.
      rewrite Forall_map.
      rewrite Forall_forall.
      intros x xin e [??] [??].
      congruence.
  Qed.
  
  Lemma event_disjoint_preimage_disj_pairs
        f1 f2 l
        {rv1 : RandomVariable dom borel_sa f1} 
        {rv2 : RandomVariable dom borel_sa f2} :
    NoDup l ->
    ForallOrdPairs event_disjoint 
                   (map (fun (x : R*R) => (preimage_singleton f1 (fst x) ∩ preimage_singleton f2 (snd x))) l).
  Proof.
    induction l; simpl; intros nd.
    - constructor.
    - invcs nd.
      constructor; auto.
      rewrite Forall_map.
      rewrite Forall_forall.
      intros [??] xin e ein.
      simpl in *.
      destruct a.
      destruct ein.
      intros [??].
      unfold pre_event_preimage, pre_event_singleton in *.
      simpl in *.
      congruence.
  Qed.

  Lemma frf_vals_nodup_preimage_disj
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X} :
    ForallOrdPairs event_disjoint (map (preimage_singleton rv_X) (nodup Req_EM_T frf_vals)).
  Proof.
    intros.
    apply event_disjoint_preimage_disj.
    apply NoDup_nodup.
  Qed.
  
  Lemma frf_vals_prob_1 
        (rv_X : Ts -> R)
        {rv: RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X} :
    list_sum (map (fun x : R => ps_P (preimage_singleton rv_X x)) 
                  (nodup Req_EM_T frf_vals)) = 1.
  Proof.
    transitivity (list_sum (map ps_P (map (preimage_singleton rv_X) 
                                          (nodup Req_EM_T frf_vals)))).
    { now rewrite map_map. }

    generalize (ps_list_disjoint_union Prts
                                       (map (preimage_singleton rv_X) (nodup Req_EM_T frf_vals)))
    ; intros HH.
    rewrite list_sum_fold_right.
    rewrite <- HH; clear HH.
    - rewrite frf_nodup_preimage_list_union.
      apply ps_one.
    - apply frf_vals_nodup_preimage_disj.
  Qed.

  Lemma simple_random_all
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X} :
    event_equiv (list_union (map (preimage_singleton rv_X) frf_vals))
                Ω .   
  Proof.
    unfold  Ω, list_union, event_equiv.
    intros.
    destruct frf.
    split; intros.
    - now repeat red.
    - eexists.
      split; trivial.
      apply in_map_iff.
      now exists (rv_X x).
                 now simpl.
  Qed.

  Lemma prob_inter_all1
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}                               
        (frf1 : FiniteRangeFunction rv_X1) 
        (frf2 : FiniteRangeFunction rv_X2)
        (a:R) :
    NoDup (frf_vals (FiniteRangeFunction := frf2)) ->
    ps_P (preimage_singleton rv_X1 a) =
    list_sum
      (map (fun x : R => ps_P (preimage_singleton rv_X1 a ∩ preimage_singleton rv_X2 x)) 
           (frf_vals (FiniteRangeFunction:=frf2))).
  Proof.
    intros.
    rewrite list_sum_fold_right.
    rewrite <- map_map.
    rewrite <- ps_list_disjoint_union.
    - replace (map (fun x => preimage_singleton rv_X1 a ∩ preimage_singleton rv_X2 x) frf_vals)
        with (map (event_inter (preimage_singleton rv_X1 a))
                  (map (preimage_singleton rv_X2) 
                       frf_vals)).
      + rewrite <- event_inter_list_union_distr.
        rewrite simple_random_all.
        now rewrite event_inter_true_r.
      + unfold event_inter.
        now rewrite map_map.
    - now apply event_disjoint_and_preimage_disj.
  Qed.
  
  Lemma prob_inter_all2
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}                               
        (frf1 : FiniteRangeFunction rv_X1) 
        (frf2 : FiniteRangeFunction rv_X2)
        (a:R) :
    NoDup (frf_vals (FiniteRangeFunction := frf1)) ->
    ps_P (preimage_singleton rv_X2 a) =
    list_sum
      (map (fun x : R => ps_P (preimage_singleton rv_X1 x ∩ preimage_singleton rv_X2 a)) 
           (frf_vals (FiniteRangeFunction:=frf1))).
  Proof.
    intros.
    rewrite (prob_inter_all1 frf2 frf1 a H); intros.
    f_equal.
    apply map_ext; intros.
    apply ps_proper.
    now rewrite event_inter_comm.
  Qed.

  Lemma RefineEvent
        (E : event dom) (lE : list (event dom)):
    event_equiv (list_union lE) Ω ->
    event_equiv E (list_union (map (event_inter E) lE)).
  Proof.
    intros.
    rewrite <- event_inter_list_union_distr.
    rewrite H.
    now rewrite event_inter_true_r.
  Qed.

  Lemma RefineSimpleExpectation
        {rv_X rv_X2 : Ts -> R}
        {rv: RandomVariable dom borel_sa rv_X}
        {rv2: RandomVariable dom borel_sa rv_X2}                               
        (frf : FiniteRangeFunction rv_X)
        (frf2 : FiniteRangeFunction rv_X2) :  
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X v))
           (nodup Req_EM_T (frf_vals (FiniteRangeFunction:=frf)))) = 
    list_sum
      (map (fun vv : R*R => 
              (fst vv) * ps_P ((preimage_singleton rv_X (fst vv)) ∩ (preimage_singleton rv_X2 (snd vv))))
           (list_prod (nodup Req_EM_T (frf_vals (FiniteRangeFunction:=frf)))
                      (nodup Req_EM_T (frf_vals (FiniteRangeFunction:=frf2))))).
  Proof.
    induction (nodup Req_EM_T (@frf_vals Ts R rv_X frf)); simpl; trivial.
    rewrite IHl.
    rewrite map_app.
    rewrite list_sum_cat.
    f_equal.
    rewrite map_map.
    simpl.
    transitivity (list_sum (List.map (fun z => a*z)
                                     (map (fun x : R => ps_P ((preimage_singleton rv_X a) ∩ (preimage_singleton rv_X2 x))) (nodup Req_EM_T (frf_vals (FiniteRangeFunction:=frf2)))))).
    - rewrite list_sum_mult_const.
      f_equal.
      rewrite map_map.
      apply (prob_inter_all1 (nodup_simple_random_variable Req_EM_T frf) (nodup_simple_random_variable Req_EM_T frf2) a); simpl; try apply NoDup_nodup.
    - now rewrite map_map.
  Qed.

  Lemma zero_prob_or_witness (E : event dom) :
    ps_P E <> 0 -> exists (x:Ts), E x.
  Proof.
    intros.
    apply NNPP.
    intro x.
    apply H.
    cut (event_equiv E event_none).
    - intros HH.
      rewrite HH.
      apply ps_none.
    - intros e.
      unfold event_none, pre_event_none; simpl; intuition.
      eauto.
  Qed.

  Lemma SimpleExpectation_le 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}                               
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} : 
    rv_le rv_X1 rv_X2 ->
    SimpleExpectation rv_X1 <= SimpleExpectation rv_X2.
  Proof.
    unfold rv_le, SimpleExpectation.
    intros.
    unfold event_preimage, event_singleton.
    rewrite (RefineSimpleExpectation  frf1 frf2).
    rewrite (RefineSimpleExpectation  frf2 frf1).
    generalize (@sa_sigma_inter_pts _ _ rv_X1 rv_X2 rv1 rv2); intros sa_sigma.
    destruct frf1; destruct frf2.
    unfold RandomVariable.frf_vals in *.
    replace 
      (list_sum (map
                   (fun vv : R * R =>
                      fst vv * ps_P (preimage_singleton rv_X2 (fst vv) ∩ preimage_singleton rv_X1 (snd vv)))
                   (list_prod (nodup Req_EM_T frf_vals0) (nodup Req_EM_T frf_vals)))) with
        (list_sum (map
                     (fun vv : R * R =>
                        snd vv * ps_P (preimage_singleton rv_X1 (fst vv) ∩ preimage_singleton rv_X2 (snd vv)))
                     (list_prod (nodup Req_EM_T frf_vals) (nodup Req_EM_T frf_vals0)))).
    - apply list_sum_le; intros.
      assert (ps_P (preimage_singleton rv_X1 (fst a) ∩ preimage_singleton rv_X2 (snd a)) = 0 \/
              fst a <= snd a).
      + destruct (Req_EM_T (ps_P (preimage_singleton rv_X1 (fst a) ∩ preimage_singleton rv_X2 (snd a))) 0).
        * intuition.
        * right.
          apply zero_prob_or_witness in n.
          destruct n as [?[??]].
          rewrite <- H0; rewrite <- H1.
          apply H.
      + destruct H0.
        * rewrite H0; lra.
        * apply Rmult_le_compat_r; trivial.
          apply ps_pos.
    - apply list_sum_Proper.
      rewrite Permutation_map'; [| apply list_prod_swap].
      rewrite map_map.
      apply Permutation_refl'.
      apply map_ext; intros [??]; simpl.
      now rewrite event_inter_comm.
  Qed.

  Lemma sumSimpleExpectation00
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        (frf1 : FiniteRangeFunction rv_X1) 
        (frf2 : FiniteRangeFunction rv_X2) :
    NoDup (frf_vals (FiniteRangeFunction := frf1)) ->
    NoDup (frf_vals (FiniteRangeFunction := frf2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X1 v))
           (frf_vals (FiniteRangeFunction := frf1))) =
    list_sum
      (map
         (fun v : R * R =>
            (fst v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (frf_vals (FiniteRangeFunction := frf1))
                    (frf_vals (FiniteRangeFunction := frf2)))).
  Proof.
    intros.
    induction (frf_vals (FiniteRangeFunction := frf1)).
    - now simpl.
    - simpl.
      invcs H.
      rewrite IHl by trivial.
      rewrite map_app.
      rewrite list_sum_cat.
      f_equal.
      rewrite map_map.
      unfold fst, snd.
      rewrite list_sum_const_mul.
      now rewrite (prob_inter_all1 frf1 frf2 a).
  Qed.

  Lemma sumSimpleExpectation11
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}         
        (frf1 : FiniteRangeFunction rv_X1) 
        (frf2 : FiniteRangeFunction rv_X2) :
    NoDup (frf_vals (FiniteRangeFunction := frf1)) ->
    NoDup (frf_vals (FiniteRangeFunction := frf2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X2 v))
           (frf_vals (FiniteRangeFunction := frf2))) =
    list_sum
      (map
         (fun v : R * R =>
            (snd v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (frf_vals (FiniteRangeFunction := frf1))
                    (frf_vals (FiniteRangeFunction := frf2)))).
  Proof.
    intros.
    induction (frf_vals (FiniteRangeFunction := frf2)).
    - rewrite list_prod_nil_r.
      now simpl.
    - rewrite (Permutation_map' _ (list_prod_swap _ _)).
      simpl.
      rewrite map_map, map_app; simpl.
      rewrite (Permutation_map' _ (list_prod_swap _ _)).
      rewrite map_map; simpl.
      invcs H0.
      rewrite IHl by trivial.
      repeat rewrite map_map.
      simpl.
      rewrite list_sum_cat.
      f_equal.
      rewrite list_sum_const_mul.
      now rewrite (prob_inter_all2 frf1 frf2 a).
  Qed.
  
  Lemma sumSimpleExpectation0
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}         
        (frf1 : FiniteRangeFunction rv_X1) 
        (frf2 : FiniteRangeFunction rv_X2) :
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X1 v))
           (nodup Req_EM_T (frf_vals (FiniteRangeFunction := frf1)))) =
    list_sum
      (map
         (fun v : R * R =>
            (fst v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (nodup Req_EM_T (frf_vals (FiniteRangeFunction := frf1))) 
                    (nodup Req_EM_T (frf_vals (FiniteRangeFunction := frf2))))).
  Proof.
    intros.
    apply (sumSimpleExpectation00 (nodup_simple_random_variable Req_EM_T frf1) (nodup_simple_random_variable Req_EM_T frf2)); simpl; try apply NoDup_nodup.
  Qed.

  Lemma sumSimpleExpectation1
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}         
        (frf1 : FiniteRangeFunction rv_X1) 
        (frf2 : FiniteRangeFunction rv_X2) :
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X2 v))
           (nodup Req_EM_T (frf_vals (FiniteRangeFunction := frf2)))) =
    list_sum
      (map
         (fun v : R * R =>
            (snd v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (nodup Req_EM_T (frf_vals (FiniteRangeFunction := frf1))) 
                    (nodup Req_EM_T (frf_vals (FiniteRangeFunction := frf2))))).
  Proof.
    intros.
    apply (sumSimpleExpectation11 (nodup_simple_random_variable Req_EM_T frf1) (nodup_simple_random_variable Req_EM_T frf2)); simpl; try apply NoDup_nodup.
  Qed.

  Definition sums_same (x y:R*R) := fst x + snd x = fst y + snd y.

  Instance sums_same_equiv : Equivalence sums_same.
  Proof.
    unfold sums_same.
    constructor; red.
    - intros [??]; simpl; trivial.
    - intros [??][??]; simpl; congruence.
    - intros [??][??][??]; simpl.
      congruence.
  Qed.
  
  Instance sums_same_dec : EqDec (R*R) sums_same.
  Proof.
    intros [??] [??].
    apply Req_EM_T.
  Defined.

  Lemma preimage_points_disjoint
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        (c d: R) :
    c <> d ->
    event_disjoint (preimage_singleton rv_X c)
                   (preimage_singleton rv_X d).
  Proof.
    unfold event_disjoint.
    congruence.
  Qed.

  Lemma preimage_point_pairs_disjoint
        (rv_X1 rv_X2: Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        (c1 c2 d1 d2: R) :
    (c1 <> d1) \/ (c2 <> d2) ->
    event_disjoint (event_inter (preimage_singleton rv_X1 c1)
                                (preimage_singleton rv_X2 c2))
                   (event_inter (preimage_singleton rv_X1 d1)
                                (preimage_singleton rv_X2 d2)).
  Proof.
    intros.
    unfold event_disjoint, pre_event_disjoint, event_inter, pre_event_inter; simpl; intros.
    destruct H0; destruct H1.
    destruct H; congruence.
  Qed.

  Lemma quotient_bucket_NoDup {A:Type} (R:A->A->Prop) {eqR:Equivalence R} {decR:EqDec A R} l :
    NoDup l ->
    Forall (@NoDup A) (quotient R l).
  Proof.
    intros nd.
    assert (nd2:NoDup (concat (quotient R l))).
    - now rewrite unquotient_quotient.
    - now apply concat_NoDup in nd2.
  Qed.

  Lemma list_union_sub_cover (l : list (event dom)) (P Q: event dom) :
    event_union (list_union l) Q = Ω ->
    event_disjoint P Q ->
    (forall (e:event dom), In e l -> event_inter P e = e ) ->
    event_equiv (list_union l) P.
  Proof.
    intros.
    generalize (event_inter_true_l P); intros.
    rewrite <- H2.
    rewrite <- H.
    rewrite event_inter_comm.
    rewrite event_inter_union_distr.
    rewrite event_disjoint_inter in H0.
    rewrite H0.
    rewrite event_union_false_r.
    rewrite event_inter_list_union_distr.
    replace (map (event_inter P) l) with l.
    - now unfold event_equiv.
    - rewrite map_ext_in with (g:= fun p => p).
      now rewrite map_id.
      intros.
      apply H1, H3.
  Qed.

  Lemma sumSimpleExpectation
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        {frf1 : FiniteRangeFunction rv_X1} 
        {frf2 : FiniteRangeFunction rv_X2} :
    (SimpleExpectation rv_X1) + (SimpleExpectation rv_X2)%R =
    SimpleExpectation (rvplus rv_X1 rv_X2).
  Proof.
    unfold SimpleExpectation; intros.
    generalize (sumSimpleExpectation0 frf1 frf2); intros.
    generalize (sumSimpleExpectation1 frf1 frf2); intros.   
    generalize (@sa_sigma_inter_pts _ _ rv_X1 rv_X2). intro sa_sigma.
    destruct frf1.
    destruct frf2.
    unfold RandomVariable.frf_vals in *; intros.
    unfold frfplus.
    simpl.
    unfold event_singleton, event_preimage.
    transitivity (list_sum
                    (map (fun v : R*R => (fst v + snd v) * ps_P
                                                          (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
                         (list_prod (nodup Req_EM_T frf_vals) (nodup Req_EM_T frf_vals0)))).
    - rewrite H.
      rewrite H0.
      rewrite <-list_sum_map_add.
      f_equal.
      apply map_ext.
      intros.
      lra.
    - clear H H0.
      assert (HH:forall x y : R * R, {x = y} + {x <> y})
        by apply (pair_eqdec (H:=Req_EM_T) (H0:=Req_EM_T)).
      
      transitivity (list_sum
                      (map
                         (fun v : R * R => (fst v + snd v) * ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
                         (nodup HH (list_prod frf_vals frf_vals0)))).
      + f_equal.
        f_equal.
        symmetry.
        apply list_prod_nodup.
      + transitivity (list_sum
                        (map (fun v : R => v * ps_P (preimage_singleton (rvplus rv_X1 rv_X2) v))
                             (nodup Req_EM_T (map (fun ab : R * R => fst ab + snd ab) (nodup HH (list_prod frf_vals frf_vals0)))))).
        * generalize (NoDup_nodup HH (list_prod frf_vals frf_vals0)).
          assert (Hcomplete:forall x y, In (rv_X1 x, rv_X2 y) (nodup HH (list_prod frf_vals frf_vals0))).
          { intros.
            apply nodup_In.
            apply in_prod; eauto.
          }
          revert Hcomplete.
          generalize (nodup HH (list_prod frf_vals frf_vals0)). (* clear. *)
          intros.
          transitivity (list_sum
                          (map
                             (fun v : R * R => (fst v + snd v) * ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
                             (concat (quotient sums_same l)))).
          { apply list_sum_Proper. apply Permutation.Permutation_map. symmetry. apply unquotient_quotient.
          } 
          rewrite concat_map.
          rewrite list_sum_map_concat.
          rewrite map_map.

          transitivity (
              list_sum
                (map (fun v : R => v * ps_P (preimage_singleton (rvplus rv_X1 rv_X2) v))
                     (map (fun ab : R * R => fst ab + snd ab) (map (hd (0,0)) (quotient sums_same l))))).
          -- repeat rewrite map_map; simpl.
             f_equal.
             apply map_ext_in; intros.
             generalize (quotient_nnil sums_same l).
             generalize (quotient_all_equivs sums_same l).
             generalize (quotient_all_different sums_same l).
             unfold all_equivs, all_different.
             repeat rewrite Forall_forall.
             intros Hdiff Hequiv Hnnil.
             specialize (Hnnil _ H0).
             specialize (Hequiv _ H0).
             
             unfold is_equiv_class, ForallPairs in Hequiv.
             destruct a; simpl in *; [congruence | ]; clear Hnnil.
             transitivity ((fst p + snd p) * ps_P (preimage_singleton rv_X1 (fst p) ∩ preimage_singleton rv_X2 (snd p))  +
                           list_sum
                             (map
                                (fun v : R * R => (fst p + snd p) * ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
                                a)).
             ++ f_equal.
                f_equal.
                apply map_ext_in; intros.
                f_equal.
                apply Hequiv; auto.
             ++ rewrite list_sum_const_mul.
                simpl.
                rewrite <- Rmult_plus_distr_l.
                f_equal.
                transitivity (
                    list_sum (map (fun x : R * R => ps_P (preimage_singleton rv_X1 (fst x) ∩ preimage_singleton rv_X2 (snd x))) (p::a))); [reflexivity |].
                rewrite list_sum_fold_right.
                rewrite <- map_map.
                rewrite <- ps_list_disjoint_union.
                ** apply ps_proper; intros x.
                   unfold preimage_singleton, pre_event_preimage, event_inter, pre_event_inter, pre_event_singleton, rvplus; simpl.
                   split.
                   --- intros [e [ein ex]].
                       destruct ein as [?|ein].
                       +++ subst; simpl in *.
                           destruct ex.
                           congruence.
                       +++ apply in_map_iff in ein.
                           destruct ein as [ee [? eein]]; subst.
                           destruct ex as [ex1 ex2].
                           rewrite ex1, ex2.
                           apply Hequiv; eauto.
                   --- intros.
                       assert (Hin:In (rv_X1 x, rv_X2 x) l) by apply Hcomplete.
                       destruct (quotient_in sums_same _ _ Hin) as [xx [xxin inxx]].
                       generalize (all_different_same_eq sums_same (quotient sums_same l) xx (p::a) (rv_X1 x, rv_X2 x) (fst p, snd p)); simpl; trivial; intros.
                       rewrite H2 in inxx; trivial
                       ; destruct p; simpl; eauto.
                       destruct inxx.
                       +++ eexists.
                           split; [left; reflexivity | ]; simpl.
                           invcs H3; tauto.
                       +++ eexists.
                           split.
                           *** right.
                               apply in_map.
                               apply H3.
                           *** simpl.
                               tauto.
                ** apply event_disjoint_preimage_disj_pairs.
                   generalize (quotient_bucket_NoDup sums_same l H); rewrite Forall_forall; eauto.
          -- apply list_sum_Proper.
             apply Permutation_map.
             rewrite <- (nodup_hd_quotient Req_EM_T 0).
             rewrite quotient_map.
             match goal with
             | [|- Permutation ?l1 ?l2 ] => replace l1 with l2; [reflexivity | ]
             end.
             simpl.
             repeat rewrite map_map.
             erewrite quotient_ext.
             ++ eapply map_ext_in.
                simpl; intros.
                destruct a; simpl; lra.
             ++ unfold sums_same; red; simpl; intros; intuition.
        * now rewrite nodup_map_nodup.
  Qed.

  Lemma not_in_frf_vals_event_none
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf:FiniteRangeFunction rv_X} :
    forall (x:R), ~ (In x frf_vals) ->
             event_equiv (preimage_singleton rv_X x) event_none.
  Proof.
    destruct frf.
    unfold RandomVariable.frf_vals.
    repeat red; intros.
    unfold preimage_singleton, pre_event_singleton, pre_event_preimage; simpl.
    unfold pre_event_none.
    split; intros; subst; intuition.
  Qed.

  Lemma SimpleExpectation_simpl_incl 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        (frf:FiniteRangeFunction rv_X)
        (l:list R)
        (lincl : incl frf_vals l) :
    SimpleExpectation rv_X (frf:=frf) = SimpleExpectation rv_X (frf:=(FiniteRangeFunction_enlarged frf l lincl)).
  Proof.
    unfold SimpleExpectation; simpl.
    unfold event_preimage, event_singleton.
    generalize (incl_front_perm_nodup _ l frf_vals lincl); intros HH.
    
    destruct HH as [l2 HH].
    rewrite (list_sum_perm_eq 
               (map (fun v : R => v * ps_P (preimage_singleton rv_X v)) (nodup Req_EM_T l))
               (map (fun v : R => v * ps_P (preimage_singleton rv_X v)) ((nodup Req_EM_T frf_vals) ++ (nodup Req_EM_T l2 )))).
    - rewrite map_app.
      rewrite list_sum_cat.
      replace (list_sum
                 (map (fun v : R => v * ps_P (preimage_singleton rv_X v))
                      (nodup Req_EM_T frf_vals))) with 
          ((list_sum
              (map (fun v : R => v * ps_P (preimage_singleton rv_X v))
                   (nodup Req_EM_T frf_vals))) + 0) at 1 by lra.
      f_equal.
      rewrite <- (list_sum_map_zero (nodup Req_EM_T l2)).
      f_equal.
      apply map_ext_in; intros.
      rewrite (not_in_frf_vals_event_none rv_X).
      + rewrite ps_none.
        lra.
      + generalize (NoDup_perm_disj _ _ _ HH); intros HH2.
        cut_to HH2; [| apply NoDup_nodup].
        intros inn2.
        apply (HH2 a).
        * now apply nodup_In.
        * now apply nodup_In in H.
    - apply Permutation_map.
      rewrite HH.
      apply Permutation_app; try reflexivity.
      rewrite nodup_fixed_point; try reflexivity.
      eapply NoDup_app_inv2.
      rewrite <- HH.
      apply NoDup_nodup.
  Qed.
  
  Lemma SimpleExpectation_rv_irrel 
        {rv_X : Ts -> R}
        (rv1 : RandomVariable dom borel_sa rv_X)
        (rv2 : RandomVariable dom borel_sa rv_X)
        {frf:FiniteRangeFunction rv_X} :
    SimpleExpectation rv_X (rv:=rv1) = SimpleExpectation rv_X (rv:=rv2).
  Proof.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext; intros.
    f_equal.
    apply ps_proper.
    unfold preimage_singleton; intros ?; simpl.
    reflexivity.
  Qed.
  
  Lemma SimpleExpectation_pf_irrel 
        {rv_X : Ts -> R}
        {rv1 : RandomVariable dom borel_sa rv_X}
        {rv2 : RandomVariable dom borel_sa rv_X}
        (frf1 frf2:FiniteRangeFunction rv_X):
    SimpleExpectation rv_X (rv:=rv1) (frf:=frf1) = SimpleExpectation rv_X (rv:=rv2) (frf:=frf2).
  Proof.
    rewrite (SimpleExpectation_rv_irrel rv1 rv2).
    assert (lincl1:incl (frf_vals (FiniteRangeFunction:=frf1)) (frf_vals (FiniteRangeFunction:=frf1)++(frf_vals (FiniteRangeFunction:=frf2)))).
    { apply incl_appl.
      reflexivity.
    }
    assert (lincl2:incl (frf_vals (FiniteRangeFunction:=frf2)) (frf_vals (FiniteRangeFunction:=frf1)++(frf_vals (FiniteRangeFunction:=frf2)))).
    { apply incl_appr.
      reflexivity.
    }
    rewrite (SimpleExpectation_simpl_incl _ _ lincl1).
    rewrite (SimpleExpectation_simpl_incl _ _ lincl2).
    trivial.
  Qed.

  
  Lemma sumSimpleExpectation'
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        {frf1 : FiniteRangeFunction rv_X1} 
        {frf2 : FiniteRangeFunction rv_X2}
        {rv': RandomVariable dom borel_sa (rvplus rv_X1 rv_X2)}
        {frf' : FiniteRangeFunction (rvplus rv_X1 rv_X2)} :
    SimpleExpectation (rv:=rv') (frf:=frf') (rvplus rv_X1 rv_X2) =
    (SimpleExpectation rv_X1) + (SimpleExpectation rv_X2)%R.
  Proof.
    rewrite sumSimpleExpectation.
    apply SimpleExpectation_pf_irrel.
  Qed.


  Lemma SimplePosExpectation_pos_zero x
        {rvx:RandomVariable dom borel_sa x} 
        {xfrf:FiniteRangeFunction x} :
    almostR2 Prts eq x (const 0) ->
    SimpleExpectation x = 0.
  Proof.
    intros eqq.
    unfold SimpleExpectation.
    apply list_sum0_is0.
    apply List.Forall_forall.
    intros ? inn.
    apply in_map_iff in inn.
    destruct inn as [?[??]].
    red in eqq.
    unfold const in eqq.
    destruct (Req_EM_T x1 0).
    - subst.
      lra.
    - subst.
      apply almost_alt_eq in eqq.
      destruct eqq as [P[Pempty Pnone]].
      assert (sub:preimage_singleton x x1 ≤ P).
      {
        intros a pre; simpl.
        apply Pnone.
        vm_compute in pre.
        congruence.
      }
      generalize (ps_sub _ _ _ sub)
      ; intros PP.
      rewrite Pempty in PP.
      assert (eqq1:ps_P (preimage_singleton x x1) = 0).
      {
        generalize (ps_pos (preimage_singleton x x1)).
        lra.
      }
      rewrite eqq1.
      lra.
  Qed.

  Lemma Expectation_simple_proper_almostR2 x y
        {rvx:RandomVariable dom borel_sa x}
        {rvy:RandomVariable dom borel_sa y} 
        {xfrf:FiniteRangeFunction x}
        {yfrf:FiniteRangeFunction y} :
    almostR2 Prts eq x y ->
    SimpleExpectation x = SimpleExpectation y.
  Proof.
    intros.
    generalize (SimplePosExpectation_pos_zero (rvminus x y))
    ; intros HH.
    cut_to HH.
    - unfold rvminus in HH.
      erewrite SimpleExpectation_pf_irrel in HH.
      erewrite sumSimpleExpectation' with (frf1:=xfrf) (frf2:=frfopp) in HH; trivial.
      + unfold rvopp in HH.
        erewrite (@SimpleExpectation_pf_irrel (rvscale (-1) y)) in HH.
        erewrite <- scaleSimpleExpectation with (frf:=yfrf) in HH.
        field_simplify in HH.
        apply Rminus_diag_uniq_sym in HH.
        symmetry.
        apply HH.
    - destruct H as [P [Pa Pb]].
      exists P.
      split; trivial.
      intros.
      vm_compute.
      rewrite Pb; trivial.
      lra.
      Unshelve.
      typeclasses eauto.
      typeclasses eauto.
  Qed.
  
  Definition val_indicator (f : Ts -> R) (c : R) :=
    EventIndicator (classic_dec (fun omega => f omega = c)).

  Definition scale_val_indicator (f : Ts -> R) (c : R) :=
    rvscale c (val_indicator f c).

  Global Instance val_indicator_rv g c
         {rv:RandomVariable dom borel_sa g} :
    RandomVariable dom borel_sa (val_indicator g c).
  Proof.
    apply EventIndicator_pre_rv.
    apply sa_le_pt.
    now apply rv_measurable.
  Qed.

  Global Instance scale_val_indicator_rv g c
         {rv:RandomVariable dom borel_sa g} :
    RandomVariable dom borel_sa (scale_val_indicator g c).
  Proof.
    apply rvscale_rv.
    now apply val_indicator_rv.
  Qed.

  Definition frf_indicator (f : Ts -> R)
        {frf : FiniteRangeFunction f} :=
    (fun omega =>
       (RealAdd.list_sum (map (fun c => scale_val_indicator f c omega)
                              (nodup Req_EM_T frf_vals)))).

  Lemma frf_indicator_sum_helper f l a:
    NoDup l ->
    In (f a) l ->
    f a = 
    list_sum (map (fun c : R => scale_val_indicator f c a) l).
  Proof.
    induction l; simpl; [tauto |].
    intros nd inn.
    invcs nd.
    specialize (IHl H2).
    unfold scale_val_indicator, val_indicator, EventIndicator, rvscale in *.
    match_destr.
    - field_simplify.
      cut (list_sum
             (map
                (fun c : R =>
                   c * (if classic_dec (fun omega : Ts => f omega = c) a then 1 else 0)) l)
           = 0); [lra | ].
      rewrite <- e in H1.
      revert H1.
      clear.
      induction l; simpl; trivial.
      intros ninn.
      apply not_or_and in ninn.
      destruct ninn as [??].
      rewrite IHl by trivial.
      match_destr; lra.
    - field_simplify.
      apply IHl.
      destruct inn; trivial.
      congruence.
  Qed.

  (* Any finite range function can be viewed as a linear combination
     of EventIndicators 
   *)
  Theorem frf_indicator_sum (f : Ts -> R)
        {frf : FiniteRangeFunction f} :
    rv_eq f (frf_indicator f).
  Proof.
    intros a.
    apply frf_indicator_sum_helper.
    - apply NoDup_nodup.
    - apply nodup_In.
      apply frf_vals_complete.
  Qed.

End SimpleExpectation_sec.
Section EventRestricted.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (Prts: ProbSpace dom).

  Lemma event_restricted_SimpleExpectation P (pf1 : ps_P P = 1) pf (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f} 
        {frf : FiniteRangeFunction f} :
    @SimpleExpectation _ _ Prts f rv frf = 
    @SimpleExpectation _ _ (event_restricted_prob_space Prts P pf) 
                       (event_restricted_function P f) 
                       (Restricted_RandomVariable P f rv) _.
  Proof.
    unfold SimpleExpectation.
    f_equal.
    unfold event_restricted_function.
    unfold event_restricted_domain.
    apply map_ext.
    intros.
    apply Rmult_eq_compat_l.
    unfold event_restricted_prob_space; simpl.
    unfold cond_prob.
    rewrite pf1.
    field_simplify.
    rewrite ps_inter_r1; trivial.
    rewrite <- ps_inter_r1 with (B := P); trivial.
    eapply ps_proper.
    intros x.
    unfold event_restricted_event_lift, preimage_singleton, pre_event_singleton, pre_event_preimage, pre_event_inter; simpl.
    unfold pre_event_inter.
    split; intros HH.
    - subst.
      destruct HH.
      exists (exist _ _ H0).
      simpl.
      tauto.
    - destruct HH as [[?][??]]; subst; simpl.
      auto.
  Qed.

End EventRestricted.

Section SimpleConditionalExpectation.

  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Program Definition gen_simple_conditional_expectation_scale (P : event dom)
          (rv_X : Ts -> R)
          {rv : RandomVariable dom borel_sa rv_X}
          {frf : FiniteRangeFunction rv_X}
          (dec:forall x, {P x} + {~ P x}) :=
    rvscale (if (Req_EM_T (ps_P P) 0) then 0 else
               ((SimpleExpectation  ((rvmult rv_X (EventIndicator dec)))) / (ps_P P)))
            (EventIndicator dec).

  Instance gen_simple_conditional_expectation_scale_rv (P : event dom)
           (rv_X : Ts -> R)
           {rv : RandomVariable dom borel_sa rv_X}
           {frf : FiniteRangeFunction rv_X}
           (dec:forall x, {P x} + {~ P x}) :
    RandomVariable dom borel_sa  (gen_simple_conditional_expectation_scale P rv_X dec).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    apply rvscale_rv; now apply EventIndicator_rv.    
  Qed.

  Instance gen_simple_conditional_expectation_scale_simpl (P : event dom)
           (rv_X : Ts -> R)
           {rv : RandomVariable dom borel_sa rv_X}
           {frf : FiniteRangeFunction rv_X}
           (dec:forall x, {P x} + {~ P x}) :
    FiniteRangeFunction (gen_simple_conditional_expectation_scale P rv_X dec).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    apply frfscale; apply EventIndicator_frf.
  Defined.

  Definition with_index_simple {A} (l:list A) : list (nat*A)
    := (combine (seq 0 (length l)) l).

  Definition SimpleConditionalExpectationSA
             (rv_X : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X}
             {frf : FiniteRangeFunction rv_X}
             (l : list dec_sa_event) :=
    fold_right rvplus (const 0)
               (map
                  (fun ev => gen_simple_conditional_expectation_scale (dsa_event ev) rv_X (dsa_dec ev))
                  l).

  Instance SimpleConditionalExpectationSA_simpl
           (rv_X : Ts -> R)
           {rv : RandomVariable dom borel_sa rv_X}
           {frf : FiniteRangeFunction rv_X}
           (l : list dec_sa_event) :
    FiniteRangeFunction (SimpleConditionalExpectationSA rv_X l).
  Proof.
    unfold SimpleConditionalExpectationSA.
    induction l; simpl.
    - apply frfconst.
    - apply frfplus.
      + apply gen_simple_conditional_expectation_scale_simpl.
      + apply IHl.
  Defined.

  Global Instance gen_simple_conditional_expectation_rv 
         (rv_X : Ts -> R)
         {rv:RandomVariable dom borel_sa rv_X}
         {frf : FiniteRangeFunction rv_X}
         (l : list dec_sa_event) :
    RandomVariable dom borel_sa (SimpleConditionalExpectationSA rv_X l).
  Proof.
    unfold SimpleConditionalExpectationSA.
    induction l; simpl; typeclasses eauto.
  Qed.

  Definition simple_conditional_expectation_scale_coef (c : R)
             (rv_X rv_X2 : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X}
             {rv2 : RandomVariable dom borel_sa rv_X2}
             {frf : FiniteRangeFunction rv_X}
             {frf2 : FiniteRangeFunction rv_X2} : R :=
    if Req_EM_T (ps_P (preimage_singleton rv_X2 c)) 0 then 0 else
      ((SimpleExpectation 
          (rvmult rv_X
                  (point_preimage_indicator rv_X2 c)))
         / (ps_P (preimage_singleton rv_X2 c))).

  Definition SimpleConditionalExpectation_list
             (rv_X1 rv_X2 : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X1}
             {rv : RandomVariable dom borel_sa rv_X2}
             {frf1 : FiniteRangeFunction rv_X1}
             {frf2 : FiniteRangeFunction rv_X2}
    := map (fun c => (rvscale (simple_conditional_expectation_scale_coef c rv_X1 rv_X2)
                           (point_preimage_indicator rv_X2 c)))
           (nodup Req_EM_T (frf_vals (FiniteRangeFunction:=frf2))).

  Definition SimpleConditionalExpectation
             (rv_X1 rv_X2 : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X1}
             {rv : RandomVariable dom borel_sa rv_X2}
             {frf1 : FiniteRangeFunction rv_X1} 
             {frf2 : FiniteRangeFunction rv_X2} :=
    fold_right rvplus (const 0)
               (SimpleConditionalExpectation_list rv_X1 rv_X2).

  Lemma SimpleConditionalExpectation_list_rv  
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}                          
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} :
    Forall (RandomVariable dom borel_sa) (SimpleConditionalExpectation_list rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation_list.
    induction frf_vals; simpl.
    - constructor.
    - match_destr.
      constructor; trivial.
      typeclasses eauto.
  Defined.

  Lemma SimpleConditionalExpectation_list_simple  
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}                          
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} :
    Forallt FiniteRangeFunction (SimpleConditionalExpectation_list rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation_list.
    induction frf_vals; simpl.
    - constructor.
    - match_destr.
      constructor; trivial.
      typeclasses eauto.
  Defined.

  Instance SimpleConditionalExpectation_rv
           (rv_X1 rv_X2 : Ts -> R)
           {rv1 : RandomVariable dom borel_sa rv_X1}
           {rv2 : RandomVariable dom borel_sa rv_X2}                          
           {frf1 : FiniteRangeFunction rv_X1}
           {frf2 : FiniteRangeFunction rv_X2}
    : RandomVariable dom borel_sa (SimpleConditionalExpectation rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation; simpl.
    generalize (SimpleConditionalExpectation_list_rv rv_X1 rv_X2).
    induction (SimpleConditionalExpectation_list rv_X1 rv_X2); intros HH; simpl.
    - typeclasses eauto.
    - invcs HH.
      apply rvplus_rv; auto.
  Qed.
  
  Instance SimpleConditionalExpectation_simple
           (rv_X1 rv_X2 : Ts -> R)
           {rv1 : RandomVariable dom borel_sa rv_X1}
           {rv2 : RandomVariable dom borel_sa rv_X2}                          
           {frf1 : FiniteRangeFunction rv_X1}
           {frf2 : FiniteRangeFunction rv_X2}
    : FiniteRangeFunction (SimpleConditionalExpectation rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation; simpl.
    generalize (SimpleConditionalExpectation_list_simple rv_X1 rv_X2).
    induction (SimpleConditionalExpectation_list rv_X1 rv_X2); intros HH; simpl.
    - typeclasses eauto.
    - invcs HH.
      apply frfplus; auto.
  Qed.

  Lemma SimpleExpectation_pre_EventIndicator
        {P : pre_event Ts}
        (sa_P:sa_sigma _ P)
        (dec: forall x, {P x} + {~ P x}) :
    SimpleExpectation (EventIndicator dec)
                      (rv:=EventIndicator_pre_rv _ dec sa_P)
                      (frf:=EventIndicator_pre_frf dec)
    = ps_P (exist _ P sa_P).
  Proof.
    unfold EventIndicator_frf.
    unfold SimpleExpectation.
    unfold frf_vals.
    unfold preimage_singleton.
    unfold pre_event_preimage, pre_event_singleton.
    unfold EventIndicator.
    simpl.
    repeat match_destr; simpl; ring_simplify
    ; apply ps_proper; intros ?; simpl    
    ; match_destr; intuition.
  Qed.

  Lemma SimpleExpectation_EventIndicator 
        {P : event dom} 
        (dec: forall x, {P x} + {~ P x}) :
    SimpleExpectation (EventIndicator dec) = ps_P P.
  Proof.
    unfold EventIndicator_frf.
    unfold SimpleExpectation.
    unfold frf_vals.
    unfold preimage_singleton.
    unfold pre_event_preimage, pre_event_singleton.
    unfold EventIndicator.
    simpl.
    repeat match_destr; simpl; ring_simplify
    ; apply ps_proper; intros ?; simpl    
    ; match_destr; intuition.
  Qed.

  Definition fold_rvplus_prod_indicator
             (rv_X : Ts -> R)
             (l : list dec_sa_event) :=
    (fold_right rvplus (const 0)
                (map (fun ev => 
                        rvmult rv_X (EventIndicator (dsa_dec ev))) l)).

  Instance fold_rvplus_prod_indicator_rv
           (rv_X : Ts -> R)
           {frf : RandomVariable dom borel_sa rv_X}
           (l : list dec_sa_event) :
    RandomVariable dom borel_sa (fold_rvplus_prod_indicator rv_X l).
  Proof.
    unfold fold_rvplus_prod_indicator.
    induction l; simpl.
    - typeclasses eauto.
    - apply rvplus_rv.
      + apply rvmult_rv; trivial.
        apply EventIndicator_rv.
      + apply IHl.
  Qed.

  Instance fold_rvplus_prod_indicator_simpl
           (rv_X : Ts -> R)
           {frf : FiniteRangeFunction rv_X}
           (l : list dec_sa_event) :
    FiniteRangeFunction (fold_rvplus_prod_indicator rv_X l).
  Proof.
    unfold fold_rvplus_prod_indicator.
    induction l; simpl; typeclasses eauto.
  Defined.


  Lemma SimpleExpectation_const c frf : SimpleExpectation (const c) (frf:=frf) = c.
  Proof.
    rewrite (SimpleExpectation_pf_irrel _ (frfconst c)).
    unfold SimpleExpectation; simpl.
    unfold preimage_singleton, pre_event_preimage, pre_event_singleton, const.
    erewrite ps_proper.
    - erewrite ps_one.
      lra.
    - unfold Ω, pre_Ω.
      repeat red; intros; simpl; intuition.
  Qed.
  

  Lemma SimpleExpectation_nneg (f : Ts -> R)
        {frf: FiniteRangeFunction f}
        {rvf : RandomVariable dom borel_sa f} :
    NonnegativeFunction f ->
    0 <= SimpleExpectation f.
  Proof.
    intros.
    replace (0) with (SimpleExpectation (const 0)).
    - apply SimpleExpectation_le.
      apply H.
    - apply SimpleExpectation_const.
  Qed.


  Lemma scaleSimpleExpectation' (c:R)
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X} 
        {rv' : RandomVariable dom borel_sa (rvscale c rv_X)} 
        {frf' : FiniteRangeFunction (rvscale c rv_X)} : 
    SimpleExpectation (rv:=rv') (frf:=frf') (rvscale c rv_X) = (c * SimpleExpectation rv_X)%R.
  Proof.
    rewrite scaleSimpleExpectation.
    apply SimpleExpectation_pf_irrel.
  Qed.


  Instance RandomVariable_transport
           {rv_X1 rv_X2:Ts->R}
           {rv : RandomVariable dom borel_sa rv_X1}
           (eqq:rv_eq rv_X1 rv_X2) :
    RandomVariable dom borel_sa rv_X2.
  Proof.
    now rewrite eqq in rv.
  Qed.

  Program Instance FiniteRangeFunction_transport
          {rv_X1 rv_X2:Ts->R}
          (frf1:FiniteRangeFunction rv_X1)
          (eqq:rv_eq rv_X1 rv_X2) :
    FiniteRangeFunction rv_X2
    := { frf_vals := frf_vals }.
  Next Obligation.
    rewrite <- (eqq x).
    apply frf_vals_complete.
  Qed.

  Global Instance pre_event_preimage_proper {A B} : Proper (rv_eq ==> pre_event_equiv ==> pre_event_equiv) (@pre_event_preimage A B).
  Proof.
    unfold pre_event_preimage; intros ???????.
    rewrite H.
    apply H0.
  Qed.

  Global Instance event_preimage_proper {A B S} : Proper (rv_eq ==> event_equiv ==> pre_event_equiv) (@event_preimage A B S).
  Proof.
    unfold event_preimage; intros ???????.
    rewrite H.
    apply H0.
  Qed.
  
  Lemma SimpleExpectation_transport {rv_X1 rv_X2:Ts->R}
        {rv1 : RandomVariable dom borel_sa rv_X1}
        (frf1:FiniteRangeFunction rv_X1)
        (eqq:rv_eq rv_X1 rv_X2) :
    SimpleExpectation rv_X1 = SimpleExpectation rv_X2 (rv:=RandomVariable_transport eqq) (frf:=FiniteRangeFunction_transport frf1 eqq).
  Proof.
    unfold SimpleExpectation.
    simpl.
    induction frf_vals; simpl; trivial.
    match_destr.
    f_equal.
    apply map_ext; intros.
    f_equal.
    apply ps_proper.
    intros ?.
    unfold preimage_singleton, pre_event_preimage, pre_event_singleton; simpl.
    rewrite eqq.
    reflexivity.
  Qed.
  
  Lemma SimpleExpectation_ext 
        {rv_X1 rv_X2 : Ts -> R}
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        {frf1:FiniteRangeFunction rv_X1}
        {frf2:FiniteRangeFunction rv_X2}:
    rv_eq rv_X1 rv_X2 ->
    SimpleExpectation rv_X1 = SimpleExpectation rv_X2.
  Proof.
    intros eqq.
    rewrite (SimpleExpectation_transport frf1 eqq).
    apply SimpleExpectation_pf_irrel.
  Qed.

  Lemma EventIndicator_ext {P1 P2 : Ts->Prop} (dec1:forall x, {P1 x} + {~ P1 x}) (dec2:forall x, {P2 x} + {~ P2 x}) : 
    pre_event_equiv P1 P2 -> rv_eq (EventIndicator dec1) (EventIndicator dec2).
  Proof.
    unfold EventIndicator, pre_event_equiv, rv_eq.
    intros ??.
    repeat match_destr
    ; apply H in p; congruence.
  Qed.

  Lemma SimpleConditionalExpectationSA_ext (x y:Ts->R)
        {rvx : RandomVariable dom borel_sa x}
        {rvy : RandomVariable dom borel_sa y}
        {frfx : FiniteRangeFunction x}
        {frfy : FiniteRangeFunction y}          
        (l1 l2 : list dec_sa_event) :
    rv_eq x y ->
    Forall2 dsa_equiv l1 l2 ->
    rv_eq (SimpleConditionalExpectationSA x l1)
          (SimpleConditionalExpectationSA y l2).
  Proof.
    repeat red; intros.
    unfold SimpleConditionalExpectationSA.
    induction H0; simpl; trivial.
    unfold rvplus.
    f_equal; trivial.
    unfold gen_simple_conditional_expectation_scale.
    red in H0.
    match_destr.
    - rewrite H0 in e.
      match_destr; [| congruence].
      unfold rvscale.
      lra.
    - rewrite H0 in n.      
      match_destr; [congruence |].
      unfold rvscale.
      f_equal.
      + f_equal.
        * apply SimpleExpectation_ext.
          apply rvmult_proper; trivial.
          now apply EventIndicator_ext.
        * now rewrite H0.
      + now apply EventIndicator_ext.
  Qed.

  Lemma SimpleConditionalExpectationSA_transport (x y:Ts->R)
        {rvx : RandomVariable dom borel_sa x}
        {frfx : FiniteRangeFunction x}
        (l1 l2 : list dec_sa_event)
        (eqq:rv_eq x y) :
    Forall2 dsa_equiv l1 l2 ->
    rv_eq (SimpleConditionalExpectationSA x l1)
          (SimpleConditionalExpectationSA y l2 (rv:=RandomVariable_transport eqq) (frf:=FiniteRangeFunction_transport frfx eqq)).
  Proof.
    now apply SimpleConditionalExpectationSA_ext.
  Qed.

  Lemma SimpleConditionalExpectationSA_pf_irrel (x:Ts->R)
        {rv1 rv2 : RandomVariable dom borel_sa x}
        {frf1 frf2: FiniteRangeFunction x}
        l :
    SimpleConditionalExpectationSA x l (rv:=rv1) (frf:=frf1) = 
    (SimpleConditionalExpectationSA x l (rv:=rv1) (frf:=frf2)).
  Proof.
    unfold SimpleConditionalExpectationSA.
    f_equal.
    apply map_ext; intros.
    unfold gen_simple_conditional_expectation_scale.
    match_destr.
    f_equal.
    f_equal.
    apply SimpleExpectation_pf_irrel.
  Qed.

  
  (*
  Lemma sumSimpleExpectation
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        {frf1 : FiniteRangeFunction rv_X1} 
        {frf2 : FiniteRangeFunction rv_X2} :
    (SimpleExpectation rv_X1) + (SimpleExpectation rv_X2)%R = 
    SimpleExpectation (rvplus rv_X1 rv_X2).
  Proof.
    assert (H:incl (@frf_vals _ _ _ frf1) (0::(@frf_vals _ _ _ frf1)))
      by (red; simpl; tauto).
    rewrite (SimpleExpectation_simpl_incl frf1 _ H).
    assert (H0:incl (@frf_vals _ _ _ frf2) (0::(@frf_vals _ _ _ frf2)))
      by (red; simpl; tauto).
    rewrite (SimpleExpectation_simpl_incl frf2 _ H0).
    rewrite sumSimpleExpectation_nempty; simpl; trivial; try congruence.
    apply SimpleExpectation_pf_irrel.
  Qed.
   *)

  Lemma expectation_indicator_sum0 
        (rv_X : Ts -> R)
        (rv : RandomVariable dom borel_sa rv_X)
        {frf : FiniteRangeFunction rv_X}
        (l : list dec_sa_event) :
    
    list_sum
      (map (fun ev => SimpleExpectation 
                     (rvmult rv_X (EventIndicator (dsa_dec ev)))) l) =
    SimpleExpectation
      (fold_rvplus_prod_indicator rv_X l).
  Proof.
    unfold fold_rvplus_prod_indicator.
    induction l; simpl.
    - symmetry.
      erewrite SimpleExpectation_pf_irrel.
      apply SimpleExpectation_const.
    - rewrite IHl by (simpl in *; intuition).
      erewrite sumSimpleExpectation.
      apply SimpleExpectation_pf_irrel.
  Qed.
  
  Ltac se_rewrite H :=
    match type of H with
    | @SimpleExpectation _ _ _ ?x _ ?sx = _ =>
      match goal with
      | [|- context [@SimpleExpectation _ _ _ ?z _ ?sz]] =>
        rewrite (@SimpleExpectation_pf_irrel x sz sx); rewrite H
      end
    end.

  Lemma is_partition_list_nnil : NonEmpty Ts -> ~ is_partition_list [].
  Proof.
    intros a [??]; unfold list_union in *; simpl in *.
    assert (HH:Ω a) by now compute.
    rewrite <- (H0 a) in HH.
    destruct HH as [? [??]].
    tauto.
  Qed.

  Lemma list_union_dec (l:list dec_sa_event) :
    (forall x, sumbool ((list_union (map dsa_event l)) x) (~ (list_union (map dsa_event l)) x)).
  Proof.
    unfold list_union.
    intros x.
    induction l; simpl.
    - right; intros [?[??]]; tauto.
    - simpl in *.
      destruct (dsa_dec a x).
      + left.
        exists (dsa_event a).
        tauto.
      + destruct IHl.
        * left.
          destruct e as [? [??]]; eauto.
        * right.
          intros [? [[?|?]?]].
          -- congruence.
          -- apply n0.
             eauto.
  Defined.


  Instance fr_plus0_simple (l : list (Ts -> R)) 
           (frfs : Forallt FiniteRangeFunction l) :
    FiniteRangeFunction (fold_right rvplus (const 0) l).
  Proof.
    induction l; simpl.
    - typeclasses eauto.
    - invcs frfs.
      apply frfplus; eauto.
  Qed.

  Lemma very_specific_fold_right_rv_because_barry_waiting l :
    Forall (RandomVariable dom borel_sa) l ->
    RandomVariable dom borel_sa (fold_right rvplus (const 0) l).
  Proof.
    induction l; simpl; intros HH.
    - typeclasses eauto.
    - invcs HH.
      apply rvplus_rv; eauto.
  Qed.

  Lemma Forall_Forallt {A : Type} {P : A -> Prop} {l : list A} :
    Forall P l -> Forallt P l.
  Proof.
    induction l; intros HH; constructor.
    - rewrite Forall_forall in HH.
      apply HH; simpl; eauto.
    - apply IHl.
      now invcs HH.
  Defined.

  Lemma Forallt_conj {A : Type} {P1 P2 : A -> Type} {l : list A} :
    Forallt P1 l ->
    Forallt P2 l ->
    Forallt (fun x => prod (P1 x) (P2 x)) l.
  Proof.
    induction l; intros HH1 HH2.
    - constructor.
    - invcs HH1.
      invcs HH2.
      constructor; eauto.
  Defined.
  
  Lemma SimpleExpectation_fold_rvplus (l : list (Ts -> R)) 
        (rvs : Forall (RandomVariable dom borel_sa) l) 
        (frfs : Forallt FiniteRangeFunction l) :
    SimpleExpectation (fold_right rvplus (const 0) l) (rv:=very_specific_fold_right_rv_because_barry_waiting _ rvs) (frf:=fr_plus0_simple _ frfs) =
    list_sum (Forallt_map (fun x pf => SimpleExpectation x (rv:=fst pf) (frf:=snd pf)) (Forallt_conj (Forall_Forallt rvs) frfs)).
  Proof.
    dependent induction frfs; simpl.
    - erewrite SimpleExpectation_pf_irrel. 
      apply SimpleExpectation_const.
    - rewrite <- IHfrfs by trivial.
      rewrite sumSimpleExpectation; trivial.
      apply SimpleExpectation_pf_irrel.
  Qed.

  Lemma SimpleExpectation_fold_rvplus' (l : list (Ts -> R))
        {rv : RandomVariable dom borel_sa (fold_right rvplus (const 0) l)}
        {frf : FiniteRangeFunction (fold_right rvplus (const 0) l)}
        (rvs : Forall (RandomVariable dom borel_sa) l) 
        (frfs : Forallt FiniteRangeFunction l) :
    SimpleExpectation (fold_right rvplus (const 0) l) (rv:=rv) (frf:=frf) =
    list_sum (Forallt_map (fun x pf => SimpleExpectation x (rv:=fst pf) (frf:=snd pf)) (Forallt_conj (Forall_Forallt rvs) frfs)).
  Proof.
    generalize (SimpleExpectation_fold_rvplus l); intros HH.
    rewrite (SimpleExpectation_pf_irrel _ (fr_plus0_simple l frfs)).
    rewrite (SimpleExpectation_rv_irrel _ (very_specific_fold_right_rv_because_barry_waiting l rvs)).
    apply SimpleExpectation_fold_rvplus.
  Qed.
  Lemma indicator_sum (a:Ts)
        (l : list dec_sa_event)
        (is_disj: ForallOrdPairs event_disjoint (map dsa_event l)) :
    (EventIndicator (list_union_dec l) a) =
    (list_sum
       (map (fun ev => EventIndicator (dsa_dec ev) a) l)).
  Proof.
    unfold EventIndicator.
    induction l.
    - now simpl.
    - invcs is_disj.
      specialize (IHl H2).
      simpl.
      rewrite Forall_forall in H1.
      rewrite <- IHl; clear IHl.
      destruct (dsa_dec a0 a).
      + match_destr; try lra.
        destruct e as [? [inn ?]].
        specialize (H1 _ inn a); intuition.
      + destruct (list_union_dec l); try lra.
  Qed.

  Lemma expectation_indicator_sum_gen
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list dec_sa_event)
        (is_disj: ForallOrdPairs event_disjoint (map dsa_event l)) :
    SimpleExpectation (rvmult rv_X (EventIndicator (list_union_dec l))) =
    list_sum
      (map (fun ev => SimpleExpectation 
                     (rvmult rv_X (EventIndicator (dsa_dec ev)))) l).
  Proof.
    rewrite expectation_indicator_sum0 by trivial.
    unfold fold_rvplus_prod_indicator.
    apply SimpleExpectation_ext.
    unfold rv_eq.
    unfold pointwise_relation.
    intros.
    transitivity ( ((rv_X a) * (list_sum (map (fun ev  => 
                                                 (EventIndicator (dsa_dec ev) a))
                                              l)))).
    - unfold rvmult.
      f_equal.
      apply indicator_sum; trivial.
    - unfold rvplus.
      induction l.
      + simpl.
        unfold const.
        lra.
      + cut_to IHl.
        * simpl in *.
          unfold rvmult.
          rewrite Rmult_plus_distr_l.
          f_equal.
          now rewrite IHl.
        * now invcs is_disj.
  Qed.
  
  Lemma expectation_indicator_sum 
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list dec_sa_event)
        (is_part: is_partition_list (map dsa_event l)) :
    SimpleExpectation rv_X = 
    list_sum
      (map (fun ev => SimpleExpectation 
                     (rvmult rv_X (EventIndicator (dsa_dec ev)))) l).
  Proof.
    unfold is_partition_list in is_part.
    destruct is_part.
    rewrite <- expectation_indicator_sum_gen; trivial.
    apply SimpleExpectation_ext; trivial.
    unfold rv_eq.
    unfold pointwise_relation.
    intros.
    unfold rvmult.
    replace (rv_X a) with ((rv_X a) * 1) at 1 by lra.
    f_equal.
    unfold EventIndicator.
    destruct (list_union_dec l a); trivial.
    rewrite (H0 a) in n.
    unfold Ω, pre_Ω in n; simpl in n.
    intuition.
  Qed.

  Lemma sub_event_prob_0
        (P1 P2 : event dom) :
    ps_P P2 = 0 -> event_sub P1 P2 -> ps_P P1 = 0.
  Proof.
    intros.
    generalize (ps_sub Prts P1 P2); intros.
    cut_to H1; trivial.
    generalize (ps_pos P1); intros.
    lra.
  Qed.
  
  Lemma indicator_prob_0
        (P : event dom) 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (dec:forall x, {P x} + {~ P x})        
        (a : R) :
    ps_P P = 0 -> 
    a <> 0 ->
    ps_P (preimage_singleton (rvmult rv_X (EventIndicator dec)) a) = 0.
  Proof.
    intros.
    assert (event_sub (preimage_singleton (rvmult rv_X (EventIndicator dec)) a)
                      P).
    - unfold event_sub, pre_event_sub; simpl.
      vm_compute; intros.
      destruct (dec x); trivial.
      rewrite Rmult_0_r in x0.
      lra.
    - apply sub_event_prob_0 with (P2 := P); trivial.
  Qed.
  
  Lemma expectation_indicator_prob_0
        (P : event dom) 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (dec:forall x, {P x} + {~ P x}) :
    ps_P P = 0 -> 
    SimpleExpectation (rvmult rv_X (EventIndicator dec)) = 0.
  Proof.
    unfold SimpleExpectation.
    intros.
    simpl.
    erewrite <- (list_sum_map_zero _) at 2.
    f_equal.
    apply map_ext; intros.
    destruct (Req_EM_T a 0).
    - subst; field.
    - rewrite indicator_prob_0; trivial.
      field.
  Qed.

  Lemma gen_simple_conditional_expectation_scale_tower (P : event dom) 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (dec:forall x, {P x} + {~ P x}) :
    SimpleExpectation (gen_simple_conditional_expectation_scale P rv_X dec) =
    SimpleExpectation (rvmult rv_X (EventIndicator dec)).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    erewrite scaleSimpleExpectation'.
    match_destr.
    - field_simplify.
      unfold SimpleExpectation.
      induction frf_vals; simpl; trivial.
      match_destr.
      simpl.
      rewrite <- IHl.
      clear IHl.
      clear n l.
      destruct (Req_EM_T a 0).
      + subst; field.
      + rewrite indicator_prob_0; trivial.
        lra.
    - rewrite SimpleExpectation_EventIndicator.
      field; trivial.
  Qed.

  Lemma rv_md_gen_simple_scale
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list dec_sa_event) :
    Forall (RandomVariable dom borel_sa)
           (map (fun ev =>
                   gen_simple_conditional_expectation_scale
                     (dsa_event ev) rv_X (dsa_dec ev))
                l).
  Proof.
    induction l; simpl.
    - constructor.
    - constructor.
      + typeclasses eauto.
      + apply IHl.
  Qed.

  Lemma frf_md_gen_simple_scale
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list dec_sa_event) :
    Forallt FiniteRangeFunction
            (map (fun ev =>
                    gen_simple_conditional_expectation_scale
                      (dsa_event ev) rv_X (dsa_dec ev))
                 l).
  Proof.
    induction l; simpl.
    - constructor.
    - constructor.
      + typeclasses eauto.
      + apply IHl.
  Defined.

  Lemma gen_conditional_tower_law 
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list dec_sa_event)
        (ispart: is_partition_list (map dsa_event l)) :
    SimpleExpectation rv_X =
    SimpleExpectation
      (SimpleConditionalExpectationSA rv_X l).
  Proof.
    unfold SimpleConditionalExpectationSA.
    rewrite (expectation_indicator_sum rv_X l ispart).
    rewrite (SimpleExpectation_fold_rvplus') with (rvs:=rv_md_gen_simple_scale rv_X l)
                                                  (frfs:=frf_md_gen_simple_scale rv_X l).
    f_equal.
    clear ispart.
    induction l; simpl; trivial.
    f_equal.
    + unfold  gen_simple_conditional_expectation_scale.
      erewrite scaleSimpleExpectation'.
      rewrite SimpleExpectation_EventIndicator.
      match_destr.
      * rewrite e.
        field_simplify.
        now erewrite <- expectation_indicator_prob_0; try reflexivity.
      * field_simplify; trivial.
    + rewrite IHl.
      apply Forallt_map_irrel; intros.
      apply SimpleExpectation_pf_irrel.
  Qed.

  Program Definition induced_sigma_generators
          {rv_X : Ts -> R}
          {rv:RandomVariable dom borel_sa rv_X}
          (frf : FiniteRangeFunction rv_X)
    : list dec_sa_event
    :=
      map (fun c => Build_dec_sa_event
                   (preimage_singleton rv_X c) _)
          (nodup Req_EM_T frf_vals).
  Next Obligation.
    intros ?.
    apply Req_EM_T.
  Defined.

  
  Lemma induced_gen_ispart
        {rv_X : Ts -> R}
        {rv:RandomVariable dom borel_sa rv_X}
        (frf : FiniteRangeFunction rv_X) :
    is_partition_list (map dsa_event (induced_sigma_generators frf)).
  Proof. 
    unfold is_partition_list.
    unfold induced_sigma_generators, event_preimage, event_singleton.
    rewrite map_map; simpl.
    split.
    - apply event_disjoint_preimage_disj.
      apply NoDup_nodup.
    - destruct frf.
      unfold RandomVariable.frf_vals.
      unfold event_equiv; intros.
      unfold list_union.
      split.
      + intros.
        now unfold Ω, pre_Ω; simpl.
      + intros.
        eexists.
        split.
        * rewrite in_map_iff.
          exists (rv_X x).
          split; try easy.
          now rewrite nodup_In.
        * now simpl.
  Qed.

  Lemma conditional_tower_law 
        (rv_X1 rv_X2 : Ts -> R)
        (rv1 : RandomVariable dom borel_sa rv_X1)
        (rv2 : RandomVariable dom borel_sa rv_X2)        
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} :

    SimpleExpectation (SimpleConditionalExpectation rv_X1 rv_X2) = SimpleExpectation rv_X1.
  Proof.
    symmetry.
    rewrite  (gen_conditional_tower_law rv_X1 (induced_sigma_generators frf2))
    ; trivial ; [| apply induced_gen_ispart].
    unfold SimpleConditionalExpectationSA, gen_simple_conditional_expectation_scale.
    unfold SimpleConditionalExpectation, SimpleConditionalExpectation_list.
    unfold simple_conditional_expectation_scale_coef.
    unfold point_preimage_indicator,induced_sigma_generators.
    unfold event_preimage, event_singleton, EventIndicator.
    apply SimpleExpectation_ext.
    intros x.
    rewrite map_map; simpl.
    induction (nodup Req_EM_T frf_vals); simpl; trivial.
    unfold rvplus; simpl.
    f_equal; trivial.
    unfold rvscale.
    unfold induced_sigma_generators_obligation_1.
    match_destr.
    erewrite SimpleExpectation_pf_irrel; reflexivity.
  Qed.

  Definition simple_sigma_measurable 
             (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2}
             {frf1 : FiniteRangeFunction rv_X1}
             {frf2 : FiniteRangeFunction rv_X2} : Prop :=
    forall (c2:R), In c2 (frf_vals (FiniteRangeFunction:=frf2)) ->
              exists (c1:R), (* In c1 (frf_vals (FiniteRangeFunction:=frf1)) /\ *)
                (event_sub (preimage_singleton rv_X2 c2)
                           (preimage_singleton rv_X1 c1)).


  Lemma events_measurable0_b
        (l1 l2 : list (event dom)) :
    (exists l : list (list (event dom)),
        Forall2 (fun x y => event_equiv x (list_union y)) l1 l
        /\ Permutation (concat l) l2) ->
    (forall (p2:event dom),
        In p2 l2 ->
        exists (p1:event dom), (In p1 l1) /\ event_sub p2 p1).
  Proof.
    intros [l [Fl Pl]].
    intros p2 p2inn.
    rewrite <- Pl in p2inn.
    apply concat_In in p2inn.
    destruct p2inn as [ll [llinn inll]].
    destruct (Forall2_In_r Fl llinn) as [x [xin xequiv]].
    exists x.
    split; trivial.
    intros y p2y.
    apply xequiv.
    simpl; eauto.
  Qed.

  (*  (dec:forall a, P \/ ~P) *)
  Lemma classic_filter {A} (P:A->Prop) (l:list A) :
    exists l', sublist l' l /\ forall x, In x l' <-> In x l /\ P x.
  Proof.
    induction l.
    - exists nil.
      constructor.
      + constructor.
      + intuition.
    - destruct IHl as [l' [subl' inifl']].
      destruct (classic (P a)).
      + exists (a::l').
        split.
        * constructor; trivial.
        * simpl; intros ?; split.
          -- intros [?|?].
             ++ subst; eauto.
             ++ apply inifl' in H0.
                tauto.
          -- intros [[?|?]?].
             ++ subst; eauto.
             ++ right; apply inifl'; tauto.
      + exists l'.
        split.
        * apply sublist_skip; trivial.
        * simpl in *.
          intros x; split; intros.
          -- apply inifl' in H0.
             tauto.
          -- destruct H0 as [??].
             apply inifl'.
             split; trivial.
             destruct H0; congruence.
  Qed.

  Lemma classic_sub_filter {A} (P:A->Prop) (l:list (list A)) :
    exists l', Forall2 sublist l' l /\ Forall2 (fun ll1 ll2 => forall x, In x ll2 <-> In x ll1 /\ P x) l l'.
  Proof.
    induction l.
    - exists nil.
      constructor.
      + constructor.
      + intuition.
    - destruct IHl as [l' [subl' inifl']].
      destruct (classic_filter P a) as [a' [a's a'i]].
      exists (a'::l').
      split.
      + constructor; trivial.
      + constructor; trivial.
  Qed.

  Definition partition_measurable {Td}
             {cod:SigmaAlgebra Td}
             {has_pre:HasPreimageSingleton cod}
             (rv_X : Ts -> Td)
             {rv : RandomVariable dom cod rv_X}
             {frf : FiniteRangeFunction rv_X}
             (l : list (event dom)) : Prop :=
    is_partition_list l ->
    forall (p:event dom),
      In p l ->
      exists c, event_sub p (preimage_singleton rv_X c).

  Lemma event_none_or_witness (E : event dom) :
    E === event_none \/ exists (x:Ts), E x.
  Proof.
    classical_left.
    unfold event_none, pre_event_none.
    intros x; split; simpl; intros y
    ; [| tauto].
    apply H.
    eexists; apply y.
  Qed.

  Global Instance pre_union_of_collection_sub_partition_proper {T} :
    Proper (pre_sub_partition ==> pre_event_sub) (@pre_union_of_collection T).
  Proof.
    unfold pre_sub_partition, pre_event_sub, pre_union_of_collection.
    intros ?? sub x [n xn].
    destruct (sub n).
    - apply H in xn; eauto.
    - eapply H in xn.
      red in xn; tauto.
  Qed.

  Lemma is_pre_partition_list_contains_all {l:list (pre_event Ts)} :
    is_pre_partition_list l ->
    forall a, exists! e, In e l /\ e a.
  Proof.
    intros [FP lall] a.
    destruct (lall a) as [_ HH].
    destruct (HH I) as [e [??]].
    exists e.
    split; [tauto | ].
    intros ?[??].
    destruct (ForallOrdPairs_In FP _ _ H H1) as [?|[?|?]]; trivial.
    elim (H3 _ H0 H2).    
    elim (H3 _ H2 H0).    
  Qed.

  Lemma partition_measurable_list_rv_f {Td}
        {cod:SigmaAlgebra Td}
        {has_pre:HasPreimageSingleton cod}
        (rv_X : Ts -> Td)
        {rv : RandomVariable dom cod rv_X}
        {frf : FiniteRangeFunction rv_X}
        (has_singles: forall x, sa_sigma cod (pre_event_singleton x))
        (l : list (event dom))
        (isp:is_pre_partition_list (map event_pre l)) :
    partition_measurable rv_X l -> RandomVariable (list_partition_sa (map event_pre l)
                                                                    isp) cod rv_X.
  Proof.
    unfold RandomVariable; simpl.
    unfold partition_measurable.
    intros HH B.
    red.
    cut_to HH; [| now apply is_partition_list_pre].

    exists (fun n => pre_event_inter (event_preimage rv_X B) (pre_list_collection (map event_pre l) pre_event_none n)).
    split.
    + intros n.
      unfold pre_list_collection.
      destruct (@nth_in_or_default (pre_event Ts) n (map event_pre l) pre_event_none).
      * replace (@pre_event_none Ts) with (proj1_sig (P:=fun e : pre_event Ts => sa_sigma _ e) (@event_none Ts dom)) in i by reflexivity.
        rewrite map_nth in i.
        apply in_map_iff in i.
        destruct i as [? [eqq inn]]; subst.
        destruct (HH _ inn) as [c csub].
        destruct (sa_dec B c).
        -- left.
           unfold pre_event_inter.
           intros ?.
           split; [firstorder |].
           split; trivial.
           red.
           specialize (csub x0).
           simpl in csub.
           unfold pre_event_preimage, pre_event_singleton in csub.
           rewrite csub; trivial.
           unfold event_pre in eqq.
           rewrite eqq.
           replace (@pre_event_none Ts) with (proj1_sig (P:=fun e : pre_event Ts => sa_sigma _ e) (@event_none Ts dom)) in H0  by reflexivity.
           now rewrite map_nth in H0.
        -- right.
           intros ?.
           unfold pre_event_none, pre_event_inter.
           split; [| tauto]; intros [HH1 HH2].
           elim H.
           specialize (csub x0).
           red in HH2.
           unfold preimage_singleton, pre_event_preimage, pre_event_singleton in csub.
           simpl in csub.
           rewrite <- csub; trivial.
           unfold event_pre in eqq.
           rewrite eqq.
           rewrite <- map_nth.
           apply HH2.
      * rewrite e.
        rewrite pre_event_inter_false_r.
        left; reflexivity.
    + rewrite <- pre_event_inter_countable_union_distr.
      rewrite pre_list_union_union.
      destruct isp.
      rewrite H0.
      rewrite pre_event_inter_true_r.
      reflexivity.
  Qed.
  
  Lemma partition_measurable_list_rv_b {Td} {nempty:NonEmpty Td}
        {cod:SigmaAlgebra Td}
        {has_pre:HasPreimageSingleton cod}
        (rv_X : Ts -> Td)
        {rv : RandomVariable dom cod rv_X}
        {frf : FiniteRangeFunction rv_X}
        (has_singles: forall x, sa_sigma cod (pre_event_singleton x))
        (l : list (event dom))
        (isp:is_pre_partition_list (map event_pre l)) :
    RandomVariable (list_partition_sa (map event_pre l) isp) cod rv_X -> partition_measurable rv_X l.
  Proof.
    intros HH _ p inp.
    destruct frf.
    destruct isp as [HH2 HH3].
    destruct (event_none_or_witness p) as [Hnone | [a pa]].
    + exists nempty.
      intros ??.
      apply Hnone in H.
      repeat red in H.
      tauto.
    + specialize (HH (event_singleton (rv_X a) (has_singles _))).
      destruct HH as [C [Csub Ceqq]].
      unfold event_sub.
      unfold equiv, event_equiv in Ceqq.
      unfold preimage_singleton; simpl.
      unfold event_preimage in Ceqq.
      simpl in Ceqq.
      red in Csub.
      red in Ceqq.
      unfold pre_event_singleton in Ceqq.
      assert (inp':In (event_pre p) (map event_pre l))
        by (apply in_map_iff; eauto).
      destruct (In_nth _ _ (@pre_event_none Ts) inp')
        as [n [??]].
      destruct (Csub n).
      * exists (rv_X a).
        intros x px.
        unfold preimage_singleton; simpl.
        unfold pre_event_preimage, pre_event_singleton; simpl.
        apply Ceqq.
        red.
        exists n.
        apply H1.
        red.
        now rewrite H0.
      * specialize (Ceqq a).
        destruct Ceqq as [_ Ca].
        specialize (Ca (eq_refl _)).
        destruct Ca as [n' Cn'a].
        assert (Cn'ne:~ C n' === pre_event_none).
        {
          intros x.
          apply x in Cn'a.
          red in Cn'a.
          tauto.
        } 
        destruct (Csub n'); [| tauto].
        rewrite <- H0 in pa.
        unfold pre_list_collection in H2.
        assert (n'bound:(n' < length (map event_pre l))%nat).
        {
          destruct (lt_dec n' (length (map event_pre l))%nat); trivial.
          apply not_lt in n0.
          unfold pre_event in H2.
          rewrite (nth_overflow (map event_pre l) pre_event_none n0) in H2.
          elim (Cn'ne H2).
        }

        destruct (ForallOrdPairs_In_nth_symm
                    (map event_pre l)
                    pre_event_none pre_event_none
                    n n'
                    HH2
                    H n'bound).
        -- subst.
           elim (Cn'ne H1).
        -- elim (H3 a); trivial.
           now apply H2.
  Qed.           

  Lemma partition_measurable_list_rv {Td} {nempty:NonEmpty Td}
        {cod:SigmaAlgebra Td}
        {has_pre:HasPreimageSingleton cod}
        (rv_X : Ts -> Td)
        {rv : RandomVariable dom cod rv_X}
        {frf : FiniteRangeFunction rv_X}
        (has_singles: forall x, sa_sigma cod (pre_event_singleton x))
        (l : list (event dom))
        (isp:is_pre_partition_list (map event_pre l)) :
    partition_measurable rv_X l <-> RandomVariable (list_partition_sa (map event_pre l)
                                                                    isp) cod rv_X.
  Proof.
    split.
    - now apply partition_measurable_list_rv_f.
    - now apply partition_measurable_list_rv_b.
  Qed.
  
  Lemma nth_map_default_equiv {A} {R} n (l:list A) (d1 d2:A)
        {refl:Reflexive R} :
    R d1 d2 ->
    R (nth n l d1) (nth n l d2).
  Proof.
    repeat rewrite <- nth_default_eq.
    unfold nth_default.
    match_destr.
  Qed.

  Lemma event_inter_sub_l {T:Type} {σ:SigmaAlgebra T} (A B:event σ) :
    event_sub B A -> event_equiv (event_inter A B) B.
  Proof.
    firstorder.
  Qed.

  (*
  Lemma events_measurable_sa_f
        (l1 l2 : list (event Ts))
        (ispartl1: is_partition_list l1)
        (ispartl2: is_partition_list l2)
    : 
      (forall (p2:event Ts),
          In p2 l2 ->
          exists (p1:event Ts), (In p1 l1) /\ event_sub p2 p1) ->
      (forall (p1:event Ts),
          In p1 l1 -> (@sa_sigma Ts (list_partition_sa l2 ispartl2) p1)).
  Proof.
    intros.
    simpl.
    destruct (classic_event_none_or_has p1).
    - destruct H1 as [y py].
      unfold in_partition_union, list_collection, sub_partition.
      exists (list_collection (map (fun z => event_inter p1 z) l2) event_none).
      split.
      + intros n.
        unfold list_collection.
        rewrite (nth_map_default_equiv (R:=event_equiv) _ (map (fun z : event Ts => event_inter p1 z) l2) _ ((fun z : event Ts => event_inter p1 z) event_none))
        ; [| autorewrite with prob; reflexivity].
        rewrite map_nth.
        destruct (nth_in_or_default n l2 event_none); trivial.
        * destruct (H _ i) as [p1' [p1'inn p1'sub]].
          destruct ispartl1 as [Dl1 Al1].
          destruct (ForallOrdPairs_In Dl1 _ _ H0 p1'inn).
          -- subst.
             left.
             now apply event_inter_sub_l.
          -- assert (disj:event_disjoint p1 p1').
             {
               destruct H1; trivial.
               unfold event_disjoint in *.
               eauto.
             }
             clear H1.
             right.
             intros x; unfold event_none.
             split; [| tauto].
             intros [??].
             apply p1'sub in H2.
             eapply disj; eauto.
        * right.
          rewrite e.
          autorewrite with prob.
          reflexivity.
      + rewrite list_union_union.
        rewrite <- event_inter_list_union_distr.
        destruct ispartl2 as [FP2 equiv2].
        rewrite equiv2.
        rewrite event_inter_true_r.
        reflexivity.
    - exists (fun _ => event_none).
      split.
      + intros x.
        right; reflexivity.
      + intros x.
        unfold union_of_collection.
        split; intros.
        * apply H1.
          destruct H2; trivial.
        * apply H1 in H2.
          exists (0%nat); trivial.
  Qed.
   *)
  (*
  Lemma events_measurable_sa_b {nempty:NonEmpty Ts}
        (l1 l2 : list (event Ts))
        (ispartl1: is_partition_list l1)
        (ispartl2: is_partition_list l2)
    : 
      (forall (p1:event Ts),
          In p1 l1 -> (@sa_sigma Ts (list_partition_sa l2 ispartl2) p1)) ->
      (forall (p2:event Ts),
          In p2 l2 ->
          exists (p1:event Ts), (In p1 l1) /\ event_sub p2 p1).
  Proof.
    simpl.
    intros HH p2 p2inn.
    destruct (classic_event_none_or_has p2).
    - destruct H as [y py].
      destruct ispartl1 as [D1 A1].
      assert (yl1:list_union l1 y).
      { apply A1; red; trivial. }
      destruct yl1 as [z [zinn zy]].
      exists z.
      split; trivial.
      specialize (HH _ zinn).
      destruct HH as [c [csub cu]].
      red in csub.
      apply cu in zy.
      destruct zy.
      rewrite <- cu.
      intros w winn.
      red.
      destruct (csub x).
      + apply H0 in H.
        unfold list_collection in H.
        destruct (nth_in_or_default x l2 event_none); trivial.
        * destruct ispartl2 as [D2 A2].
          destruct (ForallOrdPairs_In D2 _ _ p2inn i).
          -- subst.
             exists x.
             apply H0.
             now red.
          -- destruct H1.
             ++ elim (H1 _ py H).
             ++ elim (H1 _ H py).
        * rewrite e in H.
          elim H.
      + apply H0 in H.
        elim H.
    - destruct l1.
      + elim (is_partition_list_nnil _ ispartl1).
      + exists e; simpl.
        split; [eauto | ].
        rewrite H.
        unfold event_sub, event_none; tauto.
  Qed.


  Lemma events_measurable_sa {nempty:NonEmpty Ts}
        (l1 l2 : list (event Ts))
        (ispartl1: is_partition_list l1)
        (ispartl2: is_partition_list l2)
    : 
      (forall (p2:event Ts),
          In p2 l2 ->
          exists (p1:event Ts), (In p1 l1) /\ event_sub p2 p1) <->
      (forall (p1:event Ts),
          In p1 l1 -> (@sa_sigma Ts (list_partition_sa l2 ispartl2) p1)).
  Proof.
    split.
    - now apply events_measurable_sa_f.
    - now apply events_measurable_sa_b.
  Qed.
   *)
  
  
  Lemma expectation_const_factor_subset (c:R)
        (p : event dom)
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} 
        (dec:  (forall x, {p x} + {~ p x})) :
    (forall (omega:Ts), p omega -> rv_X1 omega = c) ->
    SimpleExpectation
      (rvmult (rvmult rv_X1 rv_X2) (EventIndicator dec)) =
    c * SimpleExpectation
          (rvmult rv_X2 (EventIndicator dec)).
  Proof.
    intros.
    rewrite scaleSimpleExpectation.
    apply SimpleExpectation_ext.
    intros ev.
    unfold EventIndicator, rvmult, rvscale.
    match_destr.
    - rewrite H; trivial.
      field.
    - field.
  Qed.

  Global Instance rvplus_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) (@rvplus Ts).
  Proof.
    unfold rv_eq, pointwise_relation, rvplus.
    intros ???????.
    now rewrite H, H0.
  Qed.

  Lemma rvscale0 (rv:Ts->R) : rv_eq (rvscale 0 rv) (const 0).
  Proof.
    unfold rvscale, const; intros ?; simpl.
    field.
  Qed.

  (* if l is viewed as finite generators for a sigma algebra, this shows that
    we can factor out l-measurable random variables from conditional expectation *)
  Lemma gen_conditional_scale_measurable
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} 
        (l : list dec_sa_event) :
    is_partition_list (map dsa_event l) ->
    partition_measurable rv_X1 (map dsa_event l) ->
    rv_eq (SimpleConditionalExpectationSA (rvmult rv_X1 rv_X2) l)
          (rvmult rv_X1 (SimpleConditionalExpectationSA rv_X2 l  )).
  Proof.
    unfold partition_measurable, event_preimage, event_singleton.
    intros is_part meas.
    unfold SimpleConditionalExpectationSA.
    unfold gen_simple_conditional_expectation_scale.
    specialize (meas is_part).
    destruct is_part as [FP _].
    induction l.
    - simpl.
      unfold rvmult, const; intros ?; simpl.
      field.
    - simpl.
      invcs FP.
      cut_to IHl; trivial.
      + rewrite IHl.
        clear IHl.
        match_destr.
        * unfold rvplus, rvmult, rvscale; intros ?.
          field.
        * intros x.
          case_eq (dsa_dec a x); [intros d _ | intros d eqq].
          -- specialize (meas (dsa_event a)).
             cut_to meas; [| simpl; intuition].
             destruct meas as [c ceq].
             rewrite (expectation_const_factor_subset (rv_X1 x)).
             ++ unfold rvscale, rvplus, rvmult.
                field; trivial.
             ++ intros.
                apply ceq in H.
                apply ceq in d.
                congruence.
          -- unfold rvplus, rvscale, rvmult, EventIndicator.
             repeat rewrite eqq.
             field; trivial.
      + intros.
        apply meas; simpl; intuition.
  Qed.

  Lemma conditional_scale_measurable
        (rv_X1 rv_X2 rv_X3 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        {rv3 : RandomVariable dom borel_sa rv_X3}

        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} 
        {frf3 : FiniteRangeFunction rv_X3} :     
    
    simple_sigma_measurable rv_X1 rv_X3 ->
    rv_eq (SimpleConditionalExpectation (rvmult rv_X1 rv_X2) rv_X3)
          (rvmult rv_X1 (SimpleConditionalExpectation rv_X2 rv_X3)).
  Proof.
    generalize (gen_conditional_scale_measurable rv_X1 rv_X2 
                                                 (induced_sigma_generators frf3)
                                                 (induced_gen_ispart frf3)).
    intros.
    cut_to H.
    - unfold SimpleConditionalExpectationSA in H.
      unfold SimpleConditionalExpectation, SimpleConditionalExpectation_list.
      unfold simple_conditional_expectation_scale_coef.
      unfold gen_simple_conditional_expectation_scale in H.
      unfold point_preimage_indicator.
      unfold event_preimage, event_singleton.
      unfold induced_sigma_generators in H.
      unfold induced_sigma_generators_obligation_1 in H.
      unfold event_preimage, event_singleton in H.
      do 2 rewrite map_map in H.
      simpl in H.
      etransitivity; [| etransitivity; [eapply H|]]; clear.
      + induction  (nodup Req_EM_T frf_vals); simpl; [reflexivity |].
        apply rvplus_proper; eauto.
        apply rvscale_proper; try reflexivity.
        match_destr.
        f_equal.
        apply SimpleExpectation_pf_irrel.
      + induction  (nodup Req_EM_T frf_vals); simpl; [reflexivity |].
        repeat rewrite rvmult_rvadd_distr.
        apply rvplus_proper; eauto.
        apply rvmult_proper; [reflexivity |].
        apply rvscale_proper; try reflexivity.
        match_destr.
        f_equal.
        apply SimpleExpectation_pf_irrel.
    - unfold simple_sigma_measurable in H0.
      unfold partition_measurable, induced_sigma_generators.
      unfold event_preimage, event_singleton in *.
      rewrite map_map; simpl.
      intros.
      rewrite in_map_iff in H2.
      destruct H2.
      destruct H2.
      rewrite <- H2.
      apply H0.
      erewrite <- nodup_In.
      apply H3.
  Qed.

    Lemma SimpleConditionalExpectationSA_rvscale (c:R)
          (rv_X : Ts -> R)
          {rv : RandomVariable dom borel_sa rv_X}
          {frf : FiniteRangeFunction rv_X}
          (l : list dec_sa_event) :
      is_partition_list (map dsa_event l) ->
      rv_eq (SimpleConditionalExpectationSA (rvscale c rv_X) l)
            (rvscale c (SimpleConditionalExpectationSA rv_X l  )).
    Proof.
      intros.
      transitivity (SimpleConditionalExpectationSA (rvmult (const c) rv_X) l).
      { 
        apply SimpleConditionalExpectationSA_ext.
        - intros x.
          now unfold rvscale, rvmult, const.
        - easy.
      }
      apply gen_conditional_scale_measurable; trivial.
      unfold partition_measurable; intros.
      exists c.
      repeat red.
      reflexivity.
    Qed.

End SimpleConditionalExpectation.  

Section sa_sub.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Lemma SimpleExpectation_prob_space_sa_sub
        (x:Ts->R)
        {rv:RandomVariable dom borel_sa x} 
        {rv2:RandomVariable dom2 borel_sa x} 
        {frf:FiniteRangeFunction x} :
    @SimpleExpectation Ts dom2 (prob_space_sa_sub prts sub) x rv2 frf =
    @SimpleExpectation Ts dom prts x rv frf.
  Proof.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext; intros.
    f_equal.
    simpl.
    apply ps_proper.
    intros ?.
    unfold preimage_singleton; simpl.
    tauto.
  Qed.

End sa_sub.

Section indep.

    Context {Ts:Type} 
            {dom: SigmaAlgebra Ts}
            (prts:ProbSpace dom).

    Instance list_sum_map_rv {A} f (l:list A)
             {rv : forall x, RandomVariable dom borel_sa (f x)} :
      RandomVariable dom borel_sa (fun omega => list_sum (map (fun x => f x omega) l)).
    Proof.
      induction l.
      - simpl.
        apply rvconst.
      - apply rvplus_rv; trivial.
    Qed.

    Instance list_sum_map_frf {A} (f:A->Ts->R) (l:list A)
             {frf : forall x, FiniteRangeFunction (f x)} :
      FiniteRangeFunction (fun omega => list_sum (map (fun x => f x omega) l)).
    Proof.
      induction l; simpl.
      - apply frfconst.
      - apply frfplus; trivial.
    Qed.

    Lemma SimpleExpectation_list_sum_map_all {A} f (l:list A)
          {rvX : forall x, RandomVariable dom borel_sa (f x)}
          {frfX : forall x, FiniteRangeFunction (f x)}

      :
      SimpleExpectation (fun omega => list_sum (map (fun x => f x omega) l)) =
        list_sum (map (fun x => SimpleExpectation (f x)) l).
    Proof.
      induction l; simpl.
      - rewrite <- (SimpleExpectation_const 0 _).
        now apply SimpleExpectation_ext.
      - rewrite <- IHl.
        rewrite sumSimpleExpectation.
        now apply SimpleExpectation_ext.
    Qed.

    Lemma SimpleExpectation_list_sum_map_all' {A} f (l:list A)
          {rvX : forall x, RandomVariable dom borel_sa (f x)}
          {frfX : forall x, FiniteRangeFunction (f x)}
          {rvs : RandomVariable dom borel_sa (fun omega => list_sum (map (fun x => f x omega) l))}
          {frfs : FiniteRangeFunction (fun omega => list_sum (map (fun x => f x omega) l))}

      :
      SimpleExpectation (fun omega => list_sum (map (fun x => f x omega) l)) =
        list_sum (map (fun x => SimpleExpectation (f x)) l).
    Proof.
      rewrite <- SimpleExpectation_list_sum_map_all.
      apply SimpleExpectation_pf_irrel.
    Qed.

  Lemma SimpleExpectation_indep (X Y:Ts -> R)
        {rvX : RandomVariable dom borel_sa X}
        {frfX : FiniteRangeFunction X}
        {rvY : RandomVariable dom borel_sa Y}
        {frfY : FiniteRangeFunction Y} :
    independent_rvs prts borel_sa borel_sa X Y ->
    SimpleExpectation (rvmult X Y) =
      SimpleExpectation X * SimpleExpectation Y.
  Proof.
    intros indep.
    generalize (frf_indicator_sum X); intros eqqX.
    generalize (frf_indicator_sum Y); intros eqqY.
    assert (eqqXY : rv_eq (rvmult X Y) (rvmult (frf_indicator X) (frf_indicator Y)))
      by now apply rvmult_proper.
    unfold frf_indicator in eqqXY.
    assert (eqq2:rv_eq (rvmult X Y)
               (fun omega : Ts =>
                list_sum
                  (map (fun c : R =>
                          list_sum
                            (map (fun c : R => scale_val_indicator X c omega) (nodup Req_EM_T (@frf_vals _ _ X _))) *
  

                            scale_val_indicator Y c omega) (nodup Req_EM_T (@frf_vals _ _ Y _))))).
    {
      rewrite eqqXY; intros ?.
      unfold rvmult.
      now rewrite list_sum_const_mul.
    }

    assert (eqq3:rv_eq (rvmult X Y)
                       (fun omega : Ts =>
                          list_sum
                            (map (fun c : R =>
                                    list_sum
                                      (map (fun d : R => scale_val_indicator X d omega * scale_val_indicator Y c omega) (nodup Req_EM_T (@frf_vals _ _ X _)))
                                 ) (nodup Req_EM_T (@frf_vals _ _ Y _))))).
    {
      rewrite eqq2; intros ?.
      f_equal.
      apply map_ext; intros ?.
      rewrite Rmult_comm.
      rewrite <- list_sum_const_mul.
      f_equal; apply map_ext; intros ?.
      now rewrite Rmult_comm.
    }
    assert (eqq4:rv_eq (rvmult X Y)
                       (fun omega : Ts =>
                          list_sum
                            (map (fun c : R =>
                                    list_sum
                                      (map (fun d : R => rvscale (c*d)
                                                              (EventIndicator (classic_dec (fun omega => X omega = d /\ Y omega = c))) omega) (nodup Req_EM_T (@frf_vals _ _ X _)))
                                 ) (nodup Req_EM_T (@frf_vals _ _ Y _))))).
    {
      rewrite eqq3; intros ?.
      f_equal.
      apply map_ext; intros ?.
      f_equal; apply map_ext; intros ?.
      unfold scale_val_indicator, val_indicator, rvscale.
      unfold EventIndicator.
      repeat match_destr; try lra.
    }       

    rewrite (SimpleExpectation_transport _ eqq4).
    assert (frfs : forall c d, FiniteRangeFunction (EventIndicator (classic_dec (fun omega0 : Ts => X omega0 = d /\ Y omega0 = c)))).
    {
      typeclasses eauto.
    }       

    assert (rvs : forall c d, RandomVariable dom borel_sa (EventIndicator (classic_dec (fun omega0 : Ts => X omega0 = d /\ Y omega0 = c)))).
    {
      intros.
      apply EventIndicator_pre_rv.
      now apply sa_sigma_inter_pts.
    }       

    transitivity (
           list_sum
             (map
                (fun c : R =>
                   list_sum
                     (map
                        (fun d : R =>
                           Rmult (c * d)
                                 (SimpleExpectation (EventIndicator
                                                       (classic_dec (fun omega0 : Ts => X omega0 = d /\ Y omega0 = c)))))
                        (nodup Req_EM_T (@frf_vals _ _ X _)))
                                 ) (nodup Req_EM_T (@frf_vals _ _ Y _)))).
    {
      rewrite (SimpleExpectation_list_sum_map_all' _ _).
      f_equal.
      apply map_ext; intros.
      rewrite (SimpleExpectation_list_sum_map_all' _ _).
      f_equal.
      apply map_ext; intros.
      rewrite scaleSimpleExpectation.
      reflexivity.
    }

    assert (saXd : forall d, sa_sigma _(fun omega => X omega = d)).
    {
      intros.
      apply sa_le_pt.
      now apply sa_le_le_rv.
    } 
    assert (saYc : forall c, sa_sigma _(fun omega => Y omega = c)).
    {
      intros.
      apply sa_le_pt.
      now apply sa_le_le_rv.
    } 

    assert (saYXcd : forall c d, sa_sigma _ (fun omega0 : Ts => X omega0 = d /\ Y omega0 = c)).
    {
      intros.
      now apply sa_inter.
    } 
    
    transitivity 
      (list_sum
             (map
                (fun c : R =>
                   list_sum
                     (map
                        (fun d : R =>
                           Rmult (c * d)
                                 (ps_P (exist _ _ (saYXcd c d))))
                        (nodup Req_EM_T (@frf_vals _ _ X _)))
                ) (nodup Req_EM_T (@frf_vals _ _ Y _)))).
    {
      f_equal; apply map_ext; intros.
      f_equal; apply map_ext; intros.
      f_equal.
      etransitivity
      ; [| apply SimpleExpectation_pre_EventIndicator].
      apply SimpleExpectation_ext.
      reflexivity.
    } 

    transitivity 
      (list_sum
             (map
                (fun c : R =>
                   list_sum
                     (map
                        (fun d : R =>
                           (c * ps_P (exist _ _ (saYc c)) * (d * ps_P (exist _ _ (saXd d)))))
                        (nodup Req_EM_T (@frf_vals _ _ X _)))
                ) (nodup Req_EM_T (@frf_vals _ _ Y _)))).
    {
      f_equal; apply map_ext; intros.
      f_equal; apply map_ext; intros.
      field_simplify.
      repeat rewrite Rmult_assoc.
      do 2 f_equal.
      unfold independent_rvs, independent_events, rv_preimage, event_preimage in indep.
      clear eqq2 eqq3 eqq4.
      specialize (indep (exist _ _ (borel_singleton a0)) (exist _ _ (borel_singleton a))).
      etransitivity; [| etransitivity]; [| eapply indep | ].
      - apply ps_proper.
        intros ?; simpl.
        reflexivity.
      - simpl; intros.
        rewrite Rmult_comm.
        f_equal.
        + apply ps_proper; intros ?; simpl.
          reflexivity.
        + apply ps_proper; intros ?; simpl.
          reflexivity.
    }
    clear eqqXY eqq2 eqq3 eqq4.
    transitivity
      (list_sum
         (map
            (fun c : R =>
               c * ps_P (exist (sa_sigma _) (fun omega : Ts => Y omega = c) (saYc c)))
            (nodup Req_EM_T (@frf_vals _ _ Y _)))
      * 
        (list_sum
           (map
              (fun d : R =>
                 (d * ps_P (exist (sa_sigma _) (fun omega : Ts => X omega = d) (saXd d))))
              (nodup Req_EM_T (@frf_vals _ _ X _))))).
    {
      rewrite Rmult_comm.
      rewrite <- list_sum_const_mul.
      f_equal; apply map_ext; intros.
      rewrite Rmult_comm.
      rewrite list_sum_const_mul.
      rewrite (Rmult_comm).
      f_equal.
      rewrite Rmult_comm.
      reflexivity.
    }
    rewrite Rmult_comm.
    f_equal.
    - rewrite (SimpleExpectation_transport _ eqqX).
      unfold frf_indicator.
      rewrite (SimpleExpectation_list_sum_map_all' _ _).
      f_equal; apply map_ext; intros.
      unfold scale_val_indicator.
      rewrite <- (SimpleExpectation_pre_EventIndicator _ (classic_dec _)).
      rewrite  scaleSimpleExpectation.
      apply SimpleExpectation_pf_irrel.
    - rewrite (SimpleExpectation_transport _ eqqY).
      unfold frf_indicator.
      rewrite (SimpleExpectation_list_sum_map_all' _ _).
      f_equal; apply map_ext; intros.
      unfold scale_val_indicator.
      rewrite <- (SimpleExpectation_pre_EventIndicator _ (classic_dec _)).
      rewrite  scaleSimpleExpectation.
      apply SimpleExpectation_pf_irrel.
  Qed.

End indep.
