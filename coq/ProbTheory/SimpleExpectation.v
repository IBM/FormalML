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
Require Import SigmaAlgebras.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section SimpleExpectation.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Local Open Scope prob.
    
  Definition FiniteRangeFunction_partition_image 
             {rv_X : Ts -> R}
             {rrv : RandomVariable dom borel_sa rv_X}
             (srv : FiniteRangeFunction rv_X) : list (event dom) :=
    map (preimage_singleton rv_X) srv_vals.
  
  Definition SimpleExpectation
             (rv_X : Ts -> R)
             {rv:RandomVariable dom borel_sa rv_X}
             {srv : FiniteRangeFunction rv_X} : R :=
    list_sum (map (fun v => Rmult v (ps_P (preimage_singleton rv_X v)))
                  (nodup Req_EM_T srv_vals)).

  
  Lemma srv_nodup_preimage_list_union
        {Td}
        {cod:SigmaAlgebra Td}
        {has_pre:HasPreimageSingleton cod}
        dec
        {rv_X : Ts -> Td}
        {rv: RandomVariable dom cod rv_X}
        (srv : FiniteRangeFunction rv_X) :
    event_equiv (list_union (map (preimage_singleton rv_X) (nodup dec srv_vals)))  Ω .
  Proof.
    intros x.
    unfold Ω.
    split; trivial; intros _.
    unfold list_union.
    generalize (srv_vals_complete x); intros HH2.
    simpl; red; trivial.
    simpl.
    eexists.
    split.
    - apply in_map.
      apply nodup_In.
      apply srv_vals_complete.
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
        {posrv :PositiveRandomVariable x} 
        {srv : FiniteRangeFunction x} :
    SimpleExpectation x = 0 ->
    ps_P (preimage_singleton x 0) = 1.
  Proof.
    intros.
    unfold SimpleExpectation in H.
    apply list_sum_all_pos_zero_all_zero in H.
    - generalize (event_disjoint_preimage_disj x (nodup Req_EM_T srv_vals) (NoDup_nodup _ _))
      ; intros HH1.
      generalize (srv_nodup_preimage_list_union Req_EM_T srv)
      ; intros HH2.
      generalize (ps_list_disjoint_union Prts _ HH1)
      ; intros HH3.
      rewrite HH2 in HH3.
      rewrite ps_one in HH3.
      clear HH1 HH2.
      assert (nd:NoDup (nodup Req_EM_T srv_vals)) by (apply NoDup_nodup).
      induction (nodup Req_EM_T srv_vals); simpl in *; [lra | ].
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
        specialize (posrv x1).
        apply Rle_ge.
        now apply Rmult_le_pos.
      + rewrite H1, ps_none.
        lra.
  Qed.
  

  Lemma nodup_scaled (c : R) (srv_vals : list R) :
    c <> 0 -> map (fun v : R => c * v) (nodup Req_EM_T srv_vals) =
            nodup Req_EM_T (map (fun v : R => c * v) srv_vals).
  Proof.
    intros.
    symmetry.
    apply nodup_map_inj; intros.
    apply Rmult_eq_reg_l in H2; trivial.
  Qed.
  
  Lemma scaleSimpleExpectation (c:R)
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : FiniteRangeFunction rv_X} : 
    (c * SimpleExpectation rv_X)%R = SimpleExpectation (rvscale c rv_X).
  Proof.
    unfold SimpleExpectation, srvscale, rvscale.
    destruct srv.
    unfold RandomVariable.srv_vals.
    simpl.
    destruct (Req_dec c 0).
    - subst.
      case_eq srv_vals.
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
      replace (nodup Req_EM_T (map (fun v : R => c * v) srv_vals)) with
          (map (fun v : R => c * v) (nodup Req_EM_T srv_vals)).
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
    sa_sigma E ->
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
        {srv : FiniteRangeFunction rv_X} : 
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

  Lemma non_empty_srv_vals 
        (rv_X : Ts -> R)
        (srv : FiniteRangeFunction rv_X) :
    NonEmpty Ts -> srv_vals <> nil.
  Proof.
    intros.
    destruct srv.
    unfold RandomVariable.srv_vals.
    assert (In (rv_X ex) srv_vals) by apply srv_vals_complete.
    intuition.
    now subst.
  Qed.

  Lemma nil_srv_vals_empty_Ts
        {rv_X : Ts -> R}
        (srv : FiniteRangeFunction rv_X) :
    srv_vals = nil -> (forall (x:Ts), False).
  Proof.
    intros.
    destruct srv.
    unfold RandomVariable.srv_vals in *; subst.
    simpl in srv_vals_complete.
    now specialize (srv_vals_complete x).
  Qed.

  Lemma list_union_srv_preimage
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        (srv : FiniteRangeFunction rv_X) :
    event_equiv (list_union (map (preimage_singleton rv_X) srv_vals))  Ω .
  Proof.
    intros x.
    unfold Ω.
    split; trivial; intros _.
    - now repeat red.
    - unfold list_union.
      generalize (srv_vals_complete x); intros HH2.
      simpl.
      eexists.
      split.
      + apply in_map.
        apply srv_vals_complete.
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

  Lemma srv_vals_nodup_preimage_disj
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : FiniteRangeFunction rv_X} :
    ForallOrdPairs event_disjoint (map (preimage_singleton rv_X) (nodup Req_EM_T srv_vals)).
  Proof.
    intros.
    apply event_disjoint_preimage_disj.
    apply NoDup_nodup.
  Qed.
  
  Lemma srv_vals_prob_1 
        (rv_X : Ts -> R)
        {rv: RandomVariable dom borel_sa rv_X}
        {srv : FiniteRangeFunction rv_X} :
    list_sum (map (fun x : R => ps_P (preimage_singleton rv_X x)) 
                  (nodup Req_EM_T srv_vals)) = 1.
  Proof.
    transitivity (list_sum (map ps_P (map (preimage_singleton rv_X) 
                                          (nodup Req_EM_T srv_vals)))).
    { now rewrite map_map. }

    generalize (ps_list_disjoint_union Prts
                                       (map (preimage_singleton rv_X) (nodup Req_EM_T srv_vals)))
    ; intros HH.
    rewrite list_sum_fold_right.
    rewrite <- HH; clear HH.
    - rewrite srv_nodup_preimage_list_union.
      apply ps_one.
    - apply srv_vals_nodup_preimage_disj.
  Qed.

  Lemma simple_random_all
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : FiniteRangeFunction rv_X} :
    event_equiv (list_union (map (preimage_singleton rv_X) srv_vals))
                Ω .   
  Proof.
    unfold  Ω, list_union, event_equiv.
    intros.
    destruct srv.
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
        (srv1 : FiniteRangeFunction rv_X1) 
        (srv2 : FiniteRangeFunction rv_X2)
        (a:R) :
    NoDup (srv_vals (FiniteRangeFunction := srv2)) ->
    ps_P (preimage_singleton rv_X1 a) =
    list_sum
      (map (fun x : R => ps_P (preimage_singleton rv_X1 a ∩ preimage_singleton rv_X2 x)) 
           (srv_vals (FiniteRangeFunction:=srv2))).
  Proof.
    intros.
    rewrite list_sum_fold_right.
    rewrite <- map_map.
    rewrite <- ps_list_disjoint_union.
    - replace (map (fun x => preimage_singleton rv_X1 a ∩ preimage_singleton rv_X2 x) srv_vals)
        with (map (event_inter (preimage_singleton rv_X1 a))
                  (map (preimage_singleton rv_X2) 
                       srv_vals)).
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
        (srv1 : FiniteRangeFunction rv_X1) 
        (srv2 : FiniteRangeFunction rv_X2)
        (a:R) :
    NoDup (srv_vals (FiniteRangeFunction := srv1)) ->
    ps_P (preimage_singleton rv_X2 a) =
    list_sum
      (map (fun x : R => ps_P (preimage_singleton rv_X1 x ∩ preimage_singleton rv_X2 a)) 
           (srv_vals (FiniteRangeFunction:=srv1))).
  Proof.
    intros.
    rewrite (prob_inter_all1 srv2 srv1 a H); intros.
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
        (srv : FiniteRangeFunction rv_X)
        (srv2 : FiniteRangeFunction rv_X2) :  
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X v))
           (nodup Req_EM_T (srv_vals (FiniteRangeFunction:=srv)))) = 
    list_sum
      (map (fun vv : R*R => 
              (fst vv) * ps_P ((preimage_singleton rv_X (fst vv)) ∩ (preimage_singleton rv_X2 (snd vv))))
           (list_prod (nodup Req_EM_T (srv_vals (FiniteRangeFunction:=srv)))
                      (nodup Req_EM_T (srv_vals (FiniteRangeFunction:=srv2))))).
  Proof.
    induction (nodup Req_EM_T (@srv_vals Ts R rv_X srv)); simpl; trivial.
    rewrite IHl.
    rewrite map_app.
    rewrite list_sum_cat.
    f_equal.
    rewrite map_map.
    simpl.
    transitivity (list_sum (List.map (fun z => a*z)
                                     (map (fun x : R => ps_P ((preimage_singleton rv_X a) ∩ (preimage_singleton rv_X2 x))) (nodup Req_EM_T (srv_vals (FiniteRangeFunction:=srv2)))))).
    - rewrite list_sum_mult_const.
      f_equal.
      rewrite map_map.
      apply (prob_inter_all1 (nodup_simple_random_variable Req_EM_T srv) (nodup_simple_random_variable Req_EM_T srv2) a); simpl; try apply NoDup_nodup.
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
        {srv1 : FiniteRangeFunction rv_X1}
        {srv2 : FiniteRangeFunction rv_X2} : 
    rv_le rv_X1 rv_X2 ->
    SimpleExpectation rv_X1 <= SimpleExpectation rv_X2.
  Proof.
    unfold rv_le, SimpleExpectation.
    intros.
    unfold event_preimage, event_singleton.
    rewrite (RefineSimpleExpectation  srv1 srv2).
    rewrite (RefineSimpleExpectation  srv2 srv1).
    generalize (@sa_sigma_inter_pts _ _ rv_X1 rv_X2 rv1 rv2); intros sa_sigma.
    destruct srv1; destruct srv2.
    unfold RandomVariable.srv_vals in *.
    replace 
      (list_sum (map
                   (fun vv : R * R =>
                      fst vv * ps_P (preimage_singleton rv_X2 (fst vv) ∩ preimage_singleton rv_X1 (snd vv)))
                   (list_prod (nodup Req_EM_T srv_vals0) (nodup Req_EM_T srv_vals)))) with
        (list_sum (map
                     (fun vv : R * R =>
                        snd vv * ps_P (preimage_singleton rv_X1 (fst vv) ∩ preimage_singleton rv_X2 (snd vv)))
                     (list_prod (nodup Req_EM_T srv_vals) (nodup Req_EM_T srv_vals0)))).
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
      rewrite list_prod_swap.
      rewrite map_map.
      
      apply Permutation_refl'.
      apply map_ext; intros [??]; simpl.
      f_equal.
      apply ps_proper.
      now rewrite event_inter_comm.
  Qed.

  Lemma sumSimpleExpectation00
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        (srv1 : FiniteRangeFunction rv_X1) 
        (srv2 : FiniteRangeFunction rv_X2) :
    (srv_vals (FiniteRangeFunction := srv2)) <> nil ->
    NoDup (srv_vals (FiniteRangeFunction := srv1)) ->
    NoDup (srv_vals (FiniteRangeFunction := srv2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X1 v))
           (srv_vals (FiniteRangeFunction := srv1))) =
    list_sum
      (map
         (fun v : R * R =>
            (fst v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (srv_vals (FiniteRangeFunction := srv1))
                    (srv_vals (FiniteRangeFunction := srv2)))).
  Proof.
    intros.
    induction (srv_vals (FiniteRangeFunction := srv1)).
    - now simpl.
    - simpl.
      invcs H0.
      rewrite IHl by trivial.
      rewrite map_app.
      rewrite list_sum_cat.
      f_equal.
      rewrite map_map.
      unfold fst, snd.
      rewrite list_sum_const_mul.
      now rewrite (prob_inter_all1 srv1 srv2 a).
  Qed.

  Lemma sumSimpleExpectation11
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}         
        (srv1 : FiniteRangeFunction rv_X1) 
        (srv2 : FiniteRangeFunction rv_X2) :
    (srv_vals (FiniteRangeFunction := srv1)) <> nil ->
    NoDup (srv_vals (FiniteRangeFunction := srv1)) ->
    NoDup (srv_vals (FiniteRangeFunction := srv2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X2 v))
           (srv_vals (FiniteRangeFunction := srv2))) =
    list_sum
      (map
         (fun v : R * R =>
            (snd v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (srv_vals (FiniteRangeFunction := srv1))
                    (srv_vals (FiniteRangeFunction := srv2)))).
  Proof.
    intros.
    induction (srv_vals (FiniteRangeFunction := srv2)).
    - rewrite list_prod_nil_r.
      now simpl.
    - rewrite list_prod_swap.
      simpl.
      rewrite list_prod_swap.
      repeat rewrite map_map.
      simpl.
      invcs H1.
      rewrite IHl by trivial.
      rewrite map_app.
      repeat rewrite map_map.
      simpl.
      rewrite list_sum_cat.
      f_equal.
      rewrite list_sum_const_mul.
      now rewrite (prob_inter_all2 srv1 srv2 a).
  Qed.
  
  Lemma sumSimpleExpectation0
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}         
        (srv1 : FiniteRangeFunction rv_X1) 
        (srv2 : FiniteRangeFunction rv_X2) :
    (srv_vals (FiniteRangeFunction := srv2)) <> nil ->
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X1 v))
           (nodup Req_EM_T (srv_vals (FiniteRangeFunction := srv1)))) =
    list_sum
      (map
         (fun v : R * R =>
            (fst v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (nodup Req_EM_T (srv_vals (FiniteRangeFunction := srv1))) 
                    (nodup Req_EM_T (srv_vals (FiniteRangeFunction := srv2))))).
  Proof.
    intros.
    apply (sumSimpleExpectation00 (nodup_simple_random_variable Req_EM_T srv1) (nodup_simple_random_variable Req_EM_T srv2)); simpl; try apply NoDup_nodup.
    now apply nodup_not_nil.
  Qed.


  Lemma sumSimpleExpectation1
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}         
        (srv1 : FiniteRangeFunction rv_X1) 
        (srv2 : FiniteRangeFunction rv_X2) :
    (srv_vals (FiniteRangeFunction := srv1)) <> nil ->
    list_sum
      (map (fun v : R => v * ps_P (preimage_singleton rv_X2 v))
           (nodup Req_EM_T (srv_vals (FiniteRangeFunction := srv2)))) =
    list_sum
      (map
         (fun v : R * R =>
            (snd v) *
            ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
         (list_prod (nodup Req_EM_T (srv_vals (FiniteRangeFunction := srv1))) 
                    (nodup Req_EM_T (srv_vals (FiniteRangeFunction := srv2))))).
  Proof.
    intros.
    apply (sumSimpleExpectation11 (nodup_simple_random_variable Req_EM_T srv1) (nodup_simple_random_variable Req_EM_T srv2)); simpl; try apply NoDup_nodup.
    now apply nodup_not_nil.
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


  Existing Instance Equivalence_pullback.
  Existing Instance EqDec_pullback.
  
  Lemma sumSimpleExpectation_nempty
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        {srv1 : FiniteRangeFunction rv_X1} 
        {srv2 : FiniteRangeFunction rv_X2} :
    @srv_vals Ts R rv_X1 srv1 <> nil -> 
    @srv_vals Ts R rv_X2 srv2 <> nil ->
    (SimpleExpectation rv_X1) + (SimpleExpectation rv_X2)%R =
    SimpleExpectation (rvplus rv_X1 rv_X2) (srv:=srvplus _ _).
  Proof.
    unfold SimpleExpectation; intros.
    generalize (sumSimpleExpectation0 srv1 srv2 H0); intros.
    generalize (sumSimpleExpectation1 srv1 srv2 H); intros.   
    generalize (@sa_sigma_inter_pts _ _ rv_X1 rv_X2). intro sa_sigma.
    destruct srv1.
    destruct srv2.
    unfold RandomVariable.srv_vals in *; intros.
    unfold srvplus.
    simpl.
    unfold event_singleton, event_preimage.
    transitivity (list_sum
                    (map (fun v : R*R => (fst v + snd v) * ps_P
                                                          (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
                         (list_prod (nodup Req_EM_T srv_vals) (nodup Req_EM_T srv_vals0)))).
    - rewrite H1.
      rewrite H2.
      rewrite <-list_sum_map_add.
      f_equal.
      apply map_ext.
      intros.
      lra.
    - clear H1 H2.
      assert (HH:forall x y : R * R, {x = y} + {x <> y})
        by apply (pair_eqdec (H:=Req_EM_T) (H0:=Req_EM_T)).
      
      transitivity (list_sum
                      (map
                         (fun v : R * R => (fst v + snd v) * ps_P (preimage_singleton rv_X1 (fst v) ∩ preimage_singleton rv_X2 (snd v)))
                         (nodup HH (list_prod srv_vals srv_vals0)))).
      + f_equal.
        f_equal.
        symmetry.
        apply list_prod_nodup.
      + transitivity (list_sum
                        (map (fun v : R => v * ps_P (preimage_singleton (rvplus rv_X1 rv_X2) v))
                             (nodup Req_EM_T (map (fun ab : R * R => fst ab + snd ab) (nodup HH (list_prod srv_vals srv_vals0)))))).
        * generalize (NoDup_nodup HH (list_prod srv_vals srv_vals0)).
          assert (Hcomplete:forall x y, In (rv_X1 x, rv_X2 y) (nodup HH (list_prod srv_vals srv_vals0))).
          { intros.
            apply nodup_In.
            apply in_prod; eauto.
          }
          revert Hcomplete.
          generalize (nodup HH (list_prod srv_vals srv_vals0)). (* clear. *)
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
             specialize (Hnnil _ H2).
             specialize (Hequiv _ H2).
             
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
                       rewrite H4 in inxx; trivial
                       ; destruct p; simpl; eauto.
                       destruct inxx.
                       +++ eexists.
                           split; [left; reflexivity | ]; simpl.
                           invcs H5; tauto.
                       +++ eexists.
                           split.
                           *** right.
                               apply in_map.
                               apply H5.
                           *** simpl.
                               tauto.
                ** apply event_disjoint_preimage_disj_pairs.
                   generalize (quotient_bucket_NoDup sums_same l H1); rewrite Forall_forall; eauto.
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

  Lemma not_in_srv_vals_event_none
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv:FiniteRangeFunction rv_X} :
    forall (x:R), ~ (In x srv_vals) ->
             event_equiv (preimage_singleton rv_X x) event_none.
  Proof.
    destruct srv.
    unfold RandomVariable.srv_vals.
    repeat red; intros.
    unfold preimage_singleton, pre_event_singleton, pre_event_preimage; simpl.
    unfold pre_event_none.
    split; intros; subst; intuition.
  Qed.

  Lemma SimpleExpectation_simpl_incl 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        (srv:FiniteRangeFunction rv_X)
        (l:list R)
        (lincl : incl srv_vals l) :
    SimpleExpectation rv_X (srv:=srv) = SimpleExpectation rv_X (srv:=(FiniteRangeFunction_enlarged srv l lincl)).
  Proof.
    unfold SimpleExpectation; simpl.
    unfold event_preimage, event_singleton.
    generalize (incl_front_perm_nodup _ l srv_vals lincl); intros HH.
    
    destruct HH as [l2 HH].
    rewrite (list_sum_perm_eq 
               (map (fun v : R => v * ps_P (preimage_singleton rv_X v)) (nodup Req_EM_T l))
               (map (fun v : R => v * ps_P (preimage_singleton rv_X v)) ((nodup Req_EM_T srv_vals) ++ (nodup Req_EM_T l2 )))).
    - rewrite map_app.
      rewrite list_sum_cat.
      replace (list_sum
                 (map (fun v : R => v * ps_P (preimage_singleton rv_X v))
                      (nodup Req_EM_T srv_vals))) with 
          ((list_sum
              (map (fun v : R => v * ps_P (preimage_singleton rv_X v))
                   (nodup Req_EM_T srv_vals))) + 0) at 1 by lra.
      f_equal.
      rewrite <- (list_sum_map_zero (nodup Req_EM_T l2)).
      f_equal.
      apply map_ext_in; intros.
      rewrite (not_in_srv_vals_event_none rv_X).
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

End SimpleExpectation.
Section EventRestricted.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (Prts: ProbSpace dom).

  Lemma event_restricted_SimpleExpectation P (pf1 : ps_P P = 1) pf (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f} 
        {srv : FiniteRangeFunction f} :
    @SimpleExpectation _ _ Prts f rv srv = 
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
             {srv : FiniteRangeFunction rv_X}
             (dec:forall x, {P x} + {~ P x}) :=
    rvscale (if (Req_EM_T (ps_P P) 0) then 0 else
               ((SimpleExpectation  ((rvmult rv_X (EventIndicator dec)))) / (ps_P P)))
            (EventIndicator dec).

  Instance gen_simple_conditional_expectation_scale_rv (P : event dom)
           (rv_X : Ts -> R)
           {rv : RandomVariable dom borel_sa rv_X}
           {srv : FiniteRangeFunction rv_X}
           (dec:forall x, {P x} + {~ P x}) :
    RandomVariable dom borel_sa  (gen_simple_conditional_expectation_scale P rv_X dec).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    apply rvscale_rv; now apply EventIndicator_rv.    
  Qed.

  Instance gen_simple_conditional_expectation_scale_simpl (P : event dom)
           (rv_X : Ts -> R)
           {rv : RandomVariable dom borel_sa rv_X}
           {srv : FiniteRangeFunction rv_X}
           (dec:forall x, {P x} + {~ P x}) :
    FiniteRangeFunction (gen_simple_conditional_expectation_scale P rv_X dec).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    apply srvscale; apply EventIndicator_srv.
  Defined.

  Definition with_index_simple {A} (l:list A) : list (nat*A)
    := (combine (seq 0 (length l)) l).

  Definition gen_SimpleConditionalExpectation
             (rv_X : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X}
             {srv : FiniteRangeFunction rv_X}
             (l : list dec_sa_event) :=
    fold_right rvplus (const 0)
               (map
                  (fun ev => gen_simple_conditional_expectation_scale (dsa_event ev) rv_X (dsa_dec ev))
                  l).

  Instance gen_SimpleConditionalExpectation_simpl
           (rv_X : Ts -> R)
           {rv : RandomVariable dom borel_sa rv_X}
           {srv : FiniteRangeFunction rv_X}
           (l : list dec_sa_event) :
    FiniteRangeFunction (gen_SimpleConditionalExpectation rv_X l).
  Proof.
    unfold gen_SimpleConditionalExpectation.
    induction l; simpl.
    - apply srvconst.
    - apply srvplus.
      + apply gen_simple_conditional_expectation_scale_simpl.
      + apply IHl.
  Defined.

  Global Instance gen_simple_conditional_expectation_rv 
           (rv_X : Ts -> R)
           {rv:RandomVariable dom borel_sa rv_X}
           {srv : FiniteRangeFunction rv_X}
           (l : list dec_sa_event) :
    RandomVariable dom borel_sa (gen_SimpleConditionalExpectation rv_X l).
  Proof.
    unfold gen_SimpleConditionalExpectation.
    induction l; simpl; typeclasses eauto.
    Qed.

  Definition simple_conditional_expectation_scale_coef (c : R)
             (rv_X rv_X2 : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X}
             {rv2 : RandomVariable dom borel_sa rv_X2}
             {srv : FiniteRangeFunction rv_X}
             {srv2 : FiniteRangeFunction rv_X2} : R :=
    if Req_EM_T (ps_P (preimage_singleton rv_X2 c)) 0 then 0 else
      ((SimpleExpectation 
          (rvmult rv_X
                  (point_preimage_indicator rv_X2 c)))
         / (ps_P (preimage_singleton rv_X2 c))).

  Definition SimpleConditionalExpectation_list
             (rv_X1 rv_X2 : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X1}
             {rv : RandomVariable dom borel_sa rv_X2}
             {srv1 : FiniteRangeFunction rv_X1}
             {srv2 : FiniteRangeFunction rv_X2}
    := map (fun c => (rvscale (simple_conditional_expectation_scale_coef c rv_X1 rv_X2)
                              (point_preimage_indicator rv_X2 c)))
           (nodup Req_EM_T (srv_vals (FiniteRangeFunction:=srv2))).

  Definition SimpleConditionalExpectation
             (rv_X1 rv_X2 : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X1}
             {rv : RandomVariable dom borel_sa rv_X2}
             {srv1 : FiniteRangeFunction rv_X1} 
             {srv2 : FiniteRangeFunction rv_X2} :=
    fold_right rvplus (const 0)
               (SimpleConditionalExpectation_list rv_X1 rv_X2).

  Lemma SimpleConditionalExpectation_list_rv  
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}                          
        {srv1 : FiniteRangeFunction rv_X1}
        {srv2 : FiniteRangeFunction rv_X2} :
    Forall (RandomVariable dom borel_sa) (SimpleConditionalExpectation_list rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation_list.
    induction srv_vals; simpl.
    - constructor.
    - match_destr.
      constructor; trivial.
      typeclasses eauto.
  Defined.

  Lemma SimpleConditionalExpectation_list_simple  
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}                          
        {srv1 : FiniteRangeFunction rv_X1}
        {srv2 : FiniteRangeFunction rv_X2} :
    Forallt FiniteRangeFunction (SimpleConditionalExpectation_list rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation_list.
    induction srv_vals; simpl.
    - constructor.
    - match_destr.
      constructor; trivial.
      typeclasses eauto.
  Defined.

  Instance SimpleConditionalExpectation_rv
           (rv_X1 rv_X2 : Ts -> R)
           {rv1 : RandomVariable dom borel_sa rv_X1}
           {rv2 : RandomVariable dom borel_sa rv_X2}                          
           {srv1 : FiniteRangeFunction rv_X1}
           {srv2 : FiniteRangeFunction rv_X2}
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
           {srv1 : FiniteRangeFunction rv_X1}
           {srv2 : FiniteRangeFunction rv_X2}
    : FiniteRangeFunction (SimpleConditionalExpectation rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation; simpl.
    generalize (SimpleConditionalExpectation_list_simple rv_X1 rv_X2).
    induction (SimpleConditionalExpectation_list rv_X1 rv_X2); intros HH; simpl.
    - typeclasses eauto.
    - invcs HH.
      apply srvplus; auto.
  Qed.

  Lemma SimpleExpectation_pre_EventIndicator
        {P : pre_event Ts}
        (sa_P:sa_sigma P)
        (dec: forall x, {P x} + {~ P x}) :
    SimpleExpectation (EventIndicator dec)
                      (rv:=EventIndicator_pre_rv _ dec sa_P)
                      (srv:=EventIndicator_pre_srv dec)
    = ps_P (exist _ P sa_P).
  Proof.
    unfold EventIndicator_srv.
    unfold SimpleExpectation.
    unfold srv_vals.
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
    unfold EventIndicator_srv.
    unfold SimpleExpectation.
    unfold srv_vals.
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
           {srv : RandomVariable dom borel_sa rv_X}
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
           {srv : FiniteRangeFunction rv_X}
           (l : list dec_sa_event) :
    FiniteRangeFunction (fold_rvplus_prod_indicator rv_X l).
  Proof.
    unfold fold_rvplus_prod_indicator.
    induction l; simpl; typeclasses eauto.
  Defined.

  Lemma SimpleExpectation_rv_irrel 
        {rv_X : Ts -> R}
        (rv1 : RandomVariable dom borel_sa rv_X)
        (rv2 : RandomVariable dom borel_sa rv_X)
        {srv:FiniteRangeFunction rv_X} :
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
        (srv1 srv2:FiniteRangeFunction rv_X):
    SimpleExpectation rv_X (rv:=rv1) (srv:=srv1) = SimpleExpectation rv_X (rv:=rv2) (srv:=srv2).
  Proof.
    rewrite (SimpleExpectation_rv_irrel rv1 rv2).
    assert (lincl1:incl (srv_vals (FiniteRangeFunction:=srv1)) (srv_vals (FiniteRangeFunction:=srv1)++(srv_vals (FiniteRangeFunction:=srv2)))).
    { apply incl_appl.
      reflexivity.
    }
    assert (lincl2:incl (srv_vals (FiniteRangeFunction:=srv2)) (srv_vals (FiniteRangeFunction:=srv1)++(srv_vals (FiniteRangeFunction:=srv2)))).
    { apply incl_appr.
      reflexivity.
    }
    rewrite (SimpleExpectation_simpl_incl _ _ lincl1).
    rewrite (SimpleExpectation_simpl_incl _ _ lincl2).
    trivial.
  Qed.

  Lemma SimpleExpectation_const c srv : SimpleExpectation (const c) (srv:=srv) = c.
  Proof.
    rewrite (SimpleExpectation_pf_irrel _ (srvconst c)).
    unfold SimpleExpectation; simpl.
    unfold preimage_singleton, pre_event_preimage, pre_event_singleton, const.
    erewrite ps_proper.
    - erewrite ps_one.
      lra.
    - unfold Ω, pre_Ω.
      repeat red; intros; simpl; intuition.
  Qed.
  
  Lemma scaleSimpleExpectation' (c:R)
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : FiniteRangeFunction rv_X} 
        {rv' : RandomVariable dom borel_sa (rvscale c rv_X)} 
        {srv' : FiniteRangeFunction (rvscale c rv_X)} : 
    SimpleExpectation (rv:=rv') (srv:=srv') (rvscale c rv_X) = (c * SimpleExpectation rv_X)%R.
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
    now apply (RandomVariable_proper dom borel_sa rv_X1 rv_X2 eqq).
  Qed.

  Program Instance FiniteRangeFunction_transport
          {rv_X1 rv_X2:Ts->R}
          (srv1:FiniteRangeFunction rv_X1)
          (eqq:rv_eq rv_X1 rv_X2) :
    FiniteRangeFunction rv_X2
    := { srv_vals := srv_vals }.
  Next Obligation.
    rewrite <- (eqq x).
    apply srv_vals_complete.
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
        (srv1:FiniteRangeFunction rv_X1)
        (eqq:rv_eq rv_X1 rv_X2) :
    SimpleExpectation rv_X1 = SimpleExpectation rv_X2 (rv:=RandomVariable_transport eqq) (srv:=FiniteRangeFunction_transport srv1 eqq).
  Proof.
    unfold SimpleExpectation.
    simpl.
    induction srv_vals; simpl; trivial.
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
        {srv1:FiniteRangeFunction rv_X1}
        {srv2:FiniteRangeFunction rv_X2}:
    rv_eq rv_X1 rv_X2 ->
    SimpleExpectation rv_X1 = SimpleExpectation rv_X2.
  Proof.
    intros eqq.
    rewrite (SimpleExpectation_transport srv1 eqq).
    apply SimpleExpectation_pf_irrel.
  Qed.

  Lemma gen_SimpleConditionalExpectation_ext (x y:Ts->R)
        {rvx : RandomVariable dom borel_sa x}
        {rvy : RandomVariable dom borel_sa y}
        {srvx : FiniteRangeFunction x}
        {srvy : FiniteRangeFunction y}          
        (l : list dec_sa_event) :
      rv_eq x y ->
      rv_eq (gen_SimpleConditionalExpectation x l)
            (gen_SimpleConditionalExpectation y l).
    Proof.
      repeat red; intros.
      unfold gen_SimpleConditionalExpectation.
      f_equal.
      apply map_ext; intros.
      unfold gen_simple_conditional_expectation_scale.
      match_destr.
      do 2 f_equal.
      apply SimpleExpectation_ext.
      now rewrite H.
    Qed.

  Lemma sumSimpleExpectation
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        {srv1 : FiniteRangeFunction rv_X1} 
        {srv2 : FiniteRangeFunction rv_X2} :
    (SimpleExpectation rv_X1) + (SimpleExpectation rv_X2)%R = 
    SimpleExpectation (rvplus rv_X1 rv_X2).
  Proof.
    assert (H:incl (@srv_vals _ _ _ srv1) (0::(@srv_vals _ _ _ srv1)))
      by (red; simpl; tauto).
    rewrite (SimpleExpectation_simpl_incl srv1 _ H).
    assert (H0:incl (@srv_vals _ _ _ srv2) (0::(@srv_vals _ _ _ srv2)))
      by (red; simpl; tauto).
    rewrite (SimpleExpectation_simpl_incl srv2 _ H0).
    rewrite sumSimpleExpectation_nempty; simpl; trivial; try congruence.
    apply SimpleExpectation_pf_irrel.
  Qed.

  Lemma sumSimpleExpectation'
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        {srv1 : FiniteRangeFunction rv_X1} 
        {srv2 : FiniteRangeFunction rv_X2}
        {rv': RandomVariable dom borel_sa (rvplus rv_X1 rv_X2)}
        {srv' : FiniteRangeFunction (rvplus rv_X1 rv_X2)} :
    SimpleExpectation (rv:=rv') (srv:=srv') (rvplus rv_X1 rv_X2) =
    (SimpleExpectation rv_X1) + (SimpleExpectation rv_X2)%R.
  Proof.
    rewrite sumSimpleExpectation.
    apply SimpleExpectation_pf_irrel.
  Qed.

  Lemma expectation_indicator_sum0 
        (rv_X : Ts -> R)
        (rv : RandomVariable dom borel_sa rv_X)
        {srv : FiniteRangeFunction rv_X}
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
    - unfold ListAdd.map_dep_obligation_2.
      rewrite IHl by (simpl in *; intuition).
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
           (srvs : Forallt FiniteRangeFunction l) :
    FiniteRangeFunction (fold_right rvplus (const 0) l).
  Proof.
    induction l; simpl.
    - typeclasses eauto.
    - invcs srvs.
      apply srvplus; eauto.
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
        (srvs : Forallt FiniteRangeFunction l) :
    SimpleExpectation (fold_right rvplus (const 0) l) (rv:=very_specific_fold_right_rv_because_barry_waiting _ rvs) (srv:=fr_plus0_simple _ srvs) =
    list_sum (Forallt_map (fun x pf => SimpleExpectation x (rv:=fst pf) (srv:=snd pf)) (Forallt_conj (Forall_Forallt rvs) srvs)).
  Proof.
    dependent induction srvs; simpl.
    - erewrite SimpleExpectation_pf_irrel. 
      apply SimpleExpectation_const.
    - rewrite <- IHsrvs by trivial.
      rewrite sumSimpleExpectation; trivial.
      apply SimpleExpectation_pf_irrel.
  Qed.

  Lemma SimpleExpectation_fold_rvplus' (l : list (Ts -> R))
        {rv : RandomVariable dom borel_sa (fold_right rvplus (const 0) l)}
        {srv : FiniteRangeFunction (fold_right rvplus (const 0) l)}
        (rvs : Forall (RandomVariable dom borel_sa) l) 
        (srvs : Forallt FiniteRangeFunction l) :
    SimpleExpectation (fold_right rvplus (const 0) l) (rv:=rv) (srv:=srv) =
    list_sum (Forallt_map (fun x pf => SimpleExpectation x (rv:=fst pf) (srv:=snd pf)) (Forallt_conj (Forall_Forallt rvs) srvs)).
  Proof.
    generalize (SimpleExpectation_fold_rvplus l); intros HH.
    rewrite (SimpleExpectation_pf_irrel _ (fr_plus0_simple l srvs)).
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
        {srv : FiniteRangeFunction rv_X}
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
          unfold ListAdd.map_dep_obligation_2.
          f_equal.
          now rewrite IHl.
        * now invcs is_disj.
  Qed.
  
  Lemma expectation_indicator_sum 
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : FiniteRangeFunction rv_X}
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
        {srv : FiniteRangeFunction rv_X}
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
        {srv : FiniteRangeFunction rv_X}
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
        {srv : FiniteRangeFunction rv_X}
        (dec:forall x, {P x} + {~ P x}) :
    SimpleExpectation (gen_simple_conditional_expectation_scale P rv_X dec) =
    SimpleExpectation (rvmult rv_X (EventIndicator dec)).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    erewrite scaleSimpleExpectation'.
    match_destr.
    - field_simplify.
      unfold SimpleExpectation.
      induction srv_vals; simpl; trivial.
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
        {srv : FiniteRangeFunction rv_X}
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

  Lemma srv_md_gen_simple_scale
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : FiniteRangeFunction rv_X}
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
        {srv : FiniteRangeFunction rv_X}
        (l : list dec_sa_event)
        (ispart: is_partition_list (map dsa_event l)) :
    SimpleExpectation rv_X =
    SimpleExpectation
      (gen_SimpleConditionalExpectation rv_X l).
  Proof.
    unfold gen_SimpleConditionalExpectation.
    rewrite (expectation_indicator_sum rv_X l ispart).
    rewrite (SimpleExpectation_fold_rvplus') with (rvs:=rv_md_gen_simple_scale rv_X l)
                                                  (srvs:=srv_md_gen_simple_scale rv_X l).
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
          (srv : FiniteRangeFunction rv_X)
    : list dec_sa_event
    :=
      map (fun c => Build_dec_sa_event
                   (preimage_singleton rv_X c) _)
          (nodup Req_EM_T srv_vals).
  Next Obligation.
    intros ?.
    apply Req_EM_T.
  Defined.

  
  Lemma induced_gen_ispart
        {rv_X : Ts -> R}
        {rv:RandomVariable dom borel_sa rv_X}
        (srv : FiniteRangeFunction rv_X) :
    is_partition_list (map dsa_event (induced_sigma_generators srv)).
  Proof. 
    unfold is_partition_list.
    unfold induced_sigma_generators, event_preimage, event_singleton.
    rewrite map_map; simpl.
    split.
    - apply event_disjoint_preimage_disj.
      apply NoDup_nodup.
    - destruct srv.
      unfold RandomVariable.srv_vals.
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
        {srv1 : FiniteRangeFunction rv_X1}
        {srv2 : FiniteRangeFunction rv_X2} :

    SimpleExpectation (SimpleConditionalExpectation rv_X1 rv_X2) = SimpleExpectation rv_X1.
  Proof.
    symmetry.
    rewrite  (gen_conditional_tower_law rv_X1 (induced_sigma_generators srv2))
    ; trivial ; [| apply induced_gen_ispart].
    unfold gen_SimpleConditionalExpectation, gen_simple_conditional_expectation_scale.
    unfold SimpleConditionalExpectation, SimpleConditionalExpectation_list.
    unfold simple_conditional_expectation_scale_coef.
    unfold point_preimage_indicator,induced_sigma_generators.
    unfold event_preimage, event_singleton, EventIndicator.
    apply SimpleExpectation_ext.
    intros x.
    rewrite map_map; simpl.
    induction (nodup Req_EM_T srv_vals); simpl; trivial.
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
             {srv1 : FiniteRangeFunction rv_X1}
             {srv2 : FiniteRangeFunction rv_X2} : Prop :=
    forall (c2:R), In c2 (srv_vals (FiniteRangeFunction:=srv2)) ->
                   exists (c1:R), In c1 (srv_vals (FiniteRangeFunction:=srv1)) /\
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
             {srv : FiniteRangeFunction rv_X}
             (l : list (event dom)) : Prop :=
    is_partition_list l ->
    forall (p:event dom),
      In p l ->
      exists c, (In c srv_vals) /\
                    event_sub p (preimage_singleton rv_X c).
  
(*
  Lemma in_list_in_partition_union {T} (x:event T) l d :
    In x l -> 
    in_partition_union (list_collection l d) x.
  Proof.
    intros inn.
    unfold in_partition_union.
    unfold list_collection.
    apply (In_nth l x d) in inn.
    destruct inn as [n [nlen neqq]].
    exists ((fun y => if y == n then x else event_none)%nat).
    unfold event_none.
    split.
    - unfold sub_partition; intros.
      match_destr.
      + red in e; subst.
        left; reflexivity.
      + right.
        intros ?; unfold event_none.
        tauto.
    - unfold union_of_collection.
      intros y; simpl.
      split.
      + intros [??].
        match_destr_in H.
        tauto.
      + intros.
        exists n.
        match_destr.
        congruence.
  Qed.
*)

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
        {srv1 : FiniteRangeFunction rv_X1}
        {srv2 : FiniteRangeFunction rv_X2} 
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
    unfold rv_eq, rvplus.
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
        {srv1 : FiniteRangeFunction rv_X1}
        {srv2 : FiniteRangeFunction rv_X2} 
        (l : list dec_sa_event) :
    is_partition_list (map dsa_event l) ->
    partition_measurable rv_X1 (map dsa_event l) ->
    rv_eq (gen_SimpleConditionalExpectation (rvmult rv_X1 rv_X2) l)
          (rvmult rv_X1 (gen_SimpleConditionalExpectation rv_X2 l  )).
  Proof.
    unfold partition_measurable, event_preimage, event_singleton.
    intros is_part meas.
    unfold gen_SimpleConditionalExpectation.
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
             destruct meas as [c [cinn ceq]].
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

        {srv1 : FiniteRangeFunction rv_X1}
        {srv2 : FiniteRangeFunction rv_X2} 
        {srv3 : FiniteRangeFunction rv_X3} :     
    
    simple_sigma_measurable rv_X1 rv_X3 ->
    rv_eq (SimpleConditionalExpectation (rvmult rv_X1 rv_X2) rv_X3)
          (rvmult rv_X1 (SimpleConditionalExpectation rv_X2 rv_X3)).
  Proof.
    generalize (gen_conditional_scale_measurable rv_X1 rv_X2 
                                                 (induced_sigma_generators srv3)
                                                 (induced_gen_ispart srv3)).
    intros.
    cut_to H.
    - unfold gen_SimpleConditionalExpectation in H.
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
      + induction  (nodup Req_EM_T srv_vals); simpl; [reflexivity |].
        apply rvplus_proper; eauto.
        apply rvscale_proper; try reflexivity.
        match_destr.
        f_equal.
        apply SimpleExpectation_pf_irrel.
      + induction  (nodup Req_EM_T srv_vals); simpl; [reflexivity |].
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

End SimpleConditionalExpectation.  
