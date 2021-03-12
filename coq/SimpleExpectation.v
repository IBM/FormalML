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

  Definition simpleRandomVariable_partition_image 
             {rv_X : Ts -> R}
             {rrv : RandomVariable dom borel_sa rv_X}
             (srv : SimpleRandomVariable rv_X) : list (event Ts) :=
    map (event_preimage rv_X) (map event_singleton srv_vals).
  
  Definition SimpleExpectation
             (rv_X : Ts -> R)
             {srv : SimpleRandomVariable rv_X} : R :=
    list_sum (map (fun v => Rmult v (ps_P (event_preimage rv_X (event_singleton v)))) 
                  (nodup Req_EM_T srv_vals)).


  Lemma srv_nodup_preimage_list_union {Td} dec
        {rv_X : Ts -> Td}         
        (srv : SimpleRandomVariable rv_X) :
    event_equiv (list_union (map (fun (x : Td) (omega : Ts) => rv_X omega = x) (nodup dec srv_vals)))  Ω .
  Proof.
    intros x.
    unfold Ω.
    split; trivial; intros _.
    unfold list_union.
    generalize (srv_vals_complete x); intros HH2.
    exists (fun (omega : Ts) => rv_X  omega = rv_X x).
    split; trivial.
    apply in_map_iff.
    exists (rv_X x).
    split; trivial.
    now apply nodup_In.
  Qed.

  Lemma event_disjoint_preimage_disj {A B}
        f l :
    NoDup l ->
    ForallOrdPairs event_disjoint (map (fun (x : B) (omega : A) => f omega = x) l).
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

  Lemma srv_vals_nodup_preimage_sa  
        {rv_X : Ts -> R}
        (rv: RandomVariable dom borel_sa rv_X)
        (srv : SimpleRandomVariable rv_X) :
    forall x : event Ts,
      In x (map (fun (x0 : R) (omega : Ts) => rv_X omega = x0) (nodup Req_EM_T srv_vals)) -> sa_sigma x.
  Proof.
    intros.
    apply in_map_iff in H.
    destruct H as [y [? yin]]; subst.
    apply nodup_In in yin.
    apply sa_le_pt; intros.
    apply borel_sa_preimage2; intros.
    now apply rv_preimage.
  Qed.

  Lemma SimplePosExpectation_zero_pos_0helper (x : Ts -> R) l :
    ~ In 0 l ->
    Forall (fun x : R => x = 0)
           (map (fun v : R => v * ps_P (event_preimage x (event_singleton v))) l) ->
    
    fold_right Rplus 0 (map ps_P (map (fun (x0 : R) (omega : Ts) => x omega = x0) l)) = 0.
  Proof.
    induction l; simpl; intros inn Fl; trivial.
    invcs Fl.
    rewrite IHl; try tauto.
    destruct (Rmult_integral _ _ H1).
    - tauto.
    - unfold event_preimage, event_singleton in H.
      rewrite H.
      lra.
  Qed.

  Lemma SimplePosExpectation_zero_pos
        (x : Ts -> R)
        {rv : RandomVariable dom borel_sa x}
        {posrv :PositiveRandomVariable x} 
        {srv : SimpleRandomVariable x} :
    SimpleExpectation x = 0 ->
    ps_P (fun omega => x omega = 0) = 1.
  Proof.
    intros.
    unfold SimpleExpectation in H.
    apply list_sum_all_pos_zero_all_zero in H.
    - generalize (event_disjoint_preimage_disj x (nodup Req_EM_T srv_vals) (NoDup_nodup _ _))
      ; intros HH1.
      generalize (srv_nodup_preimage_list_union Req_EM_T srv)
      ; intros HH2.
      generalize (ps_list_disjoint_union Prts _ (srv_vals_nodup_preimage_sa _ srv) HH1)
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
      generalize (ps_pos  (event_preimage x (event_singleton x0))); intros HH.
      cut_to HH; [| eapply sa_singleton; eauto].
      destruct (classic_event_none_or_has ((event_preimage x (event_singleton x0)))).
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
        {srv : SimpleRandomVariable rv_X} : 
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
        apply ps_proper; red; intros.
        unfold event_preimage, event_singleton.
        split; intros.
        * now subst.
        * apply Rmult_eq_reg_l in H0; trivial.
      + now apply nodup_scaled.
  Qed.

  Lemma RefineSimpleExpectation0
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        (E : event Ts) (l : list R):
    sa_sigma E ->
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v)) l) = 
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v /\ E omega)) l)
    + 
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v /\ 
                                               (event_complement E) omega)) l).
  Proof.
    intro sa_sigmaE.
    rewrite <-list_sum_map_add.
    rewrite (map_ext (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v))
                     (fun t : R =>
                        t * ps_P (fun omega : Ts => rv_X omega = t /\ E omega) +
                        t * ps_P (fun omega : Ts => rv_X omega = t /\ event_complement E omega))); trivial.
    intros.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rmult_eq_compat_l with (r2 := (ps_P (fun omega : Ts => rv_X omega = a /\ E omega) +
                                           ps_P (fun omega : Ts => rv_X omega = a /\ 
                                                                event_complement E omega))); trivial.
    apply ps_total; trivial.
    - now apply sa_singleton.
    - now apply sa_complement.
    - apply event_disjoint_complement.
    - apply event_union_complement.
      now apply sa_dec.
  Qed.

  Lemma oppSimpleExpectation
        (rv_X : Ts -> R)
        {srv : SimpleRandomVariable rv_X} : 
    (- SimpleExpectation rv_X)%R = SimpleExpectation (rvopp rv_X).
  Proof.
    replace (- SimpleExpectation rv_X) with (-1 * SimpleExpectation rv_X) by lra.
    apply scaleSimpleExpectation.
  Qed.

  Lemma rvminus_equiv (f g : Ts -> R) :
    (forall (r:R),  
        (event_equiv (fun omega : Ts => f omega -  g omega <= r)
                     (fun omega : Ts => rvminus f g omega <= r))).
  Proof.
    intros r x.
    unfold rvminus, rvplus, rvopp, rvscale.
    split; lra.
  Qed.

  Lemma equiv_rvminus_eq (f g : Ts -> R) :
    event_equiv (fun omega => f omega = g omega)
                (fun omega => rvminus f g omega = 0).
    unfold rvminus, rvplus, rvopp, rvscale.
    intro x.
    split; lra.
  Qed.

  Class NonEmpty (A : Type) :=
    ex : A.

  Lemma non_empty_srv_vals 
        (rv_X : Ts -> R)
        (srv : SimpleRandomVariable rv_X) :
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
        (srv : SimpleRandomVariable rv_X) :
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
        (srv : SimpleRandomVariable rv_X) :
    event_equiv (list_union (map (fun (x : R) (omega : Ts) => rv_X omega = x) srv_vals))  Ω .
  Proof.
    intros x.
    unfold Ω.
    split; trivial; intros _.
    unfold list_union.
    generalize (srv_vals_complete x); intros HH2.
    exists (fun (omega : Ts) => rv_X  omega = rv_X x).
    split; trivial.
    apply in_map_iff.
    exists (rv_X x).
    split; trivial.
  Qed.


  Lemma event_disjoint_preimage_and_disj {A B}
        f P l :
    NoDup l ->
    ForallOrdPairs event_disjoint (map (fun (x : B) (omega : A) => f omega = x /\ P omega) l).
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

  Lemma event_disjoint_and_preimage_disj {A B}
        f P l :
    NoDup l ->
    ForallOrdPairs event_disjoint (map (fun (x : B) (omega : A) => P omega /\ f omega = x) l).
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
  
  Lemma event_disjoint_preimage_disj_pairs {A B}
        f1 f2 l :
    NoDup l ->
    ForallOrdPairs event_disjoint 
                   (map (fun (x : B*B) (omega : A) => f1 omega = fst x /\ f2 omega = snd x) l).
  Proof.
    induction l; simpl; intros nd.
    - constructor.
    - invcs nd.
      constructor; auto.
      rewrite Forall_map.
      rewrite Forall_forall.
      intros x xin e ein.
      destruct ein.
      rewrite H.
      rewrite H0.
      rewrite <- pair_equal_spec.
      replace (fst a, snd a) with a.
      replace (fst x, snd x) with x.
      congruence.
      now destruct x; unfold fst, snd.
      now destruct a; unfold fst, snd.
  Qed.

  Lemma srv_vals_nodup_preimage_disj
        {rv_X : Ts -> R}
        (srv : SimpleRandomVariable rv_X) :
    ForallOrdPairs event_disjoint (map (fun (x : R) (omega : Ts) => rv_X omega = x) (nodup Req_EM_T srv_vals)).
  Proof.
    intros.
    apply event_disjoint_preimage_disj.
    apply NoDup_nodup.
  Qed.

  
  Lemma srv_vals_prob_1 
        {rv_X : Ts -> R}
        (rv: RandomVariable dom borel_sa rv_X)                      
        (srv : SimpleRandomVariable rv_X) :
    list_sum (map (fun x : R => ps_P (fun omega : Ts => rv_X  omega = x)) 
                  (nodup Req_EM_T srv_vals)) = 1.
  Proof.
    transitivity (list_sum (map ps_P (map (fun x : R => (fun omega : Ts => rv_X  omega = x)) 
                                          (nodup Req_EM_T srv_vals)))).
    { now rewrite map_map. }

    generalize (ps_list_disjoint_union Prts
                                       (map (fun (x : R) (omega : Ts) => rv_X omega = x) (nodup Req_EM_T srv_vals)))
    ; intros HH.
    rewrite list_sum_fold_right.
    rewrite <- HH; clear HH.
    - rewrite srv_nodup_preimage_list_union.
      apply ps_one.
    - apply srv_vals_nodup_preimage_sa; trivial.
    - apply srv_vals_nodup_preimage_disj.
  Qed.

  (*
  Definition IndependentRandomVariables
        (rv1 rv2: RandomVariable prts cod) : Prop :=
    forall (B: event Td), 
      sa_sigma B -> 
      independent (event_preimage (rv_X (RandomVariable:=rv1)) B)
                  (event_preimage (rv_X (RandomVariable:=rv2)) B).

   Lemma independent_rv_at_point
     (rv1 rv2: RandomVariable dom borel_sa) :
   (* IndependentRandomVariables rv1 rv2 -> *)
     forall (a a0 : R),
       ps_P (fun omega : Ts => rv_X (RandomVariable := rv1) omega = a) * 
       ps_P (fun omega : Ts => rv_X (RandomVariable := rv2) omega = a0) =
       ps_P (fun omega : Ts => rv_X (RandomVariable := rv1) omega = a /\ 
                               rv_X (RandomVariable := rv2) omega = a0).
   Proof.     

   *)

  Lemma simple_random_all
        {rv_X : Ts -> R}
        (srv : SimpleRandomVariable rv_X) :
    event_equiv (list_union (map (fun (x : R) (omega : Ts) => rv_X omega = x) srv_vals))
                Ω .   
  Proof.
    unfold  Ω, list_union, event_equiv.
    intros.
    destruct srv.
    split; intros.
    - intuition.
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
        (srv1 : SimpleRandomVariable rv_X1) 
        (srv2 : SimpleRandomVariable rv_X2)
        (a:R) :
    NoDup (srv_vals (SimpleRandomVariable := srv2)) ->
    ps_P (fun omega : Ts => rv_X1 omega = a) =
    list_sum
      (map (fun x : R => ps_P (fun omega : Ts => rv_X1 omega = a /\ rv_X2 omega = x)) 
           (srv_vals (SimpleRandomVariable:=srv2))).
  Proof.
    intros.
    rewrite list_sum_fold_right.
    rewrite <- map_map.
    rewrite <- ps_list_disjoint_union.
    - replace (map (fun (x : R) (omega : Ts) => rv_X1 omega = a /\ rv_X2 omega = x) srv_vals)
        with (map (event_inter (fun omega => rv_X1 omega = a))
                  (map (fun x => (fun omega => rv_X2 omega = x)) 
                       srv_vals)).
      + rewrite <- event_inter_list_union_distr.
        rewrite simple_random_all.
        now rewrite event_inter_true_r.
      + unfold event_inter.
        now rewrite map_map.
    - intros.
      apply in_map_iff in H0.
      destruct H0.
      destruct H0.
      rewrite <- H0.
      eapply sa_sigma_inter_pts; trivial.
    - now apply event_disjoint_and_preimage_disj.
  Qed.
  
  Lemma prob_inter_all2
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}                               
        (srv1 : SimpleRandomVariable rv_X1) 
        (srv2 : SimpleRandomVariable rv_X2)
        (a:R) :
    NoDup (srv_vals (SimpleRandomVariable := srv1)) ->
    ps_P (fun omega : Ts => rv_X2 omega = a) =
    list_sum
      (map (fun x : R => ps_P (fun omega : Ts => rv_X1 omega = x /\ rv_X2 omega = a)) 
           (srv_vals (SimpleRandomVariable:=srv1))).
  Proof.
    intros.
    generalize (prob_inter_all1 srv2 srv1 a H); intros.
    rewrite map_ext with 
        (g := (fun x : R => ps_P (fun omega : Ts => rv_X2 omega = a /\ 
                                              rv_X1 omega = x))); trivial.
    intros.
    now apply ps_proper.
  Qed.

  Lemma RefineEvent
        (E : event Ts) (lE : list (event Ts)):
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
        (srv : SimpleRandomVariable rv_X)
        (srv2 : SimpleRandomVariable rv_X2) :  
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X  omega = v))
           (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv)))) = 
    list_sum
      (map (fun vv : R*R => 
              (fst vv) * ps_P (fun omega : Ts => rv_X  omega = fst vv /\
                                              rv_X2 omega = snd vv))
           (list_prod (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv)))
                      (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv2))))).
  Proof.
    induction (nodup Req_EM_T (@srv_vals Ts R rv_X srv)); simpl; trivial.
    rewrite IHl.
    rewrite map_app.
    rewrite list_sum_cat.
    f_equal.
    rewrite map_map.
    simpl.
    transitivity (list_sum (List.map (fun z => a*z)
                                     (map (fun x : R => ps_P (fun omega : Ts => (rv_X ) omega = a /\ (rv_X2) omega = x)) (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv2)))))).
    - rewrite list_sum_mult_const.
      f_equal.
      rewrite map_map.
      apply (prob_inter_all1 (nodup_simple_random_variable Req_EM_T srv) (nodup_simple_random_variable Req_EM_T srv2) a); simpl; try apply NoDup_nodup.
    - now rewrite map_map.
  Qed.

  Lemma zero_prob_or_witness (E : event Ts) :
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
      unfold event_none; intuition.
      eauto.
  Qed.

  Lemma SimpleExpectation_le 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}                               
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} : 
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
                      fst vv * ps_P (fun omega : Ts => rv_X2 omega = fst vv /\ rv_X1 omega = snd vv))
                   (list_prod (nodup Req_EM_T srv_vals0) (nodup Req_EM_T srv_vals)))) with
        (list_sum (map
                     (fun vv : R * R =>
                        snd vv * ps_P (fun omega : Ts => rv_X1 omega = fst vv /\ rv_X2 omega = snd vv))
                     (list_prod (nodup Req_EM_T srv_vals) (nodup Req_EM_T srv_vals0)))).
    - apply list_sum_le; intros.
      assert ((ps_P (fun omega : Ts => rv_X1 omega = fst a /\ rv_X2 omega = snd a)) = 0 \/
              fst a <= snd a).
      + destruct (Req_EM_T (ps_P (fun omega : Ts => rv_X1 omega = fst a /\ rv_X2 omega = snd a)) 0).
        * intuition.
        * apply zero_prob_or_witness in n.
          right.
          destruct n.
          destruct H0.
          rewrite <- H0; rewrite <- H1.
          apply H.
      + destruct H0.
        rewrite H0; lra.
        apply Rmult_le_compat_r.
        apply ps_pos.
        apply sa_sigma.
        trivial.
    - apply list_sum_Proper.
      rewrite list_prod_swap.
      rewrite map_map.
      rewrite (map_ext 
                 (fun x : R * R =>
                    snd (snd x, fst x) *
                    ps_P
                      (fun omega : Ts =>
                         rv_X1 omega = fst (snd x, fst x) /\ 
                         rv_X2 omega = snd (snd x, fst x)))
                 (fun vv : R * R =>
                    fst vv * ps_P (fun omega : Ts => rv_X2 omega = fst vv /\ 
                                                  rv_X1 omega = snd vv))).
      apply Permutation.Permutation_refl.
      intros.
      unfold snd.
      f_equal.
      apply ps_proper.
      unfold event_equiv; intros.
      intuition.
  Qed.

  Lemma sumSimpleExpectation00
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}
        (srv1 : SimpleRandomVariable rv_X1) 
        (srv2 : SimpleRandomVariable rv_X2) :
    (srv_vals (SimpleRandomVariable := srv2)) <> nil ->
    NoDup (srv_vals (SimpleRandomVariable := srv1)) ->
    NoDup (srv_vals (SimpleRandomVariable := srv2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X1 omega = v))
           (srv_vals (SimpleRandomVariable := srv1))) =
    list_sum
      (map
         (fun v : R * R =>
            (fst v) *
            ps_P (fun omega : Ts => rv_X1 omega = fst v /\ rv_X2 omega = snd v))
         (list_prod (srv_vals (SimpleRandomVariable := srv1))
                    (srv_vals (SimpleRandomVariable := srv2)))).
  Proof.
    intros.
    induction (srv_vals (SimpleRandomVariable := srv1)).
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
        (srv1 : SimpleRandomVariable rv_X1) 
        (srv2 : SimpleRandomVariable rv_X2) :
    (srv_vals (SimpleRandomVariable := srv1)) <> nil ->
    NoDup (srv_vals (SimpleRandomVariable := srv1)) ->
    NoDup (srv_vals (SimpleRandomVariable := srv2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X2 omega = v))
           (srv_vals (SimpleRandomVariable := srv2))) =
    list_sum
      (map
         (fun v : R * R =>
            (snd v) *
            ps_P (fun omega : Ts => rv_X1 omega = fst v /\ 
                                 rv_X2 omega = snd v))
         (list_prod (srv_vals (SimpleRandomVariable := srv1))
                    (srv_vals (SimpleRandomVariable := srv2)))).
  Proof.
    intros.
    induction (srv_vals (SimpleRandomVariable := srv2)).
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
        (srv1 : SimpleRandomVariable rv_X1) 
        (srv2 : SimpleRandomVariable rv_X2) :
    (srv_vals (SimpleRandomVariable := srv2)) <> nil ->
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X1 omega = v))
           (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv1)))) =
    list_sum
      (map
         (fun v : R * R =>
            (fst v) *
            ps_P (fun omega : Ts => rv_X1 omega = fst v /\ rv_X2 omega = snd v))
         (list_prod (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv1))) 
                    (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv2))))).
  Proof.
    intros.
    apply (sumSimpleExpectation00 (nodup_simple_random_variable Req_EM_T srv1) (nodup_simple_random_variable Req_EM_T srv2)); simpl; try apply NoDup_nodup.
    now apply nodup_not_nil.
  Qed.


  Lemma sumSimpleExpectation1
        {rv_X1 rv_X2 : Ts -> R}
        {rv1: RandomVariable dom borel_sa rv_X1}
        {rv2: RandomVariable dom borel_sa rv_X2}         
        (srv1 : SimpleRandomVariable rv_X1) 
        (srv2 : SimpleRandomVariable rv_X2) :
    (srv_vals (SimpleRandomVariable := srv1)) <> nil ->
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X2 omega = v))
           (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv2)))) =
    list_sum
      (map
         (fun v : R * R =>
            (snd v) *
            ps_P (fun omega : Ts => rv_X1 omega = fst v /\ 
                                 rv_X2 omega = snd v))
         (list_prod (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv1))) 
                    (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv2))))).
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
        (c d: R) :
    c <> d ->
    event_disjoint (fun omega => rv_X  omega = c)
                   (fun omega => rv_X  omega = d).
  Proof.
    unfold event_disjoint.
    congruence.
  Qed.

  Lemma preimage_point_pairs_disjoint
        (rv_X1 rv_X2: Ts -> R)
        (c1 c2 d1 d2: R) :
    (c1 <> d1) \/ (c2 <> d2) ->
    event_disjoint (event_inter (fun omega => rv_X1 omega = c1)
                                (fun omega => rv_X2 omega = c2))
                   (event_inter (fun omega => rv_X1 omega = d1)
                                (fun omega => rv_X2 omega = d2)).
  Proof.
    intros.
    unfold event_disjoint, event_inter; intros.
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

  Lemma list_union_sub_cover {T} (l : list (event T)) (P Q: event T) :
    event_union (list_union l) Q = Ω -> event_disjoint P Q ->
    (forall (e:event T), In e l -> event_inter P e = e ) ->
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
        {srv1 : SimpleRandomVariable rv_X1} 
        {srv2 : SimpleRandomVariable rv_X2} :
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
                    (map (fun v : R*R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X1 omega = fst v /\ rv_X2 omega = snd v))
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
                         (fun v : R * R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X1 omega = fst v /\ rv_X2 omega = snd v))
                         (nodup HH (list_prod srv_vals srv_vals0)))).
      + f_equal.
        f_equal.
        symmetry.
        apply list_prod_nodup.
      + transitivity (list_sum
                        (map (fun v : R => v * ps_P (fun omega : Ts => rv_X1 omega + rv_X2 omega = v))
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
                             (fun v : R * R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X1 omega = fst v /\ rv_X2 omega = snd v))
                             (concat (quotient sums_same l)))).
          { apply list_sum_Proper. apply Permutation.Permutation_map. symmetry. apply unquotient_quotient.
          } 
          rewrite concat_map.
          rewrite list_sum_map_concat.
          rewrite map_map.

          transitivity (
              list_sum
                (map (fun v : R => v * ps_P (fun omega : Ts => rv_X1 omega + rv_X2 omega = v))
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
             transitivity ((fst p + snd p) * ps_P (fun omega : Ts => rv_X1 omega = fst p /\ rv_X2 omega = snd p) +
                           list_sum
                             (map
                                (fun v : R * R => (fst p + snd p) * ps_P (fun omega : Ts => rv_X1 omega = fst v /\ rv_X2 omega = snd v))
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
                    list_sum (map (fun x : R * R => ps_P (fun omega : Ts => rv_X1 omega = fst x /\ rv_X2 omega = snd x)) (p::a))); [reflexivity |].
                rewrite list_sum_fold_right.
                rewrite <- map_map.
                rewrite <- ps_list_disjoint_union.
                ** apply ps_proper; intros x.
                   unfold list_union.
                   split.
                   --- intros [e [ein ex]].
                       apply in_map_iff in ein.
                       destruct ein as [ee [? eein]]; subst.
                       destruct ex as [ex1 ex2].
                       rewrite ex1, ex2.
                       apply Hequiv; eauto.
                   --- intros.
                       exists (fun (omega : Ts) => rv_X1 omega = rv_X1 x /\ rv_X2 omega = rv_X2 x).
                       split; [| tauto].
                       apply in_map_iff.
                       exists (rv_X1 x, rv_X2 x).
                       split; [reflexivity | ].
                       assert (Hin:In (rv_X1 x, rv_X2 x) l) by apply Hcomplete.
                       destruct (quotient_in sums_same _ _ Hin) as [xx [xxin inxx]].
                       rewrite <- (all_different_same_eq sums_same (quotient sums_same l) xx (p::a) (rv_X1 x, rv_X2 x) (fst p, snd p)); simpl; trivial.
                       destruct p; eauto.
                ** intros.
                   apply in_map_iff in H3.
                   destruct H3 as [xx [? xxin]]; subst.
                   apply sa_sigma; trivial.
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
        {rv_X : Ts -> R}
        (srv:SimpleRandomVariable rv_X) :
    forall (x:R), ~ (In x srv_vals) ->
             event_equiv (fun omega => rv_X omega = x) event_none.
  Proof.
    destruct srv.
    unfold RandomVariable.srv_vals.
    red; intros.
    unfold event_none.
    intuition.
    rewrite <- H0 in H.
    intuition.
  Qed.

  Lemma SimpleExpectation_simpl_incl 
        {rv_X : Ts -> R}
        (srv:SimpleRandomVariable rv_X)
        (l:list R)
        (lincl : incl srv_vals l) :
    SimpleExpectation rv_X (srv:=srv) = SimpleExpectation rv_X (srv:=(SimpleRandomVariable_enlarged srv l lincl)).
  Proof.
    unfold SimpleExpectation; simpl.
    unfold event_preimage, event_singleton.
    generalize (incl_front_perm_nodup _ l srv_vals lincl); intros HH.
    
    destruct HH as [l2 HH].
    rewrite (list_sum_perm_eq 
               (map (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v)) (nodup Req_EM_T l))
               (map (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v)) ((nodup Req_EM_T srv_vals) ++ (nodup Req_EM_T l2 )))).
    - rewrite map_app.
      rewrite list_sum_cat.
      replace (list_sum
                 (map (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v))
                      (nodup Req_EM_T srv_vals))) with 
          ((list_sum
              (map (fun v : R => v * ps_P (fun omega : Ts => rv_X omega = v))
                   (nodup Req_EM_T srv_vals))) + 0) at 1 by lra.
      f_equal.
      rewrite <- (list_sum_map_zero (nodup Req_EM_T l2)).
      f_equal.
      apply map_ext_in; intros.
      rewrite (not_in_srv_vals_event_none srv).
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

Section SimpleConditionalExpectation.

  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Definition gen_simple_conditional_expectation_scale (P : event Ts)
             (rv_X : Ts -> R)
             {srv : SimpleRandomVariable rv_X}
             (dec:forall x, {P x} + {~ P x})        
             (sap: sa_sigma P) :=
    rvscale (if (Req_EM_T (ps_P P) 0) then 0 else
               ((SimpleExpectation (rvmult rv_X (EventIndicator dec))) / (ps_P P)))
            (EventIndicator dec).

  Instance gen_simple_conditional_expectation_scale_rv (P : event Ts)
           (rv_X : Ts -> R)
           {srv : SimpleRandomVariable rv_X}
           (dec:forall x, {P x} + {~ P x})        
           (sap: sa_sigma P) :  
    RandomVariable dom borel_sa  (gen_simple_conditional_expectation_scale P rv_X dec sap).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    apply rvscale_rv; now apply EventIndicator_rv.    
  Qed.

  Instance gen_simple_conditional_expectation_scale_simpl (P : event Ts)
           (rv_X : Ts -> R)
           {srv : SimpleRandomVariable rv_X}
           (dec:forall x, {P x} + {~ P x})        
           (sap: sa_sigma P) :
    SimpleRandomVariable (gen_simple_conditional_expectation_scale P rv_X dec sap).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    apply srvscale; apply EventIndicator_srv.
  Defined.

  Definition with_index_simple {A} (l:list A) : list (nat*A)
    := (combine (seq 0 (length l)) l).


  Definition gen_SimpleConditionalExpectation
             (rv_X : Ts -> R)
             {srv : SimpleRandomVariable rv_X}
             (l : list dec_sa_event) :=
    fold_right rvplus (const 0)
               (map
                  (fun ev => gen_simple_conditional_expectation_scale (dsa_event ev) rv_X (dsa_dec ev) (dsa_sa ev))
                  l).

  Instance gen_SimpleConditionalExpectation_simpl
           (rv_X : Ts -> R)
           {srv : SimpleRandomVariable rv_X}
           (l : list dec_sa_event) :
    SimpleRandomVariable (gen_SimpleConditionalExpectation rv_X l).
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
           {srv : SimpleRandomVariable rv_X}
           (l : list dec_sa_event) :
    RandomVariable dom borel_sa (gen_SimpleConditionalExpectation rv_X l).
  Proof.
    unfold gen_SimpleConditionalExpectation.
    induction l; simpl; typeclasses eauto.
    Qed.

  Definition simple_conditional_expectation_scale_coef (c : R)
             (rv_X rv_X2 : Ts -> R)
             {srv : SimpleRandomVariable rv_X}
             {srv2 : SimpleRandomVariable rv_X2} : R :=
    if Req_EM_T (ps_P (event_preimage rv_X2 (event_singleton c))) 0 then 0 else
      ((SimpleExpectation 
          (rvmult rv_X
                  (point_preimage_indicator rv_X2 c)))
         / (ps_P (event_preimage rv_X2 (event_singleton c)))).

  Definition SimpleConditionalExpectation_list
             (rv_X1 rv_X2 : Ts -> R)
             {srv1 : SimpleRandomVariable rv_X1}
             {srv2 : SimpleRandomVariable rv_X2}
    := map (fun c => (rvscale (simple_conditional_expectation_scale_coef c rv_X1 rv_X2)
                              (point_preimage_indicator rv_X2 c)))
           (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv2))).

  Definition SimpleConditionalExpectation
             (rv_X1 rv_X2 : Ts -> R)
             {srv1 : SimpleRandomVariable rv_X1} 
             {srv2 : SimpleRandomVariable rv_X2} :=
    fold_right rvplus (const 0)
               (SimpleConditionalExpectation_list rv_X1 rv_X2).

  Lemma SimpleConditionalExpectation_list_simple  
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}                          
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} :
    Forallt SimpleRandomVariable (SimpleConditionalExpectation_list rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation_list.
    induction srv_vals; simpl.
    - constructor.
    - match_destr.
      constructor; trivial.
      typeclasses eauto.
  Defined.

  Instance SimpleConditionalExpectation_simple
           (rv_X1 rv_X2 : Ts -> R)
           {rv1 : RandomVariable dom borel_sa rv_X1}
           {rv2 : RandomVariable dom borel_sa rv_X2}                          
           {srv1 : SimpleRandomVariable rv_X1}
           {srv2 : SimpleRandomVariable rv_X2}
    : SimpleRandomVariable (SimpleConditionalExpectation rv_X1 rv_X2).
  Proof.
    unfold SimpleConditionalExpectation; simpl.
    generalize (SimpleConditionalExpectation_list_simple rv_X1 rv_X2).
    induction (SimpleConditionalExpectation_list rv_X1 rv_X2); intros HH; simpl.
    - typeclasses eauto.
    - invcs HH.
      apply srvplus; auto.
  Qed.

  Lemma SimpleExpectation_EventIndicator 
        {P : event Ts} 
        (dec: forall x, {P x} + {~ P x}) :
    SimpleExpectation (EventIndicator dec) = ps_P P.
  Proof.
    unfold EventIndicator_srv.
    unfold SimpleExpectation.
    unfold srv_vals.
    unfold event_preimage, event_singleton.
    unfold EventIndicator.
    simpl.
    repeat match_destr; simpl; ring_simplify
    ; apply ps_proper; intros ?; match_destr; intuition.
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
        apply dsa_sa.
      + apply IHl.
  Qed.

  Instance fold_rvplus_prod_indicator_simpl
           (rv_X : Ts -> R)
           {srv : SimpleRandomVariable rv_X}
           (l : list dec_sa_event) :
    SimpleRandomVariable (fold_rvplus_prod_indicator rv_X l).
  Proof.
    unfold fold_rvplus_prod_indicator.
    induction l; simpl; typeclasses eauto.
  Defined.

  Lemma SimpleExpectation_pf_irrel 
        {rv_X : Ts -> R}
        (srv1 srv2:SimpleRandomVariable rv_X):
    SimpleExpectation rv_X (srv:=srv1) = SimpleExpectation rv_X (srv:=srv2).
  Proof.
    assert (lincl1:incl (srv_vals (SimpleRandomVariable:=srv1)) (srv_vals (SimpleRandomVariable:=srv1)++(srv_vals (SimpleRandomVariable:=srv2)))).
    { apply incl_appl.
      reflexivity.
    }
    assert (lincl2:incl (srv_vals (SimpleRandomVariable:=srv2)) (srv_vals (SimpleRandomVariable:=srv1)++(srv_vals (SimpleRandomVariable:=srv2)))).
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
    unfold event_preimage, event_singleton, const.
    erewrite ps_proper.
    - erewrite ps_one.
      lra.
    - unfold Ω.
      red; intros; intuition.
  Qed.

  Program Instance SimpleRandomVariable_transport
          {rv_X1 rv_X2:Ts->R}
          (srv1:SimpleRandomVariable rv_X1)
          (eqq:rv_eq rv_X1 rv_X2) :
    SimpleRandomVariable rv_X2
    := { srv_vals := srv_vals }.
  Next Obligation.
    rewrite <- (eqq x).
    apply srv_vals_complete.
  Qed.

  Global Instance event_preimage_proper {A B} : Proper (rv_eq ==> event_equiv ==> event_equiv) (@event_preimage A B).
  Proof.
    unfold event_preimage; intros ???????.
    rewrite H.
    apply H0.
  Qed.
  
  Lemma SimpleExpectation_transport {rv_X1 rv_X2:Ts->R}
        (srv1:SimpleRandomVariable rv_X1)
        (eqq:rv_eq rv_X1 rv_X2) :
    SimpleExpectation rv_X1 = SimpleExpectation rv_X2 (srv:=SimpleRandomVariable_transport srv1 eqq).
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
    unfold event_preimage.
    rewrite eqq.
    + reflexivity.
  Qed.
  
  Lemma SimpleExpectation_ext 
        {rv_X1 rv_X2 : Ts -> R}
        (srv1:SimpleRandomVariable rv_X1) 
        (srv2:SimpleRandomVariable rv_X2):
    rv_eq rv_X1 rv_X2 ->
    SimpleExpectation rv_X1 = SimpleExpectation rv_X2.
  Proof.
    intros eqq.
    rewrite (SimpleExpectation_transport srv1 eqq).
    apply SimpleExpectation_pf_irrel.
  Qed.

   Lemma gen_SimpleConditionalExpectation_ext (x y:Ts->R)
          {srvx : SimpleRandomVariable x}
          {srvy : SimpleRandomVariable y}          
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
        {srv1 : SimpleRandomVariable rv_X1} 
        {srv2 : SimpleRandomVariable rv_X2} :
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

  Lemma expectation_indicator_sum0 
        (rv_X : Ts -> R)
        (rv : RandomVariable dom borel_sa rv_X)
        {srv : SimpleRandomVariable rv_X}
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
      apply SimpleExpectation_const.
    - unfold ListAdd.map_dep_obligation_2.
      rewrite IHl by (simpl in *; intuition).
      rewrite <- sumSimpleExpectation; trivial.
      + apply rvmult_rv; trivial.
        apply EventIndicator_rv; trivial.
        apply dsa_sa.
      + apply fold_rvplus_prod_indicator_rv; trivial.
  Qed.
  
  Ltac se_rewrite H :=
    match type of H with
    | @SimpleExpectation _ _ _ ?x ?sx = _ =>
      match goal with
      | [|- context [@SimpleExpectation _ _ _ ?z ?sz]] =>
        rewrite (@SimpleExpectation_pf_irrel x sz sx); rewrite H
      end
    end.

  Lemma is_partition_list_nnil {T} : NonEmpty T -> ~ @is_partition_list T [].
  Proof.
    intros a [??]; unfold list_union in *; simpl in *.
    assert (HH:@Ω T a) by now compute.
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
           (srvs : Forallt SimpleRandomVariable l) :
    SimpleRandomVariable (fold_right rvplus (const 0) l).
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
  
  Lemma SimpleExpectation_fold_rvplus (l : list (Ts -> R)) 
        (rvs : Forall (RandomVariable dom borel_sa) l) 
        (srvs : Forallt SimpleRandomVariable l) :
    SimpleExpectation (fold_right rvplus (const 0) l) (srv:=fr_plus0_simple _ srvs) =
    list_sum (Forallt_map (fun x pf => SimpleExpectation x (srv:=pf)) srvs).
  Proof.
    dependent induction srvs; simpl.
    - rewrite (SimpleExpectation_ext _ (srvconst 0)).
      + now rewrite SimpleExpectation_const.
      + intros ?; congruence.
    - invcs rvs.
      rewrite <- IHsrvs by trivial.
      rewrite sumSimpleExpectation; trivial.
      + apply SimpleExpectation_pf_irrel.
      + now apply very_specific_fold_right_rv_because_barry_waiting.
  Qed.

  (*
  Lemma list_union_dec_ext {T B} (l:list dec_sa_event) pf1 pf2 (a b:B) :
    forall x, (if (list_union_dec l pf1) x then a else b) = (if (list_union_dec l pf2) x then a else b).
  Proof.
    intros.
    repeat match_destr; congruence.
  Qed.

   *)
  (*
  Lemma map_dep_ext {A B} (l:list A) (f1 f2:(forall x, In x l -> B)) :
    (forall x pf, f1 x pf = f2 x pf) ->
    map_dep l f1 = map_dep l f2.
  Proof.
    intros eqq.
    induction l; simpl; trivial.
    rewrite eqq.
    f_equal.
    apply IHl; intros.
    unfold map_dep_obligation_2.
    now rewrite eqq.
  Qed.
   *)
  
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
        destruct l0 as [? [inn ?]].
        specialize (H1 _ inn a); intuition.
      + destruct (list_union_dec l); try lra.
  Qed.

  Lemma expectation_indicator_sum_gen
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : SimpleRandomVariable rv_X}
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
        {srv : SimpleRandomVariable rv_X}
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
    unfold Ω in n.
    intuition.
  Qed.

  Lemma sub_event_prob_0
        (P1 P2 : event Ts) 
        (sap1 : sa_sigma P1)
        (sap2 : sa_sigma P2):
    ps_P P2 = 0 -> event_sub P1 P2 -> ps_P P1 = 0.
  Proof.
    intros.
    generalize (ps_sub Prts P1 P2); intros.
    cut_to H1; trivial.
    generalize (ps_pos P1); intros.
    cut_to H2; trivial.
    lra.
  Qed.
  
  Lemma indicator_prob_0
        (P : event Ts) 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : SimpleRandomVariable rv_X}
        (dec:forall x, {P x} + {~ P x})        
        (sap: sa_sigma P) 
        (a : R) :
    ps_P P = 0 -> 
    a <> 0 ->
    ps_P (fun omega : Ts => rv_X omega * (if dec omega then 1 else 0) = a) = 0.
  Proof.
    intros.
    assert (event_sub (fun omega : Ts => rv_X omega * (if dec omega then 1 else 0) = a)
                      P).
    - unfold event_sub; intros.
      destruct (dec x); trivial.
      rewrite Rmult_0_r in H1.
      lra.
    - apply sub_event_prob_0 with (P2 := P); trivial.
      assert (event_equiv (fun omega : Ts => rv_X omega * (if dec omega then 1 else 0) = a)
                          (event_inter P (event_preimage rv_X (event_singleton a)))).
      + unfold event_equiv; intros.
        unfold event_inter, event_preimage, event_singleton.
        split; intros.
        * destruct (dec x).
          -- rewrite Rmult_1_r in H2; tauto.
          -- rewrite Rmult_0_r in H2.
             lra.
        * destruct (dec x).
          -- lra.
          -- rewrite Rmult_0_r.
             tauto.
      + rewrite H2.
        apply sa_inter; trivial.
        unfold event_preimage, event_singleton.
        apply sa_le_pt.
        now apply rv_measurable.
  Qed.
  
  Lemma expectation_indicator_prob_0
        (P : event Ts) 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : SimpleRandomVariable rv_X}
        (dec:forall x, {P x} + {~ P x})        
        (sap: sa_sigma P) :
    ps_P P = 0 -> 
    SimpleExpectation (rvmult rv_X (EventIndicator dec)) = 0.
  Proof.
    unfold SimpleExpectation.
    unfold event_preimage, EventIndicator, event_singleton, rvmult.
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

  Lemma gen_simple_conditional_expectation_scale_tower (P : event Ts) 
        {rv_X : Ts -> R}
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : SimpleRandomVariable rv_X}
        (dec:forall x, {P x} + {~ P x})        
        (sap: sa_sigma P) :
    SimpleExpectation (gen_simple_conditional_expectation_scale P rv_X dec sap) =
    SimpleExpectation (rvmult rv_X (EventIndicator dec)).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    erewrite SimpleExpectation_pf_irrel.
    rewrite <- scaleSimpleExpectation.
    match_destr.
    - field_simplify.
      unfold SimpleExpectation.
      induction srv_vals; simpl; trivial.
      match_destr.
      simpl.
      rewrite <- IHl.
      unfold event_preimage, event_singleton.
      unfold EventIndicator; simpl.
      unfold rvmult.
      clear IHl.
      clear n l.
      destruct (Req_EM_T a 0).
      + subst; field.
      + rewrite indicator_prob_0; trivial.
        lra.
    - rewrite SimpleExpectation_EventIndicator.
      field; trivial.
  Qed.

  Lemma srv_md_gen_simple_scale
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {srv : SimpleRandomVariable rv_X}
        (l : list dec_sa_event) :
    Forallt SimpleRandomVariable
            (map (fun ev =>
                    gen_simple_conditional_expectation_scale 
                      (dsa_event ev) rv_X (dsa_dec ev) (dsa_sa ev))
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
        {srv : SimpleRandomVariable rv_X}
        (l : list dec_sa_event)
        (ispart: is_partition_list (map dsa_event l)) :
    SimpleExpectation rv_X =
    SimpleExpectation
      (gen_SimpleConditionalExpectation rv_X l).
  Proof.
    unfold gen_SimpleConditionalExpectation.
    rewrite (expectation_indicator_sum rv_X l ispart).
    generalize SimpleExpectation_fold_rvplus; intros.
    specialize (H (map (fun ev =>
                          gen_simple_conditional_expectation_scale (dsa_event ev) rv_X (dsa_dec ev) (dsa_sa ev))
                       l)).
    cut_to H.
    - specialize (H (srv_md_gen_simple_scale rv_X l)).
      erewrite SimpleExpectation_pf_irrel in H.
      rewrite H.
      clear H.
      f_equal.
      unfold srv_md_gen_simple_scale.
      unfold Forallt_map.
      clear ispart.
      induction l; simpl; trivial.
      f_equal.
      + unfold  gen_simple_conditional_expectation_scale.
        erewrite SimpleExpectation_pf_irrel.
        rewrite <- scaleSimpleExpectation.
        rewrite SimpleExpectation_EventIndicator.
        match_destr.
        * rewrite expectation_indicator_prob_0; trivial.
          lra.
          apply dsa_sa.
        * field; trivial.
      + apply IHl.
    - rewrite Forall_forall; intros.
      rewrite in_map_iff in H0.
      destruct H0 as [? [? eqq]].
      subst.
      typeclasses eauto.
  Qed.

  Program Definition induced_sigma_generators
          {rv_X : Ts -> R}
          {rv:RandomVariable dom borel_sa rv_X}
          (srv : SimpleRandomVariable rv_X)
    : list dec_sa_event
    :=
      map (fun c => Build_dec_sa_event
                      (event_preimage rv_X (event_singleton c)) _ _)
          (nodup Req_EM_T srv_vals).
  Next Obligation.
    unfold event_preimage, event_singleton.
    intros ?.
    apply Req_EM_T.
  Defined.
  Next Obligation.
    eapply sa_singleton; eauto.
  Qed.
  
  Lemma induced_gen_ispart
        {rv_X : Ts -> R}
        {rv:RandomVariable dom borel_sa rv_X}
        (srv : SimpleRandomVariable rv_X) :
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
        unfold Ω .
        intuition.
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
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} :

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
    unfold induced_sigma_generators_obligation_1.
    reflexivity.
  Qed.

  Definition simple_sigma_measurable 
             (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2}
             {srv1 : SimpleRandomVariable rv_X1}
             {srv2 : SimpleRandomVariable rv_X2} : Prop :=
    forall (c2:R), In c2 (srv_vals (SimpleRandomVariable:=srv2)) ->
                   exists (c1:R), In c1 (srv_vals (SimpleRandomVariable:=srv1)) /\
                                  (event_sub (event_preimage rv_X2 (event_singleton c2) )
                                             (event_preimage rv_X1 (event_singleton c1))).


  Lemma events_measurable0_b
        (l1 l2 : list (event Ts)) :
    (exists l : list (list (event Ts)),
        Forall2 (fun x y => event_equiv x (list_union y)) l1 l
        /\ Permutation (concat l) l2) ->
    (forall (p2:event Ts),
        In p2 l2 ->
        exists (p1:event Ts), (In p1 l1) /\ event_sub p2 p1).
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
    red.
    eauto.
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
             (rv_X : Ts -> Td)
             {srv : SimpleRandomVariable rv_X}
             (l : list (event Ts)) : Prop :=
    is_partition_list l ->
    forall (p:event Ts),
      In p l ->
      exists (c:Td), (In c srv_vals) /\
                    event_sub p (event_preimage rv_X (event_singleton c)).
  
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


  Lemma nth_map_default_equiv {A} {R} n (l:list A) (d1 d2:A)
        {refl:Reflexive R} :
    R d1 d2 ->
    R (nth n l d1) (nth n l d2).
  Proof.
    repeat rewrite <- nth_default_eq.
    unfold nth_default.
    match_destr.
  Qed.


  Lemma event_inter_sub_l {T:Type} (A B:event T) :
    event_sub B A -> event_equiv (event_inter A B) B.
  Proof.
    firstorder.
  Qed.

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

  
  
  Lemma expectation_const_factor_subset (c:R)
        (p : event Ts)
        (rv_X1 rv_X2 : Ts -> R)
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} 
        (sap : sa_sigma p)
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
    - rewrite (H _ p0).
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
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} 
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
             ++ apply dsa_sa.
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

        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} 
        {srv3 : SimpleRandomVariable rv_X3} :     
    
    simple_sigma_measurable rv_X1 rv_X3 ->
    rv_eq (SimpleConditionalExpectation (rvmult rv_X1 rv_X2) rv_X3)
          (rvmult rv_X1 (SimpleConditionalExpectation rv_X2 rv_X3)).
  Proof.
    generalize (gen_conditional_scale_measurable rv_X1 rv_X2 
                                                 (induced_sigma_generators srv3)
                                                 (induced_gen_ispart srv3)).
    intros.
    cut_to H.
    unfold gen_SimpleConditionalExpectation in H.
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
    rewrite H.
    reflexivity.
    unfold simple_sigma_measurable in H0.
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
