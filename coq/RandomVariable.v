Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Lub.

Require Import Utils.
Require Import NumberIso.
Require Import ProbSpace SigmaAlgebras BorelSigmaAlgebra.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".
  
Section RandomVariable.
  (* todo better type names. *)
  (* The preimage of the function X on codomain B. *)

  (* A random variable is a mapping from a pobability space to a sigma algebra. *)
  Class RandomVariable {Ts:Type} {Td:Type}
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        (cod: SigmaAlgebra Td)
        (rv_X: Ts -> Td)
    :=
      (* for every element B in the sigma algebra, 
           the preimage of rv_X on B is an event in the probability space *)
      rv_preimage: forall (B: event Td), sa_sigma B -> sa_sigma (event_preimage rv_X B).

  (*  pointwise_relation Ts eq *)
  Definition rv_eq {Ts:Type} {Td:Type} : (Ts -> Td) -> (Ts -> Td) -> Prop
     :=  pointwise_relation Ts eq.
  
   Global Instance rv_eq_equiv
          {Ts:Type} {Td:Type} :
     Equivalence (@rv_eq Ts Td).
   Proof.
     typeclasses eauto.
   Qed.
  
  Section Simple.
    Context {Ts:Type} {Td:Type}
            {dom: SigmaAlgebra Ts}
            {prts: ProbSpace dom}
            {cod: SigmaAlgebra Td}.

    Definition singleton_event {T} (m:T) := fun x => x=m.

    Class ConstantRandomVariable
          (rv_X:Ts -> Td)
      := { 
      srv_val : Td;
      srv_val_complete : forall x, rv_X x = srv_val
        }.
    
    Global Instance rvconst c : RandomVariable prts cod (const c).
    Proof.
      red; intros.
      destruct (sa_dec H c).
      - assert (event_equiv (fun _ : Ts => B c)
                            (fun _ : Ts => True)).
        red; intros.
        intuition.
        rewrite H1.
        apply sa_all.
      - assert (event_equiv (fun _ : Ts => B c)
                            event_none).
        red; intros.
        intuition.
        rewrite H1.
        apply sa_none.
  Qed.

    Global Program Instance crvconst c : ConstantRandomVariable (const c)
    := { srv_val := c }.

  Class SimpleRandomVariable
        (rv_X:Ts->Td)
    := { 
      srv_vals : list Td ;
      srv_vals_complete : forall x, In (rv_X x) srv_vals;
    }.

  Global Program Instance srvconst c : SimpleRandomVariable (const c)
    := { srv_vals := [srv_val] }.

  Program Instance nodup_simple_random_variable (dec:forall (x y:Td), {x = y} + {x <> y})
          {rv_X:Ts->Td}
          (srv:SimpleRandomVariable rv_X) : SimpleRandomVariable rv_X
    := { srv_vals := nodup dec srv_vals }.
  Next Obligation.
    apply nodup_In.
    apply srv_vals_complete.
  Qed.

  Lemma nodup_simple_random_variable_NoDup
        (dec:forall (x y:Td), {x = y} + {x <> y})
        {rv_X}
        (srv:SimpleRandomVariable rv_X) :
    NoDup (srv_vals (SimpleRandomVariable:=nodup_simple_random_variable dec srv)).
  Proof.
    simpl.
    apply NoDup_nodup.
  Qed.
  
  End Simple.

  Section Reals.
    
    Context {Ts:Type}.

    (*
    Instance BuildRealRandomVariable
             (rvx: Ts -> R)
             (pf_pre:(forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r))%R)
      : RandomVariable prts borel_sa
      := {
      rv_X := rvx ;
      rv_preimage := borel_sa_preimage rvx pf_pre
        }.
     *)

  Definition RealRandomVariable_le
        (rv_X1 rv_X2: Ts->R) : Prop :=
    forall (x:Ts), (rv_X1 x <= 
                   rv_X2 x)%R.

  Global Instance RealRandomVariable_le_pre : PreOrder RealRandomVariable_le.
  Proof.
    unfold RealRandomVariable_le.
    constructor; intros.
    - red; intros; lra.
    - red; intros.
      eapply Rle_trans; eauto.
  Qed.

  Global Instance RealRandomVariable_le_part : PartialOrder rv_eq RealRandomVariable_le.
  Proof.
    unfold RealRandomVariable_le.
    red.
    intros ??.
    split; intros eqq.
    - repeat red.
      repeat red in eqq.
      split; intros ?; rewrite eqq; lra.
    - destruct eqq as [le1 le2].
      intros y.
      specialize (le1 y).
      specialize (le2 y).
      lra.
  Qed.

  Class IndicatorRandomVariable
        (rv_X : Ts -> R) :=
    irv_binary : forall x, In (rv_X x) [0;1] .

  Context {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

    Lemma RealRandomVariable_is_real
          rv_X
          (rv:RandomVariable prts borel_sa rv_X) :
      forall r:R, sa_sigma (fun omega:Ts => (rv_X omega) <= r)%R.
    Proof.
      now rewrite borel_sa_preimage2.
    Qed.

    Global Program Instance IndicatorRandomVariableSimpl
           rv_X
           {irv: IndicatorRandomVariable rv_X} : SimpleRandomVariable rv_X
    := {srv_vals := [0;1]}.
  Next Obligation.
    apply irv.
  Qed.

  Lemma sa_singleton (c:R)
        rv_X
        {rv : RandomVariable prts borel_sa rv_X} :
    sa_sigma (event_preimage rv_X (singleton_event c)).
  Proof.
     apply sa_le_pt; intros.
     apply borel_sa_preimage2; intros.
     now apply rv_preimage.
  Qed.

  Definition EventIndicator {P : event Ts} (dec:forall x, {P x} + {~ P x}) : Ts -> R
    := fun omega => if dec omega then 1 else 0.

  Global Instance EventIndicator_rv {P : event Ts} (dec:forall x, {P x} + {~ P x})
           (sap: sa_sigma P) : RandomVariable prts borel_sa (EventIndicator dec).
  Proof.
    red; intros.
    apply borel_sa_preimage; trivial; intros.
    destruct (Rlt_dec r 0).
    - unfold EventIndicator.
      simpl.
      assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                          event_none).
      + unfold event_equiv, event_none; intros.
        destruct (dec x); lra.
      + rewrite H0; apply sa_none.
    - destruct (Rlt_dec r 1).
      + assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                            (fun omega : Ts => ~ P omega)).
        * unfold event_equiv; intros.
          destruct (dec x).
          -- split; [lra | congruence].
          -- split; [congruence | lra].
        * rewrite H0.
          now apply sa_complement.
      + assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                            (fun omega : Ts => True)).
        * unfold event_equiv; intros.
          destruct (dec x); lra.
        * rewrite H0.
          apply sa_all.
  Qed.

  Global Instance EventIndicator_indicator (P : event Ts) (dec:forall x, {P x} + {~ P x})
    : IndicatorRandomVariable (EventIndicator dec).
 Proof.
    unfold EventIndicator.
    intros x.
    simpl.
    match_destr; tauto.
  Qed.

 Global Program Instance EventIndicator_srv {P : event Ts} (dec:forall x, {P x} + {~ P x})
    : SimpleRandomVariable (EventIndicator dec) :=
     { srv_vals := [0;1] }.
  Next Obligation.
    apply EventIndicator_indicator.
  Qed.
  
  Definition point_preimage_indicator
             (rv_X:Ts -> R)
             (c:R) :=
    EventIndicator (fun x => Req_EM_T (rv_X x) c).

  Instance point_preimage_indicator_rv
           {rv_X:Ts -> R}
           (rv: RandomVariable prts borel_sa rv_X)
           (c:R) : RandomVariable prts borel_sa (point_preimage_indicator rv_X c).
  Proof.
    red; intros.
    unfold point_preimage_indicator.
    apply EventIndicator_rv; trivial.
    now apply sa_singleton.
 Qed.    
  
  Program Instance point_preimage_indicator_srv
           {rv_X:Ts -> R}
           (rv: RandomVariable prts borel_sa rv_X)
           (c:R) : SimpleRandomVariable (point_preimage_indicator rv_X c)
    := { srv_vals := [0;1] }.
  Next Obligation.
    unfold point_preimage_indicator, EventIndicator.
    destruct (Req_EM_T (rv_X x) c); intuition.
  Qed.

  Class PositiveRandomVariable
        (rv_X:Ts->R) : Prop :=
    prv : forall (x:Ts), (0 <= rv_X x)%R.

  Global Instance prvconst c (cpos:0<=c) : PositiveRandomVariable (const c).
  Proof.
    intros x.
    unfold const; trivial.
  Qed.

  (*
  Instance IndicatorRandomVariable_positive 
   *)
  
  Lemma scale_measurable_pos (f : Ts -> R) (c:posreal) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => c * (f omega) <= r)).
    Proof.
      intros.
      assert (event_equiv (fun omega : Ts => (c * f omega <= r)%R)
                          (fun omega : Ts => (f omega <= r/c)%R)).
      - red; intros.
        assert (0 < c) by apply (cond_pos c).
        split; intros.
        + unfold Rdiv.
          rewrite Rmult_comm.
          replace (f x) with (/c * (c * f x)).
          * apply  Rmult_le_compat_l; trivial; left.
            now apply Rinv_0_lt_compat.
          * field_simplify; lra.
        + replace (r) with (c * (r / c)).
          * apply  Rmult_le_compat_l; trivial; now left.
          * field; lra.
      - rewrite H0.
        apply H.
    Qed.

  Lemma scale_measurable_neg (f : Ts -> R) (c:posreal) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => (-c) * (f omega) <= r)).
    Proof.
      intros.
      assert (event_equiv (fun omega : Ts => ((-c) * f omega <= r)%R)
                          (fun omega : Ts => (c * f omega >= -r)%R)).
      - red; intros.
        assert (0 < c) by apply (cond_pos c).
        lra.
      - rewrite H0.
        apply sa_le_ge.
        now apply scale_measurable_pos.
    Qed.

  Lemma constant_measurable (c:R) :
    forall (r:R),  sa_sigma (fun omega : Ts => c <= r).
  Proof.
    intros.
    destruct (Rle_dec c r).
    - assert (event_equiv (fun _ : Ts => c <= r)
                          (fun _ : Ts => True)).
      red; intros.
      intuition.
      rewrite H.
      apply sa_all.
    - assert (event_equiv (fun _ : Ts => c <= r)
                          event_none).
      red; intros.
      intuition.
      rewrite H.
      apply sa_none.
  Qed.

  Lemma scale_measurable (f : Ts -> R) (c:R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => c * (f omega) <= r)).
    Proof.
      intros.
      destruct (Rle_dec c 0).
      - destruct (Rle_lt_or_eq_dec c 0); trivial.
        + assert (0 < -c) by lra.
          assert (event_equiv (fun omega : Ts => c * f omega <= r)
                              (fun omega : Ts => (- - c) * f omega <= r)).
          red; intros.
          lra.
          rewrite H1.
          now apply (scale_measurable_neg f (mkposreal _ H0)).
        + assert (event_equiv (fun omega : Ts => c * f omega <= r)
                              (fun _ => 0 <= r)).
          red; intros.
          subst; lra.
          rewrite H0.
          apply constant_measurable.
      - assert (0 < c) by lra.
        now apply (scale_measurable_pos f (mkposreal _ H0)).
   Qed.

      
    Definition rvscale (c:R) (rv_X : Ts -> R) :=
      fun omega => c * (rv_X omega).

    Global Instance rvscale_rv (c: R) (rv_X : Ts -> R) 
             (rv : RandomVariable prts borel_sa rv_X) 
      : RandomVariable prts borel_sa (rvscale c rv_X).
   Proof.
     red; intros.
     apply borel_sa_preimage2; trivial; intros.
     apply scale_measurable.     
     now apply RealRandomVariable_is_real.
   Qed.
   
   Global Instance positive_scale_prv (c:posreal) 
        (rv_X : Ts -> R)
        {prv : PositiveRandomVariable rv_X} :
    PositiveRandomVariable (rvscale c rv_X).
  Proof.
    red; intros.
    red in prv.
    assert (0 < c) by apply (cond_pos c).
    unfold rvscale.
    specialize (prv x).
    replace (0) with (c*0) by lra.    
    apply Rmult_le_compat_l; trivial.
    now left.
 Qed.

End Reals.

End RandomVariable.

Section prob.
  Local Open Scope R.
  Local Open Scope prob.

  Context {Ts:Type} {Td:Type}
          {dom: SigmaAlgebra Ts}
          {prts: ProbSpace dom}
          {cod: SigmaAlgebra Td}
          {rv_X: Ts -> Td}.

  Definition Pr 
             (S:Td->Prop)
    := ps_P (fun x:Ts => S (rv_X x)).

  Definition independent (A B:Td->Prop) :=
    Pr (A ∩ B) = (Pr A * Pr B).

  Notation "a ⊥ b" := (independent a b) (at level 50) : prob. (* \perp *)

  Lemma pr_all : Pr Ω = R1.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_proper _ Ω) by firstorder. 
    apply ps_all.
  Qed.
  
  Lemma pr_none : Pr ∅ = R0.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_proper _ ∅) by firstorder.
    apply ps_none.
  Qed.


End prob.

Section SimpleExpectation.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Definition simpleRandomVariable_partition_image 
             {rv_X : Ts -> R}
             {rrv : RandomVariable Prts borel_sa rv_X}
             (srv : SimpleRandomVariable rv_X) : list (event Ts) :=
    map (event_preimage rv_X) (map singleton_event srv_vals).
    
  Definition SimpleExpectation
             (rv_X : Ts -> R)
             {srv : SimpleRandomVariable rv_X} : R :=
    list_sum (map (fun v => Rmult v (ps_P (event_preimage rv_X (singleton_event v)))) 
                  (nodup Req_EM_T srv_vals)).

  Global Program Instance scale_constant_random_variable (c: R)
         (rv_X : Ts -> R)
         {rrv : RandomVariable Prts borel_sa rv_X}
         {crv:ConstantRandomVariable rv_X} : ConstantRandomVariable (rvscale c rv_X)
    := { srv_val := Rmult c srv_val }.
  Next Obligation.
    destruct crv.
    unfold rvscale.
    now rewrite (srv_val_complete0 x).
  Qed.

  Global Program Instance srvscale (c: R)
         (rv_X : Ts -> R)
         {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvscale c rv_X)
    := { srv_vals := map (fun v => Rmult c v) srv_vals }.
  Next Obligation.
    destruct srv.
    rewrite in_map_iff.
    exists (rv_X x).
    split; trivial.
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
    unfold srv_vals.
    simpl.
    destruct (Req_dec c 0).
    - subst.
      case_eq srv_vals0.
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
      replace (nodup Req_EM_T (map (fun v : R => c * v) srv_vals0)) with
              (map (fun v : R => c * v) (nodup Req_EM_T srv_vals0)).
      + rewrite map_map.
        apply map_ext; intros.
        rewrite <- Rmult_assoc.
        f_equal.
        apply ps_proper; red; intros.
        unfold event_preimage, singleton_event.
        split; intros.
        * now subst.
        * apply Rmult_eq_reg_l in H0; trivial.
      + now apply nodup_scaled.
  Qed.

  Lemma RefineSimpleExpectation0
        (rv_X : Ts -> R)
        {rv : RandomVariable Prts borel_sa rv_X}
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
    rewrite list_sum_map.
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
    - now apply (sa_singleton Prts).
    - now apply sa_complement.
    - apply event_disjoint_complement.
    - apply event_union_complement.
      apply classic_event_lem.
  Qed.


  Lemma sa_sigma_inter_pts
         (rv_X1 rv_X2 : Ts -> R)
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}         
         (c1 c2 : R) :
    sa_sigma (fun omega : Ts => rv_X1 omega = c1 /\ 
                                rv_X2 omega = c2).
  Proof.
    apply sa_inter.
    - now apply (sa_singleton Prts).
    - now apply (sa_singleton Prts).
  Qed.

  Require Import Classical_Prop.
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

  Lemma Ropp_measurable (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => - (f omega) <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => - (f omega) <= r)
                        (fun omega : Ts => (f omega) >= -r)).
    unfold event_equiv; intros.
    lra.
    rewrite H0.
    now apply sa_le_ge.
  Qed.

  Definition rvopp (rv_X : Ts -> R) := rvscale (-1) rv_X.

  Global Instance rvopp_rv (rv_X : Ts -> R) 
             {rv : RandomVariable Prts borel_sa rv_X}
      : RandomVariable Prts borel_sa (rvopp rv_X).
   Proof.
     red; intros.
     apply borel_sa_preimage2; trivial; intros.
     unfold rvopp.
     apply scale_measurable.     
     now apply (RealRandomVariable_is_real Prts).
   Qed.

   Global Instance srvopp 
             {rv_X : Ts -> R}
             {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvopp rv_X)
     := srvscale (-1) rv_X.    

 Global Instance rvopp_proper : Proper (rv_eq ==> rv_eq ) rvopp.
 Proof.
   unfold rv_eq, rvopp, Proper, rvscale, respectful, pointwise_relation.
   intros x y eqq z.
   now rewrite eqq.
 Qed.

  Lemma oppSimpleExpectation
        (rv_X : Ts -> R)
        {srv : SimpleRandomVariable rv_X} : 
    (- SimpleExpectation rv_X)%R = SimpleExpectation (rvopp rv_X).
  Proof.
    replace (- SimpleExpectation rv_X) with (-1 * SimpleExpectation rv_X) by lra.
    apply scaleSimpleExpectation.
  Qed.

  Lemma sum_measurable (f g : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => g omega <= r)) ->    
    (forall (r:R),  sa_sigma (fun omega : Ts => (f omega) + (g omega) <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => f omega + g omega <= r)
                        (event_complement (fun omega : Ts => f omega + g omega > r))).
    - unfold event_equiv, event_complement; intros.
      lra.
    - rewrite H1.
      assert (event_equiv 
                (fun omega : Ts => (f omega) + (g omega) > r)
                (union_of_collection
                   (fun (n:nat) => 
                      event_inter
                        (fun omega : Ts => f omega > r - Qreals.Q2R (iso_b n))
                        (fun omega : Ts => g omega > Qreals.Q2R (iso_b n))))).
     + unfold event_equiv, union_of_collection, event_inter; intros.
       split; intros.
       * assert (g x > r - f x) by lra.
         generalize (Q_dense (r - f x) (g x) H3); intros.
         destruct H4.
         exists (iso_f x0).
         rewrite iso_b_f.
         lra.
       * destruct H2.
         lra.
     + apply sa_complement.
       rewrite H2.
       apply sa_countable_union.
       intros.
       apply sa_inter.
       now apply sa_le_gt.
       now apply sa_le_gt.
   Qed.
  
  Lemma minus_measurable (f g : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => g omega <= r)) ->    
    (forall (r:R),  sa_sigma (fun omega : Ts => (f omega) - (g omega) <= r)).
  Proof.
    intros.
    unfold Rminus.
    apply sum_measurable; trivial.
    now apply Ropp_measurable.
  Qed.

  Definition rvplus (rv_X1 rv_X2 : Ts -> R) :=
    (fun omega =>  (rv_X1 omega) + (rv_X2 omega)).

  Global Instance rvplus_rv (rv_X1 rv_X2 : Ts -> R)
           {rv1 : RandomVariable Prts borel_sa rv_X1}
           {rv2 : RandomVariable Prts borel_sa rv_X2} :
    RandomVariable Prts borel_sa (rvplus rv_X1 rv_X2).
  Proof.
    red; intros.
    apply borel_sa_preimage2; trivial; intros.
    unfold rvplus.
    apply sum_measurable.
    apply (RealRandomVariable_is_real Prts); trivial.
    apply (RealRandomVariable_is_real Prts); trivial.    
   Qed.

  Global Program Instance srvplus
         (rv_X1 rv_X2 : Ts -> R)
         {srv1:SimpleRandomVariable rv_X1}
         {srv2:SimpleRandomVariable rv_X2}
    : SimpleRandomVariable (rvplus rv_X1 rv_X2)
    := { srv_vals := map (fun ab => Rplus (fst ab) (snd ab)) 
                         (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                    (srv_vals (SimpleRandomVariable:=srv2))) }.
  Next Obligation.
    destruct srv1.
    destruct srv2.
    rewrite in_map_iff.
    exists (rv_X1 x, rv_X2 x).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

  Global Instance rvplus_prv (rv_X1 rv_X2 : Ts -> R)
           {rv1 : PositiveRandomVariable rv_X1}
           {rv2 : PositiveRandomVariable rv_X2} :
    PositiveRandomVariable (rvplus rv_X1 rv_X2).
  Proof.
    unfold PositiveRandomVariable in *.
    unfold rvplus.
    intros.
    specialize (rv1 x); specialize (rv2 x).
    lra.
  Qed.
  


  Definition rvminus (rv_X1 rv_X2 : Ts -> R) :=
    rvplus rv_X1 (rvopp rv_X2).

  Global Instance rvminus_rv
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable Prts borel_sa rv_X1}
         {rv2 : RandomVariable Prts borel_sa rv_X2}  :
    RandomVariable Prts borel_sa (rvminus rv_X1 rv_X2) := 
    rvplus_rv rv_X1 (rvopp rv_X2).

  Global Instance srvminus 
         (rv_X1 rv_X2 : Ts -> R)
         {srv1 : SimpleRandomVariable rv_X1}
         {srv2 : SimpleRandomVariable rv_X2}  :
    SimpleRandomVariable (rvminus rv_X1 rv_X2) := 
    srvplus rv_X1 (rvopp rv_X2).

 Global Instance rvminus_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvminus.
 Proof.
   unfold rv_eq, rvminus, rvplus, rvopp, rvscale, pointwise_relation.
   intros ???????.
   now rewrite H, H0.
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
    unfold srv_vals.
    assert (In (rv_X ex) srv_vals0) by apply srv_vals_complete0.
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
      unfold srv_vals in *; subst.
      simpl in srv_vals_complete0.
      now specialize (srv_vals_complete0 x).
  Qed.

  Lemma Rsqr_pos_measurable (f : Ts -> R) :
    (forall (x:Ts), (0 <= f x)%R) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => Rsqr (f omega) <= r)).
  Proof.
    intros.
    destruct (Rgt_dec 0 r).
    - assert (event_equiv (fun omega : Ts => (f omega)² <= r)
                          (fun _ => False)).
      + unfold event_equiv; intros.
        generalize (Rle_0_sqr (f x)).
        lra.
      + rewrite H1.
        apply sa_none.
    - assert (0 <= r) by lra.
      assert (event_equiv (fun omega : Ts => (f omega)² <= r)
                          (fun omega : Ts => (f omega) <= Rsqrt (mknonnegreal _ H1)) ).
      + unfold event_equiv; intros.
        specialize (H x).
        apply Rsqr_le_to_Rsqrt with (r := mknonnegreal _ H1) (x := mknonnegreal _ H).
      + rewrite H2.
        apply H0.
   Qed.
  
Lemma measurable_open_continuous (f : Ts -> R) (g : R -> R) :
    continuity g ->
    (forall B: event R, open_set B -> sa_sigma (event_preimage f B)) ->
    (forall B: event R, open_set B -> 
                        sa_sigma (event_preimage (fun omega => g (f omega)) B)).
  Proof.
    intros.
    generalize (continuity_P3 g); intros.
    destruct H2.
    specialize (H2 H B H1).
    unfold image_rec in *.
    unfold event_preimage in *.
    now specialize (H0 (fun x : R => B (g x)) H2).
  Qed.

Lemma measurable_continuous (f : Ts -> R) (g : R -> R) :
    continuity g ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => g (f omega) <= r)).
  Proof.
    intros.
    apply sa_open_set_le.
    apply measurable_open_continuous; trivial.
    now apply sa_le_open_set.
 Qed.

  Lemma Rsqr_measurable (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => Rsqr (f omega) <= r)).
  Proof.
    apply measurable_continuous.
    apply Rsqr_continuous.
  Qed.

  Definition rvsqr (rv_X : Ts -> R) := fun omega => Rsqr (rv_X omega).

  Global Instance rvsqr_rv
         (rv_X : Ts -> R)
         {rv : RandomVariable Prts borel_sa rv_X} :
    RandomVariable Prts borel_sa (rvsqr rv_X).
  Proof.
    red; intros.
    apply borel_sa_preimage2; trivial; intros.
    unfold rvsqr.
    apply Rsqr_measurable.
    apply (RealRandomVariable_is_real Prts); trivial.
   Qed.

  Global Program Instance srvsqr
         (rv_X : Ts -> R)
         {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvsqr rv_X)
    := { srv_vals := map Rsqr srv_vals }.
  Next Obligation.
    destruct srv.
    unfold rvsqr.
    now apply in_map.
  Qed.
  
 Global Instance rvsqr_proper : Proper (rv_eq ==> rv_eq) rvsqr.
 Proof.
   unfold rv_eq, rvsqr, Proper, respectful, pointwise_relation.
   intros x y eqq z.
   unfold Rsqr.
   rewrite eqq.
   trivial.
 Qed.

  Lemma product_measurable (f g : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => g omega <= r)) ->    
    (forall (r:R),  sa_sigma (fun omega : Ts => (f omega)*(g omega) <= r)).
  Proof.
    intros.
    assert (event_equiv 
              (fun omega : Ts => (f omega)*(g omega) <= r)
              (fun omega : Ts => (1/4)*((Rsqr (f omega + g omega)) -
                                        (Rsqr (f omega - g omega)))
                                 <= r)).
    - red; intros.
      replace ((1/4)*((Rsqr (f x + g x)) -
                      (Rsqr (f x - g x)))) with ((f x)*(g x)) by (unfold Rsqr; lra).
      intuition.
    - rewrite H1.
      apply scale_measurable.
      apply minus_measurable.
      apply Rsqr_measurable.
      now apply sum_measurable.
      apply Rsqr_measurable.
      now apply minus_measurable.
  Qed.
  
  Definition rvmult (rv_X1 rv_X2 : Ts -> R) := 
    fun omega => (rv_X1 omega) * (rv_X2 omega).

  Global Program Instance rvmult_rv 
          (rv_X1 rv_X2 : Ts -> R)
          {rv1 : RandomVariable Prts borel_sa rv_X1}
          {rv2 : RandomVariable Prts borel_sa rv_X2} :
    RandomVariable Prts borel_sa (rvmult rv_X1 rv_X2).
  Next Obligation.
    apply borel_sa_preimage2; trivial; intros.
    unfold rvmult.
    apply product_measurable.
    apply (RealRandomVariable_is_real Prts); trivial.
    apply (RealRandomVariable_is_real Prts); trivial.    
 Qed.

  Global Program Instance srvmult
         (rv_X1 rv_X2 : Ts -> R)
         {srv1:SimpleRandomVariable rv_X1}
         {srv2:SimpleRandomVariable rv_X2}
    : SimpleRandomVariable (rvmult rv_X1 rv_X2)
    := { srv_vals := map (fun ab => Rmult (fst ab) (snd ab)) 
                         (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                    (srv_vals (SimpleRandomVariable:=srv2))) }.
  Next Obligation.
    destruct srv1.
    destruct srv2.
    rewrite in_map_iff.
    exists (rv_X1 x, rv_X2 x).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

 Global Instance rvmult_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvmult.
 Proof.
   unfold rv_eq, rvmult.
   intros ???????.
   now rewrite H, H0.
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

   Lemma srv_nodup_preimage_list_union
         {rv_X : Ts -> R}         
         (srv : SimpleRandomVariable rv_X) :
     event_equiv (list_union (map (fun (x : R) (omega : Ts) => rv_X omega = x) (nodup Req_EM_T srv_vals)))  Ω .
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

   Lemma srv_vals_nodup_preimage_sa  
         {rv_X : Ts -> R}
         (rv: RandomVariable Prts borel_sa rv_X)
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
     
   Lemma srv_vals_prob_1 
         {rv_X : Ts -> R}
         (rv: RandomVariable Prts borel_sa rv_X)                      
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
     (rv1 rv2: RandomVariable Prts borel_sa) :
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
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}                               
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
        apply sa_sigma_inter_pts; trivial.
      - now apply event_disjoint_and_preimage_disj.
    Qed.
    
  Lemma prob_inter_all2
         {rv_X1 rv_X2 : Ts -> R}
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}                               
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
        {rv: RandomVariable Prts borel_sa rv_X}
        {rv2: RandomVariable Prts borel_sa rv_X2}                               
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

  Lemma SimpleExpectation_le 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1: RandomVariable Prts borel_sa rv_X1}
        {rv2: RandomVariable Prts borel_sa rv_X2}                               
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} : 
    RealRandomVariable_le rv_X1 rv_X2 ->
    SimpleExpectation rv_X1 <= SimpleExpectation rv_X2.
  Proof.
    unfold RealRandomVariable_le, SimpleExpectation.
    intros.
    unfold event_preimage, singleton_event.
    rewrite (RefineSimpleExpectation  srv1 srv2).
    rewrite (RefineSimpleExpectation  srv2 srv1).
    generalize (@sa_sigma_inter_pts rv_X1 rv_X2 rv1 rv2); intros sa_sigma.
    destruct srv1; destruct srv2.
    unfold srv_vals in *.
    replace 
      (list_sum (map
         (fun vv : R * R =>
            fst vv * ps_P (fun omega : Ts => rv_X2 omega = fst vv /\ rv_X1 omega = snd vv))
         (list_prod (nodup Req_EM_T srv_vals1) (nodup Req_EM_T srv_vals0)))) with
      (list_sum (map
           (fun vv : R * R =>
              snd vv * ps_P (fun omega : Ts => rv_X1 omega = fst vv /\ rv_X2 omega = snd vv))
           (list_prod (nodup Req_EM_T srv_vals0) (nodup Req_EM_T srv_vals1)))).
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
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}
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
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}         
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
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}         
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
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}         
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

    
  Lemma sumSimpleExpectation 
         (rv_X1 rv_X2 : Ts -> R)
         {rv1: RandomVariable Prts borel_sa rv_X1}
         {rv2: RandomVariable Prts borel_sa rv_X2}
         {srv1 : SimpleRandomVariable rv_X1} 
         {srv2 : SimpleRandomVariable rv_X2} :      
    NonEmpty Ts -> (SimpleExpectation rv_X1) + (SimpleExpectation rv_X2)%R = 
    SimpleExpectation (rvplus rv_X1 rv_X2).
   Proof.
    unfold SimpleExpectation; intros.
    generalize (non_empty_srv_vals _ srv1 X); intros.
    generalize (non_empty_srv_vals _ srv2 X); intros.    
    generalize (sumSimpleExpectation0 srv1 srv2 H0); intros.
    generalize (sumSimpleExpectation1 srv1 srv2 H); intros.   
    generalize (@sa_sigma_inter_pts rv_X1 rv_X2). intro sa_sigma.
    destruct srv1.
    destruct srv2.
    unfold srv_vals in *; intros.
    unfold srvplus.
    simpl.
    unfold singleton_event, event_preimage.
    transitivity (list_sum
                    (map (fun v : R*R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X1 omega = fst v /\ rv_X2 omega = snd v))
                         (list_prod (nodup Req_EM_T srv_vals0) (nodup Req_EM_T srv_vals1)))).
    - rewrite H1.
      rewrite H2.
      rewrite list_sum_map.
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
       (nodup HH (list_prod srv_vals0 srv_vals1)))).
      + f_equal.
        f_equal.
        symmetry.
        apply list_prod_nodup.
      + transitivity (list_sum
                        (map (fun v : R => v * ps_P (fun omega : Ts => rv_X1 omega + rv_X2 omega = v))
                             (nodup Req_EM_T (map (fun ab : R * R => fst ab + snd ab) (nodup HH (list_prod srv_vals0 srv_vals1)))))).
        * generalize (NoDup_nodup HH (list_prod srv_vals0 srv_vals1)).
          assert (Hcomplete:forall x y, In (rv_X1 x, rv_X2 y) (nodup HH (list_prod srv_vals0 srv_vals1))).
          { intros.
            apply nodup_In.
            apply in_prod; eauto.
          }
          revert Hcomplete.
          generalize (nodup HH (list_prod srv_vals0 srv_vals1)). (* clear. *)
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

End SimpleExpectation.

Section SimpleConditionalExpectation.

  Definition is_partition_list {T} (l:list (event T)) :=
    ForallOrdPairs event_disjoint l /\ event_equiv (list_union l) Ω.

  Lemma is_partition_list_partition {T} {l:list (event T)} :
    is_partition_list l ->
    SigmaAlgebras.is_partition (list_collection l event_none).
  Proof.
    intros [??].
    split.
    - now apply list_collection_disjoint.
    - rewrite list_union_union, H0.
      reflexivity.
  Qed.
    
  Instance list_partition_sa {T} (l:list (event T)) (is_part:is_partition_list l) :
    SigmaAlgebra T := countable_partition_sa
                        (list_collection l event_none)
                        (is_partition_list_partition is_part).
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
    RandomVariable Prts borel_sa  (gen_simple_conditional_expectation_scale P rv_X dec sap).
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

  Program Fixpoint map_dep {A B} (l:list A) :  (forall x, In x l -> B) -> list B
    := match l with
       | nil => fun f => nil
       | x::xs => fun f => (f x _) :: map_dep xs _
       end.
  Next Obligation.
    eapply f.
    right; eassumption.
  Defined.

  Definition with_index_simple {A} (l:list A) : list (nat*A)
    := (combine (seq 0 (length l)) l).


  Record dec_sa_event :=
    {
      dsa_event : event Ts
      ; dsa_dec :  (forall x, {dsa_event x} + {~ dsa_event x})
      ; dsa_sa : sa_sigma dsa_event
    }.
  
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
    
  Definition simple_conditional_expectation_scale_coef (c : R)
             (rv_X rv_X2 : Ts -> R)
             {srv : SimpleRandomVariable rv_X}
             {srv2 : SimpleRandomVariable rv_X2} : R :=
    if Req_EM_T (ps_P (event_preimage rv_X2 (singleton_event c))) 0 then 0 else
    ((SimpleExpectation 
        (rvmult rv_X
                 (point_preimage_indicator rv_X2 c)))
       / (ps_P (event_preimage rv_X2 (singleton_event c)))).

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
             {rv1 : RandomVariable Prts borel_sa rv_X1}
             {rv2 : RandomVariable Prts borel_sa rv_X2}                          
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
             {rv1 : RandomVariable Prts borel_sa rv_X1}
             {rv2 : RandomVariable Prts borel_sa rv_X2}                          
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
    unfold event_preimage, singleton_event.
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
        {srv : RandomVariable Prts borel_sa rv_X}
        (l : list dec_sa_event) :
     RandomVariable Prts borel_sa (fold_rvplus_prod_indicator rv_X l).
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

   Program Instance SimpleRandomVariable_enlarged
           {rv_X : Ts -> R}
           (srv:SimpleRandomVariable rv_X)
           (l:list R)
           (lincl : incl srv_vals l)
     : SimpleRandomVariable rv_X :=
     {
     srv_vals := l
     }.
   Next Obligation.
     apply lincl.
     apply srv_vals_complete.
   Qed.

   Lemma not_in_srv_vals_event_none
         {rv_X : Ts -> R}
         (srv:SimpleRandomVariable rv_X) :
     forall (x:R), ~ (In x srv_vals) ->
                   event_equiv (fun omega => rv_X omega = x) event_none.
     Proof.
       destruct srv.
       unfold srv_vals.
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
     unfold event_preimage, singleton_event.
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
   unfold RandomVariable.srvconst_obligation_1.
   unfold event_preimage, singleton_event, const.
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

   Lemma expectation_indicator_sum0 {nempty:NonEmpty Ts}
        (rv_X : Ts -> R)
        (rv : RandomVariable Prts borel_sa rv_X)
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
     - unfold map_dep_obligation_2.
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
        Forall (RandomVariable Prts borel_sa) l ->
        RandomVariable Prts borel_sa (fold_right rvplus (const 0) l).
  Proof.
    induction l; simpl; intros HH.
    - typeclasses eauto.
    - invcs HH.
      apply rvplus_rv; eauto.
  Qed.
            
  Lemma SimpleExpectation_fold_rvplus {nempty:NonEmpty Ts} (l : list (Ts -> R)) 
    (rvs : Forall (RandomVariable Prts borel_sa) l) 
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

  Lemma expectation_indicator_sum_gen {nempty:NonEmpty Ts}
        (rv_X : Ts -> R)
        {rv : RandomVariable Prts borel_sa rv_X}
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
          unfold map_dep_obligation_2.
          f_equal.
          now rewrite IHl.
        * now invcs is_disj.
  Qed.
               
  Lemma expectation_indicator_sum {nempty:NonEmpty Ts}
        (rv_X : Ts -> R)
        {rv : RandomVariable Prts borel_sa rv_X}
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
        {rv : RandomVariable Prts borel_sa rv_X}
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
                          (event_inter P (event_preimage rv_X (singleton_event a)))).
      + unfold event_equiv; intros.
        unfold event_inter, event_preimage, singleton_event.
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
        unfold event_preimage, singleton_event.
        apply sa_le_pt.
        apply (RealRandomVariable_is_real Prts); trivial.
  Qed.
    
  Lemma expectation_indicator_prob_0
             (P : event Ts) 
             {rv_X : Ts -> R}
             {rv : RandomVariable Prts borel_sa rv_X}
             {srv : SimpleRandomVariable rv_X}
             (dec:forall x, {P x} + {~ P x})        
             (sap: sa_sigma P) :
    ps_P P = 0 -> 
    SimpleExpectation (rvmult rv_X (EventIndicator dec)) = 0.
  Proof.
    unfold SimpleExpectation.
    unfold event_preimage, EventIndicator, singleton_event, rvmult.
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
             {rv : RandomVariable Prts borel_sa rv_X}
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
      unfold event_preimage, singleton_event.
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
        {rv : RandomVariable Prts borel_sa rv_X}
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
                                     
  Lemma gen_conditional_tower_law {nempty:NonEmpty Ts}
        (rv_X : Ts -> R)
        {rv : RandomVariable Prts borel_sa rv_X}
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
          {rv:RandomVariable Prts borel_sa rv_X}
             (srv : SimpleRandomVariable rv_X)
             : list dec_sa_event
    :=
      map (fun c => Build_dec_sa_event
             (event_preimage rv_X (singleton_event c)) _ _)
        (nodup Req_EM_T srv_vals).
  Next Obligation.
    unfold event_preimage, singleton_event.
    apply Req_EM_T.
  Defined.
  Next Obligation.
    eapply sa_singleton; eauto.
  Qed.
  
  Lemma induced_gen_ispart
        {rv_X : Ts -> R}
        {rv:RandomVariable Prts borel_sa rv_X}
        (srv : SimpleRandomVariable rv_X) :
    is_partition_list (map dsa_event (induced_sigma_generators srv)).
  Proof. 
    unfold is_partition_list.
    unfold induced_sigma_generators, event_preimage, singleton_event.
    rewrite map_map; simpl.
    split.
    - apply event_disjoint_preimage_disj.
      apply NoDup_nodup.
    - destruct srv.
      unfold srv_vals.
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

  Lemma conditional_tower_law {nempty:NonEmpty Ts}
        (rv_X1 rv_X2 : Ts -> R)
        (rv1 : RandomVariable Prts borel_sa rv_X1)
        (rv2 : RandomVariable Prts borel_sa rv_X2)        
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
      unfold event_preimage, singleton_event, EventIndicator.
      apply SimpleExpectation_ext.
      intros x.
      rewrite map_map; simpl.
      unfold induced_sigma_generators_obligation_1.
      reflexivity.
    Qed.

   Definition simple_sigma_measurable 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable Prts borel_sa rv_X1}
        {rv2 : RandomVariable Prts borel_sa rv_X2}
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} : Prop :=
     forall (c2:R), In c2 (srv_vals (SimpleRandomVariable:=srv2)) ->
        exists (c1:R), In c1 (srv_vals (SimpleRandomVariable:=srv1)) /\
                       (event_sub (event_preimage rv_X2 (singleton_event c2) )
                                  (event_preimage rv_X1 (singleton_event c1))).


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

   Definition partition_measurable
        (rv_X : Ts -> R)
        {srv : SimpleRandomVariable rv_X}
        (l : list (event Ts)) : Prop :=
     is_partition_list l ->
     forall (p:event Ts),
       In p l ->
       exists (c:R), (In c srv_vals) /\
                event_sub p (event_preimage rv_X (singleton_event c)).
   
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

   Lemma classic_event_none_or_has {A} (p:event A) : (exists y, p y) \/ event_equiv p event_none.
   Proof.
     destruct (classic (exists y, p y)).
     - eauto.
     - right; intros x.
       unfold event_none.
       split; [| tauto].
       intros px.
       apply H.
       eauto.
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

     
   Lemma rvmult_assoc
        (rv_X1 rv_X2 rv_X3 : Ts -> R) :
     rv_eq (rvmult (rvmult rv_X1 rv_X2) rv_X3) (rvmult rv_X1 (rvmult rv_X2 rv_X3)).
    Proof.
      intros x.
      unfold rvmult.
      lra.
    Qed.

    Lemma rvmult_comm
        (rv_X1 rv_X2 : Ts -> R) :
     rv_eq (rvmult rv_X1 rv_X2)  (rvmult rv_X2 rv_X1).
    Proof.
      intros x.
      unfold rvmult.
      lra.
    Qed.

    Lemma rvmult_rvadd_distr
        (rv_X1 rv_X2 rv_X3 : Ts -> R) :
     rv_eq (rvmult rv_X1 (rvplus rv_X2 rv_X3))  
           (rvplus (rvmult rv_X1 rv_X2) (rvmult rv_X1 rv_X3)).
    Proof.
      intros x.
      unfold rvmult, rvplus.
      lra.
    Qed.

    Global Instance nodup_perm {A} dec : Proper (@Permutation A ==> @Permutation A) (nodup dec).
    Proof.
      repeat red; intros.
      revert x y H.
      apply Permutation_ind_bis; simpl; intros.
      - trivial.
      - repeat match_destr.
        + rewrite H in i; congruence.
        + rewrite <- H in i; congruence.
        + apply perm_skip; trivial.
      - destruct (dec x y)
        ; destruct (dec y x)
        ; try congruence.
        + subst.
          destruct (in_dec dec y l)
          ; destruct (in_dec dec y l')
          ; try congruence.
          * rewrite H in i; congruence.
          * rewrite <- H in i; congruence.
          * apply perm_skip; congruence.
        + destruct (in_dec dec y l)
          ; destruct (in_dec dec x l)
          ; destruct (in_dec dec x l')
          ; destruct (in_dec dec y l')
          ; try congruence
          ; try solve [
                  rewrite H in i; congruence
                  | rewrite H in i0; congruence
                  | rewrite H in i1; congruence
                  | rewrite <- H in i; congruence
                  | rewrite <- H in i0; congruence
                  | rewrite <- H in i1; congruence
                  | apply perm_skip; congruence
                ] .
          rewrite H0.
          apply perm_swap.
      - now rewrite H0.
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
     unfold partition_measurable, event_preimage, singleton_event.
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
         {rv1 : RandomVariable Prts borel_sa rv_X1}
        {rv2 : RandomVariable Prts borel_sa rv_X2}
        {rv3 : RandomVariable Prts borel_sa rv_X3}

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
     unfold event_preimage, singleton_event.
     unfold induced_sigma_generators in H.
     unfold induced_sigma_generators_obligation_1 in H.
     unfold event_preimage, singleton_event in H.
     do 2 rewrite map_map in H.
     simpl in H.
     rewrite H.
     reflexivity.
     unfold simple_sigma_measurable in H0.
     unfold partition_measurable, induced_sigma_generators.
     unfold event_preimage, singleton_event in *.
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

Section Expectation.
 
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Definition BoundedPositiveRandomVariable
    (rv_X1 rv_X2 : Ts -> R) :=
    PositiveRandomVariable rv_X2 /\ RealRandomVariable_le rv_X2 rv_X1.

  Definition SimpleExpectationSup 
             (E :  forall 
                     (rvx:Ts -> R)
                     (srv:SimpleRandomVariable rvx), Prop) : Rbar
    := Lub_Rbar (fun (x : R) => 
                   exists rvx srv, 
                     E rvx srv /\ (SimpleExpectation rvx) = x).
    
  Definition Expectation_posRV
             (rv_X : Ts -> R)
             {posrv:PositiveRandomVariable rv_X} :  Rbar   :=
      (SimpleExpectationSup
         (fun
            (rvx2: Ts -> R)
            (srv2:SimpleRandomVariable rvx2) =>
            (BoundedPositiveRandomVariable rv_X rvx2))).

  Global Instance bprv_eq_proper : Proper (rv_eq ==> rv_eq ==> iff) BoundedPositiveRandomVariable.
  Proof.
    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold BoundedPositiveRandomVariable.
    unfold PositiveRandomVariable.
    repeat rewrite eqq1.
    rewrite eqq2.
    repeat red in eqq2.
    intuition.
    - now rewrite <- eqq2.
    - now rewrite eqq2.
  Qed.
    
  Lemma Expectation_posRV_ext 
        {rv_X1 rv_X2 : Ts -> R}
        (srv1:PositiveRandomVariable rv_X1) 
        (srv2:PositiveRandomVariable rv_X2):
    rv_eq rv_X1 rv_X2 ->
    Expectation_posRV rv_X1 = Expectation_posRV rv_X2.
  Proof.
    intros eqq.
    unfold Expectation_posRV, SimpleExpectationSup.
    apply Lub_Rbar_eqset; intros x.
    split; intros [y [ ysrv [??]]].
    - exists y; exists ysrv.
      rewrite <- eqq.
      auto.
    - exists y; exists ysrv.
      rewrite eqq.
      auto.
  Qed.      
   
  Program Definition pos_fun_part {Ts:Type} (f : Ts -> R) : (Ts -> nonnegreal) :=
    fun x => mknonnegreal (Rmax (f x) 0) _.
  Next Obligation.
    apply Rmax_r.
  Defined.

  Program Definition neg_fun_part {Ts:Type} (f : Ts -> R) : (Ts -> nonnegreal) :=
    fun x => mknonnegreal (Rmax (- f x) 0) _.
  Next Obligation.
    apply Rmax_r.
  Defined.

  Lemma Relu_measurable_neg (f : Ts -> R) :
    forall (r:R), r < 0 -> sa_sigma (fun omega : Ts => Rmax (f omega) 0 <= r).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => Rmax (f omega) 0 <= r) event_none).
    unfold event_equiv; intros.
    generalize (Rmax_r (f x) 0); intros.
    unfold event_none.
    lra.
    rewrite H0.
    apply sa_none.
  Qed.
    
  Lemma Relu_measurable_pos (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  0 <= r -> sa_sigma (fun omega : Ts => Rmax (f omega) 0 <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => Rmax (f omega) 0 <= r)
                        (fun omega : Ts => f omega <= r)).
    unfold event_equiv; intros.
    unfold Rmax.
    destruct (Rle_dec (f x) 0); lra.
    now rewrite H1.
  Qed.

  Lemma Relu_measurable (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => Rmax (f omega) 0 <= r)).
  Proof.
    intros.
    destruct (Rle_dec 0 r).
    now apply Relu_measurable_pos.
    apply Relu_measurable_neg.
    lra.
  Qed.

  Global Program Instance positive_part_rv 
     (rv_X : Ts -> R)
     (rv : RandomVariable Prts borel_sa rv_X) :
           RandomVariable Prts borel_sa (pos_fun_part rv_X).
  Next Obligation.
    apply borel_sa_preimage; trivial; intros.
    apply Relu_measurable.
    now apply (RealRandomVariable_is_real Prts).
 Qed.

  Global Instance positive_part_prv 
     (rv_X : Ts -> R) :
    PositiveRandomVariable (pos_fun_part rv_X).
  Proof.
    unfold PositiveRandomVariable.
    unfold positive_part_rv, pos_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

  Global Program Instance negative_part_rv
     (rv_X : Ts -> R)
     (rv : RandomVariable Prts borel_sa rv_X) :
           RandomVariable Prts borel_sa (neg_fun_part rv_X).
  Next Obligation.
    apply borel_sa_preimage; trivial; intros.
    apply Relu_measurable.
    apply Ropp_measurable.
    now apply (RealRandomVariable_is_real Prts).
  Qed.

  Global Instance negative_part_prv
     (rv_X : Ts -> R) :
    PositiveRandomVariable (neg_fun_part rv_X).
  Proof.
    unfold PositiveRandomVariable.
    unfold negative_part_rv, neg_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

  Definition Expectation (rv_X : Ts -> R) 
             {rrv : RandomVariable Prts borel_sa rv_X} : option Rbar :=
    Rbar_plus' (Expectation_posRV (pos_fun_part rv_X))
               (Rbar_opp (Expectation_posRV (neg_fun_part rv_X))).

  Lemma Expectation_ext {rv_X1 rv_X2 : Ts -> R}
        (srv1:RandomVariable Prts borel_sa rv_X1) 
        (srv2:RandomVariable Prts borel_sa rv_X2):
    rv_eq rv_X1 rv_X2 ->
    Expectation rv_X1 = Expectation rv_X2.
  Proof.
    intros eqq.
    unfold Expectation.
    f_equal.
    - apply Expectation_posRV_ext.
      intros x; simpl.
      now rewrite eqq.
    - f_equal.
      apply Expectation_posRV_ext.
      intros x; simpl.
      now rewrite eqq.
  Qed.      
  
  Definition rvmean (rv_X:Ts -> R) {rrv : RandomVariable Prts borel_sa rv_X} : option Rbar :=
     Expectation rv_X.

  Definition variance (rv_X : Ts -> R) {rrv : RandomVariable Prts borel_sa rv_X} : option Rbar :=
    match rvmean rv_X with
    | Some (Finite m) => Expectation (rvsqr (rvminus rv_X (const m)))
    | _ => None
    end.

   Lemma Rbar_mult_mult_pos (c : posreal) (l : Rbar) :
     Rbar_mult_pos l c = Rbar_mult l c.
   Proof.
     assert (0 < c) as cpos by apply cond_pos.
     unfold Rbar_mult_pos.
     unfold Rbar_mult, Rbar_mult'.
     destruct l.
     - trivial.
     - match_case; intros; match_case_in H; intros; try lra; rewrite H0 in H; 
          match_case_in H; intros; try lra; rewrite H1 in H; [now invcs H| congruence].
     - match_case; intros; match_case_in H; intros; try lra; rewrite H0 in H; 
          match_case_in H; intros; try lra; rewrite H1 in H; [now invcs H| congruence].
   Qed.

   Lemma Rbar_div_mult_pos (c : posreal) (l : Rbar) :
     Rbar_mult_pos (Rbar_div l c) c = l.
   Proof.
     assert (c > 0) as cpos by apply cond_pos.
     assert ((pos c) <> 0) as cneq0 by lra.
     assert (/c > 0) by apply Rinv_0_lt_compat, cpos.
     unfold Rbar_div; simpl.
     unfold Rbar_mult, Rbar_mult', Rbar_mult_pos.
     destruct l.
     - f_equal; field; trivial.
     - case (Rle_dec 0 (/ c)) ; intros; try lra.
       match_case; intros; match_case_in H0; intros; match_case_in H1; intros; 
         try lra; rewrite H2 in H0; invcs H0.
     - case (Rle_dec 0 (/ c)) ; intros; try lra.
       match_case; intros; match_case_in H0; intros; match_case_in H1; intros; 
         try lra; rewrite H2 in H0; invcs H0.
   Qed.

  Lemma rbar_le_scaled (c : posreal) (x y :Rbar) :
     Rbar_le x (Rbar_mult c y) <-> Rbar_le (Rbar_div x c) y.
   Proof.
     symmetry.
     rewrite Rbar_mult_pos_le with (z := c).
     rewrite Rbar_mult_comm.
     rewrite Rbar_div_mult_pos.
     now rewrite Rbar_mult_mult_pos.
   Qed.
       
   Lemma rbar_le_scaled2 (c : posreal) (x y :Rbar) :
     Rbar_le (Rbar_mult c x) y <-> Rbar_le x (Rbar_div y c).
   Proof.
     symmetry.
     rewrite Rbar_mult_pos_le with (z := c).     
     rewrite Rbar_div_mult_pos.
     rewrite Rbar_mult_comm.
     now rewrite Rbar_mult_mult_pos.     
   Qed.

   Lemma lub_rbar_scale0 (c:posreal) (E : R -> Prop) (l:Rbar) :
         is_lub_Rbar E l -> is_lub_Rbar (fun x => E (x/c)) (Rbar_mult c l).
   Proof.
     assert (0 < c) as cpos by apply cond_pos.
     assert (0 <= c) as cnn by lra.
     unfold is_lub_Rbar, is_ub_Rbar.
     intros.
     destruct H.
     split.
     - intros.
       specialize (H (Rbar_div x c) H1).
       now apply rbar_le_scaled.
     - intros.
       specialize (H0 (Rbar_div b c)).
       cut_to H0.
       + now apply rbar_le_scaled2.
       + intros.
         specialize (H1 (c * x)).
         replace (c * x / c) with (x) in H1.
         apply rbar_le_scaled2.
         now apply H1.
         field.
         now apply Rgt_not_eq.
    Qed.
                                                               
   Lemma lub_rbar_scale (c:posreal) (E : R -> Prop) :
     Lub_Rbar (fun x => E (x / c)) = Rbar_mult c (Lub_Rbar E).
     Proof.
       apply is_lub_Rbar_unique.
       apply lub_rbar_scale0.
       apply Lub_Rbar_correct.
   Qed.

     Global Instance rv_scale_le_proper (c:posreal) :
       Proper (RealRandomVariable_le ==> RealRandomVariable_le) (@rvscale Ts c).
     Proof.
       unfold RealRandomVariable_le, rvscale.
       intros x y xyle; intros.
       apply Rmult_le_compat_l; trivial.
       destruct c; simpl.
       lra.
     Qed.
                                                         
   Lemma Expectation_posRV_scale (c: posreal) 
        (rv_X : Ts -> R)
        {rv : RandomVariable Prts borel_sa rv_X}
        {posrv:PositiveRandomVariable rv_X} :
    Expectation_posRV (rvscale c rv_X) =
    Rbar_mult c (Expectation_posRV rv_X).
  Proof.
    unfold Expectation_posRV.
    unfold BoundedPositiveRandomVariable.
    unfold SimpleExpectationSup.
    rewrite <- lub_rbar_scale.
    apply Lub_Rbar_eqset; intros.
    split; intros [? [? [[??]?]]].
    - exists (rvscale (/ c) x0).
      exists (srvscale _ _).
      split; [split |].
      + assert (0 < / c).
        { destruct c; simpl.
          now apply Rinv_0_lt_compat.
        } 
        apply (positive_scale_prv (mkposreal _ H2) x0). 
      + unfold RealRandomVariable_le, rvscale in *.
        intros y.
        specialize (H0 y).
        apply (Rmult_le_compat_l (/ c)) in H0.
        * rewrite <- Rmult_assoc in H0.
          rewrite Rinv_l in H0.
          -- lra.
          -- destruct c; simpl; lra.
        * destruct c; simpl.
          left.
          now apply Rinv_0_lt_compat.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1.
        field; trivial.
        destruct c; simpl.
        lra.
    - exists (rvscale c x0).
      exists (srvscale c x0).
      split; [split |].
      + typeclasses eauto.
      + now rewrite H0.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1.
        field; trivial.
        destruct c; simpl.
        lra.
  Qed.

  Lemma scale_Rmax0 (c:posreal) :
    forall (x:R),
      Rmax (c * x) 0 = c * Rmax x 0.
    intros.
    replace (0) with (c * 0) at 1 by lra.
    rewrite RmaxRmult; trivial.
    left.
    apply cond_pos.
  Qed.

  Lemma Expectation_scale_pos (c:posreal) (rv_X : Ts -> R) 
    {rv : RandomVariable Prts borel_sa rv_X} :
    Expectation_posRV (fun x : Ts => pos_fun_part (rvscale c rv_X) x) =
    Rbar_mult c (Expectation_posRV (pos_fun_part rv_X)).
  Proof.
    rewrite <- Expectation_posRV_scale.
    - apply Expectation_posRV_ext.
      intros x.
      unfold pos_fun_part, rvscale.
      unfold pos_fun_part_obligation_1.
      simpl.
      now rewrite scale_Rmax0.
    - now apply positive_part_rv.
  Qed.
  
  Lemma Expectation_scale_neg (c:posreal) (rv_X : Ts -> R) 
    {rv : RandomVariable Prts borel_sa rv_X} :
    Expectation_posRV (fun x : Ts => neg_fun_part (rvscale c rv_X) x) =
    Rbar_mult c (Expectation_posRV (neg_fun_part rv_X)).
  Proof.
    rewrite <- Expectation_posRV_scale.
    - apply Expectation_posRV_ext.
      intros x.
      unfold neg_fun_part, rvscale.
      unfold neg_fun_part_obligation_1.
      simpl.
      replace (-(c*rv_X x)) with (c * (-rv_X x)) by lra.
      now rewrite scale_Rmax0.
    - now apply negative_part_rv.
  Qed.

   Lemma Rbar_mult_pos_pinf (c : posreal):
     Rbar_mult c p_infty = p_infty.
   Proof.
     apply is_Rbar_mult_unique.
     apply (is_Rbar_mult_p_infty_pos c (cond_pos c)).
   Qed.

   Lemma Rbar_mult_pos_minf (c : posreal):
     Rbar_mult c m_infty = m_infty.
   Proof.
     apply is_Rbar_mult_unique.
     apply (is_Rbar_mult_m_infty_pos c (cond_pos c)).
   Qed.

  Lemma scale_Rbar_plus (c : posreal) (x y : Rbar) :
    Rbar_plus' (Rbar_mult c x) (Rbar_mult c y) =
    match (Rbar_plus' x y) with
    | Some x' => Some (Rbar_mult c x')
    | None => None
    end.
  Proof.
    assert (0 < c) by apply cond_pos.
    assert (0 <= c) by lra.
    match_case; intros.
    - destruct x; destruct y; simpl in H1; invcs H1.
      + simpl; f_equal.
        now rewrite <- Rmult_plus_distr_l.
      + replace (Rbar_mult c r0) with (Finite (c * r0)) by now simpl.
        unfold Rbar_plus'.
        match_case; intros.
        rewrite Rbar_mult_pos_pinf in H1.
        discriminate.
      + replace (Rbar_mult c r0) with (Finite (c * r0)) by now simpl.
        unfold Rbar_plus'.
        match_case; intros.
        rewrite Rbar_mult_pos_minf in H1.
        discriminate.
      + rewrite Rbar_mult_pos_pinf.
        replace (Rbar_mult c r0) with (Finite (c * r0)) by now simpl.
        now simpl.
      + rewrite Rbar_mult_pos_pinf; now simpl.
      + rewrite Rbar_mult_pos_minf; now simpl.
      + rewrite Rbar_mult_pos_minf; now simpl.
    - destruct x; destruct y; simpl in H1; try discriminate.
      + rewrite Rbar_mult_pos_pinf, Rbar_mult_pos_minf; now simpl.
      + rewrite Rbar_mult_pos_pinf, Rbar_mult_pos_minf; now simpl.
   Qed.

  Lemma scale_Rbar_diff (c : posreal) (x y : Rbar) :
    Rbar_plus' (Rbar_mult c x) (Rbar_opp (Rbar_mult c y)) =
    match (Rbar_plus' x (Rbar_opp y)) with
    | Some x' => Some (Rbar_mult c x')
    | None => None
    end.
    Proof.
      replace (Rbar_opp (Rbar_mult c y)) with (Rbar_mult c (Rbar_opp y)).
      - apply scale_Rbar_plus.
      - apply Rbar_mult_opp_r.
    Qed.

  Lemma Expectation_scale (c: posreal) 
        (rv_X : Ts -> R)
        {rv : RandomVariable Prts borel_sa rv_X} :
    let Ex_rv := Expectation rv_X in
    let Ex_c_rv := (@Expectation (rvscale c rv_X) (rvscale_rv Prts c rv_X rv)) in
    Ex_c_rv = 
    match Ex_rv with
    | Some x => Some (Rbar_mult c x)
    | None => None
    end.
  Proof. 
    unfold Expectation.
    rewrite Expectation_scale_pos; trivial.
    rewrite Expectation_scale_neg; trivial.
    apply scale_Rbar_diff.
  Qed.
  
  Require Import Classical.

  Lemma lub_Rbar_witness (E : R -> Prop) (l : Rbar) (b:R):
    is_lub_Rbar E l -> Rbar_lt b l ->
    exists (x:R), E x /\ x > b.
  Proof.
    unfold is_lub_Rbar, is_ub_Rbar.
    intros.
    destruct H.
    specialize (H1 b).
    assert (~(forall x : R, E x -> x <= b)).
    - intros HH.
      specialize (H1 HH).
      apply Rbar_lt_not_le in H0.
      congruence.
    - apply not_all_ex_not in H2.
      destruct H2.
      apply imply_to_and in H2.
      destruct H2.
      exists x.
      split; trivial.
      lra.
  Qed.

  Lemma lub_rbar_inf_witness (E : R -> Prop) :
    is_lub_Rbar E p_infty -> forall (b:R), exists (x:R), E x /\ x>b.
  Proof.
    intros.
    apply (lub_Rbar_witness _ p_infty b H).
    now simpl.
  Qed.


  Lemma lub_bar_nonempty (E : R -> Prop) :
    (exists (x:R), E x) -> ~(Lub_Rbar E = m_infty).
    Proof.
      unfold Lub_Rbar.
      destruct (ex_lub_Rbar E); simpl.
      destruct i as [HH1 HH2].
      intros.
      destruct x.
      + discriminate.
      + discriminate.
      + destruct H.
        specialize (HH1 x H).
        now unfold Rbar_le in HH1.
   Qed.

  Lemma lub_rbar_sum_inf1  (E1 E2 : R -> Prop) :
    (exists (x:R), E1 x) -> Lub_Rbar E2 = p_infty ->
    Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = p_infty.
  Proof.
    intros nemptyE1 H.
    rewrite H.
    case_eq (Lub_Rbar E1); intros.
    - now simpl.
    - now simpl.
    - unfold Lub_Rbar in H0.
      destruct (ex_lub_Rbar E1); simpl in H0.
      destruct nemptyE1.
      destruct i.
      specialize (H2 x0 H1).
      rewrite H0 in H2.
      simpl in H2.
      tauto.
  Qed.

  Lemma lub_rbar_sum_inf2  (E1 E2 : R -> Prop) :
    (exists (x:R), E1 x) -> Lub_Rbar E2 = p_infty ->
    is_lub_Rbar (fun x => exists x1 x2, E1 x1 /\ E2 x2 /\ x = x1 + x2) p_infty.    
  Proof.
    intros nemptyE1 H.
    unfold is_lub_Rbar.
    split.
    - unfold is_ub_Rbar.
      intros.
      now simpl.
    - intros.
      unfold Lub_Rbar in H.
      destruct (ex_lub_Rbar E2); simpl in *.
      invcs H.
      generalize (lub_rbar_inf_witness _ i); intros.
      unfold is_lub_Rbar in i.
      destruct i.
      unfold is_ub_Rbar in *.
      destruct b.
      + destruct nemptyE1.
        specialize (H (r-x)).
        destruct H.
        specialize (H0 (x + x0)).
        cut_to H0.
        destruct H.
        simpl in H0; lra.
        exists x; exists x0.
        destruct H.
        tauto.
      + trivial.
      + destruct nemptyE1.
        specialize (H 0).
        destruct H.
        specialize (H0 (x + x0)).
        cut_to H0.
        now simpl in H0.
        exists x.
        exists x0.
        destruct H.
        tauto.
   Qed.

  Lemma lub_rbar_sum_inf3  (E1 E2 : R -> Prop) :
    (exists (x:R), E2 x) -> Lub_Rbar E1 = p_infty ->
    is_lub_Rbar (fun x => exists x1 x2, E1 x1 /\ E2 x2 /\ x = x1 + x2) p_infty.    
  Proof.
    intros nemptyE1 H.
    generalize (lub_rbar_sum_inf2 E2 E1 nemptyE1 H); intros.
    apply (is_lub_Rbar_eqset  
             (fun x : R => exists x1 x2 : R, E2 x1 /\ E1 x2 /\ x = x1 + x2)); 
      trivial; intros.
    split; intros; destruct H1; destruct H1; 
      exists x1; exists x0; rewrite Rplus_comm; tauto.
  Qed.

  Lemma lub_rbar_sum  (E1 E2 : R -> Prop) :
    (exists (x:R), E1 x) -> (exists (x:R), E2 x) ->
    Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = 
    Lub_Rbar (fun x => exists x1 x2, E1 x1 /\ E2 x2 /\ x = x1 + x2).
    Proof.
      intros nemptyE1 nemptyE2.
      symmetry.
      apply is_lub_Rbar_unique.
      split.
      - red; intros.
        destruct H as [y [z [Ey [Ez ?]]]].
        subst.
        red.
        unfold Lub_Rbar.
        destruct (ex_lub_Rbar E1); simpl.
        destruct (ex_lub_Rbar E2); simpl.
        destruct i as [HH11 HH12].
        specialize (HH11 _ Ey).
        destruct i0 as [HH21 HH22].
        specialize (HH21 _ Ez).
        red in HH11.
        red in HH21.
        destruct x; try tauto
        ; destruct x0; try tauto.
        simpl.
        lra.
      - intros.
        generalize (lub_rbar_sum_inf2 E1 E2 nemptyE1); intros.
        generalize (lub_rbar_sum_inf3 E1 E2 nemptyE2); intros.        

        generalize (lub_bar_nonempty E2 nemptyE2); intros.
        assert (Lub_Rbar E2 = p_infty -> 
                Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = p_infty).
        intros.
        apply lub_rbar_sum_inf1; trivial.        
        
        generalize (lub_bar_nonempty E1 nemptyE1); intros.
        assert (Lub_Rbar E1 = p_infty -> 
                Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = p_infty).
        intros.
        rewrite Rbar_plus_comm.
        apply lub_rbar_sum_inf1; trivial.
        
        case_eq (Lub_Rbar E1); intros.
        + case_eq (Lub_Rbar E2); intros.
          * simpl.
            destruct b.
            -- clear H0 H1 H2 H3 H4 H5.
               unfold Lub_Rbar in *.
               destruct (ex_lub_Rbar E1) as [lubE1 ?]; simpl in *.
               destruct (ex_lub_Rbar E2) as [lubE2 ?]; simpl in *.
               invcs H6.
               generalize (lub_Rbar_witness E1 r (r - (r + r0 - r1)/2) i).
               generalize (lub_Rbar_witness E2 r0 (r0 - (r + r0 - r1)/2) i0); intros.
               assert (r + r0 > r1 -> False); intros.
               ++ cut_to H0; [|simpl; lra].
                  cut_to H1; [|simpl; lra].
                  destruct H0 as [x0 [H0 HH0]].
                  destruct H1 as [x1 [H1 HH1]].
                  unfold is_ub_Rbar in *.
                  specialize (H (x0 + x1)).
                  cut_to H.
                  simpl in H.
                  lra.
                  exists x1; exists x0; rewrite Rplus_comm; tauto.
               ++ intros.
                  lra.
            -- trivial.
            -- unfold is_ub_Rbar in H.
               destruct nemptyE1; destruct nemptyE2.
               specialize (H (x + x0)).
               cut_to H.
               now simpl in H.
               exists x; exists x0; tauto.
          * cut_to H0; trivial.
            unfold is_lub_Rbar in H0.
            destruct H0.
            now specialize (H8 b H).
          * congruence.
        + cut_to H1; trivial.
          unfold is_lub_Rbar in H1.
          destruct H1.
          specialize (H7 b H).
          rewrite <- H6.
          rewrite H5; trivial.
        + tauto.
   Qed.

   Lemma Expectation_witness (l: Rbar) (b : R)
        (rv_X: Ts -> R)
        {rv : RandomVariable Prts borel_sa rv_X}
        {prv:PositiveRandomVariable rv_X} :
     Rbar_lt b l -> Expectation_posRV rv_X = l -> 
      exists (x:R), (exists (rvx : Ts -> R) (srv : SimpleRandomVariable rvx),
        BoundedPositiveRandomVariable rv_X rvx /\ SimpleExpectation rvx = x) /\ x > b.
     Proof.
       unfold Expectation_posRV, SimpleExpectationSup.       
       unfold Lub_Rbar.
       destruct (ex_lub_Rbar
                   (fun x : R =>
                      exists (rvx : Ts -> R) (srv : SimpleRandomVariable rvx),
                        BoundedPositiveRandomVariable rv_X rvx /\ SimpleExpectation rvx = x)).
       simpl.
       intros.
       invcs H0.
       generalize (lub_Rbar_witness (fun x : R =>
         exists (rvx : Ts -> R) (srv : SimpleRandomVariable rvx),
           BoundedPositiveRandomVariable rv_X rvx /\ SimpleExpectation rvx = x) l b i H)
       ; intros.
       apply H0.
   Qed.

   Lemma Expectation_posRV_sum
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable Prts borel_sa rv_X1}
        {rv2 : RandomVariable Prts borel_sa rv_X2}        
        {prv1:PositiveRandomVariable rv_X1}
        {prv2:PositiveRandomVariable rv_X2} :     
    Expectation_posRV (rvplus rv_X1 rv_X2) =
    Rbar_plus (Expectation_posRV rv_X1) (Expectation_posRV rv_X1).
   Proof.
     unfold Expectation_posRV, SimpleExpectationSup.
     rewrite lub_rbar_sum.
     - apply Lub_Rbar_eqset.
       intros.
       admit.
     - exists 0.
       exists (const 0).
       exists (srvconst 0).
       split.
       + unfold BoundedPositiveRandomVariable.
         split.
         * apply prvconst.
           lra.
         * intros ?.
           unfold const.
           red in prv1.
           auto.
       + now rewrite SimpleExpectation_const. 
     - exists 0.
       exists (const 0).
       exists (srvconst 0).
       split.
       + unfold BoundedPositiveRandomVariable.
         split.
         * apply prvconst.
           lra.
         * intros ?.
           unfold const.
           red in prv1.
           auto.
       + now rewrite SimpleExpectation_const. 

     Admitted.

  Lemma Expectation_sum 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable Prts borel_sa rv_X1}
        {rv2 : RandomVariable Prts borel_sa rv_X2} :
    Expectation (rvplus rv_X1 rv_X2) =
    match Expectation rv_X1, Expectation rv_X2 with
    | Some exp1, Some exp2 => Some (Rbar_plus exp1 exp2)
    | _, _ => None
    end.
  Proof. 
    Admitted.

End Expectation.


Section lebesgueintegration.
  

  Class MeasurableFunction {Ts: Type} (dom: SigmaAlgebra Ts) :=
    {
      measure_mu: event Ts -> R;

      measure_none : measure_mu event_none = R0 ;
      measure_ge_zero: forall A : event Ts, sa_sigma A -> 0 <= measure_mu A;
  
      measure_coutably_additive: forall collection: nat -> event Ts,
           (forall n : nat, sa_sigma (collection n)) ->
           collection_is_pairwise_disjoint collection ->
           sum_of_probs_equals measure_mu collection (measure_mu (union_of_collection collection))

    }.


  (* See https://en.wikipedia.org/wiki/Lebesgue_integration#Towards_a_formal_definition *)
  Definition F_star {dom:SigmaAlgebra R} (measure: MeasurableFunction dom) (f: R -> R) (t: R) :=
    measure_mu (fun (x: R) => (f x) > t).

  (* The integral $\int f d\mu defined in terms of the Riemann integral.
   * note that this definition assumes that f : R -> R+
   * Again, see https://en.wikipedia.org/wiki/Lebesgue_integration#Towards_a_formal_definition *)
  Definition Lebesgue_integrable_pos {dom: SigmaAlgebra R}
             (f : R -> R)
             (f_nonneg : forall x:R, f x > 0)
             (measure: MeasurableFunction dom)
             (a b : R) :=
    (Riemann_integrable (F_star measure f) a b).
End lebesgueintegration.

Instance ProbSpace_Measurable {T:Type} {sa: SigmaAlgebra T} (ps:ProbSpace sa) : MeasurableFunction sa
  := {
      measure_mu := ps_P ;
      measure_none := (ps_none ps) ;
      measure_ge_zero := ps_pos ;
      measure_coutably_additive := ps_countable_disjoint_union ; 
    }.

Section zmBoundedVariance.
  (* TODO finish this definition *)
  Class ZeroMeanVoundedVariance (t: nat -> R) :=
    {
      has_zero_mean: Prop;
      has_bounded_variance: Prop;
    }.
End zmBoundedVariance.

  
