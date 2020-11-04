Require Import Reals.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.
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
        (cod: SigmaAlgebra Td) :=
    {
      (* the random variable. *)
      rv_X: Ts -> Td;

      (* for every element B in the sigma algebra, 
           the preimage of rv_X on B is an event in the probability space *)
      rv_preimage: forall (B: event Td), sa_sigma B -> sa_sigma (event_preimage rv_X B);
    }.

  Section Simple.
    Context {Ts:Type} {Td:Type}
            {dom: SigmaAlgebra Ts}
            {prts: ProbSpace dom}
            {cod: SigmaAlgebra Td}.

    Definition singleton_event {T} (m:T) := fun x => x=m.

    Class ConstantRandomVariable
          (rrv : RandomVariable prts cod)
      := { 
      srv_val : Td;
      srv_val_complete : forall x, rv_X x = srv_val
        }.

  Program Instance rvconst c : RandomVariable prts cod :=
    { rv_X := (fun _ => c) }.
  Next Obligation.
    unfold event_preimage.
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

  Program Instance crvconst c : ConstantRandomVariable (rvconst c)
    := { srv_val := c }.

  Class SimpleRandomVariable 
        (rrv : RandomVariable prts cod)
    := { 
      srv_vals : list Td ;
      srv_vals_complete : forall x, In (rv_X x) srv_vals;
    }.

  Global Program Instance srvconst
         (rv:RandomVariable prts cod) 
         {crv:ConstantRandomVariable rv} : SimpleRandomVariable rv
    := { srv_vals := [srv_val] }.
  Next Obligation.
    left.
    symmetry.
    apply srv_val_complete.
  Qed.

  Program Instance nodup_simple_random_variable (dec:forall (x y:Td), {x = y} + {x <> y}) {rv:RandomVariable prts cod} (srv:SimpleRandomVariable rv) : SimpleRandomVariable rv
    := { srv_vals := nodup dec srv_vals }.
  Next Obligation.
    apply nodup_In.
    apply srv_vals_complete.
  Qed.

  Lemma nodup_simple_random_variable_NoDup
        (dec:forall (x y:Td), {x = y} + {x <> y})
        {rv:RandomVariable prts cod}
        (srv:SimpleRandomVariable rv) :
    NoDup (srv_vals (SimpleRandomVariable:=nodup_simple_random_variable dec srv)).
  Proof.
    simpl.
    apply NoDup_nodup.
  Qed.
  
  End Simple.

  Section Reals.
    
    Context {Ts:Type} 
            {dom: SigmaAlgebra Ts}
            (prts: ProbSpace dom).

    Instance BuildRealRandomVariable
             (rvx: Ts -> R)
             (pf_pre:(forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r))%R)
      : RandomVariable prts borel_sa
      := {
      rv_X := rvx ;
      rv_preimage := borel_sa_preimage rvx pf_pre
        }.

    Lemma RealRandomVariable_is_real
          (rv:RandomVariable prts borel_sa) :
      forall r:R, sa_sigma (fun omega:Ts => (rv_X omega) <= r)%R.
    Proof.
      destruct rv.
      now rewrite  borel_sa_preimage2.
    Qed.

  Definition RealRandomVariable_le 
        (rv1 rv2: RandomVariable prts borel_sa) : Prop :=
    forall (x:Ts), (rv_X (RandomVariable:=rv1) x <= 
                   rv_X (RandomVariable:=rv2) x)%R.

    Class IndicatorRandomVariable
        (rv : RandomVariable prts borel_sa) :=
      irv_binary : forall x, In (rv_X x) [0;1] .

    Global Program Instance IndicatorRandomVariableSimpl 
           (rv : RandomVariable prts borel_sa)
           {irv: IndicatorRandomVariable rv} : SimpleRandomVariable rv
      := {srv_vals := [0;1]}.
    Next Obligation.
      apply irv.
    Qed.

  Lemma sa_singleton (c:R)
    (rv : RandomVariable prts borel_sa) :
    sa_sigma (event_preimage rv_X (singleton_event c)).
  Proof.
     apply sa_le_pt; intros.
     apply borel_sa_preimage2; intros.
     now apply rv_preimage.
  Qed.

  Program Definition EventIndicator (P : event Ts) (dec:forall x, {P x} + {~ P x}) 
    (sap: sa_sigma P) :=
    BuildRealRandomVariable 
      (fun (omega:Ts) => if dec omega then 1 else 0) _.
  Next Obligation.
    destruct (Rlt_dec r 0).
    - assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                          event_none).
      + unfold event_equiv, event_none; intros.
        destruct (dec x); lra.
      + rewrite H; apply sa_none.
    - destruct (Rlt_dec r 1).
      + assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                            (fun omega : Ts => ~ P omega)).
        * unfold event_equiv; intros.
          destruct (dec x).
          -- split; [lra | congruence].
          -- split; [congruence | lra].
        * rewrite H.
          now apply sa_complement.
      + assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                            (fun omega : Ts => True)).
        * unfold event_equiv; intros.
          destruct (dec x); lra.
        * rewrite H.
          apply sa_all.
  Qed.

  Global Instance EventIndicator_indicator (P : event Ts) (dec:forall x, {P x} + {~ P x}) (sap: sa_sigma P)
    : IndicatorRandomVariable (EventIndicator P dec sap).
  Proof.
    intros x.
    simpl.
    match_destr; tauto.
  Qed.

  Definition point_preimage_indicator
    (rv : RandomVariable prts borel_sa)
    (c:R) :=
    EventIndicator (fun omega => rv_X omega = c) (fun x => Req_EM_T (rv_X x) c) 
                   (sa_singleton c rv).

  Class PositiveRandomVariable
        {prts: ProbSpace dom}
        (rv: RandomVariable prts borel_sa) : Prop :=
    prv : forall (x:Ts), (0 <= rv_X x)%R.

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


  Program Definition rvscale (c: R) (rv : RandomVariable prts borel_sa) :=
    BuildRealRandomVariable (fun omega => c * (rv_X omega)) _.
  Next Obligation.
    destruct rv.
    apply scale_measurable.
    apply borel_sa_preimage2; intros.
    now apply rv_preimage0.
 Qed.

  Lemma positive_scale_prv (c:posreal) 
        {rrv : RandomVariable prts borel_sa} 
        (prv : PositiveRandomVariable rrv): 
    PositiveRandomVariable (rvscale c rrv).
  Proof.
    unfold PositiveRandomVariable in *.
    unfold rv_X; simpl.
    intros.
    assert (0 < c) by apply (cond_pos c).
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
          {rv:RandomVariable prts cod}.

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
             {rrv : RandomVariable Prts borel_sa}
             (srv : SimpleRandomVariable rrv) : list (event Ts) :=
    map (event_preimage rv_X) (map singleton_event srv_vals).
    
  Definition SimpleExpectation
             (rrv : RandomVariable Prts borel_sa)
             {srv : SimpleRandomVariable rrv} : R :=
    list_sum (map (fun v => Rmult v (ps_P (event_preimage rv_X (singleton_event v)))) 
                  (nodup Req_EM_T srv_vals)).

  
  Global Program Instance scale_constant_random_variable (c: R)
         {rrv : RandomVariable Prts borel_sa}
         (crv:ConstantRandomVariable rrv) : ConstantRandomVariable (rvscale Prts c rrv)
    := { srv_val := Rmult c srv_val }.
  Next Obligation.
    destruct crv.
    unfold srv_val.
    now rewrite (srv_val_complete0 x).
  Qed.

  Global Program Instance srvscale (c: R)
         {rrv : RandomVariable Prts borel_sa}                      
         (srv:SimpleRandomVariable rrv) : SimpleRandomVariable (rvscale Prts c rrv)
    := { srv_vals := map (fun v => Rmult c v) srv_vals }.
  Next Obligation.
    destruct srv.
    rewrite in_map_iff.
    exists (rv_X x).
    split; trivial.
  Qed.

(* move these two lemmas out *)
Lemma map_in_inj_strong {A B} (f:A->B) a (l:list A) :
  (forall a b, In (f a) (map f l) -> In (f b) (map f l) -> f a = f b -> a = b) ->
  In (f a) (map f l) -> In a l.
Proof.
  intros inj HH.
  apply in_map_iff in HH.
  destruct HH as [x [eqqx inx]].
  rewrite (inj a x); trivial.
  - rewrite <- eqqx.
    now apply in_map.
  - now apply in_map.
  - congruence.
Qed.
   
Lemma nodup_map_inj {A B} decA decB (f:A->B) (l:list A) :
  (forall a b, In (f a) (map f l) -> In (f b) (map f l) -> f a = f b -> a = b) ->
  nodup decB (map f l) = map f (nodup decA l).
Proof.
  intros inj.
  induction l; simpl; trivial.
  assert (forall a b : A, In (f a) (map f l) -> In (f b) (map f l) -> f a = f b -> a = b).
  { simpl in inj.
    intuition.
  } 
  rewrite IHl by trivial.
  match_destr; match_destr.
  - apply map_in_inj_strong in i; trivial.
    congruence.
  - elim n.
    now apply in_map.
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

  Lemma nodup_const_map (c r:R) (l : list R) :
    [c] = nodup Req_EM_T (map (fun _ : R => c) (r :: l)).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl.
    match_destr.
    simpl.
    intuition.
  Qed.
  
  Lemma scaleSimpleExpectation (c:R)
        (rrv : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rrv} : 
    (c * SimpleExpectation rrv)%R = SimpleExpectation (rvscale _ c rrv).
  Proof.
    unfold SimpleExpectation, srvscale.
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
        (rv : RandomVariable Prts borel_sa)                      
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
    apply sa_singleton.
    now apply sa_complement.
    apply event_disjoint_complement.
    apply event_union_complement.
    apply classic_event_lem.
  Qed.

  Lemma list_prod_concat {A B} (l1:list A) (l2:list B) : list_prod l1 l2 = concat (map (fun x => map (fun y => (x, y)) l2) l1).
  Proof.
    induction l1; simpl; trivial.
    now rewrite IHl1.
  Qed.


  Lemma sa_sigma_inter_pts
         (rv1 rv2: RandomVariable Prts borel_sa)
         (c1 c2 : R) :
    sa_sigma (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = c1 /\ 
                                rv_X (RandomVariable:=rv2) omega = c2).
  Proof.
        apply sa_inter.
        apply sa_singleton.
        apply sa_singleton.        
  Qed.

  Require Import Classical_Prop.
    Lemma zero_prob_or_witness (E : event Ts) :
      ps_P E <> 0 -> exists (x:Ts), E x.
    Proof.
      intros.
      apply NNPP.
      intro x.
      apply H.
      cut (E === event_none).
      - intros HH; rewrite HH.
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

  Definition rvopp (rv : RandomVariable Prts borel_sa) := rvscale Prts (-1) rv.

  Definition srvopp 
             (rrv : RandomVariable Prts borel_sa)
             {srv:SimpleRandomVariable rrv} :=
    srvscale (-1) srv.    

  Lemma oppSimpleExpectation
         (rrv : RandomVariable Prts borel_sa)                      
         {srv : SimpleRandomVariable rrv} : 
    (- SimpleExpectation rrv)%R = SimpleExpectation (rvopp rrv).
  Proof.
    replace (- SimpleExpectation rrv) with (-1 * SimpleExpectation rrv) by lra.
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

  Program Definition rvplus (rv1 rv2 : RandomVariable Prts borel_sa) :=
    BuildRealRandomVariable Prts
                            (fun omega =>
                               (rv_X (RandomVariable:=rv1) omega) + 
                               (rv_X (RandomVariable:=rv2) omega) ) _.
  Next Obligation.
    destruct rv1.
    destruct rv2.
    apply sum_measurable.
    apply borel_sa_preimage2; intros.
    now apply rv_preimage0.
    apply borel_sa_preimage2; intros.    
    now apply rv_preimage1.
 Qed.

  Global Program Instance srvplus
         {rv1 rv2 : RandomVariable Prts borel_sa}                      
         (srv1:SimpleRandomVariable rv1)
         (srv2:SimpleRandomVariable rv2)
    : SimpleRandomVariable (rvplus rv1 rv2)
    := { srv_vals := map (fun ab => Rplus (fst ab) (snd ab)) 
                         (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                    (srv_vals (SimpleRandomVariable:=srv2))) }.
  Next Obligation.
    destruct srv1.
    destruct srv2.
    rewrite in_map_iff.
    exists ((rv_X (RandomVariable:=rv1) x), (rv_X (RandomVariable:=rv2) x)).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

  Definition rvminus (rv1 rv2 : RandomVariable Prts borel_sa) := 
    rvplus rv1 (rvopp rv2).

  Definition srvminus 
             (rv1 rv2 : RandomVariable Prts borel_sa)
             {srv1 : SimpleRandomVariable rv1}
             {srv2 : SimpleRandomVariable rv2} :=     
    rvplus rv1 (rvopp rv2).

  Class NonEmpty (A : Type) :=
  ex : A.

  Lemma non_empty_srv_vals 
         {rv: RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rv) :
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
        {rv: RandomVariable Prts borel_sa}                      
        (srv : SimpleRandomVariable rv) :
    srv_vals = nil -> (forall (x:Ts), False).
    Proof.
      intros.
      destruct srv.
      unfold srv_vals in *; subst.
      simpl in srv_vals_complete0.
      now specialize (srv_vals_complete0 x).
  Qed.

    (* should move to RealAdd *)
    Lemma Rsqrt_le (x y : nonnegreal) : 
      x <= y <-> Rsqrt x <= Rsqrt y.
    Proof.
      split; intros.
      - apply Rsqr_incr_0; try apply Rsqrt_positivity.
        unfold Rsqr.
        now repeat rewrite Rsqrt_Rsqrt.
      - rewrite <- (Rsqrt_Rsqrt x).
        rewrite <- (Rsqrt_Rsqrt y).
        apply Rsqr_incr_1; try apply Rsqrt_positivity.
        trivial.
    Qed.

    Lemma Rsqrt_sqr (x:nonnegreal) :
      Rsqrt {| nonneg := x²; cond_nonneg := Rle_0_sqr x |} = x.
    Proof.
      unfold Rsqr.
      apply Rsqr_inj.
      - apply Rsqrt_positivity.
      - apply cond_nonneg.
      - unfold Rsqr. rewrite Rsqrt_Rsqrt.
        trivial.
    Qed.
          
    Lemma Rsqr_le_to_Rsqrt (r x:nonnegreal):
      x² <= r <-> x <= Rsqrt r.
    Proof.
      intros.
      etransitivity.
      - eapply (Rsqrt_le (mknonnegreal _ (Rle_0_sqr x)) r).
      - rewrite Rsqrt_sqr.
        intuition.
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

  Lemma Rsqr_continuous :
    continuity Rsqr.
  Proof.
    apply derivable_continuous.
    apply derivable_Rsqr.
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

  Program Definition rvsqr (rv : RandomVariable Prts borel_sa) :=
    BuildRealRandomVariable Prts
                            (fun omega => Rsqr (rv_X omega)) _.
  Next Obligation.
    destruct rv.
    apply Rsqr_measurable.
    apply borel_sa_preimage2; intros.
    now apply rv_preimage0.
 Qed.

  Global Program Instance srvsqr
         {rv : RandomVariable Prts borel_sa}                      
         (srv:SimpleRandomVariable rv) : SimpleRandomVariable (rvsqr rv)
    := { srv_vals := map Rsqr srv_vals }.
  Next Obligation.
    destruct srv.
    now apply in_map.
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
  
  Program Definition rvmult (rv1 rv2 : RandomVariable Prts borel_sa) :=
    BuildRealRandomVariable Prts
                            (fun omega =>
                               (rv_X (RandomVariable:=rv1) omega) * 
                               (rv_X (RandomVariable:=rv2) omega) ) _.
  Next Obligation.
    destruct rv1.
    destruct rv2.
    apply product_measurable.
    apply borel_sa_preimage2; intros.
    now apply rv_preimage0.
    apply borel_sa_preimage2; intros.    
    now apply rv_preimage1.
 Qed.

  Global Program Instance srvmult
         {rv1 rv2 : RandomVariable Prts borel_sa}                      
         (srv1:SimpleRandomVariable rv1)
         (srv2:SimpleRandomVariable rv2)
    : SimpleRandomVariable (rvmult rv1 rv2)
    := { srv_vals := map (fun ab => Rmult (fst ab) (snd ab)) 
                         (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                    (srv_vals (SimpleRandomVariable:=srv2))) }.
  Next Obligation.
    destruct srv1.
    destruct srv2.
    rewrite in_map_iff.
    exists ((rv_X (RandomVariable:=rv1) x), (rv_X (RandomVariable:=rv2) x)).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.


   Lemma list_union_srv_preimage
         {rv: RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rv) :
     (list_union (map (fun (x : R) (omega : Ts) => rv_X omega = x) srv_vals)) ===  Ω .
   Proof.
     intros x.
     unfold Ω.
     split; trivial; intros _.
     unfold list_union.
     generalize (srv_vals_complete x); intros HH2.
     exists (fun (omega : Ts) => rv_X (RandomVariable:=rv) omega = rv_X x).
     split; trivial.
     apply in_map_iff.
     exists (rv_X x).
     split; trivial.
   Qed.

   Lemma srv_nodup_preimage_list_union
         {rv: RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rv) :
     (list_union (map (fun (x : R) (omega : Ts) => rv_X omega = x) (nodup Req_EM_T srv_vals))) ===  Ω .
   Proof.
     intros x.
     unfold Ω.
     split; trivial; intros _.
     unfold list_union.
     generalize (srv_vals_complete x); intros HH2.
     exists (fun (omega : Ts) => rv_X (RandomVariable:=rv) omega = rv_X x).
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
         {rv: RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rv) :
     ForallOrdPairs event_disjoint (map (fun (x : R) (omega : Ts) => rv_X omega = x) (nodup Req_EM_T srv_vals)).
   Proof.
     intros.
     apply event_disjoint_preimage_disj.
     apply NoDup_nodup.
   Qed.

   Lemma srv_vals_nodup_preimage_sa  {rv: RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rv) :
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
     
   Lemma list_sum_fold_right l : list_sum l = fold_right Rplus 0 l.
   Proof.
     induction l; firstorder.
   Qed.


   Lemma srv_vals_prob_1 
         {rv: RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rv) :
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
     - apply srv_vals_nodup_preimage_sa.
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
     Admitted.

*)

   Lemma simple_random_all
         {rv: RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rv) :
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
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2)
         (a:R) :
    NoDup (srv_vals (SimpleRandomVariable := srv2)) ->
    ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = a) =
    list_sum
      (map (fun x : R => ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = a /\ 
                                                 rv_X (RandomVariable:=rv2) omega = x)) 
           (srv_vals (SimpleRandomVariable:=srv2))).
    Proof.
      intros.
      rewrite list_sum_fold_right.
      rewrite <- map_map.
      rewrite <- ps_list_disjoint_union.
      - replace (map (fun (x : R) (omega : Ts) => rv_X omega = a /\ rv_X omega = x) srv_vals)
          with (map (event_inter (fun omega => rv_X (RandomVariable:=rv1) omega = a))
                    (map (fun x => (fun omega => rv_X (RandomVariable:=rv2) omega = x)) 
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
        apply sa_sigma_inter_pts.
      - now apply event_disjoint_and_preimage_disj.
    Qed.
    
  Lemma prob_inter_all2
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2)
         (a:R) :
    NoDup (srv_vals (SimpleRandomVariable := srv1)) ->
    ps_P (fun omega : Ts => rv_X (RandomVariable:=rv2) omega = a) =
    list_sum
      (map (fun x : R => ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = x /\ 
                                                 rv_X (RandomVariable:=rv2) omega = a)) 
           (srv_vals (SimpleRandomVariable:=srv1))).
  Proof.
    intros.
    generalize (prob_inter_all1 srv2 srv1 a H); intros.
    rewrite map_ext with 
        (g := (fun x : R => ps_P (fun omega : Ts => rv_X (RandomVariable:=rv2) omega = a /\ 
                                                    rv_X (RandomVariable:=rv1) omega = x))); trivial.
    intros.
    now apply ps_proper.
  Qed.

  Lemma RefineEvent
        (E : event Ts) (lE : list (event Ts)):
    (list_union lE) ===  Ω ->
    E === list_union (map (event_inter E) lE).
  Proof.
    intros.
    rewrite <- event_inter_list_union_distr.
    rewrite H.
    now rewrite event_inter_true_r.
  Qed.

  Lemma RefineSimpleExpectation
        (rv rv2 : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        {srv2 : SimpleRandomVariable rv2} :  
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X (RandomVariable:=rv) omega = v))
           (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv)))) = 
    list_sum
      (map (fun vv : R*R => 
              (fst vv) * ps_P (fun omega : Ts => rv_X (RandomVariable:=rv) omega = fst vv /\
                                                 rv_X (RandomVariable:=rv2) omega = snd vv))
           (list_prod (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv)))
                      (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv2))))).
  Proof.
    induction ((@nodup R Req_EM_T (@srv_vals Ts R dom Prts borel_sa rv srv))); simpl; trivial.
    rewrite IHl.
    rewrite map_app.
    rewrite list_sum_cat.
    f_equal.
    rewrite map_map.
    simpl.
    transitivity (list_sum (List.map (fun z => a*z)
                                     (map (fun x : R => ps_P (fun omega : Ts => (rv_X (RandomVariable:=rv)) omega = a /\ (rv_X (RandomVariable:=rv2)) omega = x)) (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv2)))))).
    - rewrite list_sum_mult_const.
      f_equal.
      rewrite map_map.
     apply (prob_inter_all1 (nodup_simple_random_variable Req_EM_T srv) (nodup_simple_random_variable Req_EM_T srv2) a); simpl; try apply NoDup_nodup.
    - now rewrite map_map.
  Qed.

  Lemma SimpleExpectation_le 
        (rv1 rv2 : RandomVariable Prts borel_sa)
        {srv1 : SimpleRandomVariable rv1}
        {srv2 : SimpleRandomVariable rv2} : 
    RealRandomVariable_le Prts rv1 rv2 ->
    SimpleExpectation rv1 <= SimpleExpectation rv2.
  Proof.
    unfold RealRandomVariable_le, SimpleExpectation.
    intros.
    unfold event_preimage, singleton_event.
    rewrite (RefineSimpleExpectation  rv1 rv2).
    rewrite (RefineSimpleExpectation  rv2 rv1).
    generalize (@sa_sigma_inter_pts rv1 rv2); intros sa_sigma.
    destruct rv1; destruct rv2.
    destruct srv1; destruct srv2.
    unfold rv_X, srv_vals in *.
    replace 
      (list_sum (map
         (fun vv : R * R =>
            fst vv * ps_P (fun omega : Ts => rv_X1 omega = fst vv /\ rv_X0 omega = snd vv))
         (list_prod (nodup Req_EM_T srv_vals1) (nodup Req_EM_T srv_vals0)))) with
      (list_sum (map
           (fun vv : R * R =>
              snd vv * ps_P (fun omega : Ts => rv_X0 omega = fst vv /\ rv_X1 omega = snd vv))
           (list_prod (nodup Req_EM_T srv_vals0) (nodup Req_EM_T srv_vals1)))).
    - apply list_sum_le; intros.
      assert ((ps_P (fun omega : Ts => rv_X0 omega = fst a /\ rv_X1 omega = snd a)) = 0 \/
              fst a <= snd a).
      + destruct (Req_EM_T (ps_P (fun omega : Ts => rv_X0 omega = fst a /\ rv_X1 omega = snd a)) 0).
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
                         rv_X0 omega = fst (snd x, fst x) /\ 
                         rv_X1 omega = snd (snd x, fst x)))
                 (fun vv : R * R =>
                    fst vv * ps_P (fun omega : Ts => rv_X1 omega = fst vv /\ 
                                                     rv_X0 omega = snd vv))).
      apply Permutation.Permutation_refl.
      intros.
      unfold snd.
      f_equal.
      apply ps_proper.
      unfold event_equiv; intros.
      intuition.
    Qed.

  Lemma sumSimpleExpectation00
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2) :
    (srv_vals (SimpleRandomVariable := srv2)) <> nil ->
    NoDup (srv_vals (SimpleRandomVariable := srv1)) ->
    NoDup (srv_vals (SimpleRandomVariable := srv2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = v))
           (srv_vals (SimpleRandomVariable := srv1))) =
    list_sum
      (map
       (fun v : R * R =>
          (fst v) *
          ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = fst v /\ 
                                  rv_X (RandomVariable:=rv2) omega = snd v))
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
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2) :
    (srv_vals (SimpleRandomVariable := srv1)) <> nil ->
    NoDup (srv_vals (SimpleRandomVariable := srv1)) ->
    NoDup (srv_vals (SimpleRandomVariable := srv2)) ->    
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X (RandomVariable:=rv2) omega = v))
           (srv_vals (SimpleRandomVariable := srv2))) =
    list_sum
      (map
       (fun v : R * R =>
          (snd v) *
          ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = fst v /\ 
                                  rv_X (RandomVariable:=rv2) omega = snd v))
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
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2) :
    (srv_vals (SimpleRandomVariable := srv2)) <> nil ->
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = v))
           (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv1)))) =
    list_sum
      (map
       (fun v : R * R =>
          (fst v) *
          ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = fst v /\ 
                                  rv_X (RandomVariable:=rv2) omega = snd v))
       (list_prod (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv1))) 
                  (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv2))))).
   Proof.
     intros.
     apply (sumSimpleExpectation00 (nodup_simple_random_variable Req_EM_T srv1) (nodup_simple_random_variable Req_EM_T srv2)); simpl; try apply NoDup_nodup.
     now apply nodup_not_nil.
   Qed.


   Lemma sumSimpleExpectation1
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2) :      
    (srv_vals (SimpleRandomVariable := srv1)) <> nil ->
    list_sum
      (map (fun v : R => v * ps_P (fun omega : Ts => rv_X (RandomVariable:=rv2) omega = v))
           (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv2)))) =
    list_sum
      (map
       (fun v : R * R =>
          (snd v) *
          ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = fst v /\ 
                                  rv_X (RandomVariable:=rv2) omega = snd v))
       (list_prod (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv1))) 
                  (nodup Req_EM_T (srv_vals (SimpleRandomVariable := srv2))))).
   Proof.
     intros.
     apply (sumSimpleExpectation11 (nodup_simple_random_variable Req_EM_T srv1) (nodup_simple_random_variable Req_EM_T srv2)); simpl; try apply NoDup_nodup.
     now apply nodup_not_nil.
   Qed.

    Require Import cond_expt.

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
         {rv: RandomVariable Prts borel_sa}                      
         (c d: R) :
    c <> d ->
    event_disjoint (fun omega => rv_X (RandomVariable:=rv) omega = c)
                   (fun omega => rv_X (RandomVariable:=rv) omega = d).
   Proof.
     unfold event_disjoint.
     congruence.
   Qed.

  Lemma preimage_point_pairs_disjoint
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (c1 c2 d1 d2: R) :
    (c1 <> d1) \/ (c2 <> d2) ->
    event_disjoint (event_inter (fun omega => rv_X (RandomVariable:=rv1) omega = c1)
                                (fun omega => rv_X (RandomVariable:=rv2) omega = c2))
                   (event_inter (fun omega => rv_X (RandomVariable:=rv1) omega = d1)
                                (fun omega => rv_X (RandomVariable:=rv2) omega = d2)).
  Proof.
    intros.
    unfold event_disjoint, event_inter; intros.
    destruct H0; destruct H1.
    destruct H; congruence.
  Qed.    

  Lemma concat_NoDup {A} (l:list (list A)) : NoDup (concat l) -> Forall (@NoDup A) l.
    Proof.
      induction l; simpl; intros nd.
      - constructor.
      - constructor.
        + eapply NoDup_app_inv; eauto.
        + apply IHl. eapply NoDup_app_inv2; eauto.
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

  Lemma nodup_app2_incl {A} decA (l1 l2:list A) :
    incl l1 l2 ->
    nodup decA (l1 ++ l2) = nodup decA l2.
  Proof.
    unfold incl; intros inn.
    induction l1; simpl; trivial; simpl in *.
    match_destr.
    - eauto.
    - elim n.
      apply in_app_iff.
      eauto.
  Qed.

  Lemma nodup_app_distr {A} decA (l1 l2:list A) :
    disjoint l1 l2 ->
    nodup decA (l1 ++ l2) = nodup decA l1 ++ nodup decA l2.
  Proof.
    unfold disjoint.
    intros disj.
    induction l1; simpl; trivial.
    rewrite IHl1 by firstorder.
    destruct (in_dec decA a l1).
    - match_destr.
      elim n.
      apply in_app_iff; auto.
    - match_destr.
      apply in_app_iff in i.
      elim (disj a); simpl; intuition.
  Qed.
    
  Lemma list_prod_nodup {A B} decA decB decAB (l1:list A) (l2:list B):
    nodup decAB (list_prod l1 l2) = list_prod (nodup decA l1) (nodup decB l2).
  Proof.
    repeat rewrite list_prod_concat.
    revert l2.
    induction l1; simpl; trivial.
    intros l2.
    match_destr.
    - rewrite <- IHl1.
      apply nodup_app2_incl.
      intros x inn.
      apply concat_In.
      eexists.
      split; try eassumption.
      apply in_map_iff.
      eauto.
    - simpl.
      rewrite <- IHl1.
      rewrite nodup_app_distr.
      + f_equal.
        induction l2; simpl; trivial.
        rewrite IHl2.
        match_destr.
        * apply in_map_iff in i.
          destruct i as [x [eqq xin]].
          invcs eqq.
          match_destr.
          congruence.
        * match_destr.
          elim n0.
          apply in_map_iff.
          eauto.
      + unfold disjoint.
        intros [x y] inn HH.
        apply concat_In in HH.
        destruct HH as [xx [xxin xinn]].
        apply in_map_iff in xxin.
        destruct xxin as [xxx [? xxxin]]; subst.
        apply in_map_iff in inn.
        destruct inn as [? [eqq ?]].
        invcs eqq; subst.
        apply in_map_iff in xinn.
        destruct xinn as [? [eqq ?]].
        invcs eqq.
        congruence.
  Qed.

  Existing Instance Equivalence_pullback.

  Instance EqDec_pullback {A B} (R:A->A->Prop) {eqR:Equivalence R} {decR:EqDec A R} (f:B->A) :
    EqDec B (fun x y : B => R (f x) (f y)).
  Proof.
    intros x y.
    destruct (decR (f x) (f y)).
    - left; trivial.
    - right; trivial.
  Defined.

  Lemma add_to_bucket_map {A B:Type} (R:A->A->Prop) {eqR:Equivalence R} {decR:EqDec A R} (l:list (list B)) 
          (f:B->A) b :
    add_to_bucket R (f b) (map (map f) l) = 
    map (map f) (add_to_bucket (fun x y : B => R (f x) (f y)) b l).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl.
    destruct a; simpl; trivial.
    unfold equiv_dec, EqDec_pullback.
    match_destr.
  Qed.
    
  Lemma quotient_map {A B:Type} (R:A->A->Prop) {eqR:Equivalence R} {decR:EqDec A R} (l:list B) 
          (f:B->A) :
    quotient R (map f l) = map (map f) (quotient  (fun x y : B => R (f x) (f y)) l).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl.
    apply add_to_bucket_map.
  Qed.

  Lemma add_to_bucket_eq_nin {A} (decA:EqDec A eq) a l :
    Forall (fun x : list A => not_nil x = true) l ->
      (forall l' : list A, In l' l -> ~ In a l') ->
    (add_to_bucket eq a l) = l++[[a]].
  Proof.
    intros.
    induction l; simpl; trivial.
    invcs H.
    match_destr.
    match_destr.
    - red in e; subst.
      simpl in H0.
      eelim H0; eauto.
      simpl; eauto.
    - simpl in *.
      rewrite IHl; eauto.
  Qed.

  Require Import Permutation.

  Lemma nodup_hd_quotient {A} (decA:EqDec A eq) def (l:list A) : 
    Permutation ((map (hd def) (quotient eq l)))
                (nodup decA l).
  Proof.
    induction l; simpl; trivial.
    match_destr.
    - rewrite <- IHl.
      apply (quotient_in eq) in i.
      match goal with
      | [|- Permutation ?l1 ?l2 ] => replace l1 with l2; [reflexivity | ]
      end.
      revert i.
      clear.
      generalize (quotient_nnil eq l).
      generalize (quotient_all_equivs eq l).
      generalize (quotient_all_different eq l).
      generalize (quotient eq l); clear; intros l.
      unfold all_different, all_equivs, is_equiv_class, ForallPairs.
      repeat rewrite Forall_forall.
      unfold not_nil.
      intros alldiff alleq nnil [l' [l'in ain]].
      induction l; simpl in *.
      + tauto.
      + destruct a0.
        * specialize (nnil []); simpl in nnil; intuition.
        * match_destr.
          -- red in e; subst; trivial.
          -- destruct l'in.
             ++ subst.
                elim c.
                apply (alleq (a0::a1)); simpl; eauto.
             ++ simpl.
                rewrite <- IHl; auto.
                now invcs alldiff.
                firstorder.
    - rewrite add_to_bucket_eq_nin.
      + rewrite map_app; simpl.
        rewrite <- Permutation_cons_append.
        now apply perm_skip.
      + apply quotient_nnil.
      + intros l' inn1 inn2.
        generalize (in_quotient eq a l).
        eauto.
  Qed.

  Lemma nodup_map_nodup {A B} decA decB (f:A->B) (l:list A) :
    nodup decB (map f (nodup decA l)) = nodup decB (map f l).
  Proof.
    induction l; simpl; trivial.
    match_destr; match_destr.
    + elim n.
      apply in_map_iff; eauto.
    + simpl.
      match_destr.
      elim n0.
      eapply in_map_iff.
      eapply in_map_iff in i.
      destruct i as [? [? inn]].
      eapply nodup_In in inn.
      eauto.
    + simpl.
      rewrite IHl.
      match_destr.
      elim n0.
      eapply in_map_iff in i.
      destruct i as [? [? inn]].
      apply nodup_In in inn.
      apply in_map_iff.
      eauto.
  Qed.

  Lemma add_to_bucket_ext {A:Type} (R1 R2:A->A->Prop) {eqR1:Equivalence R1} {decR1:EqDec A R1} {eqR2:Equivalence R2} {decR2:EqDec A R2} a (l:list (list A)) :
    (forall l' y, In y l' -> In l' l -> R1 a y <-> R2 a y) ->
    add_to_bucket R1 a l = add_to_bucket R2 a l.
  Proof.
    intros.
    induction l; simpl; trivial.
    cut_to IHl; [| firstorder].
    rewrite IHl.
    specialize (H a0); simpl in H.
    match_destr; simpl in *.
    repeat match_destr; unfold equiv, complement in *; firstorder.
  Qed.
    
  Lemma quotient_ext {A:Type} (R1 R2:A->A->Prop) {eqR1:Equivalence R1} {decR1:EqDec A R1} {eqR2:Equivalence R2} {decR2:EqDec A R2} (l:list A) :
    ForallPairs (fun x y => R1 x y <-> R2 x y) l ->
    quotient R1 l = quotient R2 l.
  Proof.
    unfold ForallPairs.
    induction l; simpl; intros; trivial.
    rewrite IHl by eauto.
    apply add_to_bucket_ext.
    intros.
    eapply H; eauto.
    right.
    eapply in_quotient; eauto.
  Qed.

  Lemma all_different_same_eq {A} R {eqR:Equivalence R} (l:list (list A)) l1 l2 a b:
    all_different R l ->
    In l1 l ->
    In l2 l ->
    In a l1 ->
    In b l2 ->
    R a b ->
    l1 = l2.
  Proof.
    induction l; simpl; intros.
    - tauto.
    - unfold all_different in H.
      invcs H.
      rewrite Forall_forall in H7.
      unfold different_buckets in H7.
      destruct H0; destruct H1; subst.
      + trivial.
      + specialize (H7 _ H0 _ _ H2 H3).
        congruence.
      + specialize (H7 _ H _ _ H3 H2).
        symmetry in H4.
        congruence.
      + apply IHl; eauto.
  Qed.
    
  Lemma sumSimpleExpectation 
         (rv1 rv2: RandomVariable Prts borel_sa)                      
         {srv1 : SimpleRandomVariable rv1} 
         {srv2 : SimpleRandomVariable rv2} :      
    NonEmpty Ts -> (SimpleExpectation rv1) + (SimpleExpectation rv2)%R = 
    SimpleExpectation (rvplus rv1 rv2).
   Proof.
    unfold SimpleExpectation; intros.
    generalize (non_empty_srv_vals srv1 X); intros.
    generalize (non_empty_srv_vals srv2 X); intros.    
    generalize (sumSimpleExpectation0 srv1 srv2 H0); intros.
    generalize (sumSimpleExpectation1 srv1 srv2 H); intros.   
    generalize (@sa_sigma_inter_pts rv1 rv2). intro sa_sigma.
    destruct srv1.
    destruct srv2.
    unfold srv_vals in *; intros.
    unfold srvplus.

    destruct rv1.
    destruct rv2.
    unfold rv_X in *.
    simpl.
    unfold singleton_event, event_preimage.
    transitivity (list_sum
                    (map (fun v : R*R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X0 omega = fst v /\ rv_X1 omega = snd v))
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
       (fun v : R * R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X0 omega = fst v /\ rv_X1 omega = snd v))
       (nodup HH (list_prod srv_vals0 srv_vals1)))).
      + f_equal.
        f_equal.
        symmetry.
        apply list_prod_nodup.
      + transitivity (list_sum
                        (map (fun v : R => v * ps_P (fun omega : Ts => rv_X0 omega + rv_X1 omega = v))
                             (nodup Req_EM_T (map (fun ab : R * R => fst ab + snd ab) (nodup HH (list_prod srv_vals0 srv_vals1)))))).
        * generalize (NoDup_nodup HH (list_prod srv_vals0 srv_vals1)).
          assert (Hcomplete:forall x y, In (rv_X0 x, rv_X1 y) (nodup HH (list_prod srv_vals0 srv_vals1))).
          { intros.
            apply nodup_In.
            apply in_prod; eauto.
          }
          revert Hcomplete.
          generalize (nodup HH (list_prod srv_vals0 srv_vals1)). (* clear. *)
          intros.
          transitivity (list_sum
                          (map
                             (fun v : R * R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X0 omega = fst v /\ rv_X1 omega = snd v))
                             (concat (quotient sums_same l)))).
          { apply list_sum_Proper. apply Permutation.Permutation_map. symmetry. apply unquotient_quotient.
          } 
          rewrite concat_map.
          rewrite list_sum_map_concat.
          rewrite map_map.

          transitivity (
              list_sum
                (map (fun v : R => v * ps_P (fun omega : Ts => rv_X0 omega + rv_X1 omega = v))
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
             transitivity ((fst p + snd p) * ps_P (fun omega : Ts => rv_X0 omega = fst p /\ rv_X1 omega = snd p) +
             list_sum
               (map
                  (fun v : R * R => (fst p + snd p) * ps_P (fun omega : Ts => rv_X0 omega = fst v /\ rv_X1 omega = snd v))
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
                    list_sum (map (fun x : R * R => ps_P (fun omega : Ts => rv_X0 omega = fst x /\ rv_X1 omega = snd x)) (p::a))); [reflexivity |].
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
                       exists (fun (omega : Ts) => rv_X0 omega = rv_X0 x /\ rv_X1 omega = rv_X1 x).
                       split; [| tauto].
                       apply in_map_iff.
                       exists (rv_X0 x, rv_X1 x).
                       split; [reflexivity | ].
                       assert (Hin:In (rv_X0 x, rv_X1 x) l) by apply Hcomplete.
                       destruct (quotient_in sums_same _ _ Hin) as [xx [xxin inxx]].
                       rewrite <- (all_different_same_eq sums_same (quotient sums_same l) xx (p::a) (rv_X0 x, rv_X1 x) (fst p, snd p)); simpl; trivial.
                       destruct p; eauto.
                ** intros.
                   apply in_map_iff in H3.
                   destruct H3 as [xx [? xxin]]; subst.
                   apply sa_sigma.
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
    ForallOrdPairs event_disjoint l /\ list_union l = Ω.

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
             (rv : RandomVariable Prts borel_sa)
             {srv : SimpleRandomVariable rv}
             (dec:forall x, {P x} + {~ P x})        
             (sap: sa_sigma P) :=
    rvscale _ ((SimpleExpectation (rvmult rv (EventIndicator Prts P dec sap))) / (ps_P P))
            ((EventIndicator Prts P dec sap)).

  Instance gen_simple_conditional_expectation_scale_simpl (P : event Ts)
           (rv : RandomVariable Prts borel_sa)
           (srv : SimpleRandomVariable rv) 
           (dec:forall x, {P x} + {~ P x})        
           (sap: sa_sigma P) :
    SimpleRandomVariable (gen_simple_conditional_expectation_scale P rv dec sap).
  Proof.
    typeclasses eauto.
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

  Definition gen_SimpleConditionalExpectation
             (rv : RandomVariable Prts borel_sa)
             {srv : SimpleRandomVariable rv}
             (l : list (event Ts))
             (sap_all : forall p, In p l -> sa_sigma p)
             (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :=
    fold_right rvplus (rvconst 0)
               (map_dep l (fun p pf => gen_simple_conditional_expectation_scale p rv (dec_all p pf) (sap_all p pf))).

  Instance gen_SimpleConditionalExpectation_simpl
             (rv : RandomVariable Prts borel_sa)
             {srv : SimpleRandomVariable rv}
             (l : list (event Ts))
             (sap_all : forall p, In p l -> sa_sigma p)
             (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :
    SimpleRandomVariable (gen_SimpleConditionalExpectation rv l sap_all dec_all).
  Proof.
    unfold gen_SimpleConditionalExpectation.
    induction l; simpl.
    - apply srvconst.
      apply crvconst.
    - apply srvplus.
      + apply gen_simple_conditional_expectation_scale_simpl.
      + apply IHl.
  Qed.

  Lemma dec_complement {A} {p:A->Prop} (dec_p: forall x, {p x} + {~ p x}) :
    forall x, {~ p x} + {~ ~ p x}.
  Proof.
    intros x.
    destruct (dec_p x).
    - right; tauto.
    - left; trivial.
  Defined.
  
  Program Definition gen_SimpleConditionalExpectation_2part
             (rv : RandomVariable Prts borel_sa)
             {srv : SimpleRandomVariable rv}
             (p : event Ts)
             (sap : sa_sigma p)
             (dec_p: forall x, {p x} + {~ p x})
    :  RandomVariable Prts borel_sa
    :=    
    rvplus (gen_simple_conditional_expectation_scale p rv dec_p sap)
           (gen_simple_conditional_expectation_scale (event_complement p) rv (dec_complement dec_p) _).
  Next Obligation.
    now apply sa_complement.
  Qed.
  
  Instance gen_SimpleConditionalExpectation_2part_simpl
          (rv : RandomVariable Prts borel_sa)
          {srv : SimpleRandomVariable rv}
          (p : event Ts)
          (sap : sa_sigma p)
          (dec_p: forall x, {p x} + {~ p x})
    : SimpleRandomVariable (gen_SimpleConditionalExpectation_2part rv p sap dec_p).
  Proof.
    unfold gen_SimpleConditionalExpectation_2part.
    typeclasses eauto.
  Qed.
  
  Definition simple_conditional_expectation_scale_coef (c : R)
  {rv rv2: RandomVariable Prts borel_sa}
  (srv : SimpleRandomVariable rv) 
  (srv2 : SimpleRandomVariable rv2) : R :=
    ((SimpleExpectation 
        (rvmult rv 
                 (point_preimage_indicator Prts rv2 c)))
       / (ps_P (event_preimage (rv_X (RandomVariable:=rv2)) (singleton_event c)))).

  Definition SimpleConditionalExpectation_list
             {rv1 rv2 : RandomVariable Prts borel_sa}             
             (srv1 : SimpleRandomVariable rv1) 
             (srv2 : SimpleRandomVariable rv2)
    : list (RandomVariable Prts borel_sa)
    := map (fun c => (rvscale Prts (simple_conditional_expectation_scale_coef c srv1 srv2)
                           (point_preimage_indicator Prts rv2 c)))
           (srv_vals (SimpleRandomVariable:=srv2)).

  Definition simple_conditional_expectation_scale (c:R)
             {rv1 rv2 : RandomVariable Prts borel_sa}             
             (srv1 : SimpleRandomVariable rv1) 
             (srv2 : SimpleRandomVariable rv2) :
    SimpleRandomVariable
      (rvscale Prts (simple_conditional_expectation_scale_coef c srv1 srv2)
               (point_preimage_indicator Prts rv2 c))
    := srvscale (simple_conditional_expectation_scale_coef c srv1 srv2)  
                (IndicatorRandomVariableSimpl Prts (point_preimage_indicator Prts rv2 c)).

  Lemma SimpleConditionalExpectation_list_simple  {rv1 rv2 : RandomVariable Prts borel_sa}             
             (srv1 : SimpleRandomVariable rv1) 
             (srv2 : SimpleRandomVariable rv2) :
    Forallt (@SimpleRandomVariable Ts R dom Prts borel_sa) (SimpleConditionalExpectation_list srv1 srv2).
  Proof.
    unfold SimpleConditionalExpectation_list.
    induction srv_vals; simpl.
    - constructor.
    - constructor; trivial.
      apply simple_conditional_expectation_scale.
  Defined.
  
  Definition SimpleConditionalExpectation
             (rv1 rv2 : RandomVariable Prts borel_sa)
             {srv1 : SimpleRandomVariable rv1}
             {srv2 : SimpleRandomVariable rv2} :=    
    fold_right rvplus (rvconst 0)
               (SimpleConditionalExpectation_list srv1 srv2).

  Instance SimpleConditionalExpectation_simple
           (rv1 rv2 : RandomVariable Prts borel_sa)
           {srv1 : SimpleRandomVariable rv1}
           {srv2 : SimpleRandomVariable rv2} : SimpleRandomVariable (SimpleConditionalExpectation rv1 rv2).
  Proof.
    generalize (SimpleConditionalExpectation_list_simple srv1 srv2).
    unfold SimpleConditionalExpectation; simpl.
    induction (SimpleConditionalExpectation_list srv1 srv2); simpl; intros ft.
    - apply srvconst.
      apply crvconst.
    - invcs ft.
      apply srvplus; eauto.
  Qed.

  Lemma SimpleExpectation_EventIndidcator P dec sap :
    SimpleExpectation (EventIndicator Prts P dec sap) = ps_P P.
  Proof.
    unfold EventIndicator, SimpleExpectation; simpl.
    match_destr.
    - intuition.
    - simpl.
      field_simplify.
      unfold event_preimage, singleton_event.
      apply ps_proper.
      intros x.
      match_destr; intuition.
  Qed.
  

  Definition fold_rvplus
        (rv : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        (l : list (event Ts))
        (sap_all : forall p, In p l -> sa_sigma p)
        (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :=
    (fold_right rvplus (rvconst 0)
                (map_dep l (fun p pf => 
                              rvmult rv (EventIndicator Prts p 
                                                        (dec_all p pf)
                                                        (sap_all p pf))))).

   Instance fold_rvplus_simpl
        (rv : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        (l : list (event Ts))
        (sap_all : forall p, In p l -> sa_sigma p)
        (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :
     SimpleRandomVariable (fold_rvplus rv l sap_all dec_all).
   Proof.
   Admitted.

   Lemma expectation_indicator_sum0
        (rv : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        (l : list (event Ts))
        (sap_all : forall p, In p l -> sa_sigma p)
        (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :
    list_sum
      (map_dep l (fun p pf => SimpleExpectation 
                                (rvmult rv (EventIndicator Prts p 
                                                           (dec_all p pf)
                                                           (sap_all p pf))))) =
    SimpleExpectation
      (fold_rvplus rv l sap_all dec_all).
   Proof.
   Admitted.

   Program Instance SimpleRandomVariable_enlarged
            {rv : RandomVariable Prts borel_sa}
            (srv:SimpleRandomVariable rv)
            (l:list R)
            (lincl : incl srv_vals l)
     : SimpleRandomVariable rv :=
     {
     srv_vals := l
     }.
   Next Obligation.
     apply lincl.
     apply srv_vals_complete.
   Qed.
   
   Lemma SimpleExpectation_simpl_incl (rv : RandomVariable Prts borel_sa) (srv:SimpleRandomVariable rv)
         (l:list R)
         (lincl : incl srv_vals l) :
     SimpleExpectation rv (srv := srv) = SimpleExpectation rv (srv:=SimpleRandomVariable_enlarged srv l lincl).
   Proof.
     unfold SimpleExpectation; simpl.
   Admitted.

     
   Lemma SimpleExpectation_pf_irrel (rv : RandomVariable Prts borel_sa) (srv1 srv2:SimpleRandomVariable rv):
     SimpleExpectation rv (srv := srv1) = SimpleExpectation rv (srv := srv2).
   Proof.

     (* incl preserves it *)
     
   Admitted.
   
   Lemma SimpleExpectation_ext (rv1 rv2 : RandomVariable Prts borel_sa) (srv1:SimpleRandomVariable rv1) (srv2:SimpleRandomVariable rv2):
     rv1 = rv2 ->
     SimpleExpectation rv1 (srv := srv1) = SimpleExpectation rv2 (srv := srv2).
   Proof.
     intros.
     subst.
     apply SimpleExpectation_pf_irrel.
   Qed.
   
  Lemma expectation_indicator_sum
        (rv : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        (l : list (event Ts))
        (is_part: is_partition_list l)
        (sap_all : forall p, In p l -> sa_sigma p)
        (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :
    SimpleExpectation rv = 
    list_sum
      (map_dep l (fun p pf => SimpleExpectation 
                                (rvmult rv (EventIndicator Prts p 
                                                           (dec_all p pf)
                                                           (sap_all p pf)
      )))).
  Proof.
      transitivity
        (SimpleExpectation
           (fold_rvplus rv l sap_all dec_all)).
      - apply SimpleExpectation_ext.
  Admitted.


  Lemma gen_simple_conditional_expectation_scale_tower (P : event Ts) (Ppos:ps_P P > 0)
             (rv : RandomVariable Prts borel_sa)
             {srv : SimpleRandomVariable rv}
             (dec:forall x, {P x} + {~ P x})        
             (sap: sa_sigma P) :
    SimpleExpectation (gen_simple_conditional_expectation_scale P rv dec sap) =
    SimpleExpectation (rvmult rv (EventIndicator Prts P dec sap)).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    generalize (scaleSimpleExpectation (SimpleExpectation (rvmult rv (EventIndicator Prts P dec sap)) / ps_P P)
                                       (EventIndicator Prts P dec sap)); intros HH.
    etransitivity.
    - symmetry. eauto.
    - rewrite SimpleExpectation_EventIndidcator.
      field.
      lra.
  Qed.

  Ltac se_rewrite H :=
    match type of H with
    | @SimpleExpectation _ _ _ ?x ?sx = _ =>
      match goal with
      | [|- context [@SimpleExpectation _ _ _ ?z ?sz]] =>
        rewrite (@SimpleExpectation_pf_irrel x sz sx); rewrite H
      end
    end.
      
  Lemma gen_conditional_tower_law_2part0
        (rv : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        (p : event Ts)
        (sap: sa_sigma p)
        (sanp: sa_sigma (event_complement p))        
        (dec_p: forall x, {p x} + {~ p x})
        (dec_np: forall x, {(event_complement p) x} + {~ (event_complement p) x}) :    
    NonEmpty Ts ->
    (SimpleExpectation (rvmult rv (EventIndicator Prts p dec_p sap))) +
    (SimpleExpectation (rvmult rv (EventIndicator Prts (event_complement p) dec_np sanp))) =
    SimpleExpectation
      (gen_SimpleConditionalExpectation_2part rv p sap dec_p).
  Proof.
    unfold gen_SimpleConditionalExpectation_2part; intro.
    generalize (sumSimpleExpectation 
                  (gen_simple_conditional_expectation_scale p rv dec_p sap)
                  (gen_simple_conditional_expectation_scale 
                     (event_complement p) rv
                     (dec_complement dec_p)
                     (gen_SimpleConditionalExpectation_2part_obligation_1 p sap)) X).
    intros.
    symmetry in H.
    se_rewrite H.

  Admitted.

  Lemma gen_conditional_tower_law
        (rv : RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        (l : list (event Ts))
        (ispart: is_partition_list l)
        (sap_all : forall p, In p l -> sa_sigma p)
        (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :
    SimpleExpectation rv =
    SimpleExpectation
      (gen_SimpleConditionalExpectation rv l sap_all dec_all).
  Proof.
    unfold SimpleExpectation, gen_SimpleConditionalExpectation.
    unfold event_preimage, singleton_event.
    destruct rv; destruct srv.
    unfold srv_vals, rv_X.
    unfold gen_simple_conditional_expectation_scale.
    unfold SimpleExpectation.
    unfold event_preimage, singleton_event.    
    unfold EventIndicator.
    
    Admitted.
      

  Lemma conditional_tower_law
        (rv1 rv2 : RandomVariable Prts borel_sa)
        {srv1 : SimpleRandomVariable rv1}
        {srv2 : SimpleRandomVariable rv2} :
    SimpleExpectation (SimpleConditionalExpectation rv1 rv2) = SimpleExpectation rv1.
    Proof.
      unfold SimpleConditionalExpectation.
      unfold SimpleConditionalExpectation_list.
      unfold SimpleExpectation.
      destruct rv1; destruct rv2.
      destruct srv1; destruct srv2.
      unfold rv_X, srv_vals.
      unfold event_preimage, singleton_event.
      unfold simple_conditional_expectation_scale_coef.
      unfold point_preimage_indicator.
      unfold EventIndicator.
      unfold SimpleExpectation.
      unfold event_preimage, singleton_event.
      Admitted.

   Definition simple_sigma_measurable 
        (rv1 rv2 : RandomVariable Prts borel_sa)
        {srv1 : SimpleRandomVariable rv1}
        {srv2 : SimpleRandomVariable rv2} : Prop :=
     forall (c1:R), In c1 (srv_vals (SimpleRandomVariable:=srv1)) ->
                   forall (c2:R), 
                     In c2 (srv_vals (SimpleRandomVariable:=srv2)) ->
                     (event_disjoint (event_preimage (rv_X (RandomVariable:=rv1))
                                                   (singleton_event c1) )
                                    (event_preimage (rv_X (RandomVariable:=rv2))
                                                   (singleton_event c2))) \/
                     (event_sub (event_preimage (rv_X (RandomVariable:=rv2))
                                               (singleton_event c2) )
                                (event_preimage (rv_X (RandomVariable:=rv1))
                                                   (singleton_event c1))).
   Definition partition_measurable
        (rv: RandomVariable Prts borel_sa)
        {srv : SimpleRandomVariable rv}
        (l : list (event Ts)) : Prop :=
     is_partition_list l ->
     forall (c:R), 
       In c srv_vals ->
       forall (p:event Ts), 
         In p l ->
         (event_disjoint (event_preimage rv_X (singleton_event c)) p) \/
         (event_sub p (event_preimage rv_X (singleton_event c))).

   Lemma gen_conditional_scale_measurable
        (rv1 rv2: RandomVariable Prts borel_sa)
        {srv1 : SimpleRandomVariable rv1}
        {srv2 : SimpleRandomVariable rv2} 
        (l : list (event Ts))
        (is_part: is_partition_list l)
        (sap_all : forall p, In p l -> sa_sigma p)
        (dec_all:  forall p, In p l -> (forall x, {p x} + {~ p x})) :
     partition_measurable rv1 l ->
     gen_SimpleConditionalExpectation (rvmult rv1 rv2) l sap_all dec_all =
     rvmult rv1 (gen_SimpleConditionalExpectation rv2 l  sap_all dec_all).
     Proof.
       Admitted.

   Lemma conditional_scale_measurable
        (rv1 rv2 rv3: RandomVariable Prts borel_sa)
        {srv1 : SimpleRandomVariable rv1}
        {srv2 : SimpleRandomVariable rv2} 
        {srv3 : SimpleRandomVariable rv3} :     
         
     simple_sigma_measurable rv1 rv3 ->
     SimpleConditionalExpectation (rvmult rv1 rv2) rv3 =
     rvmult rv1 (SimpleConditionalExpectation rv2 rv3).
   Proof.
     Admitted.


End SimpleConditionalExpectation.  

Section Expectation.

  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Definition BoundedPositiveRandomVariable
    (rv1 rv2 : RandomVariable Prts borel_sa) : Prop :=
    PositiveRandomVariable rv2 /\ RealRandomVariable_le Prts rv2 rv1.

  Definition SimpleExpectationSup 
             (E :  forall 
                     (rrv: RandomVariable Prts borel_sa)
                     (srv:SimpleRandomVariable rrv), Prop) : Rbar
    := Lub_Rbar (fun (x : R) => 
                   exists rrv srv, 
                     E rrv srv /\ (SimpleExpectation rrv) = x).
    
  Definition Expectation_posRV
             {rrv : RandomVariable Prts borel_sa}
             (posrv:PositiveRandomVariable rrv) :  Rbar   :=
      (SimpleExpectationSup
         (fun
            (rrv2: RandomVariable Prts borel_sa)
            (srv2:SimpleRandomVariable rrv2) =>
            (BoundedPositiveRandomVariable rrv rrv2))).

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


  Program Definition positive_part_rv (rvv : RandomVariable Prts borel_sa) :=
    BuildRealRandomVariable Prts (pos_fun_part rv_X) _.
  Next Obligation.
    destruct rvv.
    apply Relu_measurable.
    now apply borel_sa_preimage2.    
 Qed.

  Lemma positive_part_prv (rrv : RandomVariable Prts borel_sa) : 
    PositiveRandomVariable (positive_part_rv rrv).
  Proof.
    unfold PositiveRandomVariable, rv_X.
    unfold positive_part_rv, pos_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

  Program Definition negative_part_rv (rvv : RandomVariable Prts borel_sa) :=
    BuildRealRandomVariable Prts (neg_fun_part rv_X) _.
  Next Obligation.
    destruct rvv.
    apply Relu_measurable.
    apply Ropp_measurable.
    now apply borel_sa_preimage2.    
  Qed.

  Lemma negative_part_prv
           (rrv : RandomVariable Prts borel_sa) :
    PositiveRandomVariable (negative_part_rv rrv).
  Proof.
    unfold PositiveRandomVariable, rv_X.
    unfold negative_part_rv, neg_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

  Definition Expectation (rrv : RandomVariable Prts borel_sa) : option Rbar :=
    Rbar_plus' (Expectation_posRV  (positive_part_prv rrv))
               (Rbar_opp (Expectation_posRV  (negative_part_prv rrv))).

  Definition rvmean (rrv : RandomVariable Prts borel_sa) : option R :=
    match Expectation rrv with
    | Some m => match m with
                | Finite m' => Some (real m)
                | _ => None
                end
    | None => None
    end.

  Definition variance (rrv : RandomVariable Prts borel_sa) : option Rbar :=
    match rvmean rrv with
    | Some m => Expectation (rvsqr (rvminus rrv (rvconst m)))
    | None => None
    end.

  Lemma Expectation_posRV_scale (c: posreal) 
        (rv : RandomVariable Prts borel_sa) 
        (posrv:PositiveRandomVariable rv) :  
    Expectation_posRV (positive_scale_prv Prts c posrv) =
    c * Expectation_posRV posrv.
  Proof.
    unfold Expectation_posRV.
    unfold BoundedPositiveRandomVariable.
    unfold SimpleExpectationSup.
        
    Admitted.

  Lemma Expectation_scale (c: posreal) (rv : RandomVariable Prts borel_sa) :
    let Ex_rv := Expectation rv in
    let Ex_c_rv := Expectation (rvscale Prts c rv) in
    match Ex_rv, Ex_c_rv with
    | Some ex, Some exc => c*ex = exc
    | None, None => True
    | _,_ => False
    end.
  Proof. 
    unfold Expectation.
    generalize (Expectation_posRV_scale c _ (positive_part_prv rv)); intro eprv.
    Set Printing All.
    
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

  
