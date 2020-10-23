Require Import Reals.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.

Require Import Utils.
Require Import ProbSpace SigmaAlgebras BorelSigmaAlgebra.
Import ListNotations.

Section RandomVariable.
  (* todo better type names. *)
  (* The preimage of the function X on codomain B. *)
  Definition preimage {Ts: Type} {Td: Type}
             (X: Ts -> Td)
             (B: event Td)
             := fun omega: Ts => B (X omega).

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
      rv_preimage: forall B: event Td, (sa_sigma (preimage rv_X B));
    }.

  Lemma BorelSigma_preimage 
    {Ts:Type} {Td:Type}
    {dom: SigmaAlgebra Ts}
    (prts: ProbSpace dom)
    (rvx: Ts -> Td) : 
    forall B: event Td, (sa_sigma (preimage rvx B)).
  Proof.
  Admitted.

  Instance BuildRealRandomVariable {Ts:Type} 
    {dom: SigmaAlgebra Ts}
    (prts: ProbSpace dom)
    (rvx: Ts -> R) : RandomVariable prts borel_sa
    := {
      rv_X := rvx ;
      rv_preimage := BorelSigma_preimage prts rvx
    }.



  Class RealValuedRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        (cod: SigmaAlgebra R)  :=
  
    {
      (* the random variable. *)
      rrv_X: Ts -> R;

      rrv_is_real: forall r:R, sa_sigma (fun omega:Ts => (rrv_X omega) <= r);
    }.

  Class ConstantRealValuedRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R}
        (rrv : RealValuedRandomVariable prts cod) :=
    { 
      srv_val : R;
      srv_val_complete : forall x, rrv_X x =  srv_val
    }.

  Class SimpleRealValuedRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R}
        (rrv : RealValuedRandomVariable prts cod) :=
    { 
      srv_vals : list R;
      srv_vals_complete : forall x, In (rrv_X x) srv_vals
    }.

  Definition RealRandomVariable_le {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R} 
        (rv1 rv2: RealValuedRandomVariable prts cod) : Prop :=
    forall (x:Ts), rrv_X (RealValuedRandomVariable:=rv1) x <= 
                   rrv_X (RealValuedRandomVariable:=rv2) x.

  Definition PositiveRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R} 
        (rv: RealValuedRandomVariable prts cod) : Prop :=
    forall (x:Ts), 0 <= rrv_X x.

End RandomVariable.

Section SimpleExpectation.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}
    {cod: SigmaAlgebra R}
    {rrv : RealValuedRandomVariable Prts cod}.

  Definition singleton_event {T} (m:T) := fun x => x=m.

  Definition simpleRandomVariable_partition_image 
             (srv : SimpleRealValuedRandomVariable rrv) : list (event Ts) :=
    map (preimage rrv_X) (map singleton_event srv_vals).
    
  Fixpoint list_sum (l : list R) : R :=
    match l with
    | nil => 0
    | x :: xs => x + list_sum xs
    end.

  Definition SimpleExpectation (srv : SimpleRealValuedRandomVariable rrv) : R :=
    list_sum (map (fun v => Rmult v (ps_P (preimage rrv_X (singleton_event v)))) 
                  srv_vals).

  Definition scaleSimpleVariable (c:R) (srv : SimpleRealValuedRandomVariable rrv) : 
    SimpleRealValuedRandomVariable rrv.
  Admitted.    

  Lemma scaleSimpleExpectation (c:R) (srv : SimpleRealValuedRandomVariable rrv) : 
    c * SimpleExpectation srv = SimpleExpectation (scaleSimpleVariable c srv).
  Proof.
  Admitted.
    
End SimpleExpectation.

Section Expectation.

  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}
    {cod: SigmaAlgebra R}.

  Definition BoundedPositiveRandomVariable
    (rv1 rv2 : RealValuedRandomVariable Prts cod) : Prop :=
    PositiveRandomVariable rv2 /\ RealRandomVariable_le rv2 rv1.

  Definition SimpleExpectationSup 
             (E :  forall 
                     (rrv: RealValuedRandomVariable Prts cod)
                     (srv:SimpleRealValuedRandomVariable rrv), Prop) : Rbar
    := Lub_Rbar (fun (x : R) => 
                   exists rrv srv, 
                     E rrv srv /\ (SimpleExpectation srv) = x).
    
  Definition Expection_posRV
             {rrv : RealValuedRandomVariable Prts cod}
             (posrv:PositiveRandomVariable rrv) :  Rbar   :=
      (SimpleExpectationSup
         (fun
            (rrv2: RealValuedRandomVariable Prts cod)
            (srv2:SimpleRealValuedRandomVariable rrv2) =>
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
    unfold event_equiv, event_union; intros.
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

  Lemma equiv_le_lt (f : Ts -> R) (r:R) :
    event_equiv (fun omega : Ts => f omega < r)
                (union_of_collection
                   (fun (n:nat) => (fun omega : Ts => f omega <= r - / INR (S n)))).
  Proof.
    unfold event_equiv, union_of_collection.
    intros.
    split; intros.
    
    admit.
    destruct H.
    assert (0 < / INR (S x0)).
    apply Rinv_0_lt_compat.
    apply  lt_0_INR; lia.
    lra.
    Admitted.

  Lemma sa_le_ge (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => f omega >= r)
                        (event_complement (fun omega : Ts => f omega < r))).
    {
      simpl.
      intro x.
      unfold event_complement.
      split; intros; lra.
    }
      rewrite H0.
      apply sa_complement.
      rewrite equiv_le_lt.
      apply sa_countable_union.
      intros.
      apply H.
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

  Program Instance positive_part_rv (rvv : RealValuedRandomVariable Prts cod) : 
    RealValuedRandomVariable Prts cod
    := {
    rrv_X := (pos_fun_part rrv_X)
      }.
  Next Obligation.
    destruct rvv.
    now apply Relu_measurable.
  Qed.

  Lemma positive_part_prv (rrv : RealValuedRandomVariable Prts cod) : 
    PositiveRandomVariable (positive_part_rv rrv).
  Proof.
    unfold PositiveRandomVariable, rrv_X.
    unfold positive_part_rv, pos_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

 Program Instance negative_part_rv
          (rrv : RealValuedRandomVariable Prts cod) : RealValuedRandomVariable Prts cod
    := {
    rrv_X := (neg_fun_part rrv_X)
      }.
  Next Obligation.
    destruct rrv.
    apply Relu_measurable.
    now apply Ropp_measurable.
  Qed.

  Lemma negative_part_prv
           (rrv : RealValuedRandomVariable Prts cod) :
    PositiveRandomVariable (negative_part_rv rrv).
  Proof.
    unfold PositiveRandomVariable, rrv_X.
    unfold negative_part_rv, neg_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

  Definition Expectation (rrv : RealValuedRandomVariable Prts cod) : option Rbar :=
    Rbar_plus' (Expection_posRV  (positive_part_prv rrv))
               (Rbar_opp (Expection_posRV  (negative_part_prv rrv))).

End Expectation.


Section lebesgueintegration.
  
  Class MeasurableFunction {Ts: Type} (dom: SigmaAlgebra Ts) :=
    {
      measure_mu: event Ts -> R;

      measure_none : measure_mu ∅ = R0 ;
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
  
