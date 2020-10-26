Require Import Reals.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Lub.

Require Import Utils.
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

  Program Instance constant_random_variable c : RandomVariable prts cod :=
    { rv_X := (fun _ => c) }.
  Next Obligation.
    unfold event_preimage.
    destruct (sa_dec B H c).
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

  Program Instance constant_random_variable_constant c : ConstantRandomVariable (constant_random_variable c)
    := { srv_val := c }.

  Class SimpleRandomVariable 
        (rrv : RandomVariable prts cod)
    := { 
      srv_vals : list Td ;
      srv_vals_complete : forall x, In (rv_X x) srv_vals;
    }.

  Global Program Instance constant_simple_random_variable (rv:RandomVariable prts cod) {crv:ConstantRandomVariable rv} : SimpleRandomVariable rv
    := { srv_vals := [srv_val] }.
  Next Obligation.
    left.
    symmetry.
    apply srv_val_complete.
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


(*
  Lemma sa_simple_list_pt (f : Ts -> R) (vals : list R) :
    (forall (x:Ts), In (f x) vals) ->
    (forall (pt:R), In pt vals -> sa_sigma (fun omega : Ts => f omega = pt)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => f omega <= r)
                        (union_of_collection (fun n => 
*)

  Definition PositiveRandomVariable
        {prts: ProbSpace dom}
        (rv: RandomVariable prts borel_sa) : Prop :=
    forall (x:Ts), (0 <= rv_X x)%R.
  
  Lemma scale_measurable (f : Ts -> R) (c:posreal) :
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

  Program Definition rvscale (c: posreal) (rv : RandomVariable prts borel_sa) :=
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
             {rrv : RandomVariable Prts borel_sa}             
             (srv : SimpleRandomVariable rrv) : R :=
    list_sum (map (fun v => Rmult v (ps_P (event_preimage rv_X (singleton_event v)))) 
                  srv_vals).

  Global Program Instance scale_constant_random_variable (c: posreal)
         {rrv : RandomVariable Prts borel_sa}
         (crv:ConstantRandomVariable rrv) : ConstantRandomVariable (rvscale Prts c rrv)
    := { srv_val := Rmult c srv_val }.
  Next Obligation.
    destruct crv.
    unfold srv_val.
    now rewrite (srv_val_complete0 x).
  Qed.

  Global Program Instance scale_simple_random_variable (c: posreal)
         {rrv : RandomVariable Prts borel_sa}                      
         (srv:SimpleRandomVariable rrv) : SimpleRandomVariable (rvscale Prts c rrv)
    := { srv_vals := map (fun v => Rmult c v) srv_vals }.
  Next Obligation.
    destruct srv.
    rewrite in_map_iff.
    exists (rv_X x).
    split; trivial.
  Qed.

  Lemma scaleSimpleExpectation (c:posreal)
         {rrv : RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rrv) : 
    (c * SimpleExpectation srv)%R = SimpleExpectation (scale_simple_random_variable c srv).
  Proof.
    unfold SimpleExpectation, scale_simple_random_variable.
    destruct srv.
    unfold srv_vals.
    simpl.
    induction srv_vals0.
    - simpl; lra.
    - simpl in *.
  Admitted.

End SimpleExpectation.



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
                     E rrv srv /\ (SimpleExpectation srv) = x).
    
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

  Compute (1/2)%nat.

  Definition N_to_Z (n : nat) :=
    let quo := ((S n)/2)%nat in
    let rem := ((S n) - 2*quo)%nat in
    match n with
    | 0 => Z.of_nat n
    | _ => match rem with
           | 0 => Z.of_nat quo
           | _ => (- Z.of_nat quo)%Z
           end
    end.
  
  Definition NxN_to_rat (nxn : nat*nat) := IZR (N_to_Z (fst nxn)) / (INR (S (snd nxn))).

  Definition N_to_NxN (n:nat) := (n,n).
  
  Definition indexed_rational (n:nat) := NxN_to_rat (N_to_NxN n).

  Lemma measurable_sum (f g : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => g omega <= r)) ->    
    (forall (r:R),  sa_sigma (fun omega : Ts => (f omega) + (g omega) <= r)).
  Proof.
    intros.
    assert (event_equiv 
              (fun omega : Ts => (f omega) + (g omega) <= r)
              (union_of_collection
                 (fun (n:nat) => 
                    event_inter
                      (fun omega : Ts => f omega <= r + indexed_rational n)
                      (fun omega : Ts => g omega <= - indexed_rational n)))).
                        
  Admitted.

  Lemma measurable_continuous (f : Ts -> R) (g : R -> R) :
    continuity g ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => g (f omega) <= r)).
  Proof.
  Admitted.

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


  Lemma Expection_posRV_scale (c: posreal) 
        (rv : RandomVariable Prts borel_sa) 
        (posrv:PositiveRandomVariable rv) :  
    Expectation_posRV (positive_scale_prv Prts c posrv) =
    c * Expectation_posRV posrv.
  Proof.
    unfold Expectation_posRV.
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
    intros.
    
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
  
