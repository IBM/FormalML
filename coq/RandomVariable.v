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

  Definition PositiveRandomVariable
        {prts: ProbSpace dom}
        (rv: RandomVariable prts borel_sa) : Prop :=
    forall (x:Ts), (0 <= rv_X x)%R.
  
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

  Lemma Rsqr_measurable (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => Rsqr (f omega) <= r)).
  Proof.
    intros.
    destruct (Rlt_dec r 0).
    - assert (event_equiv (fun omega : Ts => Rsqr (f omega) <= r)
                          (fun omega : Ts => False)).
      + red; intros.
        generalize (Rle_0_sqr (f x)); intros.
        lra.
      + rewrite H0.
        apply sa_none.
    - assert (0 <= r) by lra.
      assert (event_equiv (fun omega : Ts => (f omega)² <= r)
                          (fun omega : Ts => (f omega) <= Rsqrt (mknonnegreal _ H0))).
      + red; intros.
        simpl.
        replace (r) with (Rsqr (Rsqrt (mknonnegreal _ H0))).
        Search Rsqr.
        split.
        admit.
        
        
  Admitted.

(* Rsqr_sqrt: forall x : R, 0 <= x -> (sqrt x)² = x *)

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

  Global Program Instance scale_simple_random_variable (c: R)
         {rrv : RandomVariable Prts borel_sa}                      
         (srv:SimpleRandomVariable rrv) : SimpleRandomVariable (rvscale Prts c rrv)
    := { srv_vals := map (fun v => Rmult c v) srv_vals }.
  Next Obligation.
    destruct srv.
    rewrite in_map_iff.
    exists (rv_X x).
    split; trivial.
  Qed.

  Lemma list_sum_const_mul_gen {A : Type} (l : list A) f :
    forall r, list_sum (map (fun x => r*f x) l)  =
         r* list_sum (map (fun x => f x) l).
Proof.
  intro r.
  induction l.
  simpl; lra.
  simpl. rewrite IHl ; lra.
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
         {rrv : RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rrv) : 
    (c * SimpleExpectation srv)%R = SimpleExpectation (scale_simple_random_variable c srv).
  Proof.
    unfold SimpleExpectation, scale_simple_random_variable.
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
    - rewrite <- list_sum_const_mul_gen.
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

  Definition opp_simple_random_variable 
             {rrv : RandomVariable Prts borel_sa}                      
             (srv:SimpleRandomVariable rrv) :=
    scale_simple_random_variable (-1) srv.    

  Lemma oppSimpleExpectation
         {rrv : RandomVariable Prts borel_sa}                      
         (srv : SimpleRandomVariable rrv) : 
    (- SimpleExpectation srv)%R = SimpleExpectation (opp_simple_random_variable srv).
  Proof.
    replace (- SimpleExpectation srv) with (-1 * SimpleExpectation srv) by lra.
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

  Program Definition rvsum (rv1 rv2 : RandomVariable Prts borel_sa) :=
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

  Global Program Instance sum_simple_random_variables
         {rv1 rv2 : RandomVariable Prts borel_sa}                      
         (srv1:SimpleRandomVariable rv1)
         (srv2:SimpleRandomVariable rv2)
    : SimpleRandomVariable (rvsum rv1 rv2)
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


  Lemma list_prod_concat {A} (l1 l2:list A) : list_prod l1 l2 = concat (map (fun x => map (fun y => (x, y)) l2) l1).
  Proof.
    induction l1; simpl; trivial.
    now rewrite IHl1.
  Qed.    

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
          
    Lemma please_rename_this r 
      (H0 : 0 <= r)
      (x:nonnegreal) :
      x² <= r <-> x <= Rsqrt {| nonneg := r; cond_nonneg := H0 |}.
    Proof.
      intros.
      etransitivity.
      - eapply (Rsqrt_le (mknonnegreal _ (Rle_0_sqr x)) (mknonnegreal _ H0)).
      - rewrite Rsqrt_sqr.
        intuition.
    Qed.
                           
  Lemma sumSimpleExpectation 
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2) :      
    NonEmpty Ts -> (SimpleExpectation srv1) + (SimpleExpectation srv2)%R = 
    SimpleExpectation (sum_simple_random_variables srv1 srv2).
   Proof.
    unfold SimpleExpectation; intros.
    generalize (non_empty_srv_vals srv1 X); intros.
    generalize (non_empty_srv_vals srv2 X); intros.    
    destruct srv1.
    destruct srv2.
    unfold srv_vals in *; intros.
    unfold sum_simple_random_variables.
    destruct rv1.
    destruct rv2.
    unfold rv_X in *.
    simpl.
    unfold singleton_event, event_preimage.
    
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


Lemma measurable_continuous (f : Ts -> R) (g : R -> R) :
    continuity g ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => g (f omega) <= r)).
  Proof.
    intros.
    generalize (sa_le_open_set f); intros.
    generalize (continuity_P2 g); intros.
    generalize (continuity_P3 g); intros.
    destruct H3.
    specialize (H3 H).
    unfold image_rec in *.
    unfold event_preimage in H1.
    
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
  
