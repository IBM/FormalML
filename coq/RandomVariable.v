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

  Definition IndicatorRandomVariable
             (rv : RandomVariable prts borel_sa) : Prop :=
    forall (x:Ts), (rv_X x) = 0 \/ (rv_X x) = 1.

  (* should srv argument be minimized ? *)
  Definition IndicatorSimpleRandomVariable
             {rv : RandomVariable prts borel_sa}
             (srv : SimpleRandomVariable rv) : Prop :=
    forall (x:R), In x srv_vals -> x = 0 \/ x = 1.

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

  Definition point_preimage_indicator
    (rv : RandomVariable prts borel_sa)
    (c:R) :=
    EventIndicator (fun omega => rv_X omega = c) (fun x => Req_EM_T (rv_X x) c) 
                   (sa_singleton c rv).

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
             {rrv : RandomVariable Prts borel_sa}             
             (srv : SimpleRandomVariable rrv) : R :=
    list_sum (map (fun v => Rmult v (ps_P (event_preimage rv_X (singleton_event v)))) 
                  (nodup Req_EM_T srv_vals)).

(*
  Definition SimpleConditionalExpection 
             {rv1 rv2 : RandomVariable Prts borel_sa}             
             (srv1 : SimpleRandomVariable rv1) 
             (srv2 : SimpleRandomVariable rv2) :=    
    fold_right rvplus rvzero 
               (map (fun c => rvscale 
                    ((SimpleExpectation (rvprod rv1 (point_preimage_indicator rv2 c)))
                       / (ps_P (event_preimage rv_X (RandomVariable:=rv2) (singleton_event c))))
                    (point_preimage_indicator rv2 c))
               srv_vals (SimpleRandomVariable:=srv2)).
 *)
  
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

  Definition rvminus (rv1 rv2 : RandomVariable Prts borel_sa) := 
    rvsum rv1 (rvopp rv2).

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
  
  Program Definition rvprod (rv1 rv2 : RandomVariable Prts borel_sa) :=
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

  Global Program Instance product_simple_random_variables
         {rv1 rv2 : RandomVariable Prts borel_sa}                      
         (srv1:SimpleRandomVariable rv1)
         (srv2:SimpleRandomVariable rv2)
    : SimpleRandomVariable (rvprod rv1 rv2)
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


   Lemma list_sum_fold_right l : list_sum l = fold_right Rplus 0 l.
   Proof.
     induction l; firstorder.
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
                  

  Lemma sa_sigma_inter_pts
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (c1 c2 : R) :
    sa_sigma (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = c1 /\ 
                                rv_X (RandomVariable:=rv2) omega = c2).
  Proof.
        apply sa_inter.
        apply sa_singleton.
        apply sa_singleton.        
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

    Lemma expect_list_pairs_const 
         {rv1 rv2: RandomVariable Prts borel_sa}                      
         (srv1 : SimpleRandomVariable rv1) 
         (srv2 : SimpleRandomVariable rv2) 
         (pairsum : R)
      :      
        let pairs := 
            filter (fun xy => if Req_EM_T ((fst xy) + (snd xy)) pairsum then true else false)
                   (list_prod (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv1)))
                              (nodup Req_EM_T (srv_vals (SimpleRandomVariable:=srv2)))) in
      list_sum
        (map
           (fun v : R * R =>
              (fst v + snd v) *
              ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega = fst v /\ 
                                      rv_X (RandomVariable:=rv2) omega = snd v))
           pairs) = 
      list_sum
        (map (fun v : R => v * ps_P (fun omega : Ts => rv_X (RandomVariable:=rv1) omega + 
                                                       rv_X (RandomVariable:=rv2) omega = v))
             (nodup Req_EM_T
                    (map (fun ab : R * R => fst ab + snd ab) pairs ))).
    Proof.
      intros.
      replace (nodup Req_EM_T (map (fun ab : R * R => fst ab + snd ab) pairs )) with
          [pairsum].
      simpl.
      admit.
      Search "nodup".
    Admitted.

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
    generalize (sumSimpleExpectation0 srv1 srv2 H0); intros.
    generalize (sumSimpleExpectation1 srv1 srv2 H); intros.   
    generalize (@sa_sigma_inter_pts rv1 rv2). intro sa_sigma.
    destruct srv1.
    destruct srv2.
    unfold srv_vals in *; intros.
    unfold sum_simple_random_variables.

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
      assert (HH:forall x y : R * R, {x = y} + {x <> y}) by admit.
      transitivity (list_sum
                      (map
       (fun v : R * R => (fst v + snd v) * ps_P (fun omega : Ts => rv_X0 omega = fst v /\ rv_X1 omega = snd v))
       (nodup HH (list_prod srv_vals0 srv_vals1)))).
      + admit.
      + transitivity (list_sum
                        (map (fun v : R => v * ps_P (fun omega : Ts => rv_X0 omega + rv_X1 omega = v))
                             (nodup Req_EM_T (map (fun ab : R * R => fst ab + snd ab) (nodup HH (list_prod srv_vals0 srv_vals1)))))).
        * generalize (NoDup_nodup HH (list_prod srv_vals0 srv_vals1)).
          generalize (nodup HH (list_prod srv_vals0 srv_vals1)). clear.
          intros.
          rewrite <- (unquotient_quotient sums_same l) at 1.
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
             specialize (Hnnil _ H0).
             specialize (Hequiv _ H0).
             
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
                f_equal.
                ** admit.
                ** intros.

(* did we lose some information? *)
                   
                   admit.
                ** 
                   
(*                   
                symmetry.
                transitivity (
                    fold_right Rplus 0
                               (map ps_P (map (event_inter (fun omega : Ts => rv_X0 omega + rv_X1 omega = fst p + snd p) (map (fun omega : Ts => rv_X0 omega = fst p /\ rv_X1 omega = snd p) (p::a)))))).

                                                 
                generalize (ps_total Prts (fun omega : Ts => rv_X0 omega + rv_X1 omega = fst p + snd p)
                                     (map (fun x : R * R => (fun omega : Ts => rv_X0 omega = fst x /\ rv_X1 omega = snd x)) (p :: a))).




                
                admit.
          -- 
*)
    Admitted.
    
    (*    Lemma NoDup l1 complete l1,  *)
    

(*
   Lemma SimpleExpectation_minimal
          {rrv : RandomVariable Prts borel_sa}             
          (srv1: SimpleRandomVariable rrv) : SimpleExpectation rrv
      SimpleExpectation srv1 = SimpleExpectation srv2.
    and it is minimal

        Lemma SimpleExpectation_ext
        {rrv : RandomVariable Prts borel_sa}             
        (srv1 srv2 : SimpleRandomVariable rrv) : R :=    
      SimpleExpectation srv1 = SimpleExpectation srv2.

    
                                               Definition SimpleExpectation
             {rrv : RandomVariable Prts borel_sa}             
             (srv : SimpleRandomVariable rrv) : R :=
    list_sum (map (fun v => Rmult v (ps_P (event_preimage rv_X (singleton_event v)))) 
                  (nodup Req_EM_T srv_vals)).
    *)

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
    | Some m => Expectation (rvsqr (rvminus rrv 
                                            (constant_random_variable m)))
    | None => None
    end.

  Lemma Expection_posRV_scale (c: posreal) 
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

  
