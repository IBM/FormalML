Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Classical.
Require Import FunctionalExtensionality.

Require Import hilbert.

Require Import BorelSigmaAlgebra.
Require Import ProbSpace.
Require Import RandomVariable.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section L2.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).


  Class IsL2 (rv_X:Ts->R) 
    := is_L2 : match Expectation (rvsqr rv_X) with
       | Some (Finite _) => True
       | _ => False
       end.

  Lemma Expectation_sqr
        (rv_X :Ts->R)  :
    Expectation (rvsqr rv_X) = Some (Expectation_posRV (rvsqr rv_X)).
  Proof.
    apply Expectation_pos_posRV.
  Qed.

  Definition IsL2' (rv_X:Ts->R)  :=
    is_finite (Expectation_posRV (rvsqr rv_X)).

  Lemma IsL2_spec (rv_X:Ts->R) {rv:RandomVariable prts borel_sa rv_X} :
    IsL2 rv_X <-> IsL2' rv_X.
  Proof.
    unfold IsL2, IsL2'.
    rewrite Expectation_sqr.
    match_destr; now simpl.
  Qed.

  Definition Expectation_total (x : Ts -> R) : Rbar
    :=  match (Expectation x) with
        | Some z => z
        | _ => 0
        end.

  Lemma Expectation_total_pos_posRV (rv_X : Ts -> R) 
         {prv : PositiveRandomVariable rv_X} :
    Expectation_total rv_X = Expectation_posRV rv_X.
   Proof.
     generalize (Expectation_pos_posRV rv_X); intros.
     unfold Expectation_total.
     now rewrite H.
   Qed.

   Lemma Rmult_le_0_compat (r1 r2 : R) :
     0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
   Proof.
     intros.
     replace (0) with (r1 * 0) by lra.
     now apply Rmult_le_compat_l.
   Qed.

   Lemma Expectation_abs_neg_part_finite (rv_X : Ts -> R)
        {rv:RandomVariable prts borel_sa rv_X} :         
     is_finite (Expectation_posRV (rvabs rv_X)) ->
     is_finite (Expectation_posRV (neg_fun_part rv_X)).
   Proof.
     apply Finite_Expectation_posRV_le.
     apply neg_fun_part_le.
   Qed.
     
   Lemma Expectation_neg_part_finite (rv_X : Ts -> R)
        {rv:RandomVariable prts borel_sa rv_X} :         
     match Expectation rv_X with
     | Some (Finite _) => True
     | _ => False
     end -> is_finite (Expectation_posRV (neg_fun_part rv_X)).
   Proof.
     intros.
     unfold Expectation in H.
     destruct (Expectation_posRV (fun x : Ts => pos_fun_part rv_X x)).
     destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x)).     
     now unfold is_finite.
     simpl in H; tauto.
     simpl in H; tauto.     
     destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x));
       simpl in H; tauto.
     destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x));
       simpl in H; tauto.
   Qed.
   
   Lemma Rbar_pos_finite (r : Rbar):
         0 < r -> is_finite r.
     Proof.
       intros.
       destruct r.
       now unfold is_finite.
       simpl in H; lra.
       simpl in H; lra.
     Qed.
     
  Lemma Expectation_sum_finite_alt 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable prts borel_sa rv_X1}
        {rv2 : RandomVariable prts borel_sa rv_X2} :
     match Expectation rv_X1 with
     | Some (Finite _) => True
     | _ => False
     end -> 
     match Expectation rv_X2 with
     | Some (Finite _) => True
     | _ => False
     end ->  Expectation (rvplus rv_X1 rv_X2) = 
             Some (Finite (Expectation_total rv_X1 +
                           Expectation_total rv_X2)).
  Proof.
    intros.
    apply Expectation_sum_finite; trivial.

    unfold Expectation_total.
    match_case_in H; intros.
    rewrite H1 in H.
    match_destr_in H; tauto.
    match_destr_in H; tauto.

    unfold Expectation_total.
    match_case_in H0; intros.
    rewrite H1 in H0.
    match_destr_in H0; tauto.
    match_destr_in H0; tauto.
 Qed.

  Lemma Cauchy_Schwarz_ineq (rv_X1 rv_X2 :Ts->R) 
        {rv1:RandomVariable prts borel_sa rv_X1}
        {rv2:RandomVariable prts borel_sa rv_X2}        
        {is1:IsL2' rv_X1}
        {is2:IsL2' rv_X2}  :
    is_finite (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2))) ->
    0 < Expectation_posRV(rvsqr rv_X1) ->
    0 < Expectation_posRV(rvsqr rv_X2) ->    
    Rsqr (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2))) <=
    Expectation_posRV (rvsqr rv_X1) * Expectation_posRV (rvsqr rv_X2).
  Proof.
    unfold IsL2' in *.
    intro isfin_prod.
    intros.
    destruct (Req_dec (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2))) 0).
    - rewrite H1.
      left.
      rewrite Rsqr_0.
      now apply Rmult_lt_0_compat.
    - assert (PositiveRandomVariable
                (rvsqr (rvminus
                          (rvscale (Expectation_posRV (rvsqr rv_X2)) (rvabs rv_X1))
                          (rvscale (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2))) (rvabs rv_X2))))).
      apply prvsqr.
      assert (sqr_abs_mult_ne : Rsqr (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2)) ) <> 0).
      now apply Rmult_integral_contrapositive_currified.        
      assert (sqr_abs1: rv_eq (rvsqr (rvabs rv_X1)) (rvsqr rv_X1)).
      intro x.
      unfold rvsqr, rvabs.
      now rewrite <- Rsqr_abs.
      assert (sqr_abs2: rv_eq (rvsqr (rvabs rv_X2)) (rvsqr rv_X2)).
      intro x.
      unfold rvsqr, rvabs.
      now rewrite <- Rsqr_abs.
      assert (mult_abs: rv_eq (rvmult (rvabs rv_X1) (rvabs rv_X2)) (rvabs (rvmult rv_X1 rv_X2))).

      intro x.
      unfold rvmult, rvabs.
      now rewrite Rabs_mult.
      
      assert (rv_eq
                (rvsqr (rvminus
                          (rvscale (Expectation_posRV (rvsqr rv_X2)) (rvabs rv_X1))
                          (rvscale (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2))) (rvabs rv_X2))))
              (rvplus
                 (rvplus
                    (rvscale (Rsqr (Expectation_posRV (rvsqr rv_X2)))
                             (rvsqr (rvabs rv_X1)))
                    (rvscale
                       (-2 * (Expectation_posRV (rvsqr rv_X2)) 
                         * (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2))))
                       (rvmult (rvabs rv_X1) (rvabs rv_X2))))
                 (rvscale (Rsqr (Expectation_posRV (rvabs (rvmult rv_X1 rv_X2))))
                          (rvsqr (rvabs rv_X2))))).                 
      intros x.
      unfold rvsqr, rvminus, rvscale, rvopp, rvabs, rvplus, rvscale, rvabs, rvmult, Rsqr.
      apply Rminus_diag_uniq.
      now ring_simplify.
      rewrite H3 in H2.
      generalize Expectation_posRV_pos; intros.
      specialize (H4 _ H2).

    rewrite <- Expectation_total_pos_posRV in H4.
    unfold Expectation_total in H4.
    rewrite Expectation_sum_finite_alt in H4.
    unfold Expectation_total in H4.
    rewrite Expectation_sum_finite_alt in H4.
    unfold Expectation_total in H4.    
    rewrite Expectation_scale in H4; trivial.
    rewrite Expectation_scale in H4; trivial.
    

    rewrite Expectation_pos_posRV with (prv := prvsqr (rvabs rv_X1)) in H4.
    rewrite Expectation_scale in H4; trivial.
    rewrite Expectation_pos_posRV with (prv := prvsqr (rvabs rv_X2)) in H4.
    rewrite (@Expectation_ext _ _  prts _ (rvabs (rvmult rv_X1 rv_X2))) in H4; trivial.
    rewrite Expectation_pos_posRV with (prv := prvabs (rvmult rv_X1 rv_X2)) in H4.
    rewrite Expectation_posRV_ext with (prv1 := prvsqr (rvabs rv_X1)) (prv2 := prvsqr rv_X1) in H4; trivial.
    rewrite Expectation_posRV_ext with (prv1 := prvsqr (rvabs rv_X2)) (prv2 := prvsqr rv_X2) in H4; trivial.    
    rewrite <- is1 in H4.
    rewrite <- is2 in H4.
    rewrite <- isfin_prod in H4.
    simpl in H4.
    unfold Rsqr in H4.
    ring_simplify in H4.
    unfold pow at 1 in H4.
    replace ( Expectation_posRV (rvsqr rv_X2) * (Expectation_posRV (rvsqr rv_X2) * 1) *
       Expectation_posRV (rvsqr rv_X1) -
       Expectation_posRV (rvsqr rv_X2) *
       Expectation_posRV (rvabs (rvmult rv_X1 rv_X2)) ^ 2)
      with
        (Expectation_posRV (rvsqr rv_X2)*((Expectation_posRV (rvsqr rv_X1) * Expectation_posRV (rvsqr rv_X2))  -
       Expectation_posRV (rvabs (rvmult rv_X1 rv_X2)) ^ 2)) in H4.
    replace (0) with ((Expectation_posRV (rvsqr rv_X2)) * 0) in H4 by lra.
    apply Rmult_le_reg_l in H4; trivial.
    unfold Rsqr.
    unfold pow in H4.
    lra.
    now ring_simplify.

    apply Rmult_integral_contrapositive_currified.
    apply Rmult_integral_contrapositive_currified.    
    lra.
    now apply Rgt_not_eq.
    trivial.
    apply Rmult_integral_contrapositive_currified.        
    now apply Rgt_not_eq.
    now apply Rgt_not_eq.    
    typeclasses eauto.
    typeclasses eauto.    

    rewrite Expectation_scale; trivial.
    rewrite (@Expectation_ext _ _ prts _ (rvsqr rv_X1)); trivial.
    rewrite Expectation_pos_posRV with (prv :=prvsqr rv_X1).
    rewrite <- is1.
    rewrite <- is2.
    now simpl.
    apply Rmult_integral_contrapositive_currified.        
    now apply Rgt_not_eq.
    now apply Rgt_not_eq.    

    rewrite Expectation_scale; trivial.
    rewrite (@Expectation_ext _ _ prts _ (rvabs (rvmult rv_X1 rv_X2))); trivial.
    rewrite Expectation_pos_posRV with (prv :=prvabs (rvmult rv_X1 rv_X2)).
    rewrite <- isfin_prod.
    now simpl.
    apply Rmult_integral_contrapositive_currified; trivial.
    apply Rmult_integral_contrapositive_currified; trivial.
    lra.
    now apply Rgt_not_eq.

    typeclasses eauto.
    typeclasses eauto.

    rewrite Expectation_sum_finite_alt.
    tauto.
    typeclasses eauto.
    typeclasses eauto.    

    rewrite Expectation_scale; trivial.
    rewrite (@Expectation_ext _ _ prts _ (rvsqr rv_X1)); trivial.
    rewrite Expectation_pos_posRV with (prv :=prvsqr rv_X1).
    rewrite <- is2.
    rewrite <- is1.    
    now simpl.
    apply Rmult_integral_contrapositive_currified; trivial.
    now apply Rgt_not_eq.
    now apply Rgt_not_eq.    

    rewrite Expectation_scale; trivial.
    rewrite (@Expectation_ext _ _ prts _ (rvabs (rvmult rv_X1 rv_X2))); trivial.
    rewrite Expectation_pos_posRV with (prv :=prvabs (rvmult rv_X1 rv_X2)).
    now rewrite <- isfin_prod.
    apply Rmult_integral_contrapositive_currified; trivial.
    apply Rmult_integral_contrapositive_currified; trivial.
    lra.
    now apply Rgt_not_eq.

    rewrite Expectation_scale; trivial.
    rewrite (@Expectation_ext _ _ prts _ (rvsqr rv_X2)); trivial.
    rewrite Expectation_pos_posRV with (prv :=prvsqr rv_X2).
    rewrite <- is2.
    now simpl.
  Qed.

  Lemma rvabs_bound (rv_X : Ts -> R) :
    RealRandomVariable_le (rvabs rv_X) (rvplus (rvsqr rv_X) (const 1)).
  Proof.
    assert (PositiveRandomVariable (rvsqr (rvplus (rvabs rv_X) (const (-1))))) by apply prvsqr.
    assert (rv_eq (rvsqr (rvplus (rvabs rv_X) (const (-1))))
                  (rvplus 
                     (rvplus (rvsqr (rvabs rv_X)) (rvscale (-2) (rvabs rv_X)))
                     (const 1))).
    intro x.
    unfold rvsqr, rvplus, rvscale, rvabs, const, Rsqr.
    now ring_simplify.
    rewrite H0 in H; clear H0.
    unfold PositiveRandomVariable in H.
    unfold RealRandomVariable_le; intros.
    specialize (H x).
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, rvabs in *.
    rewrite Rsqr_abs.
    unfold Rsqr in *.
    apply Rplus_le_compat_l with (r := 2 * Rabs (rv_X x)) in H.
    ring_simplify in H.
    generalize (Rabs_pos (rv_X x)); intros.
    apply Rplus_le_compat_l with (r := Rabs(rv_X x)) in H0.
    lra.
  Qed.

  Lemma L2Expectation_finite_abs (rv_X:Ts->R) 
        {rv : RandomVariable prts borel_sa rv_X}
        {l2:IsL2 rv_X}
    :  match Expectation (rvabs rv_X) with
       | Some (Finite _) => True
       | _ => False
       end.
  Proof.
    assert (PositiveRandomVariable (rvabs rv_X)) by apply prvabs.
    generalize (Expectation_pos_posRV (rvabs rv_X)); intros.
    generalize (rvabs_bound rv_X); intros.
    assert (one_pos: 0 < 1) by lra.
    assert (PositiveRandomVariable (rvplus (rvsqr rv_X) (const 1))).
    apply rvplus_prv.
    apply prvsqr.
    apply prvconst.
    lra.
    generalize (Finite_Expectation_posRV_le _ _ H H2 H1); intros.
    unfold IsL2 in l2.
    rewrite Expectation_pos_posRV with (prv := prvsqr rv_X) in l2.
    match_case_in l2; intros.
    rewrite H4 in l2.
    assert (PositiveRandomVariable (@const R Ts 1)).
    apply prvconst; lra.
    assert (PositiveRandomVariable (rvsqr rv_X)) by apply prvsqr.
    generalize (Expectation_posRV_sum (rvsqr rv_X) (const 1)); intros.
    cut_to H3.
    rewrite Expectation_pos_posRV with (prv := H).
    now rewrite <- H3.
    assert (0 <= 1) by lra.
    erewrite Expectation_posRV_pf_irrel in H7.
    rewrite H7.
    erewrite Expectation_posRV_pf_irrel in H4.
    rewrite H4.
    generalize (Expectation_posRV_const 1 H8); intros.
    erewrite Expectation_posRV_pf_irrel in H9.
    rewrite H9.
    simpl.
    reflexivity.

    rewrite H4 in l2; tauto.
    rewrite H4 in l2; tauto.    
  Qed.

  Lemma L2Expectation_finite (rv_X:Ts->R)  
        {rv : RandomVariable prts borel_sa rv_X}
        {l2:IsL2 rv_X}
    :  match Expectation rv_X with
       | Some (Finite _) => True
       | _ => False
       end.
  Proof.
    apply Expectation_abs_then_finite; trivial.
    apply L2Expectation_finite_abs; trivial.
  Qed.

  Definition L2Expectation_ex (rv_X:Ts->R) {rv:RandomVariable prts borel_sa rv_X} {l2:IsL2 rv_X} :
    { x: R | Expectation rv_X = Some (Finite x)}.
  Proof.
    generalize (L2Expectation_finite rv_X).
    match_destr; [| tauto].
    destruct r; [| tauto..].
    eauto.
  Defined.

  Definition L2Expectation (rv_X:Ts->R) {rv:RandomVariable prts borel_sa rv_X} {l2:IsL2 rv_X}
    := proj1_sig (L2Expectation_ex rv_X).
  
  Instance is_L2_const x : IsL2 (const x).
  Proof.
    unfold IsL2.
    assert (@rv_eq Ts R (rvsqr (const x)) (const (Rsqr x))).
    - intro x0.
      now unfold rvsqr, const.
    - rewrite (@Expectation_ext _ _ _ _ (const (Rsqr x))).
      + now rewrite Expectation_const.
      + intros ?; reflexivity.
  Qed.

  Lemma rvprod_bound (rv_X1 rv_X2 : Ts->R) :
    RealRandomVariable_le (rvscale 2 (rvmult rv_X1 rv_X2))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
  Proof.
    assert (PositiveRandomVariable (rvsqr (rvminus rv_X1 rv_X2))) by apply prvsqr.
    assert (rv_eq (rvsqr (rvminus rv_X1 rv_X2)) 
                  (rvplus (rvplus (rvsqr rv_X1) (rvopp (rvscale 2 (rvmult rv_X1 rv_X2))))
                          (rvsqr rv_X2))).
    intro x.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr.
    now ring_simplify.
    rewrite H0 in H; clear H0.
    unfold RealRandomVariable_le; intros.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr in *.
    unfold PositiveRandomVariable in H.
    specialize (H x).
    lra.
  Qed.  

  Lemma rvprod_abs_bound (rv_X1 rv_X2 : Ts->R) :
    RealRandomVariable_le (rvscale 2 (rvabs (rvmult rv_X1 rv_X2)))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
  Proof.
    assert (PositiveRandomVariable (rvsqr (rvminus (rvabs rv_X1) (rvabs rv_X2)))) by apply prvsqr.
    assert (rv_eq (rvsqr (rvminus (rvabs rv_X1) (rvabs rv_X2))) 
                  (rvplus (rvplus (rvsqr rv_X1) (rvopp (rvscale 2 (rvabs (rvmult rv_X1 rv_X2)))))
                          (rvsqr rv_X2))).
    intro x.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, rvabs, Rsqr.
    rewrite Rabs_mult.
    ring_simplify.
    replace (pow (Rabs (rv_X1 x)) 2) with (pow (rv_X1 x) 2).
    replace (pow (Rabs (rv_X2 x)) 2) with (pow (rv_X2 x) 2).    
    now ring_simplify.
    unfold Rabs; match_destr; lra.
    unfold Rabs; match_destr; lra.    
    rewrite H0 in H; clear H0.
    unfold RealRandomVariable_le; intros.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, rvabs, Rsqr in *.
    unfold PositiveRandomVariable in H.
    specialize (H x).
    lra.
  Qed.  

  Lemma rvsum_sqr_bound (rv_X1 rv_X2 : Ts->R) :
    RealRandomVariable_le (rvsqr (rvplus rv_X1 rv_X2)) 
                           (rvscale 2 (rvplus (rvsqr rv_X1) (rvsqr rv_X2))).
  Proof.
    assert (PositiveRandomVariable (rvsqr (rvminus rv_X1 rv_X2))) by apply prvsqr.
    assert (rv_eq (rvsqr (rvminus rv_X1 rv_X2)) 
                  (rvplus (rvplus (rvsqr rv_X1) (rvopp (rvscale 2 (rvmult rv_X1 rv_X2))))
                          (rvsqr rv_X2))).
    intro x.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr.
    now ring_simplify.
    rewrite H0 in H; clear H0.
    unfold PositiveRandomVariable in H.
    unfold RealRandomVariable_le; intros.
    specialize (H x).
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr in *.
    apply Rplus_le_compat_l with (r:= ((rv_X1 x + rv_X2 x) * (rv_X1 x + rv_X2 x))) in H.
    ring_simplify in H.
    ring_simplify.
    apply H.
  Qed.    

  Instance is_L2_plus rv_X1 rv_X2
           {rv1:RandomVariable prts borel_sa rv_X1}
           {rv2:RandomVariable prts borel_sa rv_X2}
           {isl21:IsL2 rv_X1}
           {isl22:IsL2 rv_X2} :
    IsL2 (rvplus rv_X1 rv_X2).
  Proof.
    unfold IsL2 in *.
    generalize (rvsum_sqr_bound rv_X1 rv_X2); intros.
    generalize (Expectation_sum_finite (rvsqr rv_X1) (rvsqr rv_X2)); intros.
    repeat match_destr_in isl21; try tauto.
    repeat match_destr_in isl22; try tauto.
    specialize (H0 _ _ (eq_refl ) (eq_refl _)).
    assert (0 < 2) by lra.
    generalize (Expectation_scale (mkposreal 2 H1) (rvplus (rvsqr rv_X1) (rvsqr rv_X2))); intros.
    simpl in H2.
    assert (2 <> 0) by lra.
    specialize (H2 H3).
    rewrite H0 in H2.
    assert (PositiveRandomVariable (rvsqr (rvplus rv_X1 rv_X2))) by apply prvsqr.
    assert (PositiveRandomVariable (rvscale (mkposreal _ H1) (rvplus (rvsqr rv_X1) (rvsqr rv_X2)))).
    - apply rvscale_pos.
      apply rvplus_prv; apply prvsqr.
    - rewrite Expectation_pos_posRV with (prv := H4).
      generalize (Finite_Expectation_posRV_le (rvsqr (rvplus rv_X1 rv_X2))
                                              (rvscale 2 (rvplus (rvsqr rv_X1) (rvsqr rv_X2))) H4 H5 H); intros.
    rewrite Expectation_pos_posRV with (prv := H5) in H2.
    inversion H2.
    rewrite H8 in H6.
    cut_to H6; try easy.
    now rewrite <- H6.
  Qed.

  Instance is_L2_scale x rv_X 
           {isl2:IsL2 rv_X} :
    IsL2 (rvscale x rv_X).
  Proof.
    unfold IsL2.
    assert (rv_eq  (rvsqr (rvscale x rv_X)) (rvscale (Rsqr x) (rvsqr rv_X))).
    - intro x0.
      unfold rvsqr, rvscale, Rsqr; lra.
    - destruct (Rlt_dec 0 (Rsqr x)).
      + rewrite (Expectation_ext (rv_X2 := (rvscale (mkposreal _ r) (rvsqr rv_X))) H).
        rewrite Expectation_scale_posreal.
        unfold IsL2 in isl2.
        match_destr_in isl2.
        now match_destr_in isl2.
      + generalize (Rle_0_sqr x); intros.
        assert (0 = Rsqr x) by lra.
        symmetry in H1.
        apply Rsqr_eq_0 in H1.
        rewrite (Expectation_ext (rv_X2 := const 0)).
        * now rewrite Expectation_const.
        * intro x0.
          unfold rvsqr, rvscale, const, Rsqr.
          subst.
          lra.
  Qed.
  
  Record L2RRV : Type
    := L2RRV_of {
      L2RRV_rv_X :> Ts -> R
      ; L2RRV_rv :> RandomVariable prts borel_sa L2RRV_rv_X
      ; L2RRV_l2 :> IsL2 L2RRV_rv_X
         }.

  Existing Instance L2RRV_rv.
  Existing Instance L2RRV_l2.
  
  Definition pack_L2RRV (rv_X:Ts -> R) {rv:RandomVariable prts borel_sa rv_X} {l2:IsL2 rv_X}
    := L2RRV_of rv_X rv l2.
  
  Definition L2RRV_eq (rv1 rv2:L2RRV)
    := rv_almost_eq prts rv1 rv2.

  Local Hint Resolve Hsigma_borel_eq_pf : prob.

  Global Instance L2RRV_eq_equiv : Equivalence L2RRV_eq.
  Proof.
    unfold L2RRV_eq.
    constructor.
    - intros [x?].
      now apply rv_almost_eq_rv_refl.
    - intros [x?] [y?] ps1; simpl in *.
      now apply rv_almost_eq_rv_sym.
    - intros [x??] [y??] [z??] ps1 ps2.
      simpl in *.
      now apply rv_almost_eq_rv_trans with (y0:=y).
  Qed.
  
  Definition L2RRVconst (x:R) : L2RRV
    := pack_L2RRV (const x).

  Definition L2RRVzero : L2RRV := L2RRVconst 0.

  Definition L2RRVplus (rv1 rv2:L2RRV) : L2RRV
    := pack_L2RRV (rvplus rv1  rv2).

  Global Instance L2RRV_plus_proper : Proper (L2RRV_eq ==> L2RRV_eq ==> L2RRV_eq) L2RRVplus.
  Proof.
    unfold Proper, respectful, L2RRV_eq.
    intros [x1??] [x2??] eqqx [y1??] [y2??] eqqy.
    simpl in *.
    now apply rv_almost_eq_plus_proper.
  Qed.
  
  Program Definition L2RRVscale (x:R) (rv:L2RRV) : L2RRV
    := pack_L2RRV (rvscale x rv).

  Global Instance L2RRV_scale_proper : Proper (eq ==> L2RRV_eq ==> L2RRV_eq) L2RRVscale.
  Proof.
    unfold Proper, respectful, L2RRV_eq.
    intros ? x ? [x1??] [x2??] eqqx.
    subst.
    simpl in *.
    unfold rvscale.
    red.
    destruct (Req_EM_T x 0).
    - subst.
      erewrite ps_proper; try eapply ps_one.
      red.
      unfold Ω.
      split; trivial.
      lra.
    - erewrite ps_proper; try eapply eqqx.
      red; intros.
      split; intros.
      + eapply Rmult_eq_reg_l; eauto.
      + congruence.
  Qed.

  Instance is_L2_opp rv_X
           {rv:RandomVariable prts borel_sa rv_X}
           {isl2:IsL2 rv_X} :
    IsL2 (rvopp rv_X).
  Proof.
    unfold rvopp.
    eapply is_L2_scale; eauto.
  Qed.

  Program Definition L2RRVopp (rv:L2RRV) : L2RRV
    := pack_L2RRV (rvopp rv).
  
  Global Instance L2RRV_opp_proper : Proper (L2RRV_eq ==> L2RRV_eq) L2RRVopp.
  Proof.
    unfold Proper, respectful.
    intros x y eqq.
    generalize (L2RRV_scale_proper (-1) _ (eq_refl _) _ _ eqq)
    ; intros HH.
    destruct x as [x?]
    ; destruct y as [y?].
    apply HH.
  Qed.
  
  Definition L2RRVminus (rv1 rv2:L2RRV) : L2RRV
    := pack_L2RRV (rvminus rv1 rv2).

  Global Instance L2RRV_minus_proper : Proper (L2RRV_eq ==> L2RRV_eq ==> L2RRV_eq) L2RRVminus.
  Proof.
    unfold Proper, respectful, L2RRV_eq.

    intros x1 x2 eqq1 y1 y2 eqq2.
    
    generalize (L2RRV_plus_proper _ _ eqq1 _ _ (L2RRV_opp_proper _ _ eqq2)) 
    ; intros HH.
    destruct x1 as [???]; destruct x2 as [???]
    ; destruct y1 as [???]; destruct y2 as [???].
    apply HH.
  Qed.

  Definition L2RRVexpectation (rv:L2RRV) : R
    := L2Expectation rv.

  Lemma pos_fun_part_proper_almost x y 
    {rvx:RandomVariable prts borel_sa x}
    {rvy:RandomVariable prts borel_sa y} :
    rv_almost_eq prts x y ->
    rv_almost_eq prts (fun x0 => nonneg (pos_fun_part x x0)) (fun x0 => nonneg (pos_fun_part y x0)).
  Proof.
    unfold pos_fun_part; simpl.
    unfold rv_almost_eq; intros eqq.
    apply Rle_antisym; trivial.
    - apply ps_le1.
      apply (Hsigma_borel_eq_pf prts)
      ; now apply positive_part_rv.
    - rewrite <- eqq.
      apply ps_sub.
      + now apply (Hsigma_borel_eq_pf prts).
      + apply (Hsigma_borel_eq_pf prts)
        ; now apply positive_part_rv.
      + intros a; intros eqq2.
        congruence.
  Qed.

  Lemma neg_fun_part_proper_almost x y 
    {rvx:RandomVariable prts borel_sa x}
    {rvy:RandomVariable prts borel_sa y} :
    rv_almost_eq prts x y ->
    rv_almost_eq prts (fun x0 => nonneg (neg_fun_part x x0)) (fun x0 => nonneg (neg_fun_part y x0)).
  Proof.
    unfold neg_fun_part; simpl.
    unfold rv_almost_eq; intros eqq.
    apply Rle_antisym; trivial.
    - apply ps_le1.
      apply (Hsigma_borel_eq_pf prts)
      ; now apply negative_part_rv.
    - rewrite <- eqq.
      apply ps_sub.
      + now apply (Hsigma_borel_eq_pf prts).
      + apply (Hsigma_borel_eq_pf prts)
        ; now apply negative_part_rv.
      + intros a; intros eqq2.
        congruence.
  Qed.

  Lemma list_sum0_is0 l :
    Forall (fun x => x = 0) l ->
    RealAdd.list_sum l = 0%R.
  Proof.
    induction l; simpl; trivial.
    inversion 1; subst.
    rewrite IHl; trivial.
    lra.
  Qed.

  Lemma SimplePosExpectation_pos_zero x
        {rvx:RandomVariable prts borel_sa x} 
        {xsrv:SimpleRandomVariable x} :
    rv_almost_eq prts x (const 0) ->
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
    - replace (ps_P (fun omega : Ts => x omega = x1)) with 0 in H; [lra |].
      apply Rle_antisym.
      + apply ps_pos.
        eapply Hsigma_borel_eq_pf; eauto.
        apply rvconst.
      +
      assert (event_sub  (fun x0 : Ts => x x0 = 0) (event_complement (fun omega : Ts => x omega = x1))).
      {
        unfold event_complement.
        red; intros.
        lra.
      }
      apply (ps_sub prts) in H1.
      * rewrite ps_complement in H1.
        -- rewrite eqq in H1.
           lra.
        -- eapply Hsigma_borel_eq_pf; eauto.
           apply rvconst.
      * eapply Hsigma_borel_eq_pf; eauto.
        apply rvconst.
      * apply sa_complement.
        eapply Hsigma_borel_eq_pf; eauto.
        apply rvconst.
  Qed.

  Lemma Expectation_simple_proper_almost x y
        {rvx:RandomVariable prts borel_sa x}
        {rvy:RandomVariable prts borel_sa y} 
        {xsrv:SimpleRandomVariable x}
        {ysrv:SimpleRandomVariable y} :
    rv_almost_eq prts x y ->
    SimpleExpectation x = SimpleExpectation y.
  Proof.
    intros.
    generalize (SimplePosExpectation_pos_zero (rvminus x y))
    ; intros HH.
    cut_to HH.
    - unfold rvminus in HH.
      erewrite SimpleExpectation_pf_irrel in HH.
      rewrite <- sumSimpleExpectation with (srv1:=xsrv) (srv2:=srvopp) in HH; trivial.
      + unfold rvopp in HH.
        erewrite (@SimpleExpectation_pf_irrel _ _ _ (rvscale (-1) y)) in HH.
        rewrite <- scaleSimpleExpectation with (srv:=ysrv) in HH.
        lra.
      + typeclasses eauto.
    - clear HH.
      unfold rv_almost_eq in *.
      unfold const.
      rewrite ps_proper; try eapply H.
      intros a.
      unfold rvminus, rvplus, rvopp, rvscale.
      split; intros; lra.
  Qed.

  Lemma Expectation_posRV_almost_0 x 
        {rvx:RandomVariable prts borel_sa x}
        {prv:PositiveRandomVariable x} :
    rv_almost_eq prts x (const 0) ->
    Expectation_posRV x = 0.
  Proof.
    intros.
    unfold Expectation_posRV, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
      [|- context [proj1_sig ?x]] => destruct x; simpl
    end.
    destruct i as [xub xlub].
    unfold is_ub_Rbar in xub.
    specialize (xub 0).
    specialize (xlub 0).
    unfold is_ub_Rbar in xlub.
    cut_to xub.
    - cut_to xlub.
      + now apply Rbar_le_antisym.
      + intros.
        unfold BoundedPositiveRandomVariable in H0.
        destruct H0 as [? [? [? [[? ?] ?]]]].
        unfold rv_almost_eq in H.
        assert (rv_almost_eq prts x2 (const 0)).
        * unfold rv_almost_eq.
          assert (event_sub (fun x0 : Ts => x x0 = const 0 x0)
                            (fun x5 : Ts => x2 x5 = const 0 x5)).
          -- unfold event_sub; intros.
             unfold const in H3.
             unfold const.
             unfold RealRandomVariable_le in H1.
             specialize (H1 x5).
             unfold PositiveRandomVariable in H0.
             specialize (H0 x5).
             lra.
          -- unfold RandomVariable in *.
             rewrite <- borel_sa_preimage2 in rvx.
             rewrite <- borel_sa_preimage2 in x3.
             assert (sa_sigma (fun x5 : Ts => x2 x5 = const 0 x5)).
             ++ unfold const.
                now apply sa_le_pt.
             ++ assert (sa_sigma (fun x5 : Ts => x x5 = const 0 x5)).    
                ** unfold const.
                   now apply sa_le_pt.
                ** apply (ps_sub prts) in H3; trivial.
                   generalize (ps_le1 prts (fun x5 : Ts => x2 x5 = const 0 x5) H4); intros.
                   lra.
        * generalize (SimplePosExpectation_pos_zero x2 H3); intros.
          rewrite H4 in H2.
          rewrite <- H2.
          simpl; lra.
    - exists (const 0); exists (rvconst 0); exists (srvconst 0).
      split.
      + unfold BoundedPositiveRandomVariable.
        split.
        * apply prvconst; lra.
        * unfold RealRandomVariable_le, const.
          apply prv.
      + apply SimpleExpectation_const.
 Qed.

  Lemma Expectation_almost_0 x 
        {rvx:RandomVariable prts borel_sa x} :
    rv_almost_eq prts x (const 0) ->
    Expectation x = Some (Finite 0).
  Proof.
    unfold rv_almost_eq.
    intros.
    assert (RandomVariable prts borel_sa (pos_fun_part x)).
    now apply positive_part_rv.
    assert (RandomVariable prts borel_sa (neg_fun_part x)).
    now apply negative_part_rv.
    unfold RandomVariable in rvx.
    rewrite <- borel_sa_preimage2 in rvx.
    assert (sa_sigma (fun x0 : Ts => nonneg(pos_fun_part x x0) = 0)).
    apply sa_le_pt.
    now apply Relu_measurable.
    assert (sa_sigma (fun x0 : Ts => nonneg(neg_fun_part x x0) = 0)).
    apply sa_le_pt.
    apply Relu_measurable.
    now apply Ropp_measurable.
    unfold Expectation.
    assert (rv_almost_eq prts (fun omega => nonneg(pos_fun_part x omega)) (const 0)).
    unfold rv_almost_eq.
    assert (event_sub (fun x0 : Ts => x x0 = const 0 x0)
                      (fun x0 : Ts => nonneg(pos_fun_part x x0) = const 0 x0)).
    intro x0.
    unfold pos_fun_part, const; simpl.
    unfold Rmax; match_destr.
    unfold const in *.
    apply (ps_sub prts) in H4; trivial.
    generalize (ps_le1 prts (fun x0 : Ts => nonneg(pos_fun_part x x0) = const 0 x0)); intros.
    unfold const in H5.
    specialize (H5 H2).
    lra.
    now apply sa_le_pt.
    assert (rv_almost_eq prts (fun omega => nonneg(neg_fun_part x omega)) (const 0)).
    assert (event_sub (fun x0 : Ts => x x0 = const 0 x0)
                      (fun x0 : Ts => nonneg(neg_fun_part x x0) = const 0 x0)
                        ).
    intro x0.
    unfold neg_fun_part, const; simpl.
    unfold Rmax; match_destr.
    lra.
    unfold rv_almost_eq.
    unfold const in *.
    apply (ps_sub prts) in H5; trivial.
    generalize (ps_le1 prts (fun x0 : Ts => nonneg(neg_fun_part x x0) = const 0 x0)); intros.
    unfold const in H6.
    specialize (H6 H3).
    lra.
    now apply sa_le_pt.
    rewrite (Expectation_posRV_almost_0 (fun x0 : Ts => pos_fun_part x x0) H4).
    rewrite (Expectation_posRV_almost_0 (fun x0 : Ts => neg_fun_part x x0) H5).
    simpl; f_equal; f_equal; lra.
  Qed.


  Lemma Expectation_finite_neg_part x
        {rvx:RandomVariable prts borel_sa x}  :
    forall (e:R), 
      Expectation x = Some (Finite e) ->
      is_finite (Expectation_posRV (neg_fun_part x)).
  Proof.
    intros.
    unfold Expectation, Rbar_minus' in H.
    destruct (Expectation_posRV (fun x0 : Ts => pos_fun_part x x0)).
    - destruct (Expectation_posRV (fun x0 : Ts => neg_fun_part x x0)).
      + now unfold is_finite.
      + simpl in H; discriminate.
      + simpl in H; discriminate.
    - destruct (Expectation_posRV (fun x0 : Ts => neg_fun_part x x0));
        simpl in H; discriminate.
    - destruct (Expectation_posRV (fun x0 : Ts => neg_fun_part x x0));
        simpl in H; discriminate.
  Qed.

  Lemma Expectation_finite_pos_part x
        {rvx:RandomVariable prts borel_sa x}  :
    forall (e:R), 
      Expectation x = Some (Finite e) ->
      is_finite (Expectation_posRV (pos_fun_part x)).
  Proof.
    intros.
    unfold Expectation, Rbar_minus' in H.
    destruct (Expectation_posRV (fun x0 : Ts => pos_fun_part x x0)).
    - destruct (Expectation_posRV (fun x0 : Ts => neg_fun_part x x0)).
      + now unfold is_finite.
      + simpl in H; discriminate.
      + simpl in H; discriminate.
    - destruct (Expectation_posRV (fun x0 : Ts => neg_fun_part x x0));
        simpl in H; discriminate.
    - destruct (Expectation_posRV (fun x0 : Ts => neg_fun_part x x0));
        simpl in H; discriminate.
  Qed.

  Lemma Expectation_finite_proper_almost x y
        {rvx:RandomVariable prts borel_sa x}
        {rvy:RandomVariable prts borel_sa y} :
    forall (e1 e2:R), 
      Expectation x = Some (Finite e1) ->
      Expectation y = Some (Finite e2) ->
      rv_almost_eq prts x y ->
      e1 = e2.
  Proof.
    intros.
    generalize (Expectation_almost_0 (rvminus x y))
    ; intros HH.
    cut_to HH.
    - unfold rvminus in HH.
      generalize (Expectation_sum x (rvopp y)); intros Esum.
      cut_to Esum.
      + rewrite HH in Esum.
        unfold rvopp in Esum.
        rewrite Expectation_scale in Esum; try lra.
        rewrite H in Esum.
        rewrite H0 in Esum.
        inversion Esum.
        lra.
      + apply Expectation_finite_neg_part with (e := e1); trivial.
      + assert (PositiveRandomVariable (fun x0 => nonneg(pos_fun_part y x0))).
        unfold PositiveRandomVariable, pos_fun_part; simpl.
        intros.
        apply Rmax_r.
        rewrite Expectation_posRV_ext with (prv2 := H2).
        apply Expectation_finite_pos_part with (e := e2); trivial.
        intro x0.
        unfold pos_fun_part, neg_fun_part, rvopp, rvscale; simpl.
        f_equal.
        lra.
    - unfold rv_almost_eq in *.
      unfold const in *.
      assert (event_equiv (fun x0 : Ts => rvminus x y x0 = 0) (fun x0 : Ts => x x0 = y x0)).
      intros a.
      unfold rvminus, rvplus, rvopp, rvscale.
      split; intros; lra.
      now rewrite H2.
   Qed.

  Global Instance L2RRV_expectation_proper : Proper (L2RRV_eq ==> eq) L2RRVexpectation.
  Proof.
    unfold Proper, respectful, L2RRVexpectation, L2RRV_eq.
    unfold L2Expectation.
    intros x y eqq.
    repeat match goal with
      [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    apply (Expectation_finite_proper_almost _ _ _ _ e e0 eqq).
  Qed.

  Definition L2RRVinner (x y:L2RRV) : R
    :=  match (Expectation (rvmult x y)) with
        | Some (Finite z) => z
        | _ => 0
        end.

  Ltac L2RRV_simpl
    := repeat match goal with
              | [H : L2RRV |- _ ] => destruct H as [???]
              end
       ; unfold L2RRVplus, L2RRVminus, L2RRVopp, L2RRVscale
       ; simpl.

  Lemma is_L2_mult_finite x y 
        {xrv:RandomVariable prts borel_sa x}
        {yrv:RandomVariable prts borel_sa y} : 
    IsL2 x -> IsL2 y ->
    match Expectation (rvmult x y) with
    | Some (Finite _) => True
    | _ => False
    end.
  Proof.
    intros HH1 HH2.
    unfold IsL2 in *.
    match_case_in HH1
    ; [intros ? eqq1 | intros eqq1]
    ; rewrite eqq1 in HH1
    ; try contradiction.
    match_destr_in HH1; try contradiction.
    match_case_in HH2
    ; [intros ? eqq2 | intros eqq2]
    ; rewrite eqq2 in HH2
    ; try contradiction.
    match_destr_in HH2; try contradiction.

    apply Expectation_abs_then_finite.
    - typeclasses eauto.
    - generalize (rvprod_abs_bound x y)
      ; intros xyle.

      rewrite Expectation_pos_posRV with (prv:=prvabs _).
      assert (prv2:PositiveRandomVariable (rvplus (rvsqr x) (rvsqr y)))
             by typeclasses eauto.
      generalize (Finite_Expectation_posRV_le (rvabs (rvmult x y))
                                              (rvplus (rvsqr x) (rvsqr y))
                                              (prvabs _)
                                              prv2
                 )
      ; intros HH.
      rewrite <- HH; trivial.
      + etransitivity; try eapply xyle.
        intros a.
        unfold rvscale, rvabs, rvmult.
        assert (0 <= Rabs (x a * y a))
               by apply Rabs_pos.
        lra.
      + generalize (Expectation_posRV_sum (rvsqr x) (rvsqr y))
        ; intros HH3.
        erewrite Expectation_posRV_pf_irrel in HH3.
        rewrite HH3.
        rewrite Expectation_pos_posRV with (prv:=prvsqr _) in eqq1.
        rewrite Expectation_pos_posRV with (prv:=prvsqr _) in eqq2.
        invcs eqq1.
        invcs eqq2.
        rewrite H0, H1.
        reflexivity.
  Qed.
    
  Global Instance L2RRV_inner_proper : Proper (L2RRV_eq ==> L2RRV_eq ==> eq) L2RRVinner.
  Proof.
    unfold Proper, respectful, L2RRV_eq.

    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold L2RRVinner.
    assert (eqq:rv_almost_eq prts (rvmult x1 y1) (rvmult x2 y2)).
    - L2RRV_simpl.
      now apply rv_almost_eq_mult_proper.
    - generalize (Expectation_finite_proper_almost (rvmult x1 y1)  (rvmult x2 y2))
      ; intros HH0.
      L2RRV_simpl; simpl in *.

    generalize (is_L2_mult_finite L2RRV_rv_X3 L2RRV_rv_X1)
    ; intros HH1.
    cut_to HH1; trivial.
    generalize (is_L2_mult_finite L2RRV_rv_X2 L2RRV_rv_X0)
    ; intros HH2.
    cut_to HH2; trivial.
    repeat (match_destr_in HH1; try contradiction).
    repeat (match_destr_in HH2; try contradiction).
    apply HH0; trivial.
  Qed.    

  Lemma L2RRV_plus_comm x y : L2RRV_eq (L2RRVplus x y) (L2RRVplus y x).
  Proof.
    red; intros.
    L2RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus; lra.
  Qed.
  
  Lemma L2RRV_plus_assoc (x y z : L2RRV) : L2RRV_eq (L2RRVplus x (L2RRVplus y z)) (L2RRVplus (L2RRVplus x y) z).
  Proof.
    red; intros.
    L2RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus.
    lra.
  Qed.

  Lemma L2RRV_plus_zero (x : L2RRV) : L2RRV_eq (L2RRVplus x (L2RRVconst 0)) x.
  Proof.
    red; intros.
    L2RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus, const.
    lra.
  Qed.

  Lemma L2RRV_plus_inv (x: L2RRV) : L2RRV_eq (L2RRVplus x (L2RRVopp x)) (L2RRVconst 0).
  Proof.
    red; intros.
    L2RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus, rvopp, rvscale, const.
    lra.
  Qed.

   Lemma L2RRV_scale_scale (x y : R) (u : L2RRV) :
     L2RRV_eq (L2RRVscale x (L2RRVscale y u)) (L2RRVscale (x * y) u).
   Proof.
     red; intros.
     L2RRV_simpl.
     apply rv_almost_eq_eq; intros ?.
     unfold rvplus, rvopp, rvscale, const, mult; simpl.
     lra.
   Qed.

   Lemma L2RRV_scale1 (u : L2RRV) :
     L2RRV_eq (L2RRVscale one u) u.
  Proof.
     red; intros.
     L2RRV_simpl.
     apply rv_almost_eq_eq; intros ?.
     unfold rvplus, rvopp, rvscale, const, mult, one; simpl.
     lra.
  Qed.
  
  Lemma L2RRV_scale_plus_l (x : R) (u v : L2RRV) :
    L2RRV_eq (L2RRVscale x (L2RRVplus u v)) (L2RRVplus (L2RRVscale x u) (L2RRVscale x v)).
  Proof.
     red; intros.
     L2RRV_simpl.
     apply rv_almost_eq_eq; intros ?.
     unfold rvplus, rvopp, rvscale, const, mult; simpl.
     lra.
  Qed.
  
  Lemma L2RRV_scale_plus_r (x y : R) (u : L2RRV) :
    L2RRV_eq (L2RRVscale (x + y) u) (L2RRVplus (L2RRVscale x u) (L2RRVscale y u)).
  Proof.
     red; intros.
     L2RRV_simpl.
     apply rv_almost_eq_eq; intros ?.
     unfold rvplus, rvopp, rvscale, const, mult; simpl.
     lra.
  Qed.

  Lemma L2RRV_inner_comm (x y : L2RRV) :
    L2RRVinner x y = L2RRVinner y x.
  Proof.
    unfold L2RRVinner.
    now rewrite (Expectation_ext (rvmult_comm x y)).
  Qed.
  
  Lemma L2RRV_inner_pos (x : L2RRV) : 0 <= L2RRVinner x x.
  Proof.
    unfold L2RRVinner.
    match_case; intros; [| lra].
    match_case; intros; try lra.
    subst.
    apply (Expectation_le _ _ _ _ (Expectation_const 0) H).
    red; intros.
    unfold const, rvmult.
    fold (Rsqr (x x0)).
    apply Rle_0_sqr.
  Qed.

  Lemma rvsqr_eq (x:Ts->R): rv_eq (rvsqr x) (rvmult x x).
  Proof.
    intros ?.
    reflexivity.
  Qed.

  Lemma L2RRV_inner_zero_inv (x:L2RRV) : L2RRVinner x x = 0 ->
                                         L2RRV_eq x (L2RRVconst 0).
  Proof.
    unfold L2RRVinner, L2RRV_eq.
    destruct x as [x rv l2]; simpl.
    red in l2.
    generalize (Expectation_ext (rvsqr_eq x)); intro exp_ext.
    rewrite exp_ext in l2.
    match_case; [intros r eqq1 | intros eqq1]
    ; rewrite eqq1 in l2; try contradiction.
    match_destr; try contradiction.
    intros; subst.
    unfold rv_almost_eq.
    assert (event_equiv (fun x0 : Ts => x x0 = const 0 x0)
                        (fun x0 : Ts => rvsqr x x0 = 0)).
    intro x0.
    unfold const, rvsqr.
    split; intros.
    rewrite H; unfold Rsqr; lra.
    now apply Rsqr_0_uniq with (r := (x x0)).
    rewrite H.
    apply Expectation_zero_pos.
    - typeclasses eauto.
    - unfold PositiveRandomVariable, rvsqr; intros.
      now apply Rle_0_sqr.
    - now rewrite exp_ext.
  Qed.
  
  Lemma L2RRV_inner_scal (x y : L2RRV) (l : R) :
    L2RRVinner (L2RRVscale l x) y = l * L2RRVinner x y.
  Proof.
    unfold L2RRVinner, L2RRVscale; simpl.
    rewrite (Expectation_ext (rv_X2 := rvscale l (rvmult x y))).
    destruct (Req_EM_T l 0).
    subst.
    rewrite (Expectation_ext (rv_X2 := const 0)).
    rewrite Expectation_const; lra.
    intro x0.
    unfold rvscale, rvmult, const; lra.
    generalize (Expectation_scale l (rvmult x y) n); intros.
    rewrite H.
    case_eq (Expectation (rvmult x y)); intros.
    destruct (Rlt_dec 0 l).
    assert (0 <= l) by lra.
    unfold Rbar_mult; simpl.
    destruct r; simpl; try lra.
    destruct (Rle_dec 0 l); try lra.
    destruct ( Rle_lt_or_eq_dec 0 l r); try lra.
    destruct (Rle_dec 0 l); try lra.
    destruct ( Rle_lt_or_eq_dec 0 l r); try lra.
    assert (0 > l) by lra.
    destruct r; simpl; try lra.
    destruct (Rle_dec 0 l); try lra.
    destruct ( Rle_lt_or_eq_dec 0 l r); try lra.
    destruct (Rle_dec 0 l); try lra.
    destruct ( Rle_lt_or_eq_dec 0 l r); try lra.
    lra.
    intro x0.
    unfold rvmult, rvscale.
    lra.
  Qed.

  Lemma rvprod_bound_abs (rv_X1 rv_X2 : Ts->R) :
    RealRandomVariable_le (rvscale 2 (rvabs (rvmult rv_X1 rv_X2)))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
  Proof.
    assert (PositiveRandomVariable (rvsqr (rvminus (rvabs rv_X1) (rvabs rv_X2)))) by apply prvsqr.
    assert (rv_eq (rvsqr (rvminus (rvabs rv_X1) (rvabs rv_X2))) 
                  (rvplus (rvplus (rvsqr rv_X1) (rvopp (rvscale 2 (rvabs (rvmult rv_X1 rv_X2)))))
                          (rvsqr rv_X2))).
    intro x.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, rvabs, Rsqr.
    rewrite Rabs_mult.
    apply Rminus_diag_uniq.
    ring_simplify.
    do 2 rewrite pow2_abs.
    now ring_simplify.
    rewrite H0 in H; clear H0.
    unfold RealRandomVariable_le; intros.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, rvabs, Rsqr in *.
    unfold PositiveRandomVariable in H.
    specialize (H x).
    apply Rplus_le_compat_l with (r:= (2 * Rabs (rv_X1 x * rv_X2 x))) in H.
    ring_simplify in H.
    now ring_simplify.
  Qed.  

  Lemma rvprod_bound_abs1 (rv_X1 rv_X2 : Ts->R) :
    RealRandomVariable_le (rvabs (rvmult rv_X1 rv_X2))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
    Proof.
      generalize (rvprod_bound_abs rv_X1 rv_X2).
      unfold RealRandomVariable_le, rvscale, rvabs, rvmult, rvsqr, Rsqr; intros.
      specialize (H x).
      assert (Rabs (rv_X1 x * rv_X2 x) <= 2 * Rabs (rv_X1 x * rv_X2 x)).
      apply Rplus_le_reg_l with (r := - Rabs(rv_X1 x * rv_X2 x)).
      ring_simplify.
      apply Rabs_pos.
      lra.
    Qed.

  Lemma L2Expectation_finite_abs_prod (rv_X1 rv_X2:Ts->R) 
        {rv1 : RandomVariable prts borel_sa rv_X1}
        {rv2 : RandomVariable prts borel_sa rv_X2} 
        {l21:IsL2 rv_X1}
        {l22:IsL2 rv_X2}        
    :  match Expectation (rvabs (rvmult rv_X1 rv_X2)) with
       | Some (Finite _) => True
       | _ => False
       end.
  Proof.
    assert (PositiveRandomVariable (rvabs (rvmult rv_X1 rv_X2))) by apply prvabs.
    generalize (Expectation_pos_posRV (rvabs (rvmult rv_X1 rv_X2))); intros.
    generalize (rvprod_bound_abs1 rv_X1 rv_X2); intros.
    assert (PositiveRandomVariable (rvplus (rvsqr rv_X1) (rvsqr rv_X2))).
    apply rvplus_prv; apply prvsqr.
    generalize (Finite_Expectation_posRV_le _ _ H H2 H1); intros.
    unfold IsL2 in *.
    rewrite Expectation_pos_posRV with (prv := prvsqr rv_X1) in l21.
    rewrite Expectation_pos_posRV with (prv := prvsqr rv_X2) in l22.    
    match_case_in l21; intros.
    match_case_in l22; intros.
    rewrite H4 in l21.
    rewrite H5 in l22.
    assert (PositiveRandomVariable (rvsqr rv_X1)) by apply prvsqr.
    assert (PositiveRandomVariable (rvsqr rv_X2)) by apply prvsqr.
    generalize (Expectation_posRV_sum (rvsqr rv_X1) (rvsqr rv_X2)); intros.
    cut_to H3.
    rewrite Expectation_pos_posRV with (prv := H).
    now rewrite <- H3.
    erewrite Expectation_posRV_pf_irrel in H8.
    rewrite H8.
    erewrite Expectation_posRV_pf_irrel in H4.
    rewrite H4.
    erewrite Expectation_posRV_pf_irrel in H5.
    rewrite H5.
    simpl.
    now unfold is_finite.

    rewrite H5 in l22; tauto.
    rewrite H5 in l22; tauto.    
    rewrite H4 in l21; tauto.
    rewrite H4 in l21; tauto.    
  Qed.

  Lemma L2RRV_inner_plus (x y z : L2RRV) :
    L2RRVinner (L2RRVplus x y) z = L2RRVinner x z + L2RRVinner y z.
  Proof.
    unfold L2RRVinner, L2RRVplus; simpl.
    rewrite (Expectation_ext (rv_X2 := rvplus (rvmult x z) (rvmult y z))).
    - destruct x.
      destruct y.
      destruct z.
      simpl.
      generalize (L2Expectation_finite_abs_prod L2RRV_rv_X0 L2RRV_rv_X2); intros.
      generalize (L2Expectation_finite_abs_prod L2RRV_rv_X1 L2RRV_rv_X2); intros.      
      generalize (Expectation_abs_then_finite  (rvmult L2RRV_rv_X0 L2RRV_rv_X2) H); intros.
      generalize (Expectation_abs_then_finite  (rvmult L2RRV_rv_X1 L2RRV_rv_X2) H0); intros.
      match_case_in H1; intros.
      match_case_in H2; intros.
      rewrite Expectation_sum.
      rewrite H3 in H1.
      rewrite H4 in H2.
      rewrite H3, H4.
      match_destr_in H1; try tauto.
      match_destr_in H2; try tauto.
      now apply rvmult_rv.
      now apply rvmult_rv.
      assert (RealRandomVariable_le (neg_fun_part (rvmult L2RRV_rv_X0 L2RRV_rv_X2))
                                    (rvabs (rvmult L2RRV_rv_X0 L2RRV_rv_X2))).
      unfold RealRandomVariable_le, neg_fun_part, rvmult, rvabs; intros.
      simpl.
      unfold Rmax, Rabs.
      match_destr; match_destr; lra.
      apply Finite_Expectation_posRV_le with (prv2 := prvabs (rvmult L2RRV_rv_X0 L2RRV_rv_X2)); trivial.
      match_case_in H; intros.
      rewrite H6 in H.
      match_destr_in H; try tauto.
      rewrite Expectation_pos_posRV with (prv := prvabs (rvmult L2RRV_rv_X0 L2RRV_rv_X2)) in H6.
      inversion H6.
      rewrite H8.
      now unfold is_finite.
      now rewrite H6 in H.
      assert (RealRandomVariable_le (neg_fun_part (rvmult L2RRV_rv_X1 L2RRV_rv_X2))
                                    (rvabs (rvmult L2RRV_rv_X1 L2RRV_rv_X2))).
      unfold RealRandomVariable_le, neg_fun_part, rvmult, rvabs; intros.
      simpl.
      unfold Rmax, Rabs.
      match_destr; match_destr; lra.
      apply Finite_Expectation_posRV_le with (prv2 := prvabs (rvmult L2RRV_rv_X1 L2RRV_rv_X2)); trivial.
      match_case_in H0; intros.
      rewrite H6 in H0.
      match_destr_in H0; try tauto.
      rewrite Expectation_pos_posRV with (prv := prvabs (rvmult L2RRV_rv_X1 L2RRV_rv_X2)) in H6.
      inversion H6.
      rewrite H8.
      now unfold is_finite.
      now rewrite H6 in H0.
      now rewrite H4 in H2.
      now rewrite H3 in H1.
    - intro x0.
      unfold rvmult, rvplus.
      lra.
  Qed.

  Definition L2RRVq : Type := quot L2RRV_eq.

  Definition L2RRVq_const (x:R) : L2RRVq := Quot _ (L2RRVconst x).

  Lemma L2RRVq_constE x : L2RRVq_const x = Quot _ (L2RRVconst x).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite L2RRVq_constE : quot.

  Definition L2RRVq_zero : L2RRVq := L2RRVq_const 0.

  Lemma L2RRVq_zeroE : L2RRVq_zero = L2RRVq_const 0.
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite L2RRVq_zeroE : quot.

  Definition L2RRVq_scale (x:R) : L2RRVq -> L2RRVq
    := quot_lift _ (L2RRVscale x).

  Lemma L2RRVq_scaleE x y : L2RRVq_scale x (Quot _ y)  = Quot _ (L2RRVscale x y).
  Proof.
    apply quot_liftE.
  Qed.

  Hint Rewrite L2RRVq_scaleE : quot.
  
  Definition L2RRVq_opp  : L2RRVq -> L2RRVq
    := quot_lift _ L2RRVopp.

  Lemma L2RRVq_oppE x : L2RRVq_opp (Quot _ x)  = Quot _ (L2RRVopp x).
  Proof.
    apply quot_liftE.
  Qed.

  Hint Rewrite L2RRVq_oppE : quot.

  Definition L2RRVq_plus  : L2RRVq -> L2RRVq -> L2RRVq
    := quot_lift2 _ L2RRVplus.
  
  Lemma L2RRVq_plusE x y : L2RRVq_plus (Quot _ x) (Quot _ y) = Quot _ (L2RRVplus x y).
  Proof.
    apply quot_lift2E.
  Qed.

  Hint Rewrite L2RRVq_plusE : quot.

  Definition L2RRVq_minus  : L2RRVq -> L2RRVq -> L2RRVq
    := quot_lift2 _ L2RRVminus.

  Lemma L2RRVq_minusE x y : L2RRVq_minus (Quot _ x) (Quot _ y) = Quot _ (L2RRVminus x y).
  Proof.
    apply quot_lift2E.
  Qed.

  Hint Rewrite L2RRVq_minusE : quot.

  Definition L2RRVq_inner : L2RRVq -> L2RRVq -> R
    := quot_lift2_to _ L2RRVinner.

  Lemma L2RRVq_innerE x y : L2RRVq_inner (Quot _ x) (Quot _ y) = (L2RRVinner x y).
  Proof.
    apply quot_lift2_toE.
  Qed.

  Hint Rewrite L2RRVq_innerE : quot.

  Ltac L2RRVq_simpl
    := repeat match goal with
       | [H: L2RRVq |- _ ] =>
         let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
              end
       ; try autorewrite with quot
       ; try apply (@eq_Quot _ _ L2RRV_eq_equiv).

  Lemma L2RRVq_plus_comm x y : L2RRVq_plus x y = L2RRVq_plus y x.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_plus_comm.
  Qed.
         
  Lemma L2RRVq_plus_assoc (x y z : L2RRVq) : L2RRVq_plus x (L2RRVq_plus y z) = L2RRVq_plus (L2RRVq_plus x y) z.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_plus_assoc.
  Qed.


  Lemma L2RRVq_plus_zero (x : L2RRVq) : L2RRVq_plus x L2RRVq_zero = x.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_plus_zero.
  Qed.

  Lemma L2RRVq_plus_inv (x: L2RRVq) : L2RRVq_plus x (L2RRVq_opp x) = L2RRVq_zero.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_plus_inv.
  Qed.
    
  Definition L2RRVq_AbelianGroup_mixin : AbelianGroup.mixin_of L2RRVq
    := AbelianGroup.Mixin L2RRVq L2RRVq_plus L2RRVq_opp L2RRVq_zero
                          L2RRVq_plus_comm L2RRVq_plus_assoc
                          L2RRVq_plus_zero L2RRVq_plus_inv.

  Canonical L2RRVq_AbelianGroup :=
    AbelianGroup.Pack L2RRVq L2RRVq_AbelianGroup_mixin L2RRVq.


   Ltac L2RRVq_simpl ::=
     repeat match goal with
       | [H: L2RRVq |- _ ] =>
         let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
       | [H: AbelianGroup.sort L2RRVq_AbelianGroup |- _ ] =>
         let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
           end
       ; try autorewrite with quot
       ; try apply (@eq_Quot _ _ L2RRV_eq_equiv).
  
  Lemma L2RRVq_scale_scale (x y : R_Ring) (u : L2RRVq_AbelianGroup) :
    L2RRVq_scale x (L2RRVq_scale y u) = L2RRVq_scale (x * y) u.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_scale_scale.
  Qed.
  
  Lemma L2RRVq_scale1 (u : L2RRVq_AbelianGroup) :
    L2RRVq_scale one u = u.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_scale1.
  Qed.
  
  Lemma L2RRVq_scale_plus_l (x : R_Ring) (u v : L2RRVq_AbelianGroup) :
    L2RRVq_scale x (plus u v) = plus (L2RRVq_scale x u) (L2RRVq_scale x v).
  Proof.
    L2RRVq_simpl.
    apply L2RRV_scale_plus_l.
  Qed.

  Lemma L2RRVq_scale_plus_r (x y : R_Ring) (u : L2RRVq_AbelianGroup) :
    L2RRVq_scale (plus x y) u = plus (L2RRVq_scale x u) (L2RRVq_scale y u).
  Proof.
    L2RRVq_simpl.
    apply L2RRV_scale_plus_r.
  Qed.

  Definition L2RRVq_ModuleSpace_mixin : ModuleSpace.mixin_of R_Ring L2RRVq_AbelianGroup
    := ModuleSpace.Mixin R_Ring L2RRVq_AbelianGroup
                         L2RRVq_scale L2RRVq_scale_scale L2RRVq_scale1
                         L2RRVq_scale_plus_l L2RRVq_scale_plus_r.

  Canonical L2RRVq_ModuleSpace :=
    ModuleSpace.Pack R_Ring L2RRVq (ModuleSpace.Class R_Ring L2RRVq L2RRVq_AbelianGroup_mixin L2RRVq_ModuleSpace_mixin) L2RRVq.

  Ltac L2RRVq_simpl ::=
     repeat match goal with
       | [H: L2RRVq |- _ ] =>
         let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
       | [H: AbelianGroup.sort L2RRVq_AbelianGroup |- _ ] =>
         let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
       | [H: ModuleSpace.sort R_Ring L2RRVq_ModuleSpace |- _ ] =>
         let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
            end
       ; try autorewrite with quot
       ; try apply (@eq_Quot _ _ L2RRV_eq_equiv).

  Lemma L2RRVq_inner_comm (x y : L2RRVq_ModuleSpace) :
    L2RRVq_inner x y = L2RRVq_inner y x.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_inner_comm.
  Qed.
  
  Lemma L2RRVq_inner_pos (x : L2RRVq_ModuleSpace) : 0 <= L2RRVq_inner x x.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_inner_pos.
  Qed.
  
  Lemma L2RRVq_inner_zero_inv (x:L2RRVq_ModuleSpace) : L2RRVq_inner x x = 0 ->
                                                       x = zero.
  Proof.
    unfold zero; simpl.
    L2RRVq_simpl; intros; L2RRVq_simpl.
    now apply L2RRV_inner_zero_inv.
  Qed.
  
  Lemma L2RRVq_inner_scal (x y : L2RRVq_ModuleSpace) (l : R) :
    L2RRVq_inner (scal l x) y = l * L2RRVq_inner x y.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_inner_scal.
  Qed.

  Lemma L2RRVq_inner_plus (x y z : L2RRVq_ModuleSpace) :
    L2RRVq_inner (plus x y) z = L2RRVq_inner x z + L2RRVq_inner y z.
  Proof.
    L2RRVq_simpl.
    apply L2RRV_inner_plus.
  Qed.
  
  Definition L2RRVq_PreHilbert_mixin : PreHilbert.mixin_of L2RRVq_ModuleSpace
    := PreHilbert.Mixin L2RRVq_ModuleSpace L2RRVq_inner
                        L2RRVq_inner_comm  L2RRVq_inner_pos L2RRVq_inner_zero_inv
                        L2RRVq_inner_scal L2RRVq_inner_plus.

  Canonical L2RRVq_PreHilbert :=
    PreHilbert.Pack L2RRVq (PreHilbert.Class _ _ L2RRVq_PreHilbert_mixin) L2RRVq.


  Definition L2RRVq_lim (lim : ((L2RRVq -> Prop) -> Prop)) : L2RRVq.
  Admitted.
  
  Lemma L2RRVq_lim_complete (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (L2RRVq_lim  F) eps).
  Proof.
  Admitted.

  Definition L2RRVq_Hilbert_mixin : Hilbert.mixin_of L2RRVq_PreHilbert
    := Hilbert.Mixin L2RRVq_PreHilbert L2RRVq_lim L2RRVq_lim_complete.

  Canonical L2RRVq_Hilbert :=
    Hilbert.Pack L2RRVq (Hilbert.Class _ _ L2RRVq_Hilbert_mixin) L2RRVq.

End L2.
