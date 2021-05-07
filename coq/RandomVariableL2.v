Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Export RandomVariableLpR.
Require Import quotient_space.
Require Import RbarExpectation.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section L2.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Lemma big2 : 1 <= 2.
  Proof.
    lra.
  Qed.
  Let nneg2 : nonnegreal := bignneg 2 big2.
  Canonical nneg2.


  Global Instance IsL2_Finite (rv_X:Ts->R)
        {rrv:RandomVariable dom borel_sa rv_X}
        {lp:IsLp prts 2 rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    apply IsLp_Finite in lp; trivial.
    apply big2.
  Qed.

  Lemma Expectation_sqr
        (rv_X :Ts->R)  :
    Expectation (rvsqr rv_X) = Some (Expectation_posRV (rvsqr rv_X)).
  Proof.
    apply Expectation_pos_posRV.
  Qed.
  
  Lemma rvabs_bound (rv_X : Ts -> R) :
    rv_le (rvabs rv_X) (rvplus (rvsqr rv_X) (const 1)).
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
    unfold rv_le; intros x.
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

  Lemma rvabs_pos_eq (rv_X:Ts->R) {prv:PositiveRandomVariable rv_X} :
    rv_eq (rvabs rv_X) rv_X.
  Proof.
    intros a.
    unfold rvabs.
    now rewrite Rabs_pos_eq.
  Qed.
    
  Lemma rvabs_sqr (rv_X : Ts -> R) :
    rv_eq (rvabs (rvsqr rv_X)) (rvsqr rv_X).
    Proof.
      intro x.
      unfold rvabs, rvsqr.
      apply Rabs_pos_eq.
      apply Rle_0_sqr.
    Qed.
      
  Lemma rvsqr_abs (rv_X : Ts -> R) :
    rv_eq (rvsqr (rvabs rv_X)) (rvsqr rv_X).
    Proof.
      intro x.
      unfold rvabs, rvsqr.
      now rewrite <- Rsqr_abs.
    Qed.

    Lemma rvmult_abs (rv_X1 rv_X2 : Ts -> R):
      rv_eq (rvabs (rvmult rv_X1 rv_X2)) (rvmult (rvabs rv_X1) (rvabs rv_X2)).
      Proof.
        intro x.
        unfold rvmult, rvabs.
        apply Rabs_mult.
     Qed.

  Lemma rvprod_bound (rv_X1 rv_X2 : Ts->R) :
    rv_le (rvscale 2 (rvmult rv_X1 rv_X2))
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
    intros x.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr in *.
    unfold PositiveRandomVariable in H.
    specialize (H x).
    lra.
  Qed.  
  
  Lemma rvprod_abs_bound (rv_X1 rv_X2 : Ts->R) :
    rv_le (rvscale 2 (rvabs (rvmult rv_X1 rv_X2)))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
  Proof.
    generalize (rvprod_bound (rvabs rv_X1) (rvabs rv_X2)); intros.
    do 2 rewrite rvsqr_abs in H.
    now rewrite rvmult_abs.
  Qed.

  Lemma rvsum_sqr_bound (rv_X1 rv_X2 : Ts->R) :
    rv_le (rvsqr (rvplus rv_X1 rv_X2)) 
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
    intros x.
    specialize (H x).
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr in *.
    apply Rplus_le_compat_l with (r:= ((rv_X1 x + rv_X2 x) * (rv_X1 x + rv_X2 x))) in H.
    ring_simplify in H.
    ring_simplify.
    apply H.
  Qed.    

    Global Instance is_L2_mult_finite x y 
        {xrv:RandomVariable dom borel_sa x}
        {yrv:RandomVariable dom borel_sa y} : 
    IsLp prts 2 x -> IsLp prts 2 y ->
    IsFiniteExpectation prts (rvmult x y).
  Proof.
    intros HH1 HH2.
    unfold IsLp, IsFiniteExpectation in *.
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

      rewrite (Expectation_pos_posRV _).
      generalize (Finite_Expectation_posRV_le (rvabs (rvmult x y))
                                              (rvplus (rvsqr x) (rvsqr y))
                                              _
                                              _
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

        rewrite rvpower_abs2_unfold in eqq1, eqq2.
        
        rewrite (Expectation_pos_posRV _) in eqq1.
        rewrite (Expectation_pos_posRV _) in eqq2.
        invcs eqq1.
        invcs eqq2.
        rewrite H0, H1.
        reflexivity.
  Qed.

  Definition L2RRVinner (x y:LpRRV prts 2) : R
    := FiniteExpectation prts (rvmult x y).

  Global Instance L2RRV_inner_proper : Proper (LpRRV_eq prts ==> LpRRV_eq prts ==> eq) L2RRVinner.
  Proof.
    unfold Proper, respectful, LpRRV_eq.

    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold L2RRVinner.
    assert (eqq:rv_almost_eq prts (rvmult x1 y1) (rvmult x2 y2)).
    - LpRRV_simpl.
      now apply rv_almost_eq_mult_proper.
    - eapply FiniteExpectation_proper_almost; try eapply eqq
      ; try typeclasses eauto.
  Qed.    

  Lemma L2RRV_inner_comm (x y : LpRRV prts 2) :
    L2RRVinner x y = L2RRVinner y x.
  Proof.
    unfold L2RRVinner.
    apply FiniteExpectation_ext.
    apply rvmult_comm.
  Qed.
  
  Lemma L2RRV_inner_pos (x : LpRRV prts 2) : 0 <= L2RRVinner x x.
  Proof.
    unfold L2RRVinner.
    apply FiniteExpectation_pos.
    typeclasses eauto.
  Qed.

  Lemma rvsqr_eq (x:Ts->R): rv_eq (rvsqr x) (rvmult x x).
  Proof.
    intros ?.
    reflexivity.
  Qed.

  Lemma L2RRV_inner_zero_inv (x:LpRRV prts 2) : L2RRVinner x x = 0 ->
                                         LpRRV_eq prts x (LpRRVconst prts 0).
  Proof.
    unfold L2RRVinner, LpRRV_eq; intros.
    eapply FiniteExpectation_zero_pos in H; try typeclasses eauto.
    red.
    erewrite ps_proper; try eapply H.
    intros a.
    unfold LpRRVconst, const, rvmult.
    split; intros; simpl in *.
    - unfold pre_event_preimage, pre_event_singleton.
      rewrite H0; lra.
    - now apply Rsqr_0_uniq in H0.
      Unshelve.
      typeclasses eauto.
  Qed.
  
  Lemma L2RRV_inner_scal (x y : LpRRV prts 2) (l : R) :
    L2RRVinner (LpRRVscale prts l x) y = l * L2RRVinner x y.
  Proof.
    unfold L2RRVinner, LpRRVscale; simpl.
    rewrite (FiniteExpectation_ext _ _ (rvscale l (rvmult x y))).
    - destruct (Req_EM_T l 0).
      + subst.
        erewrite (FiniteExpectation_ext _ _ (const 0)).
        * rewrite FiniteExpectation_const; lra.
        * intro x0.
          unfold rvscale, rvmult, const; lra.
      + now rewrite (FiniteExpectation_scale _ l (rvmult x y)).
    - intro x0.
      unfold rvmult, rvscale.
      lra.
  Qed.

  Lemma rvprod_abs1_bound (rv_X1 rv_X2 : Ts->R) :
    rv_le (rvabs (rvmult rv_X1 rv_X2))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
  Proof.
    generalize (rvprod_abs_bound rv_X1 rv_X2).
    unfold rv_le, rvscale, rvabs, rvmult, rvsqr, Rsqr; intros H x.
    specialize (H x).
    assert (Rabs (rv_X1 x * rv_X2 x) <= 2 * Rabs (rv_X1 x * rv_X2 x)).
    apply Rplus_le_reg_l with (r := - Rabs(rv_X1 x * rv_X2 x)).
    ring_simplify.
    apply Rabs_pos.
    lra.
  Qed.

  Global Instance L2Expectation_l1_prod (rv_X1 rv_X2:Ts->R) 
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {l21:IsLp prts 2 rv_X1}
        {l22:IsLp prts 2 rv_X2}        
    :  IsFiniteExpectation prts (rvabs (rvmult rv_X1 rv_X2)).

  Proof.
    assert (PositiveRandomVariable (rvabs (rvmult rv_X1 rv_X2))) by apply prvabs.
    generalize (Expectation_pos_posRV (rvabs (rvmult rv_X1 rv_X2))); intros.
    generalize (rvprod_abs1_bound rv_X1 rv_X2); intros.
    assert (PositiveRandomVariable (rvplus (rvsqr rv_X1) (rvsqr rv_X2)))
      by (apply rvplus_prv; apply prvsqr).
    generalize (Finite_Expectation_posRV_le _ _ H H2 H1); intros.
    unfold IsLp, IsFiniteExpectation in *.
    rewrite (Expectation_pos_posRV _) in l21.
    rewrite (Expectation_pos_posRV _)  in l22.    
    match_case_in l21
    ; [intros ? eqq1 | intros eqq1..]
    ; rewrite eqq1 in l21
    ; try contradiction.
    match_case_in l22
    ; [intros ? eqq2 | intros eqq2..]
    ; rewrite eqq2 in l22
    ; try contradiction.
    assert (PositiveRandomVariable (rvsqr rv_X1)) by apply prvsqr.
    assert (PositiveRandomVariable (rvsqr rv_X2)) by apply prvsqr.
    generalize (Expectation_posRV_sum (rvsqr rv_X1) (rvsqr rv_X2)); intros.
    cut_to H3.
    - rewrite Expectation_pos_posRV with (prv := H).
      now rewrite <- H3.
    - erewrite Expectation_posRV_pf_irrel in H6.
      rewrite H6.
      rewrite (Expectation_posRV_ext _ _ (rvpower_abs2_unfold _)) in eqq1.
      rewrite (Expectation_posRV_ext _ _  (rvpower_abs2_unfold _)) in eqq2.
      erewrite Expectation_posRV_pf_irrel in eqq1.
      rewrite eqq1.
      erewrite Expectation_posRV_pf_irrel in eqq2.
      rewrite eqq2.
      simpl.
      now unfold is_finite.
  Qed.

  Lemma L2RRV_inner_plus (x y z : LpRRV prts 2) :
    L2RRVinner (LpRRVplus prts x y) z = L2RRVinner x z + L2RRVinner y z.
  Proof.
    unfold L2RRVinner, LpRRVplus; simpl.
    erewrite (FiniteExpectation_ext _ _ (rvplus (rvmult x z) (rvmult y z))).
    - erewrite <- FiniteExpectation_plus.
      apply FiniteExpectation_pf_irrel.
    - intro x0.
      unfold rvmult, rvplus.
      lra.
  Qed.

  (* get abs version by saying (x : L2RRV) <-> (abs x : L2RRV) *)

  Lemma L2RRV_inner_plus_r (x y z : LpRRV prts 2) :
    L2RRVinner x (LpRRVplus prts y z) = L2RRVinner x y  + L2RRVinner x z.
  Proof.
    do 3 rewrite L2RRV_inner_comm with (x := x).
    now rewrite L2RRV_inner_plus.
  Qed.

  Lemma L2RRV_inner_scal_r (x y : LpRRV prts 2) (l : R) :
    L2RRVinner x (LpRRVscale prts l y) = l * L2RRVinner x y.
  Proof.
    do 2 rewrite L2RRV_inner_comm with (x := x).
    now rewrite L2RRV_inner_scal.
  Qed.

  Lemma L2RRV_Cauchy_Schwarz (x1 x2 : LpRRV prts 2) :
    0 < L2RRVinner x2 x2 ->
    Rsqr (L2RRVinner x1 x2) <= (L2RRVinner x1 x1)*(L2RRVinner x2 x2).
  Proof.
    generalize (L2RRV_inner_pos 
                  (LpRRVminus prts
                     (LpRRVscale prts (L2RRVinner x2 x2) x1)
                     (LpRRVscale prts (L2RRVinner x1 x2) x2))); intros.
    rewrite LpRRVminus_plus, LpRRVopp_scale in H.
    repeat (try rewrite L2RRV_inner_plus in H; try rewrite L2RRV_inner_plus_r in H; 
            try rewrite L2RRV_inner_scal in H; try rewrite L2RRV_inner_scal_r in H).
    ring_simplify in H.
    unfold pow in H.
    do 3 rewrite Rmult_assoc in H.
    rewrite <- Rmult_minus_distr_l in H.
    replace (0) with (L2RRVinner x2 x2 * 0) in H by lra.
    apply Rmult_le_reg_l with (r := L2RRVinner x2 x2) in H; trivial.
    rewrite L2RRV_inner_comm with (x := x2) (y := x1) in H.
    unfold Rsqr; lra.
  Qed.

  Definition L2RRVq_inner : LpRRVq prts 2 -> LpRRVq prts 2 -> R
    := quot_lift2_to _ L2RRVinner.

  Lemma L2RRVq_innerE x y : L2RRVq_inner (Quot _ x) (Quot _ y) = (L2RRVinner x y).
  Proof.
    apply quot_lift2_toE.
  Qed.

  Hint Rewrite L2RRVq_innerE : quot.

  Lemma L2RRVq_inner_comm (x y : LpRRVq_ModuleSpace prts nneg2) :
    L2RRVq_inner x y = L2RRVq_inner y x.
  Proof.
    LpRRVq_simpl.
    apply L2RRV_inner_comm.
  Qed.
  
  Lemma L2RRVq_inner_pos (x : LpRRVq_ModuleSpace prts nneg2) : 0 <= L2RRVq_inner x x.
  Proof.
    LpRRVq_simpl.
    apply L2RRV_inner_pos.
  Qed.
  
  Lemma L2RRVq_inner_zero_inv (x:LpRRVq_ModuleSpace prts nneg2) : L2RRVq_inner x x = 0 ->
                                                       x = zero.
  Proof.
    unfold zero; simpl.
    LpRRVq_simpl; intros; LpRRVq_simpl.
    now apply L2RRV_inner_zero_inv.
  Qed.
  
  Lemma L2RRVq_inner_scal (x y : LpRRVq_ModuleSpace prts nneg2) (l : R) :
    L2RRVq_inner (scal l x) y = l * L2RRVq_inner x y.
  Proof.
    unfold scal; simpl.
    LpRRVq_simpl.
    apply L2RRV_inner_scal.
  Qed.

  Lemma L2RRVq_inner_plus (x y z : LpRRVq_ModuleSpace prts nneg2) :
    L2RRVq_inner (plus x y) z = L2RRVq_inner x z + L2RRVq_inner y z.
  Proof.
    unfold plus; simpl.
    LpRRVq_simpl.
    apply L2RRV_inner_plus.
  Qed.
  
  Definition L2RRVq_PreHilbert_mixin : PreHilbert.mixin_of (LpRRVq_ModuleSpace prts nneg2)
    := PreHilbert.Mixin (LpRRVq_ModuleSpace prts nneg2) L2RRVq_inner
                        L2RRVq_inner_comm  L2RRVq_inner_pos L2RRVq_inner_zero_inv
                        L2RRVq_inner_scal L2RRVq_inner_plus.

  Canonical L2RRVq_PreHilbert :=
    PreHilbert.Pack (LpRRVq prts 2) (PreHilbert.Class _ _ L2RRVq_PreHilbert_mixin) (LpRRVq prts 2).

  Lemma L2RRVq_Cauchy_Schwarz (x1 x2 : LpRRVq prts 2) :
    0 < L2RRVq_inner x2 x2 ->
    Rsqr (L2RRVq_inner x1 x2) <= (L2RRVq_inner x1 x1)*(L2RRVq_inner x2 x2).
  Proof.
    LpRRVq_simpl.
    apply L2RRV_Cauchy_Schwarz.
  Qed.

  (* generalize to be over any normed space *)
   Definition Cauchy_crit (Un : nat -> LpRRV prts 2) : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat,
        (forall n m:nat,
          (n >= N)%nat -> (m >= N)%nat -> LpRRVnorm prts (LpRRVminus prts (Un n) (Un m)) < eps).

   Lemma inv_pow_2_pos (n : nat) :
        0 < / (pow 2 n) .
  Proof.
    apply Rinv_0_lt_compat.
    apply pow_lt.
    lra.
  Qed.

  Definition L2RRV_lim_ball_center (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop) :
    ProperFilter F -> cauchy F ->
    forall (n:nat), {b:LpRRV prts 2 ->Prop | F b}.
  Proof.
    intros Pf cF n.
    pose ( ϵ := / (pow 2 n)).
    assert (ϵpos : 0 < ϵ) by apply inv_pow_2_pos.
    destruct (constructive_indefinite_description _ (cF (mkposreal ϵ ϵpos)))
      as [x Fx].
    simpl in *.
    now exists  (Hierarchy.ball (M:= LpRRV_UniformSpace prts big2) x ϵ).
  Defined.

  Definition L2RRV_lim_ball_cumulative
             (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : {x:LpRRV prts 2->Prop | F x}
    := fold_right (fun x y =>
                     exist _ _ (Hierarchy.filter_and
                       _ _ (proj2_sig x) (proj2_sig y)))
                  (exist _ _ Hierarchy.filter_true)
                  (map (L2RRV_lim_ball_center F PF cF) (seq 0 (S n))).

  Definition L2RRV_lim_picker
             (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : LpRRV prts 2
    := (proj1_sig (
            constructive_indefinite_description
              _
              (filter_ex
                 _
                 (proj2_sig (L2RRV_lim_ball_cumulative F PF cF n))))).

    Lemma lim_picker_cumulative_included
             (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N n:nat) :
      (N <= n)%nat ->
      forall x,
      proj1_sig (L2RRV_lim_ball_cumulative F PF cF n) x ->
       (proj1_sig (L2RRV_lim_ball_center F PF cF N)) x.
    Proof.
      unfold L2RRV_lim_ball_cumulative.
      intros.
      assert (inn:In N (seq 0 (S n))).
      {
        apply in_seq.
        lia.
      }
      revert inn H0.
      generalize (seq 0 (S n)).
      clear.
      induction l; simpl.
      - tauto.
      - intros [eqq | inn]; intros.
        + subst.
          tauto.
        + apply (IHl inn).
          tauto.
    Qed.
    
  Lemma lim_picker_included
             (F : (LpRRV_UniformSpace prts big2  -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N n:nat) :
    (N <= n)%nat ->
    (proj1_sig (L2RRV_lim_ball_center F PF cF N)) 
      (L2RRV_lim_picker F PF cF n).
  Proof.
    intros.
    unfold L2RRV_lim_picker.
    unfold proj1_sig at 2.
    match_destr.
    eapply lim_picker_cumulative_included; eauto.
  Qed.

  Lemma LpRRVq_opp_opp (x : LpRRVq prts 2) :
    opp x = LpRRVq_opp prts x.
  Proof.
    unfold opp; simpl.
    LpRRVq_simpl.
    reflexivity.
  Qed.

  Lemma LpRRVq_norm_norm (x : LpRRVq prts 2) :
    Hnorm x = LpRRVq_norm prts x.
  Proof.
    unfold Hnorm; simpl.
    LpRRVq_simpl.
    rewrite LpRRVq_normE.
    unfold LpRRVnorm.
    unfold L2RRVinner.
    rewrite power_sqrt.
    - f_equal.
      apply FiniteExpectation_ext.
      intros ?; simpl.
      now rewrite rvpower_abs2_unfold, rvsqr_eq.
    - apply FiniteExpectation_pos.
      typeclasses eauto.
  Qed.

  Lemma LpRRVq_minus_plus_opp'
        (x y : LpRRVq prts 2) :
    LpRRVq_minus prts x y = LpRRVq_plus prts x (LpRRVq_opp prts y).
  Proof.
    unfold minus, plus, opp; simpl.
    LpRRVq_simpl.
    now rewrite LpRRVminus_plus.
  Qed.

  Lemma Hnorm_minus_opp {T:PreHilbert} (a b:T) :
    (Hnorm (minus a b) = Hnorm (minus b a)).
  Proof.
    rewrite <- (norm_opp (minus a b)).
    rewrite opp_minus.
    reflexivity.
  Qed.

  Lemma LpRRV_norm_opp (x : LpRRV prts 2) : LpRRVnorm prts (LpRRVopp prts x) = LpRRVnorm prts x.
  Proof.
    unfold LpRRVnorm, LpRRVopp.
    f_equal.
    apply FiniteExpectation_ext.
    simpl.
    intro z.
    rv_unfold.
    f_equal.
    replace (-1 * (x z)) with (- x z) by lra.
    now rewrite Rabs_Ropp.
  Qed.

  Lemma lim_ball_center_dist (x y : LpRRV prts 2)
             (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N:nat) :
    (proj1_sig (L2RRV_lim_ball_center F PF cF N)) x ->
    (proj1_sig (L2RRV_lim_ball_center F PF cF N)) y ->
    LpRRVnorm prts (LpRRVminus prts x y) < 2 / pow 2 N.
  Proof.
    unfold L2RRV_lim_ball_center; simpl.
    unfold proj1_sig.
    match_case; intros.
    match_destr_in H.
    invcs H.
    unfold Hierarchy.ball in *; simpl in *.
    unfold ball in *; simpl in *.
    generalize (Rplus_lt_compat _ _ _ _ H0 H1)
    ; intros HH.
    field_simplify in HH.
    - eapply Rle_lt_trans; try eapply HH.
      generalize (LpRRV_norm_plus prts big2 (LpRRVminus prts x x1) (LpRRVminus prts x1 y)); intros HH2.
      repeat rewrite LpRRVminus_plus in HH2.
      repeat rewrite LpRRVminus_plus.
      assert (eqq:LpRRV_seq (LpRRVplus prts (LpRRVplus prts x (LpRRVopp prts x1))
                                   (LpRRVplus prts x1 (LpRRVopp prts y)))
                            ((LpRRVplus prts x (LpRRVopp prts y)))).
      {
        intros ?; simpl.
        rv_unfold; lra.
      }
      generalize (LpRRV_norm_opp (LpRRVplus prts x (LpRRVopp prts x1)))
      ; intros eqq3.
      subst nneg2.
      rewrite <- eqq.
      eapply Rle_trans; try eapply HH2.
      apply Rplus_le_compat_r.
      simpl in *.
      rewrite <- eqq3.
      right.
      apply LpRRV_norm_sproper.
      intros ?; simpl.
      rv_unfold; lra.
    - revert HH.
      apply pow_nzero.
      lra.
  Qed.
  
  Lemma lim_filter_cauchy 
        (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    forall N : nat,
      forall n m : nat,
        (n >= N)%nat ->
        (m >= N)%nat -> 
        LpRRVnorm prts (LpRRVminus 
                            prts  
                            (L2RRV_lim_picker F PF cF n)
                            (L2RRV_lim_picker F PF cF m)) < 2 / pow 2 N.
  Proof.
    intros.
    apply (lim_ball_center_dist _ _ F PF cF); now apply lim_picker_included.
  Qed.    

  Lemma cauchy_filter_sum_bound 
        (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    ex_series (fun n => 
                 LpRRVnorm prts 
                             (LpRRVminus prts
                                (L2RRV_lim_picker F PF cF (S n))
                                (L2RRV_lim_picker F PF cF n))).
  Proof.
    apply (@ex_series_le R_AbsRing R_CompleteNormedModule) with
        (b := fun n => 2 / pow 2 n).
    intros; unfold norm; simpl.
    unfold abs; simpl.
    rewrite Rabs_pos_eq.
    left.
    apply (lim_filter_cauchy F PF cF n (S n) n); try lia.
    unfold LpRRVnorm.
    apply power_nonneg.
    unfold Rdiv.
    apply (@ex_series_scal_l R_AbsRing R_CompleteNormedModule).
    apply ex_series_ext with (a := fun n => (/ 2)^n).
    intros; now rewrite Rinv_pow.
    apply ex_series_geom.
    rewrite Rabs_pos_eq; lra.
 Qed.

  Lemma cauchy_filter_sum_abs0
        (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar (p:=2)
      prts 
      (Rbar_rvlim
         (fun n0 =>
            LpRRVsum prts big2 
                     (fun n =>
                        (LpRRVabs prts
                                  (LpRRVminus prts
                                              (L2RRV_lim_picker F PF cF (S (S n)))
                                              (L2RRV_lim_picker F PF cF (S n))))) n0)).
  Proof.
    apply (islp_Rbar_lim_telescope_abs prts big2
                                       (fun n => L2RRV_lim_picker F PF cF (S n)))
    ; [ | typeclasses eauto ]; intros.
    generalize (lim_filter_cauchy F PF cF (S n) (S (S n)) (S n)); intros.
    simpl.
    cut_to H; try lia.
    simpl in H.
    unfold Rdiv in H.
    rewrite Rinv_mult_distr in H; try lra; [|apply pow2_nzero].
    rewrite <- Rmult_assoc in H.
    rewrite Rinv_r in H; try lra.
    rewrite Rmult_1_l in H.
    apply H.
  Qed.

  Lemma cauchy_filter_sum_abs
        (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts (p:=2)  
         (Rbar_rvlim
            (rvsum
               (fun n =>
                  (LpRRVabs prts
                            (LpRRVminus prts
                                        (L2RRV_lim_picker F PF cF (S (S n)))
                                        (L2RRV_lim_picker F PF cF (S n))))))).
  Proof.
    apply (IsLp_Rbar_proper (p:=2) prts ) with
        (x :=  (Rbar_rvlim
            (fun n0 =>
               LpRRVsum prts big2 
                 (fun n =>
                  (LpRRVabs prts
                            (LpRRVminus prts
                                        (L2RRV_lim_picker F PF cF (S (S n)))
                                        (L2RRV_lim_picker F PF cF (S n))))) n0))); trivial.
    - intro x.
      f_equal.
    - apply cauchy_filter_sum_abs0.
    Qed.

  Lemma Rbar_power_le (x y p : Rbar) :
    0 <= p ->
    Rbar_le 0 x ->
    Rbar_le x y ->
    Rbar_le (Rbar_power (p:=p) x) (Rbar_power (p := p) y).
  Proof.
    intros.
    destruct x; destruct y; simpl in *; trivial; try tauto.
    apply Rle_power_l; trivial; lra.
  Qed.

  Lemma Rbar_abs_nneg (x : Rbar) :
    Rbar_le 0 (Rbar_abs x).
  Proof.
    unfold Rbar_abs; destruct x; simpl; try tauto.
    apply Rabs_pos.
  Qed.

  Lemma series_is_lim_seq (f:nat -> R) (l:R) :
    is_lim_seq (sum_n f) l <-> is_series f l.
  Proof.
    easy.
   Qed.

  Lemma ex_series_is_lim_seq (f : nat -> R) :
    ex_series f -> is_lim_seq (sum_n f) (Series f).
  Proof.
    intros.
    now apply Series_correct in H.
  Qed.

  Lemma ex_series_Lim_seq (f : nat -> R) :
    ex_series f -> Lim_seq (sum_n f) = Series f.
  Proof.
    intros.
    apply ex_series_is_lim_seq in H.
    now apply is_lim_seq_unique in H.
  Qed.

  Lemma ex_finite_lim_series (f : nat -> R) :
    ex_finite_lim_seq (sum_n f) <-> ex_series f.
  Proof.
    easy.
  Qed.

  Lemma series_abs_bounded (f : nat -> R) :
    is_finite (Lim_seq (sum_n (fun n=> Rabs (f n)))) ->
    ex_series (fun n => Rabs (f n)).
  Proof.
    intros.
    rewrite <- ex_finite_lim_series.
    rewrite ex_finite_lim_seq_correct.
    split; trivial.
    apply ex_lim_seq_incr.
    intros.
    rewrite sum_Sn.
    apply Rplus_le_compat1_l.
    apply Rabs_pos.
  Qed.

  Lemma Rabs_lim_sum_le0 (f : nat -> Ts -> R) (x : Ts) :
    is_finite (Lim_seq (sum_n (fun n=> Rabs (f n x)))) ->
    Rbar_le
      (Rbar_abs (Lim_seq (fun n => (rvsum f) n x)))
      (Rbar_abs (Lim_seq (fun n => (rvsum (fun n0 => (rvabs (f n0))) n x)))).
  Proof.
    intros.
    apply series_abs_bounded in H.
    generalize H; intros HH.
    generalize (ex_series_Rabs (fun n => (f n x)) H); intros.
    generalize (Series_Rabs (fun n => (f n x)) H); intros.
    unfold rvsum, rvabs.
    apply ex_series_Lim_seq in H.
    apply ex_series_Lim_seq in H0.
    replace (Lim_seq
               (fun n : nat => sum_n (fun n0 : nat => f n0 x) n))
      with (Finite ( Series (fun n : nat => f n x))).
    replace (Lim_seq
          (fun n : nat =>
             sum_n (fun n0 : nat => Rabs (f n0 x)) n))
      with (Finite (Series (fun n : nat => Rabs (f n x)))).
    simpl.
    apply Rge_le.
    rewrite Rabs_right.
    apply Rle_ge, H1.
    apply Rle_ge, Series_nonneg; trivial.
    intros.
    apply Rabs_pos.
  Qed.

  Lemma Rabs_lim_sum_le (f : nat -> Ts -> R) (x : Ts) :
    Rbar_le
      (Rbar_abs (Lim_seq (fun n => (rvsum f) n x)))
      (Rbar_abs (Lim_seq (fun n => (rvsum (fun n0 => (rvabs (f n0))) n x)))).
  Proof.
    case_eq (Lim_seq
          (fun n : nat =>
           rvsum (fun n0 : nat => rvabs (f n0)) n x)); intros.
    - rewrite <- H.
      apply Rabs_lim_sum_le0.
      unfold rvsum, rvabs in H.
      replace  (Lim_seq (sum_n (fun n : nat => Rabs (f n x))))
        with
           (Lim_seq
              (fun n : nat =>
                 sum_n (fun n0 : nat => Rabs (f n0 x)) n)).
      now rewrite H.
      apply Lim_seq_ext.
      intros; trivial.
    - destruct (Lim_seq (fun n : nat => rvsum f n x)); now simpl.
    - assert (Rbar_le 0 (Lim_seq
        (fun n : nat =>
         rvsum (fun n0 : nat => rvabs (f n0)) n x))).
      + apply Lim_seq_pos.
        intros.
        unfold rvsum, rvabs.
        apply sum_n_nneg.
        intros.
        apply Rabs_pos.
      + rewrite H in H0.
        now simpl in H0.
  Qed.

  Lemma cauchy_filter_sum
        (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts (p:=2)  
         (Rbar_rvlim
            (rvsum
               (fun n =>
                  (LpRRVminus prts
                              (L2RRV_lim_picker F PF cF (S (S n)))
                              (L2RRV_lim_picker F PF cF (S n)))))).
  Proof.
    generalize (cauchy_filter_sum_abs F PF cF).
    unfold IsLp_Rbar; intros.
    unfold LpRRVnorm in H.
    eapply (is_finite_Rbar_Expectation_posRV_le _ _ _ H).
    Unshelve.
    intro x.
    unfold Rbar_rvlim.
    apply Rbar_power_le with (p := 2); [simpl; lra | apply Rbar_abs_nneg | ].
    simpl.
    apply Rabs_lim_sum_le.
  Qed.

  Lemma LpRRVsum_telescope0
        (f: nat -> LpRRV prts 2) : 
    forall n0,
      LpRRV_seq (LpRRVsum prts big2
                (fun n => (LpRRVminus prts (f (S n)) (f n))) 
                n0)
      (LpRRVminus prts (f (S n0)) (f 0%nat)).
   Proof.
     intros; induction n0.
     - intros x; simpl.
       unfold rvsum.
       now rewrite sum_O.
     - simpl in *.
       intros x; simpl.
       specialize (IHn0 x).
       simpl in *.
       unfold rvsum in *.
       rewrite sum_Sn.
       rewrite IHn0.
       rv_unfold.
       unfold plus; simpl.
       lra.
   Qed.

   Lemma LpRRVsum_telescope
        (f: nat -> LpRRV prts 2) : 
     forall n0,
      LpRRV_seq (LpRRVplus prts (f 0%nat)
                 (LpRRVsum prts big2
                           (fun n => (LpRRVminus prts (f (S n)) (f n))) 
                           n0))
                 (f (S n0)).
     Proof.
       intros.
       rewrite LpRRVsum_telescope0.
       rewrite LpRRVminus_plus.
       intros ?; simpl.
       rv_unfold; lra.
     Qed.

  Lemma cauchy_filter_sum_telescope
        (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    forall n0, 
      LpRRV_seq (LpRRVplus prts
                (L2RRV_lim_picker F PF cF (S 0%nat))
                (LpRRVsum prts big2 
                   (fun n =>
                      (LpRRVminus prts
                              (L2RRV_lim_picker F PF cF (S (S n)))
                              (L2RRV_lim_picker F PF cF (S n)))) n0))
                (L2RRV_lim_picker F PF cF (S (S n0))).
  Proof.
    intros.
    apply (LpRRVsum_telescope 
             (fun n =>
                L2RRV_lim_picker F PF cF (S n))).
  Qed.

  Lemma cauchy_filter_Rbar_lim
        (F : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts (p:=2)  
         (Rbar_rvlim
            (fun n => LpRRVminus prts
                        (L2RRV_lim_picker F PF cF (S (S n)))
                        (L2RRV_lim_picker F PF cF (S 0%nat))
                        
         )).
  Proof.
   apply (IsLp_Rbar_proper (p:=2) prts ) with
       (x :=  
             (Rbar_rvlim
               (fun n0 =>
                  LpRRVsum prts big2 
                           (fun n =>
                              (LpRRVminus prts
                                          (L2RRV_lim_picker F PF cF (S (S n)))
                                          (L2RRV_lim_picker F PF cF (S n))))
                           n0))).
   intro z.
   unfold Rbar_rvlim.
   apply Lim_seq_ext.
   intros.
   apply (LpRRVsum_telescope0 (fun n => (L2RRV_lim_picker F PF cF (S n)))).
   apply cauchy_filter_sum.
  Qed.

  Definition L2RRV_lim_with_conditions (lim : (LpRRV_UniformSpace prts big2 -> Prop) -> Prop)
    (PF:ProperFilter lim)
    (cF:cauchy lim) : LpRRV prts 2.
  Admitted.
  
  Definition L2RRV_lim (lim : ((LpRRV prts 2 -> Prop) -> Prop)) : LpRRV prts 2.
  Proof.
    destruct (excluded_middle_informative (ProperFilter lim)).
    - destruct (excluded_middle_informative (cauchy (T:= LpRRV_UniformSpace prts big2) lim)).
      + exact (L2RRV_lim_with_conditions _ p c).
      + exact (LpRRVzero prts).
    - exact (LpRRVzero prts).
  Defined.

  (*
  Lemma L2RRVq_lim_complete (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (L2RRV_lim  F) eps).
  Proof.
    intros.
    unfold L2RRVq_lim; simpl.
    match_destr; [| tauto].
    match_destr; [| tauto].
  Admitted.

  Definition L2RRVq_Hilbert_mixin : Hilbert.mixin_of L2RRVq_PreHilbert
    := Hilbert.Mixin L2RRVq_PreHilbert L2RRVq_lim L2RRVq_lim_complete.

  Canonical L2RRVq_Hilbert :=
    Hilbert.Pack (LpRRVq prts 2) (Hilbert.Class _ _ L2RRVq_Hilbert_mixin) (LpRRVq prts 2).
*)
End L2.
