Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Classical.
Require Import FunctionalExtensionality.

Require Import hilbert.

Require Export RandomVariableL1.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section L2.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Definition IsL2 (rv_X:Ts->R)
    := IsFiniteExpectation prts (rvsqr rv_X).

  Existing Class IsL2.
  Typeclasses Transparent IsL2.

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
    
  Global Instance isL2_isL1 (rv_X:Ts->R) 
        {rv : RandomVariable prts borel_sa rv_X}
        {l2:IsL2 rv_X}
    :  IsL1 prts rv_X.
  Proof.
    generalize (rvabs_bound rv_X)
    ; intros HH.
    eapply (IsL1_bounded _ _ (rvplus (rvsqr rv_X) (const 1))).
    etransitivity; try eapply rvabs_bound.
    reflexivity.
    Unshelve.
    eapply IsFiniteExpectation_plus; try typeclasses eauto.
    eauto.
  Qed.

  Lemma rvsqr_const (c:R) : rv_eq (Ts:=Ts) (rvsqr (const c)) (const (Rsqr c)).
  Proof.
    intros a.
    reflexivity.
  Qed.
    
  Global Instance is_L2_const x : IsL2 (const x).
  Proof.
    unfold IsL2.
    rewrite rvsqr_const.
    typeclasses eauto.
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

    Lemma isL2_abs (rv_X : Ts -> R) :
      IsL2 rv_X <-> IsL2 (rvabs rv_X).
    Proof.
      unfold IsL2.
      now rewrite rvsqr_abs.
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

  Global Instance is_L2_plus rv_X1 rv_X2
           {rv1:RandomVariable prts borel_sa rv_X1}
           {rv2:RandomVariable prts borel_sa rv_X2}
           {isl21:IsL2 rv_X1}
           {isl22:IsL2 rv_X2} :
    IsL2 (rvplus rv_X1 rv_X2).
  Proof.
    unfold IsL2, IsFiniteExpectation in *.
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

  Global Instance is_L2_scale x rv_X 
           {isl2:IsL2 rv_X} :
    IsL2 (rvscale x rv_X).
  Proof.
    unfold IsL2, IsFiniteExpectation.
    assert (rv_eq  (rvsqr (rvscale x rv_X)) (rvscale (Rsqr x) (rvsqr rv_X))).
    - intro x0.
      unfold rvsqr, rvscale, Rsqr; lra.
    - destruct (Rlt_dec 0 (Rsqr x)).
      + rewrite (Expectation_ext (rv_X2 := (rvscale (mkposreal _ r) (rvsqr rv_X))) H).
        rewrite Expectation_scale_posreal.
        unfold IsL2,IsFiniteExpectation in isl2.
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

  Global Instance is_L2_opp rv_X 
           {isl2:IsL2 rv_X} :
    IsL2 (rvopp rv_X).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance is_L2_minus rv_X1 rv_X2
           {rv1:RandomVariable prts borel_sa rv_X1}
           {rv2:RandomVariable prts borel_sa rv_X2}
           {isl21:IsL2 rv_X1}
           {isl22:IsL2 rv_X2} :
    IsL2 (rvminus rv_X1 rv_X2).
  Proof.
    typeclasses eauto.
  Qed.

    Global Instance is_L2_mult_finite x y 
        {xrv:RandomVariable prts borel_sa x}
        {yrv:RandomVariable prts borel_sa y} : 
    IsL2 x -> IsL2 y ->
    IsFiniteExpectation prts (rvmult x y).
  Proof.
    intros HH1 HH2.
    unfold IsL2, IsFiniteExpectation in *.
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

  Lemma L2RRVminus_plus (rv1 rv2:L2RRV) :
    L2RRV_eq 
      (L2RRVminus rv1 rv2) (L2RRVplus rv1 (L2RRVopp rv2)).
  Proof.
    apply rv_almost_eq_eq.
    reflexivity.
  Qed.

  Lemma L2RRVopp_scale (rv:L2RRV) :
    L2RRV_eq 
      (L2RRVopp rv) (L2RRVscale (-1) rv).
  Proof.
    red.
    apply rv_almost_eq_eq.
    reflexivity.
  Qed.
  
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
    := FiniteExpectation prts rv.

  Global Instance L2RRV_expectation_proper : Proper (L2RRV_eq ==> eq) L2RRVexpectation.
  Proof.
    unfold Proper, respectful, L2RRVexpectation, L2RRV_eq.
    intros.
    apply FiniteExpectation_proper_almost
    ; eauto.
    apply x.
    apply y.
  Qed.

  Definition L2RRVinner (x y:L2RRV) : R
    :=  FiniteExpectation prts (rvmult x y).

  Ltac L2RRV_simpl
    := repeat match goal with
              | [H : L2RRV |- _ ] => destruct H as [???]
              end
       ; unfold L2RRVplus, L2RRVminus, L2RRVopp, L2RRVscale
       ; simpl.
  
  Global Instance L2RRV_inner_proper : Proper (L2RRV_eq ==> L2RRV_eq ==> eq) L2RRVinner.
  Proof.
    unfold Proper, respectful, L2RRV_eq.

    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold L2RRVinner.
    assert (eqq:rv_almost_eq prts (rvmult x1 y1) (rvmult x2 y2)).
    - L2RRV_simpl.
      now apply rv_almost_eq_mult_proper.
    - eapply FiniteExpectation_proper_almost; try eapply eqq
      ; try typeclasses eauto.
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
    now rewrite (FiniteExpectation_ext prts _ _ (rvmult_comm x y)).
  Qed.
  
  Lemma L2RRV_inner_pos (x : L2RRV) : 0 <= L2RRVinner x x.
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

  Lemma L2RRV_inner_zero_inv (x:L2RRV) : L2RRVinner x x = 0 ->
                                         L2RRV_eq x (L2RRVconst 0).
  Proof.
    
    unfold L2RRVinner, L2RRV_eq; intros.
    apply FiniteExpectation_zero_pos in H; try typeclasses eauto.
    red.
    erewrite ps_proper; try eapply H.
    intros a.
    unfold L2RRVconst, const, rvmult.
    split; intros; simpl in *.
    - rewrite H0; lra.
    - now apply Rsqr_0_uniq in H0.
  Qed.
  
  Lemma L2RRV_inner_scal (x y : L2RRV) (l : R) :
    L2RRVinner (L2RRVscale l x) y = l * L2RRVinner x y.
  Proof.
    unfold L2RRVinner, L2RRVscale; simpl.
    rewrite (FiniteExpectation_ext _ _ (rvscale l (rvmult x y))).
    - destruct (Req_EM_T l 0).
      + subst.
        rewrite (FiniteExpectation_ext _ _ (const 0)).
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
        {rv1 : RandomVariable prts borel_sa rv_X1}
        {rv2 : RandomVariable prts borel_sa rv_X2} 
        {l21:IsL2 rv_X1}
        {l22:IsL2 rv_X2}        
    :  IsL1 prts (rvmult rv_X1 rv_X2).

  Proof.
    assert (PositiveRandomVariable (rvabs (rvmult rv_X1 rv_X2))) by apply prvabs.
    generalize (Expectation_pos_posRV (rvabs (rvmult rv_X1 rv_X2))); intros.
    generalize (rvprod_abs1_bound rv_X1 rv_X2); intros.
    assert (PositiveRandomVariable (rvplus (rvsqr rv_X1) (rvsqr rv_X2))).
    apply rvplus_prv; apply prvsqr.
    generalize (Finite_Expectation_posRV_le _ _ H H2 H1); intros.
    unfold IsL2 in *.
    unfold IsL1, IsFiniteExpectation in *.
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
    rewrite (FiniteExpectation_ext _ _ (rvplus (rvmult x z) (rvmult y z))).
    - erewrite <- FiniteExpectation_plus.
      apply FiniteExpectation_pf_irrel.
    - intro x0.
      unfold rvmult, rvplus.
      lra.
  Qed.

  (* get abs version by saying (x : L2RRV) <-> (abs x : L2RRV) *)

  Lemma L2RRV_inner_plus_r (x y z : L2RRV) :
    L2RRVinner x (L2RRVplus y z) = L2RRVinner x y  + L2RRVinner x z.
  Proof.
    do 3 rewrite L2RRV_inner_comm with (x := x).
    now rewrite L2RRV_inner_plus.
  Qed.

  Lemma L2RRV_inner_scal_r (x y : L2RRV) (l : R) :
    L2RRVinner x (L2RRVscale l y) = l * L2RRVinner x y.
  Proof.
    do 2 rewrite L2RRV_inner_comm with (x := x).
    now rewrite L2RRV_inner_scal.
  Qed.

  Lemma L2RRV_Cauchy_Schwarz (x1 x2 : L2RRV) :
    0 < L2RRVinner x2 x2 ->
    Rsqr (L2RRVinner x1 x2) <= (L2RRVinner x1 x1)*(L2RRVinner x2 x2).
  Proof.
    generalize (L2RRV_inner_pos 
                  (L2RRVminus
                     (L2RRVscale (L2RRVinner x2 x2) x1)
                     (L2RRVscale (L2RRVinner x1 x2) x2))); intros.
    rewrite L2RRVminus_plus, L2RRVopp_scale in H.
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

  Lemma L2RRVq_minus_plus (rv1 rv2:L2RRVq) :
    L2RRVq_minus rv1 rv2 = L2RRVq_plus rv1 (L2RRVq_opp rv2).
  Proof.
    L2RRVq_simpl.
    apply L2RRVminus_plus.
  Qed.

  Lemma L2RRVq_opp_scale (rv:L2RRVq) :
    L2RRVq_opp rv =L2RRVq_scale (-1) rv.
  Proof.
    L2RRVq_simpl.
    apply L2RRVopp_scale.
  Qed.
  
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

  Lemma L2RRVq_Cauchy_Schwarz (x1 x2 : L2RRVq) :
    0 < L2RRVq_inner x2 x2 ->
    Rsqr (L2RRVq_inner x1 x2) <= (L2RRVq_inner x1 x1)*(L2RRVq_inner x2 x2).
  Proof.
    L2RRVq_simpl.
    apply L2RRV_Cauchy_Schwarz.
  Qed.

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
