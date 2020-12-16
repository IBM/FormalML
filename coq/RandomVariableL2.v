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

Set Bullet Behavior "Strict Subproofs".

Section L2.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).


  Class IsL2 (rv_X:Ts->R) {rv:RandomVariable prts borel_sa rv_X}
    := is_L2 : match Expectation (rvsqr rv_X) with
       | Some (Finite _) => True
       | _ => False
       end.

  Instance is_L2_const x : IsL2 (const x).
  Proof.
    unfold IsL2.
    assert (@rv_eq Ts R (rvsqr (const x)) (const (Rsqr x))).
    - intro x0.
      now unfold rvsqr, const.
    - rewrite Expectation_ext with (rv2 := (rvconst (Rsqr x))); trivial.
      generalize (Rle_0_sqr x); intros.
      rewrite Expectation_pos_posRV with (prv := (@prvconst Ts (Rsqr x) H0)).
      now rewrite Expectation_posRV_const.
  Qed.

  Instance is_L2_plus rv_X1 rv_X2
           {rv1:RandomVariable prts borel_sa rv_X1}
           {rv2:RandomVariable prts borel_sa rv_X2}
           {isl21:IsL2 rv_X1}
           {isl22:IsL2 rv_X2} :
    IsL2 (rvplus rv_X1 rv_X2).
  Proof.
    unfold IsL2.
  Admitted.

  Instance is_L2_scale x rv_X {rv:RandomVariable prts borel_sa rv_X}
           {isl2:IsL2 rv_X} :
    IsL2 (rvscale x rv_X).
  Proof.
    unfold IsL2.
    assert (rv_eq  (rvsqr (rvscale x rv_X)) (rvscale (Rsqr x) (rvsqr rv_X))).
    - intro x0.
      unfold rvsqr, rvscale, Rsqr; lra.
    - destruct (Rlt_dec 0 (Rsqr x)).
      + rewrite Expectation_ext with (rv2 := (rvscale_rv prts (mkposreal _ r) (rvsqr rv_X) 
                                                         (rvsqr_rv rv_X))); trivial.
        rewrite Expectation_scale.
        unfold IsL2 in isl2.
        match_destr_in isl2.
        now match_destr_in isl2.
      + generalize (Rle_0_sqr x); intros.
        assert (0 = Rsqr x) by lra.
        symmetry in H1.
        apply Rsqr_eq_0 in H1.
        rewrite Expectation_ext with (rv2 := rvconst 0).
        * assert (0 <= 0) by lra.
          rewrite Expectation_pos_posRV with (prv := (@prvconst Ts 0 H2)).
          now rewrite Expectation_posRV_const.
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
    unfold L2RRV_eq, rv_almost_eq.
    constructor; red.
    - intros [x?].
      assert (eqq:event_equiv (fun x0 : Ts => x x0 = x x0) Ω)
        by firstorder.
      rewrite eqq.
      eauto with prob.
    - intros [x?] [y?] ps1; simpl in *.
      rewrite ps_proper; try eassumption.
      red; intros.
      split; congruence.
    - intros [x??] [y??] [z??] ps1 ps2.
      simpl in *.
      rewrite rv_almost_eq_alt_eq in ps1 by eauto with prob.
      rewrite rv_almost_eq_alt_eq in ps2 by eauto with prob.
      rewrite rv_almost_eq_alt_eq by eauto with prob.
      generalize (ps_union prts _ _ (sa_complement _ (Hsigma_borel_eq_pf _ x y _ _)) (sa_complement _ (Hsigma_borel_eq_pf _ y z _ _)))
      ; intros HH.
      unfold event_complement in HH.
      rewrite ps1,ps2 in HH.
      field_simplify in HH.

      assert (HH2 : ps_P
                      (event_inter (event_complement (fun x0 : Ts => x x0 = y x0))
                                   (event_complement (fun x : Ts => y x = z x))) = 0).
      {
        assert (HH3:ps_P
                      (event_union (event_complement (fun x0 : Ts => x x0 = y x0))
                                   (event_complement (fun x : Ts => y x = z x))) 
                    +
                    ps_P
                      (event_inter (event_complement (fun x0 : Ts => x x0 = y x0))
                                   (event_complement (fun x : Ts => y x = z x))) = 0)
          by (unfold event_complement; lra).
        rewrite Rplus_comm in HH3.
        apply Rplus_eq_0_l in HH3; trivial
        ; apply ps_pos
        ; eauto 6 with prob.
      }
      unfold event_complement in HH2.
      rewrite HH2, Ropp_0 in HH.
      unfold event_union in HH2.

      assert (ele:event_sub
                    (event_complement (fun x0 : Ts => x x0 = z x0))
                    (event_union (event_complement (fun x1 : Ts => x x1 = y x1))
                                 (event_complement (fun x : Ts => y x = z x)))).
      {
        unfold event_complement.
        red; intros.
        apply not_and_or.
        intros [??].
        congruence.
      }

      apply (@ps_sub _ _ prts) in ele; trivial.
      * unfold event_complement in ele.
        rewrite HH in ele.
        apply Rle_antisym; trivial.
        apply ps_pos; trivial.
        apply sa_complement.
        eauto with prob.
      * eauto with prob.
      * apply sa_union; eauto with prob.
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

  Definition L2RRVinner (x y:L2RRV) : R
    :=  match (Expectation (rvmult x y)) with
        | Some (Finite z) => z
        | _ => 0
        end.

  Global Instance L2RRV_inner_proper : Proper (L2RRV_eq ==> L2RRV_eq ==> eq) L2RRVinner.
  Proof.
    unfold Proper, respectful, L2RRV_eq.

    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold L2RRVinner.
  Admitted.

  Ltac L2RRV_simpl
    := repeat match goal with
              | [H : L2RRV |- _ ] => destruct H as [???]
              end
       ; unfold L2RRVplus, L2RRVminus, L2RRVopp, L2RRVscale
       ; simpl.

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
     L2RRV_eq (L2RRVscale x (L2RRVscale y u)) (L2RRVscale (mult x y) u).
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
    now rewrite (Expectation_ext _ _ (rvmult_comm x y)).
  Qed.
  
  Lemma L2RRV_inner_pos (x : L2RRV) : 0 <= L2RRVinner x x.
  Proof.
    unfold L2RRVinner.
  Admitted.
  
  Lemma L2RRV_inner_zero_inv (x:L2RRV) : L2RRVinner x x = 0 ->
                                         L2RRV_eq x (L2RRVconst 0).
  Proof.
    unfold L2RRVinner.
  Admitted.
  
  Lemma L2RRV_inner_scal (x y : L2RRV) (l : R) :
    L2RRVinner (L2RRVscale l x) y = l * L2RRVinner x y.
  Proof.
    unfold L2RRVinner, L2RRVscale; simpl.
  Admitted.

  Lemma L2RRV_inner_plus (x y z : L2RRV) :
    L2RRVinner (L2RRVplus x y) z = L2RRVinner x z + L2RRVinner y z.
  Proof.
    unfold L2RRVinner, L2RRVplus; simpl.
    
    
  Admitted.


  
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
  

End L2.
