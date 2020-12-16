Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Classical.
Require Import FunctionalExtensionality.

Require Import hilbert.

Require Import ProbSpace.
Require Import BorelSigmaAlgebra.
Require Import RandomVariable.
Require Import quotient_space.
Require Import AlmostEqual.

Set Bullet Behavior "Strict Subproofs".

Section L2.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Definition RRV : Type := {rv_X:Ts->R | RandomVariable prts borel_sa rv_X}.

  Program Definition RRV_eq (rv1 rv2:RRV) := rv_almost_eq prts rv1 rv2.

  Local Hint Resolve Hsigma_borel_eq_pf : prob.

  Global Instance RRV_eq_equiv : Equivalence RRV_eq.
  Proof.
    unfold RRV_eq, rv_almost_eq.
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
    - intros [x?] [y?] [z?] ps1 ps2.
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

  Program Definition RRVconst (x:R) : RRV
    := (const x).
  Next Obligation.
    apply rvconst.
  Qed.

  Definition RRVzero : RRV := RRVconst 0.

  Program Definition RRVplus (rv1 rv2:RRV) : RRV
    := rvplus rv1 rv2.
  Next Obligation.
    destruct rv1.
    destruct rv2.
    now apply rvplus_rv.
  Qed.

  Global Instance RRV_plus_proper : Proper (RRV_eq ==> RRV_eq ==> RRV_eq) RRVplus.
  Proof.
    unfold Proper, respectful, RRV_eq.
    intros [x1?] [x2?] eqqx [y1?] [y2?] eqqy.
    simpl in *.
    unfold rv_almost_eq in *.
  Admitted.

  Program Definition RRVscale (x:R) (rv:RRV) : RRV
    := rvscale x rv.
  Next Obligation.
    destruct rv.
    now apply rvscale_rv.
  Qed.

  Global Instance RRV_scale_proper : Proper (eq ==> RRV_eq ==> RRV_eq) RRVscale.
  Proof.
    unfold Proper, respectful, RRV_eq.
    intros ? x ? [x1?] [x2?] eqqx.
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

  Program Definition RRVopp (rv:RRV) : RRV
    := rvopp rv.
  Next Obligation.
    destruct rv.
    now apply rvopp_rv.
  Qed.

  Global Instance RRV_opp_proper : Proper (RRV_eq ==> RRV_eq) RRVopp.
  Proof.
    unfold Proper, respectful.
    intros x y eqq.
    generalize (RRV_scale_proper (-1) _ (eq_refl _) _ _ eqq)
    ; intros HH.
    destruct x as [x?]
    ; destruct y as [y?].
    apply HH.
  Qed.
  
  Program Definition RRVminus (rv1 rv2:RRV) : RRV
    := rvminus rv1 rv2.
  Next Obligation.
    destruct rv1.
    destruct rv2.
    now apply rvminus_rv.
  Qed.

  Global Instance RRV_minus_proper : Proper (RRV_eq ==> RRV_eq ==> RRV_eq) RRVminus.
  Proof.
    unfold Proper, respectful, RRV_eq.

    intros x1 x2 eqq1 y1 y2 eqq2.
    
    generalize (RRV_plus_proper _ _ eqq1 _ _ (RRV_opp_proper _ _ eqq2)) 
    ; intros HH.
    destruct x1 as [??]; destruct x2 as [??]
    ; destruct y1 as [??]; destruct y2 as [??].
    apply HH.
  Qed.

  Ltac RRV_simpl
    := repeat match goal with
              | [H : RRV |- _ ] => destruct H
              end
       ; unfold RRVplus, RRVminus, RRVopp, RRVscale
       ; simpl.

  Lemma RRV_plus_comm x y : RRV_eq (RRVplus x y) (RRVplus y x).
  Proof.
    red; intros.
    RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus; lra.
  Qed.
  
  Lemma RRV_plus_assoc (x y z : RRV) : RRV_eq (RRVplus x (RRVplus y z)) (RRVplus (RRVplus x y) z).
  Proof.
    red; intros.
    RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus.
    lra.
  Qed.

  Lemma RRV_plus_zero (x : RRV) : RRV_eq (RRVplus x (RRVconst 0)) x.
  Proof.
    red; intros.
    RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus, const.
    lra.
  Qed.

  Lemma RRV_plus_inv (x: RRV) : RRV_eq (RRVplus x (RRVopp x)) (RRVconst 0).
  Proof.
    red; intros.
    RRV_simpl.
    apply rv_almost_eq_eq; intros ?.
    unfold rvplus, rvopp, rvscale, const.
    lra.
  Qed.
  
  Definition RRVq : Type := quot RRV_eq.

  Definition RRVq_const (x:R) : RRVq := Quot _ (RRVconst x).

  Lemma RRVq_constE x : RRVq_const x = Quot _ (RRVconst x).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite RRVq_constE : quot.

  Definition RRVq_zero : RRVq := RRVq_const 0.

  Lemma RRVq_zeroE : RRVq_zero = RRVq_const 0.
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite RRVq_zeroE : quot.
  
  Definition RRVq_opp  : RRVq -> RRVq
    := quot_lift _ RRVopp.

  Lemma RRVq_oppE x : RRVq_opp (Quot _ x)  = Quot _ (RRVopp x).
  Proof.
    apply quot_liftE.
  Qed.

  Hint Rewrite RRVq_oppE : quot.

  Definition RRVq_plus  : RRVq -> RRVq -> RRVq
    := quot_lift2 _ RRVplus.
  
  Lemma RRVq_plusE x y : RRVq_plus (Quot _ x) (Quot _ y) = Quot _ (RRVplus x y).
  Proof.
    apply quot_lift2E.
  Qed.

  Hint Rewrite RRVq_plusE : quot.

  Definition RRVq_minus  : RRVq -> RRVq -> RRVq
    := quot_lift2 _ RRVminus.

  Lemma RRVq_minusE x y : RRVq_minus (Quot _ x) (Quot _ y) = Quot _ (RRVminus x y).
  Proof.
    apply quot_lift2E.
  Qed.

  Hint Rewrite RRVq_minusE : quot.


  Ltac RRVq_simpl
    := repeat match goal with
       | [H: RRVq |- _ ] =>
         let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
              end
       ; try autorewrite with quot
       ; try apply (@eq_Quot _ _ RRV_eq_equiv).

  Lemma RRVq_plus_comm x y : RRVq_plus x y = RRVq_plus y x.
  Proof.
    RRVq_simpl.
    apply RRV_plus_comm.
  Qed.
         
  Lemma RRVq_plus_assoc (x y z : RRVq) : RRVq_plus x (RRVq_plus y z) = RRVq_plus (RRVq_plus x y) z.
  Proof.
    RRVq_simpl.
    apply RRV_plus_assoc.
  Qed.


  Lemma RRVq_plus_zero (x : RRVq) : RRVq_plus x RRVq_zero = x.
  Proof.
    RRVq_simpl.
    apply RRV_plus_zero.
  Qed.

  Lemma RRVq_plus_inv (x: RRVq) : RRVq_plus x (RRVq_opp x) = RRVq_zero.
  Proof.
    RRVq_simpl.
    apply RRV_plus_inv.
  Qed.
    
  Program Definition RRVq_AbelianGroup_mixin : AbelianGroup.mixin_of RRVq
    := AbelianGroup.Mixin RRVq RRVq_plus RRVq_opp RRVq_zero
                          RRVq_plus_comm RRVq_plus_assoc
                          RRVq_plus_zero RRVq_plus_inv.

  Canonical RRVq_AbelianGroup :=
    AbelianGroup.Pack RRVq RRVq_AbelianGroup_mixin RRVq.

End L2.
