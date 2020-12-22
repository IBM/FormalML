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
Require Export RandomVariableFinite.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section L1.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).


  Definition IsL1 (rv_X:Ts->R)
    := IsFiniteExpectation prts (rvabs rv_X).

  Existing Class IsL1.

  Typeclasses Transparent IsL1.
  
  Global Instance IsL1_Finite (rv_X:Ts->R)
         {rrv:RandomVariable prts borel_sa rv_X}
         {l1:IsL1 rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    red.
    apply Expectation_abs_then_finite; trivial.
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
        {rv:RandomVariable prts borel_sa rv_X}
        {isfe:IsFiniteExpectation prts rv_X} :
    is_finite (Expectation_posRV (neg_fun_part rv_X)).
  Proof.
    red in isfe.
    unfold Expectation in isfe.
    destruct (Expectation_posRV (fun x : Ts => pos_fun_part rv_X x)).
    destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x)).     
    now unfold is_finite.
    simpl in isfe; tauto.
    simpl in isfe; tauto.     
    destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x));
      simpl in isfe; tauto.
    destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x));
      simpl in isfe; tauto.
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
  
  Global Instance IsL1_plus 
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2} 
         {isl11:IsL1 rv_X1}
         {isl12:IsL1 rv_X2} :
    IsL1 (rvplus rv_X1 rv_X2).
  Proof.
    unfold IsL1 in *.
    apply (IsFiniteExpectation_bounded prts (const 0) _ (rvplus (rvabs rv_X1) (rvabs rv_X2))).
    - intros a; unfold const, rvabs.
      apply Rabs_pos.
    - intros x.
      unfold rvabs, rvplus.
      apply Rabs_triang.
  Qed.

  Global Instance IsL1_proper
    : Proper (rv_eq ==> iff) IsL1.
  Proof.
    intros x y eqq.
    unfold IsL1.
    now rewrite eqq.
  Qed.

  Lemma rv_abs_scale_eq (c:R) (rv_X:Ts->R) :
    rv_eq (rvabs (rvscale c rv_X)) (rvscale (Rabs c) (rvabs rv_X)).
  Proof.
    intros a.
    unfold rvabs, rvscale.
    apply Rabs_mult.
  Qed.
  
  Lemma rv_abs_const_eq (c:R)  :
    rv_eq (Ts:=Ts) (rvabs (const c)) (const (Rabs c)).
  Proof.
    intros a.
    reflexivity.
  Qed.

  Global Instance IsL1_scale (c:R) (rv_X:Ts->R)
         {isl1:IsL1 rv_X} :
    IsL1 (rvscale c rv_X).
  Proof.
    unfold IsL1 in *.
    rewrite rv_abs_scale_eq.
    typeclasses eauto.
  Qed.

  Lemma IsL1_scale_inv c rv_X 
        {isl1:IsL1 (rvscale c rv_X)} :
    c <> 0 ->
    IsL1 rv_X.
  Proof.
    intros.
    unfold IsL1 in *.
    rewrite rv_abs_scale_eq in isl1.
    eapply IsFiniteExpectation_scale_inv; try eassumption.
    now apply Rabs_no_R0.
  Qed.
  
  Global Instance IsL1_opp (rv_X:Ts->R)
         {isl1:IsL1 rv_X} :
    IsL1 (rvopp rv_X).
  Proof.
    unfold IsL1 in *.
    now apply IsL1_scale.
  Qed.

  Global Instance IsL1_const c : IsL1 (const c).
  Proof.
    red.
    rewrite rv_abs_const_eq.
    typeclasses eauto.
  Qed.

  Global Instance IsL1_minus
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2} 
         {isl11:IsL1 rv_X1}
         {isl12:IsL1 rv_X2} :
    IsL1 (rvminus rv_X1 rv_X2).
  Proof.
    unfold rvminus.
    typeclasses eauto.
  Qed.

  Lemma rv_abs_abs (rv_X:Ts->R) :
    rv_eq (rvabs (rvabs rv_X)) (rvabs rv_X).
  Proof.
    intros a.
    unfold rvabs.
    now rewrite Rabs_Rabsolu.
  Qed.
  
  Global Instance IsL1_abs
         (rv_X : Ts -> R)
         {isl1:IsL1 rv_X} :
    IsL1 (rvabs rv_X).
  Proof.
    unfold IsL1.
    rewrite rv_abs_abs.
    apply isl1.
  Qed.

  Lemma IsL1_bounded rv_X1 rv_X2
        {isl1:IsFiniteExpectation prts rv_X2}
    :
      RealRandomVariable_le (rvabs rv_X1) rv_X2 ->
      IsL1 rv_X1.
  Proof.
    unfold IsL1 in *.
    intros.
    eapply (IsFiniteExpectation_bounded prts (const 0) _ rv_X2); trivial.
    intros a.
    unfold const, rvabs.
    apply Rabs_pos.
  Qed.      
  
  Global Instance IsL1_max
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2}
         {isl11:IsL1 rv_X1}
         {isl12:IsL1 rv_X2} :
    IsL1 (rvmax rv_X1 rv_X2).
  Proof.
    unfold IsL1 in *.
    eapply (IsL1_bounded _ (rvplus (rvabs rv_X1)  (rvabs rv_X2))).
    intros a.
    unfold rvabs, rvplus, rvmax.
    unfold Rmax, Rabs.
    repeat match_destr; lra.
  Qed.

  Global Instance IsL1_min
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable prts borel_sa rv_X1}
         {rv2 : RandomVariable prts borel_sa rv_X2}
         {isl11:IsL1 rv_X1}
         {isl12:IsL1 rv_X2} :
    IsL1 (rvmin rv_X1 rv_X2).
  Proof.
    unfold IsL1 in *.
    eapply (IsL1_bounded _ (rvplus (rvabs rv_X1)  (rvabs rv_X2))).
    intros a.
    unfold rvabs, rvplus, rvmin.
    unfold Rmin, Rabs.
    repeat match_destr; lra.
  Qed.
  
End L1.

