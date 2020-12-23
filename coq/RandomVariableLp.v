Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import FunctionalExtensionality.

Require Import hilbert.

Require Export RandomVariableFinite.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section Lp.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

(* generalize this to real p using rvpower? *)
  Definition IsLp (n:nat) (rv_X:Ts->R)
    := IsFiniteExpectation prts (rvpow (rvabs rv_X) n).

  Existing Class IsLp.
  Typeclasses Transparent IsLp.

    Global Instance IsL1_proper
    : Proper (eq ==> rv_eq ==> iff) IsLp.
  Proof.
    intros ?? eqq1 x y eqq2.
    unfold IsLp.
    now rewrite eqq1, eqq2.
  Qed.

  (* Note that IsLp 0 always holds, so it says that we are not making any assumptions *)
  Global Instance IsL0_True (rv_X:Ts->R) : IsLp 0 rv_X.
  Proof.
    red.
    assert (eqq:rv_eq (rvpow rv_X 0) (const 1)).
    { 
      intros x.
      reflexivity.
    }
    rewrite eqq.
    typeclasses eauto.
  Qed.

  Lemma rvpow1 (x:Ts->R) : rv_eq (rvpow x 1) x.
  Proof.
    intros a.
    unfold rvpow; simpl.
    lra.
  Qed.

  Lemma rvpowS (x:Ts->R) n : rv_eq (rvpow x (S n)) (rvmult x (rvpow x n)).
  Proof.
    intros a.
    reflexivity.
  Qed.

  Global Instance IsL1_Finite (rv_X:Ts->R)
         {rrv:RandomVariable dom borel_sa rv_X}
         {lp:IsLp 1 rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    red.
    red in lp.
    apply Expectation_abs_then_finite; trivial.
    now rewrite rvpow1 in lp.
  Qed.

  Global Instance IsL1_abs_Finite (rv_X:Ts->R)
         {lp:IsLp 1 rv_X} : IsFiniteExpectation prts (rvabs rv_X).
  Proof.
    red.
    red in lp.
    now rewrite rvpow1 in lp.
  Qed.

  Lemma Finite_abs_IsL1 (rv_X:Ts->R)
         {isfe:IsFiniteExpectation prts (rvabs rv_X)} :
    IsLp 1 rv_X.
  Proof.
    red.
    now rewrite rvpow1.
  Qed.

  Lemma le_pow_mult_plus a n :
    0 <= a ->
    a ^ n <= a * a^n + 1.
  Proof.
    intros.
    destruct n.
    - simpl; lra.
    - destruct (Rtotal_order a 1) as [|[|]].
      + eapply Rle_trans.
        * left.
          apply Rlt_R1_pow.
          -- lra.
          -- lia.
        * assert (0 <= a*a^(S n)); try lra.
          apply Rmult_le_pos; trivial.
          now apply pow_le.
      + subst.
        rewrite pow1.
        lra.
      + rewrite Rmult_comm.
        rewrite <- (Rinv_r (a^(S n))).
        * rewrite <- Rmult_plus_distr_l.
          replace  (a ^ (S n)) with ( a ^ (S n) * (1 + 0)) at 1 by lra.
          apply Rmult_le_compat_l; trivial.
          -- now apply pow_le.
          -- apply Rplus_le_compat.
             ++ lra.
             ++ left.
                apply Rinv_pos.
                apply pow_lt.
                lra.
        * apply pow_nzero.
          lra.
  Qed.
  
  (* move it to FunctionsToReal *)
  Lemma rvabs_pow_bound n (rv_X : Ts -> R) :
    rv_le (rvpow (rvabs rv_X) n) (rvplus (rvmult (rvabs rv_X) (rvpow (rvabs rv_X) n)) (const 1)).
  Proof.
    intros a.
    unfold rvpow, rvabs, rvmult, rvplus, const.
    apply le_pow_mult_plus.
    apply Rabs_pos.
  Qed.
  
  Global Instance IsLp_down n (rv_X:Ts->R)
         {rrv:RandomVariable dom borel_sa rv_X}
         {lp:IsLp (S n) rv_X} : IsLp n rv_X.
  Proof.
    red in lp.
    rewrite rvpowS in lp.
    red.
    apply (@IsFiniteExpectation_bounded _ _ _ (const 0) _
                                        (rvplus (rvmult (rvabs rv_X) (rvpow (rvabs rv_X) n)) (const 1)) _ _).
    - intros a.
      unfold const, rvpow.
      apply pow_le.
      apply Rabs_pos.
    - apply rvabs_pow_bound.
  Qed.      

  Lemma IsLp_down_le m n (rv_X:Ts->R)
           {rrv:RandomVariable dom borel_sa rv_X}
           (pfle:(n <= m)%nat)
         {lp:IsLp m rv_X} : IsLp n rv_X.
  Proof.
    eapply (Nat.left_induction (fun x => IsLp x rv_X)); try eassumption.
    - intros ???; subst.
      tauto.
    - intros.
      now apply IsLp_down.
  Qed.

  Lemma IsLp_Finite n (rv_X:Ts->R)
         {rrv:RandomVariable dom borel_sa rv_X}
         (nzero:(1 <= n)%nat)
         {lp:IsLp n rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    apply IsL1_Finite; trivial.
    now apply (IsLp_down_le n 1).
  Qed.

  Global Instance IsLSp_Finite n (rv_X:Ts->R)
         {rrv:RandomVariable dom borel_sa rv_X}
         {lp:IsLp (S n) rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    eapply IsLp_Finite; try eassumption.
    lia.
  Qed.

  Lemma IsLSp_abs_Finite n (rv_X:Ts->R)
         {rrv:RandomVariable dom borel_sa rv_X}
         {lp:IsLp (S n) rv_X} : IsFiniteExpectation prts (rvabs rv_X).
  Proof.
    apply IsL1_abs_Finite; trivial.
    apply (IsLp_down_le (S n) 1); trivial.
    lia.
  Qed.


  Lemma IsLp_bounded n rv_X1 rv_X2
        {islp:IsFiniteExpectation prts rv_X2}
    :
      rv_le (rvpow (rvabs rv_X1) n) rv_X2 ->
      IsLp n rv_X1.
  Proof.
    unfold IsLp in *.
    intros.
    eapply (IsFiniteExpectation_bounded prts (const 0) _ rv_X2); trivial.
    intros a.
    unfold const, rvabs, rvpow.
    apply pow_le.
    apply Rabs_pos.
  Qed.      

  Lemma Expectation_abs_neg_part_finite (rv_X : Ts -> R)
        {rv:RandomVariable dom borel_sa rv_X} :
    is_finite (Expectation_posRV (rvabs rv_X)) ->
    is_finite (Expectation_posRV (neg_fun_part rv_X)).
  Proof.
    apply Finite_Expectation_posRV_le.
    apply neg_fun_part_le.
  Qed.
  
  Lemma Expectation_neg_part_finite (rv_X : Ts -> R)
        {rv:RandomVariable dom borel_sa rv_X}
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

  Global Instance IsLp_plus p
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
         {isl11:IsLp p rv_X1}
         {isl12:IsLp p rv_X2} :
    IsLp p (rvplus rv_X1 rv_X2).
  Proof.
    destruct p; simpl.
    - apply IsL0_True.
    - (* HERE *)
  Admitted.
  

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
  
  Lemma rvpow_mult_distr (x y:Ts->R) n :
    rv_eq (rvpow (rvmult x y) n) (rvmult (rvpow x n) (rvpow y n)).
  Proof.
    intros a.
    unfold rvpow, rvmult.
    apply Rpow_mult_distr.
  Qed.

  Lemma rvpow_scale c (X:Ts->R) n :
    rv_eq (rvpow (rvscale c X) n) (rvscale (pow c n) (rvpow X n)).
  Proof.
    intros x.
    unfold rvpow, rvscale.
    apply Rpow_mult_distr.
  Qed.

  Lemma rvpow_const c n :
    rv_eq (Ts:=Ts) (rvpow (const c) n) (const (pow c n)).
  Proof.
    intros x.
    reflexivity.
  Qed.

  Global Instance IsLp_scale p (c:R) (rv_X:Ts->R)
         {islp:IsLp p rv_X} :
    IsLp p (rvscale c rv_X).
  Proof.
    unfold IsLp in *.
    rewrite rv_abs_scale_eq.
    rewrite rvpow_scale.
    typeclasses eauto.
  Qed.

  Lemma IsLp_scale_inv p c rv_X 
        {islp:IsLp p (rvscale c rv_X)} :
    c <> 0 ->
    IsLp p rv_X.
  Proof.
    intros.
    unfold IsLp in *.
    rewrite rv_abs_scale_eq, rvpow_scale in islp.
    eapply IsFiniteExpectation_scale_inv; try eassumption.
    apply pow_nzero.
    now apply Rabs_no_R0.
  Qed.
  
  Global Instance IsLp_opp p (rv_X:Ts->R)
         {islp:IsLp p rv_X} :
    IsLp p (rvopp rv_X).
  Proof.
    now apply IsLp_scale.
  Qed.

  Global Instance IsLp_const p c : IsLp p (const c).
  Proof.
    red.
    rewrite rv_abs_const_eq, rvpow_const.
    typeclasses eauto.
  Qed.

  Global Instance IsLp_minus p
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
         {islp1:IsLp p rv_X1}
         {islp2:IsLp p rv_X2} :
    IsLp p (rvminus rv_X1 rv_X2).
  Proof.
    unfold rvminus.
    apply IsLp_plus; 
    typeclasses eauto.
  Qed.

  Lemma rv_abs_abs (rv_X:Ts->R) :
    rv_eq (rvabs (rvabs rv_X)) (rvabs rv_X).
  Proof.
    intros a.
    unfold rvabs.
    now rewrite Rabs_Rabsolu.
  Qed.
  
  Global Instance IsLp_abs p
         (rv_X : Ts -> R)
         {islp:IsLp p rv_X} :
    IsLp p (rvabs rv_X).
  Proof.
    unfold IsLp.
    rewrite rv_abs_abs.
    apply islp.
  Qed.

  Lemma rvpowabs_choice_le c (rv_X1 rv_X2 : Ts -> R) p :
    rv_le (rvpow (rvabs (rvchoice c rv_X1 rv_X2)) p)
          (rvplus (rvpow (rvabs rv_X1) p) (rvpow (rvabs rv_X2) p)).
  Proof.
    intros a.
    rv_unfold.
    repeat rewrite RPow_abs.
    match_destr.
    - assert (0 <= Rabs (rv_X2 a ^ p)) by apply Rabs_pos.
      lra.
    - assert (0 <= Rabs (rv_X1 a ^ p)) by apply Rabs_pos.
      lra.
  Qed.

  Global Instance IsLp_choice p
         c
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2}
         {islp1:IsLp p rv_X1}
         {islp2:IsLp p rv_X2} :
    IsLp p (rvchoice c rv_X1 rv_X2).
  Proof.
    unfold IsLp in *.
    eapply (IsLp_bounded _)
    ; try eapply rvpowabs_choice_le.
    apply IsFiniteExpectation_plus; eauto.
    - apply rvpow_rv.
      now apply rvabs_rv.
    - apply rvpow_rv.
      now apply rvabs_rv.
  Qed.
  
  Global Instance IsLp_max p
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2}
         {islp1:IsLp p rv_X1}
         {islp2:IsLp p rv_X2} :
    IsLp p (rvmax rv_X1 rv_X2).
  Proof.
    rewrite rvmax_choice.
    typeclasses eauto.
  Qed.

  Global Instance IsLp_min p
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2}
         {islp1:IsLp p rv_X1}
         {islp2:IsLp p rv_X2} :
    IsLp p (rvmin rv_X1 rv_X2).
  Proof.
    rewrite rvmin_choice.
    typeclasses eauto.
  Qed.
  
End Lp.

