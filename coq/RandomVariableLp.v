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

  Lemma IsL1_Finite (rv_X:Ts->R)
         {rrv:RandomVariable dom borel_sa rv_X}
         {lp:IsLp 1 rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    red.
    red in lp.
    apply Expectation_abs_then_finite; trivial.
    now rewrite rvpow1 in lp.
  Qed.

  Lemma IsL1_abs_Finite (rv_X:Ts->R)
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
        (rle:rv_le (rvpow (rvabs rv_X1) n) rv_X2)
        {islp:IsFiniteExpectation prts rv_X2}
    :
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

  Lemma pow_ineq p x y : 2*Rabs (x + y )^p <= (2*Rabs x)^p + (2*Rabs y)^p.
  Proof.
  Admitted.
    
   Lemma pow_ineq1 (p : nat) (x y : R) :
     0 <= x -> 0 <= y -> pow (x + y) p <= (pow 2 p) * ((pow x p) + (pow y p)).
   Proof.
     rewrite binomial.
     rewrite sum_f_R0_sum_f_R0'.
     generalize ( sum_f_R0'_le_f (fun i : nat => Binomial.C p i * x ^ i * y ^ (p - i))
                                 (fun i : nat => (pow x p + pow y p) * Binomial.C p i) (S p)); intros.
     cut_to H.
     - rewrite sum_f_R0'_mult_const in H.
       generalize (binomial 1 1 p); intros.
       replace (1+1) with (2) in H2 by lra.
       rewrite sum_f_R0_ext with (f2 := Binomial.C p) in H2.
       + rewrite sum_f_R0_sum_f_R0' in H2.
         rewrite <- H2 in H.
         now rewrite Rmult_comm in H.
       + intros.
         rewrite Rmult_assoc.
         do 2 rewrite pow1.
         lra.
     - intros.
       ring_simplify.
       rewrite <- Rmult_plus_distr_l.
       rewrite Rmult_assoc.
       apply Rmult_le_compat_l.
       * unfold Binomial.C.
         left; unfold Rdiv.
         apply Rmult_lt_0_compat.
         -- apply lt_0_INR; apply lt_O_fact.
         -- apply Rinv_0_lt_compat.
            apply Rmult_lt_0_compat; apply lt_0_INR; apply lt_O_fact.
       * destruct (Rle_dec y x).
         -- replace (p) with (i + (p-i))%nat at 2.
            ++ rewrite Rdef_pow_add.
               assert (x ^ i * y ^ (p - i) <= x ^ i * x ^ (p - i)); intros.
               ** apply Rmult_le_compat_l
                  ; [now apply pow_le | apply pow_maj_Rabs; rewrite Rabs_right; lra].
               ** assert (0 <= y^p); [now apply pow_le | lra].
            ++ lia.
     
         -- replace (p) with (i + (p-i))%nat at 3.
            ++ rewrite Rdef_pow_add.
               assert (x ^ i * y ^ (p - i) <= y ^ i * y ^ (p - i)); intros.
               ** apply Rmult_le_compat_r
                  ; [now apply pow_le | apply pow_maj_Rabs; rewrite Rabs_right; lra].
               ** assert (0 <= x^p); [now apply pow_le | lra].
            ++ lia.
   Qed.     
     
   Lemma pow_abs_ineq1 (p : nat) (x y : R) :
     pow (Rabs(x + y)) p <= (pow 2 p) * ((pow (Rabs x) p) + (pow (Rabs y) p)).
   Proof.
     apply Rle_trans with (r2 := pow (Rabs x + Rabs y) p).
     - apply pow_maj_Rabs.
       rewrite Rabs_Rabsolu.
       apply Rabs_triang.
     - apply pow_ineq1; apply Rabs_pos.
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
    
  Global Instance IsLp_plus p
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
         {islp1:IsLp p rv_X1}
         {islp2:IsLp p rv_X2} :
    IsLp p (rvplus rv_X1 rv_X2).
  Proof.
    destruct p; simpl.
    - apply IsL0_True.
    - apply (IsLp_bounded (S p) _ (rvscale (/2) (rvplus (rvpow (rvscale 2 (rvabs rv_X1)) (S p)) (rvpow (rvscale 2 (rvabs rv_X2)) (S p))))).
      + intros x.
        rv_unfold.
        apply Rmult_le_reg_l with (r:=2); try lra.
        rewrite <- Rmult_assoc.
        field_simplify.
        apply pow_ineq.
      + apply IsFiniteExpectation_scale.
        apply IsFiniteExpectation_plus.
        * typeclasses eauto.
        * typeclasses eauto.
        * rewrite rvpow_scale.
          apply IsFiniteExpectation_scale.
          apply islp1.
        * rewrite rvpow_scale.
          apply IsFiniteExpectation_scale.
          apply islp2.
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

  Section packed.

    Context {p:nat}.
    
    Record LpRRV : Type
      := LpRRV_of {
             LpRRV_rv_X :> Ts -> R
             ; LpRRV_rv :> RandomVariable dom borel_sa LpRRV_rv_X
             ; LpRRV_lp :> IsLp p LpRRV_rv_X
           }.

    Global Existing Instance LpRRV_rv.
    Global Existing Instance LpRRV_lp.

    Definition pack_LpRRV (rv_X:Ts -> R) {rv:RandomVariable dom borel_sa rv_X} {lp:IsLp p rv_X}
      := LpRRV_of rv_X rv lp.
    
    Definition LpRRV_eq (rv1 rv2:LpRRV)
      := rv_almost_eq prts rv1 rv2.

    Local Hint Resolve Hsigma_borel_eq_pf : prob.

    Global Instance LpRRV_eq_equiv : Equivalence LpRRV_eq.
    Proof.
      unfold LpRRV_eq.
      constructor.
      - intros [x?].
        now apply rv_almost_eq_rv_refl.
      - intros [x?] [y?] ps1; simpl in *.
        now apply rv_almost_eq_rv_sym.
      - intros [x??] [y??] [z??] ps1 ps2.
        simpl in *.
        now apply rv_almost_eq_rv_trans with (y0:=y).
    Qed.

    
    Definition LpRRVconst (x:R) : LpRRV
      := pack_LpRRV (const x).

    Definition LpRRVzero : LpRRV := LpRRVconst 0.

    Definition LpRRVplus (rv1 rv2:LpRRV) : LpRRV
      := pack_LpRRV (rvplus rv1  rv2) (lp:=IsLp_plus _ _ _).

    Global Instance LpRRV_plus_proper : Proper (LpRRV_eq ==> LpRRV_eq ==> LpRRV_eq) LpRRVplus.
    Proof.
      unfold Proper, respectful, LpRRV_eq.
      intros [x1??] [x2??] eqqx [y1??] [y2??] eqqy.
      simpl in *.
      now apply rv_almost_eq_plus_proper.
    Qed.
    
    Program Definition LpRRVscale (x:R) (rv:LpRRV) : LpRRV
      := pack_LpRRV (rvscale x rv).

    Global Instance LpRRV_scale_proper : Proper (eq ==> LpRRV_eq ==> LpRRV_eq) LpRRVscale.
    Proof.
      unfold Proper, respectful, LpRRV_eq.
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

    Program Definition LpRRVopp (rv:LpRRV) : LpRRV
      := pack_LpRRV (rvopp rv).
    
    Global Instance LpRRV_opp_proper : Proper (LpRRV_eq ==> LpRRV_eq) LpRRVopp.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      generalize (LpRRV_scale_proper (-1) _ (eq_refl _) _ _ eqq)
      ; intros HH.
      destruct x as [x?]
      ; destruct y as [y?].
      apply HH.
    Qed.
    
    Definition LpRRVminus (rv1 rv2:LpRRV) : LpRRV
      := pack_LpRRV (rvminus rv1 rv2)  (lp:=IsLp_minus _ _ _).

    Lemma LpRRVminus_plus (rv1 rv2:LpRRV) :
      LpRRV_eq 
        (LpRRVminus rv1 rv2) (LpRRVplus rv1 (LpRRVopp rv2)).
    Proof.
      apply rv_almost_eq_eq.
      reflexivity.
    Qed.

    Lemma LpRRVopp_scale (rv:LpRRV) :
      LpRRV_eq 
        (LpRRVopp rv) (LpRRVscale (-1) rv).
    Proof.
      red.
      apply rv_almost_eq_eq.
      reflexivity.
    Qed.
    
    Global Instance LpRRV_minus_proper : Proper (LpRRV_eq ==> LpRRV_eq ==> LpRRV_eq) LpRRVminus.
    Proof.
      unfold Proper, respectful, LpRRV_eq.

      intros x1 x2 eqq1 y1 y2 eqq2.
      
      generalize (LpRRV_plus_proper _ _ eqq1 _ _ (LpRRV_opp_proper _ _ eqq2)) 
      ; intros HH.
      destruct x1 as [???]; destruct x2 as [???]
      ; destruct y1 as [???]; destruct y2 as [???].
      apply HH.
    Qed.

    Ltac LpRRV_simpl
      := repeat match goal with
                | [H : LpRRV |- _ ] => destruct H as [???]
                end
         ; unfold LpRRVplus, LpRRVminus, LpRRVopp, LpRRVscale
         ; simpl.

    
    Lemma LpRRV_plus_comm x y : LpRRV_eq (LpRRVplus x y) (LpRRVplus y x).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus; lra.
    Qed.
    
    Lemma LpRRV_plus_assoc (x y z : LpRRV) : LpRRV_eq (LpRRVplus x (LpRRVplus y z)) (LpRRVplus (LpRRVplus x y) z).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus.
      lra.
    Qed.

    Lemma LpRRV_plus_zero (x : LpRRV) : LpRRV_eq (LpRRVplus x (LpRRVconst 0)) x.
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, const.
      lra.
    Qed.

    Lemma LpRRV_plus_inv (x: LpRRV) : LpRRV_eq (LpRRVplus x (LpRRVopp x)) (LpRRVconst 0).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const.
      lra.
    Qed.

    Lemma LpRRV_scale_scale (x y : R) (u : LpRRV) :
      LpRRV_eq (LpRRVscale x (LpRRVscale y u)) (LpRRVscale (x * y) u).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    Lemma LpRRV_scale1 (u : LpRRV) :
      LpRRV_eq (LpRRVscale one u) u.
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult, one; simpl.
      lra.
    Qed.
    
    Lemma LpRRV_scale_plus_l (x : R) (u v : LpRRV) :
      LpRRV_eq (LpRRVscale x (LpRRVplus u v)) (LpRRVplus (LpRRVscale x u) (LpRRVscale x v)).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.
    
    Lemma LpRRV_scale_plus_r (x y : R) (u : LpRRV) :
      LpRRV_eq (LpRRVscale (x + y) u) (LpRRVplus (LpRRVscale x u) (LpRRVscale y u)).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    Section quot.

      Definition LpRRVq : Type := quot LpRRV_eq.

      Definition LpRRVq_const (x:R) : LpRRVq := Quot _ (LpRRVconst x).

      Lemma LpRRVq_constE x : LpRRVq_const x = Quot _ (LpRRVconst x).
      Proof.
        reflexivity.
      Qed.

      Hint Rewrite LpRRVq_constE : quot.

      Definition LpRRVq_zero : LpRRVq := LpRRVq_const 0.

      Lemma LpRRVq_zeroE : LpRRVq_zero = LpRRVq_const 0.
      Proof.
        reflexivity.
      Qed.

      Hint Rewrite LpRRVq_zeroE : quot.

      Definition LpRRVq_scale (x:R) : LpRRVq -> LpRRVq
        := quot_lift _ (LpRRVscale x).

      Lemma LpRRVq_scaleE x y : LpRRVq_scale x (Quot _ y)  = Quot _ (LpRRVscale x y).
      Proof.
        apply quot_liftE.
      Qed.

      Hint Rewrite LpRRVq_scaleE : quot.
      
      Definition LpRRVq_opp  : LpRRVq -> LpRRVq
        := quot_lift _ LpRRVopp.

      Lemma LpRRVq_oppE x : LpRRVq_opp (Quot _ x)  = Quot _ (LpRRVopp x).
      Proof.
        apply quot_liftE.
      Qed.

      Hint Rewrite LpRRVq_oppE : quot.

      Definition LpRRVq_plus  : LpRRVq -> LpRRVq -> LpRRVq
        := quot_lift2 _ LpRRVplus.
      
      Lemma LpRRVq_plusE x y : LpRRVq_plus (Quot _ x) (Quot _ y) = Quot _ (LpRRVplus x y).
      Proof.
        apply quot_lift2E.
      Qed.

      Hint Rewrite LpRRVq_plusE : quot.

      Definition LpRRVq_minus  : LpRRVq -> LpRRVq -> LpRRVq
        := quot_lift2 _ LpRRVminus.

      Lemma LpRRVq_minusE x y : LpRRVq_minus (Quot _ x) (Quot _ y) = Quot _ (LpRRVminus x y).
      Proof.
        apply quot_lift2E.
      Qed.

      Hint Rewrite LpRRVq_minusE : quot.

      Ltac LpRRVq_simpl
        := repeat match goal with
                  | [H: LpRRVq |- _ ] =>
                    let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
                  end
           ; try autorewrite with quot
           ; try apply (@eq_Quot _ _ LpRRV_eq_equiv).

      Lemma LpRRVq_minus_plus (rv1 rv2:LpRRVq) :
        LpRRVq_minus rv1 rv2 = LpRRVq_plus rv1 (LpRRVq_opp rv2).
      Proof.
        LpRRVq_simpl.
        apply LpRRVminus_plus.
      Qed.

      Lemma LpRRVq_opp_scale (rv:LpRRVq) :
        LpRRVq_opp rv =LpRRVq_scale (-1) rv.
      Proof.
        LpRRVq_simpl.
        apply LpRRVopp_scale.
      Qed.
      
      Lemma LpRRVq_plus_comm x y : LpRRVq_plus x y = LpRRVq_plus y x.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_plus_comm.
      Qed.
      
      Lemma LpRRVq_plus_assoc (x y z : LpRRVq) : LpRRVq_plus x (LpRRVq_plus y z) = LpRRVq_plus (LpRRVq_plus x y) z.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_plus_assoc.
      Qed.


      Lemma LpRRVq_plus_zero (x : LpRRVq) : LpRRVq_plus x LpRRVq_zero = x.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_plus_zero.
      Qed.

      Lemma LpRRVq_plus_inv (x: LpRRVq) : LpRRVq_plus x (LpRRVq_opp x) = LpRRVq_zero.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_plus_inv.
      Qed.
      
      Definition LpRRVq_AbelianGroup_mixin : AbelianGroup.mixin_of LpRRVq
        := AbelianGroup.Mixin LpRRVq LpRRVq_plus LpRRVq_opp LpRRVq_zero
                              LpRRVq_plus_comm LpRRVq_plus_assoc
                              LpRRVq_plus_zero LpRRVq_plus_inv.

      Canonical LpRRVq_AbelianGroup :=
        AbelianGroup.Pack LpRRVq LpRRVq_AbelianGroup_mixin LpRRVq.


      Ltac LpRRVq_simpl ::=
        repeat match goal with
               | [H: LpRRVq |- _ ] =>
                 let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
               | [H: AbelianGroup.sort LpRRVq_AbelianGroup |- _ ] =>
                 let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
               end
        ; try autorewrite with quot
        ; try apply (@eq_Quot _ _ LpRRV_eq_equiv).
      
      Lemma LpRRVq_scale_scale (x y : R_Ring) (u : LpRRVq_AbelianGroup) :
        LpRRVq_scale x (LpRRVq_scale y u) = LpRRVq_scale (x * y) u.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_scale_scale.
      Qed.
      
      Lemma LpRRVq_scale1 (u : LpRRVq_AbelianGroup) :
        LpRRVq_scale one u = u.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_scale1.
      Qed.
      
      Lemma LpRRVq_scale_plus_l (x : R_Ring) (u v : LpRRVq_AbelianGroup) :
        LpRRVq_scale x (plus u v) = plus (LpRRVq_scale x u) (LpRRVq_scale x v).
      Proof.
        LpRRVq_simpl.
        apply LpRRV_scale_plus_l.
      Qed.

      Lemma LpRRVq_scale_plus_r (x y : R_Ring) (u : LpRRVq_AbelianGroup) :
        LpRRVq_scale (plus x y) u = plus (LpRRVq_scale x u) (LpRRVq_scale y u).
      Proof.
        LpRRVq_simpl.
        apply LpRRV_scale_plus_r.
      Qed.

      Definition LpRRVq_ModuleSpace_mixin : ModuleSpace.mixin_of R_Ring LpRRVq_AbelianGroup
        := ModuleSpace.Mixin R_Ring LpRRVq_AbelianGroup
                             LpRRVq_scale LpRRVq_scale_scale LpRRVq_scale1
                             LpRRVq_scale_plus_l LpRRVq_scale_plus_r.

      Canonical LpRRVq_ModuleSpace :=
        ModuleSpace.Pack R_Ring LpRRVq (ModuleSpace.Class R_Ring LpRRVq LpRRVq_AbelianGroup_mixin LpRRVq_ModuleSpace_mixin) LpRRVq.
      
    End quot.

  End packed.

  Global Arguments LpRRV : clear implicits.
  Global Arguments LpRRVq : clear implicits.

  Section packed.

    Context {p:nat}.

    (* this is only really defined for n >= 0 *)
    Definition root x n
      := if Req_EM_T n 0
         then 0
         else Rpower n (Rinv x).

    Lemma root_integral x n : root x n = 0 -> n = 0.
    Proof.
      unfold root.
      match_destr.
      unfold Rpower.
      intros eqq.
      generalize (exp_pos (/ x * ln n)); intros.
      lra.
    Qed.
    
    Definition LpRRVnorm (rv_X:LpRRV (S p)) : R
      := root (INR (S p)) (FiniteExpectation prts (rvpow (rvabs rv_X) (S p)) (isfe:=LpRRV_lp _)).
    
    Global Instance LpRRV_norm_proper : Proper (LpRRV_eq ==> eq) LpRRVnorm.
    Proof.
      unfold Proper, respectful, LpRRVnorm, LpRRV_eq.
      intros.
      f_equal.
      apply FiniteExpectation_proper_almost
      ; try typeclasses eauto.
      apply rv_almost_eq_pow_abs_proper
      ; try typeclasses eauto.
      apply rv_almost_eq_abs_proper
      ; trivial
      ; try typeclasses eauto.
    Qed.

    Lemma LpRRV_norm_plus x y : LpRRVnorm (LpRRVplus x y) <= LpRRVnorm x + LpRRVnorm y.
    Proof.
      
    Admitted.


    Lemma root_mult_distr x a b :
      0 <= a ->
      0 <= b ->
      root x (a * b) = root x a * root x b.
    Proof.
      intros.
      unfold root.
      match_destr.
      - apply Rmult_integral in e.
        destruct e; subst; simpl
        ; repeat match_destr; lra.
      - repeat (match_destr; subst; try lra).
        rewrite Rpower_mult_distr; trivial; lra.
    Qed.

    Lemma root_pos x a :
      0 <= root x a.
    Proof.
      intros.
      unfold root.
      match_destr; try lra.
      unfold Rpower.
      left.
      apply exp_pos.
    Qed.

    Lemma pow_root_inv x :
      0 <= x ->
      root (INR (S p)) x ^ S p = x.
    Proof.
      intros.
      unfold root.
      match_destr.
      - now rewrite pow0_Sbase.
      - rewrite <- Rpower_pow.
        + rewrite Rpower_mult.
          rewrite Rinv_l.
          * rewrite Rpower_1; trivial.
            lra.
          * apply INR_nzero; lia.
        + apply exp_pos.
    Qed.
    
    Lemma root_pow_inv x :
      0 <= x ->
      root (INR (S p)) (x ^ S p) = x.
    Proof.
      intros.
      unfold root.
      match_destr.
      - now apply pow_integral in e.
      - assert (x <> 0).
        {
          intro; subst.
          rewrite pow_i in n; try lra; try lia.
        }
        rewrite <- Rpower_pow; try lra.
        rewrite Rpower_mult.
        rewrite Rinv_r.
        + rewrite Rpower_1; trivial.
          lra.
        + apply INR_nzero; lia.
    Qed.

    Lemma FiniteExpectation_Lp_pos y
          {islp:IsLp (S p) y} :
      0 <= FiniteExpectation prts (rvpow (rvabs y) (S p)) (isfe:=islp).
    Proof.
      apply FiniteExpectation_pos.
      typeclasses eauto.
    Qed.

    Lemma LpRRV_norm_scal_strong x y : LpRRVnorm (LpRRVscale x y) = Rabs x * LpRRVnorm y.
    Proof.
      unfold LpRRVnorm, LpRRVscale.
      simpl LpRRV_rv_X.
      assert (eqq:rv_eq
                (rvpow (rvabs (rvscale x y)) (S p))
                (rvscale (Rabs x ^ S p) (rvpow (rvabs y) (S p))))
        by now rewrite rv_abs_scale_eq, rvpow_scale.
      rewrite (@FiniteExpectation_ext _ _ prts _ _ eqq
                                         (@LpRRV_lp (S p)
                                                    (@pack_LpRRV (S p) (@rvscale Ts x (@LpRRV_rv_X (S p) y))
                                                                 (@rvscale_rv Ts dom x (@LpRRV_rv_X (S p) y) (@LpRRV_rv (S p) y))
                                                                 (@IsLp_scale (S p) x (@LpRRV_rv_X (S p) y) (@LpRRV_lp (S p) y))))
                                         (@IsFiniteExpectation_scale _ _ _ _ _ (LpRRV_lp _))).

      rewrite FiniteExpectation_scale.
      rewrite root_mult_distr.
      - f_equal.
        rewrite root_pow_inv.
        + lra.
        + apply Rabs_pos.
      - apply pow_le; apply Rabs_pos.
      - apply FiniteExpectation_Lp_pos.
    Qed.

    Lemma LpRRV_norm_scal x y : LpRRVnorm (LpRRVscale x y) <= Rabs x * LpRRVnorm y.
    Proof.
      right.
      apply LpRRV_norm_scal_strong.
    Qed.

    Lemma LpRRV_norm0 x : LpRRVnorm x = 0 -> rv_almost_eq prts x (LpRRVzero (p:=S p)).
    Proof.
      unfold LpRRVnorm, LpRRVzero, LpRRVconst.
      intros.
      apply root_integral in H.
      apply FiniteExpectation_zero_pos in H; try typeclasses eauto.
      erewrite ps_proper in H; try eapply H.
      intros a; simpl; unfold const.
      split; intros eqq.
      + apply pow_integral in eqq.
        now apply Rabs_eq_0.
      + rv_unfold.
        rewrite eqq.
        rewrite Rabs_R0.
        rewrite pow_i; trivial.
        lia.
    Qed.

        
    Section quot.

      Ltac LpRRVq_simpl :=
        repeat match goal with
               | [H: LpRRVq _ |- _ ] =>
                 let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
               | [H: AbelianGroup.sort LpRRVq_AbelianGroup |- _ ] =>
                 let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
               end
        ; try autorewrite with quot in *
        ; try apply (@eq_Quot _ _ LpRRV_eq_equiv).
      
      Hint Rewrite @LpRRVq_constE : quot.
      Hint Rewrite @LpRRVq_zeroE : quot.
      Hint Rewrite @LpRRVq_scaleE : quot.
      Hint Rewrite @LpRRVq_oppE : quot.
      Hint Rewrite @LpRRVq_plusE : quot.
      Hint Rewrite @LpRRVq_minusE : quot.
      Hint Rewrite @LpRRVq_constE : quot.

      Definition LpRRVq_norm : LpRRVq (S p) -> R
        := quot_rec LpRRV_norm_proper.

      Lemma LpRRVq_normE x : LpRRVq_norm (Quot _ x)  = LpRRVnorm x.
      Proof.
        apply quot_recE.
      Qed.

      Hint Rewrite LpRRVq_normE : quot.
      
      Lemma LpRRVq_norm_plus x y : LpRRVq_norm (LpRRVq_plus x y) <= LpRRVq_norm x + LpRRVq_norm y.
      Proof.
        LpRRVq_simpl.
        now apply LpRRV_norm_plus.
      Qed.
      
      Lemma LpRRVq_norm_scal_strong x y : LpRRVq_norm (LpRRVq_scale x y) = Rabs x * LpRRVq_norm y.
      Proof.
        LpRRVq_simpl.
        now apply LpRRV_norm_scal_strong.
      Qed.

      Lemma LpRRVq_norm_scal x y : LpRRVq_norm (LpRRVq_scale x y) <= Rabs x * LpRRVq_norm y.
      Proof.
        LpRRVq_simpl.
        now apply LpRRV_norm_scal.
      Qed.

      Lemma LpRRVq_norm0 x : LpRRVq_norm x = 0 -> x = LpRRVq_zero.
      Proof.
        intros.
        LpRRVq_simpl.
        now apply LpRRV_norm0.
      Qed.

      (*
    
    Record mixin_of (K : AbsRing) (V : NormedModuleAux K) := Mixin {
  norm : V -> R ;
  norm_factor : R ;
  ax1 : forall (x y : V), norm (plus x y) <= norm x + norm y ;
  ax2 : forall (l : K) (x : V), norm (scal l x) <= abs l * norm x ;
  ax3 : forall (x y : V) (eps : R), norm (minus y x) < eps -> ball x eps y ;
  ax4 : forall (x y : V) (eps : posreal), ball x eps y -> norm (minus y x) < norm_factor * eps ;
  ax5 : forall x : V, norm x = 0 -> x = zero
}.

  *)  

    End quot.
    
  End packed.
  
End Lp.


