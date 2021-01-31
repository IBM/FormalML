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

(** This defines the space Lp (https://en.wikipedia.org/wiki/Lp_space) for finite p. 
    This is the space of RandomVariables, where the pth power of its absolute value
    has a finite expectation, module (quotiented by) the a.e relation.
    The a.e. (almost equal) relation is an equivalence relation  that equates random variables
    that are equal with probablity 1.
*)
(**
   There are differences depending on $p$.  The world splits into a couple cases:
   nonnegative p: Lp is a module space (vector space)
     p = 0: nothing extra :-). Note that this is the space of all RandomVariables modulo a.e.
     0 < p < 1: not done yet.
     1 <= p: This is a normed vector space.
       p = 2: This is a hilbert space.  See RandomVariableL2 for more information.
     p = ∞: This is defined in the file RandomVariableLinf, see there for more information.

*)

Local Notation NNR x := (mknonnegreal x ltac:(lra)) (only parsing).

Section Lp.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Global Instance rvnneg_const (pp:nonnegreal) : 
    RandomVariable dom borel_sa (fun x : Ts => const pp x).
  Proof.
    destruct pp; simpl.
    apply rvconst.
  Qed.

  
  Definition IsLp n (rv_X:Ts->R)
    := IsFiniteExpectation prts (rvpower (rvabs rv_X) (const n)).

  Existing Class IsLp.
  Typeclasses Transparent IsLp.

  Global Instance Lp_FiniteLp n rv_X
         {islp:IsLp n rv_X}
    : IsFiniteExpectation prts (rvpower (rvabs rv_X) (const n))
    := islp.

  Global Instance IsLp_proper
    : Proper (eq ==> rv_eq ==> iff) IsLp.
  Proof.
    intros ?? eqq1 x y eqq2.
    unfold IsLp.
    now rewrite eqq1, eqq2.
  Qed.

  Lemma IsLp_proper_almost n rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
        {islp1:IsLp n rv_X1}
    :
      rv_almost_eq prts rv_X1 rv_X2 ->
      IsLp n rv_X2.
  Proof.
    red; intros.
    eapply IsFiniteExpectation_proper_almost
    ; try eapply islp1
    ; try typeclasses eauto.
    apply rv_almost_eq_power_abs_proper
    ; try typeclasses eauto.
    now apply rv_almost_eq_abs_proper
    ; try typeclasses eauto.
  Qed.

  Lemma FiniteExpectation_Lp_pos p y
        {islp:IsLp p y} :
    0 <= FiniteExpectation prts (rvpower (rvabs y) (const p)).
  Proof.
    apply FiniteExpectation_pos.
    typeclasses eauto.
  Qed.

  (* Note that IsLp 0 always holds, so it says that we are not making any assumptions *)
  Global Instance IsL0_True (rv_X:Ts->R) : IsLp (NNR 0) rv_X.
  Proof.
    red.
    assert(eqq:rv_eq (rvpower (rvabs rv_X) (const 0))
                     (rvchoice (fun x => if Req_EM_T (rv_X x) 0 then true else false)
                               (const 0)
                               (const 1))).
    {
      intros a.
      rv_unfold.
      unfold power.
      destruct (Req_EM_T (rv_X a)).
      - rewrite Rabs_pos_eq by lra.
        match_destr; congruence.
      - match_destr.
        + apply Rabs_eq_0 in e; congruence.
        + rewrite Rpower_O; trivial.
          generalize (Rabs_pos (rv_X a)); lra.
    } 
    rewrite eqq.
    typeclasses eauto.
  Qed.

  Lemma IsL1_Finite (rv_X:Ts->R)
        {rrv:RandomVariable dom borel_sa rv_X}
        {lp:IsLp 1 rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    red.
    red in lp.
    apply Expectation_abs_then_finite; trivial.
    now rewrite rvabs_pow1 in lp.
  Qed.

  Lemma IsL1_abs_Finite (rv_X:Ts->R)
        {lp:IsLp 1 rv_X} : IsFiniteExpectation prts (rvabs rv_X).
  Proof.
    red.
    red in lp.
    now rewrite rvabs_pow1 in lp.
  Qed.

  Lemma Finite_abs_IsL1 (rv_X:Ts->R)
        {isfe:IsFiniteExpectation prts (rvabs rv_X)} :
    IsLp 1 rv_X.
  Proof.
    red.
    now rewrite rvabs_pow1.
  Qed.

  Lemma IsLp_bounded n rv_X1 rv_X2
        (rle:rv_le (rvpower (rvabs rv_X1) (const n)) rv_X2)
        {islp:IsFiniteExpectation prts rv_X2}
    :
      IsLp n rv_X1.
  Proof.
    unfold IsLp in *.
    intros.
    eapply (IsFiniteExpectation_bounded prts (const 0) _ rv_X2); trivial.
    intros a.
    unfold const, rvabs, rvpower.
    apply power_nonneg.
  Qed.      

    Lemma IsLp_down_le m n (rv_X:Ts->R)
        {rrv:RandomVariable dom borel_sa rv_X}
        (pfle:0 <= n <= m)
        {lp:IsLp m rv_X} : IsLp n rv_X.
    Proof.
      red in lp; red.
      apply (@IsLp_bounded _ _
                           (rvmax
                              (const 1)
                              (rvpower (rvabs rv_X) (const m))))
      ; [| typeclasses eauto].
      intros a.
      rv_unfold.
      destruct (Rle_lt_dec 1 (Rabs (rv_X a))).
      - eapply Rle_trans; [| eapply Rmax_r].
        now apply Rle_power.
      - eapply Rle_trans; [| eapply Rmax_l].
        unfold power.
        match_destr; [lra | ].
        generalize (Rabs_pos (rv_X a)); intros.
        destruct (Req_EM_T n 0).
        + subst.
          rewrite Rpower_O; lra.
        + assert (eqq:1 = Rpower 1 n).
          {
            unfold Rpower.
            rewrite ln_1.
            rewrite Rmult_0_r.
            now rewrite exp_0.
          }
          rewrite eqq.
          apply Rle_Rpower_l; lra.
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
  
  Global Instance IsLp_scale p (c:R) (rv_X:Ts->R)
         {islp:IsLp p rv_X} :
    IsLp p (rvscale c rv_X).
  Proof.
    unfold IsLp in *.
    rewrite rv_abs_scale_eq.
    rewrite rvpower_abs_scale.
    typeclasses eauto.
  Qed.

  Lemma IsLp_scale_inv p c rv_X 
        {islp:IsLp p (rvscale c rv_X)} :
    c <> 0 ->
    IsLp p rv_X.
  Proof.
    intros.
    unfold IsLp in *.
    rewrite rv_abs_scale_eq in islp.
    rewrite rvpower_abs_scale in islp.
    eapply IsFiniteExpectation_scale_inv; try eassumption.
    generalize (power_pos (Rabs c) p); intros HH.
    cut_to HH.
    - lra.
    - now apply Rabs_no_R0.
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
    rewrite rv_abs_const_eq, rvpower_const.
    typeclasses eauto.
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
    apply IsFiniteExpectation_plus; eauto
    ; typeclasses eauto. 
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

  Lemma IsLp_Finite n (rv_X:Ts->R)
        {rrv:RandomVariable dom borel_sa rv_X}
        (nbig:1<=n)
        {lp:IsLp n rv_X} : IsFiniteExpectation prts rv_X.
  Proof.
    apply IsL1_Finite; trivial.
    eapply IsLp_down_le; try eapply lp; trivial; lra.
  Qed.

  Lemma IsLSp_abs_Finite n (rv_X:Ts->R)
        {rrv:RandomVariable dom borel_sa rv_X}
        (nbig:1<=n)
        {lp:IsLp n rv_X} : IsFiniteExpectation prts (rvabs rv_X).
  Proof.
    apply IsL1_abs_Finite; trivial.
    apply (IsLp_down_le n 1); trivial.
    lra.
  Qed.

  Global Instance IsLp_plus (p:nonnegreal)
         (rv_X1 rv_X2 : Ts -> R)
         {rv1 : RandomVariable dom borel_sa rv_X1}
         {rv2 : RandomVariable dom borel_sa rv_X2} 
         {islp1:IsLp p rv_X1}
         {islp2:IsLp p rv_X2} :
    IsLp p (rvplus rv_X1 rv_X2).
  Proof.
    destruct p as [p ?].
    apply (IsLp_bounded _ _ (rvscale ((power 2 p)) (rvplus (rvpower (rvabs rv_X1) (const p)) (rvpower (rvabs rv_X2) (const p)))))
    ; [| typeclasses eauto].
    intros x.
    rv_unfold.
    now apply power_abs_ineq.
  Qed.

  Global Instance IsLp_minus (p:nonnegreal)
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

  Section packed.
    Context {p:R}.

    Record LpRRV : Type
      := LpRRV_of {
             LpRRV_rv_X :> Ts -> R
             ; LpRRV_rv :> RandomVariable dom borel_sa LpRRV_rv_X
             ; LpRRV_lp :> IsLp p LpRRV_rv_X
           }.
    
    Global Existing Instance LpRRV_rv.
    Global Existing Instance LpRRV_lp.
    
    Global Instance LpRRV_LpS_FiniteLp (rv_X:LpRRV)
      : IsFiniteExpectation prts (rvpower (rvabs rv_X) (const p))
      := LpRRV_lp _.

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
    
    Lemma LpRRVopp_scale (rv:LpRRV) :
      LpRRV_eq 
        (LpRRVopp rv) (LpRRVscale (-1) rv).
    Proof.
      red.
      apply rv_almost_eq_eq.
      reflexivity.
    Qed.

    Section quoted.

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

    End quoted.
    
  End packed.

  Hint Rewrite @LpRRVq_constE : quot.
  Hint Rewrite @LpRRVq_zeroE : quot.
  Hint Rewrite @LpRRVq_scaleE : quot.
  Hint Rewrite @LpRRVq_oppE : quot.
      

  Global Arguments LpRRV : clear implicits.
  Global Arguments LpRRVq : clear implicits.

  Section packednonneg.

    Context {p:nonnegreal}.

    Definition LpRRVplus (rv1 rv2:LpRRV p) : LpRRV p
      := pack_LpRRV (rvplus rv1  rv2).

    Global Instance LpRRV_plus_proper : Proper (LpRRV_eq ==> LpRRV_eq ==> LpRRV_eq) LpRRVplus.
    Proof.
      unfold Proper, respectful, LpRRV_eq.
      intros [x1??] [x2??] eqqx [y1??] [y2??] eqqy.
      simpl in *.
      now apply rv_almost_eq_plus_proper.
    Qed.
    
    Definition LpRRVminus (rv1 rv2:LpRRV p) : LpRRV p
      := pack_LpRRV (rvminus rv1 rv2).

    Lemma LpRRVminus_plus (rv1 rv2:LpRRV p) :
      LpRRV_eq 
        (LpRRVminus rv1 rv2) (LpRRVplus rv1 (LpRRVopp rv2)).
    Proof.
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
    
    Lemma LpRRV_plus_assoc (x y z : LpRRV p) : LpRRV_eq (LpRRVplus x (LpRRVplus y z)) (LpRRVplus (LpRRVplus x y) z).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus.
      lra.
    Qed.

    Lemma LpRRV_plus_zero (x : LpRRV p) : LpRRV_eq (LpRRVplus x (LpRRVconst 0)) x.
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, const.
      lra.
    Qed.

    Lemma LpRRV_plus_inv (x: LpRRV p) : LpRRV_eq (LpRRVplus x (LpRRVopp x)) (LpRRVconst 0).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const.
      lra.
    Qed.

    Lemma LpRRV_scale_scale (x y : R) (u : LpRRV p) :
      LpRRV_eq (LpRRVscale x (LpRRVscale y u)) (LpRRVscale (x * y) u).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    Lemma LpRRV_scale1 (u : LpRRV p) :
      LpRRV_eq (LpRRVscale one u) u.
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult, one; simpl.
      lra.
    Qed.
    
    Lemma LpRRV_scale_plus_l (x : R) (u v : LpRRV p) :
      LpRRV_eq (LpRRVscale x (LpRRVplus u v)) (LpRRVplus (LpRRVscale x u) (LpRRVscale x v)).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.
    
    Lemma LpRRV_scale_plus_r (x y : R) (u : LpRRV p) :
      LpRRV_eq (LpRRVscale (x + y) u) (LpRRVplus (LpRRVscale x u) (LpRRVscale y u)).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply rv_almost_eq_eq; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    (* Lp is a module space for all finite nonnegative p *)
    Section quotnneg.

      Definition LpRRVq_plus  : LpRRVq p -> LpRRVq p -> LpRRVq p
        := quot_lift2 _ LpRRVplus.
      
      Lemma LpRRVq_plusE x y : LpRRVq_plus (Quot _ x) (Quot _ y) = Quot _ (LpRRVplus x y).
      Proof.
        apply quot_lift2E.
      Qed.

      Hint Rewrite LpRRVq_plusE : quot.

      Definition LpRRVq_minus  : LpRRVq p -> LpRRVq p -> LpRRVq p
        := quot_lift2 _ LpRRVminus.

      Lemma LpRRVq_minusE x y : LpRRVq_minus (Quot _ x) (Quot _ y) = Quot _ (LpRRVminus x y).
      Proof.
        apply quot_lift2E.
      Qed.

      Hint Rewrite LpRRVq_minusE : quot.

      Ltac LpRRVq_simpl
        := repeat match goal with
                  | [H: LpRRVq _ |- _ ] =>
                    let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
                  end
           ; try autorewrite with quot
           ; try apply (@eq_Quot _ _ LpRRV_eq_equiv).

      Lemma LpRRVq_minus_plus (rv1 rv2:LpRRVq p) :
        LpRRVq_minus rv1 rv2 = LpRRVq_plus rv1 (LpRRVq_opp rv2).
      Proof.
        LpRRVq_simpl.
        apply LpRRVminus_plus.
      Qed.

      Lemma LpRRVq_opp_scale (rv:LpRRVq p) :
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
      
      Lemma LpRRVq_plus_assoc (x y z : LpRRVq p) : LpRRVq_plus x (LpRRVq_plus y z) = LpRRVq_plus (LpRRVq_plus x y) z.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_plus_assoc.
      Qed.


      Lemma LpRRVq_plus_zero (x : LpRRVq p) : LpRRVq_plus x LpRRVq_zero = x.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_plus_zero.
      Qed.

      Lemma LpRRVq_plus_inv (x: LpRRVq p) : LpRRVq_plus x (LpRRVq_opp x) = LpRRVq_zero.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_plus_inv.
      Qed.
      
      Definition LpRRVq_AbelianGroup_mixin : AbelianGroup.mixin_of (LpRRVq p)
        := AbelianGroup.Mixin (LpRRVq p) LpRRVq_plus LpRRVq_opp LpRRVq_zero
                              LpRRVq_plus_comm LpRRVq_plus_assoc
                              LpRRVq_plus_zero LpRRVq_plus_inv.

      Canonical LpRRVq_AbelianGroup :=
        AbelianGroup.Pack (LpRRVq p) LpRRVq_AbelianGroup_mixin (LpRRVq p).

      Ltac LpRRVq_simpl ::=
        repeat match goal with
               | [H: LpRRVq _ |- _ ] =>
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
        ModuleSpace.Pack R_Ring (LpRRVq p) (ModuleSpace.Class R_Ring (LpRRVq p) LpRRVq_AbelianGroup_mixin LpRRVq_ModuleSpace_mixin) (LpRRVq p).

    End quotnneg.
  End packednonneg.

    (** At this point, we will be spliting into three cases:
        p = 0       => This is the space of Random Variables modulo almost-equal.  
                      We already showed what we know about it.  (It is a ModuleSpace)
        1 <= p < ∞  => This is a normed vector space
        0 < p < 1   => This is a metric space.
     *)

    Section normish.
      (** For p = 0, this is not really defined.
          For 1 <= p this defines a norm.
          For 0 < p < 1 this defines a quasi norm
       *)
      Context {p:R}.
      Definition LpRRVnorm (rv_X:LpRRV p) : R
        := power (FiniteExpectation prts (rvpower (rvabs rv_X) (const p))) (Rinv p).

      Global Instance LpRRV_norm_proper : Proper (LpRRV_eq ==> eq) LpRRVnorm.
      Proof.
        unfold Proper, respectful, LpRRVnorm, LpRRV_eq.
        intros.
        f_equal.
        apply FiniteExpectation_proper_almost
        ; try typeclasses eauto.
        apply rv_almost_eq_power_abs_proper
        ; try typeclasses eauto.
        apply rv_almost_eq_abs_proper
        ; trivial
        ; try typeclasses eauto.
      Qed.

      Lemma almost0_lpf_almost0 (rv_X:Ts->R)
            {rrv:RandomVariable dom borel_sa rv_X}
            {isfe: IsFiniteExpectation prts (rvpower (rvabs rv_X) (const p))}:
        rv_almost_eq prts rv_X (const 0) <->
        rv_almost_eq prts (rvpower (rvabs rv_X) (const p)) (const 0).
      Proof.
        intros.
        unfold rv_almost_eq in *.
        erewrite ps_proper.
        - split; intros H; exact H.
        - red; intros a.
          rv_unfold.
          split; intros eqq.
          + rewrite eqq.
            rewrite Rabs_R0.
            rewrite power0_Sbase; lra.
          + apply power_integral in eqq.
            now apply Rabs_eq_0 in eqq.
      Qed.

      (* If the norm is 0 then p is a.e. 0 *)
      Theorem LpFin0_almost0 (rv_X:Ts->R)
            {rrv:RandomVariable dom borel_sa rv_X}
            {isfe: IsFiniteExpectation prts (rvpower (rvabs rv_X) (const p))}:
        FiniteExpectation prts (rvpower (rvabs rv_X) (const p)) = 0 ->
        rv_almost_eq prts rv_X (const 0).
      Proof.
        intros fin0.
        apply FiniteExpectation_zero_pos in fin0
        ; try typeclasses eauto.
        apply almost0_lpf_almost0
        ; try typeclasses eauto.
        apply fin0.
      Qed.

      Lemma LpRRV_norm0 (x:LpRRV p) :
        LpRRVnorm x = 0 ->
        rv_almost_eq prts x (LpRRVzero (p:=p)).
      Proof.
        unfold LpRRVnorm, LpRRVzero, LpRRVconst.
        intros.
        apply power_integral in H.
        apply FiniteExpectation_zero_pos in H; try typeclasses eauto.
        erewrite ps_proper in H; try eapply H.
        intros a; simpl; unfold const.
        split; intros eqq.
        + apply power_integral in eqq.
          now apply Rabs_eq_0.
        + rv_unfold.
          rewrite eqq.
          rewrite Rabs_R0.
          rewrite power0_Sbase; trivial.
      Qed.

    End normish.

    Definition LpRRVpoint (p:R) : LpRRV p := LpRRVconst 0.
    
    Section packedbigp.
      Context {p:R}.
      Context (pbig:1 <= p).

      Let pnneg : nonnegreal := mknonnegreal p ltac:(lra).
      Canonical pnneg.
      
      Lemma Minkowski_rv (x y : LpRRV p) (t:R): 
        0 < t < 1 -> 
        rv_le (rvpower (rvplus (rvabs x) (rvabs y)) (const p))
              (rvplus
                 (rvscale (power (/t) (p-1)) (rvpower (rvabs x) (const p))) 
                 (rvscale (power (/(1-t)) (p-1)) (rvpower (rvabs y) (const p)))).
      Proof.
        intros.
        intro x0.
        generalize (@power_minkowski_helper p (rvabs x x0) (rvabs y x0) t); intros.
        rv_unfold.
        apply H0; trivial.
        apply Rabs_pos.
        apply Rabs_pos.
      Qed.

      Lemma rvpower_plus_le (x y : LpRRV p) :
        rv_le (rvpower (rvabs (rvplus x y)) (const p)) (rvpower (rvplus (rvabs x) (rvabs y)) (const p)).
      Proof.
        intro x0.
        rv_unfold.
        apply Rle_power_l; [lra|].
        split.
        - apply Rabs_pos.
        - apply Rabs_triang.
      Qed.

      Lemma Minkowski_1 (x y : LpRRV p) (t:R):
        0 < t < 1 -> 
        (FiniteExpectation prts (rvpower (rvabs (rvplus x y)) (const p)))  <=
        (power (/t) (p-1)) * (FiniteExpectation prts (rvpower (rvabs x) (const p))) + 
        (power (/(1-t)) (p-1)) * (FiniteExpectation prts (rvpower (rvabs y) (const p))).
      Proof.
        intros.
        generalize (Minkowski_rv x y t H); intros.
        generalize (rvpower_plus_le x y); intros.
        assert (IsFiniteExpectation prts (rvpower (rvplus (rvabs x) (rvabs y)) (const p))).
        {
          eapply (IsFiniteExpectation_bounded _ _ _ _ H1 H0).
        } 
        assert (FiniteExpectation prts (rvpower (rvabs (rvplus x y)) (const p)) <=
                FiniteExpectation prts (rvpower (rvplus (rvabs x) (rvabs y)) (const p))).
        {
          apply FiniteExpectation_le.
          apply rvpower_plus_le.
        } 
        generalize (FiniteExpectation_le _ _ _ H0); intros.
        rewrite FiniteExpectation_plus in H4.
        rewrite FiniteExpectation_scale in H4.
        rewrite FiniteExpectation_scale in H4.
        apply Rle_trans with 
            (r2 := FiniteExpectation prts (rvpower (rvplus (rvabs x) (rvabs y)) (const p))); trivial.
      Qed.

      Lemma Minkowski_2 (x y : LpRRV p)
            (xexppos : 0 < FiniteExpectation prts (rvpower (rvabs x) (const p)))
            (yexppos : 0 < FiniteExpectation prts (rvpower (rvabs y) (const p))) :
        FiniteExpectation prts (rvpower (rvabs (rvplus x y)) (const p))  <=
        power ((power (FiniteExpectation prts (rvpower (rvabs x) (const p))) (/ p)) +
               (power (FiniteExpectation prts (rvpower (rvabs y) (const p))) (/ p))) p.
      Proof.
        generalize (Minkowski_1 x y); intros.
        pose (a := power (FiniteExpectation prts (rvpower (rvabs x) (const p))) (/ p)).
        pose (b := power (FiniteExpectation prts (rvpower (rvabs y) (const p))) (/ p)).
        assert (0 < a)
          by (apply power_pos; lra).
        assert (0 < b)
          by (apply power_pos; lra).
        replace (FiniteExpectation prts (rvpower (rvabs x) (const p))) with (power a p) in H
          by (apply power_inv_cancel; lra).
        replace (FiniteExpectation prts (rvpower (rvabs y) (const p))) with (power b p) in H
          by (apply power_inv_cancel; lra).
        specialize (H (a /(a + b))).
        cut_to H.
        - rewrite (power_minkowski_subst p H0 H1) in H; trivial.
        - now apply minkowski_range.
      Qed.

      Lemma Rle_power_inv_l (a b : R) :
        0 < a -> a  <= b -> power a (/ p) <= power b (/ p).
      Proof.
        intros.
        apply Rle_power_l.
        - left; apply Rinv_0_lt_compat; lra.
        - lra.
      Qed.
      
      Lemma Minkowski_lt (x y : LpRRV p)
            (xexppos : 0 < FiniteExpectation prts (rvpower (rvabs x) (const p)))
            (yexppos : 0 < FiniteExpectation prts (rvpower (rvabs y) (const p))) 
            (xyexppos : 0 < FiniteExpectation prts (rvpower (rvabs (rvplus x y)) (const p))) :
        power (FiniteExpectation prts (rvpower (rvabs (rvplus x y)) (const p))) (/ p)  <=
        power (FiniteExpectation prts (rvpower (rvabs x) (const p))) (/ p) +
        power (FiniteExpectation prts (rvpower (rvabs y) (const p))) (/ p).
      Proof.
        generalize (Minkowski_2 x y xexppos yexppos); intros.
        apply Rle_power_inv_l in H; try lra.
        rewrite inv_power_cancel in H; trivial; try lra.
        apply Rplus_le_le_0_compat
        ; apply power_nonneg.
      Qed.   

      Theorem Minkowski (x y : LpRRV p) :
        power (FiniteExpectation prts (rvpower (rvabs (rvplus x y)) (const p))) (/ p)  <=
        power (FiniteExpectation prts (rvpower (rvabs x) (const p))) (/ p) +
        power (FiniteExpectation prts (rvpower (rvabs y) (const p))) (/ p).
      Proof.
        destruct (FiniteExpectation_pos prts (rvpower (rvabs x) (const p))).
        - {
            destruct (FiniteExpectation_pos prts (rvpower (rvabs y) (const p))).
            - {
                - destruct (FiniteExpectation_pos prts (rvpower (rvabs (rvplus x y)) (const p))). 
                  + now apply Minkowski_lt.
                  + rewrite <- H1.
                    rewrite power0_Sbase
                      by (apply Rinv_neq_0_compat; lra).
                    apply Rplus_le_le_0_compat
                    ; apply power_nonneg.
              } 
            - rewrite <- H0.
              rewrite power0_Sbase
                by (apply Rinv_neq_0_compat; lra).
              symmetry in H0.
              apply LpFin0_almost0 in H0; try typeclasses eauto.
              rewrite (FiniteExpectation_proper_almost prts (rvpower (rvabs (rvplus x y)) (const p)) (rvpower (rvabs x) (const p))).
              + lra.
              + apply rv_almost_eq_power_abs_proper
                ; try typeclasses eauto.
                apply rv_almost_eq_abs_proper
                ; try typeclasses eauto.
                
                generalize (rv_almost_eq_plus_proper prts x x y (const 0)); intros HH.
                cut_to HH; trivial; try typeclasses eauto.
                * apply (rv_almost_eq_rv_trans prts _ (rvplus x (const 0)))
                  ; trivial
                  ; try typeclasses eauto.
                  apply rv_almost_eq_eq.
                  intros a.
                  rv_unfold.
                  lra.
                * apply rv_almost_eq_rv_refl
                  ; typeclasses eauto.
          }                                                    
        - rewrite <- H.
          rewrite power0_Sbase
            by (apply Rinv_neq_0_compat; lra).
          symmetry in H.
          apply LpFin0_almost0 in H; try typeclasses eauto.
          rewrite (FiniteExpectation_proper_almost prts (rvpower (rvabs (rvplus x y)) (const p)) (rvpower (rvabs y) (const p))).
          + lra.
          + apply rv_almost_eq_power_abs_proper
            ; try typeclasses eauto.
            apply rv_almost_eq_abs_proper
            ; try typeclasses eauto.
            generalize (rv_almost_eq_plus_proper prts x (const 0) y y H)
            ; intros HH.
            cut_to HH.
            * apply (rv_almost_eq_rv_trans prts _ (rvplus (const 0) y))
              ; trivial
              ; try typeclasses eauto.
              apply rv_almost_eq_eq.
              intros a.
              rv_unfold.
              lra.
            * apply rv_almost_eq_rv_refl.
              typeclasses eauto.
      Qed.

      Lemma LpRRV_norm_plus (x y:LpRRV p) : LpRRVnorm (LpRRVplus x y) <= LpRRVnorm x + LpRRVnorm y.
      Proof.
        unfold Proper, respectful, LpRRVnorm, LpRRVplus.
        simpl LpRRV_rv_X.
        simpl LpRRV_LpS_FiniteLp.
        apply Minkowski.
      Qed.

      Lemma LpRRV_norm_scal_strong (x:R) (y:LpRRV p) : LpRRVnorm (LpRRVscale x y) = Rabs x * LpRRVnorm y.
      Proof.
        unfold LpRRVnorm, LpRRVscale.
        simpl LpRRV_rv_X.
        assert (eqq:rv_eq
                      (rvpower (rvabs (rvscale x y)) (const p))
                      (rvscale (power (Rabs x) p) (rvpower (rvabs y) (const p)))).
        {
          rewrite rv_abs_scale_eq.
          rv_unfold; intros a.
          rewrite power_mult_distr; trivial; apply Rabs_pos.
        } 
        rewrite (FiniteExpectation_ext prts _ _ eqq).
        rewrite FiniteExpectation_scale.
        rewrite <- power_mult_distr.
        - f_equal.
          rewrite inv_power_cancel; try lra.
          apply Rabs_pos.
        - apply power_nonneg. 
        - apply FiniteExpectation_Lp_pos.
      Qed.

      Lemma LpRRV_norm_scal (x:R) (y:LpRRV p) : LpRRVnorm (LpRRVscale x y) <= Rabs x * LpRRVnorm y.
      Proof.
        right.
        apply LpRRV_norm_scal_strong.
      Qed.

      Definition LpRRVball (x:LpRRV p) (e:R) (y:LpRRV p): Prop
        := LpRRVnorm (LpRRVminus x y) < e.

      Ltac LpRRV_simpl
        := repeat match goal with
                   | [H : LpRRV _ |- _ ] => destruct H as [???]
                   end;
            unfold LpRRVball, LpRRVnorm, LpRRVplus, LpRRVminus, LpRRVopp, LpRRVscale, LpRRVnorm in *
            ; simpl pack_LpRRV; simpl LpRRV_rv_X in *.


      Global Instance LpRRV_ball_proper : Proper (LpRRV_eq ==> eq ==> LpRRV_eq ==> iff) LpRRVball.
      Proof.
        intros ?? eqq1 ?? eqq2 ?? eqq3.
        unfold LpRRVball in *.
        rewrite <- eqq1, <- eqq2, <- eqq3.
        reflexivity.
      Qed.

      Lemma LpRRV_ball_refl x (e : posreal) : LpRRVball x e x.
      Proof.
        LpRRV_simpl.
        assert (eqq1:rv_eq (rvpower (rvabs (rvminus LpRRV_rv_X0 LpRRV_rv_X0)) (const p))
                           (const 0)).
        {
          rewrite rvminus_self.
          rewrite rv_abs_const_eq.
          rewrite Rabs_pos_eq by lra.
          rewrite rvpower_const.
          rewrite power0_Sbase.
          reflexivity.
        }
        rewrite (FiniteExpectation_ext _ _ _ eqq1).
        rewrite FiniteExpectation_const.
        rewrite power0_Sbase.
        apply cond_pos.
      Qed.
      
      Lemma LpRRV_ball_sym x y e : LpRRVball x e y -> LpRRVball y e x.
      Proof.
        LpRRV_simpl.
        intros.
        rewrite (FiniteExpectation_ext _ _  (rvpower (rvabs (rvminus LpRRV_rv_X1 LpRRV_rv_X0)) (const p)))
        ; trivial.
        rewrite rvabs_rvminus_sym.
        reflexivity.
      Qed.

      Lemma LpRRV_ball_trans x y z e1 e2 : LpRRVball x e1 y -> LpRRVball y e2 z -> LpRRVball x (e1+e2) z.
      Proof.
        generalize (LpRRV_norm_plus
                      (LpRRVminus x y)
                      (LpRRVminus y z)).
        LpRRV_simpl.
        intros.

        apply (Rle_lt_trans
                 _ 
                 ((power (FiniteExpectation prts (rvpower (rvabs (rvminus LpRRV_rv_X2 LpRRV_rv_X1)) (const p))) (/ p)) +
                  (power  (FiniteExpectation prts (rvpower (rvabs (rvminus LpRRV_rv_X1 LpRRV_rv_X0)) (const p))) (/ p))))
        ; [ | now apply Rplus_lt_compat].

        (* by minkowski *)
        rewrite (FiniteExpectation_ext _ (rvpower (rvabs (rvminus LpRRV_rv_X2 LpRRV_rv_X0)) (const p))
                                       (rvpower (rvabs (rvplus (rvminus LpRRV_rv_X2 LpRRV_rv_X1) (rvminus LpRRV_rv_X1 LpRRV_rv_X0))) (const p))); trivial.
        intros a.
        rv_unfold.
        f_equal.
        f_equal.
        lra.
      Qed.

      Lemma LpRRV_close_close (x y : LpRRV p) (eps : R) :
        LpRRVnorm (LpRRVminus y x) < eps ->
        LpRRVball x eps y.
      Proof.
        intros.
        apply LpRRV_ball_sym.
        apply H.
      Qed.

      Definition LpRRVnorm_factor : R := 1.
      
      Lemma LpRRV_norm_ball_compat (x y : LpRRV p) (eps : posreal) :
        LpRRVball x eps y -> LpRRVnorm (LpRRVminus y x) < LpRRVnorm_factor * eps.
      Proof.
        intros HH.
        apply LpRRV_ball_sym in HH.
        unfold LpRRVnorm_factor.
        field_simplify.
        apply HH.
      Qed.

      Lemma LpRRV_plus_opp_minus (x y : LpRRV p) :
        LpRRV_eq (LpRRVplus x (LpRRVopp y)) (LpRRVminus x y).
      Proof.
        unfold LpRRVminus, LpRRVplus, LpRRVopp.
        simpl.
        apply rv_almost_eq_eq.
        intros ?.
        reflexivity.
      Qed.

      Lemma LpRRV_norm_telescope_minus (f : nat -> LpRRV p) :
        forall (n k:nat), 
          LpRRVnorm (LpRRVminus (f ((S k)+n)%nat) (f n)) <= 
          sum_n_m (fun m => LpRRVnorm (LpRRVminus (f (S m)) (f m))) n (k + n).
      Proof.
        intros.
        induction k.
        - replace (0+n)%nat with n by lia.
          rewrite sum_n_n.
          simpl; lra.
        - replace (S k + n)%nat with (S (k + n)%nat) by lia.
          rewrite sum_n_Sm; [|lia].
          rewrite (LpRRV_norm_proper (LpRRVminus (f (S (S k) + n)%nat) (f n))
                                     (LpRRVplus  
                                        (LpRRVminus (f (S (S k) + n)%nat) (f ((S k)+n)%nat))
                                        (LpRRVminus (f ((S k) + n)%nat) (f n)))).
          generalize (LpRRV_norm_plus  
                        (LpRRVminus (f (S (S k) + n)%nat) (f (S k + n)%nat))
                        (LpRRVminus (f (S k + n)%nat) (f n))); intros.
          apply Rle_trans with (r2 := LpRRVnorm (LpRRVminus (f (S k + n)%nat) (f n)) +
                                      LpRRVnorm (LpRRVminus (f (S (S k) + n)%nat) (f (S k + n)%nat))).
          now rewrite Rplus_comm.
          now apply Rplus_le_compat_r.
          do 3 rewrite LpRRVminus_plus.
          rewrite LpRRV_plus_assoc.
          rewrite <- LpRRV_plus_assoc with (x := (f (S (S k) + n)%nat)).
          rewrite <- (@LpRRV_plus_comm pnneg (f (S k + n)%nat)).
          rewrite LpRRV_plus_inv.          
          now rewrite LpRRV_plus_zero.
      Qed.

      Lemma sum_geom (n : nat) (c : R):
        c <> 1 ->
        sum_n (fun k => pow c k) n = (pow c (S n) - 1)/(c - 1).
      Proof.
        intros.
        induction n.
        - rewrite sum_O, pow_O, pow_1.
          unfold Rdiv.
          rewrite Rinv_r; lra.
        - unfold sum_n.
          rewrite sum_n_Sm; [|lia].
          unfold sum_n in IHn.
          rewrite IHn.
          unfold plus; simpl.
          field; lra.
      Qed.

      Lemma sum_geom_n_m (n m : nat) (c : R) :
        c <> 1 ->
        (S n <= m)%nat ->
        sum_n_m (fun k => pow c k) (S n) m = (pow c (S m) - pow c (S n))/(c-1).
      Proof.
        intros.
        rewrite sum_n_m_sum_n; [|lia].
        rewrite sum_geom; trivial.
        rewrite sum_geom; trivial.
        unfold minus, plus, opp; simpl.
        field; lra.
      Qed.

      Global Instance IsLp_sum (n : nat)
             (rv_X : nat -> Ts -> R)
             {rv : forall n, RandomVariable dom borel_sa (rv_X n)}
             {islp:forall n, IsLp p (rv_X n)} :
        IsLp p (rvsum rv_X n).
      Proof.
        unfold IsLp, rvsum.
        
      Admitted.

      Definition LpRRVsum (rvn:nat -> LpRRV p) (n:nat) : LpRRV p
        := pack_LpRRV (rvsum rvn n).

      Definition LpRRVabs (rv : LpRRV p) : LpRRV p
        := pack_LpRRV (rvabs rv).                                                 

      Lemma LpRRV_norm_sum (f : nat -> LpRRV p) :
        forall (n:nat), 
          LpRRVnorm (LpRRVsum f n) <=
          sum_n (fun m => LpRRVnorm (f m)) n.
      Proof.
        unfold sum_n; intros.
        induction n.
        - unfold sum_n.
          rewrite sum_n_n.
          assert (LpRRV_eq  (LpRRVsum f 0) (f 0%nat)).
          + apply rv_almost_eq_eq.
            intro x.
            unfold LpRRVsum; simpl.
            unfold rvsum.
            now rewrite sum_O.
          + rewrite H; lra.
        - rewrite sum_n_Sm; [|lia].
          assert (LpRRV_eq (LpRRVsum f (S n)) (LpRRVplus (LpRRVsum f n) (f (S n)))).
          + apply rv_almost_eq_eq.
            intro x.
            unfold LpRRVsum; simpl.
            unfold rvsum, sum_n.
            rewrite sum_n_Sm; [|lia].
            now unfold rvplus, plus; simpl.
          + rewrite H.
            generalize (LpRRV_norm_plus (LpRRVsum f n) (f (S n))); intros.
            apply Rle_trans with (r2 := LpRRVnorm (LpRRVsum f n) + LpRRVnorm (f (S n))); trivial.
            unfold plus; simpl; lra.
      Qed.

      Lemma norm_abs (f : LpRRV p) :
        LpRRVnorm (LpRRVabs f) = LpRRVnorm f.
      Proof.
        unfold LpRRVnorm.
        f_equal.
        unfold LpRRVabs.
        simpl.
        erewrite FiniteExpectation_ext with (rv_X2 := rvpower (rvabs f) (const p)).
        reflexivity.
        now rewrite rv_abs_abs.
      Qed.
      
      Lemma c_pow_bound(c : R) (n : nat) :
        0 < c < 1 ->
        (1-c^n) / (1-c) <= 1/(1-c).
      Proof.
        intros.
        unfold Rdiv.
        apply Rmult_le_reg_r with (r := 1-c); [lra|].
        rewrite Rmult_assoc.
        rewrite <- Rinv_l_sym; [|lra].
        rewrite Rmult_assoc.
        rewrite <- Rinv_l_sym; [|lra].
        apply Rplus_le_reg_r with (r := -1).
        apply Ropp_le_cancel.
        ring_simplify.
        left; apply pow_lt; lra.
      Qed.

      Lemma lp_telescope_norm_bound (f : nat -> LpRRV p) :
        (forall (n:nat), LpRRVnorm (LpRRVminus (f (S n)) (f n)) < / (pow 2 n)) ->
        forall (n:nat), 
          LpRRVnorm (LpRRVsum (fun n0 => LpRRVabs (LpRRVminus (f (S n0)) (f n0))) n) <= 2.
      Proof.
        intros.
        apply Rle_trans with (r2 := sum_n (fun n0 => LpRRVnorm (LpRRVabs (LpRRVminus (f (S n0)) (f n0)))) n).
        apply LpRRV_norm_sum.
        apply Rle_trans with (r2 := sum_n (fun n0 => / 2^n0) n).
        unfold sum_n.
        apply sum_n_m_le.
        intros; left.
        rewrite norm_abs.
        apply H.
        rewrite sum_n_ext with (b := fun n0 => (/ 2)^n0) by (intros; now rewrite Rinv_pow).
        rewrite sum_geom; [|lra].
        generalize (c_pow_bound (/2) (S n)); intros.
        lra.
      Qed.
        
      (* note this is zero at points where the limit is infinite *)
      Definition rv_lim (f : nat -> Ts -> R) : (Ts -> R) :=
        (fun omega => real (Lim_seq (fun n => f n omega))).

      Lemma islp_lim_bound (f : nat -> LpRRV p) (c : R) :
        (forall (n:nat), LpRRVnorm (LpRRVsum f n) <= c) ->
        IsLp p (rv_lim (fun n => LpRRVsum f n)).
      Proof.
        Admitted.

      Lemma islp_lim_telescope_abs (f : nat -> LpRRV p) :
        (forall (n:nat), LpRRVnorm (LpRRVminus (f (S n)) (f n)) < / (pow 2 n)) ->
        IsLp p (rv_lim
                  (fun n => LpRRVsum (fun n0 => LpRRVabs (LpRRVminus (f (S n0)) (f n0))) n)).
      Proof.
        intros.
        apply islp_lim_bound with (c := 2).
        intros.
        now apply lp_telescope_norm_bound.
      Qed.

      Lemma lp_norm_seq_pow2 (f : nat -> LpRRV p) :
        (forall (n:nat), LpRRVnorm (LpRRVminus (f (S n)) (f n)) < / (pow 2 n)) ->
        forall (n m:nat), (m > S n)%nat -> 
                          LpRRVnorm (LpRRVminus (f m) (f (S n))) <= / (pow 2 n).
      Proof.
        intros.
        generalize (LpRRV_norm_telescope_minus f (S n) (m-S (S n))%nat); intros.
        replace (S (m - S (S n)) + (S n))%nat with (m) in H1 by lia.
        replace (m - S (S n) + (S n))%nat with (m-1)%nat in H1 by lia.
        apply Rle_trans with 
            (r2 := sum_n_m (fun m : nat => LpRRVnorm (LpRRVminus (f (S m)) (f m))) (S n) (m - 1)); trivial.
        apply Rle_trans with (r2 := sum_n_m (fun m0 => / (2 ^ m0)) (S n) (m-1)%nat).
        apply sum_n_m_le; intros; left.
        apply H.
        assert (forall n, (/ (pow 2 n)) = pow (/ 2) n).
        intros.
        now rewrite <- Rinv_pow.
        rewrite sum_n_m_ext with (b := fun m0 => pow (/ 2) m0); trivial.
        rewrite sum_geom_n_m; [|lra|lia].
        replace (/2 ^ n) with ((/2)^n) by now rewrite H2.
        replace (S (m-1)) with (m) by lia.
        unfold Rdiv.
        replace (/2 - 1) with (-/2) by lra.
        rewrite <- Ropp_inv_permute; [|lra].
        field_simplify.
        simpl.
        rewrite <- Rmult_assoc.
        replace (2 * / 2) with (1) by lra.
        ring_simplify.
        replace ((/ 2)^n) with (0 + (/ 2)^n) at 2 by lra.
        apply Rplus_le_compat_r.
        apply Ropp_le_cancel.
        ring_simplify.
        replace (m) with (S (m-1)) by lia.
        simpl.
        field_simplify.
        apply pow_le; lra.
     Qed.

      Section quotbigp.
      Ltac LpRRVq_simpl :=
        repeat match goal with
               | [H: LpRRVq p |- _ ] =>
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

      Definition LpRRVq_ball : LpRRVq p -> R -> LpRRVq p -> Prop
        := quot_lift_ball LpRRV_eq LpRRVball.

      Lemma LpRRVq_ballE x e y : LpRRVq_ball (Quot _ x) e (Quot _ y)  = LpRRVball x e y.
      Proof.
        apply quot_lift_ballE.
      Qed.

      Hint Rewrite LpRRVq_ballE : quot.
      
      Definition LpRRVq_point : LpRRVq p
        := Quot _ (LpRRVpoint p).


      Lemma LpRRVq_pointE : LpRRVq_point  = Quot _ (LpRRVpoint p).
      Proof.
        reflexivity.
      Qed.

      Hint Rewrite LpRRVq_pointE : quot.

      Lemma LpRRVq_ball_refl x (e : posreal) : LpRRVq_ball x e x.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_ball_refl.
      Qed.
      
      Lemma LpRRVq_ball_sym x y e : LpRRVq_ball x e y -> LpRRVq_ball y e x.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_ball_sym.
      Qed.

      Lemma LpRRVq_ball_trans x y z e1 e2 : LpRRVq_ball x e1 y -> LpRRVq_ball y e2 z -> LpRRVq_ball x (e1+e2) z.
      Proof.
        LpRRVq_simpl.
        apply LpRRV_ball_trans.
      Qed.

      Definition LpRRVq_UniformSpace_mixin : UniformSpace.mixin_of (LpRRVq p)
        := UniformSpace.Mixin  (LpRRVq p) LpRRVq_point LpRRVq_ball
                               LpRRVq_ball_refl
                               LpRRVq_ball_sym
                               LpRRVq_ball_trans.

      Canonical LpRRVq_UniformSpace :=
        UniformSpace.Pack (LpRRVq p) LpRRVq_UniformSpace_mixin (LpRRVq p).

      Canonical LpRRVq_NormedModuleAux :=
        NormedModuleAux.Pack R_AbsRing (LpRRVq p)
                             (NormedModuleAux.Class R_AbsRing (LpRRVq p)
                                                    (ModuleSpace.class _ LpRRVq_ModuleSpace)
                                                    (LpRRVq_UniformSpace_mixin)) (LpRRVq p).

      
      Definition LpRRVq_norm : (LpRRVq p) -> R
        := quot_rec LpRRV_norm_proper.

      Lemma LpRRVq_normE x : LpRRVq_norm (Quot _ x)  = LpRRVnorm x.
      Proof.
        apply quot_recE.
      Qed.

      Hint Rewrite LpRRVq_normE : quot.

      Lemma LpRRVq_norm_plus (x y:LpRRVq p) : LpRRVq_norm (LpRRVq_plus x y) <= LpRRVq_norm x + LpRRVq_norm y.
      Proof.
        LpRRVq_simpl.
        now apply LpRRV_norm_plus.
      Qed.
      
      Lemma LpRRVq_norm_scal_strong (x:R) (y:LpRRVq p) : LpRRVq_norm (LpRRVq_scale x y) = Rabs x * LpRRVq_norm y.
      Proof.
        LpRRVq_simpl.
        now apply LpRRV_norm_scal_strong.
      Qed.

      Lemma LpRRVq_norm_scal x (y:LpRRVq p) : LpRRVq_norm (LpRRVq_scale x y) <= Rabs x * LpRRVq_norm y.
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

      Lemma LpRRVq_minus_minus (x y : LpRRVq p) :
        minus x y = LpRRVq_minus x y.
      Proof.
        unfold minus, plus, opp; simpl.
        LpRRVq_simpl.
        apply LpRRVminus_plus.
      Qed.

      Lemma LpRRVq_close_close (x y : LpRRVq p) (eps : R) :
        LpRRVq_norm (minus y x) < eps ->
        LpRRVq_ball x eps y.
      Proof.
        intros.
        rewrite LpRRVq_minus_minus in H.
        LpRRVq_simpl.
        now apply LpRRV_close_close.
      Qed.

      Lemma LpRRVq_norm_ball_compat (x y : LpRRVq p) (eps : posreal) :
        LpRRVq_ball x eps y -> LpRRVq_norm (minus y x) < LpRRVnorm_factor * eps.
      Proof.
        intros.
        rewrite LpRRVq_minus_minus.
        LpRRVq_simpl.
        now apply LpRRV_norm_ball_compat.
      Qed.
 
      Definition LpRRVq_NormedModule_mixin : NormedModule.mixin_of R_AbsRing LpRRVq_NormedModuleAux
        := NormedModule.Mixin R_AbsRing LpRRVq_NormedModuleAux
                              LpRRVq_norm
                              LpRRVnorm_factor
                              LpRRVq_norm_plus
                              LpRRVq_norm_scal
                              LpRRVq_close_close
                              LpRRVq_norm_ball_compat
                              LpRRVq_norm0.

      Definition LpRRVq_NormedModule :=
        NormedModule.Pack R_AbsRing (LpRRVq p)
                          (NormedModule.Class R_AbsRing (LpRRVq p)
                                              (NormedModuleAux.class _ LpRRVq_NormedModuleAux)
                                              LpRRVq_NormedModule_mixin)
                          (LpRRVq p).


    End quotbigp.

  End packedbigp.

    Global Arguments LpRRV : clear implicits.
    Global Arguments LpRRVq : clear implicits.

End Lp.

Hint Rewrite LpRRVq_constE : quot.
Hint Rewrite LpRRVq_zeroE : quot.
Hint Rewrite LpRRVq_scaleE : quot.
Hint Rewrite LpRRVq_oppE : quot.
Hint Rewrite LpRRVq_plusE : quot.
Hint Rewrite LpRRVq_minusE : quot.
Hint Rewrite @LpRRVq_constE : quot.
Hint Rewrite @LpRRVq_zeroE : quot.
Hint Rewrite @LpRRVq_scaleE : quot.
Hint Rewrite @LpRRVq_oppE : quot.
Hint Rewrite @LpRRVq_plusE : quot.
Hint Rewrite @LpRRVq_minusE : quot.
Hint Rewrite @LpRRVq_constE : quot.
Hint Rewrite LpRRVq_normE : quot.

Global Arguments LpRRVq_AbelianGroup {Ts} {dom} prts p.
Global Arguments LpRRVq_ModuleSpace {Ts} {dom} prts p.

Global Arguments LpRRVq_UniformSpace {Ts} {dom} prts p.
Global Arguments LpRRVq_NormedModule {Ts} {dom} prts p.

Ltac LpRRVq_simpl :=
  repeat match goal with
         | [H: LpRRVq _ _ |- _ ] =>
           let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
         | [H: AbelianGroup.sort (LpRRVq_AbelianGroup _ _ _) |- _ ] =>
           let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
         | [H: ModuleSpace.sort R_Ring (LpRRVq_ModuleSpace _ _) |- _ ] =>
           let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
         end
  ; try autorewrite with quot in *
  ; try apply (@eq_Quot _ _ (LpRRV_eq_equiv _)).

Ltac LpRRV_simpl
  := repeat match goal with
            | [H : LpRRV _ _ |- _ ] => destruct H as [???]
            end
     ; unfold LpRRVplus, LpRRVminus, LpRRVopp, LpRRVscale
     ; simpl
.
