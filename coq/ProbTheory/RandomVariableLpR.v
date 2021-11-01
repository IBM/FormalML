Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.
Require Import PropExtensionality.

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Export RandomVariableFinite.
Require Import quotient_space.
Require Import RbarExpectation.

Require Import Almost.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

(** This defines the space Lp (https://en.wikipedia.org/wiki/Lp_space) for finite p. 
    This is the space of RandomVariables, where the pth power of its absolute value
    has a finite expectation, module (quotiented by) the a.e relation.
    The a.e. (almostR2 equal) relation is an equivalence relation  that equates random variables
    that are equal with probablity 1.
*)
(**
   There are differences depending on $p$.  The world splits into a couple cases:
   nonnegative p: Lp is a module space (vector space)
     p = 0: nothing extra :-). Note that this is the space of all RandomVariables modulo a.e.
     0 < p < 1: not done yet.
     1 <= p: This is a complete normed vector space.
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

  Lemma IsLp_proper_almostR2 n rv_X1 rv_X2
        {rrv1:RandomVariable dom borel_sa rv_X1}
        {rrv2:RandomVariable dom borel_sa rv_X2}
        {islp1:IsLp n rv_X1}
    :
      almostR2 prts eq rv_X1 rv_X2 ->
      IsLp n rv_X2.
  Proof.
    unfold IsLp in *.
    red; intros.
    eapply (IsFiniteExpectation_proper_almostR2 _ (rvpower (rvabs rv_X1) (const n)))
    ; try eapply islp; trivial
    ; try typeclasses eauto.
    now rewrite H.
  Qed.

  Definition IsLp_Rbar n (rv_X:Ts->Rbar)
    := is_finite (Rbar_NonnegExpectation
                    (fun omega => Rbar_power (Rbar_abs (rv_X omega)) n )).

  Global Instance IsLp_Rbar_proper
    : Proper (eq ==> rv_eq ==> iff) IsLp_Rbar.
  Proof.
    intros ?? eqq1 x y eqq2.
    unfold IsLp_Rbar.
    rewrite eqq1.
    rewrite Rbar_NonnegExpectation_ext with (nnf2 := power_abs_pos y y0).
    tauto.
    intro xx.
    now rewrite eqq2.
  Qed.

  Global Instance almostR2_eq_Rbar_power_proper :
   Proper (almostR2 prts eq ==> eq ==> almostR2 prts eq) Rbar_rvpower.
Proof.
  intros x1 x2 eqq1 ? n ?; subst.
  apply (almostR2_sub prts eq (fun x => Rbar_rvpower x n)); trivial.
  intros.
  unfold Rbar_rvpower, Rbar_power.
  now rewrite H.
Qed.

Global Instance almostR2_eq_Rbar_abs_proper :
  Proper (almostR2 prts eq ==> almostR2 prts eq) Rbar_rvabs.
Proof.
  eapply almostR2_sub; eauto; try typeclasses eauto.
  intros.
  unfold Rbar_rvabs.
  now rewrite H.
Qed.


    Lemma Rbar_Expectation_proper_almostR2 (rv_X1 rv_X2 : Ts -> Rbar)
        (rv1pos: Rbar_NonnegativeFunction rv_X1)
        (rv2pos: Rbar_NonnegativeFunction rv_X2):
        almostR2 prts eq rv_X1 rv_X2 ->
        Rbar_NonnegExpectation rv_X1 = 
        Rbar_NonnegExpectation rv_X2.
  Proof.
    unfold almostR2; intros.
    destruct H as [P [? ?]].
    assert (dec:forall x: Ts, {P x} + {~ P x}).
    {
      intros.
      apply ClassicalDescription.excluded_middle_informative.
    }
    assert (0 < ps_P P) by lra.
    generalize (event_restricted_Rbar_NonnegExpectation prts P H H1 rv_X1 rv1pos); intros.
    generalize (event_restricted_Rbar_NonnegExpectation prts P H H1 rv_X2 rv2pos); intros.
    rewrite H2, H3.
    apply Rbar_NonnegExpectation_ext.
    intro x.
    unfold event_restricted_function.
    destruct x.
    simpl.
    now apply H0.
  Qed.

  Lemma IsLp_Rbar_proper_almostR2 n (rv_X1 rv_X2 : Ts -> Rbar)
        {islp1:IsLp_Rbar n rv_X1} :
      almostR2 prts eq rv_X1 rv_X2 ->
      IsLp_Rbar n rv_X2.
  Proof.
    unfold IsLp_Rbar in *; intros.
    assert (Rbar_NonnegativeFunction
              (fun omega : Ts => Rbar_power (Rbar_abs (rv_X1 omega)) n)) by
        apply power_abs_pos.
    erewrite Rbar_Expectation_proper_almostR2; trivial.
    unfold almostR2 in *.
    destruct H as [P [? ?]].
    exists P.
    split; trivial.
    intros.
    now rewrite H1.
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
      - rewrite e.
        rewrite Rabs_R0.
        match_destr.
        lra.
      - generalize (Rabs_pos (rv_X a)); intros.
        match_destr.
        + assert (e: Rabs (rv_X a) = 0) by lra.
          apply Rabs_eq_0 in e; congruence.          
        + rewrite Rpower_O; trivial; lra.
    } 
    rewrite eqq.
    typeclasses eauto.
  Qed.

  Lemma IsL1_Finite (rv_X:Ts->R)
(*         {rrv:RandomVariable dom borel_sa rv_X} *)
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
(*        {rv:RandomVariable dom borel_sa rv_X} *) : 
    is_finite (NonnegExpectation (rvabs rv_X)) ->
    is_finite (NonnegExpectation (neg_fun_part rv_X)).
  Proof.
    apply Finite_NonnegExpectation_le.
    apply neg_fun_part_le.
  Qed.
  
  Lemma Expectation_pos_part_finite (rv_X : Ts -> R)
        {isfe:IsFiniteExpectation prts rv_X} :
    is_finite (NonnegExpectation (pos_fun_part rv_X)).
  Proof.
    red in isfe.
    unfold Expectation in isfe.
    destruct (NonnegExpectation (fun x : Ts => pos_fun_part rv_X x)).
    destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x)).     
    now unfold is_finite.
    simpl in isfe; tauto.
    simpl in isfe; tauto.     
    destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x));
      simpl in isfe; tauto.
    destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x));
      simpl in isfe; tauto.
  Qed.

  Lemma Expectation_neg_part_finite (rv_X : Ts -> R)
        {isfe:IsFiniteExpectation prts rv_X} :
    is_finite (NonnegExpectation (neg_fun_part rv_X)).
  Proof.
    red in isfe.
    unfold Expectation in isfe.
    destruct (NonnegExpectation (fun x : Ts => pos_fun_part rv_X x)).
    destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x)).     
    now unfold is_finite.
    simpl in isfe; tauto.
    simpl in isfe; tauto.     
    destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x));
      simpl in isfe; tauto.
    destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x));
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
    c > 0 ->
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
    - apply Rabs_pos_lt.
      now apply Rgt_not_eq.
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

  Lemma big_nneg n (nbig: 1 <= n) : 0 <= n.
  Proof.
    lra.
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
    
    Definition LpRRV_seq (rv1 rv2:LpRRV) (* strict equality *)
      := rv_eq (LpRRV_rv_X rv1) (LpRRV_rv_X rv2).

    Definition LpRRV_eq (rv1 rv2:LpRRV)
      := almostR2 prts eq rv1 rv2.

    Global Instance LpRRV_seq_eq : subrelation LpRRV_seq LpRRV_eq.
    Proof.
      red; unfold LpRRV_seq, LpRRV_eq, rv_eq.
      intros x y eqq.
      now apply almostR2_eq_subr.
    Qed.      
    
    Global Instance LpRRV_seq_equiv : Equivalence (LpRRV_seq).
    Proof.
      unfold LpRRV_seq.
      apply Equivalence_pullback.
      apply rv_eq_equiv.
    Qed.

    Global Instance LpRRV_eq_equiv : Equivalence LpRRV_eq.
    Proof.
      unfold LpRRV_eq.
      constructor.
      - intros [x?].
        reflexivity.
      - intros [x?] [y?] ps1; simpl in *.
        now symmetry.
      - intros [x??] [y??] [z??] ps1 ps2.
        simpl in *.
        etransitivity; eauto.
    Qed.

    Definition LpRRVconst (x:R) : LpRRV
      := pack_LpRRV (const x).

    Definition LpRRVzero : LpRRV := LpRRVconst 0.

    Program Definition LpRRVscale (x:R) (rv:LpRRV) : LpRRV
      := pack_LpRRV (rvscale x rv).

    Global Instance LpRRV_scale_sproper : Proper (eq ==> LpRRV_seq ==> LpRRV_seq) LpRRVscale.
    Proof.
      unfold Proper, respectful, LpRRV_eq.
      intros ? x ? [x1??] [x2??] eqqx.
      subst.
      simpl in *.
      unfold rvscale.
      red.
      simpl.
      red in eqqx.
      simpl in *.
      now rewrite eqqx.
    Qed.

    Global Instance LpRRV_scale_proper : Proper (eq ==> LpRRV_eq ==> LpRRV_eq) LpRRVscale.
    Proof.
      unfold Proper, respectful, LpRRV_eq.
      intros ? x ? [x1??] [x2??] eqqx.
      subst.
      simpl in *.
      rewrite eqqx.
      reflexivity.
    Qed.

    Definition LpRRVopp (rv:LpRRV) : LpRRV
      := pack_LpRRV (rvopp rv).
    
    Global Instance LpRRV_opp_sproper : Proper (LpRRV_seq ==> LpRRV_seq) LpRRVopp.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      generalize (LpRRV_scale_sproper (-1) _ (eq_refl _) _ _ eqq)
      ; intros HH.
      destruct x as [x?]
      ; destruct y as [y?].
      apply HH.
    Qed.

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
      reflexivity.
    Qed.

    Definition LpRRVabs (rv:LpRRV) : LpRRV
      := pack_LpRRV (rvabs rv).

    Global Instance LpRRV_abs_sproper : Proper (LpRRV_seq ==> LpRRV_seq) LpRRVabs.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      red in eqq.
      red; simpl.
      now rewrite eqq.
    Qed.

    Global Instance LpRRV_abs_proper : Proper (LpRRV_eq ==> LpRRV_eq) LpRRVabs.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      now apply almostR2_eq_abs_proper.
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
        := quot_lift (LpRRVscale x).

      Lemma LpRRVq_scaleE x y : LpRRVq_scale x (Quot _ y)  = Quot _ (LpRRVscale x y).
      Proof.
        apply quot_liftE.
      Qed.

      Hint Rewrite LpRRVq_scaleE : quot.
      
      Definition LpRRVq_opp  : LpRRVq -> LpRRVq
        := quot_lift LpRRVopp.

      Lemma LpRRVq_oppE x : LpRRVq_opp (Quot _ x)  = Quot _ (LpRRVopp x).
      Proof.
        apply quot_liftE.
      Qed.

      Hint Rewrite LpRRVq_oppE : quot.
      
      Definition LpRRVq_abs  : LpRRVq -> LpRRVq
        := quot_lift LpRRVabs.

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

    Global Instance LpRRV_plus_sproper : Proper (LpRRV_seq ==> LpRRV_seq ==> LpRRV_seq) LpRRVplus.
    Proof.
      unfold Proper, respectful, LpRRV_seq.
      intros [x1??] [x2??] eqqx [y1??] [y2??] eqqy.
      simpl in *.
      simpl in *.
      now rewrite eqqx, eqqy.
    Qed.

    Global Instance LpRRV_plus_proper : Proper (LpRRV_eq ==> LpRRV_eq ==> LpRRV_eq) LpRRVplus.
    Proof.
      unfold Proper, respectful, LpRRV_eq.
      intros [x1??] [x2??] eqqx [y1??] [y2??] eqqy.
      simpl in *.
      now apply almostR2_eq_plus_proper.
    Qed.

    Definition LpRRVminus (rv1 rv2:LpRRV p) : LpRRV p
      := pack_LpRRV (rvminus rv1 rv2).

    Lemma LpRRVminus_plus (rv1 rv2:LpRRV p) :
      LpRRV_seq 
        (LpRRVminus rv1 rv2) (LpRRVplus rv1 (LpRRVopp rv2)).
    Proof.
      intros ?.
      reflexivity.
    Qed.

    Lemma LpRRValmost_sub_zero_eq (x y:LpRRV p)
      (eqq: almostR2 prts eq (LpRRVminus x y) (LpRRVzero (p:=p))) :
      almostR2 prts eq x y.
    Proof.
      generalize (almostR2_eq_plus_proper prts _ _ eqq _ _ (reflexivity y))
      ; intros HH.
      transitivity (rvplus (LpRRVzero (p:=p)) y).
      - rewrite <- HH.
        apply almostR2_eq_subr.
        intros ?; simpl.
        rv_unfold.
        lra.
      - apply almostR2_eq_subr.
        intros ?; simpl.
        rv_unfold.
        lra.
    Qed.
    
    Global Instance LpRRV_minus_sproper : Proper (LpRRV_seq ==> LpRRV_seq ==> LpRRV_seq) LpRRVminus.
    Proof.
      unfold Proper, respectful, LpRRV_seq.

      intros x1 x2 eqq1 y1 y2 eqq2; simpl.
      now rewrite eqq1, eqq2.
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
      apply almostR2_eq_subr; intros ?.
      unfold rvplus; lra.
    Qed.
    
    Lemma LpRRV_plus_assoc (x y z : LpRRV p) : LpRRV_eq (LpRRVplus x (LpRRVplus y z)) (LpRRVplus (LpRRVplus x y) z).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply almostR2_eq_subr; intros ?.
      unfold rvplus.
      lra.
    Qed.

    Lemma LpRRV_plus_zero (x : LpRRV p) : LpRRV_eq (LpRRVplus x (LpRRVconst 0)) x.
    Proof.
      red; intros.
      LpRRV_simpl.
      apply almostR2_eq_subr; intros ?.
      unfold rvplus, const.
      lra.
    Qed.

    Lemma LpRRV_plus_inv (x: LpRRV p) : LpRRV_eq (LpRRVplus x (LpRRVopp x)) (LpRRVconst 0).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply almostR2_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const.
      lra.
    Qed.

    Lemma LpRRV_scale_scale (x y : R) (u : LpRRV p) :
      LpRRV_eq (LpRRVscale x (LpRRVscale y u)) (LpRRVscale (x * y) u).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply almostR2_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    Lemma LpRRV_scale1 (u : LpRRV p) :
      LpRRV_eq (LpRRVscale one u) u.
    Proof.
      red; intros.
      LpRRV_simpl.
      apply almostR2_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult, one; simpl.
      lra.
    Qed.
    
    Lemma LpRRV_scale_plus_l (x : R) (u v : LpRRV p) :
      LpRRV_eq (LpRRVscale x (LpRRVplus u v)) (LpRRVplus (LpRRVscale x u) (LpRRVscale x v)).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply almostR2_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.
    
    Lemma LpRRV_scale_plus_r (x y : R) (u : LpRRV p) :
      LpRRV_eq (LpRRVscale (x + y) u) (LpRRVplus (LpRRVscale x u) (LpRRVscale y u)).
    Proof.
      red; intros.
      LpRRV_simpl.
      apply almostR2_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    (* Lp is a module space for all finite nonnegative p *)
    Section quotnneg.

      Definition LpRRVq_plus  : LpRRVq p -> LpRRVq p -> LpRRVq p
        := quot_lift2 LpRRVplus.
      
      Lemma LpRRVq_plusE x y : LpRRVq_plus (Quot _ x) (Quot _ y) = Quot _ (LpRRVplus x y).
      Proof.
        apply quot_lift2E.
      Qed.

      Hint Rewrite LpRRVq_plusE : quot.

      Definition LpRRVq_minus  : LpRRVq p -> LpRRVq p -> LpRRVq p
        := quot_lift2 LpRRVminus.

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
        now rewrite LpRRVminus_plus.
      Qed.

      Lemma LpRRVq_opp_scale (rv:LpRRVq p) :
        LpRRVq_opp rv = LpRRVq_scale (-1) rv.
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
        p = 0       => This is the space of Random Variables modulo almostR2-equal.  
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
        eapply FiniteExpectation_proper_almostR2
        ; try typeclasses eauto.
        rewrite H.
        reflexivity.
      Qed.

      Global Instance LpRRV_norm_sproper : Proper (LpRRV_seq ==> eq) LpRRVnorm.
      Proof.
        unfold Proper, respectful; intros.
        now rewrite H.
      Qed.

      Lemma almostR20_lpf_almostR20 (rv_X:Ts->R)
            {rrv:RandomVariable dom borel_sa rv_X}
            {isfe: IsFiniteExpectation prts (rvpower (rvabs rv_X) (const p))}:
        almostR2 prts eq rv_X (const 0) <->
        almostR2 prts eq (rvpower (rvabs rv_X) (const p)) (const 0).
      Proof.
        intros.
      unfold almostR2 in *.
      split; intros [P [Pall eq_on]]
      ; exists P; split; trivial
      ; intros a Pa
      ; rv_unfold.
      - rewrite eq_on by trivial.
        now rewrite Rabs_R0, power0_Sbase.
      - specialize (eq_on _ Pa).
        apply power_integral in eq_on.
        generalize (Rabs_pos (rv_X a)); intros.
        apply Rabs_eq_0.
        lra.
      Qed.

      (* If the norm is 0 then p is a.e. 0 *)
      Theorem LpFin0_almostR20 (rv_X:Ts->R)
            {rrv:RandomVariable dom borel_sa rv_X}
            {isfe: IsFiniteExpectation prts (rvpower (rvabs rv_X) (const p))}:
        FiniteExpectation prts (rvpower (rvabs rv_X) (const p)) = 0 ->
        almostR2 prts eq rv_X (const 0).
      Proof.
        intros fin0.
        eapply FiniteExpectation_zero_pos in fin0
        ; try typeclasses eauto.
        now apply almostR20_lpf_almostR20
        ; try typeclasses eauto.
      Qed.

      Lemma LpRRV_norm0 (x:LpRRV p) :
        LpRRVnorm x = 0 ->
        almostR2 prts eq x (LpRRVzero (p:=p)).
      Proof.
        unfold LpRRVnorm, LpRRVzero, LpRRVconst.
        intros.
        apply power_integral in H.
        generalize (FiniteExpectation_Lp_pos p x); intros.
        assert (FiniteExpectation prts (rvpower (rvabs x) (const p)) = 0)
          by now apply Rle_antisym.
        now apply  LpFin0_almostR20 in H1; try typeclasses eauto.
      Qed.
      
      Lemma LpRRVnorm_const c : p <> 0 -> LpRRVnorm (LpRRVconst c) = Rabs c.
      Proof.
        intros.
        unfold LpRRVnorm; simpl.
        rv_unfold.
        generalize (FiniteExpectation_const prts (power (Rabs c) p))
        ; intros HH.
        unfold const in HH.
        erewrite FiniteExpectation_pf_irrel.
        rewrite HH.
        apply inv_power_cancel; trivial.
        apply Rabs_pos.
      Qed.
  
      Lemma LpRRVnorm0 : p <> 0 -> LpRRVnorm LpRRVzero = 0.
      Proof.
        intros.
        unfold LpRRVzero.
        rewrite LpRRVnorm_const; trivial.
        now rewrite Rabs_R0.
      Qed.

    End normish.

    Definition LpRRVpoint (p:R) : LpRRV p := LpRRVconst 0.

    Definition bignneg n (nbig: 1 <= n) : nonnegreal
      := mknonnegreal n (big_nneg n nbig).

    Section packedbigp.
      Context {p:R}.
      Context (pbig:1 <= p).

      Let pnneg : nonnegreal := bignneg p pbig.
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
              eapply LpFin0_almostR20 in H0; try typeclasses eauto.
              rewrite (FiniteExpectation_proper_almostR2 prts (rvpower (rvabs (rvplus x y)) (const p)) (rvpower (rvabs x) (const p))).
              + lra.
              + rewrite H0.
                apply almostR2_eq_subr.
                intros ?.
                rv_unfold.
                repeat f_equal.
                lra.
          }                                                    
        - rewrite <- H.
          rewrite power0_Sbase
            by (apply Rinv_neq_0_compat; lra).
          symmetry in H.
          eapply LpFin0_almostR20 in H; try typeclasses eauto.
          rewrite (FiniteExpectation_proper_almostR2 prts (rvpower (rvabs (rvplus x y)) (const p)) (rvpower (rvabs y) (const p))).
          + lra.
          + rewrite H.
            apply almostR2_eq_subr.
            intros a.
            rv_unfold.
            repeat f_equal.
            lra.
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


      Global Instance LpRRV_ball_sproper : Proper (LpRRV_seq ==> eq ==> LpRRV_seq ==> iff) LpRRVball.
      Proof.
        intros ?? eqq1 ?? eqq2 ?? eqq3.
        unfold LpRRVball in *.
        rewrite <- eqq1, <- eqq2, <- eqq3.
        reflexivity.
      Qed.

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
        apply almostR2_eq_subr.
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
        intros.
        induction n.
        - assert (rv_eq (rvsum rv_X 0%nat)
                        (rv_X 0%nat)).
          + intros ?.
            unfold rvsum.
            now rewrite sum_O.
          + now rewrite H.
        - assert (rv_eq (rvsum rv_X (S n)) (rvplus (rvsum rv_X n) (rv_X (S n)))).
          + intros ?.
            unfold rvsum, sum_n, rvplus.
            rewrite sum_n_Sm; [|lia].
            reflexivity.
          + rewrite H.
            typeclasses eauto.
      Qed.

      Definition LpRRVsum (rvn:nat -> LpRRV p) (n:nat) : LpRRV p
        := pack_LpRRV (rvsum rvn n).

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
          + apply almostR2_eq_subr.
            intro x.
            unfold LpRRVsum; simpl.
            unfold rvsum.
            now rewrite sum_O.
          + rewrite H; lra.
        - rewrite sum_n_Sm; [|lia].
          assert (LpRRV_eq (LpRRVsum f (S n)) (LpRRVplus (LpRRVsum f n) (f (S n)))).
          + apply almostR2_eq_subr.
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

      Lemma power_inv_le b q c :
            0 < q -> 0 <= b -> 0 <= c ->
            power b (/ q) <= c ->
            b <= power c q.
      Proof.
        intros.
        replace c with (power (power c q) (/q)) in H2.
        apply power_incr_inv in H2; trivial.
        now apply Rinv_0_lt_compat.
        apply power_nonneg.
        apply inv_power_cancel; lra.
      Qed.

      Lemma isfin_Lim_seq (f : nat -> Ts -> R) :
        (forall (omega:Ts), ex_finite_lim_seq (fun n => f n omega)) ->
        forall (omega:Ts), is_finite (Lim_seq (fun n => f n omega)).
      Proof.
        intros.
        now apply ex_finite_lim_seq_correct.
      Qed.

      Lemma rvlim_incr (f : nat -> LpRRV p)  :
        (forall (n:nat), NonnegativeFunction  (f n)) ->
        (forall (n:nat), rv_le (f n) (f (S n))) ->
        (forall (omega:Ts), ex_finite_lim_seq (fun n => f n omega)) ->
        (forall (n:nat), rv_le (f n) (rvlim f)).
      Proof.
        unfold rv_le, pointwise_relation, rvlim; intros.
        generalize (Lim_seq_le_loc (fun _ => f n a) (fun n0 => f n0 a)); intros.
        cut_to H2.
        rewrite Lim_seq_const in H2.
        generalize (isfin_Lim_seq _ H1); intros.
        now rewrite <- (H3 a) in H2.
        exists n; intros.
        now apply (incr_le_strong (fun n => f n a)).
      Qed.

      Definition p_power (x:R) := (power x p).

      Lemma continuity_p_power_pos (x : R) :
        0 < x ->
        continuity_pt p_power x.
      Proof.
        intros.
        unfold p_power.
        generalize (continuity_pt_filterlim); intros.
        apply derivable_continuous_pt.
        generalize (derivable_pt_lim_power' x p H); intros.
        unfold derivable_pt, derivable_pt_abs.
        eauto.
      Qed.

      (* implicitly assumes p > 0 *)
      Lemma continuity_p_power_Rabs (x : R) :
        continuity_pt (fun x0 => p_power (Rabs x0)) x.
      Proof.
        destruct (Req_dec x 0).
        - unfold p_power.
          repeat red; intros.
          exists (power eps (/ p)).
          split; [apply power_pos; lra | ].
          unfold dist; simpl; unfold R_dist.
          intros; subst.
          rewrite Rabs_R0.
          rewrite Rminus_0_r in H1.
          destruct H1.
          rewrite power0_Sbase, Rminus_0_r.
          rewrite Rabs_right; [| apply Rle_ge, power_nonneg].
          replace (eps) with (power (power eps (/p)) p) by (apply power_inv_cancel; lra).
          apply Rlt_power_l; [lra |].
          split; trivial.
          apply Rabs_pos.
        - apply continuity_pt_comp with (f2 := p_power).
          generalize Rcontinuity_abs.
          now unfold continuity.
          apply continuity_p_power_pos.
          generalize (Rabs_pos x); intros.
          destruct H0; trivial.
          symmetry in H0; apply Rabs_eq_0 in H0.
          lra.
      Qed.

      (* need stronger version of monotone_convergence to remove
         is_finite (Lim_seq (fun n : nat => f n omega))) hypothesis *)
      Lemma islp_rvlim_bounded (f : nat -> LpRRV p) (c : R) :
        (forall (n:nat), LpRRVnorm (f n) <= c) ->
        (forall (n:nat), RandomVariable dom borel_sa (f n)) ->
        (forall (n:nat), NonnegativeFunction  (f n)) ->
        (forall (n:nat), rv_le (f n) (f (S n))) ->
        (forall (omega:Ts), ex_finite_lim_seq (fun n : nat => f n omega)) ->
        IsLp p (rvlim f).
      Proof.
        intros fnorm f_rv fpos fincr exfinlim.
        assert (cpos: 0 <= c).
        {
          specialize (fnorm 0%nat).
          apply Rle_trans with (r2 := (LpRRVnorm (f 0%nat))); trivial.
          unfold LpRRVnorm.
          apply power_nonneg.
        }
        generalize (isfin_Lim_seq _ exfinlim); intros isfin_flim.
        unfold LpRRVnorm in fnorm.
        unfold IsLp.
        assert (finexp: forall n, FiniteExpectation prts (rvpower (rvabs (f n)) (const p)) <= 
                                  power c p).
        {
        intros.
        apply power_inv_le; trivial.
        lra.
        apply FiniteExpectation_Lp_pos.

        }
        assert (forall n, NonnegativeFunction (rvpower (rvabs (f n)) (const p))).
        {
          intros.
          unfold NonnegativeFunction, rvpower; intros.
          apply power_nonneg.
        }
        assert (rvlim_rv: RandomVariable dom borel_sa (rvpower (rvabs (rvlim (fun x : nat => f x))) (const p))).
        apply rvpower_rv.
        apply rvabs_rv.
        apply rvlim_rv; trivial.
        typeclasses eauto.
        generalize ( monotone_convergence 
                      (rvpower (rvabs (rvlim (fun x : nat => f x))) (const p))
                      (fun n => (rvpower (rvabs (f n)) (const p))) _ _ _ _); intro monc.

        cut_to monc.
        - unfold IsFiniteExpectation.
          assert (NonnegativeFunction  (rvpower (rvabs (rvlim (fun x : nat => f x))) (const p))).
          {
            unfold NonnegativeFunction, rvpower; intros.
            apply power_nonneg.            
          }
          rewrite Expectation_pos_pofrf with (nnf := H0).
          assert (Rbar_le
                    (Lim_seq (fun n : nat => NonnegExpectation (rvpower (rvabs (f n)) (const p)))) (power c p)).
          replace (Finite (power c p)) with (Lim_seq (fun _ => power c p)).
          apply Lim_seq_le_loc.
          exists (0%nat).
          intros.
          specialize (finexp n).
          now rewrite FiniteNonnegExpectation with (posX := (H n)) in finexp.
          apply Lim_seq_const.
          rewrite monc in H1.
          cut (is_finite (NonnegExpectation (rvpower (rvabs (rvlim (fun x : nat => f x))) (const p)))).
          + intros eqq; now rewrite <- eqq.
           + eapply bounded_is_finite.
            * eapply NonnegExpectation_pos.
            * eapply H1.
        - intros n x.
          unfold rvpower.
          apply Rle_power_l; [ unfold const; lra |].
          split; [apply Rabs_pos |].
          unfold rvabs.
          rewrite Rabs_right by apply Rle_ge, fpos.
          rewrite Rabs_right.
          apply rvlim_incr; trivial.
          apply Rge_trans with (r2 := f n x).
          + apply Rle_ge.
            apply rvlim_incr; trivial.
          + apply Rle_ge, fpos.
        - intros n x.
          apply Rle_power_l.
          + unfold const; lra.
          + unfold rvabs.
            split; [apply Rabs_pos |].
            rewrite Rabs_right by apply Rle_ge, fpos.
            rewrite Rabs_right by apply Rle_ge, fpos.
            apply fincr.
        - intros; apply IsFiniteNonnegExpectation.
          apply (@LpRRV_LpS_FiniteLp p (f n)).
        - intros.
          unfold rvpower, rvabs, rvlim, const.
          apply is_lim_seq_ext with (u := fun n : nat => p_power (Rabs (f n omega))).
          now unfold p_power.
          apply is_lim_seq_continuous with (f := fun x => p_power (Rabs x)).
          apply continuity_p_power_Rabs.
          generalize (Lim_seq_correct (fun n : nat => f n omega)); intros.
          rewrite <- (isfin_flim omega) in H0.
          apply H0.
          apply ex_lim_seq_incr.
          now unfold rv_le, pointwise_relation in fincr.
        Qed.


      Lemma is_lim_power_inf (f : nat -> R) :
        is_lim_seq f p_infty -> is_lim_seq (fun n => power (f n) p) p_infty.
      Proof.
        do 2 rewrite <- is_lim_seq_spec.
        unfold is_lim_seq'; intros.
        specialize (H (power (Rmax M 0) (/p))).
        destruct H.
        exists x.
        intros.
        specialize (H n H0).
        apply Rle_lt_trans with (r2 := Rmax M 0).
        apply Rmax_l.
        replace (Rmax M 0) with (power (power (Rmax M 0) (/p)) p).
        apply Rlt_power_l.
        lra.
        split; trivial.
        apply power_nonneg.
        apply power_inv_cancel; try lra.
        apply Rmax_r.
      Qed.

      Lemma lim_power_inf (f : nat -> R) :
        ex_lim_seq f ->
        Lim_seq f = p_infty -> Lim_seq (fun n => power (f n) p) = p_infty.
      Proof.
        intros.
        apply Lim_seq_correct in H.
        rewrite H0 in H.
        apply is_lim_power_inf in H.
        now apply is_lim_seq_unique in H.
      Qed.

      Lemma Rbar_power_lim_comm (f : nat -> Ts -> R) (x:Ts) :
        (forall (n:nat), rv_le (f n) (f (S n))) ->
        Rbar_power (Rbar_abs (Lim_seq (fun n : nat => f n x))) p = Lim_seq (fun n : nat => power (Rabs (f n x)) p).
      Proof.
        intros.
        assert (exlim: ex_lim_seq (fun n => f n x)).
        {
          apply ex_lim_seq_incr.
          intros; apply H.
        }
        case_eq (Lim_seq (fun n : nat => f n x)); intros.
        - generalize (is_lim_seq_continuous (fun x => p_power (Rabs x)) (fun n => f n x) (Lim_seq (fun n => f n x))); intros.
          cut_to H1.
          + apply is_lim_seq_unique in H1.
            unfold p_power in H1.
            rewrite H0 in H1.
            rewrite H1.
            now simpl.
          + apply continuity_p_power_Rabs.
          + assert (is_finite (Lim_seq (fun n => f n x))) by now rewrite H0.
            rewrite H2.
            now apply Lim_seq_correct.
        - simpl; symmetry.
          generalize (ex_lim_seq_abs _ exlim); intros.
          apply lim_power_inf; trivial.
          rewrite Lim_seq_abs; trivial.
          rewrite H0.
          now simpl.
        - simpl; symmetry.
          generalize (ex_lim_seq_abs _ exlim); intros.
          apply lim_power_inf; trivial.
          rewrite Lim_seq_abs; trivial.
          rewrite H0.
          now simpl.
      Qed.

      (* stronger version monotone_convergence_Rbar allows us to remove
         is_finite (Lim_seq (fun n : nat => f n omega))) hypothesis *)
      Lemma islp_Rbar_rvlim_bounded (f : nat -> LpRRV p) (c : R) :
(*        0 <= c -> *)
        (forall (n:nat), LpRRVnorm (f n) <= c) ->
        (forall (n:nat), RandomVariable dom borel_sa (f n)) ->
        (forall (n:nat), NonnegativeFunction  (f n)) ->
        (forall (n:nat), rv_le (f n) (f (S n))) ->
        IsLp_Rbar p (Rbar_rvlim (fun n => LpRRV_rv_X (f n))).
      Proof.
        intros fnorm f_rv fpos fincr.
        assert (cpos: 0 <= c).
        {
          specialize (fnorm 0%nat).
          apply Rle_trans with (r2 := (LpRRVnorm (f 0%nat))); trivial.
          unfold LpRRVnorm.
          apply power_nonneg.
        }
        unfold LpRRVnorm in fnorm.
        unfold IsLp_Rbar.
        assert (finexp: forall n, FiniteExpectation prts (rvpower (rvabs (f n)) (const p)) <= 
                                  power c p).
        {
        intros.
        apply power_inv_le; trivial.
        lra.
        apply FiniteExpectation_Lp_pos.

        }
        assert (forall n, NonnegativeFunction (rvpower (rvabs (f n)) (const p))).
        {
          intros.
          unfold NonnegativeFunction, rvpower; intros.
          apply power_nonneg.
        }
        generalize ( monotone_convergence_Rbar_rvlim_fin
                      (fun n => (rvpower (rvabs (f n)) (const p))) _ _ ); intro monc.
        cut_to monc.
        - assert (Rbar_le
                    (ELim_seq (fun n : nat => NonnegExpectation (rvpower (rvabs (f n)) (const p)))) (power c p)).
          {
            replace (Finite (power c p)) with (ELim_seq (fun _ => power c p)).
            - apply ELim_seq_le_loc.
              apply filter_forall; intros n.
              specialize (finexp n).
              rewrite <- (FiniteNonnegExpectation_alt _ _).
              apply finexp.
            - apply ELim_seq_const.
          }
          rewrite monc in H0.
          assert (Rbar_NonnegativeFunction (Rbar_rvlim (fun n : nat => rvpower (rvabs (f n)) (const p)))) by typeclasses eauto.
          rewrite Rbar_NonnegExpectation_ext with (nnf2 := H1).
          + eapply bounded_is_finite.
            * eapply Rbar_NonnegExpectation_pos.
            * eapply H0.
          + intro x.
            unfold Rbar_rvlim, rvpower, rvabs, const.
            repeat rewrite Elim_seq_fin.
            apply (Rbar_power_lim_comm f x fincr).
        - intros n x.
          unfold rvpower.
          apply Rle_power_l; [ unfold const; lra |].
          split; [apply Rabs_pos |].
          unfold rvabs.
          rewrite Rabs_right by apply Rle_ge, fpos.
          rewrite Rabs_right.
          apply fincr.
          apply Rle_ge, fpos.
    Qed.

      Lemma LpRRVsum_pos (f : nat -> LpRRV p) (n : nat) :
        (forall n, NonnegativeFunction (f n)) ->
        NonnegativeFunction (LpRRVsum f n).
      Proof.
        unfold NonnegativeFunction.
        intros.
        unfold LpRRVsum, pack_LpRRV; simpl.
        unfold rvsum.
        induction n.
        - now rewrite sum_O.
        - rewrite sum_Sn.
          unfold rvplus, plus; simpl.
          now apply Rplus_le_le_0_compat.
      Qed.
          
      Lemma islp_lim_telescope_abs (f : nat -> LpRRV p) :
        (forall (n:nat), LpRRVnorm (LpRRVminus (f (S n)) (f n)) < / (pow 2 n)) ->
        (forall (n:nat), RandomVariable dom borel_sa (f n)) ->
        (forall omega : Ts,
            ex_finite_lim_seq
              (fun n : nat =>
                 LpRRVsum (fun n0 : nat => LpRRVabs (LpRRVminus (f (S n0)) (f n0))) n omega)) ->
        IsLp p (rvlim
                  (fun n => LpRRVsum (fun n0 => LpRRVabs (LpRRVminus (f (S n0)) (f n0))) n)).
      Proof.
        intros.
        apply islp_rvlim_bounded with (c := 2); try lra.
        intros.
        apply lp_telescope_norm_bound; trivial.
        - intros.
          typeclasses eauto.
        - intros.
          apply LpRRVsum_pos.
          typeclasses eauto.
        - intros n x.
          unfold LpRRVsum, pack_LpRRV; simpl.
          unfold rvsum.
          rewrite sum_Sn.
          apply Rplus_le_compat1_l.
          unfold rvabs.
          apply Rabs_pos.
        - apply H1.
      Qed.
      
      Lemma islp_Rbar_lim_telescope_abs_c (f : nat -> LpRRV p) (c : R) :
        (forall n : nat,
            LpRRVnorm
              (LpRRVsum (fun n0 : nat => LpRRVabs (LpRRVminus (f (S n0)) (f n0))) n) <= c) ->
        (forall (n:nat), RandomVariable dom borel_sa (f n)) ->
        IsLp_Rbar p (Rbar_rvlim
                  (fun n => LpRRV_rv_X (LpRRVsum (fun n0 => LpRRVabs (LpRRVminus (f (S n0)) (f n0))) n))).
      Proof.
        intros.
        apply islp_Rbar_rvlim_bounded with (c := c); trivial; try lra.
        - intros.
          typeclasses eauto.
        - intros.
          apply LpRRVsum_pos.
          typeclasses eauto.
        - intros n x.
          unfold LpRRVsum, pack_LpRRV; simpl.
          unfold rvsum.
          rewrite sum_Sn.
          apply Rplus_le_compat1_l.
          unfold rvabs.
          apply Rabs_pos.
      Qed.

      Lemma islp_Rbar_lim_telescope_abs (f : nat -> LpRRV p) :
        (forall (n:nat), LpRRVnorm (LpRRVminus (f (S n)) (f n)) < / (pow 2 n)) ->
        (forall (n:nat), RandomVariable dom borel_sa (f n)) ->
        IsLp_Rbar p (Rbar_rvlim
                  (fun n => LpRRV_rv_X (LpRRVsum (fun n0 => LpRRVabs (LpRRVminus (f (S n0)) (f n0))) n))).
      Proof.
        intros.
        apply islp_Rbar_lim_telescope_abs_c with (c := 2); trivial.
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

      Definition LpRRV_UniformSpace_mixin : UniformSpace.mixin_of (LpRRV p)
        := UniformSpace.Mixin  (LpRRV p) (LpRRVpoint p) LpRRVball
                               LpRRV_ball_refl
                               LpRRV_ball_sym
                               LpRRV_ball_trans.

      Canonical LpRRV_UniformSpace :=
        UniformSpace.Pack (LpRRV p) LpRRV_UniformSpace_mixin (LpRRV p).
      
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
        now rewrite LpRRVminus_plus.
      Qed.

      Lemma LpRRVq_minus_plus_opp
            (x y : LpRRVq p) :
        LpRRVq_minus x y = LpRRVq_plus x (LpRRVq_opp y).
      Proof.
        unfold minus, plus, opp; simpl.
        LpRRVq_simpl.
        now rewrite LpRRVminus_plus.
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

      Canonical LpRRVq_NormedModule :=
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

Global Arguments LpRRV_seq {Ts} {dom} {prts} {p} rv1 rv2.
(* Global Arguments LpRRV_eq {Ts} {dom}{prts} {p} rv1 rv2. *)

Section complete.
  Section complete1.

    Context {Ts:Type} 
            {dom: SigmaAlgebra Ts}
            (prts: ProbSpace dom).
    
    Context {p:R}.
    Context (pbig:1 <= p).

  Let pnneg : nonnegreal := bignneg p pbig.
  Canonical pnneg.

  Lemma LpRRV_norm_opp (x : LpRRV prts p) : LpRRVnorm prts (LpRRVopp prts x) = LpRRVnorm prts x.
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

     Lemma inv_pow_2_pos  (n : nat) :
        0 < / (2 ^ n) .
  Proof.
    apply Rinv_0_lt_compat.
    apply pow_lt.
    lra.
  Qed.

  Definition LpRRV_lim_ball_center_center 
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop) :
    ProperFilter F -> cauchy F ->
    forall (n:nat), 
      {b:LpRRV_UniformSpace prts pbig |
        F (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig) b (mkposreal _ (inv_pow_2_pos n)))}.
  Proof.
    intros Pf cF n.
    pose ( ϵ := / (2 ^ n)).
    assert (ϵpos : 0 < ϵ) by apply inv_pow_2_pos.
    destruct (constructive_indefinite_description _ (cF (mkposreal ϵ ϵpos)))
      as [x Fx].
    now exists x.
  Defined.

  Definition LpRRV_lim_ball_center 
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop) :
    ProperFilter F -> cauchy F ->
    forall (n:nat), {b:LpRRV prts p ->Prop | F b}.
  Proof.
    intros Pf cF n.
    pose ( ϵ := / (2 ^ n)).
    assert (ϵpos : 0 < ϵ) by apply inv_pow_2_pos.
    destruct (constructive_indefinite_description _ (cF (mkposreal ϵ ϵpos)))
      as [x Fx].
    simpl in *.
    now exists  (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig) x ϵ).
  Defined.

  Definition LpRRV_lim_ball_cumulative
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : {x:LpRRV prts p->Prop | F x}
    := fold_right (fun x y =>
                     exist _ _ (Hierarchy.filter_and
                       _ _ (proj2_sig x) (proj2_sig y)))
                  (exist _ _ Hierarchy.filter_true)
                  (map (LpRRV_lim_ball_center F PF cF) (seq 0 (S n))).

  Definition LpRRV_lim_picker
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : LpRRV prts p
    := (proj1_sig (
            constructive_indefinite_description
              _
              (filter_ex
                 _
                 (proj2_sig (LpRRV_lim_ball_cumulative F PF cF n))))).

  Definition LpRRV_lim_picker_ext0
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (n:nat) : LpRRV prts p
    := match n with
       | 0 => LpRRVzero prts
       | S n' => LpRRV_lim_picker F PF cF n
       end.

    Lemma lim_picker_cumulative_included
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N n:nat) :
      (N <= n)%nat ->
      forall x,
      proj1_sig (LpRRV_lim_ball_cumulative F PF cF n) x ->
       (proj1_sig (LpRRV_lim_ball_center F PF cF N)) x.
    Proof.
      unfold LpRRV_lim_ball_cumulative.
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
             (F : (LpRRV_UniformSpace prts pbig  -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N n:nat) :
    (N <= n)%nat ->
    (proj1_sig (LpRRV_lim_ball_center F PF cF N)) 
      (LpRRV_lim_picker F PF cF n).
  Proof.
    intros.
    unfold LpRRV_lim_picker.
    unfold proj1_sig at 2.
    match_destr.
    eapply lim_picker_cumulative_included; eauto.
  Qed.

  Lemma lim_ball_center_ball_center_center  (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (n:nat) :
    forall (x:UniformSpace.sort (LpRRV_UniformSpace prts pbig)),
      (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig)
                      (proj1_sig (LpRRV_lim_ball_center_center F PF cF n))
                      (mkposreal _ (inv_pow_2_pos n))) x

      <-> proj1_sig (LpRRV_lim_ball_center F PF cF n) x.
  Proof.
    unfold LpRRV_lim_ball_center; simpl.
    unfold LpRRV_lim_ball_center_center; simpl.
    intros.
    destruct ( constructive_indefinite_description
            (fun x0 : LpRRV prts p => F (Hierarchy.ball x0 (/ 2 ^ n)))
            (cF {| pos := / 2 ^ n; cond_pos := inv_pow_2_pos n |})); simpl.
    tauto.
  Qed.
    
  Lemma lim_picker_center_included
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (n:nat) :
    (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig)
                    (proj1_sig (LpRRV_lim_ball_center_center F PF cF n))
                    (mkposreal _ (inv_pow_2_pos n)))
      (LpRRV_lim_picker F PF cF n).
  Proof.
    simpl.
    apply lim_ball_center_ball_center_center.
    now apply lim_picker_included.
  Qed.

  Lemma lim_picker_center_included2
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (N:nat) :
    forall (n:nat), 
      (n >= N)%nat ->
      (Hierarchy.ball (M:= LpRRV_UniformSpace prts pbig)
                    (proj1_sig (LpRRV_lim_ball_center_center F PF cF N))
                    (mkposreal _ (inv_pow_2_pos N)))
      (LpRRV_lim_picker F PF cF n).
  Proof.
    intros.
    simpl.
    apply lim_ball_center_ball_center_center.
    apply lim_picker_included.
    lia.
  Qed.

  Lemma LpRRVq_opp_opp (x : LpRRVq_AbelianGroup prts (bignneg _ pbig)) :
    opp x = LpRRVq_opp prts x.
  Proof.
    unfold opp; simpl.
    LpRRVq_simpl.
    reflexivity.
  Qed.

  Lemma LpRRVq_minus_plus_opp'
        (x y : LpRRVq prts p) :
    LpRRVq_minus prts x y = LpRRVq_plus prts x (LpRRVq_opp prts y).
  Proof.
    unfold minus, plus, opp; simpl.
    LpRRVq_simpl.
    now rewrite LpRRVminus_plus.
  Qed.

  Lemma lim_ball_center_dist (x y : LpRRV prts p)
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N:nat) :
    (proj1_sig (LpRRV_lim_ball_center F PF cF N)) x ->
    (proj1_sig (LpRRV_lim_ball_center F PF cF N)) y ->
    LpRRVnorm prts (LpRRVminus prts x y) < 2 / 2 ^ N.
  Proof.
    unfold LpRRV_lim_ball_center; simpl.
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
      generalize (LpRRV_norm_plus prts pbig (LpRRVminus prts (p:=bignneg _ pbig) x x1) (LpRRVminus prts x1 y)); intros HH2.
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
      subst pnneg.
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
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    forall N : nat,
      forall n m : nat,
        (n >= N)%nat ->
        (m >= N)%nat -> 
        LpRRVnorm prts (LpRRVminus 
                            prts  
                            (LpRRV_lim_picker F PF cF n)
                            (LpRRV_lim_picker F PF cF m)) < 2 / 2 ^ N.
  Proof.
    intros.
    apply (lim_ball_center_dist _ _ F PF cF); now apply lim_picker_included.
  Qed.    
    
  Lemma cauchy_filter_sum_bound 
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) (pbigger:1 < p):
    ex_series (fun n => 
                 LpRRVnorm prts 
                             (LpRRVminus prts
                                (LpRRV_lim_picker F PF cF (S n))
                                (LpRRV_lim_picker F PF cF n))).
  Proof.
    apply (@ex_series_le R_AbsRing R_CompleteNormedModule) with
        (b := fun n => 2 / 2 ^ n).
    intros; unfold norm; simpl.
    unfold abs; simpl.
    rewrite Rabs_pos_eq.
    left.
    apply (lim_filter_cauchy F PF cF n (S n) n); try lia.
    unfold LpRRVnorm.
    apply power_nonneg.
    unfold Rdiv.
    apply (@ex_series_scal_l R_AbsRing R_CompleteNormedModule).
    apply ex_series_ext with (a := fun n => (/ 2) ^ n).
    - intros.
      intros; rewrite Rinv_pow; lra.
    - apply ex_series_geom.
      rewrite Rabs_Rinv by lra.
      rewrite Rabs_pos_eq; try lra.
 Qed.
  
  Lemma series_is_lim_seq (f:nat -> R) (l:R) :
    is_lim_seq (sum_n f) l <-> is_series f l.
  Proof.
    easy.
   Qed.

  Lemma series_sum_le (f : nat -> R) (x: R) :
    is_series f x ->
    (forall n, 0 <= f n) ->
    forall n, sum_n f n <= x.
  Proof.
    intros.
    rewrite <- series_is_lim_seq in H.
    apply is_lim_seq_incr_compare; trivial.
    intros.
    rewrite sum_Sn.
    now apply Rplus_le_pos_l.
  Qed.    

  Lemma islp_Rbar_lim_telescope_abs_gen (f : nat -> LpRRV prts p) :
    ex_series (fun n => 
                 LpRRVnorm prts 
                           (LpRRVminus prts (f (S n)) (f n))) ->
    (forall (n:nat), RandomVariable dom borel_sa (f n)) ->
    IsLp_Rbar prts p
              (Rbar_rvlim
                 (fun n => LpRRV_rv_X _ (LpRRVsum 
                                      prts pbig
                                      (fun n0 => LpRRVabs prts (LpRRVminus prts (f (S n0)) 
                                                                        (f n0))) n))).
  Proof.
    intros.
    apply ex_series_ext with (b := fun n : nat => LpRRVnorm prts (LpRRVabs prts (LpRRVminus prts (f (S n)) (f n))))
      in H.
    - unfold ex_series in H.
      destruct H.
      apply islp_Rbar_rvlim_bounded with (c := x); try lra.
      + intros.
        eapply Rle_trans.
        apply LpRRV_norm_sum.
        apply series_sum_le; trivial.
        intros.
        unfold LpRRVnorm.
        apply power_nonneg.
      + intros.
        typeclasses eauto.
      + intros.
        apply LpRRVsum_pos.
        typeclasses eauto.
      + intros n xx.
        unfold LpRRVsum, pack_LpRRV; simpl.
        unfold rvsum.
        rewrite sum_Sn.
        apply Rplus_le_compat1_l.
        unfold rvabs.
        apply Rabs_pos.
    - intros.
      now rewrite norm_abs.
  Qed.

  Lemma cauchy_filter_sum_abs
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar 
      prts p
      (Rbar_rvlim
         (fun n0 =>
            LpRRV_rv_X _ 
                       (LpRRVsum prts pbig 
                                 (fun n =>
                                    (LpRRVabs prts
                                              (LpRRVminus prts
                                                          (LpRRV_lim_picker F PF cF (S (S n)))
                                                          (LpRRV_lim_picker F PF cF (S n))))) n0))).
  Proof.
    apply (islp_Rbar_lim_telescope_abs prts pbig
                                       (fun n => LpRRV_lim_picker F PF cF (S n)))
    ; [ | typeclasses eauto ]; intros.
    generalize (lim_filter_cauchy F PF cF (S n) (S (S n)) (S n)); intros.
    simpl.
    cut_to H; try lia.
    simpl in H.
    unfold Rdiv in H.
    rewrite Rinv_mult_distr in H; try lra; [|apply pow_nzero; lra].
    rewrite <- Rmult_assoc in H.
    rewrite Rinv_r in H; try lra.
    rewrite Rmult_1_l in H.
    apply H.
  Qed.

  Lemma cauchy_filter_sum_abs_ext0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar 
      prts p
      (Rbar_rvlim
         (fun n0 =>
            LpRRV_rv_X _ (LpRRVsum prts pbig 
                     (fun n =>
                        (LpRRVabs prts
                                  (LpRRVminus prts
                                              (LpRRV_lim_picker_ext0 F PF cF (S n))
                                              (LpRRV_lim_picker_ext0 F PF cF n)))) n0))).
  Proof.
    apply  islp_Rbar_lim_telescope_abs_gen
    ; [ | typeclasses eauto ]; intros.

    apply (@ex_series_le R_AbsRing R_CompleteNormedModule) with
        (b := fun n => match n with 
                       | 0 => LpRRVnorm prts (LpRRV_lim_picker_ext0 F PF cF 1)
                       | S n' => 2 / (pow 2 n')
                       end).

    - intros; unfold norm; simpl.
      unfold abs; simpl.
      rewrite Rabs_pos_eq.
      match_destr.
      + simpl.
        unfold LpRRVminus, LpRRVzero.
        unfold pack_LpRRV, LpRRVconst.
        unfold rvminus, rvplus, rvopp, rvscale, const; simpl.
        right.
        apply LpRRV_norm_sproper.
        intro z.
        simpl.
        ring.
      + left.
        simpl.
        apply (lim_filter_cauchy F PF cF n (S (S n)) (S n)); try lia.
      + unfold LpRRVnorm.
        apply power_nonneg.
    - rewrite ex_series_incr_1.
      unfold Rdiv.
      apply (@ex_series_scal_l R_AbsRing R_CompleteNormedModule).
      apply ex_series_ext with (a := fun n => (/ 2)^n).
      intros; now rewrite Rinv_pow.
      apply ex_series_geom.
      rewrite Rabs_pos_eq; lra.
 Qed.

  Lemma cauchy_filter_sum
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p 
         (Rbar_rvlim
            (rvsum
               (fun n =>
                  (LpRRVminus prts
                              (LpRRV_lim_picker F PF cF (S (S n)))
                              (LpRRV_lim_picker F PF cF (S n)))))).
  Proof.
    generalize (cauchy_filter_sum_abs F PF cF).
    unfold IsLp_Rbar; intros.
    unfold LpRRVnorm in H.
    eapply (is_finite_Rbar_NonnegExpectation_le _ _ _ H).
    Unshelve.
    intro x.
    unfold Rbar_rvlim.
    apply Rbar_power_le with (p := p); [simpl; lra | apply Rbar_abs_nneg | ].
    simpl.
    repeat rewrite Elim_seq_fin.
    apply Rbar_Rabs_lim_sum_le.
  Qed.

  Lemma cauchy_filter_sum_ext0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
         (Rbar_rvlim
            (rvsum
               (fun n =>
                  (LpRRVminus prts
                              (LpRRV_lim_picker_ext0 F PF cF (S n))
                              (LpRRV_lim_picker_ext0 F PF cF n))))).
  Proof.
    generalize (cauchy_filter_sum_abs_ext0 F PF cF).
    unfold IsLp_Rbar; intros.
    unfold LpRRVnorm in H.
    eapply (is_finite_Rbar_NonnegExpectation_le _ _ _ H).
    Unshelve.
    intro x.
    unfold Rbar_rvlim.
    apply Rbar_power_le with (p := p); [simpl; lra | apply Rbar_abs_nneg | ].
    simpl.
    repeat rewrite Elim_seq_fin.
    apply Rbar_Rabs_lim_sum_le.
  Qed.

  Lemma LpRRVsum_telescope0
        (f: nat -> LpRRV prts p) : 
    forall n0,
      LpRRV_seq (LpRRVsum prts pbig
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
        (f: nat -> LpRRV prts p) : 
     forall n0,
      LpRRV_seq (LpRRVplus prts (f 0%nat)
                 (LpRRVsum prts pbig
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
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    forall n0, 
      LpRRV_seq (LpRRVplus 
                   prts
                   (LpRRV_lim_picker F PF cF (S 0%nat))
                   (LpRRVsum prts pbig 
                             (fun n =>
                                (LpRRVminus prts
                                            (LpRRV_lim_picker F PF cF (S (S n)))
                                            (LpRRV_lim_picker F PF cF (S n)))) n0))
                (LpRRV_lim_picker F PF cF (S (S n0))).
  Proof.
    intros.
    apply (LpRRVsum_telescope 
             (fun n =>
                LpRRV_lim_picker F PF cF (S n))).
  Qed.

  Lemma cauchy_filter_Rbar_lim
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
         (Rbar_rvlim
            (fun n => LpRRV_rv_X _ (LpRRVminus prts
                        (LpRRV_lim_picker F PF cF (S (S n)))
                        (LpRRV_lim_picker F PF cF (S 0%nat)))
                        
         )).
  Proof.
   apply (IsLp_Rbar_proper prts p) with
       (x :=  
             (Rbar_rvlim
               (fun n0 =>
                  LpRRV_rv_X _ (LpRRVsum prts pbig 
                           (fun n =>
                              (LpRRVminus prts
                                          (LpRRV_lim_picker F PF cF (S (S n)))
                                          (LpRRV_lim_picker F PF cF (S n))))
                           n0)))); trivial.
   intro z.
   unfold Rbar_rvlim.
   apply ELim_seq_ext.
   intros.
   f_equal.
   apply (LpRRVsum_telescope0 (fun n => (LpRRV_lim_picker F PF cF (S n)))).
   apply cauchy_filter_sum.
  Qed.

   Lemma cauchy_filter_Rbar_lim_ext0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
         (Rbar_rvlim
            (fun n => LpRRV_rv_X _ (LpRRVminus prts
                        (LpRRV_lim_picker_ext0 F PF cF (S n))
                        (LpRRV_lim_picker_ext0 F PF cF 0%nat)))
                        
         ).
  Proof.
   apply (IsLp_Rbar_proper prts p) with
       (x :=  
             (Rbar_rvlim
               (fun n0 =>
                  LpRRV_rv_X _ (LpRRVsum prts pbig 
                           (fun n =>
                              (LpRRVminus prts
                                          (LpRRV_lim_picker_ext0 F PF cF (S n))
                                          (LpRRV_lim_picker_ext0 F PF cF n)))
                           n0)))); trivial.
   intro z.
   unfold Rbar_rvlim.
   apply ELim_seq_ext.
   intros.
   f_equal.
   apply (LpRRVsum_telescope0 (fun n => (LpRRV_lim_picker_ext0 F PF cF n))).
   apply  cauchy_filter_sum_ext0.
  Qed.

  Lemma IsLp_IsLp_Rbar (f : LpRRV prts p) :
    IsLp_Rbar prts p (LpRRV_rv_X prts f).
  Proof.
    unfold IsLp_Rbar.
    unfold IsLp, IsLp_Rbar; intros.
    generalize (LpRRV_LpS_FiniteLp prts f); intros.
    unfold IsFiniteExpectation in H.
    generalize (rvpower_nnf (rvabs f) (const p)); intros.
    rewrite Expectation_pos_pofrf with (nnf := H0) in H.
    match_case_in H; intros.
    - rewrite NNExpectation_Rbar_NNExpectation in H1.
      unfold rvpower, rvabs, const in H1.
      unfold Rbar_power, Rbar_abs.
      erewrite Rbar_NonnegExpectation_pf_irrel.
      erewrite Rbar_NonnegExpectation_pf_irrel in H1.      
      now rewrite H1.
    - now rewrite H1 in H.
    - generalize (NonnegExpectation_pos (rvpower (rvabs f) (const p))); intros.
      rewrite H1 in H2.
      now simpl in H2.
   Qed.

  Lemma IsLp_Rbar_IsLp (f : Ts -> R) :
    IsLp_Rbar prts p f ->
    IsLp prts p f.
  Proof.
    unfold IsLp, IsLp_Rbar; intros.
    unfold IsFiniteExpectation.
    generalize (rvpower_nnf (rvabs f) (const p)); intros.
    rewrite Expectation_pos_pofrf with (nnf := H0).
    rewrite NNExpectation_Rbar_NNExpectation.
    unfold Rbar_power, Rbar_abs in H.
    unfold rvpower, rvabs, const.
    erewrite Rbar_NonnegExpectation_pf_irrel.
    erewrite Rbar_NonnegExpectation_pf_irrel in H.
    now rewrite <- H.
  Qed.

  Lemma cauchy_filter_Rbar_rvlim1
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    IsLp_Rbar prts p
              (Rbar_rvlim (fun n => (LpRRV_rv_X _ (LpRRV_lim_picker F PF cF (S n))))).
   Proof.
     generalize (cauchy_filter_Rbar_lim_ext0 F PF cF); intros.
     unfold LpRRV_lim_picker_ext0 in H.
     eapply IsLp_Rbar_proper; trivial.
     shelve.
     apply H.
     Unshelve.
     intro x.
     unfold Rbar_rvlim.
     apply ELim_seq_ext.
     intros.
     f_equal.
     unfold LpRRVzero, LpRRVconst, const.
     unfold pack_LpRRV; simpl.
     unfold rvminus, rvplus, rvopp, rvscale.
     ring.
   Qed.

  Instance nnf_0 :
    (@Rbar_NonnegativeFunction Ts (fun x => const 0 x)).
  Proof.
    unfold Rbar_NonnegativeFunction.
    intros.
    simpl.
    unfold const.
    lra.
  Qed.

  Lemma Rbar_IsLp_bounded n (rv_X1 rv_X2 : Ts -> Rbar)
        (rle:Rbar_rv_le (fun (omega : Ts) => Rbar_power (Rbar_abs (rv_X1 omega)) n) rv_X2)
        {islp:Rbar_IsFiniteExpectation prts rv_X2}
    :
      IsLp_Rbar prts n rv_X1.
  Proof.
    unfold IsLp_Rbar.
    assert (Rbar_IsFiniteExpectation prts (fun x => const 0 x)).
    {
      generalize (Rbar_Expectation_pos_pofrf (fun x => Finite (const 0 x))); intros.
      unfold Rbar_IsFiniteExpectation.
      rewrite H.
      assert (0 <= 0) by lra.
      generalize (Rbar_NonnegExpectation_const 0 H0); intros.
      rewrite Rbar_NonnegExpectation_pf_irrel with (nnf2 := nnf_0) in H1.
      now rewrite H1.
    }
    generalize (Rbar_IsFiniteExpectation_bounded prts (const 0)
                                                 (fun (omega : Ts) => Rbar_power (Rbar_abs (rv_X1 omega)) n) rv_X2); intros.
    cut_to H0; trivial.
    - unfold Rbar_IsFiniteExpectation in H0.
      rewrite Rbar_Expectation_pos_pofrf with (nnf := power_abs_pos rv_X1 n) in H0.
      match_destr_in H0; easy.
    - intro x.
      unfold const.
      apply Rbar_power_nonneg.
  Qed.

  Instance Rbar_power_pos m (rv_X: Ts -> Rbar) :
    Rbar_NonnegativeFunction 
      (fun omega => Rbar_power (rv_X omega) m).
  Proof.
    intro x.
    apply Rbar_power_nonneg.
  Qed.

  Lemma IsLp_Rbar_down_le m n (rv_X:Ts->Rbar)
        {rrv:RandomVariable dom Rbar_borel_sa rv_X}
        (pfle:0 <= n <= m)
        {lp:IsLp_Rbar prts m rv_X} : IsLp_Rbar prts n rv_X.
  Proof.
    apply Rbar_IsLp_bounded with (rv_X2 := fun omega => Rbar_max 1 (Rbar_power (Rbar_abs (rv_X omega)) m)).
    - intros a.
      case_eq (rv_X a); intros.
      + unfold Rbar_abs, Rbar_power.
        replace (Rbar_max 1 (power (Rabs r) m)) with (Finite (Rmax 1 (power (Rabs r) m))).
        unfold Rbar_le.
        destruct (Rle_lt_dec 1 (Rabs r)).
        * eapply Rle_trans; [| eapply Rmax_r].
          now apply Rle_power.
        * eapply Rle_trans; [| eapply Rmax_l].
          unfold power.
          match_destr; [lra | ].
          generalize (Rabs_pos r); intros.
          destruct (Req_EM_T n 0).
          -- subst.
             rewrite Rpower_O; lra.
          -- assert (eqq:1 = Rpower 1 n).
             {
               unfold Rpower.
               rewrite ln_1.
               rewrite Rmult_0_r.
               now rewrite exp_0.
             }
             rewrite eqq.
             apply Rle_Rpower_l; lra.
        * unfold Rbar_max.
          match_case; intros.
          -- simpl in r0.
             now rewrite Rmax_right.
          -- simpl in n0.
             rewrite Rmax_left; trivial.
             left; lra.
      + simpl.
        unfold Rbar_max.
        case_eq (Rbar_le_dec 1 p_infty); intros; trivial.
        now simpl in n0.
      + simpl.
        unfold Rbar_max.
        case_eq (Rbar_le_dec 1 p_infty); intros; trivial.
        now simpl in n0.
    - assert (Rbar_NonnegativeFunction 
                 (fun omega : Ts => Rbar_max 1 (Rbar_power (Rbar_abs (rv_X omega)) m))).
      {
        intro x.
        unfold Rbar_max.
        match_destr.
        - apply Rbar_power_nonneg.
        - simpl; lra.
      }
      unfold Rbar_IsFiniteExpectation.
      rewrite Rbar_Expectation_pos_pofrf with (nnf := H).
      unfold IsLp_Rbar in lp.
      assert (0 <= 1) by lra.

      assert (rv1: RandomVariable dom Rbar_borel_sa 
                                  (fun omega => (Rbar_power (Rbar_abs (rv_X omega)) m))).
      {
        apply Rbar_measurable_rv.
        apply Rbar_power_measurable.
        apply Rbar_Rabs_measurable.
        now apply rv_Rbar_measurable.
      }
      generalize (@Rbar_NonnegExpectation_plus Ts dom prts
                    (const (Finite 1))
                    (fun omega => (Rbar_power (Rbar_abs (rv_X omega)) m))
                    _ _ (nnfconst _ H0) _ ); intros.
      assert (is_finite
                 (@Rbar_NonnegExpectation Ts dom prts
            (Rbar_rvplus (@const Rbar Ts (Finite (IZR (Zpos xH))))
               (fun omega : Ts => Rbar_power (Rbar_abs (rv_X omega)) m))
            (@pos_Rbar_plus Ts 
                            (@const Rbar Ts (Finite (IZR (Zpos xH))))
                            (fun omega : Ts => Rbar_power (Rbar_abs (rv_X omega)) m)
                            (nnfconst _ H0)
                            (Rbar_power_pos m (fun omega : Ts => Rbar_abs (rv_X omega))) ))).
      {
        rewrite H1.
        assert (is_finite (@Rbar_NonnegExpectation Ts dom prts (@const Rbar Ts (Finite 1))  (nnfconst _ H0))).
        - generalize (Rbar_NonnegExpectation_const _ H0); intros.
          unfold const in H2.
          unfold const.
          rewrite H2.
          now simpl.
        - rewrite <- H2.
          rewrite <- lp.
          now simpl.
      } 
      assert (Rbar_rv_le
                (fun omega : Ts => Rbar_max 1 (Rbar_power (Rbar_abs (rv_X omega)) m))
                (Rbar_rvplus (const (Finite 1))
                             (fun omega => Rbar_power (Rbar_abs (rv_X omega)) m))).
      {
        intro x.
        unfold Rbar_rvplus, const, Rbar_max.
        match_destr.
        - replace (Rbar_power (Rbar_abs (rv_X x)) m) with
              (Rbar_plus (Finite 0) (Rbar_power (Rbar_abs (rv_X x)) m)) at 1.
          + apply Rbar_plus_le_compat.
            * simpl; lra.
            * apply Rbar_le_refl.
          + apply Rbar_plus_0_l.
        - replace (Finite 1) with (Rbar_plus (Finite 1) (Finite 0)) at 1.
          + apply Rbar_plus_le_compat.
            * apply Rbar_le_refl.
            * apply Rbar_power_nonneg.
          + simpl.
            apply Rbar_finite_eq.
            lra.
      }
      generalize (is_finite_Rbar_NonnegExpectation_le _ _ H3 H2); intros.
      now rewrite <- H4.
   Qed.

  Lemma IsL1_Rbar_abs_Finite (rv_X:Ts->Rbar)
        {lp:IsLp_Rbar prts 1 rv_X} : is_finite (Rbar_NonnegExpectation (Rbar_rvabs rv_X)).
  Proof.
    red in lp.
    assert (rv_eq (fun omega => Rbar_power (Rbar_abs (rv_X omega)) 1)
                  (Rbar_rvabs rv_X)).
    - intro x.
      unfold Rbar_power, Rbar_rvabs.      
      destruct (rv_X x); simpl; trivial.
      unfold power.
      match_destr.
      + generalize (Rabs_pos r); intros.
        apply Rbar_finite_eq.
        lra.
      + rewrite Rpower_1; trivial.
        apply Rabs_pos_lt.
        unfold Rabs in n.
        match_destr_in n; lra.
    - now rewrite (Rbar_NonnegExpectation_ext _ _ H) in lp.
    Qed.

  Lemma IsL1_Rbar_Finite (rv_X:Ts->Rbar)
        {rv:RandomVariable dom Rbar_borel_sa rv_X}
        {lp:IsLp_Rbar prts 1 rv_X} : Rbar_IsFiniteExpectation prts rv_X.
  Proof.
    apply finiteExp_Rbar_rvabs; trivial.
    now apply IsL1_Rbar_abs_Finite.
  Qed.

  Lemma Rbar_IsLp_IsFiniteExpectation (f : Ts -> Rbar) (n : R)
        {rrv:RandomVariable dom Rbar_borel_sa f} :
    1 <= n ->
    IsLp_Rbar prts n f -> Rbar_IsFiniteExpectation prts f.
  Proof.
    intros.
    apply IsL1_Rbar_Finite; trivial.
    apply (IsLp_Rbar_down_le n 1 f); trivial.
    lra.
  Qed.

  Lemma Rbar_IsLp_almostR2_finite (f : Ts -> Rbar) (n : R)
        {rrv:RandomVariable dom Rbar_borel_sa f} :
    1 <= n ->
    IsLp_Rbar prts n f ->
    ps_P (exist sa_sigma _ (sa_finite_Rbar f rrv)) = 1.    
  Proof.
    intros.
    apply Rbar_IsLp_IsFiniteExpectation in H0; trivial.
    now apply finite_Rbar_Expectation_almostR2_finite.
  Qed.

  Instance picker_rv
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) 
        (n : nat) :
    RandomVariable dom borel_sa (LpRRV_rv_X prts (LpRRV_lim_picker F PF cF n)).
  Proof.
    exact (LpRRV_rv prts (LpRRV_lim_picker F PF cF n)).
  Qed.

  Lemma Rbar_lim_seq_pos_rv
        (f : nat -> Ts -> Rbar) :
    (forall n, RandomVariable dom Rbar_borel_sa (f n)) ->
    (forall n, Rbar_NonnegativeFunction (f n)) ->
    RandomVariable dom Rbar_borel_sa (fun omega => ELim_seq (fun n => f n omega)).
  Proof.
    intros.
    unfold RandomVariable.
    apply Rbar_borel_sa_preimage2.    
    intros.
    apply Rbar_lim_seq_measurable_pos; trivial.
    intros.
    unfold RbarMeasurable.
    apply Rbar_borel_sa_preimage2.        
    apply H.
  Qed.
    
   Lemma cauchy_filter_sum_abs_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
     almost prts (fun x =>
          is_finite (ELim_seq 
                       (fun n0 =>
                          LpRRVsum prts pbig 
                                   (fun n =>
                                      (LpRRVabs prts
                                                (LpRRVminus prts
                                                            (LpRRV_lim_picker F PF cF (S (S n)))
                                                            (LpRRV_lim_picker F PF cF (S n))))) n0 x))).
   Proof.
    generalize (cauchy_filter_sum_abs F PF cF); intros.
    pose (limpick :=
             (Rbar_rvlim
           (fun n0 : nat =>
            LpRRV_rv_X _ (LpRRVsum prts pbig
              (fun n : nat =>
               LpRRVabs prts
                 (LpRRVminus prts (LpRRV_lim_picker F PF cF (S (S n)))
                    (LpRRV_lim_picker F PF cF (S n)))) n0)))).
    assert (rv:RandomVariable dom Rbar_borel_sa limpick).
    {
      subst limpick.
      unfold Rbar_rvlim.
      apply Rbar_lim_seq_pos_rv.
      - intros.
        apply borel_Rbar_borel.
        apply LpRRV_rv.
      - intros.
        apply positive_Rbar_positive.
        apply LpRRVsum_pos.
        intros.
        unfold LpRRVabs, pack_LpRRV;simpl.
        apply nnfabs.
    }
    exists (exist _ _ (sa_finite_Rbar limpick rv)).
    split.
    - subst limpick.
      apply Rbar_IsLp_almostR2_finite with (n := p); trivial.
    - intros.
      apply H0.
  Qed.

   Lemma cauchy_filter_sum_abs_ext0_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    almost prts (fun x =>
          is_finite (ELim_seq 
                       (fun n0 =>
                          LpRRVsum prts pbig 
                                   (fun n =>
                                      (LpRRVabs prts
                                                (LpRRVminus prts
                                                            (LpRRV_lim_picker_ext0 F PF cF (S n))
                                                            (LpRRV_lim_picker_ext0 F PF cF n)))) n0 x))).
   Proof.
    generalize (cauchy_filter_sum_abs_ext0 F PF cF); intros.
    pose (limpick :=
             (Rbar_rvlim
           (fun n0 : nat =>
            LpRRV_rv_X _ (LpRRVsum prts pbig
              (fun n : nat =>
               LpRRVabs prts
                 (LpRRVminus prts (LpRRV_lim_picker_ext0 F PF cF (S n))
                    (LpRRV_lim_picker_ext0 F PF cF n))) n0)))).
    assert (rv:RandomVariable dom Rbar_borel_sa limpick).
    {
      subst limpick.
      unfold Rbar_rvlim.
      apply Rbar_lim_seq_pos_rv.
      - intros.
        apply borel_Rbar_borel.
        apply LpRRV_rv.
      - intros.
        apply positive_Rbar_positive.
        apply LpRRVsum_pos.
        intros.
        unfold LpRRVabs, pack_LpRRV;simpl.
        apply nnfabs.
    }
    exists (exist _ _ (sa_finite_Rbar limpick rv)).
    split.
    - subst limpick.
      apply Rbar_IsLp_almostR2_finite with (n := p); trivial.
    - intros.
      apply H0.
  Qed.

  Lemma cauchy_filter_sum_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    almost prts (fun x =>
          ex_finite_lim_seq
            (fun n0 =>
               LpRRVsum prts pbig 
                        (fun n =>
                           (LpRRVminus prts
                                       (LpRRV_lim_picker F PF cF (S (S n)))
                                       (LpRRV_lim_picker F PF cF (S n)))) n0 x)).
  Proof.
    generalize (cauchy_filter_sum_abs_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    unfold LpRRVsum, pack_LpRRV, rvsum; simpl.
    unfold LpRRVsum, pack_LpRRV, rvsum in H0; simpl in H0.
    unfold rvabs in H0.
    rewrite Elim_seq_fin in H0.
    now apply lim_sum_abs_bounded.
 Qed.

  Lemma ex_finite_lim_seq_ext (f g : nat -> R) :
    (forall n, f n = g n) ->
    ex_finite_lim_seq f <-> ex_finite_lim_seq g.
  Proof.
    intros.
    unfold ex_finite_lim_seq.
    split; intros;
      destruct H0 as [l ?]; exists l.
    - now apply is_lim_seq_ext with (u := f).      
    - now apply is_lim_seq_ext with (u := g).      
  Qed.

  Lemma ex_finite_lim_seq_S (f : nat -> R) :
    ex_finite_lim_seq f <-> ex_finite_lim_seq (fun n => f (S n)).
  Proof.
    unfold ex_finite_lim_seq.
    split; intros; destruct H as [l ?]; exists l.
    now apply is_lim_seq_incr_1 in H.
    now apply is_lim_seq_incr_1.    
  Qed.

  Lemma cauchy_filter_sum_ext0_finite00
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    almost prts (fun x =>
          ex_finite_lim_seq
            (fun n0 =>
               LpRRVsum prts pbig 
                        (fun n =>
                           (LpRRVminus prts
                                       (LpRRV_lim_picker_ext0 F PF cF (S n))
                                       (LpRRV_lim_picker_ext0 F PF cF n))) n0 x)).
  Proof.
    generalize (cauchy_filter_sum_abs_ext0_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    unfold LpRRVsum, pack_LpRRV, rvsum; simpl.
    unfold LpRRVsum, pack_LpRRV, rvsum in H0; simpl in H0.
    unfold rvabs in H0.
    rewrite Elim_seq_fin in H0.
    now apply lim_sum_abs_bounded.
 Qed.
    
  Lemma cauchy_filter_rvlim_finite0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    almost prts (fun x =>
                   ex_finite_lim_seq (fun n => (LpRRV_lim_picker F PF cF (S (S n))) x)).
  Proof.
    generalize (cauchy_filter_sum_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    rewrite ex_finite_lim_seq_ext in H0.
    shelve.
    intros.
    generalize (LpRRVsum_telescope0 (fun n => LpRRV_lim_picker F PF cF (S n)) n); intros.
    apply H2.
    Unshelve.
    unfold LpRRVminus, pack_LpRRV in H0; simpl in H0.
    unfold rvminus, rvplus, rvopp, rvscale in H0.
    unfold ex_finite_lim_seq in H0.
    destruct H0 as [l ?].
    unfold ex_finite_lim_seq.
    exists (l + LpRRV_lim_picker F PF cF 1 x).
    apply is_lim_seq_ext with
        (u :=  fun n : nat =>
                 (LpRRV_lim_picker F PF cF (S (S n)) x + -1 * LpRRV_lim_picker F PF cF 1 x)
                   +
                   (LpRRV_lim_picker F PF cF 1 x)); [(intros; lra) |].
    apply is_lim_seq_plus'; trivial.
    apply is_lim_seq_const.
 Qed.

    Lemma cauchy_filter_rvlim_ext0_finite0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    almost prts (fun x =>
                   ex_finite_lim_seq (fun n => (LpRRV_lim_picker F PF cF (S n)) x)).
  Proof.
    generalize (cauchy_filter_sum_ext0_finite00 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P; split; trivial.
    intros.
    specialize (H0 x H1).
    rewrite ex_finite_lim_seq_ext in H0.
    shelve.
    intros.
    generalize (LpRRVsum_telescope0 (fun n => LpRRV_lim_picker_ext0 F PF cF n) n); intros.
    apply H2.
    Unshelve.
    unfold LpRRVminus, pack_LpRRV in H0; simpl in H0.
    unfold rvminus, rvplus, rvopp, rvscale, const in H0.
    rewrite ex_finite_lim_seq_ext in H0.
    apply H0.
    intros.
    lra.
 Qed.

    Lemma cauchy_filter_rvlim_Sext0_finite0
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    almost prts (fun x =>
                   ex_finite_lim_seq (fun n => (LpRRV_lim_picker F PF cF n) x)).
   Proof.
     generalize (cauchy_filter_rvlim_ext0_finite0 F PF cF); intros.
     destruct H as [P [? ?]].
     exists P.
     split; trivial; intros.
     specialize (H0 x H1).
     now apply ex_finite_lim_seq_S.
   Qed.

  Lemma cauchy_filter_rvlim_finite
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    exists (P: event dom),
      exists (dec: forall x, {P x} + {~ P x}),
        ps_P P = 1 /\
        (forall x,
          ex_finite_lim_seq (fun n => (rvmult (EventIndicator dec)
                                              (LpRRV_lim_picker F PF cF (S n)))
                                        x) ) /\
        IsLp prts p
             (rvlim (fun n => (rvmult (EventIndicator dec)
                                      (LpRRV_lim_picker F PF cF (S n))))).
  Proof.
    generalize (cauchy_filter_rvlim_ext0_finite0 F PF cF); intros.
    destruct H as [P [? ?]].
    exists P.
    assert (forall x: Ts, {P x} + {~ P x}).
    {
      intros.
      apply ClassicalDescription.excluded_middle_informative.
    }
    exists X.
    split; trivial.
    split.
    - intros.
      destruct (X x).
      + specialize (H0 x e).
        unfold ex_finite_lim_seq.
        unfold ex_finite_lim_seq in H0.
        destruct H0.
        exists x0.
        eapply is_lim_seq_ext.
        shelve.
        apply H0.
        Unshelve.
        intros; simpl.
        unfold rvmult, EventIndicator.
        match_destr; try tauto; lra.
      + unfold rvmult, EventIndicator, ex_finite_lim_seq.
        exists 0.
        apply is_lim_seq_ext with (u := (const 0)); [|apply is_lim_seq_const].
        intros.
        unfold const.
        match_destr; try tauto; lra.
    - generalize (cauchy_filter_Rbar_rvlim1 F PF cF); intros.
      apply IsLp_Rbar_IsLp.
      apply (IsLp_Rbar_proper_almostR2 prts _ (Rbar_rvlim (fun n : nat => LpRRV_rv_X _ (LpRRV_lim_picker F PF cF (S n)))))
      ; try typeclasses eauto; trivial.
      exists P. split; trivial; intros a Pa.
      specialize (H0 _ Pa).
      unfold Rbar_rvlim.
      unfold rvlim.
      unfold rvmult, EventIndicator.
      destruct (X a); [| tauto].
      rewrite Lim_seq_ext with (u := (fun n : nat => 1 * LpRRV_lim_picker F PF cF (S n) a))
                               (v := (fun n : nat => LpRRV_lim_picker F PF cF (S n) a)); [|intros; lra].
      rewrite ex_finite_lim_seq_correct in H0.
      destruct H0.
      rewrite Elim_seq_fin.
      auto.
  Qed.

  Lemma cauchy_filter_rvlim_finite1
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    { P: event dom | 
         exists dec: forall x, {P x} + {~ P x},
           ps_P P = 1 /\
           (forall x,
               ex_finite_lim_seq (fun n => (rvmult (EventIndicator dec)
                                                (LpRRV_lim_picker F PF cF (S n)))
                                             x) ) /\
           IsLp prts p
                (rvlim (fun n => (rvmult (EventIndicator dec)
                                      (LpRRV_lim_picker F PF cF (S n)))))
    }.
  Proof.
    apply constructive_indefinite_description.
    apply cauchy_filter_rvlim_finite.
  Qed.

  Lemma cauchy_filter_rvlim_finite2
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F) :
    { P: event dom &
         {dec: forall x, {P x} + {~ P x} |
           ps_P P = 1 /\
           (forall x,
               ex_finite_lim_seq (fun n => (rvmult (EventIndicator dec)
                                                   (LpRRV_lim_picker F PF cF (S n)))
                                          x) ) /\
           IsLp prts p
                (rvlim (fun n => (rvmult (EventIndicator dec)
                                         (LpRRV_lim_picker F PF cF (S n)))))}
    }.
  Proof.
    destruct (cauchy_filter_rvlim_finite1 F PF cF).
    exists x.
    apply constructive_indefinite_description.
    apply e.
  Qed.

  Definition cauchy_rvlim_fun  (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : Ts -> R
    := match cauchy_filter_rvlim_finite2 F PF cF with
       | existT P (exist dec PP) =>  (rvlim (fun n => (rvmult (EventIndicator dec)
                                                              (LpRRV_lim_picker F PF cF (S n)))))
       end.

  Global Instance cauchy_rvlim_fun_isl2 (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : IsLp prts p (cauchy_rvlim_fun F PF cF).
  Proof.
    unfold cauchy_rvlim_fun.
    repeat match_destr.
    tauto.
  Qed.

  Global Instance cauchy_rvlim_fun_rv (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : RandomVariable dom borel_sa (cauchy_rvlim_fun F PF cF).
  Proof.
    unfold cauchy_rvlim_fun.
    repeat match_destr.
    apply rvlim_rv.
    - typeclasses eauto.
    - tauto.
  Qed.
  
  Definition LpRRV_lim_with_conditions (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F) : LpRRV prts p
      := pack_LpRRV prts (cauchy_rvlim_fun F PF cF).

  Definition LpRRV_lim (F : ((LpRRV prts p -> Prop) -> Prop)) : LpRRV prts p.
  Proof.
    destruct (excluded_middle_informative (ProperFilter F)).
    - destruct (excluded_middle_informative (cauchy (T:= LpRRV_UniformSpace prts pbig) F)).
      + exact (LpRRV_lim_with_conditions _ _ c).
      + exact (LpRRVzero prts).
    - exact (LpRRVzero prts).
  Defined.
  
  Lemma Lim_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    Lim_seq (fun n => f (u n)) = f (Lim_seq u).
  Proof.
    intros.
    unfold ex_finite_lim_seq in H0.
    destruct H0.
    generalize (is_lim_seq_continuous f u x); intros.
    generalize (is_lim_seq_unique _ _ H0); intros.
    rewrite H2 in H.
    specialize (H1 H H0).
    apply is_lim_seq_unique in H1.
    now rewrite H2.
  Qed.

  Lemma is_finite_Lim_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    is_finite (Lim_seq (fun n => f (u n))).
  Proof.
    intros.
    unfold ex_finite_lim_seq in H0.
    destruct H0.
    generalize (is_lim_seq_continuous f u x); intros.
    generalize (is_lim_seq_unique _ _ H0); intros.
    rewrite H2 in H.
    specialize (H1 H H0).
    apply is_lim_seq_unique in H1.
    now rewrite H1.
  Qed.

  Lemma ex_lim_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    ex_lim_seq (fun n => f (u n)).
  Proof.
    intros.
    unfold ex_finite_lim_seq in H0.
    destruct H0.
    generalize (is_lim_seq_continuous f u x); intros.
    generalize (is_lim_seq_unique _ _ H0); intros.
    unfold ex_lim_seq.
    exists (f x).
    rewrite H2 in H.
    now apply H1.
  Qed.

  Lemma lim_seq_lim_inf (f : nat -> R) :
    ex_lim_seq f ->
    Lim_seq f = LimInf_seq f.
  Proof.
    intros.
    rewrite ex_lim_LimSup_LimInf_seq in H.
    unfold Lim_seq.
    rewrite H.
    now rewrite x_plus_x_div_2.
  Qed.

  Lemma is_finite_LimInf_seq_continuous (f : R -> R) (u : nat -> R) :
    continuity_pt f (Lim_seq u) ->
    ex_finite_lim_seq u ->
    is_finite (LimInf_seq (fun n => f (u n))).
  Proof.
    intros.
    rewrite <- lim_seq_lim_inf.
    apply is_finite_Lim_seq_continuous; trivial.
    now apply ex_lim_seq_continuous.
 Qed.

  Lemma LpRRVnorm_NonnegExpectation 
        (f : LpRRV prts p)
        (rv : RandomVariable dom borel_sa f) :
    LpRRVnorm prts f = power (NonnegExpectation (rvpower (rvabs f)  (const p))) (/ p).
  Proof.
    unfold LpRRVnorm.
    f_equal.
    now erewrite FiniteNonnegExpectation.
  Qed.

   Lemma rvpowerabs_rvminus_rvlim_comm (f : nat -> Ts -> R) (n:nat):
     (forall x, ex_finite_lim_seq (fun n0 => f n0 x)) ->
     (rv_eq
        (rvpower (rvabs (rvminus (rvlim f) (f n))) (const p))
        (rvlim (fun x => (rvpower (rvabs (rvminus (f x) (f n))) (const p))))).
    Proof.
      intros exfin z.
      unfold rvpower, rvabs, rvminus, rvplus, rvopp, rvscale, rvlim, const.
      pose (p_power_abs := fun x => @p_power p (Rabs x) ).
      generalize (Lim_seq_ext 
                    (fun n0 : nat => power (Rabs (f n0 z + -1 * f n z)) p)
                    (fun n0 => p_power_abs (f n0 z + -1 * f n z))); intros.
      rewrite H.
      - rewrite Lim_seq_continuous; trivial.
        + unfold p_power_abs, p_power.
          rewrite Lim_seq_plus, Lim_seq_const.
          * specialize (exfin z).
            rewrite ex_finite_lim_seq_correct in exfin.
            destruct exfin.
            rewrite <- H1.
            now simpl.
          * specialize (exfin z).
            rewrite ex_finite_lim_seq_correct in exfin.
            now destruct exfin.
          * apply ex_lim_seq_const.
          * specialize (exfin z).
            rewrite ex_finite_lim_seq_correct in exfin.
            destruct exfin.
            rewrite <- H1.
            rewrite Lim_seq_const.
            now simpl.
        + apply continuity_p_power_Rabs; lra.
        + unfold ex_finite_lim_seq.
          specialize (exfin z).
          unfold ex_finite_lim_seq in exfin.
          destruct exfin.
          exists (x + -1 * f n z).
          apply is_lim_seq_plus'; trivial.
          apply is_lim_seq_const.
      - intros.
        now unfold p_power_abs.
   Qed.

    Lemma lt_Rbar_lt (x : Rbar) (y : R) :
      0 < y ->
      Rbar_lt x y -> (real x) < y.
    Proof.
      intros.
      destruct x.
      - now simpl in H.
      - now simpl.
      - now simpl.
    Qed.

    Lemma le_Rbar_le (x : Rbar) (y : R) :
      0 <= y ->
      Rbar_le x y -> (real x) <= y.
    Proof.
      intros.
      destruct x.
      - now simpl in H.
      - now simpl.
      - now simpl.
    Qed.

    Lemma LimInf_seq_ext (f g : nat -> R) :
      eventually (fun n => f n = g n) ->
      LimInf_seq f = LimInf_seq g.
    Proof.
      intros.
      unfold eventually in H.
      destruct H.
      apply Rbar_le_antisym.
      - apply LimInf_le.
        exists x.
        intros.
        specialize (H n H0).
        lra.
      - apply LimInf_le.
        exists x.
        intros.
        specialize (H n H0).
        lra.
    Qed.

  Instance Rbar_real_rv 
           (f : Ts -> Rbar)
           (rv : RandomVariable dom Rbar_borel_sa f) :
    RandomVariable dom borel_sa (fun omega => real (f omega)).
  Proof.
    apply measurable_rv.
    apply Rbar_real_measurable.
    now apply rv_Rbar_measurable.
  Qed.
  
  Lemma norm_rvminus_rvlim_le
        (f : nat -> LpRRV prts p) 
        (rvl : RandomVariable dom borel_sa (rvlim f)) 
        (isl : IsLp prts p (rvlim f)) :
    (forall x, ex_finite_lim_seq (fun n => f n x)) ->
    (forall (eps:posreal),
      exists (N : nat),
        forall (n m : nat), 
          (n >= N)%nat ->
          (m >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (f m) (f n))) < eps) ->
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) <= eps. 
  Proof.
    intros.
    specialize (H0 eps).
    destruct H0 as [N ?].
    exists N.
    intros.
    unfold LpRRVnorm, LpRRVminus, pack_LpRRV; simpl.
    replace (pos eps) with (power (power eps p) (/ p)) by (apply inv_power_cancel; [left; apply cond_pos| lra]).
    apply Rle_power_l.
    left; apply Rinv_0_lt_compat; lra.
    split.
    apply FiniteExpectation_pos; typeclasses eauto.
    assert (1 <= 2) by lra.
    generalize (rvpowerabs_rvminus_rvlim_comm f n H); intros.
    rewrite (FiniteExpectation_ext_alt _ _ _ H3).
    assert (rv_eq 
              (rvlim (fun x : nat => rvpower (rvabs (rvminus (f x) (f n))) (const p)))
              (fun omega => LimInf_seq (fun x : nat => rvpower (rvabs (rvminus (f x) (f n))) (const p) omega))).
    {
      intros z.
      unfold rvlim.
      rewrite lim_seq_lim_inf; trivial.
      pose (p_power_abs := fun x => @p_power p (Rabs x) ).      
      unfold rvpower, rvabs, const, rvminus, rvplus, rvopp, rvscale.
      apply ex_lim_seq_ext with (u := fun n0 => p_power_abs (f n0 z + -1 * f n z)).
      intros.
      now unfold p_power_abs, p_power.
      specialize (H z).
      unfold ex_finite_lim_seq in H.
      destruct H.
      unfold ex_lim_seq.
      exists (p_power_abs (x + -1 * f n z)).
      apply is_lim_seq_continuous.
      apply continuity_p_power_Rabs; lra.
      apply is_lim_seq_plus'; trivial.
      apply is_lim_seq_const.
    }
    rewrite (FiniteExpectation_ext_alt _ _ _ H4).
    unfold LpRRVnorm in H0.
    erewrite FiniteNonnegExpectation.
    apply le_Rbar_le.
    rewrite <- (power0_Sbase p).
    assert (0 < eps) by apply cond_pos.
    apply Rle_power_l; lra.
    assert (forall omega : Ts, is_finite (LimInf_seq (fun n0 : nat => rvpower (rvabs (rvminus (f n0) (f n))) (const p) omega))).
    {
      intros.
      unfold rvpower, rvabs, rvminus, rvplus, rvopp, rvscale, rvlim, const.
      pose (p_power_abs := fun x => @p_power p (Rabs x) ).
      specialize (H omega).

      generalize (LimInf_seq_ext 
                    (fun n0 : nat => power (Rabs (f n0 omega + -1 * f n omega)) p)
                    (fun n0 => p_power_abs (f n0 omega + -1 * f n omega))); intros.
      rewrite H5.
      - apply is_finite_LimInf_seq_continuous.
        + rewrite ex_finite_lim_seq_correct in H.
          destruct H.
          unfold p_power_abs, p_power.
          rewrite Lim_seq_plus, Lim_seq_const; trivial.
          * apply continuity_p_power_Rabs; lra.
          * apply ex_lim_seq_const.
          * rewrite Lim_seq_const.
            rewrite <- H6.
            now simpl.
        + unfold ex_finite_lim_seq.
          unfold ex_finite_lim_seq in H.
          destruct H.
          exists (x + -1 * f n omega).
          apply is_lim_seq_plus'; trivial.
          apply is_lim_seq_const.
      - intros.
        exists (0%nat); intros.
        now unfold p_power_abs.
    }
    eapply Rbar_le_trans.
    - apply Fatou; trivial.
      + intros; typeclasses eauto.
      + intros.
        generalize (IsLp_minus prts pnneg (f n0) (f n)); intros.
        unfold IsLp in H6.
        unfold IsFiniteExpectation in H6.
        erewrite Expectation_pos_pofrf in H6.
        simpl in H6.
        match_case_in H6; intros.
        * rewrite H7; now simpl.
        * now rewrite H7 in H6.
        * now rewrite H7 in H6.
      + eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)).
        { intros ?.
          rewrite <- ELimInf_seq_fin.
          reflexivity.
        }
        apply borel_Rbar_borel.
        generalize Rbar_lim_inf_rv.
        intros.
        typeclasses eauto.
    - simpl.
      unfold LpRRVnorm in H1.
      simpl in H1.
      assert (forall n0,
                 (n0 >= N)%nat ->
                 NonnegExpectation (fun omega : Ts => rvpower (rvabs (rvminus (f n0) (f n))) (const p) omega) <=
                 (power eps p)).
      {
        intros.
        specialize (H0 n n0 H1 H6).
        generalize (Rle_power_l (power (FiniteExpectation prts (rvpower (rvabs (rvminus (f n0) (f n))) (const p))) (/ p) ) (pos eps) p); intros.
        rewrite power_inv_cancel in H7.
        erewrite FiniteNonnegExpectation in H7.
        apply H7.
        lra.
        split; [apply power_nonneg |].
        erewrite FiniteNonnegExpectation in H0.
        left; apply H0.
        apply FiniteExpectation_pos.
        typeclasses eauto.
        lra.
      }
      replace (Finite (power eps p)) with (LimInf_seq (fun _ => power eps p)) by apply LimInf_seq_const.
      apply LimInf_le.
      exists N; intros.
      apply H6.
      lia.
  Qed.
    
  Lemma norm_rvminus_rvlim
        (f : nat -> LpRRV prts p) 
        (rvl : RandomVariable dom borel_sa (rvlim f)) 
        (isl : IsLp prts p (rvlim f)) :
    (forall x, ex_finite_lim_seq (fun n => f n x)) ->
    (forall (eps:posreal),
      exists (N : nat),
        forall (n m : nat), 
          (n >= N)%nat ->
          (m >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (f m) (f n))) < eps) ->
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.
  Proof.
    intros.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/2) by lra.
    generalize (norm_rvminus_rvlim_le f rvl isl H H0 (mkposreal _ H2)); intros.
    destruct H3 as [N ?].
    exists N.
    intros.
    eapply Rle_lt_trans.
    apply H3; trivial.
    simpl; lra.
  Qed.

  End complete1.

  Section complete2.
        
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Context {p:R}.
  Context (pbig:1 <= p).

  Let pnneg : nonnegreal := bignneg p pbig.
  Canonical pnneg.

  Global Instance event_restricted_islp P n (pf1 : ps_P P = 1) pf 
           (f : Ts -> R) 
           (isl:  IsLp  prts n f):
    IsLp (event_restricted_prob_space prts P pf) n (event_restricted_function P f).
  Proof.
    unfold IsLp, IsFiniteExpectation in *.
    now rewrite event_restricted_Expectation with (P0 := P) (pf0 := pf) in isl; trivial.
  Qed.

  Program Definition event_restricted_LpRRV n P (pf1 : ps_P P = 1) pf (rv:LpRRV prts n) :
    LpRRV (event_restricted_prob_space prts P pf) n
    := {|
    LpRRV_rv_X := event_restricted_function P (LpRRV_rv_X _ rv)
      |} .
  Next Obligation.
    destruct rv.
    now apply event_restricted_islp.
  Qed.

  Lemma restricted_LpRRVminus P (pf1 : ps_P P = 1) pf
        (f g : LpRRV prts p) :
    LpRRV_seq 
      (LpRRVminus (event_restricted_prob_space prts P pf)
                  (event_restricted_LpRRV p P pf1 pf f)
                  (event_restricted_LpRRV p P pf1 pf g))
      (event_restricted_LpRRV p P pf1 pf (LpRRVminus prts f g)).
  Proof.
    easy.
  Qed.

  Lemma restricted_LpRRVnorm P (pf1 : ps_P P = 1) pf
        (f : LpRRV prts p) :
    LpRRVnorm prts f = LpRRVnorm (event_restricted_prob_space prts P pf)
                                 (event_restricted_LpRRV p P pf1 pf f).
  Proof.
    intros.
    unfold LpRRVnorm.
    f_equal.
    unfold FiniteExpectation.
    simpl.
    destruct (IsFiniteExpectation_Finite prts (rvpower (rvabs f) (const p))).
    destruct (IsFiniteExpectation_Finite 
                (event_restricted_prob_space prts P pf)
                (rvpower (rvabs (event_restricted_function P f)) (const p))).
    simpl.
    rewrite event_restricted_Expectation with (P0 := P) (pf0 := pf) in e; trivial.
    assert (rv_eq
              (event_restricted_function P (rvpower (rvabs f) (const p)))
              (rvpower (rvabs (event_restricted_function P f)) (const p))) by easy.
    rewrite (Expectation_ext H) in e.
    rewrite e in e0.
    now inversion e0.
  Qed.

  Lemma restricted_LpRRV_rvlim P (pf1 : ps_P P = 1) pf
        (f : nat -> LpRRV prts p) 
        (rv : RandomVariable dom borel_sa (rvlim (fun x : nat => f x)))
        (isl : IsLp prts p (rvlim (fun x : nat => f x)))
        (rve : RandomVariable (event_restricted_sigma P) borel_sa
         (rvlim (fun x : nat => event_restricted_LpRRV p P pf1 pf (f x)))) 
        (isle : IsLp (event_restricted_prob_space prts P pf) p
         (rvlim (fun x : nat => event_restricted_LpRRV p P pf1 pf (f x)))) :
    ps_P P = 1 ->
    LpRRV_seq 
      (pack_LpRRV (event_restricted_prob_space prts P pf)
                  (rvlim (fun x : nat => event_restricted_LpRRV p P pf1 pf (f x))))
      (event_restricted_LpRRV p P pf1 pf
                               (pack_LpRRV prts (rvlim (fun x : nat => f x)))).
  Proof.
    easy.
  Qed.

  Lemma norm_rvminus_rvlim_almostR2 
        (f : nat -> LpRRV prts p) 
        (rvl : RandomVariable dom borel_sa (rvlim f)) 
        (isl : IsLp prts p (rvlim f))
        (P : event dom) :
    ps_P P = 1 ->
    (forall x, P x -> ex_finite_lim_seq (fun n => f n x)) ->
    (forall (eps:posreal),
      exists (N : nat),
        forall (n m : nat), 
          (n >= N)%nat ->
          (m >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (f m) (f n))) < eps) ->
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.
  Proof.
    intros.
    pose (nts := event_restricted_domain P).
    pose (ndom := event_restricted_sigma P).
    assert (pf : 0 < ps_P P).
    rewrite H; lra.
    pose (nprts := event_restricted_prob_space prts P pf).
    pose (nf := fun n => event_restricted_LpRRV _ P H pf (f n)).
    pose (nrvlim := event_restricted_function P (rvlim f)).
    assert (rv_eq nrvlim (rvlim nf)) by easy.
    assert (nrvl : RandomVariable ndom borel_sa (rvlim nf)).
    {
      apply rvlim_rv.
      - typeclasses eauto.
      - intros.
        destruct omega; simpl.
        apply H0.
        now simpl.
    }
    assert (nisl : IsLp nprts p (rvlim nf)).
    {
      unfold nprts, nf.
      generalize (event_restricted_islp P p H pf _ isl); intros.
      apply H3.
    }
    generalize (norm_rvminus_rvlim nprts pbig nf nrvl nisl); intros.
    cut_to H3.
    - specialize (H3 eps).
      destruct H3 as [N ?].
      exists N.
      intros.
      specialize (H3 n H4).
      rewrite restricted_LpRRVnorm with (P := P) (pf := pf) (pf1 := H); trivial.
      unfold nprts in H3.
      rewrite <- restricted_LpRRVminus; trivial.
      unfold nf in H3.
      rewrite restricted_LpRRV_rvlim in H3; trivial.
      apply H3.
    - intros.
      unfold nf.
      unfold event_restricted_domain in x.
      apply H0.
      destruct x.
      now simpl.
    - intros.
      specialize (H1 eps0).
      destruct H1 as [N ?].
      exists N.
      intros.
      specialize (H1 n m H4 H5).
      unfold nprts, nf.
      generalize (restricted_LpRRVminus P H pf (f m) (f n)); intros.
      unfold pnneg in H6.
      rewrite (LpRRV_norm_sproper (event_restricted_prob_space prts P pf) _ _ H6).
      now rewrite  <- restricted_LpRRVnorm.
   Qed.
 

  Lemma two_pow_gt (r : R) :
    exists n, r < pow 2 n.
  Proof.
    assert (2 > 1) by lra.
    replace (2) with (Rabs 2) in H by (apply Rabs_right; lra).
    generalize (Pow_x_infinity 2 H r); intros.
    destruct H0 as [N ?].
    exists (S N).
    specialize (H0 N).
    rewrite Rabs_right in H0.
    cut_to H0; try lia.
    apply Rge_le in H0.
    eapply Rle_lt_trans.
    apply H0.
    replace (2^N) with (1 * (2^N)) by lra.
    simpl.
    apply Rmult_lt_compat_r; try lra.
    apply pow2_pos.
    left.
    apply pow2_pos.
  Qed.
        
  Lemma inv_two_pow_lt (eps : posreal) :
    exists n, / (pow 2 n) < eps.
  Proof.
    generalize (two_pow_gt (/ eps)); intros.
    destruct H.
    exists x.
    replace (pos eps) with (/ / eps) by
        (rewrite Rinv_involutive; trivial; apply Rgt_not_eq; apply cond_pos).
    apply Rinv_lt_contravar; trivial.
    apply Rmult_lt_0_compat.
    - apply Rinv_0_lt_compat, cond_pos.
    - apply pow2_pos.
  Qed.


  Lemma Npow_eps (eps : posreal) :
    exists (N : nat), 2 / (pow 2 N) < eps.
  Proof.
    generalize (cond_pos eps); intros.
    assert (0 < eps/2) by lra.
    generalize (inv_two_pow_lt (mkposreal _ H0)); intros.
    destruct H1 as [N ?].
    exists N.
    unfold Rdiv.
    rewrite Rmult_comm.
    apply Rmult_lt_reg_r with (r := /2).
    apply Rinv_0_lt_compat; lra.
    rewrite Rmult_assoc.
    rewrite <- Rinv_r_sym; try lra.
    rewrite Rmult_1_r.
    unfold Rdiv in H1.
    apply H1.
  Qed.

  Lemma LpRRVnorm_rvminus_rvlim_almostR2 
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal)
        (rv : RandomVariable dom borel_sa (rvlim (fun n : nat => LpRRV_lim_picker prts pbig F PF cF (S n)))) 
        (islp : IsLp prts p (rvlim (fun n : nat => LpRRV_lim_picker prts pbig F PF cF (S n)))):
    let f := fun n => LpRRV_lim_picker prts pbig F PF cF (S n)  in 
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.

  Proof.
    unfold cauchy in cF.
    generalize (cauchy_filter_rvlim_finite2 prts pbig F PF cF); intros.
    destruct X as [P [dec [? [? ?]]]].
    apply norm_rvminus_rvlim_almostR2  with (P := P); trivial.
    - intros.
      specialize (H0 x).
      rewrite ex_finite_lim_seq_ext in H0.
      apply H0.
      intros.
      unfold rvmult, EventIndicator.
      match_destr; try tauto.
      subst f.
      lra.
    - intros.
      generalize (lim_filter_cauchy prts pbig F PF cF); intros.
      generalize (Npow_eps eps1); intros.
      destruct H3 as [N ?].
      exists N; intros.
      specialize (H2 N (S m) (S n)).
      subst f.
      eapply Rlt_trans.
      apply H2; try lia.
      apply H3.
   Qed.
  
  Global Instance IsLp_EventIndicator_mult {P : event dom} (dec : forall x, {P x} + {~ P x}) 
         (rv_X: Ts -> R)
         {rv : RandomVariable dom borel_sa rv_X}
         {islp:IsLp prts p rv_X} :
    IsLp prts p (rvmult (EventIndicator dec) rv_X).
  Proof.
    generalize (IsLp_bounded prts p (rvmult (EventIndicator dec) rv_X) (rvpower (rvabs rv_X) (const p))); intros.
    apply H; trivial.
    intro x.
    unfold rvpower, rvabs, rvmult, const, EventIndicator.
    apply Rle_power_l.
    lra.
    split.
    apply Rabs_pos.
    match_destr.
    - rewrite Rmult_1_l; now right.
    - rewrite Rmult_0_l.
      rewrite Rabs_R0.
      apply Rabs_pos.
  Qed.

  Definition LpRRVindicator {P : event dom} (dec : forall x, {P x} + {~ P x}) (rv : LpRRV prts p) : LpRRV prts p
    :=  pack_LpRRV prts (rvmult (EventIndicator dec) rv).

  Instance rvlim_rv_almostR2_P 
           (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
           (PF:ProperFilter F)
           (cF:cauchy F)
           {P : event dom} 
           (dec : forall x, {P x} + {~ P x})
           (pf:forall x : Ts,
               ex_finite_lim_seq
                 (fun n : nat => rvmult (EventIndicator dec) (LpRRV_lim_picker prts pbig F PF cF (S n)) x)):
    let f := fun n : nat => LpRRVindicator dec (LpRRV_lim_picker prts pbig F PF cF (S n)) in
    RandomVariable dom borel_sa (rvlim f).
  Proof.
    intros.
    subst f.
    apply rvlim_rv.
    unfold LpRRVindicator.
    unfold pack_LpRRV; simpl.
    typeclasses eauto.
    intros.
    eauto.
  Qed.

  Lemma LpRRVminus_indicator_comm {P : event dom} (dec : forall x, {P x} + {~ P x})
        (f g : LpRRV prts p) :
    LpRRV_seq
      (LpRRVminus prts (LpRRVindicator dec f) (LpRRVindicator dec g))
      (LpRRVindicator dec (LpRRVminus prts f g)).
  Proof.
    intro x.
    unfold LpRRVindicator.
    unfold LpRRVminus, pack_LpRRV; simpl.
    unfold EventIndicator, rvminus, rvmult, rvplus, rvopp, rvscale.
    match_destr; lra.
  Qed.

  Lemma LpRRVnorm_indicator {P : event dom} (dec : forall x, {P x} + {~ P x})
        (f : LpRRV prts p) :
    ps_P P = 1 ->
    LpRRVnorm prts f = LpRRVnorm prts (LpRRVindicator dec f).
  Proof.
    intros.
    unfold LpRRVnorm.
    f_equal.
    apply FiniteExpectation_proper_almostR2.
    typeclasses eauto.
    typeclasses eauto.
    unfold almostR2.
    exists P.
    split; trivial.
    intros.
    unfold LpRRVindicator, pack_LpRRV; simpl.
    unfold rvpower, rvabs, const, rvmult, EventIndicator.
    match_destr.
    - now rewrite Rmult_1_l.
    - tauto.
  Qed.

  Lemma LpRRVnorm_rvminus_rvlim_almostR2_P
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal):
    let '(existT P (exist dec _)) := (cauchy_filter_rvlim_finite2 prts pbig F PF cF) in
    let f := fun n : nat => LpRRVindicator dec (LpRRV_lim_picker prts pbig F PF cF (S n)) in 
    exists (rv:RandomVariable dom borel_sa (rvlim f)),
    exists (isl: IsLp prts p (rvlim f)),
    ps_P P = 1 /\
    (forall x : Ts, ex_finite_lim_seq (fun n : nat => f n x)) /\
    forall (eps : posreal),
      exists (N : nat),
        forall (n : nat), 
          (n >= N)%nat ->
          (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts (rvlim f)) (f n))) < eps.
  Proof.
    unfold cauchy in cF.
    destruct (cauchy_filter_rvlim_finite2 prts pbig F PF cF)
             as [P [dec [? [? ?]]]].
    intros.
    exists (rvlim_rv_almostR2_P _ _ _ _ H0).
    exists H1.
    generalize ( norm_rvminus_rvlim_almostR2 f); intros.
    simpl.
    split; trivial.
    split; trivial.
    intros.
    subst f.
    specialize (H2 (rvlim_rv_almostR2_P F PF cF dec H0)).
    specialize (H2 H1 P H).
    apply H2; [intros; apply H0 |].
    intros.
    generalize (lim_filter_cauchy prts pbig F PF cF); intros.
    generalize (Npow_eps eps1); intros.
    destruct H4 as [N ?].
    exists N; intros.
    specialize (H3 N (S m) (S n) ).
    cut_to H3; try lia.
    rewrite LpRRVminus_indicator_comm .
    rewrite <- LpRRVnorm_indicator; trivial.
    eapply Rlt_trans.
    apply H3.
    apply H4.
  Qed.

  Lemma LpRRVnorm_LpRRV_cauchy_picker
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal) :
    exists (N : nat),
    exists (x : LpRRV prts p),
      (F (Hierarchy.ball x eps)) /\
      (forall (n:nat), (n >= N)%nat ->
                       ((Hierarchy.ball (M := LpRRV_UniformSpace prts pbig) x eps) 
                          (LpRRV_lim_picker prts pbig F PF cF n))).
   Proof.
     intros.
     generalize (inv_two_pow_lt eps); intros.
     destruct H as [N ?].
     generalize (lim_picker_center_included2 prts pbig F PF cF N); intros.
     pose (x0 := (LpRRV_lim_ball_center_center prts pbig F PF cF N)).     
     exists N.
     exists (proj1_sig x0).
     intros.
     generalize (ball_le (M:= LpRRV_UniformSpace prts pbig) (proj1_sig x0) (mkposreal _ (inv_pow_2_pos N)) eps); intros.
     split.
     - destruct x0.
       simpl in *.
       eapply filter_imp; try eapply f.
       apply ball_le.
       lra.
     - intros.
       specialize (H0 n).
       apply H1.
       now left.
       now apply H0.
   Qed.

   Lemma ball_LpRRV_lim_picker
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal) :
     exists (N : nat),
       forall (n : nat), (n >= N)%nat ->
                         (Hierarchy.ball (M := LpRRV_UniformSpace prts pbig) 
                                         (LpRRV_lim_picker prts pbig F PF cF (S n)) eps (LpRRV_lim prts pbig F)).
     Proof.
       generalize (LpRRVnorm_rvminus_rvlim_almostR2_P F PF cF eps); intros.
       match_case_in H; intros.
       rewrite H0 in H.
       match_destr_in H.
       simpl in H.
       destruct H as [? [? [? [? ?]]]].
       specialize (H2 eps).
       destruct H2 as [N ?].
       exists N.
       intros.
       specialize (H2 n H3).
       unfold LpRRV_lim.
       match_destr; try tauto.
       match_destr; try tauto.
       do 2 red; simpl.
       unfold LpRRV_lim_with_conditions.
       unfold LpRRVball, LpRRVnorm.
       unfold LpRRVnorm in H1.
       unfold bignneg; simpl.
       assert ((FiniteExpectation prts (rvpower (rvabs (rvminus (LpRRV_lim_picker prts pbig F PF cF (S n)) (cauchy_rvlim_fun prts pbig F p0 c))) (const p))) =
                 (FiniteExpectation prts
            (rvpower
               (rvabs
                  (LpRRVminus prts
                     (pack_LpRRV prts (rvlim (fun n : nat => rvmult (EventIndicator x0) (LpRRV_lim_picker prts pbig F PF cF (S n)))))
                     (LpRRVindicator x0 (LpRRV_lim_picker prts pbig F PF cF (S n))))) (const p)))).
       {
         apply FiniteExpectation_proper_almostR2.       
         typeclasses eauto.
         typeclasses eauto.
         unfold almostR2.
         exists x.
         split; trivial.
         intros.
         unfold rvpower, const.
         f_equal.
         unfold rvabs, LpRRVminus, pack_LpRRV; simpl.
         unfold rvminus, rvplus, rvopp, rvscale, cauchy_rvlim_fun.
         rewrite (proof_irrelevance _ p0 PF).
         rewrite (proof_irrelevance _ c cF).
         rewrite H0.
         rewrite <- Rabs_Ropp at 1.
         f_equal.
         rewrite Rplus_comm.
         ring_simplify.
         f_equal.
         unfold EventIndicator, rvmult.
         match_destr.
         lra.
         tauto.
       }
       unfold LpRRVnorm, LpRRVminus, pack_LpRRV in H2.
       simpl in H2.
       clear H0.
       clear a.
       erewrite FiniteExpectation_pf_irrel; rewrite H4.
       erewrite FiniteExpectation_pf_irrel in H2.
       apply H2.
     Qed.

  Lemma LpRRVnorm_LpRRV_lim
        (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
        (PF:ProperFilter F)
        (cF:cauchy F)
        (eps : posreal) :
    exists (x : LpRRV prts p),
      (F (Hierarchy.ball x eps)) /\
      ((Hierarchy.ball (M := LpRRV_UniformSpace prts pbig) x eps) (LpRRV_lim prts pbig F)).
  Proof.
    generalize (cond_pos eps); intro eps_pos.
    assert (eps_half: 0 < eps/2) by lra.
    generalize (LpRRVnorm_LpRRV_cauchy_picker F PF cF (mkposreal _ eps_half)); intros.
    destruct H as [N [x [? ?]]].
    exists x.
    split.
    - generalize (ball_le (M:= LpRRV_UniformSpace prts pbig) x (mkposreal _ eps_half) eps); intros.
      eapply filter_imp.
      apply H1.
      simpl; lra.
      apply H.
    - generalize (ball_LpRRV_lim_picker F PF cF (mkposreal _ eps_half)); intros.
      destruct H1.
      specialize (H0 (S (max N x0))).
      cut_to H0; try lia.
      specialize (H1 (max N x0)).
      cut_to H1; try lia.
      replace (pos eps) with ((mkposreal _ eps_half) + (mkposreal _ eps_half)) by (simpl; lra).
      now apply Hierarchy.ball_triangle with (y := (LpRRV_lim_picker prts pbig F PF cF (S (max N x0)))).
   Qed.      

  Lemma L2RRV_lim_complete (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop) 
        (PF : ProperFilter F)
        (cF : cauchy F) :
    forall eps : posreal, F (Hierarchy.ball (LpRRV_lim  prts pbig F) eps).
  Proof.
    intros.
    assert (0 < eps/2).
    {
      apply Rlt_div_r; try lra.
      rewrite Rmult_0_l.
      apply cond_pos.
    }
    generalize (LpRRVnorm_LpRRV_lim F PF cF (mkposreal _ H)); intros.
    destruct H0 as [? [? ?]].
    generalize (Hierarchy.ball_triangle 
                  (M := LpRRV_UniformSpace prts pbig)); intros.
    apply filter_imp with (P := (Hierarchy.ball x (mkposreal _ H))); trivial.
    intros.
    apply Hierarchy.ball_sym in H1.
    replace (pos eps) with ((pos (mkposreal _ H)) + (pos (mkposreal _ H))).
    apply (Hierarchy.ball_triangle _ _ _ _ _ H1 H3).
    simpl; lra.
  Qed.

  Program Definition LpRRVq_lim_with_conditions (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
          (PF:ProperFilter F)
          (cF:cauchy F) : LpRRVq prts p
    := Quot _ (LpRRV_lim_with_conditions prts pbig F PF cF).

  Lemma LpRRVq_lim_with_conditionsE F PF cF : LpRRVq_lim_with_conditions F PF cF  = Quot _ (LpRRV_lim_with_conditions prts pbig F PF cF).
  Proof.
    reflexivity. 
  Qed.
  
  Hint Rewrite LpRRVq_lim_with_conditionsE : quot.

  Definition LpRRV_toLpRRVq_set (s:(LpRRV prts p)->Prop) (x:LpRRVq prts p) : Prop
    := forall y, x = Quot _ y -> s y.

  Definition LpRRVq_filter_to_LpRRV_filter (F:((LpRRVq prts p)->Prop)->Prop) : ((LpRRV prts p)->Prop)->Prop
    := (fun x:(LpRRV prts p)->Prop => F (LpRRV_toLpRRVq_set x)).
  
  Lemma LpRRVq_filter_to_LpRRV_filter_filter (F:((LpRRVq prts p)->Prop)->Prop) 
        (FF:Filter F) :
    Filter (LpRRVq_filter_to_LpRRV_filter F).
  Proof.
    destruct FF.
    unfold LpRRVq_filter_to_LpRRV_filter, LpRRV_toLpRRVq_set.
    constructor; intros.
    - eapply filter_imp; try eapply filter_true; intros.
      destruct (Quot_inv x); subst.
      eauto.
    - generalize (filter_and _ _ H H0); intros HH.
      eapply filter_imp; try eapply HH; intros ? [??].
      intros; subst.
      specialize (H1 _ (eq_refl _)).
      specialize (H2 _ (eq_refl _)).
      tauto.
    - eapply filter_imp; try eapply H0; simpl; intros.
      subst.
      apply H.
      now apply H1.
  Qed.

  Lemma LpRRVq_filter_to_LpRRV_filter_proper (F:((LpRRVq prts p)->Prop)->Prop) 
        (PF:ProperFilter F) :
    ProperFilter (LpRRVq_filter_to_LpRRV_filter F).
  Proof.
    destruct PF.
    constructor.
    - intros.
      destruct (filter_ex (LpRRV_toLpRRVq_set P) H).
      destruct (Quot_inv x); subst.
      exists x0.
      unfold LpRRV_toLpRRVq_set in *.
      now apply H0.
    - now apply LpRRVq_filter_to_LpRRV_filter_filter.
  Qed.

  Lemma rvpower2 (x:Ts->R) {posx:NonnegativeFunction x} : rv_eq (rvpower x (const 2)) (rvsqr x).
  Proof.
    intros ?.
    unfold rvpower, rvsqr, const.
    apply power2_sqr.
    apply posx.
  Qed.
          
  Lemma LpRRVq_filter_to_LpRRV_filter_cauchy
        (F : (LpRRVq_UniformSpace prts p pbig -> Prop) -> Prop)
    (PF:ProperFilter F)
    (cF:cauchy F) : 
    @cauchy (LpRRV_UniformSpace prts pbig) (LpRRVq_filter_to_LpRRV_filter F).
  Proof.
    unfold cauchy ; intros.
    destruct (cF eps) as [??]; simpl in *.
    unfold LpRRVq_filter_to_LpRRV_filter, LpRRV_toLpRRVq_set.
    destruct (Quot_inv x); subst.
    exists x0.
    eapply filter_imp; try eapply H; intros; subst.
    repeat red.
    do 2 red in H0.
    simpl in H0.
    rewrite LpRRVq_ballE in H0.
    apply H0.
  Qed.

  Definition LpRRVq_lim_with_conditions2 (F : (LpRRVq_UniformSpace prts p pbig -> Prop) -> Prop)
    (PF:ProperFilter F)
    (cF:cauchy F) : LpRRVq prts p.
    Proof.
      simpl in F.
      pose (LpRRVq_filter_to_LpRRV_filter F).
      generalize (LpRRVq_lim_with_conditions P); intros.
      specialize (X (LpRRVq_filter_to_LpRRV_filter_proper F PF)).
      specialize (X (LpRRVq_filter_to_LpRRV_filter_cauchy F PF cF)).
      exact X.
  Defined.

  Definition LpRRVq_lim (lim : ((LpRRVq prts p -> Prop) -> Prop)) : LpRRVq prts p.
  Proof.
    destruct (excluded_middle_informative (ProperFilter lim)).
    - destruct (excluded_middle_informative (cauchy (T:=LpRRVq_UniformSpace prts p pbig) lim)).
      + exact (LpRRVq_lim_with_conditions2 _ p0 c).
      + exact (LpRRVq_zero prts).
    - exact (LpRRVq_zero prts).
  Defined.

  Lemma LpRRVq_lim_complete (F : (LpRRVq_UniformSpace prts p pbig -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (LpRRVq_ball prts pbig (LpRRVq_lim F) eps).
  Proof.
    intros.
    unfold LpRRVq_lim; simpl.
    match_destr; [| tauto].
    match_destr; [| tauto].
    generalize (L2RRV_lim_complete (LpRRVq_filter_to_LpRRV_filter F)); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_proper F H); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_cauchy F H H0); intros.
    specialize (H1 H2 H3 eps).
    unfold LpRRV_lim in H1; simpl in H1.
    match_destr_in H1; [|tauto].
    match_destr_in H1; [|tauto].
    unfold Hierarchy.ball, UniformSpace.ball in H1; simpl in H1.
    unfold LpRRVq_lim_with_conditions2.
    rewrite  LpRRVq_lim_with_conditionsE.
    rewrite (proof_irrelevance _ _ p1).
    rewrite (proof_irrelevance _ _ c0).
    unfold LpRRVq_filter_to_LpRRV_filter in *.
    eapply filter_imp; try eapply H1.
    intros x; simpl in *.

    unfold LpRRV_toLpRRVq_set; simpl; intros HH.
    unfold ball, minus, plus, opp; simpl.
    destruct (Quot_inv x); subst.
    rewrite LpRRVq_ballE.
    specialize (HH _ (eq_refl _)).
    unfold LpRRVball in *.
    eapply Rle_lt_trans; try eapply HH.
    unfold LpRRVnorm.
    apply Rle_power_l; [| split].
    - simpl.
      left; apply Rinv_pos; lra.
    - apply FiniteExpectation_pos.
      typeclasses eauto.
    - apply FiniteExpectation_le.
      reflexivity.
  Qed.

  Lemma LpRRVq_lim_close (F1 F2 : (LpRRVq_UniformSpace prts p pbig -> Prop) -> Prop) :
    filter_le F1 F2 ->
    filter_le F2 F1 ->
    @close (LpRRVq_UniformSpace prts p pbig) (LpRRVq_lim F1) (LpRRVq_lim F2).
  Proof.
    intros.
    replace F1 with F2.
    apply close_refl.
    apply functional_extensionality.
    intros x.
    unfold filter_le in *.
    apply propositional_extensionality; split.
    apply H.
    apply H0.
  Qed.

  Definition LpRRVq_Complete_mixin : CompleteSpace.mixin_of (LpRRVq_UniformSpace prts p pbig)
    := CompleteSpace.Mixin (LpRRVq_UniformSpace prts p pbig)
                           LpRRVq_lim
                           LpRRVq_lim_complete
                           LpRRVq_lim_close.


  Canonical LpRRVq_Complete :=
    CompleteSpace.Pack (LpRRVq prts p)
                       (CompleteSpace.Class _ (LpRRVq_UniformSpace_mixin prts pbig)
                                            LpRRVq_Complete_mixin)
                       (LpRRVq prts p).

  Canonical LpRRVq_CompleteNormedModule :=
        CompleteNormedModule.Pack R_AbsRing (LpRRVq prts p)
                                  (CompleteNormedModule.Class
                                     R_AbsRing (LpRRVq prts p)
                                     (NormedModule.class R_AbsRing 
                                                         (LpRRVq_NormedModule prts p pbig))
                                  LpRRVq_Complete_mixin)
                                  (LpRRVq prts p).

  End complete2.

End complete.

Section more_Lp_props.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Global Instance EventIndicator_islp (p:nonnegreal) {P} (dec : dec_pre_event P) :
    IsLp prts p (EventIndicator dec).
  Proof.
    unfold IsLp.
    apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
    - apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_const.
    - intro x.
      unfold const, rvpower.
      apply power_nonneg.
    - intro x.
      unfold rvpower, const.
      replace (1) with (power 1 p).
      + apply Rle_power_l.
        { apply cond_nonneg.
        } 
        unfold rvabs.
        split.
        * apply Rabs_pos.
        * unfold EventIndicator.
          match_destr.
          -- rewrite Rabs_R1; lra.
          -- rewrite Rabs_R0; lra.
      + now rewrite power_base_1.
  Qed.

  Lemma LpRRVnorm_minus_sym {p:nonnegreal} (x y : LpRRV prts p) :
    LpRRVnorm prts (LpRRVminus prts x y) = LpRRVnorm prts (LpRRVminus prts y x).
  Proof.
    unfold LpRRVnorm, LpRRVminus.
    f_equal.
    apply FiniteExpectation_ext.
    intro z.
    unfold rvpower, rvabs, pack_LpRRV; f_equal; simpl.
    do 2 rewrite rvminus_unfold.
    apply Rabs_minus_sym.
  Qed.

  Definition LpRRV_dist {p:nonnegreal} (x y : LpRRV prts p) := 
    LpRRVnorm prts (LpRRVminus prts x y).

  Lemma LpRRV_norm_dist {p:nonnegreal} (x y : LpRRV prts p) :
    LpRRV_dist x y = LpRRVnorm prts (LpRRVminus prts x y).  
  Proof.
    easy.
  Qed.
  
  Lemma LpRRV_dist_comm {p:nonnegreal} (x y : LpRRV prts p) :
    LpRRV_dist x y = LpRRV_dist y x.
  Proof.
    unfold LpRRV_dist, LpRRVnorm, LpRRVminus.
    f_equal.
    apply FiniteExpectation_ext.
    intro z.
    unfold rvpower, rvabs, pack_LpRRV.
    f_equal.
    simpl.
    do 2 rewrite rvminus_unfold.
    now rewrite Rabs_minus_sym.
  Qed.

  Lemma LpRRV_dist_triang {p:R} (pbig:1<= p) (x y z : LpRRV prts p) :
    LpRRV_dist (p := bignneg _ pbig) x z <= LpRRV_dist (p := bignneg _ pbig) x y + LpRRV_dist (p := bignneg _ pbig) y z.
  Proof.
    unfold LpRRV_dist.
    generalize (LpRRV_norm_plus prts pbig (LpRRVminus prts (p := bignneg _ pbig) x y) (LpRRVminus prts (p := bignneg _ pbig) y z)); intros.
    do 2 rewrite LpRRVminus_plus in H.
    rewrite <- LpRRV_plus_assoc in H.
    rewrite (LpRRV_plus_assoc prts (p := bignneg _ pbig) (LpRRVopp prts y) _) in H.     
    rewrite (LpRRV_plus_comm prts (p := bignneg _ pbig) _ y) in H.
    rewrite LpRRV_plus_inv in H.
    rewrite (LpRRV_plus_comm prts (p := bignneg _ pbig) (LpRRVconst prts 0) _ ) in H.
    rewrite LpRRV_plus_zero in H.
    now repeat rewrite <- LpRRVminus_plus in H.
  Qed.  

End more_Lp_props.

Section sa_sub.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).
  
  Lemma IsLp_prob_space_sa_sub
        p (x:Ts->R)
        {rv:RandomVariable dom2 borel_sa x} :
    IsLp prts p x <->
    IsLp (prob_space_sa_sub prts sub) p x.
  Proof.
    unfold IsLp, IsFiniteExpectation; intros.
    now rewrite Expectation_prob_space_sa_sub by typeclasses eauto.
  Qed.

  Definition LpRRV_sa_sub p
             (x: LpRRV (prob_space_sa_sub prts sub) p) : LpRRV prts p
    := pack_LpRRV _ x
                  (rv:=RandomVariable_sa_sub sub x)
                  (lp:=(proj2 (IsLp_prob_space_sa_sub p x)) _).

  Definition LpRRV_sa_sub_f p
             (x:LpRRV prts p)
             {rv:RandomVariable dom2 borel_sa x}
    : LpRRV (prob_space_sa_sub prts sub) p
    := pack_LpRRV _ x (lp:=(proj1 (IsLp_prob_space_sa_sub p x)) _).

  Lemma LpRRV_sa_sub_b_f p (x:LpRRV prts p)
        {rv:RandomVariable dom2 borel_sa x} :
    LpRRV_seq (LpRRV_sa_sub p (LpRRV_sa_sub_f p x)) x.
  Proof.
    intros ?.
    now destruct x; simpl.
  Qed.    

  Lemma LpRRV_sa_sub_f_b p (x:LpRRV (prob_space_sa_sub prts sub) p) :
    LpRRV_seq (LpRRV_sa_sub_f p (LpRRV_sa_sub p x) (rv:=LpRRV_rv _ _)) x.
  Proof.
    intros ?.
    now destruct x; simpl.
  Qed.    

End sa_sub.
