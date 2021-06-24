Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import Reals.
Require Import FunctionalExtensionality.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq Coquelicot.Hierarchy.

Require Export RandomVariableFinite RandomVariableLpR.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section Linf.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Lemma sa_le_gt_rv (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : sa_sigma (fun omega => (rvabs rv_X) omega > x).
  Proof.
    apply sa_le_gt.
    apply rv_measurable.
    typeclasses eauto.
  Qed.

  Definition Linfty_term (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    := exist _ (fun omega => (rvabs rv_X) omega > x) (sa_le_gt_rv _ _).
  
  Definition Linfty_norm (rv_X : Ts -> R) 
             {rv : RandomVariable dom borel_sa rv_X} : Rbar :=
    Glb_Rbar (fun (x : R) =>
                ps_P (Linfty_term rv_X x) = 0).

  Class IsLinfty (rv_X : Ts -> R) 
             {rv : RandomVariable dom borel_sa rv_X}  :=
    is_linfty : is_finite (Linfty_norm rv_X).

  Lemma empty_glb_inf (E : R -> Prop) :
    (forall (r:R), ~ E r) -> is_glb_Rbar E p_infty.
  Proof.
    unfold is_glb_Rbar, is_lb_Rbar.
    split; intros.
    - specialize (H x).
      tauto.
    - unfold Rbar_le.
      match_destr.
    Qed.
      
  Lemma is_finite_glb (E : R -> Prop) :
    (exists (z:Rbar), is_glb_Rbar E z /\ is_finite z) -> exists (r:R), E r.
  Proof.
    intros.
    destruct H as [z [? ?]].
    generalize (empty_glb_inf E); intros.
    apply imply_to_or in H1.
    destruct H1.
    - now apply not_all_not_ex in H1.
    - apply is_glb_Rbar_unique in H1.
      apply is_glb_Rbar_unique in H.
      rewrite H in H1.
      rewrite H1 in H0.
      discriminate.
  Qed.

  Lemma finite_glb (E : R -> Prop) :
    is_finite (Glb_Rbar E) -> exists (r:R), E r.
  Proof.
    unfold Glb_Rbar.
    destruct (ex_glb_Rbar E); simpl.
    intros.
    apply is_finite_glb.
    exists x.
    tauto.
  Qed.

  Lemma abs_neg_psall (rv_X : Ts -> R) (r:R)
        {rv : RandomVariable dom borel_sa rv_X} :        
    ps_P (Linfty_term rv_X r) = 0 -> 0<=r.
  Proof.
    destruct (Rle_dec 0 r); intros; trivial.
    assert (event_equiv (Linfty_term rv_X r) Ω).
    intro x0.
    unfold rvabs.
    generalize (Rabs_pos (rv_X x0)); intros.
    unfold  Ω, pre_Ω; simpl.
    unfold rvabs.
    split; trivial; intros.
    lra.
    rewrite H0 in H.
    rewrite ps_all in H.
    lra.
  Qed.  
    
  Lemma is_Linfty_c_nonneg (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {isl:IsLinfty rv_X} :
    exists (c:nonnegreal), ps_P  (Linfty_term rv_X c) = 0.
  Proof.
    unfold IsLinfty, Linfty_norm in *.
    apply finite_glb in isl.
    destruct isl.
    destruct (Rle_dec 0 x).
    - exists (mknonnegreal _ r).
      now simpl.
    - assert (0 > x) by lra.
      assert (event_equiv  (Linfty_term rv_X x) Ω ).
      + intro x0.
        unfold rvabs.
        generalize (Rabs_pos (rv_X x0)); intros.
        unfold  Ω, pre_Ω; simpl. unfold rvabs.
        intuition lra.
      + rewrite H1 in H.
        generalize (ps_all prts); intros.
        rewrite H in H2.
        lra.
    Qed.                          

  Lemma Linfty_norm_nneg (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {isl:IsLinfty rv_X} :
      0 <= Linfty_norm rv_X.
  Proof.
    intros.
    generalize (Glb_Rbar_correct (fun x : R => ps_P (Linfty_term rv_X x) = 0)); intros.    
    unfold is_glb_Rbar in H.
    destruct H.
    destruct (Rle_dec 0 (Linfty_norm rv_X)); trivial.
    assert (0 > Linfty_norm rv_X) by lra.
    unfold Linfty_norm in H1.
    specialize (H0 0).
    unfold IsLinfty, Linfty_norm in isl.
    rewrite <- isl in H0.
    simpl in H0.
    cut_to H0.
    lra.
    unfold is_lb_Rbar; intros.
    simpl.
    now apply (abs_neg_psall rv_X x).
  Qed.

  Lemma rvclip_almost_bounded (rv_X : Ts -> R) (c : nonnegreal)
        {rv : RandomVariable dom borel_sa rv_X} :
    ps_P  (Linfty_term rv_X c) = 0 ->
    almost prts eq rv_X (rvclip rv_X c).
 Proof.
   intros.
   apply almost_alt_eq.
   exists (Linfty_term rv_X c).
   split; trivial.
   unfold rvclip, Linfty_term, rvabs.
   intros a neq.
   match_destr_in neq; simpl.
   - unfold Rabs.
     match_destr; lra.
   - match_destr_in neq.
     + assert (- rv_X a > c) by lra.
       generalize (Rcomplements.Rabs_maj2 (rv_X a)); intros.
       lra.
     + lra.
 Qed.

 Lemma rvclip_almost_bounded_exists (rv_X : Ts -> R)
        (rv : RandomVariable dom borel_sa rv_X)
        {isl:IsLinfty rv_X} :
    exists (c:nonnegreal), almost prts eq rv_X (rvclip rv_X c).
  Proof.
    destruct (is_Linfty_c_nonneg rv_X).
    exists x.
    now eapply rvclip_almost_bounded.
  Qed.

  Lemma zero_prob_bound
        (rv_X : Ts -> R)         
        {rv : RandomVariable dom borel_sa rv_X} : 
    forall (c1 c2 : R),
      c1 <= c2  ->
      ps_P (Linfty_term rv_X c1) = 0 ->
      ps_P (Linfty_term rv_X c2) = 0.
  Proof.
    intros.
    assert (event_sub (Linfty_term rv_X c2)
                      (Linfty_term rv_X c1))
           by (intros ?; simpl; unfold rvabs; lra).

    assert (ps_P (Linfty_term rv_X c2) <=
            ps_P (Linfty_term rv_X c1))
           by now apply ps_sub.
    generalize (ps_pos (Linfty_term rv_X c2)); intros.
    lra.
  Qed.

  Lemma zero_prob_bound_Linfty
        (rv_X : Ts -> R)         
        {rv : RandomVariable dom borel_sa rv_X}
        {isl:IsLinfty rv_X} :
    forall (c : R),
      (0 < c  ->
       ps_P (Linfty_term rv_X (Linfty_norm rv_X + c))  = 0).
  Proof.
     rename isl into H.
     intros.
     unfold IsLinfty, Linfty_norm in H.
     generalize (Glb_Rbar_correct (fun x : R => ps_P (Linfty_term rv_X x) = 0)); intros.
     unfold is_glb_Rbar in H1.
     destruct H1.
     rewrite <- H in H1; simpl in H1.
     destruct (classic (exists (y:R), (Linfty_norm rv_X <= y <= Linfty_norm rv_X + c) /\
                                      ps_P (Linfty_term rv_X y) = 0)).
     - destruct H3 as [y [? ?]].
       apply zero_prob_bound with (c1 := y); trivial; lra.
     - specialize (H2 (Linfty_norm rv_X + c)).
       cut_to H2.
       unfold Linfty_norm in H2.
       do 3 rewrite <- H in H2; simpl in H2.
       lra.

       generalize (not_ex_all_not _ _ H3)
       ; intros HH.
       red; intros.
       specialize (HH x).
       apply not_and_or in HH.
       destruct HH; try congruence.
       apply not_and_or in H5.
       destruct H5.
       + red in H1.
         specialize (H1 _ H4).
         red in H1.
         tauto.
       + red; lra.
   Qed.

  Lemma Linfty_norm_contains_finite_lim (rv_X : Ts -> R) 
        {rv : RandomVariable dom borel_sa rv_X}
        {isl:IsLinfty rv_X} :
      ps_P  (Linfty_term rv_X (Linfty_norm rv_X)) = 0.
  Proof.
    generalize (lim_prob (fun n => (Linfty_term rv_X ((Linfty_norm rv_X) + / INR (S n))))
                         (Linfty_term rv_X (Linfty_norm rv_X))); intros.
     cut_to H.
    - assert (forall n, ps_P
                     (Linfty_term rv_X (Linfty_norm rv_X + / INR (S n))) = 0).
      + generalize (zero_prob_bound_Linfty rv_X); intros.
         apply H0.
         apply Rinv_0_lt_compat.
         apply lt_0_INR; lia.
       + apply is_lim_seq_ext with (v := fun _ => 0) in H; trivial.
         generalize (is_lim_seq_const 0); intros.
         generalize (is_lim_seq_unique); intros.
         apply is_lim_seq_unique in H.
         apply is_lim_seq_unique in H1.
         rewrite H in H1.
         now rewrite Rbar_finite_eq in H1.
    - unfold event_sub, pre_event_sub; intros. 
       apply Rgt_trans with (r2 :=  Linfty_norm rv_X + / INR (S n)); trivial.
       apply Rplus_gt_compat_l.
       apply Rinv_1_lt_contravar.
       + replace (1) with (0 + 1) by lra.
         rewrite S_INR.
         apply Rplus_le_compat_r.
         apply pos_INR.
       + apply lt_INR; lia.
     - intro x.
       unfold union_of_collection.
       split; intros.
       + destruct H0.
         replace (real(Linfty_norm rv_X)) with (real (Linfty_norm rv_X) + 0) by lra.
         apply Rgt_trans with (r2 := Linfty_norm rv_X + / INR (S x0)); trivial.
         apply Rplus_gt_compat_l.
         apply Rinv_0_lt_compat.
         apply lt_0_INR; lia.
       + exists (Z.to_nat (up (/ (rvabs rv_X x - Linfty_norm rv_X)))).
         apply Rplus_gt_reg_l with (r := - Linfty_norm rv_X).
         ring_simplify.
         rewrite Rplus_comm.
         rewrite <- (Rinv_involutive  (rvabs rv_X x + - Linfty_norm rv_X)).
         * apply Rinv_lt_contravar.
           -- apply Rmult_lt_0_compat.
              ++ simpl in *; apply Rinv_0_lt_compat; lra.
              ++ apply lt_0_INR; lia.
           -- assert (forall (r:R), 0 < r -> r < INR (S (Z.to_nat (up r)))); intros.
              ++ rewrite S_INR.
                 rewrite INR_up_pos.
                 ** generalize (archimed r); intros.
                    destruct H2; lra.
                 ** lra.
              ++ apply H1.
                 simpl in *.
                 apply Rinv_0_lt_compat; lra.
         * simpl in *; apply Rgt_not_eq; lra.
   Qed.

  Instance IsLp_const_bounded (n:R) (rv_X : Ts -> R) (bound : R)
           {rv : RandomVariable dom borel_sa rv_X} :
    0 <= n ->
    rv_le (rvabs rv_X) (const bound) ->
    IsLp prts n rv_X.
  Proof.
    generalize (IsLp_bounded prts n rv_X (const (power bound n))); intros.
    apply H
    ; try typeclasses eauto.
    unfold rvpower, rvabs, const, rv_le, pointwise_relation in *.
    intro x.
    specialize (H1 x).
    apply Rle_power_l; trivial.
    split; trivial.
    apply Rabs_pos.
  Qed.

  Global Instance Linfty_Lp (n:nonnegreal) (rv_X : Ts -> R) 
    {rv : RandomVariable dom borel_sa rv_X}
    {isl:IsLinfty rv_X}
    : IsLp prts n rv_X.
  Proof.
    intros.
    generalize (rvclip_almost_bounded_exists rv_X rv); intros.
    destruct H as [c H0].
    generalize (rvclip_abs_le_c rv_X c); intros.
    generalize (IsLp_const_bounded n _ c (cond_nonneg _) H); intros.
    eapply IsLp_proper_almost with (rv_X1 := (rvclip rv_X c)); trivial
    ; try typeclasses eauto.
    now symmetry.
  Qed.

  Definition posreal_nnneg (x:posreal) : nonnegreal
    := mknonnegreal x (Rlt_le _ _ (cond_pos x)).
  
  Coercion posreal_nnneg : posreal >-> nonnegreal.
  
  Global Instance Linfty_Lp' (n:posreal) (rv_X : Ts -> R) 
    {rv : RandomVariable dom borel_sa rv_X}
    {isl:IsLinfty rv_X}
    : IsLp prts n rv_X.
  Proof.
    eapply (Linfty_Lp n); eauto.
  Qed.
  
  Lemma Linfty_Lp_le (p:posreal) (rv_X : Ts -> R) 
    {rv : RandomVariable dom borel_sa rv_X} 
    {isl:IsLinfty rv_X} :
    LpRRVnorm (p:=p) prts (pack_LpRRV prts rv_X (lp:=Linfty_Lp p _)) <= Linfty_norm rv_X.
  Proof.      
    generalize (Linfty_norm_nneg rv_X); intros.
    apply power_incr_inv with (n:=p); trivial.
    - apply cond_pos.
    - unfold LpRRVnorm.
      apply power_nonneg.
    - unfold LpRRVnorm.
      rewrite power_inv_cancel.
      + assert (IsFiniteExpectation prts (rvpower (rvabs (rvclip rv_X (mknonnegreal _ H))) (const p))).
        * eapply (IsLp_proper_almost prts p rv_X); try eapply isl
          ; try typeclasses eauto.
          eapply rvclip_almost_bounded
          ; try typeclasses eauto.
          simpl.
          now apply Linfty_norm_contains_finite_lim.
        * erewrite FiniteExpectation_proper_almost with 
            (rv_X2 := (rvpower (rvabs (rvclip rv_X (mknonnegreal _ H))) (const p)))
            (isfe2 := H0)
          ; try typeclasses eauto.
          -- rewrite <- (FiniteExpectation_const prts (power (Linfty_norm rv_X) p)).
             apply FiniteExpectation_le.
             intro x.
             unfold rvpower, rvabs, const.
             apply Rle_power_l.
             ++ destruct p; simpl; lra.
             ++ split.
                ** apply Rabs_pos.
                ** apply rvclip_abs_bounded.
          -- apply rvpower_rv; try typeclasses eauto.
             unfold const.
             apply rvconst.
          -- simpl.
             unfold const.
             apply almost_eq_power_proper
             ; try typeclasses eauto; trivial.
             apply almost_eq_abs_proper
             ; try typeclasses eauto.
             eapply rvclip_almost_bounded; trivial.
             now apply Linfty_norm_contains_finite_lim.
      + apply FiniteExpectation_pos
        ; typeclasses eauto.
      + destruct p; simpl; lra.
  Qed.

  Definition norm_convergence 
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (norm : (Ts -> R) -> nonnegreal) :=
    is_lim_seq (fun n => norm (rvminus X (Xn n))) 0.

  Lemma Linf_Lp_converge (p:posreal)
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (rvdif : forall (n:nat), RandomVariable dom borel_sa (rvminus X (Xn n))) 
        (isl: forall (n:nat), IsLinfty (rvminus X (Xn n))) :
    is_lim_seq (fun n => Linfty_norm (rvminus X (Xn n))) 0 ->
    is_lim_seq (fun n => LpRRVnorm (p:=p) prts (pack_LpRRV prts (rvminus X (Xn n)))) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with 
        (u := fun _ => 0) 
        (w := (fun n =>  Linfty_norm (rvminus X (Xn n)))); trivial.
    - exists (0%nat).
      intros.
      split; trivial.
      + unfold LpRRVnorm.
        apply power_nonneg.
      + erewrite LpRRV_norm_proper.
        * now apply Linfty_Lp_le.
        * apply almost_eq_subr; intros ?.
          reflexivity.
    - apply is_lim_seq_const.
  Qed.

End Linf.


