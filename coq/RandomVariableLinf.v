Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import Reals.
Require Import FunctionalExtensionality.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq Coquelicot.Hierarchy.

Require Export RandomVariableFinite RandomVariableLp.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section Linf.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).


  Definition Linfty_norm (rv_X : Ts -> R) 
             {rv : RandomVariable dom borel_sa rv_X} : Rbar :=
    Glb_Rbar (fun (x : R) =>
                ps_P (fun omega => (rvabs rv_X) omega > x) = 0).

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
    ps_P (fun omega => (rvabs rv_X) omega > r) = 0 -> 0<=r.
  Proof.
    destruct (Rle_dec 0 r); intros; trivial.
    assert (event_equiv (fun omega : Ts => rvabs rv_X omega > r) Ω).
    intro x0.
    unfold rvabs.
    generalize (Rabs_pos (rv_X x0)); intros.
    unfold  Ω.
    lra.
    rewrite H0 in H.
    rewrite ps_all in H.
    lra.
  Qed.  
    
  Lemma is_Linfty_c_nonneg (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {isl:IsLinfty rv_X} :
    exists (c:nonnegreal), ps_P (fun omega => (rvabs rv_X) omega > c) = 0.
  Proof.
    unfold IsLinfty, Linfty_norm in *.
    apply finite_glb in isl.
    destruct isl.
    destruct (Rle_dec 0 x).
    - exists (mknonnegreal _ r).
      now simpl.
    - assert (0 > x) by lra.
      assert (event_equiv (fun omega : Ts => rvabs rv_X omega > x)  Ω ).
      + intro x0.
        unfold rvabs.
        generalize (Rabs_pos (rv_X x0)); intros.
        unfold  Ω.
        lra.
      + rewrite H1 in H.
        generalize (ps_all prts); intros.
        rewrite H in H2.
        lra.
    Qed.                          

  Lemma Linfty_norm_nneg (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X} :
    IsLinfty rv_X -> 
      0 <= Linfty_norm rv_X.
  Proof.
    intros.
    generalize (Glb_Rbar_correct (fun x : R => ps_P (fun omega : Ts => rvabs rv_X omega > x) = 0)); intros.    
    unfold is_glb_Rbar in H0.
    destruct H0.
    destruct (Rle_dec 0 (Linfty_norm rv_X)); trivial.
    assert (0 > Linfty_norm rv_X) by lra.
    unfold Linfty_norm in H2.
    specialize (H1 0).
    unfold IsLinfty, Linfty_norm in H.
    rewrite <- H in H1.
    simpl in H1.
    cut_to H1.
    lra.
    unfold is_lb_Rbar; intros.
    simpl.
    now apply (abs_neg_psall rv_X x).
  Qed.

  Lemma almost_bounded (rv_X : Ts -> R) (c : nonnegreal)
        {rv : RandomVariable dom borel_sa rv_X} :
    ps_P (fun omega => (rvabs rv_X) omega > c) = 0 ->
    rv_almost_eq prts rv_X (rvclip rv_X c).
 Proof.
   intros.
   unfold rv_almost_eq.
   generalize (ps_complement prts (fun omega : Ts => rvabs rv_X omega > c)); intros.
   rewrite H, Rminus_0_r in H0.
   cut_to H0.
   - rewrite <- H0.
     apply ps_proper.
     intros x.
     unfold event_complement.
     unfold rvclip, rvabs.
     generalize (Rle_abs (rv_X x)); intros.       
     simpl.
     match_destr; [lra |].
     generalize (Rcomplements.Rabs_maj2 (rv_X x)); intros.
     match_destr; [lra |].
     split; [|lra].
     intros.
     unfold Rabs.
     match_destr; lra.
   - apply sa_le_gt.
     apply Rabs_measurable.
     unfold RealMeasurable.
     apply borel_sa_preimage2; intros.
     now apply rv_preimage.
   Qed.

  Lemma almost_bounded_exists (rv_X : Ts -> R)
        (rv : RandomVariable dom borel_sa rv_X)
        {isl:IsLinfty rv_X} :
    exists (c:nonnegreal), rv_almost_eq prts rv_X (rvclip rv_X c).
  Proof.
    destruct (is_Linfty_c_nonneg rv_X).
    exists x.
    now apply almost_bounded.
  Qed.

  Lemma zero_prob_bound
        (rv_X : Ts -> R)         
        {rv : RandomVariable dom borel_sa rv_X} : 
    forall (c1 c2 : R),
      c1 <= c2  ->
      ps_P (fun omega : Ts => rvabs rv_X omega > c1) = 0 ->
      ps_P (fun omega : Ts => rvabs rv_X omega > c2) = 0.
  Proof.
    intros.
    unfold RandomVariable in rv.
    assert (forall (r:R), sa_sigma (fun omega : Ts => rvabs rv_X omega > r)).
    apply sa_le_gt.
    intros.
    apply Rabs_measurable.
    unfold RealMeasurable.
    now rewrite borel_sa_preimage2.

    assert (event_sub (fun omega : Ts => rvabs rv_X omega > c2)
                      (fun omega : Ts => rvabs rv_X omega > c1) ) by (intro x0; lra).

    assert (ps_P (fun omega : Ts => rvabs rv_X omega > c2) <=
            ps_P (fun omega : Ts => rvabs rv_X omega > c1)).
    apply ps_sub; trivial.
    generalize (ps_pos (fun omega : Ts => rvabs rv_X omega > c2)); intros.
    specialize (H1 c2).
    specialize (H4 H1).
    lra.
  Qed.

  Lemma zero_prob_bound_Linfty
        (rv_X : Ts -> R)         
        {rv : RandomVariable dom borel_sa rv_X}
        {isl:IsLinfty rv_X} :
    forall (c : R),
      (0 < c  ->
       ps_P (fun omega : Ts => rvabs rv_X omega > Linfty_norm rv_X + c) = 0).
  Proof.
     rename isl into H.
     intros.
     unfold IsLinfty, Linfty_norm in H.
     generalize (Glb_Rbar_correct (fun x : R => ps_P (fun omega : Ts => rvabs rv_X omega > x) = 0)); intros.
     unfold is_glb_Rbar in H1.
     destruct H1.
     rewrite <- H in H1; simpl in H1.
     destruct (classic (exists (y:R), (Linfty_norm rv_X <= y <= Linfty_norm rv_X + c) /\
                                      ps_P (fun omega : Ts => rvabs rv_X omega > y) = 0)).
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
      ps_P (fun omega => (rvabs rv_X) omega > (Linfty_norm rv_X)) = 0.
  Proof.
     generalize (lim_prob (fun n => (fun omega => (rvabs rv_X) omega > (Linfty_norm rv_X) + / INR (S n))) (fun omega => (rvabs rv_X) omega > (Linfty_norm rv_X))); intros.
     cut_to H.
     - assert (forall n, ps_P (fun omega : Ts => rvabs rv_X omega > Linfty_norm rv_X + / INR (S n)) = 0).
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
     - intros.
       apply sa_le_gt.
       intros.
       apply Rabs_measurable.
       unfold RealMeasurable.
       unfold RandomVariable in rv.
       now rewrite borel_sa_preimage2.
     - unfold event_sub; intros.
       apply Rgt_trans with (r2 :=  Linfty_norm rv_X + / INR (S n)); trivial.
       apply Rplus_gt_compat_l.
       apply Rinv_1_lt_contravar.
       replace (1) with (0 + 1) by lra.
       rewrite S_INR.
       apply Rplus_le_compat_r.
       apply pos_INR.
       apply lt_INR; lia.
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
         apply Rinv_lt_contravar.
         apply Rmult_lt_0_compat.
         apply Rinv_0_lt_compat; lra.
         apply lt_0_INR; lia.
         assert (forall (r:R), 0 < r -> r < INR (S (Z.to_nat (up r)))); intros.
         rewrite S_INR.
         rewrite INR_up_pos.
         generalize (archimed r); intros.
         destruct H2; lra.
         lra.
         apply H1.
         apply Rinv_0_lt_compat; lra.
         apply Rgt_not_eq; lra.
   Qed.

  Instance IsLp_const_bounded (n:nat) (rv_X : Ts -> R) (bound : R)
    {rv : RandomVariable dom borel_sa rv_X} :
     rv_le (rvabs rv_X) (const bound) ->
     IsLp prts n rv_X.
  Proof.
    generalize (IsLp_bounded prts n rv_X (const (pow bound n))); intros.
    apply H.
    unfold rvpow, rvabs, const, rv_le, pointwise_relation in *.
    intro x.
    specialize (H0 x).
    apply pow_maj_Rabs.
    now rewrite Rabs_Rabsolu.
    apply IsFiniteExpectation_const.
  Qed.

  Global Instance Linfty_Lp (n:nat) (rv_X : Ts -> R) 
    {rv : RandomVariable dom borel_sa rv_X}
    {isl:IsLinfty rv_X}
    : IsLp prts n rv_X.
  Proof.
    intros.
    generalize (almost_bounded_exists rv_X rv); intros.
    destruct H as [c H0].
    generalize (rvclip_abs_le_c rv_X c); intros.
    generalize (IsLp_const_bounded n _ c H); intros.
    apply IsLp_proper_almost with (rv_X1 := (rvclip rv_X c)); trivial.
    now apply rvclip_rv.
    now symmetry.
  Qed.

  Lemma Linfty_Lp_le (p:nat) (rv_X : Ts -> R) 
    {rv : RandomVariable dom borel_sa rv_X} 
    {isl:IsLinfty rv_X} :
    LpRRVnorm (p:=p) prts (pack_LpRRV prts rv_X) <= Linfty_norm rv_X.
  Proof.
    intros.
    unfold LpRRVnorm.
    apply pow_incr_inv with (n:=p).
    - apply root_nneg.
    - now apply Linfty_norm_nneg.
    - rewrite pow_root_inv.
      + admit.
      + apply FiniteExpectation_pos.
        typeclasses eauto.
    Admitted.

  Definition norm_convergence 
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (norm : (Ts -> R) -> nonnegreal) :=
    is_lim_seq (fun n => norm (rvminus X (Xn n))) 0.

End Linf.


