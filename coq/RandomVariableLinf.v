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

  Definition Linfty_term (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x : event dom
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

  Lemma Linfty_norm_Rbar_nneg (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X} :
    Rbar_le 0 (Linfty_norm rv_X).
  Proof.
    intros.
    unfold Linfty_norm, Glb_Rbar, proj1_sig.
    match_destr.
    destruct i as [lbx glbx].
    apply (glbx 0).
    intros ??.
    apply abs_neg_psall in H.
    apply H.
  Qed.

  Lemma Linfty_norm_nneg (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {isl:IsLinfty rv_X} :
      0 <= Linfty_norm rv_X.
  Proof.
    intros.
    generalize (Linfty_norm_Rbar_nneg rv_X)
    ; intros HH.
    rewrite <- isl in HH.
    apply HH.
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
       {rv : RandomVariable dom borel_sa rv_X}
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

  Lemma almost_abs_le_Linfty_norm (rv_X : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X} 
             {isl: IsLinfty rv_X} :
   almost prts Rle (rvabs rv_X) (const (Linfty_norm rv_X)).
Proof.   
  generalize (Linfty_norm_contains_finite_lim rv_X); intros.
  eexists.
  split.
  - rewrite ps_complement.
    rewrite H; lra.
  - intros.
    simpl in H0.
    red in H0.
    unfold const.
    lra.
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
    generalize (rvclip_almost_bounded_exists rv_X); intros.
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

  Lemma ps_almost_sub (P1 P2 : event dom) :
    almost prts impl P1 P2 -> ps_P P1 <= ps_P P2.
  Proof.
    intros [a [??]].

    rewrite <- (ps_inter_r1 prts H (A:=P1)).
    rewrite <- (ps_inter_r1 prts H (A:=P2)).
    apply ps_sub.
    unfold event_inter, pre_event_inter.
    intros ? [??]; simpl in *.
    split; trivial.
    now apply H0.
  Qed.

  Lemma ps_almost_proper (P1 P2 : event dom) :
    almost prts iff P1 P2 -> ps_P P1 = ps_P P2.
  Proof.
    intros [a [??]].

    rewrite <- (ps_inter_r1 prts H (A:=P1)).
    rewrite <- (ps_inter_r1 prts H (A:=P2)).
    apply ps_proper.
    unfold event_inter, pre_event_inter; intros x; simpl.
    specialize (H0 x).
    tauto.
  Qed.

  Lemma almost_sub_event_prob0 (P1 P2 : event dom) :
    ps_P P2 = 0 ->
    almost prts impl P1 P2 -> ps_P P1 = 0.
  Proof.
    intros.
    generalize (ps_almost_sub P1 P2 H0); intros.
    generalize (ps_pos P1); intros.
    lra.
  Qed.

  (* Move this *)
  (* maybe make this just a generalzie almost_sub ? *)
  Global Instance almost_same_lift {A B} R1 R2 (f : A -> B)
        (p:Proper (R1 ==> R2) f) :
    Proper (almost prts R1 ==> almost prts R2) (fun x t => f (x t)).
  Proof.
    intros P1 P2 [P [Pone PR1]].
    exists P.
    split; trivial.
    intros ??.
    specialize (PR1 _ H).
    now apply p.
  Qed.

  Global Instance almost_sub_lift
      {Td1 Td2:Type} 
      (R1:Td1->Td1->Prop)
      (R2:Td2->Td2->Prop)
      (f:(Ts->Td1)->Ts->Td2)
      (fpres: forall x y a, R1 (x a) (y a) -> R2 (f x a) (f y a))
  : Proper (almost prts R1 ==> almost prts R2) f.
Proof.
  intros x1 x2 [Px [Pxall eq_onx]].
  exists Px.
  split; trivial.
  intros; auto.
Qed.

    
  Lemma Linfty_term_almost_Rle_impl rv_X1 rv_X2
        {rv1:RandomVariable dom borel_sa rv_X1}
        {rv2:RandomVariable dom borel_sa rv_X2} :
    almost prts Rle (rvabs rv_X1) rv_X2 ->
    forall a,
      almost prts impl (Linfty_term rv_X1 a) (Linfty_term rv_X2 a).
  Proof.
    intros le1 a.
    destruct le1 as [p[??]].
    exists p.
    split; trivial.
    unfold Linfty_term.
    intros x px ?.
    unfold Linfty_term; simpl in *.
    specialize (H0 _ px).
    eapply Rge_gt_trans; try eapply H1.
    eapply Rle_ge.
    eapply Rle_trans; try eapply H0.
    unfold rvabs.
    apply Rle_abs.
  Qed.
              
  Lemma Linfty_norm_almost_le rv_X1 rv_X2
        {rv1:RandomVariable dom borel_sa rv_X1}
        {rv2:RandomVariable dom borel_sa rv_X2}
        (rle:almost prts Rle (rvabs rv_X1) rv_X2) :
      Rbar_le (Linfty_norm rv_X1) (Linfty_norm rv_X2).
    Proof.
      generalize (Linfty_norm_Rbar_nneg rv_X1)
      ; intros Hle1.
      generalize (Linfty_norm_Rbar_nneg rv_X2)
      ; intros Hle2.
      unfold Linfty_norm.

      unfold Glb_Rbar, proj1_sig.
      repeat match_destr.
      destruct i as [lb1 glb1].
      destruct i0 as [lb2 glb2].
      unfold is_lb_Rbar in *.
      apply glb2.
      intros a pa.
      apply lb1.
      eapply almost_sub_event_prob0; eauto.
      now apply Linfty_term_almost_Rle_impl.
    Qed.


  Lemma IsLinfty_almost_le rv_X1 rv_X2
        {rv1:RandomVariable dom borel_sa rv_X1}
        {rv2:RandomVariable dom borel_sa rv_X2}
        (rle:almost prts Rle (rvabs rv_X1) rv_X2)
        {isli:IsLinfty rv_X2}
    :
      IsLinfty rv_X1.
  Proof.
    generalize (Linfty_norm_Rbar_nneg rv_X1)
    ; intros HH1.

    assert (HH3:Rbar_le (Linfty_norm rv_X1) (Linfty_norm rv_X2)).
    {
      now apply Linfty_norm_almost_le.
    }
    unfold IsLinfty in *.
    unfold Linfty_norm in *.
    rewrite <- isli in HH3.
    simpl in *.
    unfold Rbar_le in HH3.
    match_destr_in HH1; try tauto.
    reflexivity.
  Qed.

  Lemma Linfty_norm_const c : Linfty_norm (const c) = Rabs c.
  Proof.
    unfold Linfty_norm, Linfty_term.
    rewrite Glb_Rbar_eqset with (E2:=fun x => if Rgt_dec (Rabs c) x then False else True).
    {
      apply is_glb_Rbar_unique.
      red; split; intros ?.
      - match_destr; [tauto |].
        intros.
        unfold Rbar_le.
        apply Rge_le.
        now apply Rnot_gt_ge in n.
      - intros HH.
        red in HH.
        specialize (HH (Rabs c)).
        match_destr_in HH.
        + lra.
        + auto.
    }    
    {
      intros x; destruct (Rgt_dec (Rabs c) x).
      - erewrite ps_proper.
        + rewrite ps_all.
          intuition.
        + intros ?; simpl.
          unfold pre_Ω; rv_unfold.
          tauto.
      - erewrite ps_proper.
        + rewrite ps_none.
          intuition.
        + intros ?; simpl.
          unfold pre_event_none; rv_unfold.
          tauto.
    }
  Qed.
  
  Global Instance IsLinfty_const c : IsLinfty (const c).
  Proof.
    red.
    now rewrite Linfty_norm_const.
  Qed.

  Lemma Linfty_term_almost_eq  rv_X1 rv_X2
        {rv1:RandomVariable dom borel_sa rv_X1}
        {rv2:RandomVariable dom borel_sa rv_X2}
        (req:almost prts eq rv_X1 rv_X2) :
    forall x,
      almost prts iff (Linfty_term rv_X2 x) (Linfty_term rv_X1 x).
  Proof.
    intros x.
    destruct req as [p [pa HH]].
    exists p.
    split; trivial; intros.
    unfold Linfty_term, rvabs; simpl.
    rewrite (HH _ H).
    tauto.
  Qed.


    Lemma Linfty_norm_almost_eq rv_X1 rv_X2
        {rv1:RandomVariable dom borel_sa rv_X1}
        {rv2:RandomVariable dom borel_sa rv_X2}
        (req:almost prts eq rv_X1 rv_X2) :
      Linfty_norm rv_X1 = Linfty_norm rv_X2.
    Proof.
      unfold Linfty_norm.
      apply Glb_Rbar_eqset; intros.
      erewrite ps_almost_proper; [reflexivity |].
      apply Linfty_term_almost_eq.
      now symmetry.
    Qed.

    Lemma IsLinfty_almost_eq rv_X1 rv_X2
        {rv1:RandomVariable dom borel_sa rv_X1}
        {rv2:RandomVariable dom borel_sa rv_X2}
        (req:almost prts eq rv_X1 rv_X2) :
      IsLinfty rv_X1 <-> IsLinfty rv_X2.
    Proof.
      unfold IsLinfty.
      erewrite Linfty_norm_almost_eq; eauto.
      reflexivity.
    Qed.

  Lemma Linfty_norm_scale c x (y:R) 
    {rv_x:RandomVariable dom borel_sa x} :
    Linfty_norm x = y ->
    Linfty_norm (rvscale c x) = Rabs c * y.
  Proof.
    destruct (Req_EM_T c 0).
    {
      subst.
      intros.
      erewrite (Linfty_norm_almost_eq _ (const 0)).
      - rewrite Linfty_norm_const.
        repeat rewrite Rabs_R0.
        simpl.
        f_equal.
        lra.
      - apply almost_eq_subr; intros ?.
        rv_unfold.
        f_equal.
        lra.
    }
    assert (cgt:Rabs c > 0).
    {
      generalize (Rabs_pos c); intros.
      assert (Rabs c <> 0) by now apply Rabs_no_R0.
      lra.
    } 
    assert (cigt:/ Rabs c > 0).
    {
      now apply Rinv_0_lt_compat.
    } 
    unfold Linfty_norm, Linfty_term; intros.
    match type of H with
    | Glb_Rbar ?x = _ =>    generalize (Glb_Rbar_correct x)
                           ; rewrite H
                           ; clear H; intros H
    end.
    destruct H as [HH1 HH2].
    apply is_glb_Rbar_unique.
    red; split.
    - intros ??.
      unfold rvscale, rvabs in H; simpl in H.
      cut (Rbar_le y (x0 / Rabs c)).
      {
        unfold Rbar_le.
        intros.
        rewrite Rmult_comm.
        rewrite Rcomplements.Rle_div_r; trivial.
      }
      red in HH1.
      apply (HH1  (x0 / Rabs c)).
      rewrite <- H.
      apply ps_proper.
      intros a; simpl.
      unfold rvabs.
      split; intros eqq1.
      + apply (Rmult_gt_compat_r (Rabs c)) in eqq1; trivial.
        field_simplify in eqq1; try lra.
        rewrite Rabs_mult.
        lra.
      + rewrite Rabs_mult in eqq1.
        apply (Rmult_lt_reg_r (Rabs c)); trivial.
        field_simplify; try lra.
    - intros ??.
      unfold rvscale, rvabs in *; simpl in *.

      unfold is_lb_Rbar in *.
      specialize (HH2 (Rbar_div b (Rabs c))).
      cut_to HH2.
      + destruct b; simpl in *; trivial.
        * rewrite Rcomplements.Rle_div_r in HH2; trivial.
          rewrite Rmult_comm.
          field_simplify in HH2; trivial.
          lra.
        * destruct (Rle_dec 0 (/ Rabs c)); try lra.
          destruct ( Rle_lt_or_eq_dec 0 (/ Rabs c) r); try lra.
          apply HH2.
      + intros.
        specialize (H (Rabs c * x0)).
        cut_to H.
        * destruct b; simpl in *; trivial.
          -- rewrite Rcomplements.Rle_div_r; trivial.
             field_simplify; lra.
          --  tauto.
          -- destruct (Rle_dec 0 (/ Rabs c)); try lra.
             destruct ( Rle_lt_or_eq_dec 0 (/ Rabs c) r); try lra.
             now red.
        * erewrite ps_proper; try eapply H0.
          intros ?; simpl.
          {
            split; intros eqq1.
            + rewrite Rabs_mult in eqq1.
              apply (Rmult_lt_reg_l (Rabs c)) in eqq1; trivial.
            + rewrite Rabs_mult.
              apply (Rmult_lt_compat_l (Rabs c)); trivial.
          }
  Qed.

  Global Instance IsLinfty_scale c x
         {rv_x:RandomVariable dom borel_sa x}
         {li_x:IsLinfty x}
    : IsLinfty (rvscale c x).
  Proof.
    red.
    red in li_x.
    unfold is_finite in *.
    erewrite (Linfty_norm_scale c x (real (@Linfty_norm x rv_x))); eauto.
  Qed.

  Lemma Linfty_norm_abs x  
    {rv_x:RandomVariable dom borel_sa x} :
    Linfty_norm (rvabs x) = Linfty_norm x.
  Proof.
    unfold Linfty_norm, Linfty_term.
    apply Glb_Rbar_eqset.
    intros.
    erewrite ps_proper; [reflexivity |].
    intros ?; simpl.
    unfold rvabs.
    rewrite Rabs_Rabsolu.
    reflexivity.
  Qed.

  Global Instance IsLinfty_abs x
         {rv_x:RandomVariable dom borel_sa x}
         {li_x:IsLinfty x}
    : IsLinfty (rvabs x).
  Proof.
    red.
    now rewrite Linfty_norm_abs.
  Qed.

  Lemma IsLinfty_abs_inv x
         {rv_x:RandomVariable dom borel_sa x}
         {li_x:IsLinfty (rvabs x)}
    : IsLinfty x.
  Proof.
    red.
    now rewrite <- Linfty_norm_abs.
  Qed.

  Existing Instance rvclip_rv.

  Lemma Linfty_term_rvclip x c
        {rv_x:RandomVariable dom borel_sa x} :
    event_equiv (Linfty_term (rvclip x c) c) event_none.
  Proof.
    unfold rvclip, event_none, pre_event_none.
    intros ?; simpl.
    unfold rvabs.
    split; intros HH; [| tauto].
    destruct c; simpl in *.
    match_destr_in HH.
    - rewrite Rabs_pos_eq in HH; lra.
    - match_destr_in HH.
      + rewrite Rabs_Ropp in HH.
        rewrite Rabs_pos_eq in HH; try lra.
      + unfold Rabs in HH.
        match_destr_in HH; lra.
  Qed.
              
  Instance IsLinfty_rvclip x c 
         {rv_x:RandomVariable dom borel_sa x} :
    IsLinfty (rvclip x c).
  Proof.
    red.
    generalize (Linfty_norm_Rbar_nneg (rvclip x c)).
            
    unfold Linfty_norm, Glb_Rbar, proj1_sig.
    match_destr.
    intros x0pos.
    destruct i.
    specialize (H c).
    cut_to H.
    - destruct x0; simpl in *
      ; try tauto.
      reflexivity.
    - rewrite Linfty_term_rvclip.
      apply ps_none.
  Qed.

  Global Instance IsLinfty_plus x y
        {rv_x:RandomVariable dom borel_sa x} 
        {rv_y:RandomVariable dom borel_sa y} 
        {isli_x:IsLinfty x}
        {isli_y:IsLinfty y} :
    IsLinfty (rvplus x y).
    Proof.
      destruct (rvclip_almost_bounded_exists x) as [xc xeqq].
      destruct (rvclip_almost_bounded_exists y) as [yc yeqq].
      assert (almost prts eq (rvplus x y) (rvplus (rvclip x xc) (rvclip y yc)))
        by now apply almost_eq_plus_proper.
      apply (IsLinfty_almost_eq _ _ H).

      assert (pf:0 <= xc + yc)
        by (destruct xc; destruct yc; simpl; lra).

      assert (pfle2:almost prts Rle (rvabs (rvplus (rvclip x xc) (rvclip y yc))) (rvabs (rvclip (rvabs (rvplus (rvclip x xc) (rvclip y yc))) (mknonnegreal _ pf)))).
      {
        apply almost_le_subr.
        intros a.
        rv_unfold.
        unfold rvclip at 3; simpl.

        assert (le1:Rabs (rvclip x xc a + rvclip y yc a) <= Rabs (xc + yc)).
        {

          eapply Rle_trans; try apply Rabs_triang.
          rewrite (Rabs_pos_eq (xc + yc)); trivial.
          generalize (rvclip_abs_bounded x xc a)
          ; intros HH1.
          generalize (rvclip_abs_bounded y yc a)
          ; intros HH2.
          lra.
        } 


        match_destr.
        match_destr.
        - rewrite Rabs_Ropp; trivial.
        - rewrite Rabs_Rabsolu.
          apply Rle_refl.
      } 
      apply (@IsLinfty_almost_le _ _  _ _ pfle2).
      apply IsLinfty_abs.
      apply IsLinfty_rvclip.
    Qed.

    Global Instance IsLinfty_minus x y
        {rv_x:RandomVariable dom borel_sa x} 
        {rv_y:RandomVariable dom borel_sa y} 
        {isli_x:IsLinfty x}
        {isli_y:IsLinfty y} :
      IsLinfty (rvminus x y).
    Proof.
      typeclasses eauto.
    Qed.

    Lemma rvabs_triang (f g:Ts->R) :
      rv_le (rvabs (rvplus f g)) (rvplus (rvabs f) (rvabs g)).
    Proof.
      rv_unfold; intros ?.
      apply Rabs_triang.
    Qed.
    
    Lemma Linfty_norm_minkowski  (x y : (Ts -> R))
          {rv_x: RandomVariable dom borel_sa x}
          {rv_y: RandomVariable dom borel_sa y}
          {isli_x: IsLinfty x}
          {isli_y: IsLinfty y} :
      Linfty_norm (rvplus x y) <= Linfty_norm x + Linfty_norm y.
    Proof.


      generalize (almost_abs_le_Linfty_norm x); intros alex.
      generalize (almost_abs_le_Linfty_norm y); intros aley.
      generalize (almost_abs_le_Linfty_norm (rvplus x y)); intros alexy.
      generalize (rvabs_triang x y); intros tri.

      assert (le1:almost prts Rle (rvabs (rvplus x y)) (rvplus (const (Linfty_norm x)) (const (Linfty_norm y)))).
      {
        apply (almost_le_subr prts) in tri.
        rewrite tri.
        rewrite alex.
        rewrite aley.
        reflexivity.
      }

      assert (le2:
        almost prts Rle (rvabs (rvplus x y))
               (const (Linfty_norm x + Linfty_norm y))).
      {
        rewrite le1.
        reflexivity.
      }
      generalize (Linfty_norm_almost_le _ _ le2)
      ; intros le3.
      rewrite Linfty_norm_const in le3.

      assert (isli_xy:IsLinfty (rvplus x y)) by typeclasses eauto.
      rewrite <- isli_xy in le3.
      simpl in le3.
      rewrite Rabs_pos_eq in le3; trivial.
      apply Rplus_le_le_0_compat
      ; now apply Linfty_norm_nneg.
    Qed.

    Lemma almost_eq_rvabs0 x :
      almost prts eq (rvabs x) (const 0) <->
      almost prts eq x (const 0).
    Proof.
      split; intros [p[pone peq]]
      ; exists p; split; trivial
      ; intros a pa
      ; specialize (peq a pa)
      ; rv_unfold.
      - now apply Rcomplements.Rabs_eq_0.
      - rewrite peq.
        apply Rabs_R0.
    Qed.
    
    Lemma Linfty_norm0 x 
          {rv_x:RandomVariable dom borel_sa x} :
      Linfty_norm x = 0 ->
      almost prts eq x (const 0).
    Proof.
      intros HH.
      assert (isli_x:IsLinfty x).
      {
        red; rewrite HH; reflexivity.
      }
      generalize (almost_abs_le_Linfty_norm x)
      ; intros le1.
      assert (le2:almost prts Rle  (fun x0 : Ts => const (Linfty_norm x) x0) (rvabs x)).
      {
        rewrite HH.
        apply almost_le_subr.
        intros ?.
        rv_unfold.
        apply Rabs_pos.
      }
      assert (eqq1:almost prts eq (rvabs x) (fun x0 : Ts => const (Linfty_norm x) x0)).
      {
        now apply antisymmetry.
      }
      rewrite HH in eqq1.
      now apply almost_eq_rvabs0.
    Qed.

  Section packed.

    Record LiRRV : Type
      := LiRRV_of {
             LiRRV_rv_X :> Ts -> R
             ; LiRRV_rv :> RandomVariable dom borel_sa LiRRV_rv_X
             ; LiRRV_li :> IsLinfty LiRRV_rv_X
           }.


    Global Existing Instance LiRRV_rv.
    Global Existing Instance LiRRV_li.

    Definition pack_LiRRV (rv_X:Ts -> R) {rv:RandomVariable dom borel_sa rv_X} {li:IsLinfty rv_X}
      := LiRRV_of rv_X rv li.

    (* We can view a LiRRV rv as a LpRRV for any 0<=p<infty *)
    Definition LiRRV_LpRRV (n:nonnegreal) (rv:LiRRV)
      : LpRRV prts n
      := pack_LpRRV prts (LiRRV_rv_X rv).

    Definition LiRRV_seq (rv1 rv2:LiRRV) (* strict equality *)
      := rv_eq (LiRRV_rv_X rv1) (LiRRV_rv_X rv2).

    Definition LiRRV_eq (rv1 rv2:LiRRV)
      := almost prts eq rv1 rv2.

    Global Instance LiRRV_seq_eq : subrelation LiRRV_seq LiRRV_eq.
    Proof.
      red; unfold LiRRV_seq, LiRRV_eq, rv_eq.
      intros x y eqq.
      now apply almost_eq_subr.
    Qed.      
    
    Global Instance LiRRV_seq_equiv : Equivalence (LiRRV_seq).
    Proof.
      unfold LiRRV_seq.
      apply Equivalence_pullback.
      apply rv_eq_equiv.
    Qed.

    Global Instance LiRRV_eq_equiv : Equivalence LiRRV_eq.
    Proof.
      unfold LiRRV_eq.
      constructor.
      - intros [x?].
        reflexivity.
      - intros [x?] [y?] ps1; simpl in *.
        now symmetry.
      - intros [x??] [y??] [z??] ps1 ps2.
        simpl in *.
        etransitivity; eauto.
    Qed.

    Definition LiRRVconst (x:R) : LiRRV
      := pack_LiRRV (const x).

    Definition LiRRVzero : LiRRV := LiRRVconst 0.

    Program Definition LiRRVscale (x:R) (rv:LiRRV) : LiRRV
      := pack_LiRRV (rvscale x rv).

    Global Instance LiRRV_scale_sproper : Proper (eq ==> LiRRV_seq ==> LiRRV_seq) LiRRVscale.
    Proof.
      unfold Proper, respectful, LiRRV_eq.
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

    Global Instance LiRRV_scale_proper : Proper (eq ==> LiRRV_eq ==> LiRRV_eq) LiRRVscale.
    Proof.
      unfold Proper, respectful, LiRRV_eq.
      intros ? x ? [x1??] [x2??] eqqx.
      subst.
      simpl in *.
      rewrite eqqx.
      reflexivity.
    Qed.

    Definition LiRRVopp (rv:LiRRV) : LiRRV
      := pack_LiRRV (rvopp rv).
    
    Global Instance LiRRV_opp_sproper : Proper (LiRRV_seq ==> LiRRV_seq) LiRRVopp.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      generalize (LiRRV_scale_sproper (-1) _ (eq_refl _) _ _ eqq)
      ; intros HH.
      destruct x as [x?]
      ; destruct y as [y?].
      apply HH.
    Qed.

    Global Instance LiRRV_opp_proper : Proper (LiRRV_eq ==> LiRRV_eq) LiRRVopp.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      generalize (LiRRV_scale_proper (-1) _ (eq_refl _) _ _ eqq)
      ; intros HH.
      destruct x as [x?]
      ; destruct y as [y?].
      apply HH.
    Qed.

    Lemma LiRRVopp_scale (rv:LiRRV) :
      LiRRV_eq 
        (LiRRVopp rv) (LiRRVscale (-1) rv).
    Proof.
      red.
      reflexivity.
    Qed.

    Definition LiRRVabs (rv:LiRRV) : LiRRV
      := pack_LiRRV (rvabs rv).

    Global Instance LiRRV_abs_sproper : Proper (LiRRV_seq ==> LiRRV_seq) LiRRVabs.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      red in eqq.
      red; simpl.
      now rewrite eqq.
    Qed.

    Global Instance LiRRV_abs_proper : Proper (LiRRV_eq ==> LiRRV_eq) LiRRVabs.
    Proof.
      unfold Proper, respectful.
      intros x y eqq.
      now apply almost_eq_abs_proper.
    Qed.

    Program Definition LiRRVplus (x y:LiRRV) : LiRRV
      := pack_LiRRV (rvplus x y).

    Global Instance LiRRV_plus_sproper : Proper (LiRRV_seq ==> LiRRV_seq ==> LiRRV_seq) LiRRVplus.
    Proof.
      unfold Proper, respectful.
      intros x y eqq1 a b eqq2.
      red in eqq1, eqq2.
      red; simpl.
      now rewrite eqq1, eqq2.
    Qed.

    Global Instance LiRRV_plus_proper : Proper (LiRRV_eq ==> LiRRV_eq ==> LiRRV_eq) LiRRVplus.
    Proof.
      unfold Proper, respectful.
      intros x y eqq1 a b eqq2.
      now apply almost_eq_plus_proper.
    Qed.

    Definition LiRRVminus (rv1 rv2:LiRRV) : LiRRV
      := pack_LiRRV (rvminus rv1 rv2).

    Lemma LiRRVminus_plus (rv1 rv2:LiRRV) :
      LiRRV_seq 
        (LiRRVminus rv1 rv2) (LiRRVplus rv1 (LiRRVopp rv2)).
    Proof.
      intros ?.
      reflexivity.
    Qed.
    
    Global Instance LiRRV_minus_sproper : Proper (LiRRV_seq ==> LiRRV_seq ==> LiRRV_seq) LiRRVminus.
    Proof.
      unfold Proper, respectful, LiRRV_seq.

      intros x1 x2 eqq1 y1 y2 eqq2; simpl.
      now rewrite eqq1, eqq2.
    Qed.

    Global Instance LiRRV_minus_proper : Proper (LiRRV_eq ==> LiRRV_eq ==> LiRRV_eq) LiRRVminus.
    Proof.
      unfold Proper, respectful, LiRRV_eq.

      intros x1 x2 eqq1 y1 y2 eqq2.
      
      generalize (LiRRV_plus_proper _ _ eqq1 _ _ (LiRRV_opp_proper _ _ eqq2)) 
      ; intros HH.
      destruct x1 as [???]; destruct x2 as [???]
      ; destruct y1 as [???]; destruct y2 as [???].
      apply HH.
    Qed.

    Ltac LiRRV_simpl
      := repeat match goal with
                | [H : LiRRV |- _ ] => destruct H as [???]
                end
         ; unfold LiRRVplus, LiRRVminus, LiRRVopp, LiRRVscale, LiRRVabs
         ; simpl.

    Lemma LiRRV_plus_comm x y : LiRRV_eq (LiRRVplus x y) (LiRRVplus y x).
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus; lra.
    Qed.
    
    Lemma LiRRV_plus_assoc (x y z : LiRRV) : LiRRV_eq (LiRRVplus x (LiRRVplus y z)) (LiRRVplus (LiRRVplus x y) z).
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus.
      lra.
    Qed.

    Lemma LiRRV_plus_zero (x : LiRRV) : LiRRV_eq (LiRRVplus x (LiRRVconst 0)) x.
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus, const.
      lra.
    Qed.

    Lemma LiRRV_plus_inv (x: LiRRV) : LiRRV_eq (LiRRVplus x (LiRRVopp x)) (LiRRVconst 0).
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const.
      lra.
    Qed.

    Lemma LiRRV_scale_scale (x y : R) (u : LiRRV) :
      LiRRV_eq (LiRRVscale x (LiRRVscale y u)) (LiRRVscale (x * y) u).
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    Lemma LiRRV_scale1 (u : LiRRV) :
      LiRRV_eq (LiRRVscale one u) u.
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult, one; simpl.
      lra.
    Qed.
    
    Lemma LiRRV_scale_plus_l (x : R) (u v : LiRRV) :
      LiRRV_eq (LiRRVscale x (LiRRVplus u v)) (LiRRVplus (LiRRVscale x u) (LiRRVscale x v)).
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.
    
    Lemma LiRRV_scale_plus_r (x y : R) (u : LiRRV) :
      LiRRV_eq (LiRRVscale (x + y) u) (LiRRVplus (LiRRVscale x u) (LiRRVscale y u)).
    Proof.
      red; intros.
      LiRRV_simpl.
      apply almost_eq_subr; intros ?.
      unfold rvplus, rvopp, rvscale, const, mult; simpl.
      lra.
    Qed.

    Definition LiRRVnorm (rv_X:LiRRV) : R
      := real (Linfty_norm rv_X).

    Global Instance LiRRV_norm_proper : Proper (LiRRV_eq ==> eq) LiRRVnorm.
    Proof.
      unfold Proper, respectful, LiRRVnorm, LiRRV_eq.
      intros.
      f_equal.
      now apply Linfty_norm_almost_eq.
    Qed.

    Global Instance LiRRV_norm_sproper : Proper (LiRRV_seq ==> eq) LiRRVnorm.
    Proof.
      unfold Proper, respectful; intros.
      now rewrite H.
    Qed.
    
    Definition LiRRVnorm_factor : R := 1.

    Lemma LiRRV_norm_plus (x y:LiRRV) : LiRRVnorm (LiRRVplus x y) <= LiRRVnorm x + LiRRVnorm y.
    Proof.
      unfold Proper, respectful, LiRRVnorm, LiRRVplus.
      simpl.
      destruct x; destruct y; simpl.
      now apply Linfty_norm_minkowski.
    Qed.

    Lemma LiRRV_norm_scal_strong (x:R) (y:LiRRV) : LiRRVnorm (LiRRVscale x y) = Rabs x * LiRRVnorm y.
    Proof.
      unfold LiRRVnorm.
      LiRRV_simpl; simpl.
      erewrite Linfty_norm_scale; simpl.
      - reflexivity.
      - rewrite LiRRV_li0; reflexivity.
    Qed.      

    Lemma LiRRV_norm_scal (x:R) (y:LiRRV) : LiRRVnorm (LiRRVscale x y) <= Rabs x * LiRRVnorm y.
    Proof.
      right.
      apply LiRRV_norm_scal_strong.
    Qed.

    Lemma LiRRV_norm0 (x:LiRRV) :
        LiRRVnorm x = 0 ->
        almost prts eq x LiRRVzero.
    Proof.
      unfold LiRRVnorm, LiRRVzero, LiRRVconst; intros; simpl.
      eapply Linfty_norm0.
      rewrite <- H.
      rewrite LiRRV_li.
      reflexivity.
    Qed.

    Definition LiRRVpoint : LiRRV := LiRRVconst 0.

    Definition LiRRVball (x:LiRRV) (e:R) (y:LiRRV): Prop
        := LiRRVnorm (LiRRVminus x y) < e.

    Ltac LiRRV_simpl
      ::= repeat match goal with
                 | [H : LiRRV |- _ ] => destruct H as [???]
                 end;
          unfold LiRRVball, LiRRVnorm, LiRRVplus, LiRRVminus, LiRRVopp, LiRRVscale, LiRRVnorm in *
          ; simpl pack_LiRRV; simpl LiRRV_rv_X in *.

      Global Instance LiRRV_ball_sproper : Proper (LiRRV_seq ==> eq ==> LiRRV_seq ==> iff) LiRRVball.
      Proof.
        intros ?? eqq1 ?? eqq2 ?? eqq3.
        unfold LiRRVball in *.
        rewrite <- eqq1, <- eqq2, <- eqq3.
        reflexivity.
      Qed.

      Global Instance LiRRV_ball_proper : Proper (LiRRV_eq ==> eq ==> LiRRV_eq ==> iff) LiRRVball.
      Proof.
        intros ?? eqq1 ?? eqq2 ?? eqq3.
        unfold LiRRVball in *.
        rewrite <- eqq1, <- eqq2, <- eqq3.
        reflexivity.
      Qed.

      Lemma LiRRV_ball_refl x (e : posreal) : LiRRVball x e x.
      Proof.
        LiRRV_simpl.
        rewrite (Linfty_norm_almost_eq _ (const 0)).
        - rewrite Linfty_norm_const.
          rewrite Rabs_R0.
          apply cond_pos.
        - apply almost_eq_subr.
          apply rvminus_self.
      Qed.
      
      Lemma LiRRV_ball_sym x y e : LiRRVball x e y -> LiRRVball y e x.
      Proof.
        LiRRV_simpl.
        intros.
        rewrite <- Linfty_norm_abs in H.
        rewrite <- Linfty_norm_abs.
        erewrite (Linfty_norm_almost_eq _ (rvabs (rvminus LiRRV_rv_X1 LiRRV_rv_X0))); trivial.
        apply almost_eq_subr.
        apply rvabs_rvminus_sym.
      Qed.

      Lemma LiRRV_ball_trans x y z e1 e2 : LiRRVball x e1 y -> LiRRVball y e2 z -> LiRRVball x (e1+e2) z.
      Proof.
        generalize (LiRRV_norm_plus
                      (LiRRVminus x y)
                      (LiRRVminus y z)).
        LiRRV_simpl.
        intros.

        erewrite (Linfty_norm_almost_eq _ (rvplus (rvminus LiRRV_rv_X2 LiRRV_rv_X1) (rvminus LiRRV_rv_X1 LiRRV_rv_X0))).
        - eapply Rle_lt_trans; try eapply H.
          lra.
        - apply almost_eq_subr.
          rv_unfold; intros ?; lra.
      Qed.

      Lemma LiRRV_close_close (x y : LiRRV) (eps : R) :
        LiRRVnorm (LiRRVminus y x) < eps ->
        LiRRVball x eps y.
      Proof.
        intros.
        apply LiRRV_ball_sym.
        apply H.
      Qed.

      Lemma LiRRV_norm_ball_compat (x y : LiRRV) (eps : posreal) :
        LiRRVball x eps y -> LiRRVnorm (LiRRVminus y x) < LiRRVnorm_factor * eps.
      Proof.
        intros HH.
        apply LiRRV_ball_sym in HH.
        unfold LiRRVnorm_factor.
        field_simplify.
        apply HH.
      Qed.
      
    Section quoted.

      Definition LiRRVq : Type := quot LiRRV_eq.

      Definition LiRRVq_const (x:R) : LiRRVq := Quot _ (LiRRVconst x).

      Lemma LiRRVq_constE x : LiRRVq_const x = Quot _ (LiRRVconst x).
      Proof.
        reflexivity.
      Qed.

      Hint Rewrite LiRRVq_constE : quot.

      Definition LiRRVq_zero : LiRRVq := LiRRVq_const 0.

      Lemma LiRRVq_zeroE : LiRRVq_zero = LiRRVq_const 0.
      Proof.
        reflexivity.
      Qed.

      Hint Rewrite LiRRVq_zeroE : quot.

      Definition LiRRVq_scale (x:R) : LiRRVq -> LiRRVq
        := quot_lift _ (LiRRVscale x).

      Lemma LiRRVq_scaleE x y : LiRRVq_scale x (Quot _ y)  = Quot _ (LiRRVscale x y).
      Proof.
        apply quot_liftE.
      Qed.

      Hint Rewrite LiRRVq_scaleE : quot.
      
      Definition LiRRVq_opp  : LiRRVq -> LiRRVq
        := quot_lift _ LiRRVopp.

      Lemma LiRRVq_oppE x : LiRRVq_opp (Quot _ x)  = Quot _ (LiRRVopp x).
      Proof.
        apply quot_liftE.
      Qed.

      Hint Rewrite LiRRVq_oppE : quot.
      
      Definition LiRRVq_abs  : LiRRVq -> LiRRVq
        := quot_lift _ LiRRVabs.

      Lemma LiRRVq_absE x : LiRRVq_abs (Quot _ x)  = Quot _ (LiRRVabs x).
      Proof.
        apply quot_liftE.
      Qed.

      Hint Rewrite LiRRVq_absE : quot.

      Definition LiRRVq_plus  : LiRRVq -> LiRRVq -> LiRRVq
        := quot_lift2 _ LiRRVplus.
      
      Lemma LiRRVq_plusE x y : LiRRVq_plus (Quot _ x) (Quot _ y) = Quot _ (LiRRVplus x y).
      Proof.
        apply quot_lift2E.
      Qed.

      Hint Rewrite LiRRVq_plusE : quot.

      Definition LiRRVq_minus  : LiRRVq -> LiRRVq -> LiRRVq
        := quot_lift2 _ LiRRVminus.
      
      Lemma LiRRVq_minusE x y : LiRRVq_minus (Quot _ x) (Quot _ y) = Quot _ (LiRRVminus x y).
      Proof.
        apply quot_lift2E.
      Qed.

      Hint Rewrite LiRRVq_minusE : quot.

      Ltac LiRRVq_simpl
        := repeat match goal with
                  | [H: LiRRVq |- _ ] =>
                    let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
                  end
           ; try autorewrite with quot
           ; try apply (@eq_Quot _ _ LiRRV_eq_equiv).

      Lemma LiRRVq_minus_plus (rv1 rv2:LiRRVq) :
        LiRRVq_minus rv1 rv2 = LiRRVq_plus rv1 (LiRRVq_opp rv2).
      Proof.
        LiRRVq_simpl.
        now rewrite LiRRVminus_plus.
      Qed.

      Lemma LiRRVq_opp_scale (rv:LiRRVq) :
        LiRRVq_opp rv = LiRRVq_scale (-1) rv.
      Proof.
        LiRRVq_simpl.
        apply LiRRVopp_scale.
      Qed.
      
      Lemma LiRRVq_plus_comm x y : LiRRVq_plus x y = LiRRVq_plus y x.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_plus_comm.
      Qed.
      
      Lemma LiRRVq_plus_assoc (x y z : LiRRVq) : LiRRVq_plus x (LiRRVq_plus y z) = LiRRVq_plus (LiRRVq_plus x y) z.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_plus_assoc.
      Qed.


      Lemma LiRRVq_plus_zero (x : LiRRVq) : LiRRVq_plus x LiRRVq_zero = x.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_plus_zero.
      Qed.

      Lemma LiRRVq_plus_inv (x: LiRRVq) : LiRRVq_plus x (LiRRVq_opp x) = LiRRVq_zero.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_plus_inv.
      Qed.
      
      Definition LiRRVq_AbelianGroup_mixin : AbelianGroup.mixin_of LiRRVq
        := AbelianGroup.Mixin LiRRVq LiRRVq_plus LiRRVq_opp LiRRVq_zero
                              LiRRVq_plus_comm LiRRVq_plus_assoc
                              LiRRVq_plus_zero LiRRVq_plus_inv.

      Canonical LiRRVq_AbelianGroup :=
        AbelianGroup.Pack LiRRVq LiRRVq_AbelianGroup_mixin LiRRVq.

      Ltac LiRRVq_simpl ::=
        repeat match goal with
               | [H: LiRRVq |- _ ] =>
                 let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
               | [H: AbelianGroup.sort LiRRVq_AbelianGroup |- _ ] =>
                 let xx := fresh H in destruct (Quot_inv H) as [xx ?]; subst H; rename xx into H
               end
        ; try autorewrite with quot
        ; try apply (@eq_Quot _ _ LiRRV_eq_equiv).
      
      Lemma LiRRVq_scale_scale (x y : R_Ring) (u : LiRRVq_AbelianGroup) :
        LiRRVq_scale x (LiRRVq_scale y u) = LiRRVq_scale (x * y) u.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_scale_scale.
      Qed.
      
      Lemma LiRRVq_scale1 (u : LiRRVq_AbelianGroup) :
        LiRRVq_scale one u = u.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_scale1.
      Qed.
      
      Lemma LiRRVq_scale_plus_l (x : R_Ring) (u v : LiRRVq_AbelianGroup) :
        LiRRVq_scale x (plus u v) = plus (LiRRVq_scale x u) (LiRRVq_scale x v).
      Proof.
        LiRRVq_simpl.
        apply LiRRV_scale_plus_l.
      Qed.

      Lemma LiRRVq_scale_plus_r (x y : R_Ring) (u : LiRRVq_AbelianGroup) :
        LiRRVq_scale (plus x y) u = plus (LiRRVq_scale x u) (LiRRVq_scale y u).
      Proof.
        LiRRVq_simpl.
        apply LiRRV_scale_plus_r.
      Qed.

      Definition LiRRVq_ModuleSpace_mixin : ModuleSpace.mixin_of R_Ring LiRRVq_AbelianGroup
        := ModuleSpace.Mixin R_Ring LiRRVq_AbelianGroup
                             LiRRVq_scale LiRRVq_scale_scale LiRRVq_scale1
                             LiRRVq_scale_plus_l LiRRVq_scale_plus_r.

      Canonical LiRRVq_ModuleSpace :=
        ModuleSpace.Pack R_Ring LiRRVq (ModuleSpace.Class R_Ring LiRRVq LiRRVq_AbelianGroup_mixin LiRRVq_ModuleSpace_mixin) LiRRVq.

      Definition LiRRVq_norm : LiRRVq -> R
        := quot_rec LiRRV_norm_proper.

      Lemma LiRRVq_normE x : LiRRVq_norm (Quot _ x)  = LiRRVnorm x.
      Proof.
        apply quot_recE.
      Qed.

      Hint Rewrite LiRRVq_normE : quot.

      Lemma LiRRVq_norm_plus (x y:LiRRVq) : LiRRVq_norm (LiRRVq_plus x y) <= LiRRVq_norm x + LiRRVq_norm y.
      Proof.
        LiRRVq_simpl.
        now apply LiRRV_norm_plus.
      Qed.

      Lemma LiRRVq_norm_scal_strong (x:R) (y:LiRRVq) : LiRRVq_norm (LiRRVq_scale x y) = Rabs x * LiRRVq_norm y.
      Proof.
        LiRRVq_simpl.
        now apply LiRRV_norm_scal_strong.
      Qed.

      Lemma LiRRVq_norm_scal x (y:LiRRVq) : LiRRVq_norm (LiRRVq_scale x y) <= Rabs x * LiRRVq_norm y.
      Proof.
        LiRRVq_simpl.
        now apply LiRRV_norm_scal.
      Qed.

      Lemma LiRRVq_norm0 x : LiRRVq_norm x = 0 -> x = LiRRVq_zero.
      Proof.
        intros.
        LiRRVq_simpl.
        autorewrite with quot in *.
        now apply LiRRV_norm0.
      Qed.

      Definition LiRRVq_ball : LiRRVq -> R -> LiRRVq -> Prop
        := quot_lift_ball LiRRV_eq LiRRVball.

      Lemma LiRRVq_ballE x e y : LiRRVq_ball (Quot _ x) e (Quot _ y)  = LiRRVball x e y.
      Proof.
        apply quot_lift_ballE.
      Qed.

      Hint Rewrite LiRRVq_ballE : quot.
      
      Definition LiRRVq_point: LiRRVq
        := Quot _ (LiRRVpoint).

      Lemma LiRRVq_ball_refl x (e : posreal) : LiRRVq_ball x e x.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_ball_refl.
      Qed.
      
      Lemma LiRRVq_ball_sym x y e : LiRRVq_ball x e y -> LiRRVq_ball y e x.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_ball_sym.
      Qed.

      Lemma LiRRVq_ball_trans x y z e1 e2 : LiRRVq_ball x e1 y -> LiRRVq_ball y e2 z -> LiRRVq_ball x (e1+e2) z.
      Proof.
        LiRRVq_simpl.
        apply LiRRV_ball_trans.
      Qed.

      Lemma LiRRVq_minus_minus (x y : LiRRVq) :
        minus x y = LiRRVq_minus x y.
      Proof.
        unfold minus, plus, opp; simpl.
        LiRRVq_simpl.
        now rewrite LiRRVminus_plus.
      Qed.

      Lemma LiRRVq_close_close (x y : LiRRVq) (eps : R) :
        LiRRVq_norm (minus y x) < eps ->
        LiRRVq_ball x eps y.
      Proof.
        intros.
        rewrite LiRRVq_minus_minus in H.
        LiRRVq_simpl.
        autorewrite with quot in *.
        now apply LiRRV_close_close.
      Qed.

      Lemma LiRRVq_norm_ball_compat (x y : LiRRVq) (eps : posreal) :
        LiRRVq_ball x eps y -> LiRRVq_norm (minus y x) < LiRRVnorm_factor * eps.
      Proof.
        intros.
        rewrite LiRRVq_minus_minus.
        LiRRVq_simpl.
        autorewrite with quot in *.
        now apply LiRRV_norm_ball_compat.
      Qed.
      

      Definition LiRRVq_UniformSpace_mixin : UniformSpace.mixin_of LiRRVq
        := UniformSpace.Mixin  LiRRVq LiRRVq_point LiRRVq_ball
                               LiRRVq_ball_refl
                               LiRRVq_ball_sym
                               LiRRVq_ball_trans.

      Canonical LiRRVq_UniformSpace :=
        UniformSpace.Pack LiRRVq LiRRVq_UniformSpace_mixin LiRRVq.

      Canonical LiRRVq_NormedModuleAux :=
        NormedModuleAux.Pack R_AbsRing LiRRVq
                             (NormedModuleAux.Class R_AbsRing LiRRVq
                                                    (ModuleSpace.class _ LiRRVq_ModuleSpace)
                                                    (LiRRVq_UniformSpace_mixin)) LiRRVq.


      
      Definition LiRRVq_NormedModule_mixin : NormedModule.mixin_of R_AbsRing LiRRVq_NormedModuleAux
        := NormedModule.Mixin R_AbsRing LiRRVq_NormedModuleAux
                              LiRRVq_norm
                              LiRRVnorm_factor
                              LiRRVq_norm_plus
                              LiRRVq_norm_scal
                              LiRRVq_close_close
                              LiRRVq_norm_ball_compat
                              LiRRVq_norm0.

      Canonical LiRRVq_NormedModule :=
        NormedModule.Pack R_AbsRing LiRRVq
                          (NormedModule.Class R_AbsRing LiRRVq
                                              (NormedModuleAux.class _ LiRRVq_NormedModuleAux)
                                              LiRRVq_NormedModule_mixin)
                          LiRRVq.


    End quoted.
    
  End packed.

  Hint Rewrite @LiRRVq_constE : quot.
  Hint Rewrite @LiRRVq_zeroE : quot.
  Hint Rewrite @LiRRVq_scaleE : quot.
  Hint Rewrite @LiRRVq_oppE : quot.
  Hint Rewrite @LiRRVq_absE : quot.
  Hint Rewrite @LiRRVq_plusE : quot.
  Hint Rewrite @LiRRVq_minusE : quot.

  Hint Rewrite LiRRVq_normE : quot.


  Global Arguments LiRRV : clear implicits.
  Global Arguments LiRRVq : clear implicits.
  
End Linf.

