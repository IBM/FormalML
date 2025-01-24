Require Import List.
Require Import mdp qvalues fixed_point.
Require Import RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import infprod Dvoretzky Expectation RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import RandomVariableL2.
Require hilbert.
Require Import vecslln Tsitsiklis uniform_converge lim_add.
Require Import ConditionalExpectation VectorConditionalExpectation.
Require Import IndefiniteDescription ClassicalDescription.
Require slln.
Require Import RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Section jaakola_vector1.
  
Context {Ts : Type} {SS:Type} (N:nat)
        {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

Program Definition pos_to_nneg (c : posreal) : nonnegreal :=
  mknonnegreal c _.
Next Obligation.
  left; apply cond_pos.
Qed.

Lemma lemma2_0 (w : Ts)
      (X : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N -> vector R N )
      (C : posreal)   :
  (forall n,  rv_eq (X (S n) ) (fun w => G n w (X n w))) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (X n w)))
            (fun w => (G n w (Rvector_scale beta (X n w))))) ->
  (exists n, X n w = Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs (X n w)) 0.
 Proof.
  intros XG XGB H.
  destruct H.
  apply is_lim_seq_ext_loc with (u := fun n => 0).
  - exists x.
    intros.
    pose (h := (n - x)%nat).
    replace n with (x + h)%nat by lia.
    induction h.
    + replace (x + 0)%nat with (x) by lia.
      rewrite H.
      symmetry.
      now rewrite Rvector_max_abs_zero.
    + replace (x + S h)%nat with (S (x + h))%nat by lia.
      rewrite XG.
      assert (le0: 0 <= 0) by lra.
      replace  (X (x + h)%nat w) with (Rvector_scale (mknonnegreal 0 le0) (X (x + h)%nat w)).
      * rewrite <- XGB.
        rewrite Rvector_scale0.
        symmetry.
        now apply Rvector_max_abs_zero.
      * symmetry in IHh.
        apply Rvector_max_abs_zero in IHh.
        now rewrite Rvector_scale0.
  - apply is_lim_seq_const.
 Qed.

Lemma lemma2_0_w (w : Ts)
      (X : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N  -> vector R N )
      (C : posreal)   :
  (forall n,  rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n (beta : nonnegreal), 
      Rvector_scale beta (G n w (X n w))  = 
        (G n w (Rvector_scale beta (X n w)))) ->
  (exists n, X n w = Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs (X n w)) 0.
 Proof.
  intros XG XGB H.
  destruct H.
  apply is_lim_seq_ext_loc with (u := fun n => 0).
  - exists x.
    intros.
    pose (h := (n - x)%nat).
    replace n with (x + h)%nat by lia.
    induction h.
    + replace (x + 0)%nat with (x) by lia.
      rewrite H.
      symmetry.
      now rewrite Rvector_max_abs_zero.
    + replace (x + S h)%nat with (S (x + h))%nat by lia.
      rewrite XG.
      assert (le0: 0 <= 0) by lra.
      replace  (X (x + h)%nat w) with (Rvector_scale (mknonnegreal 0 le0) (X (x + h)%nat w)).
      * rewrite <- XGB.
        rewrite Rvector_scale0.
        symmetry.
        now apply Rvector_max_abs_zero.
      * symmetry in IHh.
        apply Rvector_max_abs_zero in IHh.
        now rewrite Rvector_scale0.
  - apply is_lim_seq_const.
 Qed.

 Definition Rvector_clip (v : vector R N) (c : nonnegreal) : vector R N
   := if Rgt_dec (Rvector_max_abs v) c then 
        Rvector_scale (c/Rvector_max_abs v) v else
        v.

 Lemma Rvector_clip_le  (v : vector R N) (c : nonnegreal) : 
   Rvector_max_abs (Rvector_clip v c) <= c.
 Proof.
   unfold Rvector_clip.
   match_destr.
   - rewrite Rvector_max_abs_scale.
     unfold Rdiv.
     rewrite Rabs_mult, Rabs_inv, Rabs_Rvector_max_abs.
     generalize (cond_nonneg c); intros.
     field_simplify; try lra.
     rewrite Rabs_right; lra.
   - lra.
 Qed.

 Definition vecrvclip {Ts:Type} (f : Ts -> vector R N) 
            (c : nonnegreal) : Ts -> vector R N
   := fun x => if Rgt_dec (Rvector_max_abs (f x)) c then 
                 Rvector_scale (c/Rvector_max_abs (f x)) (f x) else
                 (f x).

 Lemma vecrvclip_alt (f : Ts -> vector R N) (c : nonnegreal) :
   forall (x : Ts),
     vecrvclip f c x = Rvector_clip (f x) c.
 Proof.
   reflexivity.
 Qed.

 Lemma Rvector_clip_scale v c :
   {c1:R | Rvector_clip v c = Rvector_scale c1 v}.
 Proof.
   destruct (Rgt_dec (Rvector_max_abs v) c).
   - exists (c / Rvector_max_abs v).
     unfold Rvector_clip.
     match_destr; tauto.
   - exists 1.
     unfold Rvector_clip.
     match_destr; try tauto.
     now rewrite Rvector_scale1.
 Qed.

 Lemma vecrvclip_not_0 (x : Ts -> vector R N) (C : posreal) (w : Ts) :
   x w <> Rvector_zero ->
   vecrvclip x (pos_to_nneg C) w <> Rvector_zero.
 Proof.
   intros.
   unfold vecrvclip.
   destruct C as [? ?].
   match_destr.
   simpl.
   apply Rvector_scale_not_0.
   split; trivial.
   apply Rdiv_not_0; split.
   - apply Rgt_not_eq.
     apply cond_pos.
   - now apply Rvector_max_abs_nzero.
 Qed.

Lemma lemma2_n00 (w : Ts)
      (X XX : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N  -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n, rv_eq (XX (S n) ) (vecrvclip (fun w => G n w (XX n w) ) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (X n w)))
            (fun w => (G n w (Rvector_scale beta (X n w))))) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (XX n w) ))
            (fun w => (G n w (Rvector_scale beta (XX n w)) ))) ->
  (forall n, X n w <> Rvector_zero) ->
  forall n,
  exists (CC : R),
    CC > 0 /\
    Rvector_scale CC (X n w) = XX n w.
  Proof.
  intros XG XXG XX0 XGB XXGB Xn0.
  induction n.
  - exists ((Rvector_max_abs (XX 0%nat w))/(Rvector_max_abs (X 0%nat w))).
    assert (XX 0%nat w <> Rvector_zero).
    { 
      rewrite XX0.
      now apply vecrvclip_not_0.
    }
    split.
    + apply Rlt_gt.
      apply Rdiv_lt_0_compat.
      * generalize (Rvector_max_abs_nzero (XX 0%nat w) H); intros.
        generalize (Rvector_max_abs_nonneg (XX 0%nat w)); intros.
        lra.
      * generalize (Rvector_max_abs_nzero (X 0%nat w) (Xn0 0%nat)); intros.
        generalize (Rvector_max_abs_nonneg (X 0%nat w)); intros.        
        lra.
    + rewrite XX0.
      unfold vecrvclip.
      match_destr.
      * f_equal.
        rewrite Rvector_max_abs_scale; simpl.
        rewrite Rabs_right.
        -- field.
           now apply Rvector_max_abs_nzero.
        -- apply Rle_ge.
           apply Rdiv_le_0_compat.
           ++ simpl; left; apply cond_pos.
           ++ apply Rgt_lt.
              eapply Rgt_trans.
              ** apply r.
              ** simpl; apply cond_pos.
      * replace (Rvector_max_abs (X 0%nat w) / Rvector_max_abs (X 0%nat w)) with 1.
        -- now rewrite Rvector_scale1.
        -- field.
           now apply Rvector_max_abs_nzero.           
  - destruct IHn as [? [? ?]].
    assert (XX (S n) w <> Rvector_zero).
    {
      rewrite XXG.
      apply vecrvclip_not_0.
      rewrite <- H0.
      assert (0 <= x) by lra.
      assert (G n w (Rvector_scale (mknonnegreal x H1) (X n w)) <> Rvector_zero).
      {
        rewrite <- XGB.
        simpl.
        rewrite <- XG.
        apply Rvector_scale_not_0.
        split; trivial.
        lra.
      }
      now simpl in H2.
    }
    destruct (Rgt_dec (Rvector_max_abs (G n w (XX n w) )) C).
    + exists (x * (C / Rvector_max_abs (G n w (XX n w) ))).
      split.
      * apply Rmult_gt_0_compat; trivial.
        apply Rlt_gt.
        apply Rdiv_lt_0_compat.
        -- apply cond_pos.
        -- generalize (cond_pos C).
           lra.
      * rewrite XXG.
        unfold vecrvclip; simpl.
        match_destr; try lra.
        rewrite XG.
        rewrite <- H0.
        assert (le0: 0 <= x) by lra.
        assert (rv_eq (fun w : Ts => Rvector_scale (mknonnegreal x le0) (G n w (X n w)))
                       (fun w : Ts => G n w (Rvector_scale (mknonnegreal x le0) (X n w)))).
        {
          now rewrite <- XGB.
        }
        simpl in H2.
        rewrite <- H2.
        rewrite Rvector_scale_scale.
        f_equal.
        field.
        rewrite Rvector_max_abs_scale.
        apply Rmult_not_0; split.
        -- rewrite Rabs_right; lra.
        -- rewrite <- XG.
           now apply Rvector_max_abs_nzero.
    + assert (le0: 0 <= x) by lra.
      exists (mknonnegreal x le0).
      split; trivial.
      rewrite XXG.
      unfold vecrvclip.
      match_destr; try lra.
      * now simpl.
      * rewrite XG.
        rewrite <- H0.
        now rewrite XGB.
  Qed.

Lemma lemma2_n00_w (w : Ts)
      (X XX : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w)  )) ->
  (forall n, rv_eq (XX (S n) ) (vecrvclip (fun w => G n w (XX n w) ) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->
  (forall n (beta : nonnegreal), 
      Rvector_scale beta (G n w (X n w)) = 
        (G n w (Rvector_scale beta (X n w)))) ->
  (forall n (beta : nonnegreal), 
      Rvector_scale beta (G n w (XX n w)) = 
        (G n w (Rvector_scale beta (XX n w)))) ->  
  (forall n, X n w <> Rvector_zero) ->
  forall n,
  exists (CC : R),
    CC > 0 /\
    Rvector_scale CC (X n w) = XX n w.
  Proof.
  intros XG XXG XX0 XGB XXGB Xn0.
  induction n.
  - exists ((Rvector_max_abs (XX 0%nat w))/(Rvector_max_abs (X 0%nat w))).
    assert (XX 0%nat w <> Rvector_zero).
    { 
      rewrite XX0.
      now apply vecrvclip_not_0.
    }
    split.
    + apply Rlt_gt.
      apply Rdiv_lt_0_compat.
      * generalize (Rvector_max_abs_nzero (XX 0%nat w) H); intros.
        generalize (Rvector_max_abs_nonneg (XX 0%nat w)); intros.
        lra.
      * generalize (Rvector_max_abs_nzero (X 0%nat w) (Xn0 0%nat)); intros.
        generalize (Rvector_max_abs_nonneg (X 0%nat w)); intros.        
        lra.
    + rewrite XX0.
      unfold vecrvclip.
      match_destr.
      * f_equal.
        rewrite Rvector_max_abs_scale; simpl.
        rewrite Rabs_right.
        -- field.
           now apply Rvector_max_abs_nzero.
        -- apply Rle_ge.
           apply Rdiv_le_0_compat.
           ++ simpl; left; apply cond_pos.
           ++ apply Rgt_lt.
              eapply Rgt_trans.
              ** apply r.
              ** simpl; apply cond_pos.
      * replace (Rvector_max_abs (X 0%nat w) / Rvector_max_abs (X 0%nat w)) with 1.
        -- now rewrite Rvector_scale1.
        -- field.
           now apply Rvector_max_abs_nzero.           
  - destruct IHn as [? [? ?]].
    assert (XX (S n) w <> Rvector_zero).
    {
      rewrite XXG.
      apply vecrvclip_not_0.
      rewrite <- H0.
      assert (0 <= x) by lra.
      assert (G n w (Rvector_scale (mknonnegreal x H1) (X n w)) <> Rvector_zero).
      {
        rewrite <- XGB.
        simpl.
        rewrite <- XG.
        apply Rvector_scale_not_0.
        split; trivial.
        lra.
      }
      now simpl in H2.
    }
    destruct (Rgt_dec (Rvector_max_abs (G n w (XX n w))) C).
    + exists (x * (C / Rvector_max_abs (G n w (XX n w)))).
      split.
      * apply Rmult_gt_0_compat; trivial.
        apply Rlt_gt.
        apply Rdiv_lt_0_compat.
        -- apply cond_pos.
        -- generalize (cond_pos C).
           lra.
      * rewrite XXG.
        unfold vecrvclip; simpl.
        match_destr; try lra.
        rewrite XG.
        rewrite <- H0.
        assert (le0: 0 <= x) by lra.
        assert (Rvector_scale (mknonnegreal x le0) (G n w (X n w)) =
                 G n w (Rvector_scale (mknonnegreal x le0) (X n w))).
        {
          now rewrite <- XGB.
        }
        simpl in H2.
        rewrite <- H2.
        rewrite Rvector_scale_scale.
        f_equal.
        field.
        rewrite Rvector_max_abs_scale.
        apply Rmult_not_0; split.
        -- rewrite Rabs_right; lra.
        -- rewrite <- XG.
           now apply Rvector_max_abs_nzero.
    + assert (le0: 0 <= x) by lra.
      exists (mknonnegreal x le0).
      split; trivial.
      rewrite XXG.
      unfold vecrvclip.
      match_destr; try lra.
      * now simpl.
      * rewrite XG.
        rewrite <- H0.
        now rewrite XGB.
  Qed.

  Lemma lemma2_n000 (w : Ts)
      (X XX : nat -> Ts -> vector R N)
      (G : nat -> Ts  -> vector R N -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n, rv_eq (XX (S n)) (vecrvclip (fun w => G n w (XX n w)) 
                                           (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (X n w)))
            (fun w => (G n w (Rvector_scale beta (X n w))))) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (XX n w)))
            (fun w => (G n w (Rvector_scale beta (XX n w))))) ->
  (forall n, X n w <> Rvector_zero) ->
  forall n, XX n w <> Rvector_zero.
 Proof.
   intros XG XXG XX0 XGB XXGB Xn0.
   generalize (lemma2_n00 w X XX G C); intros.
   cut_to H; trivial.
   destruct (H n) as [? [? ?]].
   rewrite <- H1.
   apply Rvector_scale_not_0.
   split; trivial.
   lra.
 Qed.

  Lemma lemma2_n000_w (w : Ts)
      (X XX : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n, rv_eq (XX (S n)) (vecrvclip (fun w => G n w (XX n w)) 
                                           (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->
  (forall n (beta : nonnegreal), 
      Rvector_scale beta (G n w (X n w)) = 
        (G n w (Rvector_scale beta (X n w)))) ->
  (forall n (beta : nonnegreal), 
      Rvector_scale beta (G n w (XX n w)) = 
        (G n w (Rvector_scale beta (XX n w)))) ->  
  (forall n, X n w <> Rvector_zero) ->
  forall n, XX n w <> Rvector_zero.
 Proof.
   intros XG XXG XX0 XGB XXGB Xn0.
   generalize (lemma2_n00_w w X XX G C); intros.
   cut_to H; trivial.
   destruct (H n) as [? [? ?]].
   rewrite <- H1.
   apply Rvector_scale_not_0.
   split; trivial.
   lra.
 Qed.

Lemma lemma2_n0 (w : Ts)
      (X XX : nat  -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n, rv_eq (XX (S n)) (vecrvclip (fun w => G n w (XX n w)) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (X n w)))
            (fun w => (G n w (Rvector_scale beta (X n w))))) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (XX n w)))
            (fun w => (G n w (Rvector_scale beta (XX n w))))) ->
  (forall n, X n w <> Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs(XX n w)) 0 ->
  is_lim_seq (fun n => Rvector_max_abs(X n w)) 0.
Proof.
  intros XG XXG XX0 XGB XXGB Xn0 H.
  assert (XXn0: forall n, XX n w <> Rvector_zero).
  {
   generalize (lemma2_n000 w X XX G C); intros.
   cut_to H0; trivial.
  }
  generalize H; intros HH.
  apply is_lim_seq_spec in H.
  unfold is_lim_seq' in H.
  intros.
  assert (exists (nn:nat) (CC:R), 
             forall n, (nn <= n)%nat ->
                       (X n w) = Rvector_scale CC (XX n w)).
  {
    destruct (H C) as [n0 ?].
    exists n0.
    assert (forall n, (n0 <= n)%nat ->
                      (XX (S n) w = G n w (XX n w))).
    {
      intros.
      rewrite XXG.
      specialize (H0 (S n)).
      cut_to H0; try lia.
      rewrite Rminus_0_r in H0.
      rewrite Rabs_right in H0.
      - rewrite XXG in H0.
        unfold vecrvclip; simpl.
        unfold vecrvclip in H0; simpl in H0.
        match_destr.
        rewrite Rvector_max_abs_scale in H0.
        rewrite Rabs_div in H0.
        + unfold Rdiv in H0.
          rewrite Rabs_right in H0.
          * rewrite Rabs_right in H0.
            -- field_simplify in H0; try lra.
               try rewrite H0 in r.
               destruct C as [? ?].
               simpl in r.
               lra.
            -- left.
               eapply Rgt_trans.
               ++ apply r.
               ++ apply cond_pos.
         * left; apply cond_pos.
       + apply Rgt_not_eq.
         eapply Rgt_trans.
         * apply r.
         * apply cond_pos.
      - apply Rle_ge, Rvector_max_abs_nonneg.
    }
    generalize (lemma2_n00 w X XX G C); intros.
    cut_to H2; trivial.
    destruct (H2 n0) as [? [? ?]].
    exists (/ x).
    intros.
    pose (h := (n - n0)%nat).
    replace n with (n0 + h)%nat by lia.
    induction h.
    - replace (n0 + 0)%nat with n0 by lia.
      rewrite <- H4.
      rewrite Rvector_scale_scale.
      rewrite <- Rinv_l_sym; trivial.
      now rewrite Rvector_scale1.
      lra.
    - replace (n0 + S h)%nat with (S (n0 + h))%nat by lia.
      rewrite XG.
      rewrite H1; try lia.
      rewrite IHh.
      assert (0 <= /x).
      {
        assert (0 < /x).
        {
          now apply Rinv_0_lt_compat.
        }
        lra.
      }
      assert ( G (n0 + h)%nat w (Rvector_scale (mknonnegreal (/ x) H6) (XX (n0 + h)%nat w)) =
                 Rvector_scale (mknonnegreal (/ x) H6) (G (n0 + h)%nat w (XX (n0 + h)%nat w))).
      {
        now rewrite XXGB.
      }
      now simpl in H7.
  }
  destruct H0 as [nn [CC ?]].
  apply is_lim_seq_ext_loc with (u := fun n => Rabs(CC) * Rvector_max_abs (XX n w)).
  - exists nn; intros.
    rewrite H0; trivial.
    now rewrite Rvector_max_abs_scale.
  - replace (Finite 0) with (Rbar_mult (Rabs CC) 0).
    + now apply is_lim_seq_scal_l.
    + apply Rbar_mult_0_r.
  Qed.

Lemma lemma2_n0_w (w : Ts)
      (X XX : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n, rv_eq (XX (S n)) (vecrvclip (fun w => G n w (XX n w)) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->

 (forall n (beta : nonnegreal), 
      Rvector_scale beta (G n w (X n w)) = 
        (G n w (Rvector_scale beta (X n w)))) ->
  (forall n (beta : nonnegreal), 
      Rvector_scale beta (G n w (XX n w)) = 
        (G n w (Rvector_scale beta (XX n w)))) ->  
  (forall n, X n w <> Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs(XX n w)) 0 ->
  is_lim_seq (fun n => Rvector_max_abs(X n w)) 0.
Proof.
  intros XG XXG XX0 XGB XXGB Xn0 H.
  assert (XXn0: forall n, XX n w <> Rvector_zero).
  {
   generalize (lemma2_n000_w w X XX G C); intros.
   cut_to H0; trivial.
  }
  generalize H; intros HH.
  apply is_lim_seq_spec in H.
  unfold is_lim_seq' in H.
  intros.
  assert (exists (nn:nat) (CC:R), 
             forall n, (nn <= n)%nat ->
                       (X n w) = Rvector_scale CC (XX n w)).
  {
    destruct (H C) as [n0 ?].
    exists n0.
    assert (forall n, (n0 <= n)%nat ->
                      (XX (S n) w = G n w (XX n w))).
    {
      intros.
      rewrite XXG.
      specialize (H0 (S n)).
      cut_to H0; try lia.
      rewrite Rminus_0_r in H0.
      rewrite Rabs_right in H0.
      - rewrite XXG in H0.
        unfold vecrvclip; simpl.
        unfold vecrvclip in H0; simpl in H0.
        match_destr.
        rewrite Rvector_max_abs_scale in H0.
        rewrite Rabs_div in H0.
        + unfold Rdiv in H0.
          rewrite Rabs_right in H0.
          * rewrite Rabs_right in H0.
            -- field_simplify in H0; try lra.
               try rewrite H0 in r.
               destruct C as [? ?].
               simpl in r.
               lra.
            -- left.
               eapply Rgt_trans.
               ++ apply r.
               ++ apply cond_pos.
         * left; apply cond_pos.
       + apply Rgt_not_eq.
         eapply Rgt_trans.
         * apply r.
         * apply cond_pos.
      - apply Rle_ge, Rvector_max_abs_nonneg.
    }
    generalize (lemma2_n00_w w X XX G C); intros.
    cut_to H2; trivial.
    destruct (H2 n0) as [? [? ?]].
    assert (0 <= /x).
    {
      assert (0 < /x).
      {
        now apply Rinv_0_lt_compat.
      }
      lra.
    }
    exists (mknonnegreal (/ x) H5).
    intros.
    pose (h := (n - n0)%nat).
    replace n with (n0 + h)%nat by lia.
    induction h.
    - replace (n0 + 0)%nat with n0 by lia.
      rewrite <- H4.
      rewrite Rvector_scale_scale.
      simpl.
      rewrite <- Rinv_l_sym; trivial.
      now rewrite Rvector_scale1.
      lra.
    - replace (n0 + S h)%nat with (S (n0 + h))%nat by lia.
      rewrite XG.
      rewrite H1; try lia.
      rewrite XXGB.
      now f_equal.
  }
  destruct H0 as [nn [CC ?]].
  apply is_lim_seq_ext_loc with (u := fun n => Rabs(CC) * Rvector_max_abs (XX n w)).
  - exists nn; intros.
    rewrite H0; trivial.
    now rewrite Rvector_max_abs_scale.
  - replace (Finite 0) with (Rbar_mult (Rabs CC) 0).
    + now apply is_lim_seq_scal_l.
    + apply Rbar_mult_0_r.
  Qed.

Lemma lemma2 
      (X XX : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n, rv_eq (XX (S n)) (vecrvclip (fun w => G n w (XX n w)) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (X n w)))
            (fun w => (G n w (Rvector_scale beta (X n w))))) ->
  (forall n (beta : nonnegreal), 
      rv_eq (fun w => Rvector_scale beta (G n w (XX n w)))
            (fun w => (G n w (Rvector_scale beta (XX n w))))) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (XX n w)) 0) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (X n w)) 0).
Proof.
  intros XG XXG XX0 XGB XXGB.
  apply almost_impl, all_almost; intros w H.
  destruct (classic (exists n, X n w = Rvector_zero)).
  - now apply (lemma2_0 w X G C).
  - generalize (not_ex_all_not nat _ H0); intros HH.
    now apply (lemma2_n0 w X XX G C).
Qed.
        
Lemma lemma2_almostG
      (X XX : nat -> Ts -> vector R N)
      (G : nat -> Ts -> vector R N -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n)) (fun w => G n w (X n w))) ->
  (forall n, rv_eq (XX (S n)) (vecrvclip (fun w => G n w (XX n w)) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat) (vecrvclip (X 0%nat) (pos_to_nneg C)) ->
  almost prts (fun w =>
                 forall n (beta : nonnegreal), 
                   Rvector_scale beta (G n w (X n w)) = 
                     G n w (Rvector_scale beta (X n w))) ->
  almost prts (fun w =>
                 forall n (beta : nonnegreal), 
                   Rvector_scale beta (G n w (XX n w)) = 
                     G n w (Rvector_scale beta (XX n w))) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (XX n w)) 0) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (X n w)) 0).
Proof.
  intros XG XXG XX0 XGB XXGB.
  apply almost_impl.
  revert XGB; apply almost_impl.
  revert XXGB; apply almost_impl.
  apply all_almost.
  intros w ???.
  destruct (classic (exists n, X n w = Rvector_zero)).
  - now apply (lemma2_0_w w X G C).
  - generalize (not_ex_all_not nat _ H2); intros HH.
    now apply (lemma2_n0_w w X XX G C).
Qed.
  
Lemma gamma_eps_le (gamma' : posreal) (gamma'_lt1 : gamma' < 1) :
  {eps : posreal | gamma' <=  / (1 + eps)}.
Proof.
  assert (0 < (1 - gamma') / (2 * gamma')).
  {
    assert (0 < gamma').
    {
      apply cond_pos.
    }
    apply RIneq.Rdiv_lt_0_compat; lra.
  }
  exists (mkposreal _ H).
  simpl.
  apply Rmult_le_reg_r with (r :=  (1 + ((1 - gamma') / (2 * gamma')))).
  - eapply Rlt_trans.
    apply H; lra.
    lra.
  - unfold Rdiv.
    rewrite Rinv_l; try lra.
    rewrite Rmult_plus_distr_l, Rmult_1_r.
    rewrite <- Rmult_assoc, Rmult_comm, <- Rmult_assoc.
    replace (/ (2 * gamma') * gamma') with (/2).
    + lra.
    + rewrite Rinv_mult, Rmult_assoc, Rinv_l, Rmult_1_r; trivial.
      apply Rgt_not_eq.
      apply cond_pos.
Qed.

Lemma lemma3_gamma_eps_le (gamma : posreal) :
  gamma < 1 ->
  {eps : posreal |  gamma + (1 - gamma)/2 <= / (1 + eps)}.
Proof.
  intros.
  assert (0 < gamma + (1 - gamma)/2).
  {
    generalize (cond_pos gamma); intros.
    apply Rplus_lt_0_compat; lra.
  }
  assert (mkposreal _ H0 < 1).
  {
    simpl; lra.
  }
  apply (gamma_eps_le (mkposreal _ H0) H1).
Qed.

    Lemma lemma3_helper_vector_forall (f : nat -> Ts -> vector R N) (fstar: vector R N) (C gamma : posreal)
      {rv : forall n, RandomVariable dom (Rvector_borel_sa N) (f n)} :
      (forall i pf, almost prts (fun x => is_lim_seq (fun n => vector_nth i pf (f n x)) (vector_nth i pf fstar))) ->
      Rvector_max_abs fstar <= gamma * C ->
      gamma < 1 ->
      forall (eps1 eps2:posreal),
        gamma + (1 - gamma)/2 <= / (1 + eps1) ->
        eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (f (n + n0)%nat)) (C / (1 + eps1))))) >= 1 - eps2).    
   Proof.
     intros H H0 gamma_1 eps1 eps2 gamma_lt.
      assert (0 < ((1 - gamma)/2) * C).
      {
        apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; lra.
        - apply cond_pos.
      }
      
     generalize (conv_as_prob_1_eps_vector_forall f fstar H (mkposreal _ H1) eps2).
     apply eventually_impl.
     apply all_eventually; intros.
     eapply Rge_trans; cycle 1.
     apply H2.
     apply Rle_ge.
     apply ps_sub.
     intros ?.
     simpl.
     intros.
     specialize (H3 n).
     generalize (Rvector_max_abs_triang_inv (f (n + x)%nat x0) fstar); intros.
     unfold rvmaxabs, vecrvminus, vecrvplus, vecrvopp, vecrvscale, const in H3.
     unfold Rvector_minus, Rvector_opp in H4.
     assert (Rvector_max_abs(f (n + x)%nat x0) <= (1 - gamma) * C / 2 + gamma * C) by lra.
     eapply Rle_trans.
     apply H5.
     generalize (cond_pos C); intros.
     apply Rmult_le_compat_l with (r := C) in gamma_lt; lra.
  Qed.

    Lemma lemma3_helper_vector_forall_almost_eventually_le (f g : nat -> Ts -> (vector R N)) (fstar: vector R N) (C gamma : posreal)
      {rvf : forall n, RandomVariable dom (Rvector_borel_sa N) (f n)} 
      {rvg : forall n, RandomVariable dom (Rvector_borel_sa N) (g n)} :       
      (forall i pf, almost prts (fun x => is_lim_seq (fun n => vector_nth i pf (f n x)) (vector_nth i pf fstar))) ->
      (exists n0, forall n, almostR2 prts Rle (rvmaxabs (g (n + n0)%nat)) (rvmaxabs (f n))) ->
      Rvector_max_abs fstar <= gamma * C ->
      gamma < 1 ->
      forall (eps1 eps2:posreal),
        gamma + (1 - gamma)/2 <= / (1 + eps1) ->
        eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (g (n + n0)%nat)) (C / (1 + eps1))))) >= 1 - eps2).
    Proof.
      intros H H0 H1 gamma_1 eps1 eps2 gamma_lt.
      destruct (lemma3_helper_vector_forall f fstar C gamma H H1 gamma_1 eps1 eps2 gamma_lt).
      destruct H0.
      exists (x + x0)%nat.
      intros.
      specialize (H2 (n - x0)%nat).
      cut_to H2; try lia.
      eapply Rge_trans; cycle 1.
      apply H2.
      apply Rle_ge.
      apply ps_almostR2_sub.
      apply almost_forall in H0.
      revert H0; apply almost_impl.
      apply all_almost; intros ???.
      unfold event_sub, pre_event_sub.
      simpl; intros.
      specialize (H0 (n0 + (n - x0))%nat).
      simpl in H0.
      replace (n0 + (n - x0) + x0)%nat with (n0 + n)%nat in H0 by lia.
      eapply Rle_trans.
      apply H0.
      apply H4.
    Qed.   
    

   Lemma lemma3_helper_iter_conv  (f α : nat -> R) (C : R) :
      (forall n, 0 <= α n < 1) ->
      l1_divergent α ->
      (forall n, f (S n) = (1 - α n) * f n + (α n) * C) ->
      is_lim_seq (fun n => f n) C.
   Proof.
     intros abounds adiv fprop.
     pose (g := fun n => f n - C).
     assert (is_lim_seq g 0).
     {
       assert (forall n, g (S n) = (1 - α n) * g n).
       {
         intros.
         unfold g.
         rewrite fprop.
         lra.
       }
       assert (forall k,
                  g (S k) = (part_prod (fun n => (mkposreal (1 - α n)  (a1_pos_pf (abounds  n)))) k) * (g 0%nat)).
       {
         intros.
         induction k.
         - unfold part_prod.
           rewrite part_prod_n_k_k.
           simpl.
           rewrite  H.
           lra.
         - rewrite H, IHk.
           unfold part_prod.
           rewrite part_prod_n_S; try lia.
           simpl.
           lra.
       }
       rewrite is_lim_seq_incr_1.
       apply is_lim_seq_ext with
         (u := (fun k => part_prod (fun n : nat => {| pos := 1 - α n; cond_pos := a1_pos_pf (abounds n) |}) k * g 0%nat)).
       - intros.
         now rewrite H0.
       - apply is_lim_seq_mult with (l1 := 0) (l2 := g 0%nat).
         + now apply Fprod_0.
         + apply is_lim_seq_const.
         + unfold is_Rbar_mult.
           simpl.
           now rewrite Rmult_0_l.
     }         
     apply is_lim_seq_ext with (u := fun n => g n + C).
     - intros.
       unfold g.
       lra.
     - apply is_lim_seq_plus with (l1 := 0) (l2 := C); trivial.
       + apply is_lim_seq_const.
       + unfold is_Rbar_plus.
         simpl.
         now rewrite Rplus_0_l.
  Qed.

   Lemma lemma3_helper_iter_conv1  (f α : nat -> R) (C : R) :
      (exists n,  α n = 1) ->
      (forall n, f (S n) = (1 - α n) * f n + (α n) * C) ->
      is_lim_seq (fun n => f n) C.
   Proof.
     intros.
     destruct H.
     rewrite is_lim_seq_incr_n with (N := (S x)).
     apply is_lim_seq_ext with (u := fun n => C).
     - induction n.
       + replace (0 + S x)%nat with (S x) by lia.
         rewrite H0, H.
         lra.
       + replace (S n + S x)%nat with (S (n + S x)) by lia.
         rewrite H0.
         rewrite <- IHn.
         lra.
     - apply is_lim_seq_const.
   Qed.

   Lemma lemma3_helper_iter_conv2  (f α : nat -> R) (C : R) :
      (forall n, 0 <= α n <= 1) ->
      l1_divergent α ->
      (forall n, f (S n) = (1 - α n) * f n + (α n) * C) ->
      is_lim_seq (fun n => f n) C.
   Proof.
     intros.
     destruct (excluded_middle_informative (forall n, α n < 1)).
     - apply lemma3_helper_iter_conv with (α := α); trivial.
       intro n.
       specialize (r n).
       specialize (H n).
       lra.
     - rewrite not_forall in n.
       apply lemma3_helper_iter_conv1 with (α := α); trivial.
       destruct n.
       exists x.
       specialize (H x).
       lra.
   Qed.     

    Lemma lemma3_lim_eps (eps : posreal) :
      is_lim_seq (fun n => (/ (1 + eps))^n) 0.
    Proof.
      apply is_lim_seq_geom.
      generalize (cond_pos eps); intros.
      rewrite Rabs_right.
      - replace (1) with (/1) at 2 by lra.
        apply Rinv_lt_contravar; lra.
      - left.
        apply Rinv_pos.
        generalize (cond_pos eps); intros.
        lra.
    Qed.

    Lemma lemma3_lim_eps_alt (C eps : posreal) :
      is_lim_seq (fun n => C * (/ (1 + eps))^n) 0.
    Proof.
      replace (Finite 0) with (Rbar_mult C 0).
      apply is_lim_seq_scal_l.
      - apply lemma3_lim_eps.
      - simpl.
        now rewrite Rmult_0_r.
    Qed.
    
    Lemma is_series_geom_S (q : R):
      Rabs q < 1 -> is_series (fun n : nat => q ^ (S n)) (q / (1 - q)).
    Proof.
      intros.
      generalize (is_series_geom q H); intros.
      apply is_series_scal_r with (c := q) in H0.
      unfold Rdiv.
      rewrite Rmult_comm.
      revert H0.
      apply is_series_ext.
      intros.
      now rewrite Rmult_comm, tech_pow_Rmult.
    Qed.

    Lemma xm1_exp2 :
      exists (x : posreal),
      forall y, 
        0 <= y < x ->
        exp(-2*y) <= 1-y <= exp(-y).
    Proof.
      destruct xm1_exp.
      exists x.
      intros.
      specialize (H y H0).
      generalize (exp_ineq (- y)); intros.
      lra.
    Qed.

    Lemma Rabs_xm1_exp2 :
      exists (x : posreal),
      forall y, 
        Rabs y < x ->
        exp(-2*(Rabs y)) <= 1-(Rabs y) <= exp(-(Rabs y)).
     Proof.
       destruct xm1_exp2.
       exists x.
       intros.
       apply H.
       split; trivial.
       apply Rabs_pos.
     Qed.

    Lemma pow_le_1 (y : R) :
      0 <= y <= 1 ->
      forall n,
        y ^ S n <= y.
    Proof.
      induction n.
      - now rewrite pow_1; right.
      - rewrite <- tech_pow_Rmult.
        destruct H.
        apply Rmult_le_compat_l with (r := y) in IHn; trivial.
        apply Rmult_le_compat_l with (r := y) in H0; trivial.        
        lra.
    Qed.

    Lemma prod_pow_m1_le :
      exists (x : posreal),
      forall y, 
        0 <= y < x ->
        y <= 1 ->
        forall m,
          exp (-2 * (sum_n (fun n => y ^ S n)) m) <=
            prod_f_R0 (fun n => 1 - y ^ S n) m <=
            exp (-1 * sum_n (fun n => y ^ S n) m).
    Proof.
      destruct xm1_exp2.
      exists x.
      intros.
      rewrite Rmult_comm, slln.sum_n_Rscal_r.
      rewrite Rmult_comm, slln.sum_n_Rscal_r.
      rewrite exp_sum_prod_f_R0.
      rewrite exp_sum_prod_f_R0.
      assert (forall n, y^S n <= y).
      {
        apply pow_le_1.
        lra.
      }
      assert (forall n, y^S n <= 1).
      {
        intros.
        specialize (H2 n).
        lra.
      }
      assert (forall n, 0 <= y^S n < x).
      {
        split.
        - apply pow_le; lra.
        - specialize (H2 n); lra.
      }
      split; apply prod_SO_Rle; intros.
      - rewrite Rmult_comm.
        split.
        + left; apply exp_pos.
        + apply H.
          apply H4.
      - split.
        + specialize (H2 n); lra.
        + replace (y^S n * -1) with (- y^S n) by lra.
          apply H.
          apply H4.
    Qed.

     Lemma prod_pow_m1_le_alt :
       exists (x : posreal),
         x <= 1 /\
           forall y, 
             0 <= y < x ->
             forall m,
               exp (-2 * (sum_n (fun n => y ^ S n)) m) <=
                 prod_f_R0 (fun n => 1 - y ^ S n) m <=
                 exp (-1 * sum_n (fun n => y ^ S n) m).
     Proof.
       destruct prod_pow_m1_le.
       assert (0 < Rmin x 1).
       {
         apply Rmin_Rgt.
         split; try lra.
         apply cond_pos.
       }
       exists (mkposreal _ H0).
       split.
       - simpl.
         apply Rmin_r.
       - intros.
         specialize (H y).
         apply H; simpl in H1; destruct H1; apply Rmin_Rgt in H2; lra.
    Qed.         
    
    Lemma lim_seq_prod_pow_m1_le1 :
      exists (x : posreal),
        x <= 1 /\
          forall y, 
            0 <= y < x ->
            Rbar_le (Lim_seq (fun m => 
                                exp (-2 * (sum_n (fun n => y ^ S n)) m)))
              (Lim_seq (fun m => prod_f_R0 (fun n => 1 - y ^ S n) m)) /\
              Rbar_le (Lim_seq (fun m => prod_f_R0 (fun n => 1 - y ^ S n) m))
                (Lim_seq (fun m => exp (-1 * sum_n (fun n => y ^ S n) m))).
      Proof.
        destruct prod_pow_m1_le_alt as [? [??]].
        exists x.
        split; trivial.
        intros.
        specialize (H0 y H1).
        split; apply Lim_seq_le; intros; apply H0.
      Qed.

      Lemma lim_seq_prod_pow_m1_le1_alt :
        exists (x : posreal),
          x <= 1 /\
            forall y, 
              0 <= y < x ->
              Rbar_le (exp (-2 * y / (1 - y)))
                (Lim_seq (fun m => prod_f_R0 (fun n => 1 - y ^ S n) m)) /\
                Rbar_le (Lim_seq (fun m => prod_f_R0 (fun n => 1 - y ^ S n) m))
                  (exp (-1 * y / (1 - y))).
        Proof.
          destruct lim_seq_prod_pow_m1_le1 as [? [??]].
          exists x.
          split; trivial.
          intros.
          specialize (H0 y H1).
          destruct H0.
          generalize (is_series_geom_S y); intros.
          rewrite Rabs_right in H3; try lra.
          assert ( y < 1) by lra.
          specialize (H3 H4).
          rewrite series_seq in H3.
          split.
          - assert (is_lim_seq (fun m : nat => exp (-2 * sum_n (fun n : nat => y ^ S n) m)) (exp (-2 * y / (1 - y)))).
            {
              apply is_lim_seq_continuous.
              - apply derivable_continuous_pt.
                apply derivable_pt_exp.
              - replace (Finite (-2 * y / (1 - y))) with
                  (Rbar_mult (-2) (y / (1 - y))).
                + apply is_lim_seq_scal_l; trivial.
                + unfold Rbar_mult; simpl.
                  f_equal; lra.
            }
            apply is_lim_seq_unique in H5.
            now rewrite H5 in H0.
          - assert (is_lim_seq (fun m : nat => exp (-1 * sum_n (fun n : nat => y ^ S n) m)) (exp (-1 * y / (1 - y)))).
            {
              apply is_lim_seq_continuous.
              - apply derivable_continuous_pt.
                apply derivable_pt_exp.
              - replace (Finite (-1 * y / (1 - y))) with
                  (Rbar_mult (-1) (y / (1 - y))).
                + apply is_lim_seq_scal_l; trivial.
                + unfold Rbar_mult; simpl.
                  f_equal; lra.
            }
            apply is_lim_seq_unique in H5.            
            now rewrite H5 in H2.
        Qed.

       
       Lemma lemma3_plim_Rabs :
         is_lim (fun y => Lim_seq (fun m => prod_f_R0 (fun n => 1 - (Rabs y) ^ S n) m)) 0 1.
       Proof.
         apply is_lim_le_le_loc with (f := fun y => (exp (-2 * (Rabs y) / (1 - (Rabs y)))))
                                     (g := fun y => (exp (-1 * (Rabs y) / (1 - (Rabs y))))).
         - destruct lim_seq_prod_pow_m1_le1_alt as [? [??]].
           exists x.
           intros.
           unfold ball in H1.
           simpl in H1.
           unfold AbsRing_ball in H1.
           unfold abs, minus,plus, opp in H1; simpl in H1.
           replace (y + - 0) with y in H1 by lra.
           specialize (H0 (Rabs y)).
           cut_to H0.
           + destruct H0.
             generalize (bounded_is_finite _ _ _ H0 H3); intros.
             rewrite <- H4 in H0; simpl in H0.
             rewrite <- H4 in H3; simpl in H3.
             split; trivial.
           + unfold ball in H1.
             simpl in H1.
             unfold AbsRing_ball in H1.
             unfold abs, minus,plus, opp in H1; simpl in H1.
             replace (y + - 0) with y in H1 by lra.
             split; trivial.
             apply Rabs_pos.
         - assert (-2 <> 0) by lra.
           generalize (is_lim_exp_c_Rabs_y_m1 _ H); intros.
           revert H0.
           apply is_lim_ext.
           intros.
           f_equal.
           lra.
         - assert (-1 <> 0) by lra.
           generalize (is_lim_exp_c_Rabs_y_m1 _ H); intros.
           revert H0.
           apply is_lim_ext.
           intros.
           f_equal.
           lra.
       Qed.

     End jaakola_vector1.
     Section newN.

       Context {Ts : Type} {SS:Type} (N:nat)
         {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.


       Lemma lemma3_vector_forall_eventually_almost
         (α X f : nat -> Ts -> vector R (S N)) (C γ : posreal)
         (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n))
         (rvf : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (f n)) :          
         almost prts (fun ω => forall t i pf , 0 <= vector_nth i pf (α t ω) <= 1) ->
         almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
         γ < 1 ->
         rv_eq (f 0%nat) (vecrvconst (S N) C) ->
         (forall n, rv_eq (f (S n))
                      (vecrvplus 
                         (vecrvmult (vecrvminus (vecrvconst (S N) 1) (α n)) 
                            (f n))
                         (vecrvscale (γ * C) (α n)))) ->
         (exists n0, almost prts (fun ω => forall n,
                          rvmaxabs (X (n + n0)%nat) ω <= rvmaxabs (f n) ω)) ->
         forall (eps1 eps2:posreal),
           γ + (1 - γ)/2 <= / (1 + eps1) ->
           eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps1))))) >= 1 - eps2).
       Proof.
         intros.
         assert (0 <= γ * C).
         {
           apply Rmult_le_pos; left; apply cond_pos.
         }
         apply lemma3_helper_vector_forall_almost_eventually_le with (f := f) (fstar := vector_const (γ * C) (S N)) (gamma := γ); trivial.
         - intros.
           revert H; apply almost_impl.
           revert H0; apply almost_impl.
           apply all_almost; intros ???.
           rewrite vector_nth_const.
           apply (lemma3_helper_iter_conv2 (fun n => vector_nth i pf (f n x))
                    (fun n => vector_nth i pf (α n x))); trivial.
           intros.
           rewrite H3.
           unfold vecrvminus, vecrvmult, vecrvplus, vecrvconst, vecrvopp, vecrvscale.
           rewrite Rvector_nth_plus, Rvector_nth_mult.
           rewrite Rvector_nth_plus, Rvector_nth_scale, vector_nth_const.
           rewrite Rvector_nth_scale.
           lra.
         - destruct H4.
           exists x.
           apply forall_almost.
           revert H4; apply almost_impl.
           apply all_almost; intros ??.
           now unfold pre_inter_of_collection.
         - rewrite Rvector_max_abs_const, Rabs_right; lra.
    Qed.

       Lemma vecrvclip_le (f : Ts -> vector R (S N)) (C : nonnegreal) :
         forall i pf ω,
           Rabs (vector_nth i pf (vecrvclip (S N) f C ω)) <=
             Rabs (vector_nth i pf (f ω)).
       Proof.
         intros.
         unfold vecrvclip.
         match_destr; try lra.
         assert (Rabs (C / Rvector_max_abs (f ω)) <= 1).
         {
           apply Rgt_lt in r.
           assert (0 < Rvector_max_abs (f ω)).
           {
             apply Rle_lt_trans with (r2 := C); trivial.
             apply cond_nonneg.
           }
           rewrite Rabs_right.
           - unfold Rdiv.
             left.
             apply Rmult_lt_reg_r with (r := Rvector_max_abs (f ω)); trivial.
             apply Rle_lt_trans with (r2 := C); try lra.
             rewrite Rmult_assoc, Rinv_l; lra.
           - apply Rle_ge.
             apply Rmult_le_reg_r with (r := Rvector_max_abs (f ω)); trivial.
             unfold Rdiv.
             rewrite Rmult_0_l, Rmult_assoc, Rinv_l; try lra.
             rewrite Rmult_1_r.
             apply cond_nonneg.
         }
         replace (Rabs (vector_nth i pf (f ω))) with (1 * Rabs (vector_nth i pf (f ω))) by lra.
         rewrite Rvector_nth_scale, Rabs_mult.
         apply Rmult_le_compat_r; trivial.
         apply Rabs_pos.
       Qed.


       Lemma lemma3_vector_forall_eventually_alt_almost (α β X : nat -> Ts -> vector R (S N)) (C C0 γ : posreal)
         (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n))
         (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) :
         almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
         almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
         almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

         almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->

         γ < 1 ->

         (forall n, rv_eq (X (S n))
                      (vecrvclip (S N)
                         (vecrvplus 
                            (vecrvminus (X n)
                               (vecrvmult (α n) (X n)))
                            (vecrvscalerv (rvmaxabs (X n))
                               (vecrvscale γ (β n))))
                         (pos_to_nneg C0))) ->
         eventually (fun n => rv_le (rvmaxabs (X n)) (const C)) ->
         forall (eps1 eps2:posreal),
           γ + (1 - γ)/2 <= / (1 + eps1) ->
           eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps1))))) >= 1 - eps2).
     Proof.
       intros aprop bprop abprop gamma_div gamma_lt1 Xprop Yprop eps1 eps2 eps1_prop.
       destruct Yprop as [nY Yprop].
       pose (f := fix f nn :=
          match nn with
                | 0%nat => vecrvconst (S N) C
                | S n =>
                    (vecrvplus 
                       (vecrvmult (vecrvminus (vecrvconst (S N) 1) (α (n + nY)%nat)) 
                          (f n))
                       (vecrvscale (γ * C) (α (n + nY)%nat)))
          end).
       generalize (lemma3_vector_forall_eventually_almost (fun n => α (n + nY)%nat) X f C γ rvX); intros.
       assert (rvf : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (f n)).
         {
           intros.
           induction n.
           - simpl.
             apply rvconst.
           - simpl.
             apply Rvector_plus_rv.
             + apply Rvector_mult_rv; trivial.
               apply Rvector_minus_rv.
               * apply rvconst.
               * apply rva.
             + apply Rvector_scale_rv.
               apply rva.
         }
         specialize (H rvf).
         apply H; trivial.
         - revert aprop; apply almost_impl.
           apply all_almost; intros ?????.
           apply H0.
         - revert gamma_div; apply almost_impl.
           apply all_almost; intros ????.
           specialize (H0 i pf).
           apply (seq_sum_shift (fun n => vector_nth i pf (α n x)) nY).
           apply H0.
         - now simpl.
         - intros.
           now simpl.
         - exists nY.
           apply almost_forall.
           intros.
           revert aprop; apply almost_impl.
           revert bprop; apply almost_impl.
           revert abprop; apply almost_impl.
           apply all_almost; intros ? abprop bprop aprop.
           apply Rvector_max_abs_le.
           induction n.
           + intros.
             simpl.
             unfold vecrvconst.
             rewrite vector_nth_const.
             generalize (cond_pos C); intros.
             rewrite (Rabs_right C); try lra.
             eapply Rle_trans.
             apply Rvector_max_abs_nth_le.
             now apply Yprop.
           + intros.
             replace (S n + nY)%nat with (S (n + nY)) by lia.
             rewrite Xprop.
             eapply Rle_trans.
             apply vecrvclip_le.
             assert (forall n i pf, (vector_nth i pf (f n x)) >= 0).
             {
               intros.
               induction n0.
               - simpl.
                 unfold vecrvconst.
                 rewrite vector_nth_const.
                 generalize (cond_pos C); lra.
               - simpl.
                 unfold vecrvplus, vecrvmult, vecrvminus, vecrvconst, vecrvopp, vecrvscale.
                 rewrite Rvector_nth_plus.
                 apply Rle_ge.
                 apply Rplus_le_le_0_compat.
                 + rewrite Rvector_nth_mult.
                   apply Rmult_le_pos; try lra.
                   unfold vecrvplus.
                   rewrite Rvector_nth_plus.
                   rewrite vector_nth_const.
                   rewrite Rvector_nth_scale.
                   specialize (aprop (n0 + nY)%nat i0 pf0).
                   lra.
                 + rewrite Rvector_nth_scale.
                   apply Rmult_le_pos.
                   * apply Rmult_le_pos.
                     generalize (cond_pos γ); lra.
                     generalize (cond_pos C); lra.                     
                   * apply aprop.
             }
             rewrite (Rabs_right (vector_nth i pf (f (S n) x))); [|apply H0].
             simpl.
             unfold vecrvplus.
             repeat rewrite Rvector_nth_plus.
             eapply Rle_trans.
             apply Rabs_triang.
             apply Rplus_le_compat.
             * unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vecrvmult, vecrvconst.
               rewrite Rvector_nth_plus.
               rewrite Rvector_nth_scale, Rvector_nth_mult.
               rewrite Rvector_nth_mult, Rvector_nth_plus, Rvector_nth_scale.
               rewrite vector_nth_const.
               replace (vector_nth i pf (X (n + nY)%nat x) +
                        -1 * (vector_nth i pf (α (n + nY)%nat x) * vector_nth i pf (X (n + nY)%nat x)))
                 with
                 ((1 + -1 * vector_nth i pf (α (n + nY)%nat x)) * vector_nth i pf (X (n + nY)%nat x)) by lra.
               rewrite Rabs_mult.
               assert (0 <=  (1 + -1 * vector_nth i pf (α (n + nY)%nat x))).
               {
                 specialize (aprop (n + nY)%nat i pf).
                 lra.
               }
               apply Rle_ge in H1.
               rewrite (Rabs_right _ H1).
               apply Rmult_le_compat_l; try lra.
               eapply Rle_trans.
               apply IHn.
               rewrite Rabs_right; [|apply H0].
               lra.
             * unfold vecrvscalerv.
               unfold vecrvscale.
               repeat rewrite Rvector_nth_scale.
               replace (Rabs (rvmaxabs (X (n + nY)%nat) x * (γ * vector_nth i pf (β (n + nY)%nat x)))) with
                 (γ * (Rabs (rvmaxabs (X (n + nY)%nat) x) * (vector_nth i pf (β (n + nY)%nat x)))).
               -- rewrite Rmult_assoc.
                  apply Rmult_le_compat_l.
                  ++ generalize (cond_pos γ); lra.
                  ++ apply Rmult_le_compat.
                     ** apply Rabs_pos.
                     ** apply bprop.
                     ** unfold rvmaxabs.
                        rewrite Rabs_right.
                        --- apply Yprop; try lia.
                        --- apply Rle_ge.
                            apply Rvector_max_abs_nonneg.
                     ** apply abprop.
               -- unfold rvmaxabs.
                  simpl.
                  rewrite Rabs_mult.
                  rewrite Rabs_mult.
                  generalize (cond_pos γ); intros.
                  rewrite (Rabs_right γ); try lra.
                  rewrite (Rabs_right  (vector_nth i pf (β (n + nY)%nat x))); try lra.
                  apply Rle_ge.
                  apply bprop.
        Qed.
     
End newN.
Section jaakola_vector2.

  Context {Ts : Type} {SS:Type} (N:nat)
    {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

 Lemma rvmaxabs_vecrvclip (X : Ts -> vector R (S N)) (C : nonnegreal) :
     rv_le 
       (rvmaxabs (vecrvclip (S N) X C))
       (const C).
   Proof.
     intros ?.
     unfold rvmaxabs, const, vecrvclip.
     match_destr; try lra.
     rewrite Rvector_max_abs_scale.
     generalize (cond_nonneg C); intros.
     rewrite Rabs_right.
     - unfold Rdiv.
       rewrite Rmult_assoc.
       rewrite Rinv_l; lra.
     - apply Rle_ge.
       apply Rdiv_le_0_compat; lra.
   Qed.

  Lemma lemma3_vector_forall_eventually_cond_prob_almost (α β X : nat -> Ts -> vector R (S N)) (C C0 γ : posreal)
        (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n))
        (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n))        
        (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) :
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

        almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
        γ < 1 ->
        (forall n, rv_eq (X (S n))
                         (vecrvclip (S N)
                            (vecrvplus 
                               (vecrvminus (X n)
                                  (vecrvmult (α n) (X n)))
                               (vecrvscalerv (rvmaxabs (X n))
                                  (vecrvscale γ (β n))))
                            (pos_to_nneg C0))) ->
         forall (eps1 eps2 prob:posreal),
           forall (nY : nat),
             γ + (1 - γ)/2 <= / (1 + eps1) ->
             1 - eps2 > 0 ->
             0 < ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + nY)%nat)) C))) ->
             eventually (fun n0 => cond_prob prts (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps1)))))
                                   (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + nY)%nat)) C)))
                                 >= 1 - eps2).
       Proof.
         intros aprop bprop abprop gamma_div gamma_lt1 Xprop  eps1 eps2 prob nY eps1_prop eps2_prop Yprop.
         pose (re:= (inter_of_collection (fun n0 : nat => event_le dom (rvmaxabs (X (n0 + nY)%nat)) C))).
         assert (rvα':(forall n : nat,
                           RandomVariable
                             (event_restricted_sigma
                                re) (Rvector_borel_sa (S N))
                             (event_restricted_function re (α n))) ).
         {
           intros.
           now apply Restricted_RandomVariable.
         }
         assert (rvX':(forall n : nat,
                           RandomVariable
                             (event_restricted_sigma
                                re) (Rvector_borel_sa (S N))
                             (event_restricted_function re (X n))) ).
         {
           intros.
           now apply Restricted_RandomVariable.
         }
         assert (rvY':(forall n : nat,
                           RandomVariable
                             (event_restricted_sigma
                                re) borel_sa
                             (event_restricted_function re (rvmaxabs (X n))) )).
         {
           intros.
           apply Restricted_RandomVariable.
           now apply Rvector_max_abs_rv.
         }
         generalize (lemma3_vector_forall_eventually_alt_almost  (prts:=event_restricted_prob_space prts _ Yprop) N
                       (fun n => event_restricted_function re (α n))
                       (fun n => event_restricted_function re (β n))
                       (fun n => event_restricted_function re (X n)) C C0 γ rvα' rvX'); intros HH.
         cut_to HH; trivial.
         - specialize (HH eps1 eps2 eps1_prop).
           destruct HH.
           exists (x + nY)%nat.
           intros.
           specialize (H n).
           cut_to H; try lia.
           rewrite event_restricted_cond_prob with (pf := Yprop).
           eapply Rge_trans; [| apply H].
           right.
           apply ps_proper; intros ?.
           reflexivity.
         - apply (almost_prob_space_event_restricted _ _ Yprop) in aprop.
           revert aprop.
           apply almost_impl.
           apply all_almost.
           intros ???.
           unfold event_restricted_function in H.
           apply H.
         - apply (almost_prob_space_event_restricted _ _ Yprop) in bprop.
           revert bprop.
           apply almost_impl.
           apply all_almost.
           intros ???.
           unfold event_restricted_function in H.
           apply H.
         - apply (almost_prob_space_event_restricted _ _ Yprop) in abprop.
           revert abprop.
           apply almost_impl.
           apply all_almost.
           intros ???.
           unfold event_restricted_function in H.
           apply H.
         - apply (almost_prob_space_event_restricted _ _ Yprop) in gamma_div.
           revert gamma_div.
           apply almost_impl.
           apply all_almost.
           intros ???.
           unfold event_restricted_function in H.
           apply H.
         - intros ??.
           unfold event_restricted_function.
           rewrite Xprop.
           reflexivity.
         - exists nY; intros nn Nn [xx xxP]; simpl.
           unfold rvmaxabs, event_restricted_function, const; simpl.
           red in xxP; simpl in xxP.
           specialize (xxP (nn-nY)%nat).
           replace (nn - nY + nY)%nat with nn in xxP by lia.
           unfold rvabs in xxP.
           apply xxP.
      Qed.

      Lemma lemma3_vector_forall_eventually_prob_inter_almost (α β X : nat -> Ts -> vector R (S N)) (C C0 γ : posreal)
        (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n))
        (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n))        
        (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) :
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

        almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
        γ < 1 ->
        (forall n, rv_eq (X (S n))
                         (vecrvclip (S N)
                            (vecrvplus 
                               (vecrvminus (X n)
                                  (vecrvmult (α n) (X n)))
                               (vecrvscalerv (rvmaxabs (X n))
                                  (vecrvscale γ (β n))))
                            (pos_to_nneg C0))) ->
         forall (eps1 eps2 prob:posreal),
           forall (nY : nat),
             γ + (1 - γ)/2 <= / (1 + eps1) ->
             1 - eps2 > 0 ->

             ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + nY)%nat)) C))) >= prob ->
             eventually (fun n0 => ps_P (event_inter 
                                           (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps1)))))
                                           (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + nY)%nat)) C))) ) >= prob * (1 - eps2)).
      Proof.
        intros aprop bprop abprop gamma_div gamma_lt1 Xprop eps1 eps2 prob nY eps1_prop eps2_prop Yprop.
        assert (0 < ps_P (inter_of_collection (fun n : nat => event_le dom (rvmaxabs (X (n + nY)%nat)) C))).
        {
          generalize (cond_pos prob); lra.
        }
        generalize (lemma3_vector_forall_eventually_cond_prob_almost α β X C C0 γ _ _ _ aprop bprop abprop gamma_div gamma_lt1 Xprop eps1 eps2 prob nY eps1_prop eps2_prop H); intros.
        destruct H0.
        exists (x + nY)%nat.
        intros.
        specialize (H0 n).
        cut_to H0; try lia.
        rewrite ps_inter_cond_prob_r; try lra.
        rewrite Rmult_comm.
        apply Rmult_ge_compat; trivial.
        - left.
          apply cond_pos.
        - generalize (cond_pos prob); lra.
      Qed.

      Lemma lemma3_vector_forall_eventually_prob_almost (α β X : nat -> Ts -> vector R (S N)) (C C0 γ : posreal)
        (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n))
        (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n))        
        (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) :
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

        almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
        γ < 1 ->
        (forall n, rv_eq (X (S n))
                         (vecrvclip (S N)
                            (vecrvplus 
                               (vecrvminus (X n)
                                  (vecrvmult (α n) (X n)))
                               (vecrvscalerv (rvmaxabs (X n))
                                  (vecrvscale γ (β n))))
                            (pos_to_nneg C0))) ->
         forall (eps1 eps2 prob:posreal),
           γ + (1 - γ)/2 <= / (1 + eps1) ->
           1 - eps2 > 0 ->
           eventually (fun nY => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + nY)%nat)) C))) >= prob) ->
           eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps1))))) >= prob * (1 - eps2)).
      Proof.
        intros aprop bprop abprop gamma_div gamma_lt1 Xprop eps1 eps2 prob eps1_prop eps2_prop Yprop.
        destruct Yprop as [nY Yprop].
        specialize (Yprop nY).
        cut_to Yprop; try lia.
        generalize (lemma3_vector_forall_eventually_prob_inter_almost α β X C C0 γ _ _ _ aprop bprop abprop gamma_div gamma_lt1 Xprop eps1 eps2 prob nY eps1_prop eps2_prop Yprop); intros.
        destruct H.
        exists x.
        intros.
        specialize (H n H0).
        eapply Rge_trans; cycle 1.
        apply H.
        apply Rle_ge.
        apply ps_sub.
        apply Event.event_inter_sub_l.
     Qed.

      Lemma lemma3_vector_forall_eventually_prob_iter_almost (α β X : nat -> Ts -> vector R (S N)) (C γ : posreal)
        (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n))
        (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n))        
        (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) :
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

        almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
           γ < 1 ->
        (forall n, rv_le (rvmaxabs (X n)) (const C)) ->
        (forall n, rv_eq (X (S n))
                         (vecrvclip (S N)
                            (vecrvplus 
                               (vecrvminus (X n)
                                  (vecrvmult (α n) (X n)))
                               (vecrvscalerv (rvmaxabs (X n))
                                  (vecrvscale γ (β n))))
                            (pos_to_nneg C))) ->
        forall (eps1 : posreal),
               forall (eps2:nat -> posreal),
               forall (k : nat),
                 γ + (1 - γ)/2 <= / (1 + eps1) ->
                 (forall n, 1 - eps2 n > 0) ->
                 eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps1)^k)))) >= prod_f_R0 (fun n => (1 - eps2 n)) k).
      Proof.
        intros aprop bprop abprop gamma_div gamma_lt1 Xbound Xprop eps1 eps2 k eps1_prop eps2_prop.
        induction k.
        - apply all_eventually.
          intros.
          simpl.
          rewrite Rdiv_1.
          assert (1 >= 1 - eps2 0%nat).
          {
            generalize (cond_pos (eps2 0%nat)).
            lra.
          }
          eapply Rge_trans; cycle 1.
          apply H.
          right.
          apply ps_one_countable_inter.
          intros.
          replace 1 with R1 by lra.
          rewrite <- ps_one.
          apply ps_proper.
          intros ?.
          simpl.
          unfold pre_Ω.
          specialize (Xbound (n + x)%nat x0).
          unfold const in Xbound.
          tauto.
        - assert (0 < C/(1+eps1)^k).
          {
            apply Rdiv_lt_0_compat.
            apply cond_pos.
            apply pow_lt.
            generalize (cond_pos eps1).
            lra.
          }
          generalize (lemma3_vector_forall_eventually_prob_almost α β X (mkposreal _ H) C γ _ _ _ aprop bprop abprop gamma_div gamma_lt1 Xprop eps1 (eps2 (S k))); intros.
          assert (0 < prod_f_R0 (fun n => (1 - eps2 n)) k).
          {
            clear H H0 IHk.
            induction k.
            - simpl.
              apply eps2_prop.
            - simpl.
              apply Rmult_lt_0_compat; trivial.
              apply eps2_prop.
          }
          specialize (H0 (mkposreal _ H1) eps1_prop (eps2_prop (S k))); intros.
          rewrite Rmult_comm in H0.
          cut_to H0.
          + destruct H0.
            exists x.
            intros.
            specialize (H0 n H2).
            simpl in H0.
            simpl.
            rewrite Rmult_comm in H0.
            eapply Rge_trans; cycle 1.
            apply H0.
            right.
            apply ps_proper.
            intros ?.
            simpl.
            replace  (C / (1 + eps1) ^ k / (1 + eps1)) with
              (C / ((1 + eps1) * (1 + eps1) ^ k)); [tauto | ].
            rewrite Rmult_comm.
            unfold Rdiv.
            rewrite Rmult_assoc.
            now rewrite Rinv_mult.
          + destruct IHk.
            exists x.
            intros.
            specialize (H2 n H3).
            simpl.
            eapply Rge_trans; cycle 1.
            apply H2.
            now right.
      Qed.

      Lemma lemma3_vector_forall_eventually_prob_iter_alt_almost (α β X : nat -> Ts -> vector R (S N)) (C γ : posreal)
        (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n))
        (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n))        
        (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) :
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
        almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

        almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
        γ < 1 ->
        (forall n, rv_le (rvmaxabs (X n)) (const C)) ->
        (forall n, rv_eq (X (S n))
                         (vecrvclip (S N)
                            (vecrvplus 
                               (vecrvminus (X n)
                                  (vecrvmult (α n) (X n)))
                               (vecrvscalerv (rvmaxabs (X n))
                                  (vecrvscale γ (β n))))
                            (pos_to_nneg C))) ->
        forall (eps1 : posreal),
               forall (eps2:nat -> posreal),
                 γ + (1 - γ)/2 <= / (1 + eps1) ->
                 (forall n, 1 - eps2 n > 0) ->
                 forall (k : nat),
                   eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps1)^k)))) >= prod_f_R0 (fun n => (1 - eps2 n)) k).
        Proof.
          intros.
          now apply (lemma3_vector_forall_eventually_prob_iter_almost α β) with (γ := γ).
        Qed.

        Lemma eps_pos_eventually (C eps eps0: posreal) :
          eventually (fun k => C / (1 + eps)^k < eps0).
        Proof.
          generalize (lemma3_lim_eps_alt C eps); intros.          
          assert (lim_C_eps1: is_lim_seq (fun n => C / (1 + eps)^n) 0).
          {
            revert H.
            apply is_lim_seq_ext.
            intros.
            unfold Rdiv.
            now rewrite pow_inv.
          }
          apply is_lim_seq_spec in lim_C_eps1.
          specialize (lim_C_eps1 eps0).
          revert lim_C_eps1.
          apply eventually_impl.
          apply all_eventually.
          intros.
          rewrite Rminus_0_r in H0.
          rewrite Rabs_right in H0; trivial.
          apply Rle_ge.
          apply Rdiv_le_0_compat.
          - left; apply cond_pos.
          - apply pow_lt.
            generalize (cond_pos eps); lra.
      Qed.

        Lemma is_lim_seq_eventually_0 (f : nat -> posreal)  (C eps : posreal) :
          (forall (k : nat),
              eventually (fun n0 =>  f (n0) <= C / (1 + eps)^k)) ->
          is_lim_seq f 0.
        Proof.
          intros.
          apply is_lim_seq_spec.
          intros ?.
          generalize (eps_pos_eventually C eps eps0); intros.
          destruct H0.
          specialize (H x).
          specialize (H0 x).
          cut_to H0; try lia.
          revert H.
          apply eventually_impl.
          apply all_eventually.
          intros.
          rewrite Rminus_0_r.
          rewrite Rabs_right.
          - eapply Rle_lt_trans.
            apply H.
            apply H0.
          - left.
            apply cond_pos.
       Qed.

       Lemma lemma3_plim0 :
         filterlim (fun y => real (Lim_seq (fun m => prod_f_R0 (fun n => 1 - (Rabs y) ^ S n) m)))
           (at_right 0) (Rbar_locally 1).
       Proof.
         generalize lemma3_plim_Rabs.
         apply filterlim_right.
       Qed.

       Lemma lemma3_plim1 :
         filterlim (fun y => real (Lim_seq (fun m => prod_f_R0 (fun n => 1 - (Rabs y) ^ S n) m)))
           (at_right 0) (locally 1).
       Proof.
         generalize lemma3_plim0.
         apply filterlim_filter_le_2.         
         apply filter_le_refl.
       Qed.

       Lemma lemma3_plim :
         filterlim (fun y => (lift_posreal_f (fun (yy : posreal) => real (Lim_seq (fun m => prod_f_R0 (fun n => 1 - yy ^ S n) m))) 0) y)
           (at_right 0) (locally 1).
       Proof.
         generalize lemma3_plim1.
         apply filterlim_within_ext.
         intros.
         unfold lift_posreal_f.
         match_destr; try lra.
         f_equal.
         apply Lim_seq_ext.
         intros.
         apply prod_f_R0_proper; trivial.
         intros ?.
         f_equal.
         f_equal.
         rewrite Rabs_right; trivial.
         lra.
       Qed.

       Lemma lemma3_plim_pos :
         is_lim_pos (fun (y : posreal) => real (Lim_seq (fun m => prod_f_R0 (fun n => 1 - y ^ S n) m))) 1.
       Proof.
         apply lemma3_plim.
       Qed.

      Lemma lemma3_almost (α β X : nat -> Ts -> vector R (S N)) (C γ : posreal)
         (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) 
         (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n)) 
         (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n)) :           
         almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
         almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
         almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

         almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
         γ < 1 ->
         (forall n, rv_le (rvmaxabs (X n)) (const C)) ->
         (forall n, rv_eq (X (S n))
                      (vecrvclip (S N)
                         (vecrvplus 
                            (vecrvminus (X n)
                               (vecrvmult (α n) (X n)))
                            (vecrvscalerv (rvmaxabs (X n))
                               (vecrvscale γ (β n))))
                         (pos_to_nneg C))) ->
         almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
      Proof.
        intros.
        generalize (lemma3_vector_forall_eventually_prob_iter_alt_almost α β X C γ _ _ _); intros.
        cut_to H6; trivial.
        destruct (lemma3_gamma_eps_le _ H3) as [eps1 eps1_prop].
        generalize (lemma3_lim_eps_alt C eps1); intros.
        assert (lim_C_eps1: is_lim_seq (fun n => C / (1 + eps1)^n) 0).
        {
          revert H7.
          apply is_lim_seq_ext.
          intros.
          unfold Rdiv.
          now rewrite pow_inv.
        }
        assert (eps_pow : forall (eps : posreal) (n : nat),
                   0 < eps ^ n).
        {
          intros.
          apply pow_lt.
          apply cond_pos.
        }
        pose (eps2' := fun (eps : posreal) (n : nat) => mkposreal _ (eps_pow eps (S n))).
        assert (lim_0_1': is_lim_pos (fun (y : posreal) => real (Lim_seq (fun m => prod_f_R0 (fun n => 1 - eps2' y n) m))) 1).
        {
          apply lemma3_plim_pos.
        }
        assert (exists (eps : posreal),
                 forall (eps' : posreal),
                   eps' <= eps ->
                   (γ + (1 - γ) / 2 <= / (1 + eps')) /\
                     (forall n, 1 - eps2' eps' n > 0)).
        {
          assert (0 < Rmin eps1 (1/2)).
          {
            apply Rgt_lt.
            apply Rmin_Rgt_r.
            split; try lra.
            apply cond_pos.
          }
          exists (mkposreal _ H8).
          intros.
          split.
          - eapply Rle_trans.
            apply eps1_prop.
            apply Rinv_le_contravar.
            + simpl.
              generalize (cond_pos eps'); lra.
            + apply Rplus_le_compat_l.
              eapply Rle_trans.
              apply H9.
              apply Rmin_l.
          - intros.
            unfold eps2'.
            induction n.
            + simpl.
              rewrite Rmult_1_r.
              assert (eps' <= 1/2).
              {
                eapply Rle_trans.
                apply H9.
                apply Rmin_r.
              }
              lra.
           + simpl.
             simpl in IHn.
             assert (eps' * (eps' * eps' ^ n) <=  1 * (eps' * eps' ^ n)).
             {
               generalize (cond_pos eps'); intros.
               apply Rmult_le_compat_r.
               - apply Rmult_le_pos; try lra.
                 apply pow_le.
                 lra.
               - eapply Rle_trans.
                 apply H9.
                 eapply Rle_trans with (r2 := 1/2); try lra.
                 apply Rmin_r.
             }
             lra.
        }
        destruct H8 as [eps eps_prop].
        assert (inter_prod : forall (eps' : posreal),
                   eps' <= eps ->
                   forall k : nat,
                     eventually
                       (fun n0 : nat =>
                          ps_P
                            (inter_of_collection
                               (fun n : nat =>
                                  event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps') ^ k))) >=
                            prod_f_R0 (fun n : nat => 1 - eps2' eps' n) k)).
        {
          intros.
          specialize (H6 eps' (eps2' eps')).
          apply H6; now apply eps_prop.
        }

        assert (esub_eventually : forall (eps : posreal) k,
                   event_sub
                     (event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps) ^ (S k))))
                     (event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps) ^ k)))).
        {
          intros ???.
          simpl.
          apply eventually_impl.
          apply all_eventually.
          intros.
          eapply Rle_trans.
          apply H8.
          unfold Rdiv.
          apply Rmult_le_compat_l.
          - left.
            apply cond_pos.
          - generalize (cond_pos eps0); intros.
            apply Rinv_le_contravar.
            + apply pow_lt; lra.
            + rewrite <- (Rmult_1_l ((1 + eps0)^k)) at 1.
              apply Rmult_le_compat_r; try lra.
              apply pow_le; lra.
        }
        assert (inter_prod_eventually :
                  forall eps' : posreal,
                    eps' <= eps ->
                    forall k : nat,
                      ps_P
                        (event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps') ^ k))) >=
                        prod_f_R0 (fun n : nat => 1 - eps2' eps' n) k).
        {
          intros.
          specialize (inter_prod eps' H8 k).
          destruct inter_prod as [n0 inter_prod].
          assert (event_sub
                    (inter_of_collection (fun n : nat => event_le dom (rvmaxabs (X (n0 + n)%nat)) (C / (1 + eps') ^ k)))
                    (event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps') ^ k)))).
          {
            generalize (event_sub_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps') ^ k)) n0) ; intros.
            apply H9.
          }
          specialize (inter_prod n0).
          cut_to inter_prod; try lia.
          eapply Rge_trans; cycle 1.
          apply inter_prod.
          apply Rle_ge.
          apply ps_sub.
          assert (event_equiv (inter_of_collection (fun n : nat => event_le dom (rvmaxabs (X (n + n0)%nat)) (C / (1 + eps') ^ k)))
                    (inter_of_collection (fun n : nat => event_le dom (rvmaxabs (X (n0 + n)%nat)) (C / (1 + eps') ^ k)))).
          {
            apply inter_of_collection_proper.
            intros ?.
            now replace (n0 + a)%nat with (a + n0)%nat by lia.
          }
          rewrite H10.
          apply H9.
        }
        assert (rv_rvmaxabs: forall n,
                   RandomVariable dom Rbar_borel_sa (rvmaxabs (X n))).
        {
          intros.
          apply Real_Rbar_rv.
          now apply Rvector_max_abs_rv.
        }
       pose (is_lim_event :=
                     (event_inter (event_ex_Elim_seq (fun n => rvmaxabs (X n)) rv_rvmaxabs)
                                   (preimage_singleton (has_pre := Rbar_borel_has_preimages)
                        (Rbar_rvlim (fun n => rvmaxabs (X n))) (Finite 0)))).


       assert (eesub_eventually_is_limseq: forall eps : posreal,
                   event_sub
                     (inter_of_collection 
                        (fun k => (event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps) ^ k)))))
                     is_lim_event).
        {
          intros ??.
          simpl.
          intros.
          unfold pre_event_inter, pre_event_preimage.
          unfold pre_event_preimage, pre_event_singleton, Rbar_rvlim.
          rewrite ex_Elim_seq_fin, Elim_seq_fin.
          assert (is_lim_seq (fun x0 : nat => rvmaxabs (X x0) x) 0).
          {
            rewrite <- is_lim_seq_spec.
            intros ?.
            assert (eventually (fun n => C / (1 + eps0) ^ n < eps2)).
            {
              generalize (lemma3_lim_eps_alt C eps0); intros.
              assert (is_lim_seq (fun n => C / (1 + eps0)^n) 0).
              {
                revert H9.
                apply is_lim_seq_ext.
                intros.
                unfold Rdiv.
                now rewrite pow_inv.
              }
              apply is_lim_seq_spec in H10.
              specialize (H10 eps2).
              simpl in H10.
              revert H10.
              apply eventually_impl.
              apply all_eventually.
              intros.
              rewrite Rminus_0_r in H10.
              rewrite Rabs_right in H10; trivial.
              apply Rle_ge.
              apply Rdiv_le_0_compat.
              - generalize (cond_pos C); lra.
              - apply pow_lt.
                generalize (cond_pos eps0); lra.
            }
            destruct H9.
            specialize (H9 x0).
            cut_to H9; try lia.
            specialize (H8 x0).
            revert H8.
            apply eventually_impl.
            apply all_eventually.
            intros ??.
            rewrite Rminus_0_r.
            unfold rvmaxabs.
            rewrite Rabs_Rvector_max_abs.
            eapply Rle_lt_trans; cycle 1.
            apply H9.
            apply H8.
          }
          split.
          - now exists 0.
          - now apply is_lim_seq_unique.
        }
        assert (ps_P_le_eventually : forall (eps : posreal),
                   ps_P (inter_of_collection
                          (fun k : nat =>
                             event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps) ^ k)))) <=
                     ps_P is_lim_event).
        {
          intros.
          now apply ps_sub.
        }
        assert (is_lim_seq_ps_P :
                 forall eps : posreal,
                   is_lim_seq 
                     (fun k => ps_P
                                 (event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps) ^ k))))
                     (ps_P (inter_of_collection
                              (fun k : nat =>
                                 event_eventually (fun n : nat => event_le dom (rvmaxabs (X n)) (C / (1 + eps) ^ k)))))).
        {
          intros.
          apply lim_prob_descending.
          - intros.
            apply esub_eventually.
          - intros ?.
            simpl.
            tauto.
       }
        assert (forall (eps' : posreal),
                   eps' <= eps ->
                   is_finite (Lim_seq (fun m : nat => prod_f_R0 (fun n : nat => 1 - eps2' eps' n) m))).
          {
            intros.
            apply is_finite_Lim_bounded with (m := 0) (M := 1).
            intros.
            split.
            - apply prod_f_R0_nonneg.
              intros.
              specialize (eps_prop eps' H8).
              destruct eps_prop.
              specialize (H10 n0).
              lra.
            - apply prod_f_R0_le_1.
              intros.
              specialize (eps_prop eps' H8).
              destruct eps_prop.
              specialize (H10 n0).
              generalize (cond_pos (eps2' eps' n0)); intros.
              lra.
          }
          assert (forall (eps' : posreal),
                   eps' <= eps ->
                   Rbar_ge
                     (ps_P is_lim_event)
                     (Lim_seq (fun m : nat => prod_f_R0 (fun n : nat => 1 - eps2' eps' n) m))).
        {
          intros.
          specialize (inter_prod_eventually eps' H9).
          unfold Rbar_ge.
          specialize (ps_P_le_eventually eps').
          specialize (is_lim_seq_ps_P eps').
          apply is_lim_seq_unique in is_lim_seq_ps_P.
          assert (Rbar_ge 
                    (Lim_seq 
                       (fun k =>
                          (ps_P
                             (event_eventually
                                (fun n : nat =>
                                   event_le dom (rvmaxabs (X n)) (C / (1 + eps') ^ k))))))
                    (Lim_seq 
                       (fun k =>
                          (prod_f_R0 (fun n : nat => 1 - eps2' eps' n) k)))).
          {
            unfold Rbar_ge.
            apply Lim_seq_le.
            intros.
            apply Rge_le.
            apply inter_prod_eventually.
          }
          unfold Rbar_ge in H10.
          eapply Rbar_le_trans.
          apply H10.
          rewrite is_lim_seq_ps_P.
          apply ps_P_le_eventually.
        }
        assert (ps_P is_lim_event = 1).
        {
          generalize (ps_le1 _ is_lim_event); intros.
          assert (Rbar_ge (ps_P is_lim_event) 1).
          {
            unfold is_lim_pos in lim_0_1'.
            generalize (filterlim_const_at_right0
                          (ps_P is_lim_event)); intros.
            assert (ProperFilter' (at_right 0)).
            {
              apply Proper_StrongProper.
              apply at_right_proper_filter.
            }
            generalize (@filterlim_le R (at_right 0) H12); intros.
            unfold Rbar_ge.
            apply H13 with 
              (f := (fun y : R =>
                       lift_posreal_f
                         (fun y0 : posreal =>
                            Lim_seq
                              (fun m : nat => prod_f_R0 (fun n : nat => 1 - eps2' y0 n) m))
                         0 y))
              (g := (fun _ : R => ps_P is_lim_event)); trivial.
            unfold at_right, within.
            clear H11 H12 H13.
            unfold Rbar_ge in H9.
            assert (forall eps' : posreal,
                       eps' <= eps ->
                       (Lim_seq (fun m : nat => prod_f_R0 (fun n : nat => 1 - eps2' eps' n) m)) <=
                         (ps_P is_lim_event)).
            {
              intros.
              specialize (H8 eps' H11).
              specialize (H9 eps' H11).
              rewrite <- H8 in H9.
              now simpl in H9.
            }
            unfold locally.
            exists eps.
            intros.
            red in H12; simpl in H12.
            red in H12; simpl in H12.
            unfold abs, minus, plus, opp in H12.
            simpl in H12.
            replace (y + - 0) with y in H12 by lra.
            rewrite Rabs_right in H12; try lra.
            specialize (H11 (mkposreal y H13)).
            simpl in H11.
            cut_to H11; try lra.
            unfold eps2'.
            simpl.
            unfold lift_posreal_f.
            match_destr.
            lra.
          }
          simpl in H11.
          lra.
       }
       exists is_lim_event.
        split; trivial.
        intros.
        unfold preimage_singleton in H11.
        simpl in H11.
        unfold pre_event_preimage in H11.
        unfold pre_event_singleton in H11.
        unfold Rbar_rvlim in H11.
        unfold pre_event_inter in H11.
        rewrite Elim_seq_fin in H11.
        rewrite ex_Elim_seq_fin in H11.
        destruct H11.
        apply Lim_seq_correct in H11.
        now rewrite H12 in H11.
   Qed.

 Lemma vecrvclip_choice {M} (f : Ts -> vector R M) (c : nonnegreal) :
   rv_eq (vecrvclip _ f c) (vecrvchoice (fun x => if Rgt_dec (Rvector_max_abs (f x)) c then true else false)
                              (fun x => Rvector_scale (c/Rvector_max_abs (f x)) (f x))
                              f).
 Proof.
   intros ?.
   unfold vecrvclip, vecrvchoice.
   match_destr.
 Qed.

 Lemma vecrvclip_rv (X : Ts -> vector R (S N)) (C : nonnegreal) :
   RandomVariable dom (Rvector_borel_sa (S N)) X ->
   RandomVariable dom (Rvector_borel_sa (S N)) (vecrvclip (S N) X C).
 Proof.
   intros.
   rewrite vecrvclip_choice.
   assert (rv_C: RandomVariable dom (discrete_sa bool)
                   (fun x : Ts => if Rgt_dec (Rvector_max_abs (X x)) C then true else false)).
   { Existing Instance FiniteRange_FiniteRangeFunction.
     apply (frf_singleton_rv _ _).
     intros [|] _; unfold pre_event_singleton, pre_event_singleton, pre_event_preimage; simpl.
     * apply sa_proper with
         (x := (fun ω => Rvector_max_abs (X ω) > C)).
       -- intros ?.
          now match_destr.
       -- apply sa_le_gt_rv.
          now apply Rvector_max_abs_rv.
     * apply sa_proper with
         (x := (fun ω => ~(Rvector_max_abs (X ω) > C))).               
       -- intros ?.
          now match_destr.
       -- apply sa_proper with
            (x := (fun ω => (Rvector_max_abs (X ω) <= C))).               
          ++ intros ?; lra.
          ++ apply sa_le_le_rv.
             now apply Rvector_max_abs_rv.
   } 
   apply (@vecrvchoiceb_restricted_rv _ _ _ _ _ _ rv_C); trivial.
   - apply RealVectorMeasurableRandomVariable; intros i pf; simpl.
     rewrite vector_nth_fun_to_vector.
     unfold Rvector_scale.
     eapply RealMeasurable_proper.
     {
       intro.
       unfold event_restricted_function, Rdiv.
       rewrite vector_nth_map, Rmult_assoc.
       reflexivity.
     }
     apply scale_measurable.
     apply mult_measurable.
     + intros ?.
       simpl.
       apply (sa_proper _ (fun a : Ts =>
                             C < Rvector_max_abs (X a) /\ / Rvector_max_abs (X a) <= r)).
       {
         intros ?.
         split; intros ?.
         - destruct H0.
           unfold event_restricted_domain.
           simpl.
           assert (Hpf:(if Rgt_dec (Rvector_max_abs (X x)) C then true else false) = true).
           {
             match_destr; lra.
           } 
           exists (exist _ x Hpf); simpl.
           tauto.
         - destruct H0 as [?[??]]; subst.
           destruct x0; simpl in *.
           match_destr_in e.
           lra.
       }
       assert (vmax_rv: RealMeasurable dom (fun a => Rvector_max_abs (X a))).
       {
         apply Rvector_max_abs_measurable.
         now apply RandomVariableRealVectorMeasurable.
       }
       destruct (Rlt_dec 0 r).
       { red in vmax_rv.
         generalize (sa_le_ge _ vmax_rv (/ r)); intros HH.
         apply (sa_proper _ (fun a : Ts => C < Rvector_max_abs (X a) /\ Rvector_max_abs (X a) >= / r)).
         {
           intros ?.
           rewrite <- (Rinv_inv r) at 2.
           intuition.
           - apply Rinv_le_contravar.
             + now apply Rinv_pos.
             + lra.
           - apply Rinv_le_cancel in H2.
             + lra.
             + eapply Rle_lt_trans; try apply H1.
               apply cond_nonneg.
         }
         apply sa_inter; trivial.
         apply event_Rgt_sa.
         - now apply measurable_rv.
         - apply rvconst.
       }
       apply (sa_proper _ event_none).
       * intros ?.
         split; [unfold event_none, pre_event_none; simpl; tauto |].
         intros [??].
         assert (r <= 0) by lra.
         {
           destruct (Req_dec C 0).
           - rewrite H3 in H0.
             apply Rinv_pos in H0.
             lra.
           - assert (0 < Rvector_max_abs (X x)).
             { eapply Rle_lt_trans; try apply H0.
               destruct C; simpl in *; lra.
             }
             assert (0 < / Rvector_max_abs (X x))
               by now apply Rinv_pos.
             lra.
         }
       * apply sa_none.
     + apply (RealMeasurable_proper _
                (fun a => event_restricted_function _ (fun a => vector_nth i pf (X a)) a)); try reflexivity.
       apply rv_measurable.
       apply Restricted_RandomVariable.
       apply (vec_rv _ _ pf) in H.
       revert H.
       apply RandomVariable_proper; try reflexivity.
       intros ?; simpl.
       now rewrite vector_nth_fun_to_vector.
   - now apply Restricted_RandomVariable.
 Qed.

 Lemma lemma3_full_almost (α β X : nat -> Ts -> vector R (S N)) (γ : posreal)
   (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) 
   (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n)) 
   (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n)) :           
   almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
   almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
   almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

   almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
   γ < 1 ->
   (forall n, rv_eq (X (S n))
                (vecrvplus 
                   (vecrvminus (X n)
                      (vecrvmult (α n) (X n)))
                   (vecrvscalerv (rvmaxabs (X n))
                      (vecrvscale γ (β n))))) ->
   almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
 Proof.
   intros.
   assert (0 < 1) by lra.
   pose (C := mkposreal 1 H5).
   pose (G := fun n ω Y =>
                Rvector_plus
                  (Rvector_plus Y
                     (Rvector_scale (-1)  (Rvector_mult (α n ω) Y)))
                  (Rvector_scale (γ * Rvector_max_abs Y)
                     (β n ω))).
   pose (XC := fix XC nn :=
           match nn with
           | 0%nat => vecrvclip (S N) (X 0%nat) (pos_to_nneg C)
           | S n =>
               vecrvclip (S N)
                 (vecrvplus 
                    (vecrvminus (XC n)
                       (vecrvmult (α n) (XC n)))
                    (vecrvscalerv (rvmaxabs (XC n))
                       (vecrvscale γ (β n))))
                 (pos_to_nneg C)
           end).
   generalize (lemma3_almost α β XC C γ); intros.
   cut_to H6; trivial.
   - apply (lemma2 (S N) X XC G C).
     + intros ??.
       rewrite H4.
       unfold G, vecrvminus, vecrvmult, vecrvscalerv, rvmaxabs.
       unfold vecrvplus, vecrvopp, vecrvscale.
       rewrite Rvector_scale_scale.
       now rewrite Rmult_comm.
     + intros ??.
       simpl.
       unfold G, vecrvminus, vecrvmult, vecrvscalerv, rvmaxabs.
       unfold vecrvplus, vecrvopp, vecrvscale.
       f_equal.
       apply functional_extensionality.
       intros.
       rewrite Rvector_scale_scale.
       now rewrite Rmult_comm.
     + simpl.
       reflexivity.
     + intros ???.
       unfold G.
       rewrite Rvector_scale_plus_l.
       rewrite Rvector_scale_plus_l.
       repeat rewrite (Rvector_scale_comm beta).
       rewrite Rvector_scale_mult_r.
       rewrite Rvector_max_abs_scale.
       repeat rewrite Rvector_scale_scale.
       generalize (cond_nonneg beta); intros.
       rewrite Rabs_right; try lra.
       rewrite (Rmult_comm beta).
       now rewrite Rmult_assoc.
     + intros ???.
       unfold G.
       rewrite Rvector_scale_plus_l.
       rewrite Rvector_scale_plus_l.
       repeat rewrite (Rvector_scale_comm beta).
       rewrite Rvector_scale_mult_r.
       rewrite Rvector_max_abs_scale.
       repeat rewrite Rvector_scale_scale.
       generalize (cond_nonneg beta); intros.
       rewrite Rabs_right; try lra.
       rewrite (Rmult_comm beta).
       now rewrite Rmult_assoc.
     + apply H6.
   - intros.
     induction n.
     + simpl.
       now apply vecrvclip_rv.
     + simpl.
       apply vecrvclip_rv.
       apply Rvector_plus_rv.
       * apply Rvector_minus_rv; trivial.
         now apply Rvector_mult_rv.
       * apply Rvector_scale_rv_rv.
         -- now apply Rvector_max_abs_rv.
         -- now apply Rvector_scale_rv.
   - intros.
     induction n; simpl; apply rvmaxabs_vecrvclip.
   - intros.
     now simpl.
 Qed.

 Lemma lemma3'_almost (α β X : nat -> Ts -> vector R (S N)) (C γ : posreal)
   (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) 
   (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n)) 
   (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n)) :           
   almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
   almost prts (fun ω => forall t i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
   almost prts (fun ω => forall t i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->       

   almost prts (fun ω => forall i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
   γ < 1 ->
   (forall n, rv_le (rvmaxabs (X n)) (const C)) ->
   (forall n, rv_eq (X (S n))
                (vecrvclip (S N)
                   (vecrvplus 
                      (vecrvminus (X n)
                         (vecrvmult (α n) (X n)))
                      (vecrvscalerv (rvmaxabs (X n))
                         (vecrvscale γ (β n))))
                   (pos_to_nneg C))) ->
   forall i pf,
     almost prts (fun ω => Lim_seq (fun n => vector_nth i pf (X n ω)) = 0).
 Proof.
   intros.
   generalize (lemma3_almost α β X C γ _ _ _ H H0 H1 H2 H3 H4 H5).
   apply almost_impl.
   apply all_almost.
   intros ??.
   apply is_lim_seq_unique in H6.
   assert (Lim_seq (fun n => - (rvmaxabs (X n) x)) = 0).
   {
     rewrite Lim_seq_opp, H6.
     simpl.
     now rewrite Ropp_0.
   }
   generalize (Lim_seq_le  (fun n : nat => - rvmaxabs (X n) x) (fun n : nat => vector_nth i pf (X n x))); intros.
   generalize (Lim_seq_le   (fun n : nat => vector_nth i pf (X n x)) (fun n : nat => rvmaxabs (X n) x)); intros.       
   assert (forall n, - rvmaxabs (X n) x <= vector_nth i pf (X n x) <=  rvmaxabs (X n) x).
   {
     intros.
     apply Rabs_le_between.
     apply Rvector_max_abs_nth_le.
   }
   rewrite H6 in H9.
   rewrite H7 in H8.
   cut_to H8.
   cut_to H9.
   - now apply Rbar_le_antisym.
   - intros.
     apply H10.
   - intros.
     apply H10.
 Qed.

 Lemma lemma3_counter_prob_choice (d1 d2 : R) :
   d1 > 1 ->
   d2 < 1 ->
   exists p, 0 < p < 1 /\ p * d1 + (1-p)*d2 = 1.
 Proof.
   exists ((1-d2)/(d1-d2)).
   split.
   - split.
     + apply Rdiv_lt_0_compat; lra.
     + rewrite <- Rdiv_lt_1; lra.
   - field_simplify; try lra.
     apply Rdiv_diag; lra.
 Qed.

 Lemma sum_n_Rscal_l (f : nat -> R) (c:R)  (n : nat):
   c * (sum_n f n)  = (sum_n (fun k => c * (f k)) n).
 Proof.
   induction n.
   - now do 2 rewrite sum_O.
   - do 2 rewrite sum_Sn.
     rewrite <- IHn.
     unfold plus; simpl.
     now ring.
 Qed.

 Lemma l1_divergent_scale (a : nat -> R) (d : posreal) :
   l1_divergent a ->
   l1_divergent (fun n => d * (a n)).
 Proof.
   unfold l1_divergent.
   intros.
   apply is_lim_seq_spec in H.
   apply is_lim_seq_spec.
   intros ?.
   specialize (H (M / d)).
   revert H.
   apply eventually_impl.
   apply all_eventually.
   intros.
   rewrite <- sum_n_Rscal_l.
   generalize (cond_pos d); intros.
   apply Rmult_lt_compat_r with (r := d) in H; try lra.
   unfold Rdiv in H.
   rewrite Rmult_assoc in H.
   rewrite Rinv_l in H; lra.
 Qed.

 Lemma isfe_beta  (α : R) (d1 d2 : R) (ev : event dom) :
   let β :=
     rvplus
       (rvscale (d1 * α)
          (EventIndicator (classic_dec ev)))
       (rvscale (d2 * α)
          (EventIndicator (classic_dec (event_complement ev)))) in
   IsFiniteExpectation prts β.
 Proof.
   intros.
   apply IsFiniteExpectation_plus.
   - apply rvscale_rv.
     apply EventIndicator_rv.
   - apply rvscale_rv.
     apply EventIndicator_rv.
   - apply IsFiniteExpectation_scale.
     apply ProductSpace.indicator_isfe.
   - apply IsFiniteExpectation_scale.
     apply ProductSpace.indicator_isfe.
 Qed.

 Lemma lemm3_counter_alpha :
   let α := fun n => / INR (S n) in
   (forall t, 0 <= α t <= 1) /\
     l1_divergent (fun n : nat => α n) /\
     ex_series (fun n : nat => Rsqr (α n)).
 Proof.
   split.
   - intros.
     split.
     + left.
       apply Rinv_0_lt_compat.
       apply lt_0_INR.
       lia.
     + replace 1 with (/ 1) by lra.
       apply Rinv_le_contravar; try lra.
       rewrite <- INR_1.
       apply le_INR.
       lia.
   - split.
     + unfold l1_divergent.
       generalize harmonic_series; intros.
       apply is_lim_seq_incr_1 in H.
       revert H.
       apply is_lim_seq_ext.
       intros.
       rewrite <- sum_f_R0_sum_f_R0', <- sum_n_Reals.
       apply sum_n_ext.
       intros.
       lra.
     + generalize (genharmonic_series_sq0 (mkposreal _ Rlt_0_1)).
       apply ex_series_ext.
       intros.
       f_equal; f_equal.
       simpl; lra.
 Qed.              

 Lemma lemma3_counter_example (α : nat -> R) (C : posreal) :
   (forall t, 0 <= α t <= 1) ->
   l1_divergent (fun n : nat => α n) ->
   ex_series (fun n : nat => Rsqr (α n)) ->        
   (exists (ev : event dom), 0 < ps_P ev <= 0.5) ->
   exists (β X : nat -> Ts -> R),
   exists (isfeβ : forall t, IsFiniteExpectation prts (β t)), 
   exists (rvX : forall t, RandomVariable dom borel_sa (X t)), 
     (forall n, RandomVariable dom borel_sa (β n)) /\
       (forall ω, l1_divergent (fun n : nat => β n ω)) /\
       (forall ω, ex_series (fun n : nat => Rsqr (β n ω))) /\            
       (forall n, rv_eq (X (S n))
                    (rvplus 
                       (rvscale
                          (1 - (α n))
                          (X n))
                       (rvscale C (β n)))) /\
       (forall n ω, 0 <= β n ω) /\
       (forall n, FiniteExpectation prts (β n) <= FiniteExpectation prts (const (α n))) /\
       ps_P (event_le dom (rvlim X) C) < 1.
 Proof.
   intros.
   pose (d1 := 1.5).
   pose (d2 := 0.5).
   assert (d1_gt1: d1 > 1) by (compute; lra).
   assert (d2_lt1: d2 < 1) by (compute; lra).
   pose (p := 0.5).
   assert(p * d1 + (1-p)*d2 <= 1) by (compute; lra).
   destruct H2 as [ev ?].
   pose (β := fun n =>
                rvplus
                  (rvscale (d1 * (α n))
                     (EventIndicator (classic_dec ev)))
                  (rvscale (d2 * (α n))
                     (EventIndicator (classic_dec (event_complement ev))))).
   exists β.
   pose (X := fix X n :=
           match n with
           | 0%nat => const (pos C)
           | S n =>
               (rvplus 
                  (rvscale
                     (1 - (α n))
                     (X n))
                  (rvscale C (β n)))
           end).
   exists X.
   exists (fun t => isfe_beta (α t) d1 d2 ev).
   assert (rvb: forall t,
              RandomVariable dom borel_sa (β t)).                    
   {
     intros.
     apply rvplus_rv.
     - apply rvscale_rv.
       apply EventIndicator_rv.
     - apply rvscale_rv.
       apply EventIndicator_rv.
   }
   assert (rvX: forall t,
              RandomVariable dom borel_sa (X t)).
   {
     intros.
     induction t.
     - simpl.
       apply rvconst.
     - simpl.
       apply rvplus_rv.
       + now apply rvscale_rv.
       + now apply rvscale_rv.
   }
   exists rvX.
   split;trivial.
   split.
   - intros.
     unfold β.
     assert (d1 > 0) by lra.
     assert (d2 > 0) by (compute; lra).
     generalize (l1_divergent_scale α (mkposreal _ H4) H0); intros.
     generalize (l1_divergent_scale α (mkposreal _ H5) H0); intros.           
     simpl in H6; simpl in H7.
     unfold rvplus, rvscale, EventIndicator, event_complement, pre_event_complement; simpl.
     repeat match_destr; try tauto.
     + revert H6.
       apply is_lim_seq_ext; intros ?.
       apply sum_n_ext; intros ?.
       lra.
     + revert H7.
       apply is_lim_seq_ext; intros ?.
       apply sum_n_ext; intros ?.
       lra.
   - split.
     + intros.
       unfold β.
       unfold rvplus, rvscale, EventIndicator, event_complement, pre_event_complement; simpl.
       repeat match_destr; try tauto.
       * generalize (ex_series_scal_r (Rsqr d1) _ H1).
         apply ex_series_ext.
         intros.
         unfold Rsqr; lra.
       * generalize (ex_series_scal_r (Rsqr d2) _ H1).
         apply ex_series_ext.
         intros.
         unfold Rsqr; lra.
     + split; [intros; reflexivity|].
       split.
       * intros.
         unfold β.
         unfold rvplus, rvscale, EventIndicator, event_complement, pre_event_complement; simpl.
         repeat match_destr; try tauto.
           -- rewrite Rmult_0_r, Rplus_0_r, Rmult_1_r.
              apply Rmult_le_pos; try lra.
              apply H.
           -- rewrite Rmult_0_r, Rplus_0_l, Rmult_1_r.
                  apply Rmult_le_pos.
                  ++ compute; lra.
                  ++ apply H.
            * split.
               -- intros.
                  unfold β.
                  erewrite FiniteExpectation_plus'.
                  erewrite FiniteExpectation_scale.
                  erewrite FiniteExpectation_scale.
                  erewrite FiniteExpectation_indicator.
                  erewrite FiniteExpectation_indicator.               
                  rewrite ps_complement.
                  rewrite FiniteExpectation_const.
                  assert (ps_P ev*d1 + (1 - ps_P ev)*d2 <= 1).
                  {
                    eapply Rle_trans; cycle 1.
                    apply H3.
                    replace (ps_P ev * d1 + (1 - ps_P ev) * d2) with
                      (d2 + (ps_P ev)* ( d1 - d2)) by lra.
                    replace (p * d1 + (1 - p) * d2) with
                      (d2 + p * ( d1 - d2)) by lra.
                    apply Rplus_le_compat_l.
                    apply Rmult_le_compat_r; try lra.
                    now unfold p.
                  }
                  apply Rmult_le_compat_l with (r := α n) in H4; try lra.
                  apply H.
                  ++ apply rvscale_rv.
                     apply EventIndicator_rv.
                  ++ apply rvscale_rv.
                     apply EventIndicator_rv.
                  ++ apply rvplus_rv.
                     ** apply rvscale_rv.
                        apply EventIndicator_rv.         
                     ** apply rvscale_rv.
                        apply EventIndicator_rv.         
               -- assert (forall ω, ev ω -> (rvlim X ω) > C).
                  {
                    intros.
                    unfold rvlim.
                    pose (XX := fix XX (n : nat) : R :=
                            match n with
                            | 0%nat => pos C
                            | S n0 => (1 - α n0) * (XX n0) 
                                      + (C * d1 * (α n0))
                            end : R).
                    assert (forall n,
                               X n ω = XX n).
                    {
                      intros.
                      induction n.
                      - now simpl.
                      - simpl.
                        rv_unfold.
                        rewrite IHn.
                        f_equal.
                        rewrite Rmult_assoc.
                        f_equal.
                        unfold β.
                        unfold event_complement, pre_event_complement; simpl.
                        repeat match_destr; try tauto.
                        lra.
                    }
                    rewrite (Lim_seq_ext _ _ H5).
                    generalize (lemma3_helper_iter_conv2  XX α (d1 * C) H H0); intros.
                    cut_to H6.
                    - apply is_lim_seq_unique in H6.
                      assert (is_finite (Lim_seq (fun n : nat => XX n))).
                      {
                        rewrite H6.
                        now simpl.
                      }
                      rewrite <- H7 in H6.
                      rewrite Rbar_finite_eq in H6.
                      replace (Lim_seq XX) with (Lim_seq (fun n => XX n)).
                      + rewrite H6.
                        generalize (cond_pos C); intros.
                        apply Rmult_gt_compat_r with (r := C) in d1_gt1; lra.
                      + apply Lim_seq_ext.
                        reflexivity.
                    - intros.
                      simpl.
                      rv_unfold.
                      ring.
                  }
               
               cut (ps_P (event_le dom (rvlim X) C) <= ps_P (event_complement ev)).
               {
                 rewrite ps_complement.
                 lra.
               } 
               apply ps_sub; intros ?; simpl.
               unfold pre_event_complement.
               intros ??.
               specialize (H4 _ H6).
               lra.
       Qed.

       Lemma not01_ex05 : (~ forall (e : event dom), ps_P e = 0 \/ ps_P e = 1) -> (exists (ev : event dom), 0 < ps_P ev <= 0.5).
       Proof.
         intros HH.
         apply not_all_ex_not in HH.
         destruct HH as [e nprob].
         apply not_or_and in nprob.
         destruct (Rle_dec (ps_P e) 0.5).
         - exists e; generalize (ps_pos e); lra.
         - exists (event_complement e).
           split.
           + destruct (ps_pos (event_complement e)); trivial.
             rewrite ps_complement in H.
             lra.
           + rewrite ps_complement.
             lra.
       Qed.
       
      Lemma vecrvclip_max_bound (rvec : Ts -> vector R (S N)) (C : posreal) :
        forall a,
          Rvector_max_abs (vecrvclip (S N) rvec (pos_to_nneg C) a) <= C.
      Proof.
        intros.
        unfold vecrvclip.
        match_destr.
        - rewrite Rvector_max_abs_scale.
          simpl.
          generalize (cond_pos C); intros.
          assert (Rvector_max_abs (rvec a) > 0).
          {
            simpl in r; lra.
          }
          rewrite Rabs_right.
          + field_simplify; lra.
          + apply Rle_ge.
            apply Rdiv_le_0_compat; lra.
        - simpl in n.
          lra.
      Qed.

      Lemma almost_is_lim_nth_maxabs {NN} (X : nat -> Ts -> vector R (S NN)) :
        almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0) <->
        forall k pf,
          almost prts (fun x : Ts => is_lim_seq (fun m : nat => vector_nth k pf (X m x)) 0).
      Proof.
        split; intros.
        {
          revert H.
          apply almost_impl.
          apply all_almost.
          intros ??.
          now apply lim_seq_maxabs0.
        }
        {
          apply almost_bounded_forall in H.
          - revert H.
            apply almost_impl.
            apply all_almost; intros ??.
            now apply lim_seq_maxabs0_b.
          - intros.
            apply lt_dec.
          - intros.
            revert H0.
            apply is_lim_seq_ext.
            intros.
            apply vector_nth_ext.
        }
      Qed.

   Lemma condexp_condexp_diff_0 (XF : Ts -> R)
     {dom2 : SigmaAlgebra Ts}
     (sa_sub2 : sa_sub dom2 dom) 
     {rvXF : RandomVariable dom borel_sa XF}
     {isfe : IsFiniteExpectation prts XF} 
     {rv3 : RandomVariable dom borel_sa (FiniteConditionalExpectation prts sa_sub2 XF)} :
     almostR2 prts eq
       (ConditionalExpectation
          prts sa_sub2
          (rvminus XF
             (FiniteConditionalExpectation prts sa_sub2 XF)))
       (const 0).
     Proof.
       intros.
       apply (almost_prob_space_sa_sub_lift prts sa_sub2).
       generalize (Condexp_minus prts sa_sub2 XF (FiniteConditionalExpectation prts sa_sub2 XF)).
       apply almost_impl.
       apply all_almost; intros ??.
       rewrite H.
       generalize (FiniteCondexp_rv prts sa_sub2 XF); intros.
       assert (rv_eq 
                  (Rbar_rvminus (ConditionalExpectation prts sa_sub2 XF)
                     (ConditionalExpectation prts sa_sub2 (FiniteConditionalExpectation prts sa_sub2 XF)))
                  (Rbar_rvminus (ConditionalExpectation prts sa_sub2 XF) 
                     (ConditionalExpectation prts sa_sub2 XF))).
       {
         generalize (Condexp_id prts sa_sub2); intros.
         specialize (H1 _ _ H0).
         intros ?.
         unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
         f_equal.
         f_equal.
         rewrite H1.
         now rewrite (FiniteCondexp_eq prts sa_sub2 XF).
       }
       rewrite H1.
       generalize (FiniteCondexp_eq prts sa_sub2 XF); intros.
       rewrite H2.
       unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, const.
       simpl.
       apply Rbar_finite_eq.
       lra.
   Qed.
  
   Lemma condexp_sqr_bounded  (XF : Ts -> R) (C : R)
     {dom2 : SigmaAlgebra Ts}
     (sa_sub2 : sa_sub dom2 dom) 
     {rvXF : RandomVariable dom borel_sa XF} :
     almostR2 prts Rle (rvsqr XF) (const C) ->
     almostR2 (prob_space_sa_sub prts sa_sub2) Rbar_le (ConditionalExpectation prts sa_sub2 (rvsqr XF)) (const C).
   Proof.
     intros.
     generalize (Condexp_const prts sa_sub2 C); intros.     
     assert (IsFiniteExpectation prts (rvsqr XF)).
     {
       apply (IsFiniteExpectation_abs_bound_almost prts (rvsqr XF) (const C)).
       - revert H.
         apply almost_impl.
         unfold const, rvsqr, rvabs.
         apply all_almost; intros ??.
         now rewrite <- Rabs_sqr.
       - apply IsFiniteExpectation_const.
     }
     generalize (Condexp_ale prts sa_sub2 (rvsqr XF) (const C)); intros.
     rewrite Condexp_const in H2.
     now apply H2.
  Qed.

   Lemma condexp_sqr_bounded_prts  (XF : Ts -> R) (C : R)
     {dom2 : SigmaAlgebra Ts}
     (sa_sub2 : sa_sub dom2 dom) 
     {rvXF : RandomVariable dom borel_sa XF} :
     almostR2 prts Rle (rvsqr XF) (const C) ->
     almostR2 prts Rbar_le (ConditionalExpectation prts sa_sub2 (rvsqr XF)) (const C).
   Proof.
     intros.
     apply (almost_prob_space_sa_sub_lift prts sa_sub2).
     now apply condexp_sqr_bounded.
  Qed.

   Lemma condexp_square_bounded (XF : Ts -> R) (C : R)
     {dom2 : SigmaAlgebra Ts}
     (sa_sub2 : sa_sub dom2 dom) 
     {rvXF : RandomVariable dom borel_sa XF}
     {isfe : IsFiniteExpectation prts XF} 
     {rv3 : RandomVariable dom borel_sa (FiniteConditionalExpectation prts sa_sub2 XF)} :
     (forall ω, Rabs (XF ω) <= C) ->
     almostR2 prts Rbar_le
       (ConditionalExpectation
          prts sa_sub2
          (rvsqr (rvminus XF
                    (FiniteConditionalExpectation prts sa_sub2 XF))))
       (const (Rsqr (2 * C))).
  Proof.
    intros.
    apply condexp_sqr_bounded_prts.
    assert (almostR2 prts Rle (FiniteConditionalExpectation prts sa_sub2 XF) (const C)).
    {
      generalize (FiniteCondexp_ale prts sa_sub2 XF (const C)); intros.
      apply (almost_prob_space_sa_sub_lift prts sa_sub2).      
      rewrite FiniteCondexp_const in H0.
      apply H0.
      apply all_almost; intros ?.
      unfold const.
      specialize (H x).
      now rewrite Rabs_le_both in H.
   }
   assert (almostR2 prts Rle (const (- C)) (FiniteConditionalExpectation prts sa_sub2 XF)).
   {
      generalize (FiniteCondexp_ale prts sa_sub2 (const (- C)) XF ); intros.
      apply (almost_prob_space_sa_sub_lift prts sa_sub2).      
      rewrite FiniteCondexp_const in H1.
      apply H1.
      apply all_almost; intros ?.
      unfold const.
      specialize (H x).
      now rewrite Rabs_le_both in H.
   }
   revert H0; apply almost_impl.
   revert H1; apply almost_impl.
   unfold const, rvsqr, rvminus, rvplus, rvopp, rvscale.
   apply all_almost; intros ???.
   apply Rsqr_le_abs_1.    
   eapply Rle_trans.
   apply Rabs_triang.
   repeat rewrite Rabs_mult.
   rewrite Rabs_m1, Rmult_1_l.
   rewrite (Rabs_right 2); try lra.
   assert (0 <= C).
   {
     eapply Rle_trans; cycle 1.
     apply (H x).
     apply Rabs_pos.
   }
   rewrite (Rabs_right C); try lra.
   replace (2 * C) with (C + C) by lra.
   apply Rplus_le_compat; trivial.
   now rewrite Rabs_le_both.
  Qed.

  Lemma LimSup_pos_0 (f : nat -> R) :
    (forall n, 0 <= f n) ->
    LimSup_seq f = 0->
    Lim_seq f = 0.
  Proof.
    intros.
    generalize (Lim_seq_sup_le f); intros.
    rewrite H0 in H1.
    apply Rbar_le_antisym; trivial.
    replace (Finite 0) with (Lim_seq (const 0)).
    - apply Lim_seq_le.
      apply H.
    - unfold const.
      now rewrite Lim_seq_const.
  Qed.

  Lemma is_lim_seq_pos_0 (f : nat -> R) :
    (forall n, 0 <= f n) ->
    (forall (eps: posreal),
        eventually (fun n => f n < eps)) ->
    is_lim_seq f 0.
  Proof.
    intros.
    apply is_lim_seq_spec.
    intros ?.
    specialize (H0 eps).
    revert H0.
    apply eventually_impl.
    apply all_eventually.
    intros.
    rewrite Rminus_0_r, Rabs_right; try lra.
    now apply Rle_ge.
  Qed.
  

  Lemma LimSup_pos_bounded_finite (f : nat -> R) (c : R) :
    (forall n, 0 <= f n) ->
    Rbar_le (LimSup_seq f) c ->
    is_finite (LimSup_seq f).
  Proof.
    intros.
    apply bounded_is_finite with (a := 0) (b := c); trivial.
    replace (Finite 0) with (LimSup_seq (fun _ => 0)).
    - apply LimSup_le.
      exists 0%nat.
      intros.
      apply H.
    - apply LimSup_seq_const.
  Qed.

  Lemma Lim_seq_pos_bounded_finite (f : nat -> R) (c : R) :
    (forall n, 0 <= f n) ->
    Rbar_le (Lim_seq f) c ->
    is_finite (Lim_seq f).
  Proof.
    intros.
    apply bounded_is_finite with (a := 0) (b := c); trivial.
    replace (Finite 0) with (Lim_seq (fun _ => 0)).
    - apply Lim_seq_le.
      apply H.
    - apply Lim_seq_const.
  Qed.

  Theorem Jaakkola_alpha_beta_bounded
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S N))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S N)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S N)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))} :
    0 < γ < 1 ->
      
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <= vector_nth i pf (α k ω)) ->        

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (α n ω))))) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (β n ω))))) ->
    (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->

    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->                  
    (exists (C : Ts -> R), 
          almost prts (fun ω => forall k, Rvector_max_abs (X k ω) <= C ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k)))) ->
    (exists epsilon : posreal,
        eventually (fun n => forall i pf,
                        almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (vecrvnth i pf (β (nn+n)%nat)) ω))) (const epsilon))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
  Proof.
    intros.
    assert (rvXF2 : forall k, RandomVariable dom (Rvector_borel_sa (S N)) (XF k)).
    {
      intros.
      now apply (RandomVariable_sa_sub (filt_sub (S k))).
    }
    assert (vecisfe: forall k, vector_IsFiniteExpectation prts (XF k)).
    {
      intros.
      now apply vector_nth_IsFiniteExpectation.
    }
    pose (r := fun (k : nat) => vecrvminus (XF k)
                                  (vector_FiniteConditionalExpectation prts (filt_sub k) (XF k))).
    pose (δ := fix δ kk :=
          match kk with
                | 0%nat => X 0%nat
                | S k =>
                    (vecrvplus (vecrvminus (δ k) (vecrvmult (α k) (δ k))) 
                       (vecrvmult (β k)
                          (vector_FiniteConditionalExpectation prts (filt_sub k) (XF k))))
          end).

    pose (w := fix w kk :=
          match kk with
                | 0%nat => vecrvconst (S N) 0
                | S k =>
                    (vecrvplus (vecrvminus (w k) (vecrvmult (α k) (w k))) 
                       (vecrvmult (β k) (r k)))
          end).

    assert (forall k, rv_eq (X k) (vecrvplus (δ k) (w k))).
    {
      intros.
      induction k.
      - intros ?.
        simpl.
        unfold vecrvplus, vecrvconst.
        now rewrite Rvector_plus_zero.        
      - intros ?.
        simpl.
        rewrite H10.
        specialize (IHk a).
        unfold r, vecrvminus, vecrvplus, vecrvopp, vecrvmult, vecrvscale.
        rewrite IHk.
        unfold vecrvplus, Rvector_scale.
        repeat rewrite Rvector_mult_explode.        
        repeat rewrite Rvector_plus_explode.
        apply vector_create_ext; intros.
        repeat rewrite vector_nth_map.
        repeat rewrite vector_map_create.
        repeat rewrite vector_nth_create.
        repeat rewrite vector_nth_map.
        assert (pf3 : (i < (S N))%nat).
        {
          lia.
        }
        simpl.
        repeat match goal with
          [|- context [@vector_nth ?RR ?nn i (plus_lt_compat_l ?pi ?pn ?pc ?pp) ?v]] =>
            replace (@vector_nth RR nn i (plus_lt_compat_l pi pn pc pp) v)
            with (@vector_nth RR nn i pf3 v)
            by apply vector_nth_ext
        end.
        lra. 
    }
    assert (exists (C : Ts -> R),
               (almost prts (fun ω => forall k i pf, Rbar_le (ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k)) ω)
                                                       (C ω)))).
    {
      
      destruct H8 as [? [??]].
      destruct H9 as [? ?].
      exists (rvscale x (rvsqr (rvplus (const 1) x0))).
      intros.
      revert H13; apply almost_impl.
      revert H9; apply almost_impl.
      apply all_almost; intros ???.
      intros.
      specialize (H13 k i pf).
      eapply Rbar_le_trans.
      simpl in H13.
      apply H13.
      unfold rvmult, rvsqr, rvplus, const.
      simpl.
      apply Rmult_le_compat_l; try lra.
      unfold Rsqr.
      rewrite Rmult_1_r.
      assert (0 <= x0 x1).
      {
        eapply Rle_trans; cycle 1.
        apply (H9 0%nat).
        apply Rvector_max_abs_nonneg.
      }
      generalize (Rvector_max_abs_nonneg (X k x1)); intros.
      specialize (H9 k).
      apply Rmult_le_compat; try lra.
    }
    assert (forall k i pf,
               RandomVariable dom borel_sa (vecrvnth i pf (r k))).
    {
      intros.
      unfold r.
      apply vecrvnth_rv.
      apply Rvector_minus_rv; trivial.
      apply (RandomVariable_sa_sub (filt_sub k)).
      apply vector_FiniteCondexp_rv.
    }
    assert (forall k, vector_IsFiniteExpectation prts (r k)).
    {
      intros.
      unfold r.
      unfold vecrvminus, vecrvopp.
      apply vector_IsFiniteExpectation_plus; trivial.
      - apply Rvector_scale_rv.
        apply (RandomVariable_sa_sub (filt_sub k)).
        apply vector_FiniteCondexp_rv.
      - apply vector_IsFiniteExpectation_scale.
        apply vector_FiniteCondexp_isfe.
    }
    assert (forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (r k))).
    {
      intros.
      now apply vector_IsFiniteExpectation_nth.
    }
    assert (forall k i pf,
               almostR2 prts eq (ConditionalExpectation prts (filt_sub k) (fun ω : Ts => vector_nth i pf (r k ω)))
                 (fun x : Ts => const 0 x)).
    {
      intros.
      unfold r.
      assert (RandomVariable dom borel_sa                 (rvminus (vecrvnth i pf (XF k))
                   (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k))))).
      {
        apply rvminus_rv; trivial.
        apply (RandomVariable_sa_sub (filt_sub k)).
        apply FiniteCondexp_rv.
      }
      assert (almostR2 prts eq (ConditionalExpectation prts (filt_sub k) 
                                  (rvminus (vecrvnth i pf (XF k))
                                     (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k)))))
                (fun x : Ts => const 0 x)).
      {
        assert  (RandomVariable dom borel_sa (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k)))).        
        {
          apply (RandomVariable_sa_sub (filt_sub k)).
          apply FiniteCondexp_rv.
        }
        generalize (condexp_condexp_diff_0 (vecrvnth i pf (XF k)) (filt_sub k)).
        apply almost_impl.
        apply all_almost; intros ??.
        rewrite <- H19.
        now apply ConditionalExpectation_ext.
      }
      revert H18.
      apply almost_impl.
      apply all_almost.
      intros ??.
      rewrite <- H18.
      apply ConditionalExpectation_ext.
      intros ?.
      unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vector_FiniteConditionalExpectation.
      rewrite Rvector_nth_plus, Rvector_nth_scale.
      simpl.
      rewrite vector_of_funs_vector_nth, vector_nth_map.
      unfold rvminus, rvplus, rvopp, rvscale, vecrvnth.
      f_equal.
      f_equal.
      apply FiniteConditionalExpectation_ext.
      intros ?.
      rewrite vector_dep_zip_nth_proj1.
      now rewrite vector_nth_fun_to_vector.
    }
    assert (eqvec: forall k i pf,
               rv_eq
                 (vecrvnth i pf
                    (vecrvminus (XF k)
                       (vector_FiniteConditionalExpectation prts (filt_sub k) (XF k))) )
                 (rvminus (vecrvnth i pf (XF k))
                    (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k))))).
    {
      intros.
      intros ?.
      unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, vector_FiniteConditionalExpectation, vecrvnth.
      rewrite Rvector_nth_plus, Rvector_nth_scale.
      simpl.
      rewrite vector_of_funs_vector_nth, vector_nth_map.
      unfold rvminus, rvplus, rvopp, rvscale, vecrvnth.
      f_equal.
      f_equal.
      apply FiniteConditionalExpectation_ext.
      intros ?.
      rewrite vector_dep_zip_nth_proj1.
      now rewrite vector_nth_fun_to_vector.
    }
    assert (exists (B : Ts -> R),
                 almost prts 
                   (fun ω =>
                      forall k i pf,
                        Rbar_le
                          ((ConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (r k)))) ω) 
                          (B ω))).
    {
      unfold ConditionalVariance in H13.
      destruct H13 as [C H13].
      exists C.
      revert H13; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H13 k i pf).
      unfold r.
      eapply Rbar_le_trans; cycle 1.
      apply H13.
      apply slln.eq_Rbar_le.
      apply ConditionalExpectation_ext.
      intros ?.
      unfold rvsqr.
      f_equal.
      now rewrite eqvec.
    }
    destruct H18 as [B ?].
    assert (lim_w_0: forall (i : nat) (pf : (i < S N)%nat),
                almost prts
                  (fun ω : Ts => is_lim_seq (fun n0 : nat => vector_nth i pf (w n0 ω)) 0)).
    {
      intros n1 pf.
      generalize (fun i pf => lemma1_alpha_beta_alt_uniform
                                (fun k ω => vector_nth i pf (α k ω))
                                (fun k ω => vector_nth i pf (β k ω))
                                (fun k ω => vector_nth i pf (r k ω))
                                (fun k ω => vector_nth i pf (w k ω))); intros.
      apply (H19 n1 pf isfilt filt_sub _ _); clear H19; trivial.
      - unfold IsAdapted; intros.
        apply vecrvnth_rv.
        unfold r.
        apply Rvector_minus_rv.
        + apply rvXF.
        + apply (RandomVariable_sa_sub (isfilt n)).
          apply vector_FiniteCondexp_rv.
      - unfold IsAdapted.
        intros.
        apply vecrvnth_rv.
        apply adapt_alpha.
      - unfold IsAdapted.
        intros.
        apply vecrvnth_rv.
        apply adapt_beta.
      - intros.
        apply Condexp_cond_exp.
        apply H16.
      - intros.
        revert H0.
        apply almost_impl.
        apply all_almost; intros ??.
        apply H0.
      - intros.
        revert H1.
        apply almost_impl.
        apply all_almost; intros ??.
        apply H1.
      - intros.
        revert H0.
        apply almost_impl.
        apply all_almost; intros ??.
        apply H0.
      - intros.
        revert H1.
        apply almost_impl.
        apply all_almost; intros ??.
        apply H1.
      - revert H3.
        apply almost_impl.
        now apply all_almost; intros ??.
      - revert H4.
        apply almost_impl.
        now apply all_almost; intros ??.
      - destruct H11 as [eps H11].
        exists eps.
        revert H11.
        apply eventually_impl.
        apply all_eventually.
        intros.
        apply H11.
      - intros.
        simpl.
        unfold vecrvminus, vecrvmult, vecrvplus, vecrvopp, vecrvscale.
        repeat rewrite Rvector_nth_plus.
        rewrite Rvector_nth_scale.
        repeat rewrite Rvector_nth_mult.
        lra.
      - exists B.
        revert H18; apply almost_impl.
        apply all_almost; intros ??.
        intros.
        apply H18.
   }
    apply almost_bounded_forall; intros.
    - apply lt_dec.
    - revert H19.
      apply is_lim_seq_ext.
      intros.
      apply vector_nth_ext.
    - assert (forall n1 : nat, RandomVariable dom (Rvector_borel_sa (S N)) (w n1)).
      {
          induction n1.
          - simpl.
            apply rvconst.
          - simpl.
            apply Rvector_plus_rv.
            + apply Rvector_minus_rv; trivial.
              apply Rvector_mult_rv; trivial.
              specialize (adapt_alpha n1).
              now apply RandomVariable_sa_sub in adapt_alpha.
            + apply Rvector_mult_rv; trivial.
              * specialize (adapt_beta n1).
              now apply RandomVariable_sa_sub in adapt_beta.
              * now apply rv_vecrvnth.
      }
      assert (forall n1 : nat, RandomVariable dom borel_sa (fun ω : Ts => vector_nth n pf (w n1 ω))).
      {
          intros.
          now apply vecrvnth_rv.
      }
      generalize lim_w_0; intros lim_maxabs_0.
      rewrite <- almost_is_lim_nth_maxabs in lim_maxabs_0.
      generalize (conv_as_prob_1_eps_forall _ lim_maxabs_0); intros.
      assert (exists C, 0 < C /\ γ * ((C + 1) / C) < 1).
      {
          exists  (2 * γ / (1 - γ)).
          split.
          - apply Rmult_lt_0_compat; try lra.
            apply Rinv_0_lt_compat.
            lra.
          - field_simplify; lra.
      }
      destruct H22 as [C [? ?]].
      assert (forall (eps : posreal),
                   forall k ω,
                     Rvector_max_abs(δ k ω) > C * eps ->
                     Rvector_max_abs (Rvector_plus (Rvector_abs (δ k ω)) (@vector_const R eps (S N))) <= ((C + 1)/C) * Rvector_max_abs(δ k ω)).
        {
          intros.
          replace (Rvector_max_abs (Rvector_plus (Rvector_abs (δ k ω)) (@vector_const R eps (S N)))) with
            ((Rvector_max_abs (Rvector_plus (Rvector_scale C (Rvector_abs (δ k ω))) (Rvector_scale C (@vector_const R eps (S N)))))/C).
          - apply Rle_trans with (r2 := Rvector_max_abs (Rvector_scale (C + 1) (δ k ω))/C).
            + unfold Rdiv.
              apply Rmult_le_compat_r.
              * left.
                now apply Rinv_0_lt_compat.
              * eapply Rle_trans.
                apply Rvector_max_abs_triang.
                repeat rewrite Rvector_max_abs_scale.
                rewrite (Rabs_right C); try lra.
                rewrite (Rabs_right (C + 1)); try lra.                
                rewrite Rmult_plus_distr_r.
                replace (Rvector_max_abs (Rvector_abs (δ k ω))) with
                  (Rvector_max_abs (δ k ω)) .
                -- apply Rplus_le_compat_l.
                   rewrite Rvector_max_abs_const.
                   rewrite (Rabs_right eps); try lra.
                   left.
                   apply cond_pos.
                -- unfold Rvector_max_abs, Rvector_abs.
                   f_equal.
                   rewrite vector_map_map.
                   apply vector_map_ext.
                   intros.
                   now rewrite Rabs_Rabsolu.
            + rewrite Rvector_max_abs_scale.
              rewrite (Rabs_right (C + 1)); try lra.
          - rewrite <- Rvector_scale_plus_l.
            rewrite Rvector_max_abs_scale.
            rewrite (Rabs_right C); try lra.
            field.
            lra.
        }
        assert (almost prts 
                  (fun  ω => forall n i pf,
                       Rabs (vector_nth i pf (δ (S n) ω)) <=
                         (1 - vector_nth i pf (α n ω)) * Rabs (vector_nth i pf (δ n ω)) +
                           γ * (vector_nth i pf (β n ω)) * 
                             Rvector_max_abs (Rvector_plus (Rvector_abs (δ n ω)) (Rvector_abs (w n ω))))).
        {
          revert H7; apply almost_impl.
          revert H0; apply almost_impl.
          revert H1; apply almost_impl.
          apply all_almost; intros ω???.
          intros.
          simpl.
          unfold vecrvminus, vecrvopp, vecrvplus, vecrvscale, vecrvmult.
          repeat rewrite Rvector_nth_plus.
          rewrite Rvector_nth_scale.
          repeat rewrite  Rvector_nth_mult.
          replace  (vector_nth i pf0 (δ n0 ω) +
                    -1 * (vector_nth i pf0 (α n0 ω) * vector_nth i pf0 (δ n0 ω))) with
            ((1 - vector_nth i pf0 (α n0 ω)) * (vector_nth i pf0 (δ n0 ω))) by lra.
          eapply Rle_trans.
          apply Rabs_triang.
          specialize (H0 n0 i pf0).
          specialize (H1 n0 i pf0).
          rewrite Rabs_mult, Rabs_right; try lra.
          apply Rplus_le_compat_l.
          rewrite Rabs_mult, Rabs_right; try lra.
          rewrite (Rmult_comm γ _).
          rewrite Rmult_assoc.
          apply Rmult_le_compat_l; try lra.
          rewrite vector_FiniteConditionalExpectation_nth.
          specialize (H7 n0 i pf0).
          rewrite H12 in H7.
          eapply Rle_trans; cycle 1.
          assert ( γ * Rvector_max_abs (vecrvplus (δ n0) (w n0) ω) <=
                     γ * Rvector_max_abs (Rvector_plus (Rvector_abs (δ n0 ω)) (Rvector_abs (w n0 ω)))).
          {
            apply Rmult_le_compat_l; try lra.
            unfold vecrvplus.
            apply Rvector_max_abs_le.
            intros.
            repeat rewrite Rvector_nth_plus.
            eapply Rle_trans.
            apply Rabs_triang.
            repeat rewrite Rvector_nth_abs.
            generalize (Rabs_pos (vector_nth i0 pf1 (δ n0 ω)) ); intros.
            generalize (Rabs_pos  (vector_nth i0 pf1 (w n0 ω))); intros.
            rewrite (Rabs_right (Rabs (vector_nth i0 pf1 (δ n0 ω)) + Rabs (vector_nth i0 pf1 (w n0 ω)))); lra.
          }
          apply H25.
          eapply Rle_trans; cycle 1.
          apply H7.
          right.
          f_equal.
          now apply FiniteConditionalExpectation_ext.
        }
        assert (rv_alpha: forall n1,
                   RandomVariable dom (Rvector_borel_sa (S N)) (α n1)).
        {
          intros.
          now apply (RandomVariable_sa_sub (filt_sub n1)).
        }
        assert (rv_beta: forall n1,
                   RandomVariable dom (Rvector_borel_sa (S N)) (β n1)).
        {
          intros.
          now apply (RandomVariable_sa_sub (filt_sub n1)).
        }
        assert (rv_delta: forall n1,
                   RandomVariable dom (Rvector_borel_sa (S N)) (δ n1)).
        {
          intros.
          induction n1.
          - simpl.
            now apply (RandomVariable_sa_sub (filt_sub 0%nat)).
          - simpl.
            apply Rvector_plus_rv.
            + apply Rvector_minus_rv; trivial.
              now apply Rvector_mult_rv.
            + apply Rvector_mult_rv; trivial.
              apply (RandomVariable_sa_sub (filt_sub n1)).
              apply vector_FiniteCondexp_rv.
        }
        assert (forall i pf n1,
                   RandomVariable dom borel_sa (rvabs (vecrvnth i pf (δ n1)))).
        {
          intros.
          apply rvabs_rv.
          now apply vecrvnth_rv.
        }
        assert (forall (eps : posreal) i pf n1,
                   RandomVariable dom borel_sa
                     (rvplus 
                        (vecrvnth i pf
                           (vecrvminus (δ n1) 
                              (vecrvmult (α n1) (δ n1))))
                        (rvscale γ
                           (rvmult (vecrvnth i pf (β n1))
                              (rvmaxabs
                                 (vecrvplus 
                                    (δ n1) 
                                    (vecrvconst (S N) eps))))))).
        {
          intros.
          apply rvplus_rv.
          - apply vecrvnth_rv.
            apply Rvector_minus_rv; trivial.
            now apply Rvector_mult_rv.
          - apply rvscale_rv.
            apply rvmult_rv.
            + now apply vecrvnth_rv.
            + apply Rvector_max_abs_rv.
              apply Rvector_plus_rv; trivial.
              apply rvconst.
        }
        assert (forall (eps : posreal),
                   eventually 
                     (fun n0 : nat =>
                        ps_P 
                          (inter_of_collection
                             (fun n1 =>
                                (bounded_inter_of_collection 
                                   (fun i pf =>
                                      (event_Rle
                                         dom
                                         (rvabs (vecrvnth i pf (δ (S (n0 + n1)))))
                                         (rvplus 
                                            (vecrvnth i pf
                                               (vecrvminus (vecrvabs (δ (n0 + n1)%nat))
                                                  (vecrvmult (α (n0 + n1)%nat) (vecrvabs (δ (n0 + n1)%nat)))))
                                            (rvscale γ
                                               (rvmult (vecrvnth i pf (β (n0 + n1)%nat))
                                                  (rvmaxabs
                                                     (vecrvplus 
                                                        (vecrvabs (δ (n0 + n1)%nat))
                                                        (vecrvconst (S N) eps)))))))))))
                                >= 1-eps  )).
        {
          intros.
          generalize (almost_and _ (almost_and _ H0 H1) H25); intros.
          destruct H28 as [? [??]].
          specialize (H21 eps eps).
          revert H21.
          apply eventually_impl.
          apply all_eventually.
          intros ??.
          assert
            (ps_P
               (event_inter x
                  (inter_of_collection
                     (fun n0 : nat => event_lt dom (rvabs (fun ω : Ts => rvmaxabs (w (n0 + x0)%nat) ω)) eps)))
                >= 1-eps).
          {
            now rewrite ps_inter_l1.
          }
          eapply Rge_trans; cycle 1.
          apply H30.
          apply Rle_ge.
          apply ps_sub.
          intros ??.
          simpl in H31.
          unfold pre_event_inter in H31.
          destruct H31.
          specialize (H29 x1 H31).
          unfold inter_of_collection, bounded_inter_of_collection, pre_bounded_inter_of_collection, event_Rle, event_Rge, proj1_sig.
          intros.
          apply Rle_ge.
          unfold rvabs.
          eapply Rle_trans.
          apply H29.
          unfold vecrvnth, vecrvminus, vecrvplus, vecrvopp, rvscale.
          unfold rvplus, rvmult, vecrvconst, vecrvscale, vecrvmult.
          rewrite Rvector_nth_plus, Rvector_nth_scale, Rvector_nth_mult.
          unfold rvmaxabs.
          destruct H29 as [[? ?] ?].
          simpl.
          replace (vector_nth i pf0 (vecrvabs (δ (x0 + n0)%nat) x1) +
                   -1 * (vector_nth i pf0 (α (x0 + n0)%nat x1) * vector_nth i pf0 (vecrvabs (δ (x0 + n0)%nat) x1))) with
            ((1 - vector_nth i pf0 (α (x0 + n0)%nat x1)) * vector_nth i pf0 (vecrvabs (δ (x0 + n0)%nat) x1)) by lra.
          unfold vecrvabs.
          replace (vector_nth i pf0 (Rvector_abs (δ (x0 + n0)%nat x1))) with
            (Rabs (vector_nth i pf0 (δ (x0 + n0)%nat x1))).
          - apply Rplus_le_compat_l.
            rewrite Rmult_assoc.
            apply Rmult_le_compat_l; try lra.
            apply Rmult_le_compat_l.
            + apply H33.
            + unfold rvabs, vecrvnth in H32.
              specialize (H32 n0).
              replace (n0 + x0)%nat with (x0 + n0)%nat in H32 by lia.
              unfold rvmaxabs in H32.
              rewrite Rabs_Rvector_max_abs in H32.
              apply Rvector_max_abs_le.
              intros.
              rewrite Rvector_nth_plus.
              rewrite Rvector_nth_plus.
              repeat rewrite Rvector_nth_abs.
              rewrite (Rabs_right  (Rabs (vector_nth i0 pf1 (δ (x0+n0)%nat x1)) + Rabs (vector_nth i0 pf1 (w (x0 + n0)%nat x1)))).
              rewrite vector_nth_const.
              rewrite (Rabs_right (Rplus (Rabs (@vector_nth R (S N) i0 pf1 (δ (x0 +n0)%nat x1))) (pos eps))).
              * apply Rplus_le_compat_l.
                left.
                eapply Rle_lt_trans.
                apply Rvector_max_abs_nth_le.
                apply H32.
              * generalize (Rabs_pos (vector_nth i0 pf1 (δ (x0+n0)%nat x1))); intros.
                generalize (cond_pos eps); intros.
                lra.
              * generalize (Rabs_pos  (vector_nth i0 pf1 (δ (x0+n0)%nat x1))); intros.
                generalize (Rabs_pos (vector_nth i0 pf1 (w (x0+n0)%nat x1))); intros.
                lra.
          - now rewrite Rvector_nth_abs.
        }
        assert (forall (eps : posreal),
                   ps_P
                     (event_eventually
                        (fun n0 : nat =>
                          (inter_of_collection
                             (fun n1 : nat =>
                                event_le dom (rvmaxabs (δ (n0 + n1)%nat))
                                  (C * eps)))))
                   >= 1 - eps).
        {
          intros eps.
          specialize (H28 eps).
          destruct H28.
          specialize (H28 x).
          cut_to H28; try lia.
          generalize almost_independent_impl; intros HH.
          assert  (gamma_C_pos: 0 < γ * ((C + 1) / C)).
          {
            apply Rmult_lt_0_compat; try lra.
            apply Rdiv_lt_0_compat; lra.
          }
          pose (δδ := fix δδ n :=
                  match n with
                  | 0%nat => vecrvabs (δ x)
                  | S n =>

                      (vecrvplus (vecrvminus (δδ n) (vecrvmult (α (x + n)%nat) (δδ n)))
                         (vecrvscalerv (rvmaxabs (δδ n))
                            (vecrvscale {| pos := γ * ((C + 1) / C); cond_pos := gamma_C_pos |} (β (x + n)%nat))))
                  end).

          assert (rvdd: forall n : nat, RandomVariable dom (Rvector_borel_sa (S N)) (δδ n)).
          {
            induction n0.
            - simpl.
              now apply Rvector_abs_rv.
            - simpl.
              intros.
              apply Rvector_plus_rv.
              + apply Rvector_minus_rv; trivial.
                now apply Rvector_mult_rv.
              + apply Rvector_scale_rv_rv.
                * now apply Rvector_max_abs_rv.
                * now apply Rvector_scale_rv.
          }
          pose (αα := fun n => α (x + n)%nat).
          pose (ββ := fun n => β (x + n)%nat).
          assert (αα_almost:
                   almost prts
                     (fun ω : Ts =>
                        forall (k i : nat) (pf : (i < S N)%nat),
                          0 <= vector_nth i pf (αα k ω) <= 1)).
          {
            revert H0; apply almost_impl.
            apply all_almost; intros ??.
            intros.
            apply H0.
         }
          assert (ββ_almost:
                   almost prts
                     (fun ω : Ts =>
                        forall (k i : nat) (pf : (i < S N)%nat),
                          0 <= vector_nth i pf (ββ k ω) <= 1)).
          {
            revert H1; apply almost_impl.
            apply all_almost; intros ??.
            intros.
            apply H1.
         }
         assert (αβ_almost : 
                  almost prts
                    (fun ω : Ts =>
                       forall (k i : nat) (pf : (i < S N)%nat),
                         vector_nth i pf (ββ k ω) <= vector_nth i pf (αα k ω))).
          {
            revert H2; apply almost_impl.
            apply all_almost; intros ??.
            intros.
            apply H2.
          }
          assert (lemma3_eq :forall n : nat,
            rv_eq (δδ (S n))
              (vecrvplus (vecrvminus (δδ n) (vecrvmult (αα n) (δδ n)))
                 (vecrvscalerv (rvmaxabs (δδ n))
                    (vecrvscale
                       {| pos := γ * ((C + 1) / C); cond_pos := gamma_C_pos |}
                       (ββ n))))) .
          {
            intros.
            now simpl.
          }
          assert (l1_div: 
                   almost prts
                     (fun ω : Ts =>
                        forall (i : nat) (pf : (i < S N)%nat),
                          l1_divergent (fun n : nat => vector_nth i pf (αα n ω)))).
          {
            revert H3; apply almost_impl.
            apply all_almost; intros ????.
            specialize (H3 i pf0).
            unfold l1_divergent, αα.
            apply is_lim_seq_sum_shift_inf with (N := x) in H3.
            revert H3.
            apply is_lim_seq_ext.
            intros.
            apply sum_n_ext.
            intros.
            now replace (n1 + x)%nat with (x + n1)%nat by lia.
          }
          generalize (lemma3_full_almost αα ββ δδ (mkposreal _ gamma_C_pos) _ _ _ αα_almost ββ_almost αβ_almost l1_div H23 lemma3_eq); intros lemma3.
          generalize (almost_and _ (almost_and _ H0 H1) (almost_and _ H2 lemma3)); intros.
          destruct H29 as [? [??]].
          assert
            (ps_P
               (event_inter x0
                            (inter_of_collection
             (fun n1 : nat =>
              bounded_inter_of_collection
                (fun (i : nat) (pf : (i < S N)%nat) =>
                 event_Rle dom (rvabs (vecrvnth i pf (δ (S (x + n1)))))
                   (rvplus
                      (vecrvnth i pf
                         (vecrvminus (vecrvabs (δ (x + n1)%nat)) (vecrvmult (α (x + n1)%nat) (vecrvabs (δ (x + n1)%nat)))))
                      (rvscale γ
                         (rvmult (vecrvnth i pf (β (x + n1)%nat))
                            (rvmaxabs (vecrvplus (vecrvabs (δ (x + n1)%nat)) (vecrvconst (S N) eps))))))))))
                >= 1-eps).
          {
            now rewrite ps_inter_l1.
          }
          eapply Rge_trans; cycle 1.
          apply H31.
          apply Rle_ge.
          apply ps_sub.
          intros ??.
          simpl.
          destruct (classic_min_of_sumbool
                     (fun n => Rvector_max_abs (δ (x + n)%nat x1) <= (C * eps))).
          - destruct s as [? [??]].
            clear H34.
            assert (forall k,
                        Rvector_max_abs (δ (x + (x2+k))%nat x1) <= C * eps).
            {
              induction k.
              - eapply Rle_trans; cycle 1.
                apply H33.
                replace (x + (x2 + 0))%nat with (x + x2)%nat by lia.
                lra.
              - unfold event_inter, pre_event_inter, inter_of_collection, bounded_inter_of_collection, pre_bounded_inter_of_collection, event_Rle, event_Rge, proj1_sig in H32.
                destruct H32.
                specialize (H30 x1 H32).
                unfold pre_event_inter in H30.
                destruct H30 as [[? ?] ?].
                rewrite Rvector_max_abs_nth_Rabs_le.
                intros.
                specialize (H34 (x2 + k)%nat i pf0).
                apply Rge_le in H34.
                unfold rvabs, vecrvnth in H34.
                replace (S (x + (x2 + k))) with (x + (x2 + S k))%nat in H34 by lia.
                eapply Rle_trans.
                apply H34.
                unfold vecrvminus, vecrvmult, vecrvplus, vecrvopp, vecrvabs, vecrvconst, vecrvscale, rvmaxabs, rvscale, rvmult, rvplus.
                rewrite Rvector_nth_plus, Rvector_nth_scale, Rvector_nth_mult.
                generalize (cond_pos eps); intros.
                rewrite Rvector_max_abs_plus_nneg; try lra.
                rewrite Rvector_nth_abs.
                replace (Rabs (vector_nth i pf0 (δ (x + (x2 + k))%nat x1)) +
                         -1 * (vector_nth i pf0 (α (x + (x2 + k))%nat x1) * Rabs (vector_nth i pf0 (δ (x + (x2 + k))%nat x1))))
                  with
                  ((1 - (vector_nth i pf0 (α (x + (x2 + k))%nat x1))) * Rabs (vector_nth i pf0 (δ (x + (x2 + k))%nat x1))) by lra.
                assert ((Rvector_max_abs (δ (x + (x2 + k))%nat x1) + eps) <= (C + 1)*eps).
                {
                  lra.
                }
                apply Rmult_lt_compat_r with (r := C) in H23; trivial.
                rewrite Rmult_1_l in H23.
                unfold Rdiv in H23.
                rewrite Rmult_assoc in H23.
                rewrite Rmult_assoc in H23.
                rewrite Rmult_inv_l in H23; try lra.
                rewrite Rmult_1_r in H23.
                apply Rmult_le_compat_l with (r :=  γ * (vector_nth i pf0 (β (x + (x2 + k))%nat x1))) in H38.
                + assert (γ * vector_nth i pf0 (β (x + (x2 + k))%nat x1) * (Rvector_max_abs (δ (x + (x2 + k))%nat x1) + eps) <=
                            (vector_nth i pf0 (α (x + (x2 + k))%nat x1) * (C * eps))).
                  {
                    eapply Rle_trans.
                    apply H38.
                    generalize (cond_pos eps); intros.
                    assert  (γ * (C + 1) <= C) by lra.
                    apply Rmult_le_compat_r with (r := eps) in H40; try lra.
                    apply Rmult_le_compat_l with (r := vector_nth i pf0 (β (x + (x2 + k))%nat x1)) in H40.
                    apply Rle_trans with (r2 := vector_nth i pf0 (β (x + (x2 + k))%nat x1) * (C * eps)); try lra.
                    apply Rmult_le_compat_r.
                    apply Rmult_le_pos; lra.
                    apply H36.
                    apply H35.
                  }
                  apply Rplus_le_compat_l with (r :=  (1 - vector_nth i pf0 (α (x + (x2 + k))%nat x1)) * Rabs (vector_nth i pf0 (δ (x + (x2 + k))%nat x1))) in H39.
                  rewrite <- Rmult_assoc.
                  eapply Rle_trans.
                  apply H39.
                  assert (Rabs (vector_nth i pf0 (δ (x + (x2 + k))%nat x1)) <= C * eps).
                  {
                    now rewrite Rvector_max_abs_nth_le.
                  }
                  apply Rmult_le_compat_l with (r := (1 - vector_nth i pf0 (α (x + (x2 + k))%nat x1)) ) in H40.
                  apply Rplus_le_compat_r with (r := vector_nth i pf0 (α (x + (x2 + k))%nat x1) * (C * eps)) in H40.
                  eapply Rle_trans.
                  apply H40.
                  rewrite <- Rmult_plus_distr_r; try lra.
                  specialize (H30 (x + (x2 + k))%nat i pf0); try lra.
             + apply Rmult_le_pos; try lra.
               apply H35.
            }
            exists (x + x2)%nat.
            intros.
            specialize (H34 (n1 + (n0 - (x + x2)))%nat).
            replace (x + (x2 + (n1 + (n0 - (x + x2)))))%nat with (n0 + n1)%nat in H34 by lia.
            apply H34.
          - assert (forall n0,  Rvector_max_abs (δ (x + n0)%nat x1) > C * eps).
            {
              intros.
              specialize (n0 n1).
              now apply Rnot_le_gt in n0.
            }
            unfold event_inter, pre_event_inter, inter_of_collection, bounded_inter_of_collection, pre_bounded_inter_of_collection, event_Rle, event_Rge, proj1_sig in H32.
            destruct H32.
            specialize (H30 x1 H32).
            unfold pre_event_inter in H30.
            destruct H30 as [[? ?] [? ?]].
            assert (dd_pos: forall n i pf0,
                       0 <= vector_nth i pf0 (δδ n x1)).
            {
              intros.
              induction n1.
              - simpl.
                unfold vecrvabs.
                rewrite Rvector_nth_abs.
                apply Rabs_pos.
              - simpl.
                unfold vecrvminus, vecrvplus, vecrvmult, vecrvscalerv, vecrvopp, vecrvscale.
                repeat rewrite Rvector_nth_plus.
                repeat rewrite Rvector_nth_scale.
                rewrite Rvector_nth_mult.
                replace (vector_nth i pf0 (δδ n1 x1) + -1 * (vector_nth i pf0 (α (x + n1)%nat x1) * vector_nth i pf0 (δδ n1 x1))) with
                  ((1 - (vector_nth i pf0 (α (x + n1)%nat x1))) * vector_nth i pf0 (δδ n1 x1)) by lra.
                apply Rplus_le_le_0_compat.
                + apply Rmult_le_pos; trivial.
                  specialize (H30 (x + n1)%nat i pf0); lra.
                + apply Rmult_le_pos.
                  * apply Rvector_max_abs_nonneg.
                  * apply Rmult_le_pos.
                    -- apply Rmult_le_pos; try lra.
                       apply Rdiv_le_0_compat; lra.
                    -- specialize (H35 (x + n1)%nat i pf0); lra.
            }
            assert (forall n i pf,
                       Rabs(vector_nth i pf (δ (x + n)%nat x1)) <=
                         vector_nth i pf (δδ (n)%nat x1)).
            {
              induction n1.
              - intros.
                simpl.
                rewrite vecrvabs_unfold.
                rewrite vector_nth_apply.
                rewrite vector_nth_const.
                now replace (x + 0)%nat with x by lia.
              - intros.
                replace (x + S n1)%nat with (S (x + n1)) by lia.
                specialize (H34 n1 i pf0).
                apply Rge_le in H34.
                eapply Rle_trans.
                apply H34.
                simpl.
                unfold vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale, vecrvnth.
                unfold rvplus, rvscale, rvmult.
                repeat rewrite Rvector_nth_plus.
                rewrite vecrvabs_unfold.
                repeat rewrite Rvector_nth_scale.
                repeat rewrite Rvector_nth_mult.
                repeat rewrite vector_nth_apply.
                repeat rewrite vector_nth_const.
                apply Rplus_le_compat.
                + replace (Rabs(vector_nth i pf0 (δ (x + n1)%nat x1)) +
                           -1 *
                              (vector_nth i pf0 (α (x + n1)%nat x1) * 
                                 Rabs (vector_nth i pf0 (δ (x + n1)%nat x1)))) with
                    ((1 - (vector_nth i pf0 (α (x + n1)%nat x1))) * 
                       Rabs (vector_nth i pf0 (δ (x + n1)%nat x1))) by lra.
                  replace (vector_nth i pf0 (δδ n1 x1) +
                           -1 * (vector_nth i pf0 (α (x + n1)%nat x1) * 
                                   vector_nth i pf0 (δδ n1 x1))) with
                    ((1 - (vector_nth i pf0 (α (x + n1)%nat x1))) * 
                       vector_nth i pf0 (δδ n1 x1)) by lra.
                  apply Rmult_le_compat_l; trivial.
                  specialize (H30 (x + n1)%nat i pf0); lra.
                + unfold rvmaxabs, vecrvabs, vecrvconst, vecrvscalerv.
                  rewrite Rvector_nth_scale.
                  rewrite Rvector_nth_scale.
                  rewrite Rmult_comm.
                  rewrite (Rmult_comm _ (vector_nth i pf0 (β (x + n1)%nat x1))).
                  rewrite <- Rmult_assoc.
                  rewrite (Rmult_comm _ (vector_nth i pf0 (β (x + n1)%nat x1))).
                  repeat rewrite Rmult_assoc.
                  apply Rmult_le_compat_l.
                  * specialize (H35 (x + n1)%nat i pf0); lra.
                  * specialize (H33 n1).
                    specialize (H24 eps (x + n1)%nat x1 H33).
                    apply Rmult_le_compat_r with (r := γ) in H24; try lra.
                    eapply Rle_trans.
                    apply H24.
                    rewrite Rmult_comm.
                    rewrite (Rmult_comm (Rvector_max_abs (δδ n1 x1))).
                    rewrite <- Rmult_assoc.
                    apply Rmult_le_compat_l.
                    -- apply Rmult_le_pos; try lra.
                       apply Rdiv_le_0_compat; lra.
                    -- apply Rvector_max_abs_le.
                       intros.
                       eapply Rle_trans.
                       apply IHn1.
                       apply Rle_abs.
            }
            assert (forall n i pf0,
                       Rabs (vector_nth i pf0 (δ (x + n)%nat x1)) <= Rabs (vector_nth i pf0 (δδ n x1))).
            {
              intros.
              eapply Rle_trans.
              apply H38.
              apply Rle_abs.
            }

            assert (lim_dd: forall i pf, is_lim_seq (fun m : nat => vector_nth i pf (δδ m x1)) 0).
            {
              intros.
              now apply lim_seq_maxabs0.
            }
            assert (forall n,
                       Rvector_max_abs (δ (x + n)%nat x1) <= Rvector_max_abs (δδ n x1)).
            {
              intros.
              now apply Rvector_max_abs_le.
            }
            assert (is_lim_seq  (fun m : nat => Rvector_max_abs (δ m x1)) 0).
            {
              intros.
              apply is_lim_seq_incr_n with (N := x).
              revert H37.
              apply is_lim_seq_le_le with (u := const 0).
              - intros.
                split.
                + unfold const.
                  apply Rvector_max_abs_nonneg.
                + replace (n1 + x)%nat with (x + n1)%nat by lia.
                  apply H40.
              - apply is_lim_seq_const.
            }
            apply is_lim_seq_spec in H41.
            unfold is_lim_seq' in H41.
            assert (0 < C * eps).
            {
              apply Rmult_lt_0_compat; try lra.
              apply cond_pos.
            }
            specialize (H41 (mkposreal _ H42)).
            destruct H41.
            exists x2.
            intros.
            specialize (H41 (n1 + n2)%nat).
            cut_to H41; try lia.
            rewrite Rminus_0_r in H41.
            simpl in H41.
            unfold rvmaxabs.
            rewrite Rabs_Rvector_max_abs in H41.
            lra.
        }
        assert (epsk: forall (k : nat),
                   0 < / INR (S k)).
          {
            intros.
            apply Rinv_0_lt_compat.
            apply lt_0_INR.
            lia.
          }
          assert (forall (k : nat),
                     ps_P
                       (event_eventually
                          (fun n0 : nat => inter_of_collection (fun n1 : nat => 
                                                                  event_le dom (rvmaxabs (δ (n0 + n1)%nat))
                                                                    (C * (mkposreal _ (epsk k)))))) >= 
                       1 - (mkposreal _ (epsk k)) ).
          {
            intros.
            apply H29.
          }

        assert (almost prts (fun ω : Ts => is_lim_seq (fun n1 : nat => vector_nth n pf (δ n1 ω)) 0)).
        {
          apply almost_is_lim_nth_maxabs.
          assert (is_lim_seq (fun k => mkposreal _ (epsk k)) 0).
          {
            assert (is_lim_seq (fun k => INR(S k)) p_infty).
            {
              rewrite <- is_lim_seq_incr_1.
              apply is_lim_seq_INR.
            }
            apply is_lim_seq_inv in H31.
            + replace (Rbar_inv p_infty) with (Finite 0) in H31.
              * apply H31.
              * now unfold Rbar_inv.
            + discriminate.            
          }

          assert (is_lim_seq (fun k => 1 - mkposreal _ (epsk k)) 1).
          {
            apply is_lim_seq_minus with (l1 := 1) (l2 := 0); trivial.
            - apply is_lim_seq_const.
            - unfold is_Rbar_minus, is_Rbar_plus.
              simpl.
              f_equal; f_equal; lra.
          }
          assert (is_lim_seq (fun k => (C * (mkposreal _ (epsk k)))) 0).
          {
            apply is_lim_seq_scal_l with (a := C) in H31.
            now rewrite Rbar_mult_0_r in H31.
          }
          assert (forall k,
                     event_sub
                       (event_eventually
                          (fun n0 : nat =>
                             inter_of_collection
                               (fun n1 : nat => event_le dom (rvmaxabs (δ (n0 + n1)%nat)) (C * (mkposreal _ (epsk (S k)))))))
                       (event_eventually
                          (fun n0 : nat =>
                             inter_of_collection
                               (fun n1 : nat => event_le dom (rvmaxabs (δ (n0 + n1)%nat)) (C * (mkposreal _ (epsk k))))))).
          {
            intros ??.
            unfold event_eventually, event_le, proj1_sig.
            apply eventually_impl.
            apply all_eventually.
            simpl; intros.
            specialize (H34 n0).
            eapply Rle_trans.
            apply H34.
            apply Rmult_le_compat_l.
            - lra.
            - apply Rinv_le_contravar.
              + match_destr.
                * lra.
                * generalize (pos_INR (S k)); lra.
              + match_destr;lra.
          }
         assert (event_equiv
                   (inter_of_collection
                      (fun k =>
                         (event_eventually
                            (fun n0 : nat =>
                               inter_of_collection
                                 (fun n1 : nat => event_le dom (rvmaxabs (δ (n0 + n1)%nat)) (C * (mkposreal _ (epsk k))))))))
                   (inter_of_collection
                      (fun k =>
                         (event_eventually
                            (fun n0 : nat =>
                               event_le dom (rvmaxabs (δ n0)) (C * (mkposreal _ (epsk k)))))))).
          {
            intros ?.
            unfold inter_of_collection, proj1_sig, event_eventually, event_le.
            simpl.
            unfold pre_event_preimage, pre_event_singleton.
            split; intros.
            - specialize (H35 n0).
              destruct H35.
              exists x0.
              intros.
              specialize (H35 n1 H36).
              specialize (H35 0%nat).
              replace (n1 + 0)%nat with n1 in H35 by lia.
              apply H35.
            - specialize (H35 n0).
              destruct H35.
              exists x0.
              intros.
              specialize (H35 (n1 + n2)%nat).
              cut_to H35; try lia.
              eapply Rle_trans.
              apply H35.
              lra.
          }
          generalize (lim_prob_descending _ _ H34 H35); intros.
          assert (forall k,
                     1 - {| pos := / INR (S k); cond_pos := epsk k |} <=
                           ps_P
                             (event_eventually
                                (fun n0 : nat =>
                                   inter_of_collection
                                     (fun n1 : nat => event_le dom (rvmaxabs (δ (n0 + n1)%nat)) (C * {| pos := / INR (S k); cond_pos := epsk k |}))))).
          {
            intros.
            now apply Rge_le.
          }
          generalize (is_lim_seq_le _ _ (Finite 1) (Finite (ps_P
                                                              (inter_of_collection
                                                                 (fun k =>
                                                                    (event_eventually
                                                                       (fun n0 : nat =>
                                                                          event_le dom (rvmaxabs (δ n0)) (C * (mkposreal _ (epsk k))))))))) H37 H32 H36); intros.
          simpl in H38.
          assert ( ps_P
                     (inter_of_collection
                        (fun k : nat =>
                           event_eventually
                             (fun n0 : nat => event_le dom (rvmaxabs (δ n0)) (C * / match k with
                                                                                    | 0%nat => 1
                                                                                    | S _ => INR k + 1
                                                                                    end)))) = 1).
          {
            apply Rle_antisym; trivial.
            apply ps_le1.
          }
          unfold almost.
          exists (inter_of_collection
             (fun k : nat =>
              event_eventually
                (fun n0 : nat => event_le dom (rvmaxabs (δ n0)) (C * / match k with
                                                                       | 0%nat => 1
                                                                       | S _ => INR k + 1
                                                                       end)))).
          split; trivial.
          intros.
          apply is_lim_seq_spec.
          unfold is_lim_seq'.
          intros.
          simpl in H40.
          apply is_lim_seq_spec in H33.
          specialize (H33 eps).
          destruct H33.
          specialize (H40 x0).
          revert H40.
          apply eventually_impl.
          apply all_eventually.
          intros.
          unfold rvmaxabs.
          rewrite Rminus_0_r, Rabs_Rvector_max_abs.
          eapply Rle_lt_trans.
          apply H40.
          specialize (H33 x0).
          cut_to H33; try lia.
          rewrite Rminus_0_r, Rabs_right in H33.
          - apply H33.
          - apply Rle_ge.
            apply Rmult_le_pos; try lra.
            left; apply cond_pos.
        }
        revert H31.
        apply almost_impl.
        specialize (lim_w_0 n pf).
        revert lim_w_0.
        apply almost_impl.
        apply all_almost; intros ???.
        generalize (is_lim_seq_plus' _ _ _ _ H32 H31).
        rewrite Rplus_0_r.
        apply is_lim_seq_ext.
        intros.
        rewrite H12.
        unfold vecrvplus.
        now rewrite Rvector_nth_plus.
  Qed.

  Theorem Jaakkola_alpha_beta_bounded_eventually_almost
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S N))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S N)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S N)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))} :

    0 < γ < 1 ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->
    eventually (fun k => almost prts (fun ω => forall i pf, vector_nth i pf (α k ω) <= 1)) ->          
    eventually (fun k => almost prts (fun ω => forall i pf, vector_nth i pf (β k ω) <= 1)) ->      
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (α n ω))))) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (β n ω))))) ->
     (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->

    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->        
   (exists (C : Ts -> R), 
          almost prts (fun ω => forall k, Rvector_max_abs (X k ω) <= C ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k) ))) ->
    (exists epsilon : posreal,
        eventually (fun n => forall i pf,
                        almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (vecrvnth i pf (β (nn+n)%nat)) ω))) (const epsilon))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
  Proof.
    intros.
    assert (Fx_sub: forall x, sa_sub (F 0%nat) (F x)).
    {
      induction x.
      - apply sa_equiv_sub.
        reflexivity.
      - rewrite IHx.
        apply isfilt.
    }
    destruct H2 as [? H2].
    destruct H3 as [? H3].
    pose (xx := (x + x0)%nat).
    pose (XX := fun n => X (n + xx)%nat).
    pose (XXF := fun n => XF (n + xx)%nat).
    pose (αα := fun n => α (n + xx)%nat).
    pose (ββ := fun n => β (n + xx)%nat).
    assert (isfilt_FF :IsFiltration (fun n => F (n + xx)%nat)).
    {
      unfold IsFiltration.
      intros.
      replace (S n + xx)%nat with (S (n + xx)) by lia.
      apply isfilt.
    }
    assert (filtsub_FF: forall k, sa_sub (F (k + xx)%nat) dom).
    {
      intros.
      apply filt_sub.
    }
    assert (adapt_aa: IsAdapted (Rvector_borel_sa (S N)) αα (fun n => F (n + xx)%nat)).
    {
      intros ?.
      apply adapt_alpha.
    }
    assert (adapt_bb: IsAdapted (Rvector_borel_sa (S N)) ββ (fun n => F (n + xx)%nat)).    
    {
      intros ?.
      apply adapt_beta.
    }
    assert (rv_XX0: RandomVariable (F (xx)) (Rvector_borel_sa (S N)) (XX 0%nat)).
    {
      unfold XX.
      induction xx.
      - now simpl.
      - simpl.
        rewrite H12.
        simpl in IHxx.
        cut_to IHxx; trivial.
        + apply Rvector_plus_rv.
          * apply Rvector_minus_rv.
            -- now apply (RandomVariable_sa_sub (isfilt xx)).
            -- apply Rvector_mult_rv.
               ++ now apply (RandomVariable_sa_sub (isfilt xx)).
               ++ now apply (RandomVariable_sa_sub (isfilt xx)).
          * apply Rvector_mult_rv.
            -- now apply (RandomVariable_sa_sub (isfilt xx)).   
            -- apply rvXF.
        + unfold IsFiltration.
          intros.
          apply isfilt.
        + intros ?.
          apply adapt_alpha.
        + intros ?.
          apply adapt_beta.
    }
    assert (rvXXF: forall k : nat, RandomVariable (F (S k + xx)%nat) (Rvector_borel_sa (S N)) (XXF k)).
    {
      intros.
      unfold XXF.
      replace (S k + xx)%nat with (S (k + xx)) by lia.
      apply rvXF.
    }
    assert (rvXXF_I:  forall (k i : nat) (pf : (i < S N)%nat), RandomVariable dom borel_sa (vecrvnth i pf (XXF k))).
    {
      intros.
      apply rvXF_I.
    }
    assert (isfe_XXF : forall (k i : nat) (pf : (i < S N)%nat), IsFiniteExpectation prts (vecrvnth i pf (XXF k))).
    {
      intros.
      apply isfe.
    }
    generalize (Jaakkola_alpha_beta_bounded γ XX XXF αα ββ isfilt_FF (fun k => filt_sub (k + xx)%nat) adapt_aa adapt_bb H); intros jak_bound.
    cut_to jak_bound; trivial.
    cut_to jak_bound.
    - revert jak_bound; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H14 i pf).
      unfold XX in H14.
      now apply is_lim_seq_incr_n with (N := xx).
    - destruct H13 as [eps H13].
      exists eps.
      unfold ββ.
      destruct H13 as [NN ?].
      exists NN.
      intros.
      specialize (H13 (n + xx)%nat).
      cut_to H13; try lia.
      specialize (H13 i pf).
      revert H13.
      apply almost_impl.
      apply all_almost; intros ??.
      eapply Rbar_le_lt_trans; cycle 1.
      apply H13.
      apply slln.eq_Rbar_le.
      apply Lim_seq_ext.
      intros.
      apply sum_n_ext.
      intros.
      now replace  (n1 + (n + xx))%nat with (n1 + n + xx)%nat by lia.
    - unfold αα.
      apply almost_forall.
      intros.
      apply forall_almost with (n := (n+xx)%nat) in H0.
      revert H0; apply almost_impl.
      specialize (H2 (n + xx)%nat).
      cut_to H2; try lia.
      revert H2; apply almost_impl.
      apply all_almost; intros ???.
      intros.
      split.
      + apply H2.
      + apply H0.
    - unfold ββ.
      apply almost_forall.
      intros.
      apply forall_almost with (n := (n+xx)%nat) in H1.
      revert H1; apply almost_impl.
      specialize (H3 (n + xx)%nat).
      cut_to H3; try lia.
      revert H3; apply almost_impl.
      apply all_almost; intros ???.
      intros.
      split.
      + apply H3.
      + apply H1.
    - apply almost_forall.
      intros.
      apply forall_almost with (n := (n+xx)%nat) in H4.
      revert H4; apply almost_impl.
      apply all_almost; intros ??.
      apply H4.
    - revert H5; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H5 i pf).
      apply is_lim_seq_sum_shift_inf with (N := xx) in H5.
      apply H5.
    - revert H6; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H6 i pf).
      now apply is_lim_seq_sum_shift_inf with (N := xx) in H6.
    - intros.
      specialize (H7 i pf).
      revert H7; apply almost_impl.
      apply all_almost; intros ??.
      unfold αα.
      rewrite ex_series_incr_n with (n := xx) in H7.
      revert H7.
      apply ex_series_ext.
      intros.
      now replace (xx + n)%nat with (n + xx)%nat by lia.
    - intros.
      specialize (H8 i pf).
      revert H8; apply almost_impl.
      apply all_almost; intros ??.
      unfold ββ.
      rewrite ex_series_incr_n with (n := xx) in H8.
      revert H8.
      apply ex_series_ext.
      intros.
      now replace (xx + n)%nat with (n + xx)%nat by lia.
    - revert H9; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H9 (k + xx)%nat i pf).
      eapply Rle_trans; cycle 1.
      apply H9.
      unfold XXF.
      right.
      f_equal.
      now apply FiniteConditionalExpectation_ext.
    - destruct H10 as [? [??]].
      exists x1.
      split; trivial.
      revert H14; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      unfold XX, XXF.
      specialize (H14 (k + xx)%nat i pf).
      eapply Rbar_le_trans; cycle 1.
      apply H14.
      apply slln.eq_Rbar_le.
      apply ConditionalExpectation_ext; intros ?.
      unfold rvsqr, rvminus, rvplus, rvopp, rvscale.
      do 3 f_equal.
      apply FiniteConditionalExpectation_ext; reflexivity.
    - clear jak_bound.
      destruct H11 as [? ?].
      exists x1.
      revert H11; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      apply H11.
    - intros.
      unfold XX, αα, ββ, XX, XXF.
      replace (S k + xx)%nat with (S (k + xx))%nat by lia.
      now rewrite H12.
  Qed.

   Theorem Jaakkola_alpha_beta_bounded_uniformly
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S N))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S N)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S N)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))} : 
    0 < γ < 1 ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->

    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        


    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->

     (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->

    (forall i pf,
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω)))) ->
    (forall i pf, 
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (vecrvnth i pf (β k)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (vecrvnth i pf (β k)) ω)))) ->
    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->
   (exists (C : Ts -> R), 
          almost prts (fun ω => forall k, Rvector_max_abs (X k ω) <= C ω)) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k) ))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
     Proof.
       intros.
       apply (Jaakkola_alpha_beta_bounded_eventually_almost γ X XF α β isfilt filt_sub adapt_alpha adapt_beta); trivial.
       - assert (forall i pf,
                      eventually (fun n => almostR2 prts Rle  (vecrvnth i pf (α n)) (const 1))).
         {
           intros.
           assert (forall n : nat, almostR2 prts Rle (const 0) (vecrvnth i pf (α n))).
           {
             intros.
             apply forall_almost with (n:= n) in H0.
             apply bounded_forall_almost with (n := i) (pf := pf) in H0.
             - apply H0.
             - intros.
               apply lt_dec.
             - intros.
               erewrite vector_nth_ext; try apply H11.
           }
           destruct ( uniform_converge_sq _ H11 ( uniform_converge_sum_sq _ (H6 i pf))).
           exists x.
           apply H12.
         }
         apply eventually_bounded_forall in H11.
         revert H11.
         apply eventually_impl.
         apply all_eventually; intros.
         apply  almost_bounded_forall.
         + intros; apply lt_dec.
         + intros.
           erewrite vector_nth_ext; try apply H12.
         + apply H11.
       - assert (forall i pf,
                      eventually (fun n => almostR2 prts Rle  (vecrvnth i pf (β n)) (const 1))).
         {
           intros.
           assert (forall n : nat, almostR2 prts Rle (const 0) (vecrvnth i pf (β n))).
           {
             intros.
             apply forall_almost with (n:= n) in H1.
             apply bounded_forall_almost with (n := i) (pf := pf) in H1.
             - apply H1.
             - intros.
               apply lt_dec.
             - intros.
               erewrite vector_nth_ext; try apply H11.
           }
           destruct ( uniform_converge_sq _ H11 ( uniform_converge_sum_sq _ (H7 i pf))).
           exists x.
           apply H12.
         }
         apply eventually_bounded_forall in H11.
         revert H11.
         apply eventually_impl.
         apply all_eventually; intros.
         apply  almost_bounded_forall.
         + intros; apply lt_dec.
         + intros.
           erewrite vector_nth_ext; try apply H12.
         + apply H11.
       - intros.
         eapply is_lim_seq'_uniform_ex_series_almost.
         apply H6.
       - intros.
         eapply is_lim_seq'_uniform_ex_series_almost.
         apply H7.
       - assert (forall i pf,
                  exists epsilon : posreal,
                     eventually
                       (fun n : nat =>
                          almostR2 prts Rbar_lt
                            (fun ω : Ts =>
                               Lim_seq
                                 (sum_n (fun nn : nat => rvsqr (vecrvnth i pf (β (nn + n)%nat)) ω)))
                            (fun x : Ts => const epsilon x))).
         {
           intros.
           specialize (H7 i pf).
           generalize (uniform_converge_sum_sq_tails _ H7); intros.
           assert (0 < 2) by lra.
           exists (mkposreal _ H12).
           assert (0 < 1) by  lra.
           simpl in H11.
           specialize (H11 (mkposreal _ H13)).
           destruct H11.
           exists (S x).
           intros.
           specialize (H11 (n-1)%nat).
           cut_to H11; try lia.
           revert H11.
           apply almost_impl.
           apply all_almost; intros ??.
           simpl.
           simpl in H11.
           assert (Rbar_lt 1 2) by (simpl; lra).
           eapply Rbar_le_lt_trans; cycle 1.
           apply H15.
           eapply Rbar_le_trans; cycle 1.
           apply H11.
           apply slln.eq_Rbar_le.
           apply Lim_seq_ext; intros.
           apply sum_n_ext; intros.
           unfold rvsqr.
           now replace  (S (n - 1 + n1)) with (n1 + n)%nat by lia.
         }
         generalize 
           (bounded_nat_ex_choice_vector 
              (A := posreal) (n := S N)
              (fun i pf eps =>
                   eventually
            (fun n : nat =>
             almostR2 prts Rbar_lt
               (fun ω : Ts =>
                Lim_seq
                  (sum_n (fun nn : nat => rvsqr (vecrvnth i pf (β (nn + n)%nat)) ω)))
               (fun x : Ts => const eps x)))); intros.
         cut_to H12; trivial.
         destruct H12.
         pose (eps := Rvector_max_abs (vector_map pos x)).
         assert (0 < eps).
         {
           generalize (Rvector_max_abs_nth_le  (vector_map pos x) 0 (Nat.lt_0_succ _)).
           rewrite vector_nth_map.
           unfold eps.
           intros leq.
           eapply Rlt_le_trans; try eapply leq.
           destruct ((vector_nth 0 (Nat.lt_0_succ N) x)); simpl in *.
           rewrite Rabs_right; lra.
         }
         
         exists (mkposreal _ H13).
         apply eventually_bounded_forall in H12.
         revert H12.
         apply eventually_impl; apply all_eventually; intros ? HH ??.
         specialize (HH i pf).
         revert HH.
         apply almost_impl; apply all_almost; intros ??.
         eapply Rbar_lt_le_trans.
         apply H12.
         unfold const, eps; simpl.
         generalize (Rvector_max_abs_nth_le (vector_map pos x) i pf); intros.
         eapply Rle_trans; cycle 1.
         apply H14.
         rewrite vector_nth_map.
         apply Rle_abs.
     Qed.

     Lemma jaakkola_tsitsiklis_coefs1 (x : R) :
       Rsqr (1 + x) <= 3 + 3 * Rsqr (x).
     Proof.
       unfold Rsqr; ring_simplify.
       destruct (Rlt_dec x 1).
       - generalize (pow2_ge_0 x); lra.
       - assert (1 <= x) by lra.
         apply Rmult_le_compat_l with (r := x) in H; lra.         
    Qed.         
           
     Lemma jaakkola_tsitsiklis_coefs2 (x A B : nonnegreal) :
       A + B * Rsqr x <= (A + B) *  Rsqr (1 + x).
     Proof.
       unfold Rsqr; ring_simplify.
       assert (0 <= A * x ^ 2 + 2 * A * x + 2 * B * x + B).
       {
         generalize (cond_nonneg A); intros.
         generalize (cond_nonneg B); intros.
         generalize (cond_nonneg x); intros.
         generalize (pow2_ge_0 x); intros.         
         repeat apply Rplus_le_le_0_compat; try lra;  apply Rmult_le_pos; lra.
       }
       lra.
     Qed.
       
     Lemma jaakkola_tsitsiklis_coefs2_alt (x : nonnegreal) (A B : R):
       0 <= Rmax A B ->
       A + B * Rsqr x <= (Rmax A B) *  Rsqr (1 + x).
     Proof.
       intros.
       assert ((Rmax A B)*(1 + Rsqr x) <= (Rmax A B) * Rsqr ( 1 + x)).
       {
         apply Rmult_le_compat_l; trivial.
         unfold Rsqr.
         generalize (cond_nonneg x).
         lra.
       }
       eapply Rle_trans; cycle 1.
       apply H0.
       rewrite Rmult_plus_distr_l.
       apply Rplus_le_compat.
       - rewrite Rmult_1_r.
         apply Rmax_l.
       - apply Rmult_le_compat_r.
         + apply Rle_0_sqr.
         + apply Rmax_r.
    Qed.

     Lemma jaakkola_tsitsiklis_coefs2_alt2 (A B x : R):
       0 <= Rmax A B ->
       A + B * Rsqr (Rabs x) <= (Rmax A B) *  Rsqr (1 + (Rabs x)).
     Proof.
       intros.
       generalize (Rabs_pos x); intros.
       now apply (jaakkola_tsitsiklis_coefs2_alt (mknonnegreal _ H0)).
    Qed.

  Theorem Jaakkola_alpha_beta_unbounded
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S N))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S N)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S N)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))} :
    0 < γ < 1 ->
      
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <= vector_nth i pf (α k ω)) ->        

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (α n ω))))) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (β n ω))))) ->
     (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->

    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->        

    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k)))) ->
    (exists epsilon : posreal,
        eventually (fun n => forall i pf,
                        almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (vecrvnth i pf (β (nn+n)%nat)) ω))) (const epsilon))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
  Proof.
    intros.
    apply (Jaakkola_alpha_beta_bounded γ X XF α β isfilt filt_sub _ _); trivial.
    generalize (Tsitsiklis1_Jaakkola_beta_uniform γ X); intros Tsit1.
    assert (rvXF2 : forall k, RandomVariable dom (Rvector_borel_sa (S N)) (XF k)).
    {
      intros.
      now apply (RandomVariable_sa_sub (filt_sub (S k))).
    }
    assert (vecisfe: forall k, vector_IsFiniteExpectation prts (XF k)).
    {
      intros.
      now apply vector_nth_IsFiniteExpectation.
    }
    pose (XF2 := fun k =>
                   (vector_FiniteConditionalExpectation prts (filt_sub k) (XF k))).
    pose (w := fun k => vecrvminus (XF k) (XF2 k)).

    assert (rv_XF2: forall k : nat, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF2 k)).
    {
      intros.
      apply (RandomVariable_sa_sub (isfilt k)).
      apply (vector_FiniteCondexp_rv prts (filt_sub k)).
    }

    assert  (rvw : forall (k i : nat) (pf : (i < S N)%nat),
                  RandomVariable dom borel_sa
                    (fun ω : Ts => vector_nth i pf (w k ω))).
    {
      intros.
      apply vecrvnth_rv.
      unfold w.
      apply Rvector_minus_rv; trivial.
      now apply (RandomVariable_sa_sub (filt_sub (S k))).      
    }
    assert (adapt_w :IsAdapted (Rvector_borel_sa (S N)) w (fun k : nat => F (S k))).
    {
      intros ?.
      now apply Rvector_minus_rv.
    }
    specialize (Tsit1 w α β XF2 F isfilt filt_sub _ _ _ _ _ _).
    cut_to Tsit1; trivial; try lra.
    cut_to Tsit1; try lra.
    - destruct Tsit1.
      exists x.
      apply almost_forall in H11.
      revert H11; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      apply H11.
    - assert (0 <= 0) by lra.
      exists (mknonnegreal _ H11).
      revert H7; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      simpl.
      rewrite Rplus_0_r.
      rewrite Rvector_max_abs_nth_Rabs_le.
      intros.
      unfold XF2.
      rewrite vector_FiniteConditionalExpectation_nth.
      eapply Rle_trans; cycle 1.
      apply (H7 k i pf).
      right.
      f_equal.
      now apply FiniteConditionalExpectation_ext.
    - intros.
      rewrite H9.
      assert (rv_eq
                (XF k)
                (vecrvplus (XF2 k) (w k))).
      {
        unfold w.
        unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale.
        intros ?.
        rewrite Rvector_plus_assoc.
        rewrite (Rvector_plus_comm (XF2 k a)).
        rewrite <- Rvector_plus_assoc.
        rewrite <- Rvector_opp_scale.
        rewrite Rvector_plus_inv.
        now rewrite Rvector_plus_zero.
      }
      now rewrite H11.
    - intros.
      apply Condexp_cond_exp.
      unfold w.
      assert (IsFiniteExpectation prts
                (rvminus
                   (vecrvnth i pf (XF k))
                   (vecrvnth i pf (XF2 k)))).
      {
        apply IsFiniteExpectation_minus.
        - now apply vecrvnth_rv.
        - apply vecrvnth_rv.
          now apply (RandomVariable_sa_sub (filt_sub (S k))).
        - apply isfe.
        - unfold XF2.
          rewrite vector_FiniteConditionalExpectation_nth'.
          apply FiniteCondexp_isfe.
      }
      revert H11.
      apply IsFiniteExpectation_proper.
      unfold vecrvnth, vecrvminus, vecrvplus, vecrvopp, vecrvscale.
      intros ?.
      now rewrite Rvector_nth_plus, Rvector_nth_scale.
    - intros.
      unfold w.
      assert (RandomVariable dom borel_sa
                (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k)))).
      {
        apply FiniteCondexp_rv'.
      }
      generalize (condexp_condexp_diff_0 (vecrvnth i pf (XF k)) (filt_sub k)).
      apply almost_impl.
      apply all_almost; intros ??.
      rewrite <- H12.
      apply ConditionalExpectation_ext.
      intros ?.
      unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale.
      unfold vecrvnth, rvminus, rvplus, rvopp, rvscale.
      rewrite Rvector_nth_plus, Rvector_nth_scale.
      f_equal.
      f_equal.
      unfold XF2.
      rewrite vector_FiniteConditionalExpectation_nth.
      apply FiniteConditionalExpectation_ext.
      reflexivity.
    - clear Tsit1.
      destruct H8 as [C [Cpos HH]].
      pose (A:=3 * C).
      pose (B:=3 * C).
      exists A.
      exists B.
      split; [unfold A; lra |].
      split; [unfold B; lra |].
      intros.
      assert (forall ω, (C * (1 + Rvector_max_abs (X k ω)) ^ 2) <=
                     rvplus (const A)
                       (rvscale B (rvmaxlist (fun (j : nat) (ω : Ts) => rvsqr (rvmaxabs (X j)) ω) k)) ω).
      {
        assert (forall ω, (C * (1 + Rvector_max_abs (X k ω)) ^ 2) <=
                       (rvplus (const A)
                          (rvscale B (rvsqr (rvmaxabs (X k))))) ω).
        {
          intros ω.
          unfold rvsqr, rvplus, rvscale, const, rvmaxabs.
          unfold A, B.
          rewrite (Rmult_comm 3), Rmult_assoc.
          rewrite <- Rmult_plus_distr_l, <- Rsqr_pow2.
          apply Rmult_le_compat_l; try lra.
          apply jaakkola_tsitsiklis_coefs1.
        }
        intros ω.
        specialize (H8 ω).
        rewrite H8.
        unfold rvplus, rvscale.
        apply Rplus_le_compat_l.
        apply Rmult_le_compat_l.
        - unfold B; lra.
        - unfold rvmaxlist.
          apply Rmax_spec.
          apply in_map_iff.
          exists k; split; trivial.
          apply in_seq.
          lia.
      }
      Local Existing Instance Rbar_le_pre.
      transitivity  (fun ω => C * (1 + Rvector_max_abs (X k ω)) ^ 2); [| apply all_almost; intros; apply H8].
      transitivity (fun ω => (ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k)) ω)).
      + apply all_almost; intros.
        unfold  ConditionalVariance.
        unfold w.
        apply refl_refl.
        assert (eqq: rv_eq (rvsqr (vecrvnth i pf (vecrvminus (XF k) (XF2 k))))
                       (rvsqr
                          (rvminus (vecrvnth i pf (XF k))
                             (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k)))))).
        {
          intros ?.
          unfold rvsqr, vecrvnth, vecrvminus, XF2, vecrvplus, vecrvopp, rvminus, rvplus, rvopp, vecrvscale, rvscale.
          rewrite Rvector_nth_plus, Rvector_nth_scale, vector_FiniteConditionalExpectation_nth.
          do 3 f_equal.
          apply FiniteConditionalExpectation_ext; reflexivity.
        }
        now apply ConditionalExpectation_ext.
     + revert HH; apply almost_impl.
       apply all_almost; intros ??.
       simpl.
       apply H11.
  Qed.

  Theorem Jaakkola_alpha_beta_unbounded_eventually_almost
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S N))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S N)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S N)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))} :
    0 < γ < 1 ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->
    eventually (fun k => almost prts (fun ω => forall i pf, vector_nth i pf (α k ω) <= 1)) ->          
    eventually (fun k => almost prts (fun ω => forall i pf, vector_nth i pf (β k ω) <= 1)) ->      
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (α n ω))))) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (β n ω))))) ->
     (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->

    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->        

    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k) ))) ->
    (exists epsilon : posreal,
        eventually (fun n => forall i pf,
                        almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (vecrvnth i pf (β (nn+n)%nat)) ω))) (const epsilon))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
  Proof.
    intros.
    assert (Fx_sub: forall x, sa_sub (F 0%nat) (F x)).
    {
      induction x.
      - apply sa_equiv_sub.
        reflexivity.
      - rewrite IHx.
        apply isfilt.
    }
    destruct H2 as [? H2].
    destruct H3 as [? H3].
    pose (xx := (x + x0)%nat).
    pose (XX := fun n => X (n + xx)%nat).
    pose (XXF := fun n => XF (n + xx)%nat).
    pose (αα := fun n => α (n + xx)%nat).
    pose (ββ := fun n => β (n + xx)%nat).
    assert (isfilt_FF :IsFiltration (fun n => F (n + xx)%nat)).
    {
      unfold IsFiltration.
      intros.
      replace (S n + xx)%nat with (S (n + xx)) by lia.
      apply isfilt.
    }
    assert (filtsub_FF: forall k, sa_sub (F (k + xx)%nat) dom).
    {
      intros.
      apply filt_sub.
    }
    assert (adapt_aa: IsAdapted (Rvector_borel_sa (S N)) αα (fun n => F (n + xx)%nat)).
    {
      intros ?.
      apply adapt_alpha.
    }
    assert (adapt_bb: IsAdapted (Rvector_borel_sa (S N)) ββ (fun n => F (n + xx)%nat)).    
    {
      intros ?.
      apply adapt_beta.
    }
    assert (rv_XX0: RandomVariable (F (xx)) (Rvector_borel_sa (S N)) (XX 0%nat)).
    {
      unfold XX.
      induction xx.
      - now simpl.
      - simpl.
        rewrite H11.
        simpl in IHxx.
        cut_to IHxx; trivial.
        + apply Rvector_plus_rv.
          * apply Rvector_minus_rv.
            -- now apply (RandomVariable_sa_sub (isfilt xx)).
            -- apply Rvector_mult_rv.
               ++ now apply (RandomVariable_sa_sub (isfilt xx)).
               ++ now apply (RandomVariable_sa_sub (isfilt xx)).
          * apply Rvector_mult_rv.
            -- now apply (RandomVariable_sa_sub (isfilt xx)).   
            -- apply rvXF.
        + unfold IsFiltration.
          intros.
          apply isfilt.
        + intros ?.
          apply adapt_alpha.
        + intros ?.
          apply adapt_beta.
    }
    assert (rvXXF: forall k : nat, RandomVariable (F (S k + xx)%nat) (Rvector_borel_sa (S N)) (XXF k)).
    {
      intros.
      unfold XXF.
      replace (S k + xx)%nat with (S (k + xx)) by lia.
      apply rvXF.
    }
    assert (rvXXF_I:  forall (k i : nat) (pf : (i < S N)%nat), RandomVariable dom borel_sa (vecrvnth i pf (XXF k))).
    {
      intros.
      apply rvXF_I.
    }
    assert (isfe_XXF : forall (k i : nat) (pf : (i < S N)%nat), IsFiniteExpectation prts (vecrvnth i pf (XXF k))).
    {
      intros.
      apply isfe.
    }
    generalize (Jaakkola_alpha_beta_unbounded γ XX XXF αα ββ isfilt_FF (fun k => filt_sub (k + xx)%nat) adapt_aa adapt_bb H); intros jak_bound.
    cut_to jak_bound; trivial.
    - revert jak_bound; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H13 i pf).
      unfold XX in H13.
      now apply is_lim_seq_incr_n with (N := xx).
    - unfold αα.
      apply almost_forall.
      intros.
      apply forall_almost with (n := (n+xx)%nat) in H0.
      revert H0; apply almost_impl.
      specialize (H2 (n + xx)%nat).
      cut_to H2; try lia.
      revert H2; apply almost_impl.
      apply all_almost; intros ???.
      intros.
      split.
      + apply H2.
      + apply H0.
    - unfold ββ.
      apply almost_forall.
      intros.
      apply forall_almost with (n := (n+xx)%nat) in H1.
      revert H1; apply almost_impl.
      specialize (H3 (n + xx)%nat).
      cut_to H3; try lia.
      revert H3; apply almost_impl.
      apply all_almost; intros ???.
      intros.
      split.
      + apply H3.
      + apply H1.
    - apply almost_forall.
      intros.
      apply forall_almost with (n := (n+xx)%nat) in H4.
      revert H4; apply almost_impl.
      apply all_almost; intros ??.
      apply H4.
    - revert H5; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H5 i pf).
      apply is_lim_seq_sum_shift_inf with (N := xx) in H5.
      apply H5.
    - revert H6; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H6 i pf).
      now apply is_lim_seq_sum_shift_inf with (N := xx) in H6.
    - intros.
      specialize (H7 i pf).
      revert H7; apply almost_impl.
      apply all_almost; intros ??.
      unfold αα.
      rewrite ex_series_incr_n with (n := xx) in H7.
      revert H7.
      apply ex_series_ext.
      intros.
      now replace (xx + n)%nat with (n + xx)%nat by lia.
    - intros.
      specialize (H8 i pf).
      revert H8; apply almost_impl.
      apply all_almost; intros ??.
      unfold ββ.
      rewrite ex_series_incr_n with (n := xx) in H8.
      revert H8.
      apply ex_series_ext.
      intros.
      now replace (xx + n)%nat with (n + xx)%nat by lia.
    - revert H9; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H9 (k + xx)%nat i pf).
      eapply Rle_trans; cycle 1.
      apply H9.
      unfold XXF.
      right.
      f_equal.
      now apply FiniteConditionalExpectation_ext.
    - destruct H10 as [? [??]].
      exists x1.
      split; trivial.
      revert H13; apply almost_impl.
      apply all_almost; intros ??.
      intros.
      unfold XX, XXF.
      specialize (H13 (k + xx)%nat i pf).
      eapply Rbar_le_trans; cycle 1.
      apply H13.
      apply slln.eq_Rbar_le.
      apply ConditionalExpectation_ext; intros ?.
      unfold rvsqr, rvminus, rvplus, rvopp, rvscale.
      do 3 f_equal.
      apply FiniteConditionalExpectation_ext; reflexivity.
    - intros.
      unfold XX, αα, ββ, XX, XXF.
      replace (S k + xx)%nat with (S (k + xx))%nat by lia.
      now rewrite H11.
    - destruct H12 as [eps H12].
      exists eps.
      unfold ββ.
      destruct H12 as [NN ?].
      exists NN.
      intros.
      specialize (H12 (n + xx)%nat).
      cut_to H12; try lia.
      specialize (H12 i pf).
      revert H12.
      apply almost_impl.
      apply all_almost; intros ??.
      eapply Rbar_le_lt_trans; cycle 1.
      apply H12.
      apply slln.eq_Rbar_le.
      apply Lim_seq_ext.
      intros.
      apply sum_n_ext.
      intros.
      now replace  (n1 + (n + xx))%nat with (n1 + n + xx)%nat by lia.
  Qed.

   Theorem Jaakkola_alpha_beta_unbounded_uniformly
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S N))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S N)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S N)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))}:
    0 < γ < 1 ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->

    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        


    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->

     (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->
    (forall i pf,
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω)))) ->
    (forall i pf, 
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (vecrvnth i pf (β k)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (vecrvnth i pf (β k)) ω)))) ->
    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->        
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k) ))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
     Proof.
       intros.
       apply (Jaakkola_alpha_beta_unbounded_eventually_almost γ X XF α β isfilt filt_sub adapt_alpha adapt_beta); trivial.
       - assert (forall i pf,
                      eventually (fun n => almostR2 prts Rle  (vecrvnth i pf (α n)) (const 1))).
         {
           intros.
           assert (forall n : nat, almostR2 prts Rle (const 0) (vecrvnth i pf (α n))).
           {
             intros.
             apply forall_almost with (n:= n) in H0.
             apply bounded_forall_almost with (n := i) (pf := pf) in H0.
             - apply H0.
             - intros.
               apply lt_dec.
             - intros.
               erewrite vector_nth_ext; try apply H10.
           }
           destruct ( uniform_converge_sq _ H10 ( uniform_converge_sum_sq _ (H6 i pf))).
           exists x.
           apply H11.
         }
         apply eventually_bounded_forall in H10.
         revert H10.
         apply eventually_impl.
         apply all_eventually; intros.
         apply  almost_bounded_forall.
         + intros; apply lt_dec.
         + intros.
           erewrite vector_nth_ext; try apply H11.
         + apply H10.
       - assert (forall i pf,
                      eventually (fun n => almostR2 prts Rle  (vecrvnth i pf (β n)) (const 1))).
         {
           intros.
           assert (forall n : nat, almostR2 prts Rle (const 0) (vecrvnth i pf (β n))).
           {
             intros.
             apply forall_almost with (n:= n) in H1.
             apply bounded_forall_almost with (n := i) (pf := pf) in H1.
             - apply H1.
             - intros.
               apply lt_dec.
             - intros.
               erewrite vector_nth_ext; try apply H10.
           }
           destruct ( uniform_converge_sq _ H10 ( uniform_converge_sum_sq _ (H7 i pf))).
           exists x.
           apply H11.
         }
         apply eventually_bounded_forall in H10.
         revert H10.
         apply eventually_impl.
         apply all_eventually; intros.
         apply  almost_bounded_forall.
         + intros; apply lt_dec.
         + intros.
           erewrite vector_nth_ext; try apply H11.
         + apply H10.
       - intros.
         eapply is_lim_seq'_uniform_ex_series_almost.
         apply H6.
       - intros.
         eapply is_lim_seq'_uniform_ex_series_almost.
         apply H7.
       - assert (forall i pf,
                  exists epsilon : posreal,
                    eventually
                      (fun n : nat =>
                         almostR2 prts Rbar_lt
                           (fun ω : Ts =>
                              Lim_seq
                                (sum_n (fun nn : nat => rvsqr (vecrvnth i pf (β (nn + n)%nat)) ω)))
                           (fun x : Ts => const epsilon x))).
         {
           intros.
           specialize (H7 i pf).
           generalize (uniform_converge_sum_sq_tails _ H7); intros.
           assert (0 < 2) by lra.
           exists (mkposreal _ H11).
           assert (0 < 1) by  lra.
           simpl in H10.
           specialize (H10 (mkposreal _ H12)).
           destruct H10.
           exists (S x).
           intros.
           specialize (H10 (n-1)%nat).
           cut_to H10; try lia.
           revert H10.
           apply almost_impl.
           apply all_almost; intros ??.
           simpl.
           simpl in H10.
           assert (Rbar_lt 1 2) by (simpl; lra).
           eapply Rbar_le_lt_trans; cycle 1.
           apply H14.
           eapply Rbar_le_trans; cycle 1.
           apply H10.
           apply slln.eq_Rbar_le.
           apply Lim_seq_ext; intros.
           apply sum_n_ext; intros.
           unfold rvsqr.
           now replace  (S (n - 1 + n1)) with (n1 + n)%nat by lia.
         }
         generalize 
           (bounded_nat_ex_choice_vector 
              (A := posreal) (n := S N)
              (fun i pf eps =>
                   eventually
            (fun n : nat =>
             almostR2 prts Rbar_lt
               (fun ω : Ts =>
                Lim_seq
                  (sum_n (fun nn : nat => rvsqr (vecrvnth i pf (β (nn + n)%nat)) ω)))
               (fun x : Ts => const eps x)))); intros.
         cut_to H11; trivial.
         destruct H11.
         pose (eps := Rvector_max_abs (vector_map pos x)).
         assert (0 < eps).
         {
           generalize (Rvector_max_abs_nth_le  (vector_map pos x) 0 (Nat.lt_0_succ _)).
           rewrite vector_nth_map.
           unfold eps.
           intros leq.
           eapply Rlt_le_trans; try eapply leq.
           destruct ((vector_nth 0 (Nat.lt_0_succ N) x)); simpl in *.
           rewrite Rabs_right; lra.
         } 
         exists (mkposreal _ H12).
         apply eventually_bounded_forall in H11.
         revert H11.
         apply eventually_impl; apply all_eventually; intros ? HH ??.
         specialize (HH i pf).
         revert HH.
         apply almost_impl; apply all_almost; intros ??.
         eapply Rbar_lt_le_trans.
         apply H11.
         unfold const, eps; simpl.
         generalize (Rvector_max_abs_nth_le (vector_map pos x) i pf); intros.
         eapply Rle_trans; cycle 1.
         apply H13.
         rewrite vector_nth_map.
         apply Rle_abs.
    Qed.

     Lemma pos_scaled_vec_isfincondexp {n} (W : vector posreal n) (dom2 : SigmaAlgebra Ts) (sub : sa_sub dom2 dom) 
       (f : Ts -> vector R n)
       {rv : RandomVariable dom (Rvector_borel_sa n) f}
       {isfe : vector_IsFiniteExpectation prts f} :
       vector_IsFiniteExpectation prts (fun ω => pos_Rvector_mult (f ω) W).
     Proof.
       apply vector_nth_IsFiniteExpectation.
       intros.
       assert (IsFiniteExpectation prts (rvscale (vector_nth i pf W) (vecrvnth i pf f))).
       {
         apply IsFiniteExpectation_scale.
         now apply vector_IsFiniteExpectation_nth with (i := i) (pf := pf) in isfe.
       }
       revert H.
       apply IsFiniteExpectation_proper.
       intros ?.
       unfold vecrvnth, rvscale, pos_Rvector_mult.
       now rewrite Rvector_nth_mult, vector_nth_map, Rmult_comm.
     Qed.

     Lemma pos_scaled_fincondexp_nth {n} (W : vector posreal n) {dom2 : SigmaAlgebra Ts} (sub : sa_sub dom2 dom) 
       (f : Ts -> vector R n)
       {rv : RandomVariable dom (Rvector_borel_sa n) f}
       {isfe : vector_IsFiniteExpectation prts f} 
       {isfe2 : vector_IsFiniteExpectation prts (fun ω => pos_Rvector_mult (f ω) W)} : 
       forall i pf,
         almostR2 prts eq
           (fun ω => FiniteConditionalExpectation prts sub (fun ω => vector_nth i pf (pos_Rvector_mult (f ω) W)) ω)
           (rvscale (vector_nth i pf W) (FiniteConditionalExpectation prts sub (vecrvnth i pf f) ) ).
      Proof.
         intros.
         generalize (FiniteCondexp_scale prts sub (vector_nth i pf W) (vecrvnth i pf f)); intros.
         apply almost_prob_space_sa_sub_lift in H.
         revert H.
         apply almost_impl.
         apply all_almost; intros ??.
         rewrite <- H.
         apply FiniteConditionalExpectation_ext.
         intros ?.
         unfold pos_Rvector_mult, rvscale, vecrvnth.
         now rewrite Rvector_nth_mult, vector_nth_map, Rmult_comm.
      Qed.

     Lemma pos_scaled_vec_fincondexp {n} (W : vector posreal n) {dom2 : SigmaAlgebra Ts} (sub : sa_sub dom2 dom) 
       (f : Ts -> vector R n)
       {rv : RandomVariable dom (Rvector_borel_sa n) f}
       {isfe : vector_IsFiniteExpectation prts f} 
       {isfe2 : vector_IsFiniteExpectation prts (fun ω => pos_Rvector_mult (f ω) W)} :
       almostR2 prts eq
         (fun ω => pos_scaled_Rvector_max_abs
                     (vector_FiniteConditionalExpectation prts sub f ω) W) 
         (fun ω => Rvector_max_abs
                     ((vector_FiniteConditionalExpectation prts sub (fun ω => pos_Rvector_mult (f ω) W)) ω)).
     Proof.
       generalize (pos_scaled_fincondexp_nth W sub f); intros.
       apply almost_bounded_forall in H.
       - revert H; apply almost_impl.
         apply all_almost; intros ??.
         unfold pos_scaled_Rvector_max_abs.
         f_equal.
         unfold pos_Rvector_mult.
         apply vector_nth_eq.
         intros.
         rewrite Rvector_nth_mult, vector_nth_map.
         rewrite vector_FiniteConditionalExpectation_nth.
         rewrite vector_FiniteConditionalExpectation_nth.         
         unfold pos_Rvector_mult in H.
         unfold vecrvnth.
         rewrite H.
         unfold rvscale.
         now rewrite Rmult_comm.
       - intros.
         apply lt_dec.
       - intros.
         assert (FiniteConditionalExpectation prts sub (fun ω : Ts => vector_nth i pf1 (pos_Rvector_mult (f ω) W)) x =
                   FiniteConditionalExpectation prts sub (fun ω : Ts => vector_nth i pf2 (pos_Rvector_mult (f ω) W)) x).
         {
           apply FiniteConditionalExpectation_ext.
           intros ?.
           apply vector_nth_ext.
         }
         rewrite H1 in H0.
         rewrite H0.
         unfold rvscale.
         f_equal.
         + f_equal.
           apply vector_nth_ext.
         + apply FiniteConditionalExpectation_ext.
           intros ?.
           apply vector_nth_ext.
     Qed.
     
 Theorem Jaakkola_alpha_beta_unbounded_uniformly_W (W : vector posreal (S N))
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S N))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S N)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S N)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF k)} 
    {vec_rvXF_I : forall k, RandomVariable dom (Rvector_borel_sa (S N)) (XF k)}
    {vec_isfe : forall k, vector_IsFiniteExpectation prts (XF k)} :

    0 < γ < 1 ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->

    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->

    almost prts 
      (fun ω =>
         (forall k,
             (scaled_norm((vector_FiniteConditionalExpectation _ (filt_sub k) (XF k)) ω) W) <
               (γ * (scaled_norm(X k ω) W))))  ->
    (forall i pf,
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω)))) ->
    (forall i pf, 
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (vecrvnth i pf (β k)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (vecrvnth i pf (β k)) ω)))) ->
    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + scaled_norm(X k ω) W)^2)))) ->        
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k) ))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
Proof.
  intros.
  pose (X' := fun n ω => pos_Rvector_mult (X n ω) W).
  pose (XF' := fun n ω => pos_Rvector_mult (XF n ω) W).  
  generalize (Jaakkola_alpha_beta_unbounded_uniformly γ X' XF' α β isfilt filt_sub); intros jaak.
  assert (rv'': forall k : nat, RandomVariable (F (S k)) (Rvector_borel_sa (S N)) (XF' k)).
  {
    intros.
    apply Rvector_mult_rv; trivial.
    apply rvconst.
  }
  assert (RandomVariable (F 0%nat) (Rvector_borel_sa (S N)) (X' 0%nat)).
  {
    apply Rvector_mult_rv; trivial.
    apply rvconst.
  }
  cut_to jaak; trivial.
  assert  (rvXF_I' : forall (k i : nat) (pf : (i < S N)%nat), RandomVariable dom borel_sa (vecrvnth i pf (XF' k))).
  {
    intros.
    apply vecrvnth_rv.
    unfold XF'.
    apply Rvector_mult_rv.
    - now apply (RandomVariable_sa_sub (filt_sub (S k))).
    - apply rvconst.
  }
  assert (isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))).
  {
    intros.
    now apply vector_IsFiniteExpectation_nth.
 }
  assert (isfe' : forall (k i : nat) (pf : (i < S N)%nat), IsFiniteExpectation prts (vecrvnth i pf (XF' k))).
  {
    intros.
    unfold XF', pos_Rvector_mult.
    assert (IsFiniteExpectation prts (fun ω => (vector_nth i pf W) * (vector_nth i pf (XF k ω)))).
    {
      apply IsFiniteExpectation_scale.
      apply isfe.
    }
    revert H11.
    apply IsFiniteExpectation_proper.
    intros ?.
    unfold vecrvnth.
    rewrite Rvector_nth_mult, vector_nth_map; lra.
  }
  assert (rv_XF'_sq :forall (k i : nat) (pf : (i < S N)%nat),
          RandomVariable dom borel_sa
            (rvsqr
               (rvminus (vecrvnth i pf (XF' k))
                  (FiniteConditionalExpectation prts (filt_sub k)
                     (vecrvnth i pf (XF' k)))))).
  {
    intros.
    apply rvsqr_rv.
    apply rvminus_rv.
    - apply vecrvnth_rv.
      now apply (RandomVariable_sa_sub (filt_sub (S k))).
    - apply (RandomVariable_sa_sub (filt_sub k)).
      apply FiniteCondexp_rv.
  }
  specialize (jaak _ _ H H0 H1 H2 H3 H4).
  assert
     (almost prts
           (fun ω : Ts =>
            forall (k i : nat) (pf : (i < S N)%nat),
            Rabs
              (FiniteConditionalExpectation prts (filt_sub k)
                 (vecrvnth i pf (XF' k)) ω) <= γ * Rvector_max_abs (X' k ω))).
  {
    assert (forall k, vector_IsFiniteExpectation prts (XF' k)).
    {
      intros.
      now apply vector_nth_IsFiniteExpectation.
    }
    assert (forall k,
        vector_IsFiniteExpectation prts
          (fun ω : Ts => pos_Rvector_mult (XF k ω) W)).
    {
      intros.
      apply vector_nth_IsFiniteExpectation.
      intros.
      specialize (H11 k).
      apply vector_IsFiniteExpectation_nth with (i := i) (pf := pf) in H11.
      revert H11.
      apply IsFiniteExpectation_proper.
      intros ?.
      reflexivity.
   }
    generalize (fun k => pos_scaled_vec_fincondexp W (filt_sub k) (XF k)); intros.
    apply almost_forall in H13.
    revert H13; apply almost_impl.
    revert H5; apply almost_impl.
    apply all_almost; intros ω??.
    intros.
    clear H0 H1 H2 H3 H4 jaak.
    specialize (H5 k).
    generalize (vector_FiniteConditionalExpectation_nth prts (filt_sub k) (XF' k)); intros.
    specialize (H0 i pf ω).
    replace (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF' k)) ω) with
      (vector_nth i pf (vector_FiniteConditionalExpectation prts (filt_sub k) (XF' k) ω)).
    - eapply Rle_trans.
      apply Rvector_max_abs_nth_le.
      left.
      eapply Rle_lt_trans; cycle 1.
      apply H5.
      right.
      f_equal.
      unfold XF'.
      unfold pre_inter_of_collection in H13.
      now rewrite H13.
    - rewrite vector_FiniteConditionalExpectation_nth.
      now apply FiniteConditionalExpectation_ext.
  }
  specialize (jaak H11 H6 H7).
  assert (exists C : R,
             0 < C /\
               almost prts
                 (fun ω : Ts =>
                    forall (k i : nat) (pf : (i < S N)%nat),
                      Rbar_le
                        (ConditionalVariance prts (filt_sub k) 
                           (vecrvnth i pf (XF' k)) ω)
                        (C * (1 + Rvector_max_abs (X' k ω)) ^ 2))).
  {
    clear H0 H1 H2 H3 H4 H5 jaak.
    destruct H8 as [C [Cpos HH]].
    assert (forall k i pf,
               rv_eq (vecrvnth i pf (XF' k))
                  (rvscale (vector_nth i pf W) (vecrvnth i pf (XF k)))).
    {
      intros k i pf ω.
      unfold XF', pos_Rvector_mult, vecrvnth, rvscale.
      now rewrite Rvector_nth_mult, vector_nth_map, Rmult_comm.
    }
    assert (forall i pf,
               (exists C : R,
                   0 < C /\
                     almost prts (fun ω =>
                               forall (k : nat),
                                 Rbar_le
                                   (ConditionalVariance prts (filt_sub k) 
                                      (vecrvnth i pf (XF' k)) ω)
                                   (C * (1 + Rvector_max_abs (X' k ω)) ^ 2)))).
    {
      intros.
      exists (C * Rsqr (vector_nth i pf W)).
      split.
      - apply Rmult_lt_0_compat; trivial.
        apply Rsqr_pos_lt.
        generalize (cond_pos (vector_nth i pf W)); lra.
      - apply almost_forall.
        intros k.
        generalize (ConditionalVariance_scale prts (filt_sub k) 
                      (vector_nth i pf W) (vecrvnth i pf (XF k))); intros.
        apply almost_prob_space_sa_sub_lift in H1.
        revert H1; apply almost_impl.
        revert HH; apply almost_impl.
        apply all_almost; intros ???.
        assert (rv_eq  (vecrvnth i pf (XF' k))
                       (rvscale (vector_nth i pf W) (vecrvnth i pf (XF k)))).
        {
          intros ?.
          unfold rvscale, XF', vecrvnth, pos_Rvector_mult.
          now rewrite Rvector_nth_mult, vector_nth_map, Rmult_comm.
        }
        specialize (H1 k i pf).
        assert (Rbar_le (Rbar_rvscale (vector_nth i pf W)²
                           (ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) x)
                  (C * (vector_nth i pf W)² * (1 + Rvector_max_abs (X' k x)) ^ 2)).
        {
          unfold Rbar_rvscale.
          apply Rbar_le_pos_compat_l with (c := (vector_nth i pf W)²) in H1.
          - replace  (scaled_norm(X k x) W) with
              (Rvector_max_abs (X' k x)) in H2 by reflexivity.
            rewrite (Rmult_comm C), Rmult_assoc.
            eapply Rbar_le_trans; cycle 1.
            apply H1.
            apply slln.eq_Rbar_le.
            f_equal.
            now apply ConditionalVariance_ext.
          - apply Rle_0_sqr.
        }
        eapply Rbar_le_trans; cycle 1.
        apply H4.
        rewrite <- H2.
        apply slln.eq_Rbar_le.
        now apply ConditionalVariance_ext.
    }
    generalize 
      (bounded_nat_ex_choice_vector 
         (A := R) (n := S N)
         (fun i pf C =>
            0 < C /\
              almost prts
                        (fun ω : Ts =>
                           forall k : nat,
                             Rbar_le 
                               (ConditionalVariance prts (filt_sub k) 
                                (vecrvnth i pf (XF' k)) ω) 
                               (C * (1 + Rvector_max_abs (X' k ω)) ^ 2)))); intros.
    cut_to H2.
    - destruct H2.
      exists (Rvector_max_abs x).
      split.
      + assert (0 < S N)%nat by lia.
        destruct (H2 0%nat H3).
        eapply Rlt_le_trans.
        apply H2.
        eapply Rle_trans; cycle 1.
        apply Rvector_max_abs_nth_le with (i := 0%nat) (pf := H3).
        apply Rle_abs.
      + apply almost_forall; intros.
        apply almost_bounded_forall; intros.
        * apply lt_dec.
        * eapply Rbar_le_trans; cycle 1.
          apply H3.
          apply slln.eq_Rbar_le.
          apply ConditionalVariance_ext.
          intros ?.
          apply vector_nth_ext.
       * specialize (H2 n0 pf).
         destruct H2.
         revert H3; apply almost_impl.
         apply all_almost; intros ??.
         specialize (H3 n).
         eapply Rbar_le_trans.
         apply H3.
         simpl.
         apply Rmult_le_compat_r.
         -- apply pow2_ge_0.
         -- eapply Rle_trans; cycle 1.
            apply Rvector_max_abs_nth_le with (i := n0) (pf := pf).
            apply Rle_abs.
    - intros.
      apply H1.
  }
  specialize (jaak H12).
  cut_to jaak; trivial.
  - revert jaak.
    apply almost_impl.
    apply all_almost; intros ??.
    intros.
    specialize (H13 i pf).
    unfold X' in H13.
    unfold pos_Rvector_mult in H13.
    assert (is_lim_seq (fun m => (vector_nth i pf W) * vector_nth i pf (X m x)) 0).
    {
      revert H13.
      apply is_lim_seq_ext.
      intros.
      rewrite Rvector_nth_mult, vector_nth_map; lra.
    }
    apply is_lim_seq_scal_l with (a := Rinv_mkpos (vector_nth i pf W)) in H14.
    rewrite Rbar_mult_0_r in H14.
    revert H14.
    apply is_lim_seq_ext.
    intros.
    unfold Rinv_mkpos.
    simpl.
    rewrite <- Rmult_assoc.
    rewrite Rinv_l, Rmult_1_l; try lra.
    generalize (cond_pos (vector_nth i pf W)).
    lra.
  - intros.
    unfold X'.
    intros ?.
    rewrite H9.
    unfold pos_Rvector_mult, vecrvminus, vecrvplus, vecrvmult, vecrvopp, vecrvscale.
    repeat rewrite Rvector_mult_plus_distr_r.
    f_equal.
    + f_equal.
      rewrite Rvector_scale_mult_l.
      f_equal.
      now rewrite Rvector_mult_assoc.
    + unfold XF', pos_Rvector_mult.
      now rewrite Rvector_mult_assoc.      
 Qed.

  Lemma is_lim_alpha_inf (α β : nat -> Ts -> vector R (S N)) :
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty).
  Proof.
    intros ?.
    apply almost_impl.
    revert H; apply almost_impl.
    apply all_almost; intros ???.
    intros.
    specialize (H0 i pf).
    revert H0.
    apply is_lim_seq_le_p_loc.
    exists (0%nat).
    intros.
    apply sum_n_le_loc.
    intros.
    apply H.
  Qed.

  Lemma ex_series_beta (α β : nat -> Ts -> vector R (S N)) :
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (α n ω))))) ->
    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (β n ω))))).
    Proof.
      intros.
      specialize (H1 i pf).
      revert H1; apply almost_impl.
      revert H0; apply almost_impl.
      revert H; apply almost_impl.
      apply all_almost; intros ????.
      revert H1.
      apply ex_series_nneg_bounded.
      - intros.
        apply Rle_0_sqr.
      - intros.
        apply Rsqr_le_abs_1.
        rewrite Rabs_right.
        rewrite Rabs_right.
        + apply H0.
        + apply Rle_ge.
          eapply Rle_trans.
          apply H.
          apply H0.
        + apply Rle_ge.
          apply H.
   Qed.


 Instance vec_rvXF_I
   {F : nat -> SigmaAlgebra Ts} 
   (filt_sub : forall k, sa_sub (F k) dom) 
   (XF : nat -> Ts -> vector R N)
   {rvXF : IsAdapted (Rvector_borel_sa N) XF (fun k => F (S k))} :
   forall k, RandomVariable dom (Rvector_borel_sa N) (XF k).
  Proof.
    intros.
    now apply (RandomVariable_sa_sub (filt_sub (S k))).
  Qed.

End jaakola_vector2.

Section SN.

Context {Ts : Type} {SS:Type} (N:nat)
        {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

 Theorem Jaakkola_alpha_unbounded_N
    (γ : R) 
    (X XF α : nat -> Ts -> vector R N)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa N) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa N) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa N) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))} :
    0 < γ < 1 ->
      
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

    (forall i pf, almost prts (fun ω => ex_series (fun n => Rsqr (vector_nth i pf (α n ω))))) ->

     (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->

    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->        

    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (α k) (XF k)))) ->
    (exists epsilon : posreal,
        eventually (fun n => forall i pf,
                        almostR2 prts Rbar_lt (fun ω => Lim_seq (sum_n (fun nn => rvsqr (vecrvnth i pf (α (nn+n)%nat)) ω))) (const epsilon))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
   Proof.
     intros.
     destruct N.
     - apply all_almost; intros.
       assert (is_lim_seq (fun m => 0) 0) by apply is_lim_seq_const.
       revert H7.
       apply is_lim_seq_ext.
       lia.
     - apply Jaakkola_alpha_beta_unbounded with (γ := γ) (XF := XF) (α := α) (β := α)
                                                (filt_sub := filt_sub) (rvXF_I := rvXF_I) (isfe := isfe); trivial.
        apply all_almost; intros.
        now right.
   Qed.

  Theorem Jaakkola_alpha_unbounded_uniformly_N
    (γ : R) 
    (X XF α : nat -> Ts -> vector R N)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa N) α F)
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa N) (X 0%nat)}
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa N) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))} :
    0 < γ < 1 ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->

    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->

     (almost prts
            (fun ω =>
               forall k i pf,
                 Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <= (γ * (Rvector_max_abs (X k ω))))) ->

     (forall i pf,
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (vecrvnth i pf (α k)) ω)))) ->

    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
                     (C * (1 + Rvector_max_abs (X k ω))^2)))) ->        

    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (α k) (XF k) ))) ->

        almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
   Proof.
     intros.
     destruct N.
     - apply all_almost; intros.
       assert (is_lim_seq (fun m => 0) 0) by apply is_lim_seq_const.
       revert H6.
       apply is_lim_seq_ext.
       lia.
     - apply Jaakkola_alpha_beta_unbounded_uniformly with (γ := γ) (XF := XF) (α := α) (β := α)
                                                (filt_sub := filt_sub) (rvXF_I := rvXF_I) (isfe := isfe); trivial.
        apply all_almost; intros.
        now right.
   Qed.

    Theorem Jaakkola_alpha_beta_unbounded_uniformly_W_final
      (W : vector posreal N)
      (X XF α β : nat -> Ts -> vector R N)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F) 
      (filt_sub : forall k, sa_sub (F k) dom) 
      (adapt_alpha : IsAdapted (Rvector_borel_sa N) α F)
      (adapt_beta : IsAdapted (Rvector_borel_sa N) β F)    
      {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa N) (X 0%nat)}
      {vec_isfe : forall k, vector_IsFiniteExpectation prts (XF k)} 
      {rvXF : IsAdapted (Rvector_borel_sa N) XF (fun k => F (S k))} :
      
   (**r α and β are almost always non-negative *)
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->

   (**r α is almost always less than or equal to β, component-wise  *)
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        

    (**r The sum of αs almost always increase without limit *)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    (**r The sum of βs almost always increases without limit *)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->
    
    (**r W scaled norm of conditional Expectation of XF is almost always bounded by γ * W scaled norm of X *)
    (exists (γ : R),
        0 < γ < 1 /\
          almost prts 
            (fun ω =>
               (forall k,
                   (scaled_norm((vector_FiniteConditionalExpectation prts (filt_sub k) (XF k) (rv := vec_rvXF_I N filt_sub XF k) (* (isfe := vec_isfe XF (vec_rvXF_I := vec_rvXF_I filt_sub XF) k)*) ) ω) W) <
                     (γ * (scaled_norm(X k ω) W)))))  ->

    (**r sum of α^2 converges almost always uniformly *)
    (forall i pf,
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => (vector_nth i pf (α k ω))²) n) 
          (fun ω => Lim_seq (sum_n (fun k => (vector_nth i pf (α k ω))²)))) ->

    (**r sum of β^2 converges almost always uniformly *)
    (forall i pf, 
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => (vector_nth i pf (β k ω))²)  n) 
          (fun ω => Lim_seq (sum_n (fun k => (vector_nth i pf (β k ω))² )))) ->

    (**r exists C, such that conditional variance of XF is almost always bounded by C * (1 + W_scaled norm X)^2 *)
    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k i pf,
                   Rbar_le
                     ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k)) (rv := vecrvnth_rv i pf (XF k) (rv := vec_rvXF_I N filt_sub XF k))) ω)
                    (C * (1 + scaled_norm(X k ω) W)^2)))) ->        

    (**r X (k + 1) = (1 - α_κ) * Χ (k) + β_k * XF (k) defined componentwise *)
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k) ))) ->

    (**r X converges to zero almost alwaYS *)
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
    Proof.
      intros.
      destruct N.
      - apply all_almost; intros.
        assert (is_lim_seq (fun m => 0) 0) by apply is_lim_seq_const.
        revert H9.
        apply is_lim_seq_ext.
        lia.
      - destruct H4 as [γ [??]].
        apply (Jaakkola_alpha_beta_unbounded_uniformly_W n W γ X XF α β isfilt filt_sub)
          with (vec_rvXF_I := vec_rvXF_I (S n) filt_sub XF) (vec_isfe := vec_isfe); trivial.
   Qed.

End SN.

Section qlearn.

  Context {M : MDP}  (γ : R).
  Arguments t {_}.

  Context {Ts : Type}            
          {dom : SigmaAlgebra Ts}
          {prts : ProbSpace dom}
          {F : nat -> SigmaAlgebra Ts}

          (next_state : nat -> (sigT M.(act)) -> Ts -> M.(state))          
          (next_state_rv : forall t sa,
              RandomVariable (F (S t)) (discrete_sa (state M)) (next_state t sa))
          (cost : nat -> (sigT M.(act)) -> Ts -> R)          
          (cost_rv : forall t sa, RandomVariable (F (S t)) borel_sa (cost t sa))
          (islp_cost: forall t (sa : {x : state M & act M x}), IsLp prts 2 (cost t sa))          
          (Q0 : Rfct (sigT M.(act)))
          (α : nat -> Ts -> Rfct (sigT M.(act)))
          (alpha_bound : forall t ω sa, 0 <= α t ω sa <= 1)
          (rvα : forall t sa,
              RandomVariable (F t) borel_sa (fun ω => α t ω sa))
          (isfilt : IsFiltration F) 
          (filt_sub : forall k, sa_sub (F k) dom).

  Context (indep_cost: forall k sa,
              independent_sas prts (pullback_rv_sub dom borel_sa (cost k sa)
                                      (RandomVariable_sa_sub (filt_sub (S k)) _))
                (filt_sub k))
          (indep_next_state: forall k sa,
              independent_sas prts (pullback_rv_sub dom (discrete_sa (state M)) (next_state k sa) 
                                      (RandomVariable_sa_sub (filt_sub (S k)) _))
                (filt_sub k))
          (ident_distr_next_state: forall k sa,
              identically_distributed_rvs prts (discrete_sa (state M))
                (rv1 := (RandomVariable_sa_sub (filt_sub 1) _))
                (rv2 := (RandomVariable_sa_sub (filt_sub (S k)) _))
                (next_state 0%nat sa)
                (next_state k sa))
          (ident_distr_cost: forall k sa,
              identically_distributed_rvs prts borel_sa
                (rv1 := (RandomVariable_sa_sub (filt_sub 1) _))
                (rv2 := (RandomVariable_sa_sub (filt_sub (S k)) _))
                (cost 0%nat sa)
                (cost k sa)).

              
  

(*  Context {finA : FiniteType (sigT M.(act))}. *)

(*
  Let our_iso_f := iso_f (Isomorphism := FiniteTypeVector.finite_fun_vec_encoder finA EqDecsigT (B := R)).
  Let our_iso_b := iso_b (Isomorphism := FiniteTypeVector.finite_fun_vec_encoder finA EqDecsigT (B := R)).
*)

  Let our_iso_f_M := iso_f (Isomorphism := FiniteTypeVector.finite_fun_vec_encoder (act_finite M) EqDecsigT (B := R)).
  Let our_iso_b_M := iso_b (Isomorphism := FiniteTypeVector.finite_fun_vec_encoder (act_finite M) EqDecsigT (B := R)).

  Theorem Jaakkola_alpha_fintype
    (X : nat -> Ts -> Rfct (sigT M.(act)))
    (XF : nat -> Ts -> Rfct (sigT M.(act)))
    (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F) 
    {rvX0 : forall sa, RandomVariable (F 0%nat) borel_sa (fun ω => X 0%nat ω sa)}
    (adapt_XF : forall sa, IsAdapted borel_sa (fun t ω => XF t ω sa) (fun k => F (S k)))
    {rvXF : forall k sa, RandomVariable dom borel_sa (fun ω => XF k ω sa)}
    {isfe : forall k sa, IsFiniteExpectation prts (fun ω => XF k ω sa)} :
    almost prts (fun ω => forall k sa, 0 <= α k ω sa <= 1) ->
    almost prts (fun ω => forall sa, is_lim_seq (sum_n (fun k => α k ω sa)) p_infty) ->
    almost prts (fun ω => forall sa ω, ex_series (fun k : nat => Rsqr (α k ω sa))) ->

    (almost prts
       (fun ω =>
          forall k sa,
            Rabs ((FiniteConditionalExpectation _ (filt_sub k) (fun ω => XF k ω sa)) ω) <= (γ * (Rmax_norm _ (X k ω))))) ->
    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k sa,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (fun ω => XF k ω sa)) ω)
                     (C * (1 + Rmax_norm _ (X k ω))^2)))) ->       
    0 < γ < 1 ->
(*    
     (forall k x, Rmax_norm _ (Rfct_minus _ (XF k x) x') <= β * Rmax_norm _ (Rfct_minus _ x x')) ->
*)
    (forall k ω sa, X (S k) ω sa = 
                    (X k ω sa) +  ((α k ω sa) * (((XF k ω sa) - (X k ω sa) ) ))) ->
    (*    almost prts (fun ω => is_lim_seq (fun n => Rmax_norm _ (Rfct_minus _ (X n ω) x')) 0). *)
    (exists epsilon : posreal,
        eventually
          (fun n : nat =>
             forall sa,
               almostR2 prts Rbar_lt
                 (fun ω : Ts =>
                    Lim_seq
                      (sum_n
                         (fun nn : nat => rvsqr (fun ω => α (nn + n)%nat ω sa) ω)))
                 (fun x : Ts => const epsilon x))) ->
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) 0).
  Proof.
    intros abound liminf exser exp_norm var_norm gammalim eqq aeps.

    pose (Xvec := fun t ω => our_iso_f_M (X t ω)).
    pose (XFvec := fun t ω => our_iso_f_M (XF t ω)).
    pose (αvec := fun t ω => our_iso_f_M (α t ω)).
   
    assert (IsAdapted (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) αvec F).
    {
      intros ?.
      unfold αvec.
      apply rv_vecrvnth.
      intros.
      assert (forall sa, RandomVariable (F n) borel_sa (fun ω => α n ω sa)).
      {
        intros.
        apply adapt_alpha.
      }
      generalize (finite_fun_vector_iso_nth_fun (α n)); intros.
      rewrite H0 in H.
      apply H.
      intros.
      apply RandomVariable_proper; try reflexivity.
    }
    assert ( RandomVariable (F 0) (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) (Xvec 0%nat)).
    {
      apply rv_vecrvnth.
      rewrite finite_fun_vector_iso_nth_fun in rvX0.
      intros.
      specialize (rvX0 i pf).
      apply rvX0.
      apply RandomVariable_proper; try reflexivity.
    }
    assert (0 < length (nodup (EqDecsigT (M := M)) fin_elms))%nat.
    {
      assert (NonEmpty (sigT M.(act))).
      {
        unfold NonEmpty.
        generalize (M.(ne)); intros.
        red in X0.
        generalize (M.(na) X0); intros.
        red in X1.
        exact (existT _ X0 X1).
      }
      red in X0.
      apply nodup_length_nzero.
      generalize (fin_finite X0).
      clear.
      destruct fin_elms; simpl; [tauto | lia].
    }
     generalize (Jaakkola_alpha_unbounded_N (length (nodup EqDecsigT fin_elms)) γ Xvec XFvec αvec _ filt_sub); intros jaak.


    assert (rvXFvec: forall k,   RandomVariable (F (S k))
            (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) 
            (XFvec k)).
    {
      intros.
      apply rv_vecrvnth.
      intros.
      assert (forall sa, RandomVariable (F (S k)) borel_sa (fun ω => XF k ω sa)).
      {
        intros.
        apply adapt_XF.
      }
      generalize (finite_fun_vector_iso_nth_fun (XF k)); intros.
      rewrite H3 in H2.
      apply H2.
      intros.
      apply RandomVariable_proper; try reflexivity.
    }
    assert (forall (k i : nat)
                       (pf : (i < length (nodup EqDecsigT fin_elms))%nat),
                     RandomVariable dom borel_sa (vecrvnth i pf (XFvec k))).
    {
      intros.
      apply vecrvnth_rv.
      now apply (RandomVariable_sa_sub (filt_sub (S k))).
    }
    assert   (isfex : forall (k i : nat)
                     (pf : (i < length (nodup EqDecsigT fin_elms))%nat),
                   IsFiniteExpectation prts (vecrvnth i pf (XFvec k))).
    {
      intros.
      generalize (finite_fun_vector_iso_nth_fun (XF k)); intros.
      generalize (isfe k); intros.
      rewrite H3 in H4.
      apply H4.
      apply IsFiniteExpectation_proper.
    }
    specialize (jaak H H0 rvXFvec H2 isfex gammalim).
    cut_to jaak; trivial.
    - revert jaak.
      apply almost_impl.
      apply all_almost; intros ??.
      intros sa.
      specialize (H3 _ (fin_finite_index_bound _ sa)).
      unfold our_iso_f_M in H3.
      simpl in H3.
      revert H3.
      apply is_lim_seq_ext; intros.
      unfold Xvec, our_iso_f_M; simpl.
      generalize (FiniteTypeVector.finite_fun_iso_b_f (act_finite M) EqDecsigT (X n x)).
      unfold FiniteTypeVector.vector_to_finite_fun; intros eqq2.
      now apply (f_equal (fun x => x sa)) in eqq2.
    - revert abound; apply almost_impl.
      apply all_almost; intros ??.
      intros k.
      specialize (H3 k).
      generalize (finite_fun_vector_iso_nth (α k x) (fun r => 0 <= r <= 1)); intros.
      now rewrite H4 in H3.
    - revert liminf.
      apply almost_impl.
      apply all_almost; intros ??.
      generalize (finite_fun_vector_iso_nth_fun (fun k => α k x) 
                    (fun afun => is_lim_seq (sum_n afun) p_infty)); intros.
      unfold αvec.
      rewrite H4 in H3.
      apply H3.
      intros ???.
      apply is_lim_seq_proper; trivial.
      intros ?.
      now apply sum_n_ext.
    - apply bounded_forall_almost.
      + intros; apply lt_dec.
      + intros ????.
        apply ex_series_ext.
        intros.
        f_equal.
        apply vector_nth_ext.
      + revert exser.
        apply almost_impl.
        apply all_almost; intros ??.
        generalize (finite_fun_vector_iso_nth_fun (fun k => α k x) 
                      (fun afun => (ex_series (rvsqr afun)))); intros HH.
        cut_to HH.
        * apply HH; intros.
          apply H3.
        * intros ???.
          apply ex_series_proper; intros ?.
          unfold rvsqr; f_equal; apply H4.
    - revert exp_norm; apply almost_impl.
      apply all_almost; intros ??.
      intros k.
      specialize (H3 k).
      unfold XFvec, Xvec, XFvec, our_iso_f_M; intros i pf.
      eapply Rle_trans; [| eapply Rle_trans]; [| eapply H3 |]; apply refl_refl.
      + f_equal.
        apply FiniteConditionalExpectation_ext; intros ?.
        unfold vecrvnth; simpl.
        unfold FiniteTypeVector.finite_fun_to_vector.
        rewrite vector_nth_map.
        reflexivity.
      + f_equal.
        unfold Rmax_norm, Rvector_max_abs.
        destruct (act_finite M).
        generalize (nodup_equiv EqDecsigT fin_elms)
        ; intros eqq1.
        rewrite <- (map_equivlist (fun s : sigT (act M) => Rabs (X k x s)) _ (reflexivity _) _ _ eqq1).
        rewrite <- fold_left_Rmax_abs.
        * unfold vector_fold_left; simpl.
          now rewrite map_map.
        * apply Forall_map.
          apply Forall_forall; intros.
          apply Rabs_pos.
    - destruct var_norm as [C [Cpos ?]].
      exists C.
      split; trivial.
      revert H3.
      apply almost_impl.
      apply all_almost; intros ??.
      intros k.
      unfold XFvec, Xvec, XFvec, our_iso_f_M; intros i pf.
      eapply Rbar_le_trans; [| eapply Rbar_le_trans]; [| eapply (H3 k) |]; apply slln.eq_Rbar_le.
      + apply ConditionalVariance_ext; intros ?.
        unfold vecrvnth; simpl.
        unfold FiniteTypeVector.finite_fun_to_vector.
        rewrite vector_nth_map.
        reflexivity.
      + do 3 f_equal.
        unfold Rmax_norm, Rvector_max_abs.
        destruct (act_finite M).
        generalize (nodup_equiv EqDecsigT fin_elms)
        ; intros eqq1.
        rewrite <- (map_equivlist (fun s : sigT (act M) => Rabs (X k x s)) _ (reflexivity _) _ _ eqq1).
        rewrite <- fold_left_Rmax_abs.
        * unfold vector_fold_left; simpl.
          now rewrite map_map.
        * apply Forall_map.
          apply Forall_forall; intros.
          apply Rabs_pos.
    - revert eqq.
      intros.
      intros ?.
      apply vector_nth_eq; intros.
      unfold Xvec, XFvec, αvec, our_iso_f_M, iso_f; simpl.
      unfold FiniteTypeVector.finite_fun_to_vector.
      unfold vecrvminus, vecrvopp, vecrvscale, vecrvplus, vecrvmult.
      repeat (rewrite Rvector_nth_plus || rewrite Rvector_nth_mult || rewrite Rvector_nth_scale || rewrite vector_nth_map).
      rewrite eqq.
      lra.
    - destruct aeps as [eps ?].
      exists eps.
      revert H3.
      apply eventually_impl.
      apply all_eventually; intros ????.
      eapply almost_impl; [| eapply H3].
      apply all_almost; intros ??.
      assert (HHH:forall a b c, a = b -> Rbar_lt a c -> Rbar_lt b c) by congruence.
      revert H4.
      apply HHH.
      apply Lim_seq_ext; intros ?.
      apply sum_n_ext; intros ?.
      unfold rvsqr; f_equal.
      unfold vecrvnth, αvec, our_iso_f_M; simpl.
      unfold FiniteTypeVector.finite_fun_to_vector.
      rewrite vector_nth_map.
      reflexivity.
 Qed.

  Theorem Jaakkola_alpha_uniformly_fintype
    (X : nat -> Ts -> Rfct (sigT M.(act)))
    (XF : nat -> Ts -> Rfct (sigT M.(act)))
    (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F) 
    {rvX0 : forall sa, RandomVariable (F 0%nat) borel_sa (fun ω => X 0%nat ω sa)}
    (adapt_XF : forall sa, IsAdapted borel_sa (fun t ω => XF t ω sa) (fun k => F (S k)))
    {rvXF : forall k sa, RandomVariable dom borel_sa (fun ω => XF k ω sa)}
    {isfe : forall k sa, IsFiniteExpectation prts (fun ω => XF k ω sa)} :
    almost prts (fun ω => forall k sa, 0 <= α k ω sa) ->
    almost prts (fun ω => forall sa, is_lim_seq (sum_n (fun k => α k ω sa)) p_infty) ->

    (forall sa,
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (fun ω => (α k ω sa)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (fun ω => (α k ω sa)) ω)))) ->

    (almost prts
       (fun ω =>
          forall k sa,
            Rabs ((FiniteConditionalExpectation _ (filt_sub k) (fun ω => XF k ω sa)) ω) <= (γ * (Rmax_norm _ (X k ω))))) ->
    (exists (C : R),
        (0 < C)  /\
          almost prts 
            (fun ω =>
               (forall k sa,
                   Rbar_le 
                     ((ConditionalVariance prts (filt_sub k) (fun ω => XF k ω sa)) ω)
                     (C * (1 + Rmax_norm _ (X k ω))^2)))) ->       
    0 < γ < 1 ->
(*    
     (forall k x, Rmax_norm _ (Rfct_minus _ (XF k x) x') <= β * Rmax_norm _ (Rfct_minus _ x x')) ->
*)
    (forall k ω sa, X (S k) ω sa = 
                    (X k ω sa) +  ((α k ω sa) * (((XF k ω sa) - (X k ω sa) ) ))) ->
    (*    almost prts (fun ω => is_lim_seq (fun n => Rmax_norm _ (Rfct_minus _ (X n ω) x')) 0). *)
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) 0).
  Proof.
    intros abound liminf uniform exp_norm var_norm gammalim eqq.

    pose (Xvec := fun t ω => our_iso_f_M (X t ω)).
    pose (XFvec := fun t ω => our_iso_f_M (XF t ω)).
    pose (αvec := fun t ω => our_iso_f_M (α t ω)).
   
    assert (IsAdapted (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) αvec F).
    {
      intros ?.
      unfold αvec.
      apply rv_vecrvnth.
      intros.
      assert (forall sa, RandomVariable (F n) borel_sa (fun ω => α n ω sa)).
      {
        intros.
        apply adapt_alpha.
      }
      generalize (finite_fun_vector_iso_nth_fun (α n)); intros.
      rewrite H0 in H.
      apply H.
      intros.
      apply RandomVariable_proper; try reflexivity.
    }
    assert ( RandomVariable (F 0) (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) (Xvec 0%nat)).
    {
      apply rv_vecrvnth.
      rewrite finite_fun_vector_iso_nth_fun in rvX0.
      intros.
      specialize (rvX0 i pf).
      apply rvX0.
      apply RandomVariable_proper; try reflexivity.
    }
    assert (0 < length (nodup (EqDecsigT (M := M)) fin_elms))%nat.
    {
      assert (NonEmpty (sigT M.(act))).
      {
        unfold NonEmpty.
        generalize (M.(ne)); intros.
        red in X0.
        generalize (M.(na) X0); intros.
        red in X1.
        exact (existT _ X0 X1).
      }
      red in X0.
      apply nodup_length_nzero.
      generalize (fin_finite X0).
      clear.
      destruct fin_elms; simpl; [tauto | lia].
    }
     generalize (Jaakkola_alpha_unbounded_uniformly_N (length (nodup EqDecsigT fin_elms)) γ Xvec XFvec αvec _ filt_sub); intros jaak.


    assert (rvXFvec: forall k,   RandomVariable (F (S k))
            (Rvector_borel_sa (length (nodup EqDecsigT fin_elms))) 
            (XFvec k)).
    {
      intros.
      apply rv_vecrvnth.
      intros.
      assert (forall sa, RandomVariable (F (S k)) borel_sa (fun ω => XF k ω sa)).
      {
        intros.
        apply adapt_XF.
      }
      generalize (finite_fun_vector_iso_nth_fun (XF k)); intros.
      rewrite H3 in H2.
      apply H2.
      intros.
      apply RandomVariable_proper; try reflexivity.
    }
    assert (forall (k i : nat)
                       (pf : (i < length (nodup EqDecsigT fin_elms))%nat),
                     RandomVariable dom borel_sa (vecrvnth i pf (XFvec k))).
    {
      intros.
      apply vecrvnth_rv.
      now apply (RandomVariable_sa_sub (filt_sub (S k))).
    }
    assert   (isfex : forall (k i : nat)
                     (pf : (i < length (nodup EqDecsigT fin_elms))%nat),
                   IsFiniteExpectation prts (vecrvnth i pf (XFvec k))).
    {
      intros.
      generalize (finite_fun_vector_iso_nth_fun (XF k)); intros.
      generalize (isfe k); intros.
      rewrite H3 in H4.
      apply H4.
      apply IsFiniteExpectation_proper.
    }
    specialize (jaak H H0 rvXFvec H2 isfex gammalim).
    cut_to jaak; trivial.
    - revert jaak.
      apply almost_impl.
      apply all_almost; intros ??.
      intros sa.
      specialize (H3 _ (fin_finite_index_bound _ sa)).
      unfold our_iso_f_M in H3.
      simpl in H3.
      revert H3.
      apply is_lim_seq_ext; intros.
      unfold Xvec, our_iso_f_M; simpl.
      generalize (FiniteTypeVector.finite_fun_iso_b_f (act_finite M) EqDecsigT (X n x)).
      unfold FiniteTypeVector.vector_to_finite_fun; intros eqq2.
      now apply (f_equal (fun x => x sa)) in eqq2.
    - revert abound; apply almost_impl.
      apply all_almost; intros ??.
      intros k.
      specialize (H3 k).
      now apply finite_fun_vector_iso_nth.
    - revert liminf.
      apply almost_impl.
      apply all_almost; intros ??.
      generalize (finite_fun_vector_iso_nth_fun (fun k => α k x) 
                    (fun afun => is_lim_seq (sum_n afun) p_infty)); intros.
      unfold αvec.
      rewrite H4 in H3.
      apply H3.
      intros ???.
      apply is_lim_seq_proper; trivial.
      intros ?.
      now apply sum_n_ext.
    - revert exp_norm; apply almost_impl.
      apply all_almost; intros ??.
      intros k.
      specialize (H3 k).
      unfold XFvec, Xvec, XFvec, our_iso_f_M; intros i pf.
      eapply Rle_trans; [| eapply Rle_trans]; [| eapply H3 |]; apply refl_refl.
      + f_equal.
        apply FiniteConditionalExpectation_ext; intros ?.
        unfold vecrvnth; simpl.
        unfold FiniteTypeVector.finite_fun_to_vector.
        rewrite vector_nth_map.
        reflexivity.
      + f_equal.
        unfold Rmax_norm, Rvector_max_abs.
        destruct (act_finite M).
        generalize (nodup_equiv EqDecsigT fin_elms)
        ; intros eqq1.
        rewrite <- (map_equivlist (fun s : sigT (act M) => Rabs (X k x s)) _ (reflexivity _) _ _ eqq1).
        rewrite <- fold_left_Rmax_abs.
        * unfold vector_fold_left; simpl.
          now rewrite map_map.
        * apply Forall_map.
          apply Forall_forall; intros.
          apply Rabs_pos.
    - clear jaak.
      intros.
      eapply  is_lim_seq'_uniform_almost_ext; try eapply uniform.
      + intros ??.
        apply sum_n_ext; intros ?.
        unfold rvsqr, vecrvnth, αvec, our_iso_f_M; simpl.
        unfold FiniteTypeVector.finite_fun_to_vector.
        rewrite vector_nth_map.
        reflexivity.
      + intros ?.
        f_equal.
        apply Lim_seq_ext; intros ?.
        apply sum_n_ext; intros ?.
        unfold rvsqr, vecrvnth, αvec, our_iso_f_M; simpl.
        unfold FiniteTypeVector.finite_fun_to_vector.
        rewrite vector_nth_map.
        reflexivity.
    - destruct var_norm as [C [Cpos ?]].
      exists C.
      split; trivial.
      revert H3.
      apply almost_impl.
      apply all_almost; intros ??.
      intros k.
      unfold XFvec, Xvec, XFvec, our_iso_f_M; intros i pf.
      eapply Rbar_le_trans; [| eapply Rbar_le_trans]; [| eapply (H3 k) |]; apply slln.eq_Rbar_le.
      + apply ConditionalVariance_ext; intros ?.
        unfold vecrvnth; simpl.
        unfold FiniteTypeVector.finite_fun_to_vector.
        rewrite vector_nth_map.
        reflexivity.
      + do 3 f_equal.
        unfold Rmax_norm, Rvector_max_abs.
        destruct (act_finite M).
        generalize (nodup_equiv EqDecsigT fin_elms)
        ; intros eqq1.
        rewrite <- (map_equivlist (fun s : sigT (act M) => Rabs (X k x s)) _ (reflexivity _) _ _ eqq1).
        rewrite <- fold_left_Rmax_abs.
        * unfold vector_fold_left; simpl.
          now rewrite map_map.
        * apply Forall_map.
          apply Forall_forall; intros.
          apply Rabs_pos.
    - revert eqq.
      intros.
      intros ?.
      apply vector_nth_eq; intros.
      unfold Xvec, XFvec, αvec, our_iso_f_M, iso_f; simpl.
      unfold FiniteTypeVector.finite_fun_to_vector.
      unfold vecrvminus, vecrvopp, vecrvscale, vecrvplus, vecrvmult.
      repeat (rewrite Rvector_nth_plus || rewrite Rvector_nth_mult || rewrite Rvector_nth_scale || rewrite vector_nth_map).
      rewrite eqq.
      lra.
  Qed.

(*
  Existing Instance qlearn_Q_rv_dom.
  Existing Instance isfe_qlearn_Q.
  Existing Instance frf_Qmin.
*)
  Existing Instance qlearn_Q_rv.
  Existing Instance isfe_qmin .
  Existing Instance finfun_sa.

  Instance frf_Qmin (g : Rfct (sigT M.(act))) (f : Ts -> M.(state))
           {rvf : RandomVariable dom (discrete_sa M.(state)) f} :
    FiniteRangeFunction (fun ω0 : Ts => qlearn_Qmin g (f ω0))
    := frf_Qmin g f.

  Existing Instance st_eqdec.

  (*  Context {finA : FiniteType (sigT M.(act))}. *)

  Existing Instance isl2_qlearn_Q.

  Lemma Rmax_all_norm_nneg (f:Rfct (sigT M.(act))) (fnneg:NonnegativeFunction f) :
    Rmax_norm _ f = Rmax_all f.
  Proof.
    unfold Rmax_norm, Rmax_all.
    destruct (act_finite M).
    apply Rmax_list_Proper.
    apply refl_refl.
    apply map_ext; intros ?.
    rewrite Rabs_right; trivial.
    specialize (fnneg a).
    lra.
  Qed.

  Lemma Rmax_norm_sqr (f:Rfct (sigT M.(act))) :
    Rmax_norm _ (fun sa => (f sa)²) = (Rmax_norm _ (fun sa => f sa))².
  Proof.
    unfold Rmax_norm.
    destruct (act_finite M).
    rewrite <- (map_map f Rabs).
    rewrite Rmax_list_abs_sqr.
    rewrite map_map.
    apply Rmax_list_Proper; apply refl_refl.
    apply map_ext; intros ?.
    rewrite Rabs_right; trivial.
    apply Rle_ge.
    apply nnfsqr.
  Qed.    

  Theorem qlearn_jaakkola
      (x' : Rfct (sigT M.(act)))
      (adapt_alpha : forall sa, IsAdapted borel_sa (fun t ω => α t ω sa) F)
      (fixpt: qlearn_XF next_state cost cost_rv islp_cost filt_sub γ x' = x') :
    0 < γ < 1 ->
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (sum_n (fun k => α k ω sa)) p_infty) ->
    (forall sa,
        is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (fun ω => (α k ω sa)) ω) n) 
          (fun ω => Lim_seq (sum_n (fun k => rvsqr (fun ω => (α k ω sa)) ω)))) ->

    let X := qlearn_Q next_state cost Q0 α γ in 
    almost prts (fun ω =>
                   forall sa,
                     is_lim_seq (fun n => X n ω sa) (x' sa)).
   Proof.
     intros gammalin pinf uniform X.
     pose (Xmin := fun k sa ω => qlearn_Qmin (X k ω) (next_state k sa ω)).
     pose (FT := fun k sa ω => (cost k sa ω) + γ * (Xmin k sa ω) - (x' sa)).
     assert (rvXF : RandomVariable finfun_sa finfun_sa 
                      (qlearn_XF next_state cost cost_rv islp_cost filt_sub γ)).
     {
       apply rv_finfun_sa.
       intros.
       apply rvplus_rv; try typeclasses eauto.
       apply rvscale_rv.
       assert (rv2 : forall ω, RandomVariable dom borel_sa (fun v : Ts => qlearn_Qmin ω (next_state 0%nat sa v))).
       {
         intros.
         apply rv_qmin1.
         - typeclasses eauto.
         - now apply (RandomVariable_sa_sub (filt_sub 1%nat)).
       }
       assert (RandomVariable dom (discrete_sa (state M))
                   (next_state 0 sa)).
         {
           now apply (RandomVariable_sa_sub (filt_sub 1%nat)).
        }
       eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)).
       {
         intros ?.
         rewrite (FiniteExpectation_simple _ _).
         now rewrite (SimpleExpectation_compose _ _).
       }
       apply list_sum_rv; intros; try typeclasses eauto.
       apply rvmult_rv; [| apply rvconst].
       unfold qlearn_Qmin.
       generalize (@rvs_Rmin_list (Rfct (sigT M.(act))) finfun_sa (map (fun a omega => omega (existT _ c a)) (act_list c))); intros HH.
       cut_to HH.
       - revert HH.
         apply RandomVariable_proper; try easy.
         intros ?.
         now rewrite map_map.
       - apply Forall_forall; intros.
         apply in_map_iff in H0.
         destruct H0 as [? [??]]; subst.
         apply finfun_sa_rv.
         apply id_rv.
     }
     assert (rvfinexp : forall k sa, 
                RandomVariable (F (S k)) borel_sa
                  (fun ω : Ts => FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (X k ω) (next_state k sa ω0)))).
     {
       intros.
       assert (RandomVariable (F (S k)) borel_sa
                              (fun ω =>
                                 (list_sum
                                    (map 
                                       (fun v : state M =>
                                          Rmult (qlearn_Qmin (X k ω) v)
                                            (ps_P 
                                               (@preimage_singleton Ts (state M) dom (discrete_sa (state M))
                                                  (@DiscreteProbSpace.HasPreimageSingleton_discrete (state M)) (next_state k sa)
                                                  (@rv_ns M Ts dom F next_state next_state_rv filt_sub k sa) v)))
                                       (@fin_elms (state M) (@fin_finite_nodup (state M) (st_eqdec M) (fs M))))))).
       {
         apply list_sum_rv.
         intros.
         apply rvmult_rv.
         - apply rv_qmin1.
           + intros.
             apply (RandomVariable_sa_sub (isfilt k)).
             apply qlearn_Q_rv; typeclasses eauto.
           + apply rvconst.
         - apply rvconst.
       }
       revert H.
       apply RandomVariable_proper; try easy.
       intros ?.
       now rewrite FiniteExpectation_Qmin with (next_state_rv := next_state_rv) (filt_sub := filt_sub).
     }
     assert (rvfinexp' : forall k sa,
                RandomVariable dom borel_sa
                  (fun ω : Ts => FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (X k ω) (next_state k sa ω0)))).
     {
       intros.
       now apply (RandomVariable_sa_sub (filt_sub (S k))).
     }
     assert (rvFT: forall (k : nat) (sa : {x : state M & act M x}),
                RandomVariable dom borel_sa (FT k sa)).
     {
       intros.
       apply rvplus_rv.
       - apply rvplus_rv.
         + apply (RandomVariable_sa_sub (filt_sub (S k))).
           apply cost_rv.
         + apply rvscale_rv.
           apply rv_qmin1.
           * intros.
             apply (RandomVariable_sa_sub (filt_sub k)).
             unfold X.
             apply qlearn_Q_rv; try typeclasses eauto.
           * apply (RandomVariable_sa_sub (filt_sub (S k))); trivial.
       - apply rvconst.
    }
     assert (isfe_finexp: forall k sa,
                IsFiniteExpectation prts
                  (fun ω : Ts => FiniteExpectation prts (fun ω0 : Ts => qlearn_Qmin (X k ω) (next_state k sa ω0)))).
     {
       intros.
         generalize (@ProductSpace.isfe_fubini_section_fst _ _ _ _ prts prts
                       (fun '(ω, ω0) =>
                          qlearn_Qmin (X k ω) (next_state k sa ω0)))
         ; intros HH.
         {
           assert (rvf: RandomVariable (product_sa dom dom) Rbar_borel_sa
                          (fun '(ω, ω0) => qlearn_Qmin (X k ω) (next_state k sa ω0))).
           {
             assert (RandomVariable (product_sa dom dom) borel_sa
                       (fun '(ω, ω0) => qlearn_Qmin (X k ω) (next_state k sa ω0))).
             {
               apply rv_qmin2; try easy.
               intros.
               unfold X.
               - now apply qlearn_Q_rv_dom; try typeclasses eauto.
               - now apply qlearn_next_state_rv2; try typeclasses eauto.
             }
             apply borel_Rbar_borel in H.
             revert H.
             apply RandomVariable_proper; try easy.
             intros ?.
             now destruct a.
           }

           assert (IsFiniteExpectation (ProductSpace.product_ps prts prts)
                            (fun '(ω, ω0) => qlearn_Qmin (X k ω) (next_state k sa ω0))).
          {
            unfold X.
            apply isfe_qmin2'.
            - intros.
              now apply qlearn_Q_rv_dom; try typeclasses eauto.
            - intros.
              now apply isfe_qlearn_Q; try typeclasses eauto.
          }
           assert (isfef: Rbar_IsFiniteExpectation (ProductSpace.product_ps prts prts)
                            (fun '(ω, ω0) => qlearn_Qmin (X k ω) (next_state k sa ω0))).
          {
            apply IsFiniteExpectation_Rbar in H.
            revert H.
            apply Rbar_IsFiniteExpectation_proper.
            intros ?.
            now destruct a.
         }
          specialize (HH _ _).
           revert HH.
           apply IsFiniteExpectation_proper; intros ?.
           rewrite <- FinExp_Rbar_FinExp.
           + now rewrite (ProductSpace.Rbar_FiniteExpectation0_finite _ _ (isfe:= (@IsFiniteExpectation_Rbar Ts dom prts
                                                                        (fun ω0 : Ts => qlearn_Qmin (X k a) (next_state k sa ω0))
                                                                        (isfe_qmin next_state (X k a) k sa)))).
           + apply rv_qmin1; try typeclasses eauto.
             now apply (RandomVariable_sa_sub (filt_sub (S k))).
         }
     }
     
     assert (forall k sa, IsFiniteExpectation prts (FT k sa)).
     {
       intros.
       unfold FT.
       apply IsFiniteExpectation_plus.
       - apply rvplus_rv.
         + apply (RandomVariable_sa_sub (filt_sub (S k))).
           apply cost_rv.
         + apply rvscale_rv.
           apply rv_qmin1.
           * intros.
             apply (RandomVariable_sa_sub (filt_sub k)).
             unfold X.
             apply qlearn_Q_rv; try typeclasses eauto.
           * now apply (RandomVariable_sa_sub (filt_sub (S k))).
       - apply rvconst.
       - apply IsFiniteExpectation_plus.
         + apply (RandomVariable_sa_sub (filt_sub (S k))).
           apply cost_rv.
         + apply rvscale_rv.
           apply rv_qmin1.
           * intros.
             apply (RandomVariable_sa_sub (filt_sub k)).
             unfold X.
             apply qlearn_Q_rv; try typeclasses eauto.
           * now apply (RandomVariable_sa_sub (filt_sub (S k))).
         + apply IsL2_Finite; trivial.
           now apply (RandomVariable_sa_sub (filt_sub (S k))).
         + apply IsFiniteExpectation_scale.
           apply isfe_qmin1.
           * intros.
             now apply qlearn_Q_rv_dom; try typeclasses eauto.
           * intros.
             now apply isfe_qlearn_Q; try typeclasses eauto.
       - apply IsFiniteExpectation_const.
     }
     assert (forall n sa, RandomVariable (F n) borel_sa (fun ω : Ts => X n ω sa)).
     {
       intros.
       typeclasses eauto.
     }
     assert (forall n sa,  RandomVariable (F (S n)) (discrete_sa (state M)) (next_state n sa)).
     {
       intros.
       easy.
     }
     generalize (Jaakkola_alpha_uniformly_fintype (fun k ω sa => X k ω sa - x' sa) (fun κ ω sa => FT κ sa ω) _); intros jaak.
     assert (forall sa : {x : state M & act M x}, IsAdapted borel_sa (fun (t : nat) (ω : Ts) => FT t sa ω) (fun k : nat => F (S k))).
     {
       intros.
       intros ?.
       unfold FT.
       apply rvplus_rv; try typeclasses eauto.
       apply rvplus_rv; try typeclasses eauto.
       apply rvscale_rv.
       apply rv_qmin1; try typeclasses eauto.
       intros.
       apply (RandomVariable_sa_sub (isfilt n)).
       apply qlearn_Q_rv; try typeclasses eauto.
     }
     specialize (jaak H2).
     assert (rvXF' : forall (k : nat) (sa : {x : state M & act M x}), RandomVariable dom borel_sa (fun ω : Ts => FT k sa ω)).
     {
       intros.
       apply (RandomVariable_sa_sub (filt_sub (S k))).
       apply H2.
     }
     specialize (jaak rvXF' H).
     assert (forall k sa,
                RandomVariable dom borel_sa
                  (fun ω : Ts => qlearn_Qmin (X k ω) (next_state k sa ω))).
     {
       intros.
       apply rv_qmin1.
       - intros.
         now apply (RandomVariable_sa_sub (filt_sub k)).
       - now apply (RandomVariable_sa_sub (filt_sub (S k))).
    }
       
     assert (freeze: forall k sa,
                almostR2 (prob_space_sa_sub prts (filt_sub k)) eq
                  (ConditionalExpectation prts (filt_sub k)
                     (fun ω : Ts =>
                        (fun '(q, ns) => qlearn_Qmin q ns)
                          (X k ω, next_state k sa ω)))
                  (fun ω : Ts =>
                     FiniteExpectation prts
                       (fun ω0 : Ts =>
                          (fun '(q, ns) => qlearn_Qmin q ns)
                            (X k ω, next_state k sa ω0)))).
     {
       intros.
       generalize (ProductSpace.freezing_sa_alt (filt_sub k)
                   (pullback_rv_sub dom (discrete_sa (state M))
                      (next_state k sa) (qlearn_next_state_rv2 next_state next_state_rv filt_sub k sa))
                   (X k)
                   (next_state k sa)
                ); intros freez.

       specialize (freez (fun '(q, ns) => (qlearn_Qmin q ns)) ).
       assert (rvx : RandomVariable (F k) finfun_sa (X k)).
       {
         now apply rv_finfun_sa.
       }
       assert (rvy : RandomVariable
                       (pullback_sa (discrete_sa (state M)) (next_state k sa))
                       (discrete_sa (state M)) (next_state k sa)).
       {
         apply pullback_rv.
       }
       assert  (rvPsi : RandomVariable (product_sa finfun_sa (discrete_sa (state M)))
                          borel_sa (fun '(q, ns) => qlearn_Qmin q ns)).
       {
         assert (forall sa : {x : state M & act M x},
                                RandomVariable finfun_sa borel_sa
                                  (fun q : Rfct {x : state M & act M x} => q sa)).
         {
           apply finfun_sa_rv.
           typeclasses eauto.
         }
         apply rv_qmin3.
       }

       assert ( IsFiniteExpectation prts
            (fun ω : Ts =>
             (fun '(q, ns) => qlearn_Qmin q ns) (X k ω, next_state k sa ω))).
       {
         apply isfe_qmin1.
         intros.
         - now apply (RandomVariable_sa_sub (filt_sub k)).
         - intros.
           now apply isfe_qlearn_Q; try typeclasses eauto.
       }
       specialize (freez rvx rvy rvPsi _ _).       
       cut_to freez; [|apply ProductSpace.independent_sas_comm, indep_next_state].
       destruct freez as [_ freez].
       revert freez.
       apply almost_impl.
       apply all_almost; intros ??.
       rewrite <- H5.
       apply ConditionalExpectation_ext.
       reflexivity.
     }
     simpl in freeze.
     cut_to jaak; trivial.
     - revert jaak; apply almost_impl.
       apply all_almost; intros ??.
       intros.
       specialize (H4 sa).
       assert (is_lim_seq (fun n => ((X n x sa - x' sa) + x' sa)) (0 + x' sa)).
       {
         apply is_lim_seq_plus'; trivial.
         apply is_lim_seq_const.
       }
       rewrite Rplus_0_l in H5.
       revert H5.
       apply is_lim_seq_ext.
       intros.
       lra.
     - apply all_almost.
       intros.
       apply alpha_bound.
     - clear jaak.
       unfold FT.
       assert (forall k sa,
                  RandomVariable dom borel_sa (cost k sa)).
       {
         intros.
         now apply (RandomVariable_sa_sub (filt_sub (S k))).
       }
       assert (forall k sa,
                  RandomVariable dom borel_sa (fun ω => qlearn_Qmin (X k ω) (next_state k sa ω))).
       {
         intros.
         apply rv_qmin1.
         - intros.
           now apply (RandomVariable_sa_sub (filt_sub k)).
         - now apply (RandomVariable_sa_sub (filt_sub (S k))).
       }
       assert (forall k sa,
                  almost  (prob_space_sa_sub prts (filt_sub k))
                          (fun x =>
                    (ConditionalExpectation prts (filt_sub k)
                       (fun ω : Ts =>
                          cost k sa ω + γ * qlearn_Qmin (X k ω) (next_state k sa ω))) x = 
                    (qlearn_XF next_state cost cost_rv islp_cost filt_sub γ (X k x) sa))).
       {
         intros.
         generalize (is_conditional_expectation_independent_sa prts (filt_sub k) (cost k sa) (indep_cost k sa)); intros.
         generalize (Condexp_cond_exp prts (filt_sub k) (cost k sa)); intros.
         generalize (is_conditional_expectation_unique prts (filt_sub k) (cost k sa)); intros condexp_cost.
         assert (RandomVariable (F k) Rbar_borel_sa  (fun x : Ts => const (FiniteExpectation prts (cost k sa)) x)).
         {
           apply Real_Rbar_rv.
           apply rvconst.
         }
         assert (RandomVariable (F k) Rbar_borel_sa  (ConditionalExpectation prts (filt_sub k) (cost k sa))).
         {
           apply Condexp_rv.
         }
         specialize (condexp_cost _ _ _ H8 H9 (isfe_cost cost _ _ filt_sub k sa) H6 H7).
         assert (IsFiniteExpectation prts
                   (fun ω : Ts =>
                      qlearn_Qmin (X k ω) (next_state k sa ω))).
         {
           apply isfe_qmin1.
           - intros.
             now apply (RandomVariable_sa_sub (filt_sub k)).
           - intros.
             now apply isfe_qlearn_Q; try typeclasses eauto.
         }
         generalize (Condexp_plus prts (filt_sub k)
                       (cost k sa)
                       (fun ω : Ts => γ * qlearn_Qmin (X k ω) (next_state k sa ω))).
         apply almost_impl.
         generalize (Condexp_scale 
                       prts (filt_sub k)
                       γ 
                       (fun ω : Ts => qlearn_Qmin (X k ω) (next_state k sa ω))).
         apply almost_impl.
         specialize (freeze k sa).
         revert freeze.
         apply almost_impl.
         revert condexp_cost; apply almost_impl.
         apply all_almost; intros ?????.
         unfold qlearn_XF.
         unfold rvplus in H14.
         rewrite H14.
         unfold Rbar_rvplus.
         unfold rvscale in H13.
         rewrite H13.
         unfold Rbar_rvmult.
         rewrite <- H11.
         unfold const.
         assert ( (ConditionalExpectation prts (filt_sub k)
                     (fun ω : Ts => qlearn_Qmin (X k ω) (next_state k sa ω)) x) =
                    FiniteExpectation prts
                      (fun ω0 : Ts => qlearn_Qmin (X k x) (next_state 0 sa ω0))).
         {
           etransitivity; [|etransitivity]; [|apply H12|].
           - now apply ConditionalExpectation_ext.
           - f_equal.
             symmetry.
             eapply ident_distr_finite_exp_eq.
             generalize (identically_distributed_rv_compose prts
                           (discrete_sa (state M))
                           borel_sa
                           (next_state 0%nat sa) 
                           (next_state k sa)
                           (qlearn_Qmin (X k x))
                           (ident_distr_next_state k sa)).
             now apply identically_distributed_rvs_proper.
         }
         rewrite H15.
         simpl.
         f_equal; f_equal.
         symmetry.
         apply ident_distr_finite_exp_eq with (rvy := H4 k sa) (rvx := H4 0%nat sa).
         specialize (ident_distr_cost k sa).
         revert ident_distr_cost.
         now apply identically_distributed_rvs_proper.
         Unshelve.
         - apply rv_qmin1.
           + intros; apply rvconst.
           + now apply (RandomVariable_sa_sub (filt_sub (S 0%nat))).
         - apply rv_qmin1.
           + intros; apply rvconst.
           + now apply (RandomVariable_sa_sub (filt_sub (S k))).
       }

       assert (
           forall k sa,
           almost prts
             (fun ω : Ts =>
                (FiniteConditionalExpectation prts (filt_sub k)
                   (fun ω0 : Ts =>
                      cost k sa ω0 + γ * qlearn_Qmin (X k ω0) (next_state k sa ω0) - x' sa) ω) = 
                  (qlearn_XF next_state cost cost_rv islp_cost filt_sub γ (X k ω) sa) 
                   - (x' sa))).
       {
         intros.
          assert (IsFiniteExpectation prts
                   (fun ω : Ts =>
                      qlearn_Qmin (X k ω) (next_state k sa ω))).
         {
           apply isfe_qmin1.
           - intros.
             now apply (RandomVariable_sa_sub (filt_sub k)).
           - intros.
             now apply isfe_qlearn_Q; try typeclasses eauto.
         }
         generalize (FiniteCondexp_minus' prts (filt_sub k)
                        (fun ω : Ts =>
                           cost k sa ω + γ * qlearn_Qmin (X k ω) (next_state k sa ω))
                        (const (x' sa))); intros.
        apply almost_prob_space_sa_sub_lift in H8.
        revert H8; apply almost_impl.
        specialize (H6 k sa).
        apply almost_prob_space_sa_sub_lift in H6.        
        revert H6; apply almost_impl.
        apply all_almost; intros ???.
        unfold rvminus, rvplus, rvopp, rvscale in H8.
        erewrite FiniteCondexp_eq in H6.
        rewrite Rbar_finite_eq in H6.
        rewrite <- H6.
        rewrite FiniteCondexp_const in H8.
        unfold const in H8.
        unfold Rminus at 2.
        replace (-1 * x' sa) with (- x' sa) in H8 by lra.
        rewrite <- H8.
        apply FiniteConditionalExpectation_ext.
        reflexivity.
       }
       apply almost_forall; intros.
       apply almost_countable_forall; try typeclasses eauto.
       intros.
       specialize (H7 n a).
       revert H7; apply almost_impl.
       apply all_almost; intros ??.
       unfold Xmin.
       rewrite H7.
       generalize  (@qlearn_XF_contraction M Ts dom prts F next_state _ cost _ _ filt_sub γ (act_finite M)); intros contrac.
       assert (0 <= γ < 1) by lra.
       specialize (contrac H8 (X n x) x').
       eapply Rle_trans; cycle 1.
       apply contrac.
       rewrite fixpt.
       apply Rmax_spec.
       apply in_map_iff.
       eexists; split; [reflexivity |].
       apply FiniteType.fin_finite_dep_prod_obligation_2.
     - clear jaak.
       assert (cost_rv': forall n sa, RandomVariable dom borel_sa (cost n sa)).
       {
         intros.
         now apply (RandomVariable_sa_sub (filt_sub (S n))).
       }
       assert (isfe_cost: forall k sa, IsFiniteExpectation prts (cost k sa)).
       {
         intros.
         now apply IsL2_Finite.
       }
       assert (isfe2_cost: forall k sa,
                  IsFiniteExpectation prts (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa))²)).
       {
         intros.
         generalize (isfe_variance_l2 prts (cost k sa) _).
         apply IsFiniteExpectation_proper.
         intros ?.
         unfold rvsqr, const.
         rewrite rvminus_unfold.
         do 2 f_equal.
         now apply FiniteExpectation_ext.
       }
       assert (exists A,
                 0 < A /\
                 forall k sa, 
                   FiniteExpectation prts 
                                     (fun ω => Rsqr
                                                 ((cost k sa ω) -
                                                  (FiniteExpectation prts (cost k sa))))
                   <=   A).
      {
        assert (forall k sa,
                   exists A,
                     FiniteExpectation prts 
                                     (fun ω => Rsqr
                                                 ((cost k sa ω) -
                                                  (FiniteExpectation prts (cost k sa))))
                   <=   A).
        {
          intros.
          unfold FiniteExpectation.
          unfold proj1_sig.
          match_destr.
          exists x; lra.
        }
        assert (exists A : R,
                   0 < A /\
                     (forall (sa : {x : state M & act M x}),
                         FiniteExpectation prts
                           (fun ω : Ts => (cost 0%nat sa ω - FiniteExpectation prts (cost 0%nat sa))²) <=  A)).
        {
          specialize (H4 0%nat).
          apply (finite_ex_choice _ (decA:=EqDecsigT)) in H4.
          destruct H4 as [l F2l].
          exists (Rabs (Rmax_list l) + 1).
          split.
          - unfold Rabs; match_destr; lra.
          - intros sa.
            apply Rle_trans with (r2:=Rmax_list l); [| unfold Rabs; match_destr; lra].
            destruct (Forall2_In_l F2l (a:=sa)) as [?[??]].
            + apply nodup_In; apply fin_finite.
            + eapply Rle_trans; try apply H5.
              now apply Rmax_spec.
        }
        destruct H5 as [? [? ?]].
        exists x.
        split; trivial.
        intros.
        eapply Rle_trans; cycle 1.
        apply (H6 sa).
        right.
        eapply ident_distr_finite_exp_eq.
        generalize (identically_distributed_sqr
                      (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa)))
                      (fun ω : Ts => (cost 0 sa ω - FiniteExpectation prts (cost 0%nat sa)))); intros.
        unfold compose in H7.
        cut_to H7.
        - revert H7.
          now apply identically_distributed_rvs_proper.
        - cut (identically_distributed_rvs prts borel_sa
                 (fun ω : Ts => cost k sa ω - FiniteExpectation prts (cost 0 sa))
                 (fun ω : Ts => cost 0 sa ω - FiniteExpectation prts (cost 0 sa))).
          + apply identically_distributed_rvs_proper; try reflexivity.
            intros ?.
            f_equal.
            eapply ident_distr_finite_exp_eq.
            apply identically_distributed_rvs_comm.
            generalize (ident_distr_cost k sa).
            now apply identically_distributed_rvs_proper.
          + generalize (identically_distributed_rv_compose prts borel_sa borel_sa
                          (cost k sa) (cost 0 sa) (fun x => x - FiniteExpectation prts (cost 0 sa)))
            ; intros HH.
            cut_to HH.
            * revert HH.
              now apply identically_distributed_rvs_proper.
            * apply identically_distributed_rvs_comm.
              generalize (ident_distr_cost k sa).
              now apply identically_distributed_rvs_proper.
      } 

               assert (exists (A : R),
                0 < A /\
               forall k sa,
                 almostR2 prts Rbar_le
                   (ConditionalVariance prts (filt_sub k) (cost k sa))
                   (const A)).
      {
        destruct H4 as [A [??]].
        exists A.
        split; trivial.
        intros.
        unfold ConditionalVariance.
        specialize (H5 k sa).
        assert (isfe2_cost' : IsFiniteExpectation prts
            (rvsqr
               (rvminus (cost k sa)
                  (FiniteConditionalExpectation prts (filt_sub k) (cost k sa))))).
        {
          eapply (IsFiniteExpectation_proper_almostR2 prts (fun ω : Ts => (cost k sa ω - FiniteExpectation prts (cost k sa))²) ); try typeclasses eauto.
          - apply rvsqr_rv.
            apply rvminus_rv; try typeclasses eauto.
            apply FiniteCondexp_rv'.
          - assert (almostR2 prts eq
                             (FiniteConditionalExpectation prts (filt_sub k) (cost k sa))
                             (const (FiniteExpectation prts (cost k sa)))).
            {
              generalize (is_conditional_expectation_independent_sa prts (filt_sub k) (cost k sa)); intros.
              generalize (FiniteCondexp_is_cond_exp prts (filt_sub k) (cost k sa)); intros.
              generalize (is_conditional_expectation_unique prts (filt_sub k) ); intros.
              cut_to H6.
              - specialize (H8 _ _ _ _ _ _ _ H7 H6).
                apply almost_prob_space_sa_sub_lift in H8.
                revert H8.
                apply almost_impl.
                apply all_almost; intros ??.
                rewrite Rbar_finite_eq in H8.
                now rewrite H8.
              - specialize (indep_cost k sa).
                revert indep_cost.
                now apply independent_sas_proper.
            }
            revert H6; apply almost_impl.
            apply all_almost; intros ??.
            unfold rvsqr; rewrite rvminus_unfold.
            rewrite H6.
            now unfold const.
        }
        generalize (variance_exp_independent prts (filt_sub k) (cost k sa)); intros var_ind.
        assert (independent_sas prts (pullback_rv_sub dom borel_sa (cost k sa) (cost_rv' k sa))
                  (filt_sub k)).
        {
          specialize (indep_cost k sa).
          revert indep_cost.
          now apply independent_sas_proper.
        }
        specialize (var_ind H6).
        apply almost_prob_space_sa_sub_lift in var_ind.
        revert var_ind; apply almost_impl.
        apply all_almost; intros ??.
        rewrite FiniteCondexp_eq with (isfe := isfe2_cost').
        simpl.
        unfold const.
        symmetry in H7.
        eapply Rle_trans; cycle 1.
        apply H5.
        right.
        rewrite <- H7.
        apply FiniteConditionalExpectation_ext.
        reflexivity.
      }

      assert (forall k sa, IsLp prts 2 (Xmin k sa)).
      {
        intros.
        apply isl2_qmin1; intros.
        - now apply (RandomVariable_sa_sub (filt_sub k)).
        - now apply isl2_qlearn_Q; try typeclasses eauto.
      }
      assert (forall k sa,
                 IsFiniteExpectation prts (Xmin k sa)).
      {
        intros.
        apply IsL2_Finite; typeclasses eauto.
      }
      assert (forall k sa,
                 IsFiniteExpectation prts
                   (rvsqr
                      (rvminus (Xmin k sa)
                         (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa))))).
      {
        intros.
        generalize (FiniteCondexp_L2_min_dist_isfe prts (filt_sub k) (Xmin k sa)).
        apply IsFiniteExpectation_proper.
        intros ?.
        rv_unfold.
        do 3 f_equal.
        now apply FiniteConditionalExpectation_ext.
      }
      assert (forall k sa,
                 RandomVariable dom borel_sa
                   (rvsqr
                      (rvminus (Xmin k sa)
                         (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa))))).
      {
        intros.
        apply rvsqr_rv.
        apply rvminus_rv; try typeclasses eauto.
        apply FiniteCondexp_rv'.
      }
      assert (isl2_X :forall k sa,
                 IsLp prts 2 (fun ω => X k ω sa)).
      {
        now apply isl2_qlearn_Q; try typeclasses eauto.
      }
      assert (forall k sa,
                 almostR2 prts Rle 
                   (FiniteConditionalExpectation 
                      prts (filt_sub k)
                      (rvsqr (rvminus 
                                (Xmin k sa)
                                (FiniteConditionalExpectation prts (filt_sub k) (Xmin k sa)))))
                   (fun ω => Rmax_all (fun sa => Rsqr (X k ω sa)))).
      {
        intros.
        assert (RandomVariable dom borel_sa (Xmin k sa)) by typeclasses eauto.
        assert (IsFiniteExpectation 
                  prts
                  (fun ω : Ts =>
                     Rmax_all (fun sa : {x : state M & act M x} => (X k ω sa)²))).
        {
          apply isfe_Rmax_all; intros.
          - apply rvsqr_rv.
            apply (RandomVariable_sa_sub (filt_sub k)); try typeclasses eauto.
          - now apply islp2_isfe_sqr.
        }
        generalize (conditional_variance_bound_L2_fun (dom2 := F k)
                      (Xmin k sa)
                      (fun ω => (Rmax_all (fun sa => Rsqr (X k ω sa))))); intros.
        specialize (H12 (filt_sub k) H10).
        cut_to H12.
        specialize (H12 (H6 k sa)).
        cut_to H12.
        - apply almost_prob_space_sa_sub_lift in H12.
          revert H12.
          apply almost_impl, all_almost; intros ??.
          etransitivity; [| etransitivity]; [| apply H12 |]; apply refl_refl.
          + apply FiniteConditionalExpectation_ext.
            intros ?.
            rv_unfold.
            do 3 f_equal.
            apply FiniteConditionalExpectation_ext; reflexivity.
          + reflexivity.
        - rv_unfold.
          unfold Rmax_all, Xmin, qlearn_Qmin.
          apply all_almost; intros ?.
          match_destr.
          assert (exists sa0,
                     Min_{ act_list (next_state k sa x)}
                         (fun a0 : act M (next_state k sa x) => X k x (existT (act M) (next_state k sa x) a0)) = X k x sa0).
          {
            generalize (Rmin_list_map_exist (fun a0 : act M (next_state k sa x) => X k x (existT (act M) (next_state k sa x) a0))  (act_list (next_state k sa x))); intros.
            cut_to H13.
            - destruct H13 as [? [? ?]].
              exists (existT _ _ x0).
              now rewrite <- H14.
            - apply act_list_not_nil.
          }
          destruct H13.
          rewrite H13.
          apply Rmax_spec.
          apply in_map_iff.
          exists x0.
          split; trivial.
        - apply rv_Rmax_all.
          typeclasses eauto.
        - apply isfe_Rmax_all.
          + intros.
            apply rvsqr_rv.
            now apply (RandomVariable_sa_sub (filt_sub k)).
          + intros.
            now apply islp2_isfe_sqr.
      }
      assert (forall (x y : R),
                 x² <= 2*((x-y)² + y²)).
      {
        intros.
        generalize (sq_sum_le_2sum_sq (x - y) y); intros.
        eapply Rle_trans; cycle 1.
        apply H11.
        right; unfold Rsqr; lra.
      }
     assert (exists (A B : R),
                0 < A /\ 0 < B /\
                    almost prts
                      (fun ω : Ts =>
                         forall (k : nat) (sa : {x : state M & act M x}),
                           Rbar_le
                             (ConditionalVariance prts (filt_sub k) (fun ω0 : Ts => FT k sa ω0) ω)
                             (A + B *
                                   (Rmax_norm {x : state M & act M x}
                                      (fun sa0 => X k ω sa0)) ^ 2))).
      {
        destruct H5 as [A [??]].
        exists (2*A).
        exists 2.
        split; try lra.
        split; try lra.
        apply almost_forall; intros.
        apply almost_countable_forall; try typeclasses eauto; intros.        
        specialize (H12 n a).
        revert H12; apply almost_impl.
        specialize (H10 n a).
        revert H10; apply almost_impl.
        generalize (conditional_variance_bound_sum  prts (filt_sub n)
                      (cost n a) 
                      (rvscale γ (Xmin n a))); apply almost_impl.
        generalize (ConditionalVariance_minus_const  prts (filt_sub n)(fun ω0 : Ts =>
        cost n a ω0 + γ * qlearn_Qmin (X n ω0) (next_state n a ω0)) (x' a) ); intros.
        apply almost_prob_space_sa_sub_lift in H10.
        revert H10; apply almost_impl.
        generalize (ConditionalVariance_scale prts (filt_sub n) γ (Xmin n a)); intros.
        apply almost_prob_space_sa_sub_lift in H10.
        revert H10; apply almost_impl.
        apply all_almost; intros ??????.
        unfold FT.
        assert ( Rbar_le
                   (ConditionalVariance prts (filt_sub n)
                      (fun ω0 : Ts =>
                         cost n a ω0 + γ * qlearn_Qmin (X n ω0) (next_state n a ω0)) x)
                   (2 * A +
                      2 *
                        Rsqr (Rmax_norm {x0 : state M & act M x0}
                                (fun sa0 : {x0 : state M & act M x0} => X n x sa0)))).
        {
           eapply Rbar_le_trans.
           apply H13.
           rewrite <- Rmult_plus_distr_l.
           unfold Rbar_rvmult, Rbar_rvplus, const.
           replace (Finite
                      (2 *
                         (A +
                            Rsqr (Rmax_norm {x0 : state M & act M x0}
                                    (fun sa0 : {x0 : state M & act M x0} => X n x sa0)))))
              with
              (Rbar_mult 2 (Rbar_plus A (Rsqr (Rmax_norm {x0 : state M & act M x0} (fun sa0 : {x0 : state M & act M x0} => X n x sa0) )))) by now simpl.
           apply Rbar_mult_le_compat_l.
           + simpl; lra.
           + apply Rbar_plus_le_compat.
             * apply H15.
             * rewrite H10.
               unfold ConditionalVariance.
               erewrite FiniteCondexp_eq.
               unfold Rbar_rvscale.
               rewrite <- Rmax_all_norm_nneg in H14 by apply nnfsqr.
               rewrite <- Rmax_norm_sqr.
               rewrite <- Rbar_le_Rle in H14.
               eapply Rle_trans; cycle 1.
               apply H14.
               assert ( Rsqr γ <= 1).
               {
                 rewrite <- Rsqr_1.
                 apply Rsqr_le_abs_1.
                 rewrite Rabs_right; try lra.
                 rewrite Rabs_right; try lra.
               }
               eapply Rle_trans.
               apply Rmult_le_compat_r.
               - apply FiniteCondexp_nneg.
                 apply nnfsqr.
               - apply H16.
               - rewrite Rmult_1_l.
                 right.
                 apply FiniteConditionalExpectation_ext.
                 reflexivity.
         }
         rewrite <- Rsqr_pow2.         
        rewrite <- H12 in H16.
        eapply Rbar_le_trans; cycle 1.
        apply H16.
        apply slln.eq_Rbar_le.
        apply ConditionalVariance_ext.
        reflexivity.
      }
      destruct H12 as [A [B [? [??]]]].
      assert (exists (c1 c2 : R),
                 0 <= c1 /\ 0 <= c2 /\
                 forall k ω,
                   (Rmax_norm {x : state M & act M x} (fun sa0 : {x : state M & act M x} => X k ω sa0) ^ 2) <=
                     c1 + c2 * (Rmax_norm {x : state M & act M x} (fun sa0 : {x : state M & act M x} => X k ω sa0 - x' sa0)) ^ 2).
      {
        exists (2 * (Rmax_norm {x : state M & act M x} x')^2).
        exists 2.
        intros.
        split; [| split].
        - apply Rmult_le_pos; [lra |].
          apply pow2_ge_0.
        - lra.
        - intros k ω.
          specialize (H11 (Rmax_norm {x : state M & act M x} (fun sa0 : {x : state M & act M x} => X k ω sa0)) (Rmax_norm {x : state M & act M x} x')).
          repeat rewrite <- Rsqr_pow2.
          etransitivity; [eapply H11 |].
          rewrite <- Rmult_plus_distr_l.
          apply Rmult_le_compat_l; [lra |].
          rewrite Rplus_comm.
          apply Rplus_le_compat_l.
          apply Rsqr_le_abs_1.
          etransitivity; [apply Rmax_list_minus_le_abs |]; simpl.
          rewrite Rabs_right.
          + apply Rmax_list_le_proper.
            apply Forall2_map_f.
            apply Forall2_refl_in.
            rewrite Forall_forall; intros ? _.
            apply Rabs_triang_inv2.
          + apply Rle_ge.
            apply Rmax_list_Rabs_pos.
      }
      destruct H15 as [c1 [c2 [? [??]]]].
      exists ((A + B*c1) + B*c2).
      assert (0 < A + B*c1 + B*c2).
      {
        eapply Rlt_le_trans.
        apply H12.
        assert (0 <= B * c1 + B * c2).
        {
          rewrite <- Rmult_plus_distr_l.
          apply Rmult_le_pos; try lra.
        }
        lra.
      }
      split; trivial.
      revert H14.
      apply almost_impl.
      apply all_almost; intros ??.
      intros.
      specialize (H14 k sa).
      eapply Rbar_le_trans.
      apply H14.
      rewrite Rbar_le_Rle.
      specialize (H17 k x).
      apply Rmult_le_compat_l with (r := B) in H17; try lra.
      apply Rplus_le_compat_l with (r := A) in H17.
      eapply Rle_trans.
      apply H17.
      rewrite Rmult_plus_distr_l.
      rewrite <- Rplus_assoc.
      rewrite <- Rmult_assoc.

      assert (0 <= A + B * c1).
      {
        apply Rplus_le_le_0_compat; try lra.
        apply Rmult_le_pos; lra.
      }
      assert (0 <= B * c2).
      {
        apply Rmult_le_pos; lra.
      }
      do 2 rewrite <- Rsqr_pow2.
      assert (0 <= Rmax_norm {x0 : state M & act M x0} (fun sa0 : {x0 : state M & act M x0} => X k x sa0 - x' sa0)).
      {
        apply Rmax_norm_nneg.
      }
      apply (jaakkola_tsitsiklis_coefs2 (mknonnegreal _ H21) (mknonnegreal _ H19) (mknonnegreal _ H20)).
     - intros.
       unfold X, FT.
       simpl.
       now ring_simplify.
   Qed.
              
End qlearn.

