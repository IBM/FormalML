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
Require Import vecslln Tsitsiklis.
Require Import ConditionalExpectation VectorConditionalExpectation.
Require Import IndefiniteDescription ClassicalDescription.
Require slln.
Require Import RelationClasses.

Set Bullet Behavior "Strict Subproofs".

(* move somewhere earlier *)
Lemma eventually_bounded_forall (N:nat) P : 
  (forall (i : nat) (pf : (i < N)%nat), eventually (P i pf)) ->
  eventually (fun n => forall i pf, P i pf n).
Proof.
  induction N.
  - intros.
    exists 0%nat; intros; lia.
  - intros HH.
    specialize (IHN (fun x pf => P x (lt_S _ _ pf))).
    cut_to IHN.
    + simpl in IHN.
      specialize (HH N (Nat.lt_succ_diag_r _)).
      revert HH; apply eventually_impl.
      revert IHN; apply eventually_impl.
      apply all_eventually; intros.
      destruct (Nat.eq_dec i N).
      * subst.
        now rewrite (digit_pf_irrel _ _ _ pf) in H0.
      * assert (pf2 : (i < N)%nat) by lia.
        specialize (H i pf2).
        now rewrite (digit_pf_irrel _ _ _ pf) in H.
    + intros.
      apply HH.
Qed.

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

 Lemma Rmult_not_0 (x y : R) :
       (x <> 0) /\ (y <> 0) -> x * y <> 0.
 Proof.
   intros.
   unfold not.
   intro zz.
   destruct H.
   replace 0 with (x * 0) in zz.
   apply Rmult_eq_reg_l in zz; try lra.
   apply Rmult_0_r.
 Qed.

 
 Lemma Rdiv_not_0 (x y : R) :
       (x <> 0) /\ (y <> 0) -> x / y <> 0.
 Proof.
   intros.
   unfold Rdiv.
   apply Rmult_not_0.
   destruct H.
   split; trivial.
   now apply Rinv_neq_0_compat.
 Qed.

 Lemma Rvector_scale_not_0 (x:R) (y : vector R N) :
       (x <> 0) /\ (y <> Rvector_zero) -> Rvector_scale x y <> Rvector_zero.
 Proof.
   intros.
   unfold not.
   intro zz.
   destruct H.
   rewrite <- Rvector_scale_zero with (c := x) in zz.
   now apply Rvector_scale_inj in zz.
 Qed.

 Lemma Rvector_max_abs_nzero (v : vector R N) :
   v <> Rvector_zero -> Rvector_max_abs v <> 0.
 Proof.
   unfold not.
   intros.
   apply Rvector_max_abs_zero in H0.
   now apply H in H0.
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
  
Lemma gamma_C (gamma : R) :
  0 < gamma < 1 ->
  forall (C : R),
    C > gamma / (1-gamma) ->
    0 < C /\
    gamma * (C + 1)/C < 1.
Proof.
  intros.
  assert (0 < C).
  {
    apply Rgt_lt in H0.
    eapply Rlt_trans; [|apply H0].
    apply Rdiv_lt_0_compat; lra.
  }
  split; trivial.
  apply Rmult_lt_reg_r with (r := C); trivial.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym; try lra.
  rewrite Rmult_1_l.
  rewrite Rmult_1_r.
  apply Rmult_gt_compat_r with (r := (1 - gamma)) in H0; try lra.
  unfold Rdiv in H0.
  rewrite Rmult_assoc in H0.
  rewrite <- Rinv_l_sym in H0; lra.
Qed.

Lemma Rvector_max_abs_const {n : nat} (c : R) :
  Rvector_max_abs (vector_const c (S n)) = Rabs c.
Proof.
  destruct (Rvector_max_abs_nth_in (vector_const c (S n))) as [?[? eqq]].
  rewrite eqq.
  now rewrite vector_nth_const.
Qed.

Lemma delta_eps_bound (gamma : R) (eps : posreal) (C : posreal) (delta : vector R (S N)) :
  0 < gamma ->
  Rvector_max_abs delta > C * eps ->
  gamma * Rvector_max_abs (Rvector_plus delta (vector_const (pos eps) (S N))) <=
    gamma * (C + 1)/ C * Rvector_max_abs delta.
Proof.
  intros.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l; try lra.
  rewrite <- Rmult_1_l at 1.
  rewrite (Rinv_l_sym C) at 1.
  - rewrite <- Rmult_assoc.
    rewrite (Rmult_comm (C + 1) _).
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    + left.
      apply Rinv_pos.
      apply cond_pos.
    + replace (pos C) with (Rabs C) at 1.
      * rewrite <- Rvector_max_abs_scale.
        rewrite Rvector_scale_plus_l.
        eapply Rle_trans.
        -- apply Rvector_max_abs_triang.
        -- rewrite Rvector_scale_const.
           rewrite Rvector_max_abs_const.
           rewrite Rabs_right.
           ++ apply Rgt_lt in H0.
              apply Rplus_lt_compat_l with (r := Rvector_max_abs (Rvector_scale C delta)) in H0.
              eapply Rle_trans.
              ** left; apply H0.
              ** rewrite Rvector_max_abs_scale.
                 right.
                 rewrite Rabs_right; try lra.
                 left; apply cond_pos.
          ++ apply Rle_ge.
             apply Rmult_le_pos; left; apply cond_pos.
      * apply Rabs_right; apply Rle_ge; left; apply cond_pos.
  - apply Rgt_not_eq.
    apply cond_pos.
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

Lemma gamma_eps_le_alt (gamma : posreal) :
  gamma < 1 ->
  exists (eps : posreal),
  forall (eps2 : posreal),
    eps2 <= eps ->
    gamma <= / (1 + eps2).
Proof.
  intros.
  destruct (gamma_eps_le gamma H).
  exists x.
  intros.
  eapply Rle_trans.
  apply r.
  generalize (cond_pos x); intros.
  generalize (cond_pos eps2); intros.
  apply Rle_Rinv; lra.
Qed.

Lemma gamma_eps_le_forall (gamma eps : posreal) :
  gamma <=  / (1 + eps) ->
  forall (eps2 : posreal),
    eps2 <= eps ->
    gamma <= / (1 + eps2).
Proof.
  intros.
  eapply Rle_trans.
  apply H.
  generalize (cond_pos eps); intros.
  generalize (cond_pos eps2); intros.
  apply Rle_Rinv; lra.
Qed.


    Lemma conv_as_prob_1_eps_alt (f : nat -> Ts -> R) (fstar: R)
      {rv : forall n, RandomVariable dom borel_sa (f n)} :
      almost prts (fun x => is_lim_seq (fun n => f n x) fstar) ->
      forall (eps1 eps2:posreal),
        eventually (fun n => ps_P (event_le dom (rvabs (rvminus (f n) (const fstar))) eps1) >= 1 - eps2).
    Proof.
      intros.
      apply conv_as_prob_1_eps_le.
      revert H.
      apply almost_impl; apply all_almost.
      intros ??.
      apply is_lim_seq_plus with (l1 := fstar) (l2 := -1 * fstar); trivial.
      - apply is_lim_seq_const.
      - unfold is_Rbar_plus; simpl.
        f_equal.
        f_equal.
        lra.
    Qed.

    Lemma conv_as_prob_1_eps_forall_alt (f : nat -> Ts -> R) (fstar: R)
      {rv : forall n, RandomVariable dom borel_sa (f n)} :
      almost prts (fun x => is_lim_seq (fun n => f n x) fstar) ->
      forall (eps1 eps2:posreal),
        eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvabs (rvminus (f (n + n0)%nat) (const fstar))) eps1))) >= 1 - eps2).
    Proof.
      intros.
      generalize (conv_as_prob_1_eps_forall_le (fun n =>  rvminus (f n) (const fstar))); intros.
      cut_to H0.
      - apply H0.
      - revert H.
        apply almost_impl; apply all_almost.
        intros ??.
        apply is_lim_seq_plus with (l1 := fstar) (l2 := -1 * fstar); trivial.
        + apply is_lim_seq_const.
        + unfold is_Rbar_plus; simpl.
          f_equal.
          f_equal.
          lra.
    Qed.

    Lemma conv_as_prob_1_eps_vector_forall_alt (f : nat -> Ts -> vector R N) (fstar: vector R N)
      {rv : forall n, RandomVariable dom (Rvector_borel_sa N) (f n)} :
      (forall i pf, almost prts (fun x => is_lim_seq (fun n => vector_nth i pf (f n x)) (vector_nth i pf fstar))) ->
      forall (eps1 eps2:posreal),
        forall i pf,
        eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvabs (rvminus (vecrvnth i pf (f (n + n0)%nat)) (const (vector_nth i pf fstar)))) eps1))) >= 1 - eps2).
    Proof.
      intros.
      generalize (conv_as_prob_1_eps_forall_le (fun n =>  rvminus (vecrvnth i pf (f n)) (const (vector_nth i pf fstar)))); intros.
      cut_to H0.
      - apply H0.
      - specialize (H i pf).
        revert H.
        apply almost_impl; apply all_almost.
        intros ??.
        apply is_lim_seq_plus with (l1 := vector_nth i pf fstar) (l2 := -1 * (vector_nth i pf fstar)); trivial.
        + apply is_lim_seq_const.
        + unfold is_Rbar_plus; simpl.
          f_equal.
          f_equal.
          lra.
    Qed.

    Lemma conv_as_prob_1_eps_vector_forall_alt2 (f : nat -> Ts -> vector R N) (fstar: vector R N)
      {rv : forall n, RandomVariable dom (Rvector_borel_sa N) (f n)} :
      (forall i pf, almost prts (fun x => is_lim_seq (fun n => vector_nth i pf (f n x)) (vector_nth i pf fstar))) ->
      forall (eps1 eps2:posreal),
        eventually (fun n0 => ps_P (inter_of_collection (fun n => (event_le dom (rvmaxabs (vecrvminus (f (n + n0)%nat) (const fstar))) eps1))) >= 1 - eps2).
    Proof.
      intros.
      generalize (conv_as_prob_1_rvmaxabs_forall_le (fun n =>  vecrvminus (f n) (const fstar))); intros.
      cut_to H0.
      - apply H0.
      - apply conv_as_prob_1_vec.
        + intros.
          apply Rvector_minus_rv; trivial.
          apply rvconst.
        + intros.
          specialize (H i pf).
          revert H.
          apply almost_impl; apply all_almost.
          intros ??.
          assert (is_lim_seq
                    (fun n : nat => rvminus (vecrvnth i pf (f n)) (const (vector_nth i pf fstar)) x)
                    0).
          {
            apply is_lim_seq_plus with (l1 := vector_nth i pf fstar) (l2 := -1 * (vector_nth i pf fstar)); trivial.
            + apply is_lim_seq_const.
            + unfold is_Rbar_plus; simpl.
              f_equal.
              f_equal.
              lra.
         }
         revert H1.
         apply is_lim_seq_ext.
         intros.
         unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, const.
         rewrite Rvector_nth_plus, Rvector_nth_scale.
         rv_unfold.
         now unfold vecrvnth.
    Qed.

(*
    Lemma lemma3_gamma_eps (gamma : posreal) :
      gamma < 1 ->
      exists (eps : posreal),
      forall (eps2 : posreal), 
        eps2 <= eps ->
        gamma + (1 - gamma)/2 <= / (1 + eps2).
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
      apply (gamma_eps_le_alt _ H1).
    Qed.      
*)

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
      
     generalize (conv_as_prob_1_eps_vector_forall_alt2 f fstar H (mkposreal _ H1) eps2).
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
    
   Lemma ps_inter_cond_prob_r {T:Type} {σ:SigmaAlgebra T} 
      (A B : event σ) (prts' : ProbSpace σ) :
     ps_P B > 0 ->
     ps_P (event_inter A B) = (cond_prob prts' A B) * ps_P B.
   Proof.
     intros.
     unfold cond_prob, Rdiv.
     rewrite Rmult_assoc, Rinv_l; lra.
   Qed.

   Lemma ps_inter_cond_prob_l {T:Type} {σ:SigmaAlgebra T} 
      (A B : event σ) (prts' : ProbSpace σ) :
     ps_P A > 0 ->
     ps_P (event_inter A B) = ps_P A * (cond_prob prts' B A).
   Proof.
     intros.
     rewrite event_inter_comm, ps_inter_cond_prob_r; lra.
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

        Lemma Lim_y_m1 :
          Lim (fun y => y / (1 - y)) 0 = 0.
        Proof.
          rewrite Lim_div.
          - rewrite Lim_id, Lim_minus, Lim_const, Lim_id.
            + simpl; f_equal; lra.
            + apply ex_lim_const.
            + apply ex_lim_id.
            + now rewrite Lim_const, Lim_id.
          - apply ex_lim_id.
          - apply ex_lim_minus.
            + apply ex_lim_const.
            + apply ex_lim_id.
            + now rewrite Lim_const, Lim_id.
          - rewrite Lim_minus.
            + rewrite Lim_const, Lim_id.
              simpl.
              replace (1 + - 0) with 1 by lra.
              rewrite Rbar_finite_eq; lra.
            + apply ex_lim_const.
            + apply ex_lim_id.
            + now rewrite Lim_const, Lim_id.
          - rewrite Lim_id, Lim_minus, Lim_const, Lim_id; try easy.
            + apply ex_lim_const.
            + apply ex_lim_id.
            + now rewrite Lim_const, Lim_id.
        Qed.

        Lemma ex_lim_y_m1 :
          ex_lim (fun y => (y / (1 - y))) 0.
        Proof.
          apply ex_lim_div.
          + apply ex_lim_id.
          + apply ex_lim_minus.
            * apply ex_lim_const.
            * apply ex_lim_id.
            * now rewrite Lim_const, Lim_id.
          + rewrite Lim_minus.
            * rewrite Lim_const, Lim_id.
              simpl.
              rewrite Rbar_finite_eq; lra.
            * apply ex_lim_const.
            * apply ex_lim_id.
            * now rewrite Lim_const, Lim_id.
          + rewrite Lim_id, Lim_minus.
            * now rewrite Lim_const, Lim_id.
            * apply ex_lim_const.
            * apply ex_lim_id.
            * now rewrite Lim_const, Lim_id.
        Qed.

        Lemma Lim_Rabs (c : R) :
          Lim Rabs c = Rabs c.
        Proof.
          apply Lim_continuity.
          apply Rcontinuity_abs.
        Qed.

        Lemma is_lim_Rabs (c : R) :
          is_lim Rabs c (Rabs c).
        Proof.
          apply is_lim_continuity.
          apply Rcontinuity_abs.
        Qed.

        Lemma ex_lim_Rabs (c : R) :
          ex_lim Rabs c.
        Proof.
          eexists.
          apply is_lim_Rabs.
        Qed.

        Lemma ex_lim_Rabs_y_m1 :
          ex_lim (fun y => (Rabs y / (1 - Rabs y))) 0.
        Proof.
          apply ex_lim_div.
          + apply ex_lim_Rabs.
          + apply ex_lim_minus.
            * apply ex_lim_const.
            * apply ex_lim_Rabs.
            * now rewrite Lim_const, Lim_Rabs.
          + rewrite Lim_minus.
            * rewrite Lim_const, Lim_Rabs, Rabs_R0.
              simpl.
              rewrite Rbar_finite_eq; lra.
            * apply ex_lim_const.
            * apply ex_lim_Rabs.
            * now rewrite Lim_const, Lim_Rabs.
          + rewrite Lim_Rabs, Lim_minus.
            * now rewrite Lim_const, Lim_Rabs.
            * apply ex_lim_const.
            * apply ex_lim_Rabs.
            * now rewrite Lim_const, Lim_Rabs.
        Qed.

        Lemma Lim_Rabs_y_m1 :
          Lim (fun y => Rabs y / (1 - Rabs y)) 0 = 0.
        Proof.
          rewrite (Lim_comp (fun y => y / (1 - y)) Rabs 0).
          - now rewrite Lim_Rabs, Rabs_R0, Lim_y_m1.
          - rewrite Lim_Rabs, Rabs_R0.
            apply ex_lim_y_m1.
          - apply ex_lim_Rabs.
          - assert (0 < 1) by lra.
            exists (mkposreal _ H).
            intros.
            rewrite Lim_Rabs, Rabs_R0.
            unfold not; intros.
            rewrite Rbar_finite_eq in H2.
            apply Rabs_eq_0 in H2.
            lra.
        Qed.

        Lemma Lim_c_y_m1 (c : R) :
          Lim (fun y => c * (y / (1 - y))) 0 = 0.
        Proof.
          rewrite Lim_scal_l, Lim_y_m1.
          simpl.
          now rewrite Rmult_0_r.
        Qed.

        Lemma Lim_c_Rabs_y_m1 (c : R) :
          Lim (fun y => c * (Rabs y / (1 - Rabs y))) 0 = 0.
        Proof.
          rewrite Lim_scal_l, Lim_Rabs_y_m1.
          simpl.
          now rewrite Rmult_0_r.
        Qed.

        Lemma ex_lim_c_y_m1 (c : R) :
          ex_lim (fun y => c * (y / (1 - y))) 0.
        Proof.
          apply ex_lim_scal_l.
          apply ex_lim_y_m1.
        Qed.

        Lemma ex_lim_c_Rabs_y_m1 (c : R) :
          ex_lim (fun y => c * (Rabs y / (1 - Rabs y))) 0.
        Proof.
          apply ex_lim_scal_l.
          apply ex_lim_Rabs_y_m1.
        Qed.

        Lemma is_lim_c_y_m1 (c : R) :
          is_lim (fun y => c * (y / (1 - y))) 0 0.
        Proof.
          rewrite <- Lim_c_y_m1 at 2.
          apply Lim_correct.
          apply ex_lim_c_y_m1.
        Qed.
        
        Lemma Lim_exp_c_y_m1 (c : R) :
          c <> 0 ->
          Lim (fun y => exp (c * (y / (1 - y)))) 0 = 1.
        Proof.
          intros cn0.
          rewrite Lim_comp.
          - rewrite Lim_c_y_m1.
            rewrite Lim_exp.
            now rewrite exp_0.
          - rewrite Lim_c_y_m1.
            apply ex_lim_exp.
          - apply ex_lim_c_y_m1.
          - assert (0 < 1/2) by lra.
            exists (mkposreal _ H).
            intros.
            rewrite Lim_c_y_m1.
            unfold not; intros.
            unfold ball in H0.
            simpl in H0.
            unfold AbsRing_ball in H0.
            unfold abs, minus,plus, opp in H0; simpl in H0.
            replace (y + - 0) with y in H0 by lra.
            rewrite Rbar_finite_eq in H2.
            apply Rmult_integral in H2.
            destruct H2; try easy.
            unfold Rdiv in H2.
            apply Rmult_integral in H2.
            destruct H2; try easy.
            rewrite <- Rinv_0 in H2.
            apply (f_equal (fun z => /z)) in H2.
            rewrite Rinv_inv, Rinv_inv in H2.
            rewrite Rabs_lt_both in H0.
            lra.
        Qed.

         Lemma Lim_exp_c_Rabs_y_m1 (c : R) :
          c <> 0 ->
          Lim (fun y => exp (c * (Rabs y / (1 - Rabs y)))) 0 = 1.
        Proof.
          intros cn0.
          rewrite Lim_comp.
          - rewrite Lim_c_Rabs_y_m1.
            rewrite Lim_exp.
            now rewrite exp_0.
          - rewrite Lim_c_Rabs_y_m1.
            apply ex_lim_exp.
          - apply ex_lim_c_Rabs_y_m1.
          - assert (0 < 1/2) by lra.
            exists (mkposreal _ H).
            intros.
            rewrite Lim_c_Rabs_y_m1.
            unfold not; intros.
            unfold ball in H0.
            simpl in H0.
            unfold AbsRing_ball in H0.
            unfold abs, minus,plus, opp in H0; simpl in H0.
            replace (y + - 0) with y in H0 by lra.
            rewrite Rbar_finite_eq in H2.
            apply Rmult_integral in H2.
            destruct H2; try easy.
            unfold Rdiv in H2.
            apply Rmult_integral in H2.
            destruct H2.
            + now apply Rabs_eq_0 in H2.
            + rewrite <- Rinv_0 in H2.
              apply (f_equal (fun z => /z)) in H2.
              rewrite Rinv_inv, Rinv_inv in H2.
              lra.
          Qed.

        Lemma is_lim_exp_c_y_m1 (c : R) :
          c <> 0 ->
          is_lim (fun y => exp (c * (y / (1 - y)))) 0 1.
        Proof.
          intros cn0.
          rewrite <- (Lim_exp_c_y_m1 c cn0).
          apply Lim_correct.
          apply ex_lim_comp.
          - apply ex_lim_exp.
          - apply ex_lim_c_y_m1.
          - assert (0 < 1/2) by lra.
            exists (mkposreal _ H).
            intros.
            rewrite Lim_c_y_m1.
            unfold not; intros.
            unfold ball in H0.
            simpl in H0.
            unfold AbsRing_ball in H0.
            unfold abs, minus,plus, opp in H0; simpl in H0.
            replace (y + - 0) with y in H0 by lra.
            rewrite Rbar_finite_eq in H2.
            apply Rmult_integral in H2.
            destruct H2; try easy.
            unfold Rdiv in H2.
            apply Rmult_integral in H2.
            destruct H2; try easy.
            rewrite <- Rinv_0 in H2.
            apply (f_equal (fun z => /z)) in H2.
            rewrite Rinv_inv, Rinv_inv in H2.
            rewrite Rabs_lt_both in H0.
            lra.
         Qed.

        Lemma is_lim_exp_c_Rabs_y_m1 (c : R) :
          c <> 0 ->
          is_lim (fun y => exp (c * (Rabs y / (1 - Rabs y)))) 0 1.
        Proof.
          intros cn0.
          rewrite <- (Lim_exp_c_Rabs_y_m1 c cn0).
          apply Lim_correct.
          apply ex_lim_comp.
          - apply ex_lim_exp.
          - apply ex_lim_c_Rabs_y_m1.
          - assert (0 < 1/2) by lra.
            exists (mkposreal _ H).
            intros.
            rewrite Lim_c_Rabs_y_m1.
            unfold not; intros.
            unfold ball in H0.
            simpl in H0.
            unfold AbsRing_ball in H0.
            unfold abs, minus,plus, opp in H0; simpl in H0.
            replace (y + - 0) with y in H0 by lra.
            rewrite Rbar_finite_eq in H2.
            apply Rmult_integral in H2.
            destruct H2; try easy.
            unfold Rdiv in H2.
            apply Rmult_integral in H2.
            destruct H2.
            + now apply Rabs_eq_0 in H2.
            + rewrite <- Rinv_0 in H2.
              apply (f_equal (fun z => /z)) in H2.
              rewrite Rinv_inv, Rinv_inv in H2.
              lra.
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

        Lemma is_ps_lim_inf  (E : nat -> event dom) :
          let Einf := fun k => inter_of_collection (fun n => E (n + k)%nat) in
          is_lim_seq (fun n => ps_P (Einf n)) (ps_P (union_of_collection Einf)).
        Proof.
          apply is_lim_ascending.
          intros ??.
          simpl.
          intros.
          specialize (H (S n0)).
          now replace (n0 + S n)%nat with (S n0 + n)%nat by lia.
        Qed.

        Lemma ps_lim_inf  (E : nat -> event dom) :
          let Einf := fun k => inter_of_collection (fun n => E (n + k)%nat) in
          Lim_seq (fun n => ps_P (Einf n)) = (ps_P (union_of_collection Einf)).
        Proof.
          apply lim_ascending.
          intros ??.
          simpl.
          intros.
          specialize (H (S n0)).
          now replace (n0 + S n)%nat with (S n0 + n)%nat by lia.
        Qed.

        Lemma ps_inter_inf0  (E : nat -> event dom) :
          Rbar_le (ps_P (inter_of_collection E)) (Inf_seq (fun k : nat => ps_P (E k))).
        Proof.
          rewrite <- (Inf_seq_const (ps_P (inter_of_collection E))).
          apply Inf_seq_le.
          intros.
          simpl.
          apply ps_sub.
          intros ??.
          now specialize (H n).
        Qed.

        Lemma ps_inter_inf  (E : nat -> event dom) :
          let Einf := fun k => inter_of_collection (fun n => E (n + k)%nat) in
          Rbar_le 
            (ps_P (union_of_collection Einf))
            (Lim_seq (fun n => Inf_seq (fun k => ps_P (E (k + n)%nat)))).
        Proof.
          intros.
          unfold Einf.
          rewrite <- ps_lim_inf.
          apply Lim_seq_le.
          intros.
          generalize (ps_inter_inf0 (fun k => E (k + n)%nat)); intros.
          assert (is_finite  (Inf_seq (fun k : nat => ps_P (E (k + n)%nat)))).
          {
            apply bounded_is_finite with (a := 0) (b := 1).
            - rewrite <- (Inf_seq_const 0).
              apply Inf_seq_le.
              intros.
              simpl.
              apply ps_pos.
            - rewrite <- (Inf_seq_const 1).  
              apply Inf_seq_le.
              intros.
              simpl.
              apply ps_le1.
          }
          rewrite <- H0 in H.
          now simpl in H.
        Qed.
          

        Lemma ps_inter_inf_alt  (E : nat -> event dom) :
          let Einf := fun k => inter_of_collection (fun n => E (n + k)%nat) in
          Rbar_le 
            (ps_P (union_of_collection Einf))
            (ELim_seq (fun n => Inf_seq (fun k => ps_P (E (k + n)%nat)))).
        Proof.
          intros.
          unfold Einf.
          rewrite <- ps_lim_inf.
          rewrite <- Elim_seq_fin.
          apply ELim_seq_le.
          intros.
          apply ps_inter_inf0.
        Qed.

        Lemma is_ps_lim_sup  (E : nat -> event dom) :
          let Esup := fun k => union_of_collection (fun n => E (n + k)%nat) in
          is_lim_seq (fun n => ps_P (Esup n)) (ps_P (inter_of_collection Esup)).
        Proof.
          apply is_lim_descending.
          intros ??.
          simpl.
          intros.
          destruct H.
          exists (S x0).
          now replace (S x0 + n)%nat with (x0 +S n)%nat by lia.
       Qed.

        Lemma ps_lim_sup  (E : nat -> event dom) :
          let Esup := fun k => union_of_collection (fun n => E (n + k)%nat) in
          Lim_seq (fun n => ps_P (Esup n)) = (ps_P (inter_of_collection Esup)).
        Proof.
          apply lim_descending.
          intros ??.
          simpl.
          intros.
          destruct H.
          exists (S x0).
          now replace (S x0 + n)%nat with (x0 +S n)%nat by lia.
       Qed.

        Lemma ps_union_sup0  (E : nat -> event dom) :
          Rbar_le (Sup_seq (fun k : nat => ps_P (E k))) (ps_P (union_of_collection E)).
        Proof.
          rewrite <- (Sup_seq_const (ps_P (union_of_collection E))).
          apply Sup_seq_le.
          intros.
          simpl.
          apply ps_sub.
          intros ??.
          simpl.
          now exists n.
        Qed.

        Lemma ps_union_sup  (E : nat -> event dom) :
          let Esup := fun k => union_of_collection (fun n => E (n + k)%nat) in
          Rbar_le 
            (Lim_seq (fun n => Sup_seq (fun k => ps_P (E (k + n)%nat))))
            (ps_P (inter_of_collection Esup)).
        Proof.
          intros.
          unfold Esup.
          rewrite <- ps_lim_sup.
          apply Lim_seq_le.
          intros.
          generalize (ps_union_sup0 (fun k => E (k + n)%nat)); intros.
          assert (is_finite  (Sup_seq (fun k : nat => ps_P (E (k + n)%nat)))).
          {
            apply bounded_is_finite with (a := 0) (b := 1).
            - rewrite <- (Sup_seq_const 0).
              apply Sup_seq_le.
              intros.
              simpl.
              apply ps_pos.
            - rewrite <- (Sup_seq_const 1).  
              apply Sup_seq_le.
              intros.
              simpl.
              apply ps_le1.
          }
          rewrite <- H0 in H.
          now simpl in H.
        Qed.

        Lemma ps_union_sup_alt  (E : nat -> event dom) :
          let Esup := fun k => union_of_collection (fun n => E (n + k)%nat) in
          Rbar_le 
            (ELim_seq (fun n => Sup_seq (fun k => ps_P (E (k + n)%nat))))
            (ps_P (inter_of_collection Esup)).
        Proof.
          intros.
          unfold Esup.
          rewrite <- ps_lim_sup.
          rewrite <- Elim_seq_fin.
          apply ELim_seq_le.
          intros.
          apply ps_union_sup0.
        Qed.

        Lemma Sup_seq_ps_P_fin  (E : nat -> event dom) :
          forall n,
            is_finite  (Sup_seq (fun k : nat => ps_P (E (k + n)%nat))).
          Proof.
            intros.
            apply bounded_is_finite with (a := 0) (b := 1).
            - rewrite <- (Sup_seq_const 0).
              apply Sup_seq_le.
              intros.
              simpl.
              apply ps_pos.
            - rewrite <- (Sup_seq_const 1).  
              apply Sup_seq_le.
              intros.
              simpl.
              apply ps_le1.
        Qed.

        Lemma ps_union_sup_fin  (E : nat -> event dom) :
          let Esup := fun k => union_of_collection (fun n => E (n + k)%nat) in
          (Lim_seq (fun n => Sup_seq (fun k => ps_P (E (k + n)%nat)))) <=
            (ps_P (inter_of_collection Esup)).
         Proof.
           generalize (ps_union_sup E); intros.
           simpl in H.
           assert (forall n,
                      is_finite  (Sup_seq (fun k : nat => ps_P (E (k + n)%nat)))).
           {
             intros.
            apply bounded_is_finite with (a := 0) (b := 1).
            - rewrite <- (Sup_seq_const 0).
              apply Sup_seq_le.
              intros.
              simpl.
              apply ps_pos.
            - rewrite <- (Sup_seq_const 1).  
              apply Sup_seq_le.
              intros.
              simpl.
              apply ps_le1.
          }
          assert (is_finite (Lim_seq (fun n : nat => Sup_seq (fun k : nat => ps_P (E (k + n)%nat))))).
          {
            apply bounded_is_finite with (a := 0) (b := 1).
            - rewrite <- (Lim_seq_const 0).
              apply Lim_seq_le.
              intros.
              assert (Rbar_le 0
                        (Sup_seq (fun k : nat => ps_P (E (k + n)%nat)))).
              {
                rewrite <- (Sup_seq_const 0).
                apply Sup_seq_le.
                intros.
                simpl.
                apply ps_pos.
              }
              rewrite <- H0 in H1.
              now simpl in H1.
            - rewrite <- (Lim_seq_const 1).
              apply Lim_seq_le.
              intros.
              assert (Rbar_le 
                        (Sup_seq (fun k : nat => ps_P (E (k + n)%nat))) 
                        1).
              {
                rewrite <- (Sup_seq_const 1).
                apply Sup_seq_le.
                intros.
                simpl.
                apply ps_le1.
              }
              rewrite <- H0 in H1.
              now simpl in H1.
           }
           rewrite <- H1 in H.
           now simpl in H.
         Qed.

         Lemma Inf_seq_ElimInf_seq_le (f : nat -> Rbar) :
           Rbar_le (Inf_seq f) (ELimInf_seq f).
         Proof.
           generalize (inf_ElimInf f 0%nat); intros.
           eapply Rbar_le_trans; cycle 1.
           apply H.
           apply Inf_seq_le.
           intros.
           replace (n + 0)%nat with n by lia.
           apply Rbar_le_refl.
         Qed.

         Lemma Inf_seq_Elim_seq_le (f : nat -> Rbar) :
           Rbar_le (Inf_seq f) (ELim_seq f).
         Proof.
           eapply Rbar_le_trans.
           apply Inf_seq_ElimInf_seq_le.
           apply ELimInf_ELim_seq_le.
        Qed.

         Lemma ElimSup_Sup (f : nat -> Rbar) :
           Rbar_le (ELimSup_seq f) (Sup_seq f).
           Proof.
             rewrite ELimSup_InfSup_seq.
             rewrite Inf_eq_glb.
             unfold Rbar_glb.
             match goal with
               [|- context [proj1_sig ?x ]] => destruct x; simpl
             end.
             destruct r as [lb glb].
             apply lb; eauto.
             exists (0%nat).
             apply Sup_seq_ext.
             intros.
             now replace (n + 0)%nat with n by lia.
           Qed.

         Lemma ELim_seq_Sup_seq_le (f : nat -> Rbar) :
           Rbar_le (ELim_seq f) (Sup_seq f).
         Proof.
           eapply Rbar_le_trans.
           apply ELimSup_ELim_seq_le.
           apply ElimSup_Sup.
         Qed.

        Lemma ps_is_lim_seq  (E : nat -> event dom) :
          let Einf := fun k => inter_of_collection (fun n => E (n + k)%nat) in
          let Esup := fun k => union_of_collection (fun n => E (n + k)%nat) in
          event_equiv (union_of_collection Einf) (inter_of_collection Esup) ->
          is_lim_seq (fun n => ps_P (E n)) (ps_P (inter_of_collection Esup)).
        Proof.
          intros.
          assert (ps_P (union_of_collection Einf) = ps_P (inter_of_collection Esup)).
          {
            apply ps_proper.
            now rewrite H.
          }
          generalize (ps_union_sup_alt E); intros union.
          generalize (ps_inter_inf_alt E); intros inter.
          assert (LimInf_seq (fun n => ps_P (E n)) = LimSup_seq (fun n => ps_P (E n))).
          {
            apply Rbar_le_antisym.
            - apply LimSup_LimInf_seq_le.
            - rewrite LimInf_SupInf_seq.
              rewrite LimSup_InfSup_seq.
              eapply Rbar_le_trans.
              apply Inf_seq_Elim_seq_le.
              eapply Rbar_le_trans.
              apply union.
              unfold Esup in H0.
              rewrite <- H0.
              eapply Rbar_le_trans.
              apply inter.
              apply ELim_seq_Sup_seq_le.
          }
          assert (Lim_seq (fun n => ps_P (E n)) = ps_P (inter_of_collection Esup)).
          {
            unfold Lim_seq.
            rewrite H1.
            rewrite x_plus_x_div_2.
            apply Rbar_le_antisym.
            - rewrite LimSup_InfSup_seq.
              eapply Rbar_le_trans.
              apply Inf_seq_Elim_seq_le.
              apply union.
            - rewrite <- H1.
              rewrite LimInf_SupInf_seq.
              rewrite <- H0.
              eapply Rbar_le_trans.
              apply inter.
              apply ELim_seq_Sup_seq_le.
          }
          rewrite <- H2.
          apply Lim_seq_correct.
          now rewrite ex_lim_LimSup_LimInf_seq.
        Qed.

       Lemma lemma3_plim0 :
         filterlim (fun y => real (Lim_seq (fun m => prod_f_R0 (fun n => 1 - (Rabs y) ^ S n) m)))
           (at_right 0) (Rbar_locally 1).
       Proof.
         generalize lemma3_plim_Rabs.
         apply filterlim_filter_le_1.
         intros ??.
         destruct H as [eps ?].
         exists eps.
         intros.
         apply H; trivial.
         lra.
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

       Definition is_lim_pos (f : posreal -> R) (l : Rbar) :=
         filterlim (fun y => lift_posreal_f f 0 y) (at_right 0) (Rbar_locally l).

       Lemma lemma3_plim_pos :
         is_lim_pos (fun (y : posreal) => real (Lim_seq (fun m => prod_f_R0 (fun n => 1 - y ^ S n) m))) 1.
       Proof.
         apply lemma3_plim.
       Qed.

       Lemma filterlim_const_at_right0 (c : R) :
         filterlim (fun _ => c) (at_right 0) (Rbar_locally c).
       Proof.
         apply filterlim_const.
       Qed.

       Lemma filterlim_at_right_0_Rbar_ext (f g : R -> R) (l : Rbar) :
         (forall x, 0 < x -> f x = g x) ->
         filterlim f (at_right 0) (Rbar_locally l) <-> filterlim g (at_right 0) (Rbar_locally l).
       Proof.
         intros.
         split; apply filterlim_within_ext.
         - apply H.
         - symmetry; now apply H.
       Qed.

       Lemma filterlim_at_right_0_ext (f g : R -> R) (l : R) :
         (forall x, 0 < x -> f x = g x) ->
         filterlim f (at_right 0) (locally l) <-> filterlim g (at_right 0) (locally l).
       Proof.
         intros.
         split; apply filterlim_within_ext.
         - apply H.
         - symmetry; now apply H.
       Qed.

       Lemma is_lim_pos_ext (f g : posreal -> R)  (l : R) :
         (forall x, f x = g x) ->
         is_lim_pos f l <-> is_lim_pos g l.
       Proof.
         intros.
         apply filterlim_at_right_0_ext.
         intros.
         unfold lift_posreal_f.
         match_destr.
       Qed.

       Lemma event_sub_eventually {A} {σ: SigmaAlgebra A} (pe: nat -> event σ):
         forall n,
           event_sub (inter_of_collection (fun n0 => pe (n + n0)%nat))
                     (event_eventually pe).
       Proof.
         intros ???.
         exists n.
         intros.
         specialize (H (n0 - n)%nat).
         simpl in H.
         now replace (n + (n0 - n))%nat with n0 in H by lia.
       Qed.

(*
       Lemma lemma3 (α β X : nat -> Ts -> vector R (S N)) (C γ : posreal)
         (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) 
         (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n)) 
         (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n)) :           
         (forall t ω i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
         (forall t ω i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
         (forall t ω i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->                  
         (forall ω i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
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
         (*         almost prts (fun ω => Lim_seq (fun n => rvmaxabs (X n) ω) = 0). *)
         almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
      Proof.
        intros.
        generalize (lemma3_vector_forall_eventually_prob_iter_alt α β X C γ _ _ _); intros.
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
*)
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
         (*         almost prts (fun ω => Lim_seq (fun n => rvmaxabs (X n) ω) = 0). *)
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

   Definition vecrvchoice {Ts : Type} {n : nat} (c : Ts -> bool) (rv_X1 rv_X2 : Ts -> vector R n) (omega : Ts) := if c omega then rv_X1 omega else rv_X2 omega.

   Instance vecrvchoice_measurable {n} (c: Ts -> R) (f g : Ts -> vector R n) :
      RealMeasurable dom c ->
      RealVectorMeasurable f ->
      RealVectorMeasurable g ->
      RealVectorMeasurable (vecrvchoice (fun x => if Req_EM_T (c x) 0 then false else true) f g).
    Proof.
      unfold RealVectorMeasurable.
      intros.
      generalize (rvchoice_measurable dom c (vector_nth i pf (fun_to_vector_to_vector_of_funs f)) (vector_nth i pf (fun_to_vector_to_vector_of_funs g))); intros.
      cut_to H2; trivial.
      revert H2.
      apply RealMeasurable_proper.
      intros ?.
      unfold vecrvchoice, rvchoice; simpl.
      rewrite vector_nth_fun_to_vector.
      now match_destr; rewrite vector_nth_fun_to_vector.
    Qed.

    Instance vecrvchoice_rv {n} (c: Ts -> R) (f g : Ts -> vector R n)
      {rvc:RandomVariable dom borel_sa c}
      {rvf:RandomVariable dom (Rvector_borel_sa n) f}
      {rvg:RandomVariable dom (Rvector_borel_sa n) g} :
      RandomVariable dom (Rvector_borel_sa n) (vecrvchoice (fun x => if Req_EM_T (c x) 0 then false else true) f g).
    Proof.
      apply RealVectorMeasurableRandomVariable.
      apply vecrvchoice_measurable.
      - now apply rv_measurable.
      - now apply RandomVariableRealVectorMeasurable.
      - now apply RandomVariableRealVectorMeasurable.
    Qed.

    Instance vecrvchoiceb_rv {n} (c: Ts -> bool) (f g : Ts -> vector R n)
      {rvc:RandomVariable dom (discrete_sa bool) c}
      {rvf:RandomVariable dom (Rvector_borel_sa n) f}
      {rvg:RandomVariable dom (Rvector_borel_sa n) g} :
      RandomVariable dom (Rvector_borel_sa n) (vecrvchoice c f g).
    Proof.
      cut (RandomVariable dom (Rvector_borel_sa n)
             (vecrvchoice
                (fun x => if Req_EM_T (if (c x) then 1 else 0) 0
                       then false else true) f g)).
        {
          apply RandomVariable_proper; try reflexivity.
          intros ?.
          unfold vecrvchoice.
          destruct (c a); destruct (Req_EM_T _ _); trivial; lra.
        }
        apply vecrvchoice_rv; trivial.
        assert (frf_complete : forall x : Ts, In ((fun x : Ts => if c x then 1 else 0) x) (0::1::nil)).
        {
          intros ?; match_destr; simpl; tauto.
        } 
        apply (frf_singleton_rv _ (Build_FiniteRangeFunction _ _ frf_complete)).
        intros ? [?|[?|?]]; [subst .. | tauto].
        - unfold pre_event_singleton, pre_event_preimage.
          assert (saf:sa_sigma (discrete_sa bool) (fun x => x = false)) by apply I.
          generalize (rvc (exist _ _ saf)).
          apply sa_proper.
          intros ?; simpl.
          match_destr; try tauto.
          split.
          + lra.
          + intros; discriminate.
        - unfold pre_event_singleton, pre_event_preimage.
          assert (sat:sa_sigma (discrete_sa bool) (fun x => x = true)) by apply I.
          generalize (rvc (exist _ _ sat)).
          apply sa_proper.
          intros ?; simpl.
          match_destr; try tauto.
          split.
          + lra.
          + intros; discriminate.
      Qed.

    Instance vecrvchoiceb_restricted_rv {n}
      (rv_C : Ts -> bool)
      (rv_X1 rv_X2 : Ts -> vector R n)
      {rvc : RandomVariable dom (discrete_sa bool) rv_C}
      {rv1 : RandomVariable (event_restricted_sigma
              (exist (sa_sigma dom) (fun x : Ts => rv_C x = true)
                 (rvc
                    (exist (fun e : pre_event bool => sa_sigma (discrete_sa bool) e)
                       (fun x : bool => x = true) I))))
               (Rvector_borel_sa n) (event_restricted_function (exist _ (fun x => rv_C x = true) (rvc (exist _ (fun x => x = true) I))) rv_X1)}
      {rv2 : RandomVariable (event_restricted_sigma
              (exist (sa_sigma dom) (fun x : Ts => rv_C x = false)
                 (rvc
                    (exist (fun e : pre_event bool => sa_sigma (discrete_sa bool) e)
                       (fun x : bool => x = false) I))))
               (Rvector_borel_sa n) (event_restricted_function (exist _ (fun x => rv_C x = false) (rvc (exist _ (fun x => x = false) I))) rv_X2)}  :
      RandomVariable dom (Rvector_borel_sa n) (vecrvchoice rv_C rv_X1 rv_X2).
    Proof.
      apply rv_vecrvnth; intros i pf.
      generalize (@rvchoiceb_restricted_rv _ dom rv_C (vector_nth i pf (fun_to_vector_to_vector_of_funs rv_X1)) (vector_nth i pf (fun_to_vector_to_vector_of_funs rv_X2)) rvc); intros.
      cut_to H; trivial.
      - revert H.
        apply RandomVariable_proper; try reflexivity.
        intros ?.
        unfold vecrvnth, vecrvchoice, rvchoice.
        rewrite vector_nth_fun_to_vector.
        match_destr.
        now rewrite vector_nth_fun_to_vector.
      - apply (@vecrvnth_rv _ _ _ _ pf) in rv1.
        revert rv1.
        apply RandomVariable_proper; try reflexivity; intros ?.
        now rewrite vector_nth_fun_to_vector.
      - apply (@vecrvnth_rv _ _ _ _ pf) in rv2.
        revert rv2.
        apply RandomVariable_proper; try reflexivity; intros ?.
        now rewrite vector_nth_fun_to_vector.
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
     apply (@vecrvchoiceb_restricted_rv _ _ _ _ rv_C); trivial.
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

   Lemma Rvector_scale_comm {n : nat} (a b : R) (v : vector R n) :
     Rvector_scale a (Rvector_scale b v) = Rvector_scale b (Rvector_scale a v).
   Proof.
     repeat rewrite Rvector_scale_scale.
     now rewrite Rmult_comm.
   Qed.

(*
       Lemma lemma3_full (α β X : nat -> Ts -> vector R (S N)) (γ : posreal)
         (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n)) 
         (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n)) 
         (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n)) :           
         (forall t ω i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
         (forall t ω i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
         (forall t ω i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->                  
         (forall ω i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
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
         generalize (lemma3 α β XC C γ); intros.
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
*)

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

(*
      Lemma lemma3_2 (α β X XX : nat -> Ts -> vector R (S N)) 
        (G : nat -> Ts -> vector R (S N) -> vector R (S N)) 
        (C γ : posreal)
        (rvX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (X n))
        (rvXX : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (XX n))         
        (rva : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (α n)) 
        (rvb : forall n, RandomVariable dom (Rvector_borel_sa (S N)) (β n)) :           
        (forall t ω i pf, 0 <= vector_nth i pf (α t ω) <= 1) ->
        (forall t ω i pf, 0 <= vector_nth i pf (β t ω) <= 1) ->
        (forall t ω i pf, vector_nth i pf (β t ω) <= vector_nth i pf (α t ω)) ->                  
        (forall ω i pf, l1_divergent (fun n : nat => vector_nth i pf (α n ω))) ->
        γ < 1 ->
        
        (forall n w V, G n w V =
                     Rvector_plus
                       (Rvector_minus V (Rvector_mult (α n w) V))
                       (Rvector_scale (Rvector_max_abs V)
                          (Rvector_scale γ (β n w)))) ->
        (forall n, rv_eq (X (S n))
                     (vecrvplus 
                        (vecrvminus (X n)
                           (vecrvmult (α n) (X n)))
                        (vecrvscalerv (rvmaxabs (X n))
                           (vecrvscale γ (β n))))) ->
        (rv_eq (XX 0%nat) (vecrvclip (S N) (X 0%nat) (pos_to_nneg C))) ->
        (forall n, rv_eq (XX (S n))
                     (vecrvclip (S N)
                        (vecrvplus 
                           (vecrvminus (XX n)
                              (vecrvmult (α n) (XX n)))
                           (vecrvscalerv (rvmaxabs (XX n))
                              (vecrvscale γ (β n))))
                        (pos_to_nneg C))) ->
        almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
      Proof.
        intros.
        generalize (lemma3 α β XX C γ); intros.
        cut_to H8; trivial.
        generalize (lemma2 (S N) X XX G C); intros.
        apply H9; trivial.
        - intros ??.
          rewrite H5, H4.
          reflexivity.
        - intros ??.
          rewrite H7.
          assert (rv_eq
                     (vecrvplus (vecrvminus (XX n) (vecrvmult (α n) (XX n)))
                        (vecrvscalerv (rvmaxabs (XX n)) (vecrvscale γ (β n))))
                      (fun w : Ts => G n w (XX n w))).
          {
            intros ?.
            rewrite H4.
            reflexivity.
          }
          f_equal.
          apply functional_extensionality.
          intros.
          rewrite H4.
          reflexivity.
        - intros ???.
          rewrite H4.
          rewrite H4.
          rewrite Rvector_scale_plus_l.
          f_equal.
          + unfold Rvector_minus.
            rewrite Rvector_scale_plus_l.
            f_equal.
            rewrite Rvector_scale_mult_r.
            unfold Rvector_opp.
            rewrite Rvector_scale_scale.
            rewrite Rvector_scale_scale.
            f_equal; lra.
          + rewrite Rvector_max_abs_scale.
            rewrite Rvector_scale_scale.
            f_equal.
            f_equal.
            rewrite Rabs_right; trivial.
            apply Rle_ge.
            apply cond_nonneg.
        - intros ???.
          rewrite H4.
          rewrite H4.
          rewrite Rvector_scale_plus_l.
          f_equal.
          + unfold Rvector_minus.
            rewrite Rvector_scale_plus_l.
            f_equal.
            rewrite Rvector_scale_mult_r.
            unfold Rvector_opp.
            rewrite Rvector_scale_scale.
            rewrite Rvector_scale_scale.
            f_equal; lra.
          + rewrite Rvector_max_abs_scale.
            rewrite Rvector_scale_scale.
            f_equal.
            f_equal.
            rewrite Rabs_right; trivial.
            apply Rle_ge.
            apply cond_nonneg.
        - intros.
          intros ?.
          unfold rvmaxabs.
          destruct n.
          + rewrite H6.
            apply vecrvclip_max_bound.
          + rewrite H7.
            apply vecrvclip_max_bound.
      Qed.
*)
      Lemma almost_is_lim_nth_maxabs {NN} (X : nat -> Ts -> vector R (S NN)) :
        almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0) ->
        forall k pf,
          almost prts (fun x : Ts => is_lim_seq (fun m : nat => vector_nth k pf (X m x)) 0).
      Proof.
        intros.
        revert H.
        apply almost_impl.
        apply all_almost.
        intros ??.
        assert (is_lim_seq (fun n => - (rvmaxabs (X n) x)) 0).
        {
          rewrite is_lim_seq_opp in H.
          simpl in H.
          now rewrite Ropp_0 in H.
        }
        eapply (is_lim_seq_le_le _ _ _ 0 _ H0 H).
        Unshelve.
        intros.
        simpl.
        apply Rabs_le_between.
        apply Rvector_max_abs_nth_le.
      Qed.

    Lemma almost_is_lim_nth_maxabs_alt {NN} (X : nat -> Ts -> vector R (S NN)) :
      (forall k pf,
          almost prts (fun x : Ts => is_lim_seq (fun m : nat => vector_nth k pf (X m x)) 0)) ->
        almost prts (fun ω => is_lim_seq (fun n => rvmaxabs (X n) ω) 0).
    Proof.
      intros.
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

  Theorem Jaakkola_alpha_beta_bounded {n} 
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R (S n))
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa (S n)) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa (S n)) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa (S n)) (X 0%nat)}
    (npos : (0 < n)%nat)
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa (S n)) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))}
    {isfe2 : forall k i pf, IsFiniteExpectation prts 
                              (rvsqr (rvminus (vecrvnth i pf (XF k))
                                        (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k)))))} :
    0 < γ < 1 ->
      
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω) <= 1) ->
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <= vector_nth i pf (α k ω)) ->        

(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->

    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (α k ω))))) (Finite C))) ->
    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (β k ω))))) (Finite C))) ->

    (forall k i pf ω, 
        Rabs ((FiniteConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω) <=
          (γ * (Rvector_max_abs (X k ω)))) ->

    (exists (C : R),
        0 < C /\
        forall k i pf ω, 
          Rbar_le ((FiniteConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
            (C * (1 + Rvector_max_abs (X k ω))^2)) ->                  
    (exists (C : R), forall k ω, Rvector_max_abs (X k ω) <= C) ->
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k)))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
  Proof.
    intros.
    assert (rvXF2 : forall k, RandomVariable dom (Rvector_borel_sa (S n)) (XF k)).
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
                | 0%nat => vecrvconst (S n) 0
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
        assert (pf3 : (i < (S n))%nat).
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
    assert (exists C, forall k i pf ω, (FiniteConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k)) ω) <= C).
    {
      destruct H8 as [? [??]].
      destruct H9.
      exists (x * (1 + x0)^2).
      intros.
      eapply Rle_trans.
      apply H12.
      simpl.
      apply Rmult_le_compat_l; try lra.
      repeat rewrite Rmult_1_r.
      assert (0 <= x0).
      {
        eapply Rle_trans; cycle 1.
        apply (H9 0%nat ω).
        apply Rvector_max_abs_nonneg.
      }
      generalize (Rvector_max_abs_nonneg (X k ω)); intros.
      specialize (H9 k ω).
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
        rewrite <- H18.
        now apply ConditionalExpectation_ext.
      }
      revert H17.
      apply almost_impl.
      apply all_almost.
      intros ??.
      rewrite <- H17.
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
    destruct H5 as [Ca ?].
    destruct H6 as [Cb ?].
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

    assert (forall k i pf, IsFiniteExpectation prts (rvsqr (vecrvnth i pf (r k)))).
    {
      intros.
      unfold r.
      generalize (isfe2 k i pf).
      apply IsFiniteExpectation_proper.
      intros ?.
      unfold rvsqr.
      f_equal.
      now rewrite eqvec.
    }
    assert (exists B,
             forall k i pf ω,
               (FiniteConditionalExpectation prts (filt_sub k) (rvsqr (vecrvnth i pf (r k)))) ω <=  (Rsqr B)).
    {
      unfold FiniteConditionalVariance in H12.
      destruct H12 as [C ?].
      assert (0 <= Rmax 0 C).
      {
        apply Rmax_l.
      }
      exists (Rsqrt (mknonnegreal _ H18)).
      intros.
      specialize (H12 k i pf ω).
      unfold r.
      unfold Rsqr.
      rewrite Rsqrt_Rsqrt.
      simpl.
      assert (C <= Rmax 0 C) by apply Rmax_r.
      eapply Rle_trans; cycle 1.
      apply H19.
      eapply Rle_trans; cycle 1.
      apply H12.
      right.
      apply FiniteConditionalExpectation_ext.
      intros ?.
      unfold rvsqr.
      f_equal.
      now rewrite eqvec.
    }
    destruct H18 as [B ?].
    assert (lim_w_0: forall (i : nat) (pf : (i < S n)%nat),
                almost prts
                  (fun ω : Ts => is_lim_seq (fun n0 : nat => vector_nth i pf (w n0 ω)) 0)).
    {
      intros n1 pf.
      generalize (fun i pf => lemma1_bounded_alpha_beta 
                                (fun k ω => vector_nth i pf (α k ω))
                                (fun k ω => vector_nth i pf (β k ω))
                                (fun k ω => vector_nth i pf (r k ω))
                                (fun k ω => vector_nth i pf (w k ω)) Ca Cb); intros.
      specialize (H19 n1 pf B _ isfilt filt_sub _ _).
      apply H19; clear H19.
      - unfold IsAdapted; intros.
        apply vecrvnth_rv.
        unfold r.
        apply Rvector_minus_rv.
        + apply rvXF.
        + apply (RandomVariable_sa_sub (isfilt n0)).
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
        apply H16.
      - intros.
        specialize (H18 n0 n1 pf).
        apply all_almost; intros.
        generalize (FiniteCondexp_eq prts (filt_sub n0)); intros.
        specialize (H19 (rvsqr (fun ω : Ts => vector_nth n1 pf (r n0 ω)))
                      (@rvsqr_rv Ts dom (@vecrvnth Ts R (S n) n1 pf (r n0)) (H13 n0 n1 pf))).
        assert (IsFiniteExpectation prts (rvsqr (fun ω : Ts => vector_nth n1 pf (r n0 ω)))).
        {
          generalize (isfe2 n0 n1 pf).
          apply IsFiniteExpectation_proper.
          intros ?.
          unfold rvsqr.
          f_equal.
          unfold r.
          rewrite <- eqvec.
          reflexivity.
        }
        specialize (H19 H20).
        unfold vecrvnth in H19.
        rewrite H19.
        simpl.
        unfold const.
        eapply Rle_trans; [| apply (H18 x)].
        right.
        apply FiniteConditionalExpectation_ext.
        reflexivity.
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
      - apply H5.
      - apply H6.
      - intros.
        simpl.
        unfold vecrvminus, vecrvmult, vecrvplus, vecrvopp, vecrvscale.
        repeat rewrite Rvector_nth_plus.
        rewrite Rvector_nth_scale.
        repeat rewrite Rvector_nth_mult.
        lra.
   }
    apply almost_bounded_forall; intros.
    - apply lt_dec.
    - revert H19.
      apply is_lim_seq_ext.
      intros.
      apply vector_nth_ext.
    - assert (forall n1 : nat, RandomVariable dom (Rvector_borel_sa (S n)) (w n1)).
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
      assert (forall n1 : nat, RandomVariable dom borel_sa (fun ω : Ts => vector_nth n0 pf (w n1 ω))).
      {
          intros.
          now apply vecrvnth_rv.
      }
      generalize lim_w_0; intros lim_maxabs_0.
      apply almost_is_lim_nth_maxabs_alt in lim_maxabs_0.
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
                     Rvector_max_abs (Rvector_plus (Rvector_abs (δ k ω)) (@vector_const R eps (S n))) <= ((C + 1)/C) * Rvector_max_abs(δ k ω)).
        {
          intros.
          replace (Rvector_max_abs (Rvector_plus (Rvector_abs (δ k ω)) (@vector_const R eps (S n)))) with
            ((Rvector_max_abs (Rvector_plus (Rvector_scale C (Rvector_abs (δ k ω))) (Rvector_scale C (@vector_const R eps (S n)))))/C).
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
          revert H0.
          apply almost_impl.
          revert H1.
          apply almost_impl.
          apply all_almost; intros ω??.
          intros.
          simpl.
          unfold vecrvminus, vecrvopp, vecrvplus, vecrvscale, vecrvmult.
          repeat rewrite Rvector_nth_plus.
          rewrite Rvector_nth_scale.
          repeat rewrite  Rvector_nth_mult.
          replace  (vector_nth i pf0 (δ n1 ω) +
                    -1 * (vector_nth i pf0 (α n1 ω) * vector_nth i pf0 (δ n1 ω))) with
            ((1 - vector_nth i pf0 (α n1 ω)) * (vector_nth i pf0 (δ n1 ω))) by lra.
          eapply Rle_trans.
          apply Rabs_triang.
          specialize (H0 n1 i pf0).
          specialize (H1 n1 i pf0).
          rewrite Rabs_mult, Rabs_right; try lra.
          apply Rplus_le_compat_l.
          rewrite Rabs_mult, Rabs_right; try lra.
          rewrite (Rmult_comm γ _).
          rewrite Rmult_assoc.
          apply Rmult_le_compat_l; try lra.
          rewrite vector_FiniteConditionalExpectation_nth.
          specialize (H7 n1 i pf0 ω).
          rewrite H11 in H7.
          eapply Rle_trans; cycle 1.
          assert ( γ * Rvector_max_abs (vecrvplus (δ n1) (w n1) ω) <=
                     γ * Rvector_max_abs (Rvector_plus (Rvector_abs (δ n1 ω)) (Rvector_abs (w n1 ω)))).
          {
            apply Rmult_le_compat_l; try lra.
            unfold vecrvplus.
            apply Rvector_max_abs_le.
            intros.
            rewrite Rvector_nth_plus.
            rewrite Rvector_nth_plus.
            eapply Rle_trans.
            apply Rabs_triang.
            unfold Rvector_abs.
            rewrite vector_nth_map.
            rewrite vector_nth_map.
            generalize (Rabs_pos (vector_nth i0 pf1 (δ n1 ω)) ); intros.
            generalize (Rabs_pos  (vector_nth i0 pf1 (w n1 ω))); intros.
            rewrite (Rabs_right (Rabs (vector_nth i0 pf1 (δ n1 ω)) + Rabs (vector_nth i0 pf1 (w n1 ω)))); lra.
          }
          apply H25.
          eapply Rle_trans; cycle 1.
          apply H7.
          right.
          f_equal.
          now apply FiniteConditionalExpectation_ext.
        }
        assert (rv_alpha: forall n1,
                   RandomVariable dom (Rvector_borel_sa (S n)) (α n1)).
        {
          intros.
          now apply (RandomVariable_sa_sub (filt_sub n1)).
        }
        assert (rv_beta: forall n1,
                   RandomVariable dom (Rvector_borel_sa (S n)) (β n1)).
        {
          intros.
          now apply (RandomVariable_sa_sub (filt_sub n1)).
        }
        assert (rv_delta: forall n1,
                   RandomVariable dom (Rvector_borel_sa (S n)) (δ n1)).
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
                                    (vecrvconst (S n) eps))))))).
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
                                                        (vecrvconst (S n) eps)))))))))))
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
          replace (vector_nth i pf0 (vecrvabs (δ (x0 + n1)%nat) x1) +
                   -1 * (vector_nth i pf0 (α (x0 + n1)%nat x1) * vector_nth i pf0 (vecrvabs (δ (x0 + n1)%nat) x1))) with
            ((1 - vector_nth i pf0 (α (x0 + n1)%nat x1)) * vector_nth i pf0 (vecrvabs (δ (x0 + n1)%nat) x1)) by lra.
          unfold vecrvabs.
          replace (vector_nth i pf0 (Rvector_abs (δ (x0 + n1)%nat x1))) with
            (Rabs (vector_nth i pf0 (δ (x0 + n1)%nat x1))).
          - apply Rplus_le_compat_l.
            rewrite Rmult_assoc.
            apply Rmult_le_compat_l; try lra.
            apply Rmult_le_compat_l.
            + apply H33.
            + unfold rvabs, vecrvnth in H32.
              specialize (H32 n1).
              replace (n1 + x0)%nat with (x0 + n1)%nat in H32 by lia.
              unfold rvmaxabs in H32.
              rewrite Rabs_Rvector_max_abs in H32.
              apply Rvector_max_abs_le.
              intros.
              rewrite Rvector_nth_plus.
              rewrite Rvector_nth_plus.
              unfold Rvector_abs.
              repeat rewrite vector_nth_map.
              rewrite (Rabs_right  (Rabs (vector_nth i0 pf1 (δ (x0+n1)%nat x1)) + Rabs (vector_nth i0 pf1 (w (x0 + n1)%nat x1)))).
              rewrite vector_nth_const.
              rewrite (Rabs_right (Rplus (Rabs (@vector_nth R (S n) i0 pf1 (δ (x0 +n1)%nat x1))) (pos eps))).
              * apply Rplus_le_compat_l.
                left.
                eapply Rle_lt_trans.
                apply Rvector_max_abs_nth_le.
                apply H32.
              * generalize (Rabs_pos (vector_nth i0 pf1 (δ (x0+n1)%nat x1))); intros.
                generalize (cond_pos eps); intros.
                lra.
              * generalize (Rabs_pos  (vector_nth i0 pf1 (δ (x0+n1)%nat x1))); intros.
                generalize (Rabs_pos (vector_nth i0 pf1 (w (x0+n1)%nat x1))); intros.
                lra.
          - unfold Rvector_abs.
            now rewrite vector_nth_map.
        }
(*
        assert (forall (eps : posreal) (i : nat) (pf : (i < S n)%nat),
                   eventually
                     (fun n0 : nat =>
                        ps_P
                          (inter_of_collection
                             (fun n1 : nat =>
                                event_le dom (rvabs (vecrvnth i pf (δ (n0 + n1)%nat)))
                                  (C * eps)))
                        >= 1 - eps)).
*)

        assert (rvlimsup: forall (i : nat) (pf : (i < S n)%nat),
                   RandomVariable dom borel_sa
                     (fun (ω : Ts) => real (ELimSup_seq (fun n => vector_nth i pf (δ n ω))))).
        {
          intros.
          apply measurable_rv.
          apply Rbar_real_measurable.
          apply Rbar_lim_sup_measurable.
          intros.
          rewrite <- RealMeasurable_RbarMeasurable.
          apply rv_measurable.
          now apply vecrvnth_rv.
        }

        assert (HH1: forall (eps : posreal) (i : nat) (pf : (i < S n)%nat),
                   ps_P (event_le
                           dom
                           (fun (ω : Ts) => real (ELimSup_seq (fun n => vector_nth i pf (δ n ω))))
                           (C * eps)) >= 1-eps).
        {
          intros eps i pf0.
          specialize (H28 eps).
          destruct H28.
          specialize (H28 x).
          cut_to H28; try lia.
          generalize almost_independent_impl; intros HH.
          
          generalize (almost_and _ (almost_and _ H0 H1) H2); intros.
          destruct H29 as [? [??]].
          assert
            (ps_P
               (event_inter x0
                            (inter_of_collection
             (fun n1 : nat =>
              bounded_inter_of_collection
                (fun (i : nat) (pf : (i < S n)%nat) =>
                 event_Rle dom (rvabs (vecrvnth i pf (δ (S (x + n1)))))
                   (rvplus
                      (vecrvnth i pf
                         (vecrvminus (vecrvabs (δ (x + n1)%nat)) (vecrvmult (α (x + n1)%nat) (vecrvabs (δ (x + n1)%nat)))))
                      (rvscale γ
                         (rvmult (vecrvnth i pf (β (x + n1)%nat))
                            (rvmaxabs (vecrvplus (vecrvabs (δ (x + n1)%nat)) (vecrvconst (S n) eps))))))))))
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
                specialize (H34 (x2 + k)%nat i0 pf1).
                apply Rge_le in H34.
                unfold rvabs, vecrvnth in H34.
                replace (S (x + (x2 + k))) with (x + (x2 + S k))%nat in H34 by lia.
                eapply Rle_trans.
                apply H34.
                unfold vecrvminus, vecrvmult, vecrvplus, vecrvopp, vecrvabs, vecrvconst, vecrvscale, rvmaxabs, rvscale, rvmult, rvplus.
                rewrite Rvector_nth_plus, Rvector_nth_scale, Rvector_nth_mult.
                generalize (cond_pos eps); intros.
                rewrite Rvector_max_abs_plus_nneg; try lra.
                unfold Rvector_abs.
                rewrite vector_nth_map.
                replace (Rabs (vector_nth i0 pf1 (δ (x + (x2 + k))%nat x1)) +
                         -1 * (vector_nth i0 pf1 (α (x + (x2 + k))%nat x1) * Rabs (vector_nth i0 pf1 (δ (x + (x2 + k))%nat x1))))
                  with
                  ((1 - (vector_nth i0 pf1 (α (x + (x2 + k))%nat x1))) * Rabs (vector_nth i0 pf1 (δ (x + (x2 + k))%nat x1))) by lra.
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
                apply Rmult_le_compat_l with (r :=  γ * (vector_nth i0 pf1 (β (x + (x2 + k))%nat x1))) in H38.
                + assert (γ * vector_nth i0 pf1 (β (x + (x2 + k))%nat x1) * (Rvector_max_abs (δ (x + (x2 + k))%nat x1) + eps) <=
                            (vector_nth i0 pf1 (α (x + (x2 + k))%nat x1) * (C * eps))).
                  {
                    eapply Rle_trans.
                    apply H38.
                    generalize (cond_pos eps); intros.
                    assert  (γ * (C + 1) <= C) by lra.
                    apply Rmult_le_compat_r with (r := eps) in H40; try lra.
                    apply Rmult_le_compat_l with (r := vector_nth i0 pf1 (β (x + (x2 + k))%nat x1)) in H40.
                    apply Rle_trans with (r2 := vector_nth i0 pf1 (β (x + (x2 + k))%nat x1) * (C * eps)); try lra.
                    apply Rmult_le_compat_r.
                    apply Rmult_le_pos; lra.
                    apply H36.
                    apply H35.
                  }
                  apply Rplus_le_compat_l with (r :=  (1 - vector_nth i0 pf1 (α (x + (x2 + k))%nat x1)) * Rabs (vector_nth i0 pf1 (δ (x + (x2 + k))%nat x1))) in H39.
                  rewrite <- Rmult_assoc.
                  eapply Rle_trans.
                  apply H39.
                  assert (Rabs (vector_nth i0 pf1 (δ (x + (x2 + k))%nat x1)) <= C * eps).
                  {
                    now rewrite Rvector_max_abs_nth_le.
                  }
                  apply Rmult_le_compat_l with (r := (1 - vector_nth i0 pf1 (α (x + (x2 + k))%nat x1)) ) in H40.
                  apply Rplus_le_compat_r with (r := vector_nth i0 pf1 (α (x + (x2 + k))%nat x1) * (C * eps)) in H40.
                  eapply Rle_trans.
                  apply H40.
                  rewrite <- Rmult_plus_distr_r; try lra.
                  specialize (H30 (x + (x2 + k))%nat i0 pf1); try lra.
             + apply Rmult_le_pos; try lra.
               apply H35.
            }
            rewrite ELimSup_seq_fin.
            generalize (LimSup_le  (fun x3 : nat => vector_nth i pf0 (δ x3 x1)) (const (C * eps))); intros.
            unfold const in H35.
            rewrite LimSup_seq_const in H35.
            admit.
          - assert (forall n0,  Rvector_max_abs (δ (x + n0)%nat x1) > C * eps).
            {
              intros.
              specialize (n1 n2).
              now apply Rnot_le_gt in n1.
           }
           
           admit.
            
            
(*          assert (aa : Ts) by admit.
          case_eq (chooser aa).

            apply Rnot_le_gt.
          
*)
       }
        assert (almost prts (fun ω : Ts => is_lim_seq (fun n1 : nat => vector_nth n0 pf (δ n1 ω)) 0)).
        {
          admit.
        }
        revert H29.
        apply almost_impl.
        specialize (lim_w_0 n0 pf).
        revert lim_w_0.
        apply almost_impl.
        apply all_almost; intros ???.
        generalize (is_lim_seq_plus' _ _ _ _ H30 H29).
        rewrite Rplus_0_r.
        apply is_lim_seq_ext.
        intros.
        rewrite H11.
        unfold vecrvplus.
        now rewrite Rvector_nth_plus.
  Admitted.

  Theorem Jaakkola_alpha_beta_bounded_eventually_almost {n} 
    (γ : R) 
    (X XF α β : nat -> Ts -> vector R n)
    {F : nat -> SigmaAlgebra Ts}
    (isfilt : IsFiltration F) 
    (filt_sub : forall k, sa_sub (F k) dom) 
    (adapt_alpha : IsAdapted (Rvector_borel_sa n) α F)
    (adapt_beta : IsAdapted (Rvector_borel_sa n) β F)    
    {rvX0 : RandomVariable (F 0%nat) (Rvector_borel_sa n) (X 0%nat)}
    (npos : (0 < n)%nat)
    {rvXF : forall k, RandomVariable (F (S k)) (Rvector_borel_sa n) (XF k)}
    {rvXF_I : forall k i pf, RandomVariable dom borel_sa (vecrvnth i pf (XF k))}
    {isfe : forall k i pf, IsFiniteExpectation prts (vecrvnth i pf (XF k))}
    {rv2 : forall k i pf, RandomVariable dom borel_sa
                            (rvsqr (rvminus (vecrvnth i pf (XF k))
                                      (FiniteConditionalExpectation prts (filt_sub k) (vecrvnth i pf (XF k)))))} : 


    0 < γ < 1 ->

    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (α k ω)) ->
    almost prts (fun ω => forall k i pf, 0 <= vector_nth i pf (β k ω)) ->
    eventually (fun k => almost prts (fun ω => forall i pf, vector_nth i pf (α k ω) <= 1)) ->          
    eventually (fun k => almost prts (fun ω => forall i pf, vector_nth i pf (β k ω) <= 1)) ->      
    almost prts (fun ω => forall k i pf, vector_nth i pf (β k ω) <=  vector_nth i pf (α k ω)) ->        

(*    (forall i pf, (almost prts (fun ω => is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty))) ->
*)
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (α k ω))) p_infty) ->
    almost prts (fun ω => forall i pf, is_lim_seq (sum_n (fun k => vector_nth i pf (β k ω))) p_infty) ->
    (exists (C : R),
        forall i pf,
          almost prts (fun ω => Rbar_le (Lim_seq (sum_n (fun k : nat => Rsqr (vector_nth i pf (β k ω))))) (Finite C))) ->

    (forall k i pf ω, 
        Rbar_le ((ConditionalExpectation _ (filt_sub k) ((vecrvnth i pf (XF k)))) ω)
                 (γ * (Rvector_max_abs (X k ω)))) ->

    (exists (C : R),
        0 < C /\
        forall k i pf ω, 
          Rbar_le ((ConditionalVariance prts (filt_sub k) (vecrvnth i pf (XF k))) ω)
             (C * (1 + Rvector_max_abs (X k ω))^2)) ->                  

    (exists (C : R), forall k ω, Rvector_max_abs (X k ω) <= C) ->
    
    (forall k, rv_eq (X (S k)) 
                 (vecrvplus (vecrvminus (X k) (vecrvmult (α k) (X k))) (vecrvmult (β k) (XF k) ))) ->
    almost prts (fun ω =>
                   forall i pf,
                     is_lim_seq (fun m => vector_nth i pf (X m ω)) 0).
 Proof.
   Admitted.

 End jaakola_vector2.
