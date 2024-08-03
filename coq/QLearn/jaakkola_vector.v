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

Context (gamma : R) (α : nat -> R) {Ts : Type} {SS:Type} (N:nat)
        {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

Program Definition pos_to_nneg (c : posreal) : nonnegreal :=
  mknonnegreal c _.
Next Obligation.
  left; apply cond_pos.
Qed.

Lemma lemma2_0 (x : SS) (w : Ts)
      (X : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N )
      (C : posreal)   :
  (forall n,  rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (X n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (X n x w)) (Y n w) x))) ->
  (exists n, X n x w = Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs (X n x w)) 0.
 Proof.
  intros XG XGB H.
  destruct H.
  apply is_lim_seq_ext_loc with (u := fun n => 0).
  - exists x0.
    intros.
    pose (h := (n - x0)%nat).
    replace n with (x0 + h)%nat by lia.
    induction h.
    + replace (x0 + 0)%nat with (x0) by lia.
      rewrite H.
      symmetry.
      now rewrite Rvector_max_abs_zero.
    + replace (x0 + S h)%nat with (S (x0 + h))%nat by lia.
      rewrite XG.
      replace  (X (x0 + h)%nat x w) with (Rvector_scale 0 (X (x0 + h)%nat x w)).
      * rewrite <- XGB.
        rewrite Rvector_scale0.
        symmetry.
        now apply Rvector_max_abs_zero.
      * symmetry in IHh.
        apply Rvector_max_abs_zero in IHh.
        now rewrite Rvector_scale0.
  - apply is_lim_seq_const.
 Qed.

Lemma lemma2_0_w (x : SS) (w : Ts)
      (X : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N )
      (C : posreal)   :
  (forall n,  rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n beta, 
      Rvector_scale beta (G n (X n x w) (Y n w) x) = 
        (G n (Rvector_scale beta (X n x w)) (Y n w) x)) ->
  (exists n, X n x w = Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs (X n x w)) 0.
 Proof.
  intros XG XGB H.
  destruct H.
  apply is_lim_seq_ext_loc with (u := fun n => 0).
  - exists x0.
    intros.
    pose (h := (n - x0)%nat).
    replace n with (x0 + h)%nat by lia.
    induction h.
    + replace (x0 + 0)%nat with (x0) by lia.
      rewrite H.
      symmetry.
      now rewrite Rvector_max_abs_zero.
    + replace (x0 + S h)%nat with (S (x0 + h))%nat by lia.
      rewrite XG.
      replace  (X (x0 + h)%nat x w) with (Rvector_scale 0 (X (x0 + h)%nat x w)).
      * rewrite <- XGB.
        rewrite Rvector_scale0.
        symmetry.
        now apply Rvector_max_abs_zero.
      * symmetry in IHh.
        apply Rvector_max_abs_zero in IHh.
        now rewrite Rvector_scale0.
  - apply is_lim_seq_const.
 Qed.

 Definition vecrvclip {Ts:Type} (f : Ts -> vector R N) 
            (c : nonnegreal) : Ts -> vector R N
   := fun x => if Rgt_dec (Rvector_max_abs (f x)) c then 
                 Rvector_scale (c/Rvector_max_abs (f x)) (f x) else
                 (f x).

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

Lemma lemma2_n00 {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (X n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (XX n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (XX n x w)) (Y n w) x))) ->
  (forall n, X n x w <> Rvector_zero) ->
  forall n,
  exists (CC : R),
    CC <> 0 /\
    Rvector_scale CC (X n x w) = XX n x w.
  Proof.
  intros XG XXG XX0 XGB XXGB Xn0.
  induction n.
  - exists ((Rvector_max_abs (XX 0%nat x w))/(Rvector_max_abs (X 0%nat x w))).
    assert (XX 0%nat x w <> Rvector_zero).
    { 
      rewrite XX0.
      now apply vecrvclip_not_0.
    }
    split.
    + apply Rdiv_not_0.
      split; now apply Rvector_max_abs_nzero.
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
      * replace (Rvector_max_abs (X 0%nat x w) / Rvector_max_abs (X 0%nat x w)) with 1.
        -- now rewrite Rvector_scale1.
        -- field.
           now apply Rvector_max_abs_nzero.           
  - destruct IHn as [? [? ?]].
    assert (XX (S n) x w <> Rvector_zero).
    {
      rewrite XXG.
      apply vecrvclip_not_0.
      rewrite <- H0.
      rewrite <- XGB.
      rewrite <- XG.
      apply Rvector_scale_not_0.
      split; trivial.
    }
    destruct (Rgt_dec (Rvector_max_abs (G n (XX n x w) (Y n w) x)) C).
    + exists (x0 * (C / Rvector_max_abs (G n (XX n x w) (Y n w) x))).
      split.
      * apply Rmult_not_0; split; trivial.
        apply Rdiv_not_0;split.
        -- apply Rgt_not_eq.
           apply cond_pos.
        -- apply Rgt_not_eq.
           eapply Rgt_trans.
           apply r.
           apply cond_pos.
      * rewrite XXG.
        unfold vecrvclip; simpl.
        match_destr; try lra.
        rewrite XG.
        rewrite <- H0.
        rewrite <- XGB.
        rewrite Rvector_scale_scale.
        f_equal.
        field.
        rewrite Rvector_max_abs_scale.
        apply Rmult_not_0; split.
        -- now apply Rgt_not_eq, Rabs_pos_lt.
        -- rewrite <- XG.
           now apply Rvector_max_abs_nzero.
    + exists x0.
      split; trivial.
      rewrite XXG.
      unfold vecrvclip.
      simpl.
      match_destr; try lra.
      rewrite XG.
      rewrite <- H0.
      now rewrite <- XGB.
  Qed.

Lemma lemma2_n00_w {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      Rvector_scale beta (G n (X n x w) (Y n w) x) = 
        (G n (Rvector_scale beta (X n x w)) (Y n w) x)) ->
  (forall n beta, 
      Rvector_scale beta (G n (XX n x w) (Y n w) x) = 
        (G n (Rvector_scale beta (XX n x w)) (Y n w) x)) ->  
  (forall n, X n x w <> Rvector_zero) ->
  forall n,
  exists (CC : R),
    CC <> 0 /\
    Rvector_scale CC (X n x w) = XX n x w.
  Proof.
  intros XG XXG XX0 XGB XXGB Xn0.
  induction n.
  - exists ((Rvector_max_abs (XX 0%nat x w))/(Rvector_max_abs (X 0%nat x w))).
    assert (XX 0%nat x w <> Rvector_zero).
    { 
      rewrite XX0.
      now apply vecrvclip_not_0.
    }
    split.
    + apply Rdiv_not_0.
      split; now apply Rvector_max_abs_nzero.
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
      * replace (Rvector_max_abs (X 0%nat x w) / Rvector_max_abs (X 0%nat x w)) with 1.
        -- now rewrite Rvector_scale1.
        -- field.
           now apply Rvector_max_abs_nzero.           
  - destruct IHn as [? [? ?]].
    assert (XX (S n) x w <> Rvector_zero).
    {
      rewrite XXG.
      apply vecrvclip_not_0.
      rewrite <- H0.
      rewrite <- XGB.
      rewrite <- XG.
      apply Rvector_scale_not_0.
      split; trivial.
    }
    destruct (Rgt_dec (Rvector_max_abs (G n (XX n x w) (Y n w) x)) C).
    + exists (x0 * (C / Rvector_max_abs (G n (XX n x w) (Y n w) x))).
      split.
      * apply Rmult_not_0; split; trivial.
        apply Rdiv_not_0;split.
        -- apply Rgt_not_eq.
           apply cond_pos.
        -- apply Rgt_not_eq.
           eapply Rgt_trans.
           apply r.
           apply cond_pos.
      * rewrite XXG.
        unfold vecrvclip; simpl.
        match_destr; try lra.
        rewrite XG.
        rewrite <- H0.
        rewrite <- XGB.
        rewrite Rvector_scale_scale.
        f_equal.
        field.
        rewrite Rvector_max_abs_scale.
        apply Rmult_not_0; split.
        -- now apply Rgt_not_eq, Rabs_pos_lt.
        -- rewrite <- XG.
           now apply Rvector_max_abs_nzero.
    + exists x0.
      split; trivial.
      rewrite XXG.
      unfold vecrvclip.
      simpl.
      match_destr; try lra.
      rewrite XG.
      rewrite <- H0.
      now rewrite <- XGB.
  Qed.

  Lemma lemma2_n000 {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N  -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                           (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (X n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (XX n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (XX n x w)) (Y n w) x))) ->
  (forall n, X n x w <> Rvector_zero) ->
  forall n, XX n x w <> Rvector_zero.
 Proof.
   intros XG XXG XX0 XGB XXGB Xn0.
   generalize (lemma2_n00 x w X XX Y G C); intros.
   cut_to H; trivial.
   destruct (H n) as [? [? ?]].
   rewrite <- H1.
   apply Rvector_scale_not_0.
   split; trivial.
 Qed.

  Lemma lemma2_n000_w {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N  -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                           (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      Rvector_scale beta (G n (X n x w) (Y n w) x) = 
        (G n (Rvector_scale beta (X n x w)) (Y n w) x)) ->
  (forall n beta, 
      Rvector_scale beta (G n (XX n x w) (Y n w) x) = 
        (G n (Rvector_scale beta (XX n x w)) (Y n w) x)) ->  
  (forall n, X n x w <> Rvector_zero) ->
  forall n, XX n x w <> Rvector_zero.
 Proof.
   intros XG XXG XX0 XGB XXGB Xn0.
   generalize (lemma2_n00_w x w X XX Y G C); intros.
   cut_to H; trivial.
   destruct (H n) as [? [? ?]].
   rewrite <- H1.
   apply Rvector_scale_not_0.
   split; trivial.
 Qed.

Lemma lemma2_n0 {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (X n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (XX n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (XX n x w)) (Y n w) x))) ->
  (forall n, X n x w <> Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs(XX n x w)) 0 ->
  is_lim_seq (fun n => Rvector_max_abs(X n x w)) 0.
Proof.
  intros XG XXG XX0 XGB XXGB Xn0 H.
  assert (XXn0: forall n, XX n x w <> Rvector_zero).
  {
   generalize (lemma2_n000 x w X XX Y G C); intros.
   cut_to H0; trivial.
  }
  generalize H; intros HH.
  apply is_lim_seq_spec in H.
  unfold is_lim_seq' in H.
  intros.
  assert (exists (nn:nat) (CC:R), 
             forall n, (nn <= n)%nat ->
                       (X n x w) = Rvector_scale CC (XX n x w)).
  {
    destruct (H C) as [n0 ?].
    exists n0.
    assert (forall n, (n0 <= n)%nat ->
                      (XX (S n) x w = G n (XX n x w) (Y n w) x)).
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
               rewrite H0 in r.
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
    generalize (lemma2_n00 x w X XX Y G C); intros.
    cut_to H2; trivial.
    destruct (H2 n0) as [? [? ?]].
    exists (/ x0).
    intros.
    pose (h := (n - n0)%nat).
    replace n with (n0 + h)%nat by lia.
    induction h.
    - replace (n0 + 0)%nat with n0 by lia.
      rewrite <- H4.
      rewrite Rvector_scale_scale.
      rewrite <- Rinv_l_sym; trivial.
      now rewrite Rvector_scale1.
    - replace (n0 + S h)%nat with (S (n0 + h))%nat by lia.
      rewrite XG.
      rewrite H1; try lia.
      rewrite XXGB.
      now f_equal.
  }
  destruct H0 as [nn [CC ?]].
  apply is_lim_seq_ext_loc with (u := fun n => Rabs(CC) * Rvector_max_abs (XX n x w)).
  - exists nn; intros.
    rewrite H0; trivial.
    now rewrite Rvector_max_abs_scale.
  - replace (Finite 0) with (Rbar_mult (Rabs CC) 0).
    + now apply is_lim_seq_scal_l.
    + apply Rbar_mult_0_r.
  Qed.

Lemma lemma2_n0_w {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->

 (forall n beta, 
      Rvector_scale beta (G n (X n x w) (Y n w) x) = 
        (G n (Rvector_scale beta (X n x w)) (Y n w) x)) ->
  (forall n beta, 
      Rvector_scale beta (G n (XX n x w) (Y n w) x) = 
        (G n (Rvector_scale beta (XX n x w)) (Y n w) x)) ->  
  (forall n, X n x w <> Rvector_zero) ->
  is_lim_seq (fun n => Rvector_max_abs(XX n x w)) 0 ->
  is_lim_seq (fun n => Rvector_max_abs(X n x w)) 0.
Proof.
  intros XG XXG XX0 XGB XXGB Xn0 H.
  assert (XXn0: forall n, XX n x w <> Rvector_zero).
  {
   generalize (lemma2_n000_w x w X XX Y G C); intros.
   cut_to H0; trivial.
  }
  generalize H; intros HH.
  apply is_lim_seq_spec in H.
  unfold is_lim_seq' in H.
  intros.
  assert (exists (nn:nat) (CC:R), 
             forall n, (nn <= n)%nat ->
                       (X n x w) = Rvector_scale CC (XX n x w)).
  {
    destruct (H C) as [n0 ?].
    exists n0.
    assert (forall n, (n0 <= n)%nat ->
                      (XX (S n) x w = G n (XX n x w) (Y n w) x)).
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
               rewrite H0 in r.
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
    generalize (lemma2_n00_w x w X XX Y G C); intros.
    cut_to H2; trivial.
    destruct (H2 n0) as [? [? ?]].
    exists (/ x0).
    intros.
    pose (h := (n - n0)%nat).
    replace n with (n0 + h)%nat by lia.
    induction h.
    - replace (n0 + 0)%nat with n0 by lia.
      rewrite <- H4.
      rewrite Rvector_scale_scale.
      rewrite <- Rinv_l_sym; trivial.
      now rewrite Rvector_scale1.
    - replace (n0 + S h)%nat with (S (n0 + h))%nat by lia.
      rewrite XG.
      rewrite H1; try lia.
      rewrite XXGB.
      now f_equal.
  }
  destruct H0 as [nn [CC ?]].
  apply is_lim_seq_ext_loc with (u := fun n => Rabs(CC) * Rvector_max_abs (XX n x w)).
  - exists nn; intros.
    rewrite H0; trivial.
    now rewrite Rvector_max_abs_scale.
  - replace (Finite 0) with (Rbar_mult (Rabs CC) 0).
    + now apply is_lim_seq_scal_l.
    + apply Rbar_mult_0_r.
  Qed.

Lemma lemma2 (x:SS)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (X n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => Rvector_scale beta (G n (XX n x w) (Y n w) x))
            (fun w => (G n (Rvector_scale beta (XX n x w)) (Y n w) x))) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (XX n x w)) 0) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (X n x w)) 0).
Proof.
  intros XG XXG XX0 XGB XXGB.
  apply almost_impl, all_almost; intros w H.
  destruct (classic (exists n, X n x w = Rvector_zero)).
  - now apply (lemma2_0 x w X Y G C).
  - generalize (not_ex_all_not nat _ H0); intros HH.
    now apply (lemma2_n0 x w X XX Y G C).
Qed.
        
Lemma lemma2_almostG (x:SS)
      (X XX : nat -> SS -> Ts -> vector R N)
      (Y : nat -> Ts -> vector R N)
      (G : nat -> vector R N -> vector R N -> SS -> vector R N)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (vecrvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (vecrvclip (X 0%nat x) (pos_to_nneg C)) ->
  almost prts (fun w =>
                 forall n beta, 
                   Rvector_scale beta (G n (X n x w) (Y n w) x) = 
                     G n (Rvector_scale beta (X n x w)) (Y n w) x) ->
  almost prts (fun w =>
                 forall n beta, 
                   Rvector_scale beta (G n (XX n x w) (Y n w) x) = 
                     G n (Rvector_scale beta (XX n x w)) (Y n w) x) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (XX n x w)) 0) ->
  almost prts (fun w => is_lim_seq (fun n => Rvector_max_abs (X n x w)) 0).
Proof.
  intros XG XXG XX0 XGB XXGB.
  apply almost_impl.
  revert XGB; apply almost_impl.
  revert XXGB; apply almost_impl.
  apply all_almost.
  intros w ???.
  destruct (classic (exists n, X n x w = Rvector_zero)).
  - now apply (lemma2_0_w x w X Y G C).
  - generalize (not_ex_all_not nat _ H2); intros HH.
    now apply (lemma2_n0_w x w X XX Y G C).
Qed.
  
Lemma gamma_C :
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

Lemma delta_eps_bound (eps : posreal) (C : posreal) {N} (delta : vector R (S N)) :
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

Lemma gamma_eps_le (gamma : posreal) :
  gamma < 1 ->
  exists (eps : posreal), gamma <=  / (1 + eps).
Proof.
  intros.
  assert (0 < (1 - gamma) / (2 * gamma)).
  {
    assert (0 < gamma).
    {
      apply cond_pos.
    }
    apply RIneq.Rdiv_lt_0_compat; lra.
  }
  exists (mkposreal _ H0).
  simpl.
  apply Rmult_le_reg_r with (r :=  (1 + ((1 - gamma) / (2 * gamma)))).
  - eapply Rlt_trans.
    apply H0; lra.
    lra.
  - unfold Rdiv.
    rewrite Rinv_l; try lra.
    rewrite Rmult_plus_distr_l, Rmult_1_r.
    rewrite <- Rmult_assoc, Rmult_comm, <- Rmult_assoc.
    replace (/ (2 * gamma) * gamma) with (/2).
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
  apply H0.
  generalize (cond_pos x); intros.
  generalize (cond_pos eps2); intros.
  apply Rle_Rinv; lra.
Qed.

    Lemma conv_as_prob_1_eps_alt {prts: ProbSpace dom} (f : nat -> Ts -> R) (fstar: R)
      {rv : forall n, RandomVariable dom borel_sa (f n)} :
      almost prts (fun x => is_lim_seq (fun n => f n x) fstar) ->
      forall (eps1 eps2:posreal),
        eventually (fun n => ps_P (event_lt dom (rvabs (rvminus (f n) (const fstar))) eps1) >= 1 - eps2).
    Proof.
      intros.
      apply conv_as_prob_1_eps.
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

    Lemma lemma3_helper {prts: ProbSpace dom} (f : nat -> Ts -> R) (fstar: R) (C gamma : posreal)
      {rv : forall n, RandomVariable dom borel_sa (f n)} :
      almost prts (fun x => is_lim_seq (fun n => f n x) fstar) ->
      Rabs fstar <= gamma * C ->
      gamma < 1 ->
      exists (Eps1 : posreal),
        forall (eps1 eps2:posreal),
          eps1 <= Eps1 ->
          eventually (fun n => ps_P (event_lt dom (rvabs (f n)) (C / (1 + eps1))) >= 1 - eps2).
    Proof.
      intros H H0 gamma_1.
      destruct (lemma3_gamma_eps gamma gamma_1).
      exists x.
      intros.
      assert (0 < ((1 - gamma)/2) * C).
      {
        apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; lra.
        - apply cond_pos.
      }
      destruct (conv_as_prob_1_eps_alt f fstar H (mkposreal _ H3) eps2).
      exists x0.
      intros.
      eapply Rge_trans; cycle 1.
      apply (H4 _ H5).
      apply Rle_ge.
      apply ps_sub.
      unfold event_sub, pre_event_sub, rvabs; simpl; intros.
      unfold rvabs, rvminus, rvplus, rvopp, rvscale, const in H6.
      generalize (Rabs_triang_inv (f n x1) fstar); intros.
      replace  (f n x1 + -1 * fstar) with  (f n x1 - fstar) in H6 by lra.
      assert (Rabs(f n x1) < (1 - gamma) * C / 2 + gamma * C) by lra.
      specialize (H1 eps1 H2).
      eapply Rlt_le_trans.
      apply H8.
      generalize (cond_pos C); intros.
      apply Rmult_le_compat_l with (r := C) in H1; lra.
    Qed.

    Lemma lemma3_helper_le {prts: ProbSpace dom} (f g : nat -> Ts -> R) (fstar: R) (C gamma : posreal)
      {rvf : forall n, RandomVariable dom borel_sa (f n)} 
      {rvg : forall n, RandomVariable dom borel_sa (g n)} :       
      almost prts (fun x => is_lim_seq (fun n => f n x) fstar) ->
      (forall n x, rvabs (g n) x <= rvabs (f n) x) ->
      Rabs fstar <= gamma * C ->
      gamma < 1 ->
      exists (Eps1 : posreal),
        forall (eps1 eps2:posreal),
          eps1 <= Eps1 ->
          eventually (fun n => ps_P (event_lt dom (rvabs (g n)) (C / (1 + eps1))) >= 1 - eps2).
    Proof.
      intros H H0 H1 gamma_1.
      destruct (lemma3_helper f fstar C gamma H H1 gamma_1).
      exists x.
      intros.
      specialize (H2 eps1 eps2 H3).
      destruct H2.
      exists x0.
      intros.
      specialize (H2 n H4).
      eapply Rge_trans; cycle 1.
      apply H2.
      apply Rle_ge.
      apply ps_sub.
      unfold event_sub, pre_event_sub.
      simpl; intros.
      eapply Rle_lt_trans.
      apply H0.
      apply H5.
    Qed.
      

    Lemma lemma3_helper_almost_le {prts: ProbSpace dom} (f g : nat -> Ts -> R) (fstar: R) (C gamma : posreal)
      {rvf : forall n, RandomVariable dom borel_sa (f n)} 
      {rvg : forall n, RandomVariable dom borel_sa (g n)} :       
      almost prts (fun x => is_lim_seq (fun n => f n x) fstar) ->
      (forall (n : nat), almostR2 prts Rle (rvabs (g n)) (rvabs (f n))) ->
      Rabs fstar <= gamma * C ->
      gamma < 1 ->
      exists (Eps1 : posreal),
        forall (eps1 eps2:posreal),
          eps1 <= Eps1 ->
          eventually (fun n => ps_P (event_lt dom (rvabs (g n)) (C / (1 + eps1))) >= 1 - eps2).
   Proof.
      intros H H0 H1 gamma_1.
      destruct (lemma3_helper f fstar C gamma H H1 gamma_1).
      exists x.
      intros.
      specialize (H2 eps1 eps2 H3).
      destruct H2.
      exists x0.
      intros.
      specialize (H2 n H4).
      eapply Rge_trans; cycle 1.
      apply H2.
      specialize (H0 n).
      clear H H1 gamma_1.
      apply Rle_ge.
      apply ps_almostR2_sub.
      revert H0.
      apply almost_impl.
      apply all_almost.
      intros ??.
      unfold event_sub, pre_event_sub.
      simpl; intros ?.
      eapply Rle_lt_trans.
      apply H.
      apply H0.
  Qed.     

   Lemma lemma3_helper_iter_nneg  (f α β : nat -> Ts -> R) (C C0 : nonnegreal) :
      (forall n x, 0 <= α n x <= 1) ->
      (forall n x, 0 <= β n x <= 1) ->     
      (forall x, f 0%nat x = C0) ->
      (forall n x, f (S n) x = (1 - α n x) * f n x + (β n x) * C) ->
      forall n x, 0 <= f n x.
   Proof.
     intros.
     induction n.
     - rewrite H1.
       apply cond_nonneg.
     - rewrite H2.
       apply Rplus_le_le_0_compat.
       + apply Rmult_le_pos; trivial.
         specialize (H n x).
         lra.
       + apply Rmult_le_pos.
         * specialize (H0 n x).
           lra.
         * apply cond_nonneg.
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


   Lemma lemma3_helper_iter_almost_le {prts: ProbSpace dom} (f g α β : nat -> Ts -> R) (C C0 : nonnegreal)
      {rvα : forall n, RandomVariable dom borel_sa (α n)} 
      {rvβ : forall n, RandomVariable dom borel_sa (β n)} 
      {rvf : forall n, RandomVariable dom borel_sa (f n)} 
      {rvg : forall n, RandomVariable dom borel_sa (g n)} :       
      (forall n x, 0 <= α n x <= 1) ->
      (forall n x, 0 <= β n x <= 1) ->     
      (forall n, almostR2  prts Rle (β n) (α n)) ->
      (forall x, f 0%nat x = C0) ->
      (forall x, g 0%nat x = C0) ->
      (forall n x, f (S n) x = (1 - α n x) * f n x + (α n x) * C) ->
      (forall n x, g (S n) x = (1 - α n x) * g n x + (β n x) * C) ->      
      forall n, almostR2 prts Rle (g n) (f n).
    Proof.
      intros.
      induction n.
      - apply all_almost.
        intros.
        rewrite H2.
        now right.
      - specialize (H1 n).
        revert H1.
        apply almost_impl.
        revert IHn.
        apply almost_impl.
        apply all_almost.
        intros ???.
        rewrite H4, H5.
        apply Rplus_le_compat.
        + apply Rmult_le_compat_l; trivial.
          specialize (H n x).
          lra.
        + apply Rmult_le_compat_r; trivial.
          apply cond_nonneg.
    Qed.

   Lemma lemma3_helper_iter_almost_le_abs {prts: ProbSpace dom} (f g α β : nat -> Ts -> R) (C C0 : nonnegreal)
      {rvα : forall n, RandomVariable dom borel_sa (α n)} 
      {rvβ : forall n, RandomVariable dom borel_sa (β n)} 
      {rvf : forall n, RandomVariable dom borel_sa (f n)} 
      {rvg : forall n, RandomVariable dom borel_sa (g n)} :       
      (forall n x, 0 <= α n x <= 1) ->
      (forall n x, 0 <= β n x <= 1) ->     
      (forall n, almostR2  prts Rle (β n) (α n)) ->
      (forall x, f 0%nat x = C0) ->
      (forall x, g 0%nat x = C0) ->
      (forall n x, f (S n) x = (1 - α n x) * f n x + (α n x) * C) ->
      (forall n x, g (S n) x = (1 - α n x) * g n x + (β n x) * C) ->      
      forall n, almostR2 prts Rle (rvabs (g n)) (rvabs (f n)).
    Proof.
      intros.
      induction n.
      - apply all_almost.
        intros.
        unfold rvabs.
        rewrite H2, H3.
        now right.
      - specialize (H1 n).
        revert H1.
        apply almost_impl.
        revert IHn.
        apply almost_impl.
        apply all_almost.
        intros ???.
        assert (forall n x, rvabs (f n) x = f n x).
        {
          intros.
          unfold rvabs.
          rewrite Rabs_right; trivial.
          apply Rle_ge.
          apply (lemma3_helper_iter_nneg f α α C C0); trivial.
        }
        assert (forall n x, rvabs (g n) x = g n x).
        {
          intros.
          unfold rvabs.
          rewrite Rabs_right; trivial.
          apply Rle_ge.
          apply (lemma3_helper_iter_nneg g α β C C0); trivial.
        }
        rewrite H7, H8.
        rewrite H7, H8 in H1.
        rewrite H4, H5.
        apply Rplus_le_compat.
        + apply Rmult_le_compat_l; trivial.
          specialize (H n x).
          lra.
        + apply Rmult_le_compat_r; trivial.
          apply cond_nonneg.
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

       Lemma lemma3_base (α X f : nat -> Ts -> R) (C γ : posreal)
         (rvX : forall n, RandomVariable dom borel_sa (X n))
         (rvf : forall n, RandomVariable dom borel_sa (f n)) :          
         (forall t ω, 0 <= α t ω <= 1) ->
         (forall ω, l1_divergent (fun n : nat => α n ω)) ->
         γ < 1 ->
         (rv_eq (f 0%nat) (const C)) ->
         (forall n, rv_eq (f (S n))
                      (rvplus 
                         (rvmult (rvminus (const 1) (α n)) 
                            (f n))
                         (rvscale (γ * C) (α n)))) ->
         (forall n, rv_le (rvabs (X n)) (f n)) ->
         exists (Eps1 : posreal),
         forall (eps1 eps2:posreal),
           eps1 <= Eps1 ->

           eventually (fun n => ps_P (@event_lt Ts dom (rvabs (X n)) (rvabs_rv _ (X n)) (C / (1 + eps1))) >= 1 - eps2).
       Proof.
         intros.
         assert (0 <= γ * C).
         {
           apply Rmult_le_pos; left; apply cond_pos.
         }         
         apply lemma3_helper_le with (f := f) (fstar := γ * C) (gamma := γ); trivial.
         - apply all_almost.
           intros.
           apply lemma3_helper_iter_conv2 with (α := fun n => α n x); trivial.
           intros.
           rewrite H3.
           rv_unfold.
           lra.
         - assert (forall n x, 0 <= f n x).
           {
             induction n.
             - intros.
               rewrite H2.
               unfold const; simpl.
               left.
               apply cond_pos.
             - intros.
               rewrite H3.
               rv_unfold.
               specialize (H n x).
               apply Rplus_le_le_0_compat.
               + apply Rmult_le_pos; try lra.
                 apply IHn.
               + apply Rmult_le_pos; lra.
           }
          intros.
          eapply Rle_trans.
          apply H4.
          unfold rvabs.
          rewrite Rabs_right; try lra.
          apply Rle_ge.
          apply H6.
         - rewrite Rabs_right; try lra.
       Qed.

       Lemma lemma3_base_alt (α β X Y f : nat -> Ts -> R) (C γ : posreal)
         (rvX : forall n, RandomVariable dom borel_sa (X n))
         (rvf : forall n, RandomVariable dom borel_sa (f n)) :          
         (forall t ω, 0 <= α t ω <= 1) ->
         (forall t ω, 0 <= β t ω <= 1) ->
         (forall t ω, β t ω <= α t ω) ->                  
         (forall ω, l1_divergent (fun n : nat => α n ω)) ->
         γ < 1 ->
         (rv_eq (f 0%nat) (const C)) ->
         (forall n, rv_eq (f (S n))
                      (rvplus 
                         (rvmult (rvminus (const 1) (α n)) 
                            (f n))
                         (rvscale (γ * C) (α n)))) ->
         rv_le (rvabs (X 0%nat)) (const C) ->
         (forall n, rv_eq (X (S n))
                      (rvplus 
                         (rvmult (rvminus (const 1) (α n)) 
                            (X n))
                         (rvmult (rvscale γ (β n))
                            (rvabs (Y n))))) ->
         (forall n, rv_le (rvabs (Y n)) (const C)) ->
         exists (Eps1 : posreal),
         forall (eps1 eps2:posreal),
           eps1 <= Eps1 ->
           eventually (fun n => ps_P (@event_lt Ts dom (rvabs (X n)) (rvabs_rv _ (X n)) (C / (1 + eps1))) >= 1 - eps2).
       Proof.
         intros.
         apply lemma3_base with (α := α) (f := f) (γ := γ); trivial.
         intros.
         induction n.
         - rewrite H4.
           apply H6.
         - rewrite H7, H5.
           rv_unfold.
           intros ?.
           unfold rv_le, rvabs, const.
           eapply Rle_trans.
           + apply Rabs_triang.
           + apply Rplus_le_compat.
             * replace (Rabs ((1 + -1 * α n a) * X n a)) with
                 ((1 + -1 * α n a) * Rabs (X n a)).
               -- apply Rmult_le_compat_l.
                  ++ specialize (H n a); lra.
                  ++ apply IHn.
               -- rewrite Rabs_mult.
                  f_equal.
                  rewrite Rabs_right; trivial.
                  specialize (H n a); lra.
             * rewrite Rabs_right.
               -- rewrite Rmult_assoc, Rmult_assoc.
                  apply Rmult_le_compat_l.
                  ++ left; apply cond_pos.
                  ++ rewrite Rmult_comm.
                     apply Rmult_le_compat; trivial.
                     ** apply Rabs_pos.
                     ** specialize (H0 n a); lra.
                     ** apply H8.
               -- apply Rle_ge.
                  apply Rmult_le_pos.
                  ++ apply Rmult_le_pos.
                     ** left; apply cond_pos.
                     ** specialize (H0 n a); lra.
                  ++ apply Rabs_pos.
       Qed.
           
