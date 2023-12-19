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
Require Import vecslln.
Require Import ConditionalExpectation VectorConditionalExpectation.
Require Import IndefiniteDescription ClassicalDescription.
Require slln.
Require Import RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Context (gamma : R) (α : nat -> R) {Ts : Type}
        {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

Program Definition pos_to_nneg (c : posreal) : nonnegreal :=
  mknonnegreal c _.
Next Obligation.
  left; apply cond_pos.
Qed.

Lemma lemma2_0 {SS:Type} (x : SS) (w : Ts)
      (X : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n,  rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (X n x w) (Y n w) x))
            (fun w => (G n (beta * (X n x w)) (Y n w) x))) ->
  (exists n, X n x w = 0) ->
  is_lim_seq (fun n => X n x w) 0.
 Proof.
  intros XG XGB H.
  destruct H.
  apply is_lim_seq_ext_loc with (u := fun n => 0).
  - exists x0.
    intros.
    pose (h := (n - x0)%nat).
    replace n with (x0 + h)%nat by lia.
    induction h.
    + now replace (x0 + 0)%nat with (x0) by lia.
    + replace (x0 + S h)%nat with (S (x0 + h))%nat by lia.
      rewrite XG.
      replace  (X (x0 + h)%nat x w) with (0 *  (X (x0 + h)%nat x w)); try lra.
      rewrite <- XGB; lra.
  - apply is_lim_seq_const.
 Qed.

 Lemma lemma2_0_w {SS:Type} (x : SS) (w : Ts)
      (X : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n,  rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n beta,
     beta * (G n (X n x w) (Y n w) x) = 
       (G n (beta * (X n x w)) (Y n w) x)) ->
  (exists n, X n x w = 0) ->
  is_lim_seq (fun n => X n x w) 0.
 Proof.
   intros XG XGB H.
   destruct H.
   apply is_lim_seq_ext_loc with (u := fun n => 0).
   - exists x0.
    intros.
    pose (h := (n - x0)%nat).
    replace n with (x0 + h)%nat by lia.
    induction h.
    + now replace (x0 + 0)%nat with (x0) by lia.
    + replace (x0 + S h)%nat with (S (x0 + h))%nat by lia.
      rewrite XG.
      replace  (X (x0 + h)%nat x w) with (0 *  (X (x0 + h)%nat x w)); try lra.
      rewrite <- XGB; lra.
  - apply is_lim_seq_const.
 Qed.

 Lemma rvclip_not_0 (x : Ts -> R) (C : posreal) (w : Ts) :
   x w <> 0 ->
   rvclip x (pos_to_nneg C) w <> 0.
 Proof.
   intros.
   unfold rvclip.
   destruct C as [? ?].
   match_destr.
   - apply Rgt_not_eq.
     simpl; lra.
   - match_destr.
     simpl; lra.
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

Lemma lemma2_n00 {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (X n x w) (Y n w) x))
            (fun w => (G n (beta * (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (XX n x w) (Y n w) x))
            (fun w => (G n (beta * (XX n x w)) (Y n w) x))) ->
  (forall n, X n x w <> 0) ->
  forall n,
  exists (CC : R),
    CC <> 0 /\
    CC * (X n x w) = XX n x w.
  Proof.
  intros XG XXG XX0 XGB XXGB Xn0.
  induction n.
  - exists ((XX 0%nat x w)/(X 0%nat x w)).
    assert (XX 0%nat x w <> 0).
    { 
      rewrite XX0.
      now apply rvclip_not_0.
    }
    split.
    + apply Rdiv_not_0.
      now split.
    + now field.
  - destruct IHn as [? [? ?]].
    exists ((XX (S n) x w)/(X (S n) x w)).
    assert (XX (S n) x w <> 0).
    {
      rewrite XXG.
      apply rvclip_not_0.
      rewrite <- H0.
      rewrite <- XGB.
      rewrite <- XG.
      apply Rmult_not_0.
      split; trivial.
    }
    split.
    + apply Rdiv_not_0.
      now split.
    + now field.
  Qed.

Lemma lemma2_n00_w {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      beta * (G n (X n x w) (Y n w) x) = 
        (G n (beta * (X n x w)) (Y n w) x)) ->
  (forall n beta, 
      beta * (G n (XX n x w) (Y n w) x) = 
        (G n (beta * (XX n x w)) (Y n w) x)) ->
  (forall n, X n x w <> 0) ->
  forall n,
  exists (CC : R),
    CC <> 0 /\
    CC * (X n x w) = XX n x w.
  Proof.
  intros XG XXG XX0 XGB XXGB Xn0.
  induction n.
  - exists ((XX 0%nat x w)/(X 0%nat x w)).
    assert (XX 0%nat x w <> 0).
    { 
      rewrite XX0.
      now apply rvclip_not_0.
    }
    split.
    + apply Rdiv_not_0.
      now split.
    + now field.
  - destruct IHn as [? [? ?]].
    exists ((XX (S n) x w)/(X (S n) x w)).
    assert (XX (S n) x w <> 0).
    {
      rewrite XXG.
      apply rvclip_not_0.
      rewrite <- H0.
      rewrite <- XGB.
      rewrite <- XG.
      apply Rmult_not_0.
      split; trivial.
    }
    split.
    + apply Rdiv_not_0.
      now split.
    + now field.
  Qed.

  Lemma lemma2_n000 {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (X n x w) (Y n w) x))
            (fun w => (G n (beta * (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (XX n x w) (Y n w) x))
            (fun w => (G n (beta * (XX n x w)) (Y n w) x))) ->
  (forall n, X n x w <> 0) ->
  forall n, XX n x w <> 0.
 Proof.
   intros XG XXG XX0 XGB XXGB Xn0.
   generalize (lemma2_n00 x w X XX Y G C); intros.
   cut_to H; trivial.
   destruct (H n) as [? [? ?]].
   rewrite <- H1.
   apply Rmult_not_0.
   split; trivial.
 Qed.

  Lemma lemma2_n000_w {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      beta * (G n (X n x w) (Y n w) x) = 
        (G n (beta * (X n x w)) (Y n w) x)) ->
  (forall n beta, 
      beta * (G n (XX n x w) (Y n w) x) = 
        (G n (beta * (XX n x w)) (Y n w) x)) ->
  (forall n, X n x w <> 0) ->
  forall n, XX n x w <> 0.
 Proof.
   intros XG XXG XX0 XGB XXGB Xn0.
   generalize (lemma2_n00_w x w X XX Y G C); intros.
   cut_to H; trivial.
   destruct (H n) as [? [? ?]].
   rewrite <- H1.
   apply Rmult_not_0.
   split; trivial.
 Qed.

Lemma lemma2_n0 {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (X n x w) (Y n w) x))
            (fun w => (G n (beta * (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (XX n x w) (Y n w) x))
            (fun w => (G n (beta * (XX n x w)) (Y n w) x))) ->
  (forall n, X n x w <> 0) ->
  is_lim_seq (fun n => XX n x w) 0 ->
  is_lim_seq (fun n => X n x w) 0.
Proof.
  intros XG XXG XX0 XGB XXGB Xn0 H.
  assert (XXn0: forall n, XX n x w <> 0).
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
                       (X n x w) = CC * (XX n x w)).
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
      rewrite XXG in H0.
      apply Rabs_lt_between in H0.
      unfold rvclip.
      unfold rvclip in H0.
      match_destr.
      - simpl in H0; lra.
      - match_destr.
        simpl in H0; lra.
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
      field_simplify; trivial.
    - replace (n0 + S h)%nat with (S (n0 + h))%nat by lia.
      rewrite XG.
      rewrite H1; try lia.
      rewrite XXGB.
      now f_equal.
    }
  destruct H0 as [nn [CC ?]].
  apply is_lim_seq_ext_loc with (u := fun n => CC * (XX n x w)).
  - exists nn; intros.
    now rewrite H0.
  - replace (Finite 0) with (Rbar_mult CC 0).
    + now apply is_lim_seq_scal_l.
    + apply Rbar_mult_0_r.
  Qed.

Lemma lemma2_n0_w {SS:Type} (x : SS) (w : Ts)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      beta * (G n (X n x w) (Y n w) x) = 
        (G n (beta * (X n x w)) (Y n w) x)) ->
  (forall n beta, 
      beta * (G n (XX n x w) (Y n w) x) = 
        (G n (beta * (XX n x w)) (Y n w) x)) ->
  (forall n, X n x w <> 0) ->
  is_lim_seq (fun n => XX n x w) 0 ->
  is_lim_seq (fun n => X n x w) 0.
Proof.
  intros XG XXG XX0 XGB XXGB Xn0 H.
  assert (XXn0: forall n, XX n x w <> 0).
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
                       (X n x w) = CC * (XX n x w)).
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
      rewrite XXG in H0.
      apply Rabs_lt_between in H0.
      unfold rvclip.
      unfold rvclip in H0.
      match_destr.
      - simpl in H0; lra.
      - match_destr.
        simpl in H0; lra.
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
      field_simplify; trivial.
    - replace (n0 + S h)%nat with (S (n0 + h))%nat by lia.
      rewrite XG.
      rewrite H1; try lia.
      rewrite XXGB.
      now f_equal.
    }
  destruct H0 as [nn [CC ?]].
  apply is_lim_seq_ext_loc with (u := fun n => CC * (XX n x w)).
  - exists nn; intros.
    now rewrite H0.
  - replace (Finite 0) with (Rbar_mult CC 0).
    + now apply is_lim_seq_scal_l.
    + apply Rbar_mult_0_r.
  Qed.

Lemma lemma2_scalar {SS:Type} (x:SS)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (X n x w) (Y n w) x))
            (fun w => (G n (beta * (X n x w)) (Y n w) x))) ->
  (forall n beta, 
      rv_eq (fun w => beta * (G n (XX n x w) (Y n w) x))
            (fun w => (G n (beta * (XX n x w)) (Y n w) x))) ->
  almost prts (fun w => is_lim_seq (fun n => XX n x w) 0) ->
  almost prts (fun w => is_lim_seq (fun n => X n x w) 0).
Proof.
  intros XG XXG XX0 XGB XXGB.
  apply almost_impl, all_almost; intros w H.
  destruct (classic (exists n, X n x w = 0)).
  - now apply (lemma2_0 x w X Y G C).
  - generalize (not_ex_all_not nat _ H0); intros HH.
    now apply (lemma2_n0 x w X XX Y G C).
Qed.
  
Lemma lemma2_scalar_almostG {SS:Type} (x:SS)
      (X XX : nat -> SS -> Ts -> R)
      (Y : nat -> Ts -> R)
      (G : nat -> R -> R -> SS -> R)
      (C : posreal)   :
  (forall n, rv_eq (X (S n) x) (fun w => G n (X n x w) (Y n w) x)) ->
  (forall n, rv_eq (XX (S n) x) (rvclip (fun w => G n (XX n x w) (Y n w) x) 
                                          (pos_to_nneg C))) ->
  rv_eq (XX 0%nat x) (rvclip (X 0%nat x) (pos_to_nneg C)) ->
  almost prts (fun w =>
                 forall n beta,
                   beta * (G n (X n x w) (Y n w) x) =
                     G n (beta * (X n x w)) (Y n w) x) ->                     
  almost prts (fun w =>
                 forall n beta,
                   beta * (G n (XX n x w) (Y n w) x) =
                     G n (beta * (XX n x w)) (Y n w) x) ->                     
  almost prts (fun w => is_lim_seq (fun n => XX n x w) 0) ->
  almost prts (fun w => is_lim_seq (fun n => X n x w) 0).
Proof.
  intros XG XXG XX0 XGB XXGB limXX.
  revert XXGB.
  apply almost_impl.
  revert XGB.
  apply almost_impl.
  revert limXX.
  apply almost_impl.  
  apply all_almost.
  intros w ???.
  destruct (classic (exists n, X n x w = 0)).
  - now apply (lemma2_0_w x w X Y G C).
  - generalize (not_ex_all_not nat _ H2); intros HH.
    now apply (lemma2_n0_w x w X XX Y G C).
  
  
