Require Import Reals Sums Lra Lia.
Require Import Coquelicot.Coquelicot.
Require Import LibUtils.
Require Import Expectation ConditionalExpectation.
Require Import infprod.
Require Import PushNeg.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.

Require Import Utils.
Import ListNotations.
Require Import Classical.
Require Import slln.

Set Bullet Behavior "Strict Subproofs".

Require Import LM.hilbert Classical IndefiniteDescription.

Section Dvoretzky.
  
 Context 
   {Ts : Type}
   {dom: SigmaAlgebra Ts}
   {prts: ProbSpace dom}.

 (* scalar version of T *)

 Global Instance R_nonempty : NonEmpty R
   := R0.

 Declare Scope rv.

 Infix ".+" := rvplus (left associativity, at level 50) : rv.
 Infix ".-" := rvminus (left associativity, at level 50) : rv.
 Infix ".*" := rvmult (left associativity, at level 40) : rv.
 Infix ".*." := rvscale (no associativity, at level 40) : rv.
 Notation "x .²" := (rvsqr x) (at level 1) : rv.

 Local Open Scope rv.
  
      
 Lemma frf_vals_offset
        (offset: R)
        (vals : list R) :
    map (fun ab : R * R => fst ab + snd ab) (list_prod vals [offset]) =  
    map (fun v => v + offset) vals.
 Proof.
   induction vals; simpl; trivial.
   now f_equal.
 Qed.

Definition ConditionalExpectation_rv (g f : Ts -> R)
           {rvf: RandomVariable dom borel_sa f}
           {rvg: RandomVariable dom borel_sa g}  : Ts -> Rbar :=
  ConditionalExpectation prts (pullback_rv_sub dom borel_sa g rvg) f.

Definition FiniteConditionalExpectation_rv (g f : Ts -> R)
           {rvf: RandomVariable dom borel_sa f}
           {rvg: RandomVariable dom borel_sa g}           
           {isfe : IsFiniteExpectation prts f} : Ts -> R :=
  FiniteConditionalExpectation prts (pullback_rv_sub dom borel_sa g rvg) f.

Lemma Dvoretzky_rel (n:nat) (theta:R) (X Y : nat -> Ts -> R)
      (T : nat -> R -> R)
      (F : nat -> R)
      (rvy : RandomVariable dom borel_sa (Y n)) 
      (svy : FiniteRangeFunction (Y n)) 
      (rvx : RandomVariable dom borel_sa (X n)) 
      (svx: FiniteRangeFunction (X n))
      (rvt : RandomVariable borel_sa borel_sa (fun r:R => T n r))        
      (svt: FiniteRangeFunction (fun r:Ts => T n (X n r))) 
      (rvx2 : RandomVariable dom borel_sa (X (S n)))
      (svx2: FiniteRangeFunction (X (S n))) :
  (forall (n:nat), F n >= 0) ->
  (forall (n:nat) (r:R), Rle (Rabs ((T n r) - theta)) (F n * Rabs (r-theta))) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r => T n (X n r)) (Y n))) ->
  almostR2 prts eq (ConditionalExpectation_rv (X n) (Y n)) (const 0) ->
  Rle (SimpleExpectation (rvsqr (rvminus (X (S n)) (const theta)) ))
      ((Rsqr (F n)) * SimpleExpectation (rvsqr (rvminus (X n) (const (theta))))
       + SimpleExpectation (rvsqr (Y n))).
  Proof.
    intros.
    specialize (H1 n).
    assert (rv_eq (rvminus (X (S n)) (const theta)) 
                  (rvminus (rvplus (fun r => T n (X n r)) (Y n)) (const theta))).
    now rewrite H1.
    rewrite (SimpleExpectation_transport (frfsqr (rvminus (X (S n)) (const theta)))
                                        (rvsqr_proper _ _ H3)).    
   assert (eqq1:rv_eq (rvsqr (rvminus (rvplus (fun r : Ts => T n (X n r)) (Y n)) (const theta))) 
                      (rvplus (rvsqr (rvminus (fun r : Ts => T n (X n r)) (const theta)))
                              (rvplus
                                 (rvscale 2 (rvmult (rvminus (fun r : Ts => T n (X n r)) (const theta))
                                                    (Y n)))
                            (rvsqr (Y n))))).
   { intros r.
     unfold rvsqr, rvplus, rvminus, rvopp, rvscale, Rsqr, rvmult, const.
     unfold rvplus.
     lra.
   }
   rewrite (SimpleExpectation_transport _ eqq1).
   assert (rvtx: RandomVariable dom borel_sa (fun r:Ts => T n (X n r)))
          by now apply (compose_rv (dom2 := borel_sa)).
   rewrite (SimpleExpectation_pf_irrel _ _).
   rewrite <- sumSimpleExpectation; try typeclasses eauto.
   rewrite <- sumSimpleExpectation; try typeclasses eauto.
   rewrite <- scaleSimpleExpectation.
   rewrite <- Rplus_assoc.
   apply Rplus_le_compat_r.
   assert (SimpleExpectation (((fun r : Ts => T n (X n r)) .- const theta) .* Y n) = 0).
   {
     apply SimpleCondexp_factor_out_zero 
       with (sub := (pullback_rv_sub dom borel_sa (X n) rvx)) (rvf := rvy); trivial.
     apply rvminus_rv.
     - apply (compose_rv (dom2 := borel_sa)); trivial.
       apply pullback_rv.
     - typeclasses eauto.
   }
   rewrite H4.
   rewrite Rmult_0_r, Rplus_0_r.
   specialize (H n).
   rewrite (scaleSimpleExpectation (Rsqr (F n))).
   apply SimpleExpectation_le; try typeclasses eauto.
   intros x.
   unfold rvsqr, rvscale.
   specialize (H0 n (X n x)).
   rewrite <- Rabs_right with (r:=F n) in H0; trivial.
   rewrite <- Rabs_mult in H0.
   apply Rsqr_le_abs_1 in H0.
   rewrite Rsqr_mult in H0.
   unfold rvminus, rvopp, rvplus, rvscale, const.
   replace (-1 * theta) with (-theta) by lra.
   apply H0.
  Qed.

  Lemma exp_sum (a : nat -> R) (n : nat) :
    exp(sum_n a n) = part_prod (fun j => mkposreal (exp (a j)) (exp_pos (a j))) n.
  Proof.
    unfold part_prod, sum_n, sum_n_m, Iter.iter_nat.
    rewrite Iter.iter_iter', iota_is_an_annoying_seq.
    unfold Iter.iter', part_prod_n.
    generalize (List.seq 0 (S n - 0)); intros l; simpl.
    rewrite ListAdd.fold_right_map.
    induction l; simpl.
    - apply exp_0.
    - rewrite exp_plus.
      now rewrite IHl.
  Qed.

  Lemma part_prod_le2 (a b : nat -> posreal) (n : nat) :
    (forall j, a j <= b j) -> part_prod a n <= part_prod b n.
  Proof.
    generalize (pos_part_prod a n).
    unfold part_prod, part_prod_n.
    generalize (List.seq 0 (S n - 0)); intros l; simpl.
    rewrite ListAdd.fold_right_map; intros.
    induction l; simpl; intros.
    - lra.
    - simpl in H.
      replace (0) with ((a a0)*0) in H by lra.
      apply Rmult_lt_reg_l in H.
      specialize (IHl H).
      apply Rmult_le_compat; trivial.
      + left; apply cond_pos.
      + left; trivial.
      + apply cond_pos.
  Qed.

  Lemma Ropp_sum_Ropp (a : nat -> R) (n : nat) :
    sum_n a n = - sum_n (fun j : nat => - a j) n.
  Proof.
    unfold sum_n, sum_n_m, Iter.iter_nat.
    rewrite Iter.iter_iter', iota_is_an_annoying_seq.
    rewrite Iter.iter_iter'.
    generalize (List.seq 0 (S n - 0)); intros l; simpl.
    unfold Iter.iter', zero, plus; simpl.
    induction l; simpl; lra.
 Qed.

  Definition l1_divergent (a : nat -> R) := is_lim_seq (sum_n a) p_infty.

  Lemma a1_pos_pf {a : R} :
    (0 <= a < 1) -> 0 < 1- a.
  Proof.
    lra.
  Qed.

  Lemma Fprod_0 (a : nat -> R) 
    (abounds : forall n, 0 <= a n < 1) :
    l1_divergent a ->
    is_lim_seq (part_prod (fun n => (mkposreal (1 - a n)  (a1_pos_pf (abounds  n))))) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                    (w := fun n => exp (sum_n (fun j => -a j) n)).
    - unfold eventually; exists (0%nat); intros.
      split; [left; apply pos_part_prod |].
      rewrite exp_sum.
      apply part_prod_le2.
      intros; apply exp_ineq.
    - apply is_lim_seq_const.
    - apply is_lim_seq_spec; unfold is_lim_seq'.
      intros; unfold eventually.
      assert (is_lim_seq (sum_n (fun j => - a j)) m_infty).
      + apply is_lim_seq_opp.
        apply (is_lim_seq_ext (sum_n a)); [apply Ropp_sum_Ropp | apply H].
      + apply is_lim_seq_spec in H0; unfold is_lim_seq' in H0.
        unfold eventually in H0.
        specialize (H0 (ln eps)); destruct H0.
        exists x; intros.
        specialize (H0 n H1).
        rewrite Rminus_0_r, Rabs_right by (left; apply exp_pos).
        replace (pos eps) with (exp (ln eps)); [| apply exp_ln, cond_pos].
        now apply exp_increasing.
  Qed.

  Lemma pos1 (a : R) :
    0 <= a -> 0 < 1 + a.
  Proof.
    lra.
  Qed.

  Lemma prod_exp_bound (a : nat -> R) 
    (apos : forall n, 0 <= a n) :
    (forall m,
        part_prod (fun n => mkposreal (1 + a n) (pos1 (a n) (apos n))) m <=
        exp (sum_n a m)).
   Proof.
     intros.
     rewrite exp_sum.
     apply part_prod_le2.
     intros; apply exp_ineq.
   Qed.

  Lemma Fprod_B (b : nat -> R) 
    (bpos : forall n, 0 <= b n) :
    Rbar_le
      (Lim_seq (part_prod (fun n => (mkposreal (1 + b n) (pos1 (b n) (bpos n))))))
      (Lim_seq (fun m => exp (sum_n b m))).
  Proof.
    intros.
    apply Lim_seq_le_loc.
    exists (0%nat); intros.
    apply prod_exp_bound.
  Qed.

  Lemma Fprod_B2 (b : nat -> R)
    (bpos : forall n, 0 <= b n) :
    ex_series b ->
    exists (B:R),
      Rbar_le
        (Lim_seq (part_prod (fun n => (mkposreal (1 + b n) (pos1 (b n) (bpos n))))))
        B.
  Proof.
    intros.
    destruct H.
    exists (exp x).
    replace (Finite (exp x)) with (Lim_seq (fun m => exp (sum_n b m))).
    - apply Fprod_B.
    - rewrite series_seq in H.
      rewrite Lim_seq_continuous.
      + apply is_lim_seq_unique in H.
        rewrite H.
        now simpl.
      + generalize continuous_exp; intros.
        rewrite continuity_pt_filterlim.
        apply H0.
      + now exists x.
  Qed.

  Lemma SimpleExpectation_nneg (f : Ts -> R)
        {frf: FiniteRangeFunction f}
        {rvf : RandomVariable dom borel_sa f} :
    NonnegativeFunction f ->
    0 <= SimpleExpectation f.
  Proof.
    intros.
    replace (0) with (SimpleExpectation (const 0)).
    - apply SimpleExpectation_le.
      apply H.
    - apply SimpleExpectation_const.
  Qed.

  Lemma SimpleExpectation_sq_nneg (f : Ts -> R)
        {frf: FiniteRangeFunction f}
        {rvf : RandomVariable dom borel_sa f} :
    0 <= SimpleExpectation (rvsqr f).
  Proof.
    apply SimpleExpectation_nneg.
    intro x.
    apply Rle_0_sqr.
  Qed.

  Lemma Dvoretzky_8_F_le_1 (theta:R) 
        ( X Y : nat -> Ts -> R)
        (T : nat -> R -> R)
        (F : nat -> posreal)
        (rvy : forall n, RandomVariable dom borel_sa (Y n)) 
        (svy : forall n, FiniteRangeFunction (Y n)) 
        (rvx : forall n, RandomVariable dom borel_sa (X n)) 
        (svx: forall n, FiniteRangeFunction (X n))
        (rvt : forall n, RandomVariable borel_sa borel_sa (fun r:R => T n r))        
        (svt: forall n, FiniteRangeFunction (fun r:Ts => T n (X n r))) :
  (forall (n:nat), F n >= 0) ->
  (forall (n:nat) (r:R), Rle (Rabs ((T n r) - theta)) (F n * Rabs (r-theta))) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r => T n (X n r)) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation_rv (X n) (Y n)) (fun x : Ts => const 0 x)) ->
  (forall n, F n <= 1) ->
  ex_series (fun n => SimpleExpectation (rvsqr (Y n))) ->
  is_lim_seq (part_prod F) 0 ->
  is_lim_seq (fun n => SimpleExpectation (rvsqr (rvminus (X n) (const theta)))) 0.
 Proof.
  intros.
  apply (Dvoretzky4B_Vpos F (fun n => SimpleExpectation (rvsqr (Y n)))); trivial.
  - intros.
    apply SimpleExpectation_sq_nneg.
  - intros.
    apply SimpleExpectation_sq_nneg.
  - intros.
    unfold pos_sq_fun, pos_sq; simpl.
    replace ((F n) * (F n)) with (Rsqr (F n)) by now simpl.
    generalize (Dvoretzky_rel n theta X Y T F (rvy n) (svy n) (rvx n) (svx n)
                              (rvt n) (svt n) (rvx (S n)) (svx (S n))); intros rel.
    now apply rel.
 Qed.

End Dvoretzky.

Section Derman_Sacks.

 Context 
   {Ts : Type}
   {dom: SigmaAlgebra Ts}
   {prts: ProbSpace dom}.

  Lemma ex_series_nneg_bounded (f g : nat -> R) :
    (forall n, 0 <= f n) ->
    (forall n, f n <= g n) ->
    ex_series g ->
    ex_series f.
  Proof.
    intros.
    apply (ex_series_le f g); trivial.
    intros.
    unfold norm; simpl.
    unfold abs; simpl.
    rewrite Rabs_right; trivial.
    now apply Rle_ge.
  Qed.

  Lemma ex_finite_lim_seq_bounded (f : nat -> R) :
    ex_finite_lim_seq f ->
    exists (M:R),
      forall n, Rabs (f n) <= M.
  Proof.
    intros.
    destruct H.
    apply is_lim_seq_spec in H.
    unfold is_lim_seq' in H.
    assert (0 < 1) by lra.
    specialize (H (mkposreal _ H0)).
    destruct H.
    exists (Rmax ((Rabs x)+1) (Rmax_list (map (fun n => Rabs (f n)) (seq 0 x0)))).
    intros.
    destruct (dec_le x0 n).
    - specialize (H n H1).
      apply Rle_trans with (r2 := Rabs x + 1).
      + simpl in H.
        generalize (Rabs_triang_inv (f n) x); intros.
        lra.
      + apply Rmax_l.
    - assert (n < x0)%nat by lia.
      apply Rle_trans with (r2 := Rmax_list (map (fun n0 : nat => Rabs (f n0)) (seq 0 x0))).
      + apply (Rmax_spec_map (seq 0 x0) (fun n => Rabs (f n)) n).
        apply in_seq; lia.
      + apply Rmax_r.
  Qed.

  Lemma ex_series_bounded (f : nat -> R) :
    ex_series f ->
    exists (M:R),
      forall n, Rabs (sum_n f n) <= M.
  Proof.
    intros.
    apply ex_finite_lim_seq_bounded.
    now apply ex_finite_lim_series.
  Qed.

  Lemma ex_finite_lim_seq_plus (f g : nat -> R) :
    ex_finite_lim_seq f ->
    ex_finite_lim_seq g ->
    ex_finite_lim_seq (fun n => f n + g n).
  Proof.
    intros.
    destruct H.
    destruct H0.
    exists (x + x0).
    now apply is_lim_seq_plus'.
  Qed.

  Lemma ex_series_pos_bounded (f : nat -> R) (B:R) :
    (forall n, 0 <= f n) ->
    (forall n, sum_n f n <= B) ->
    ex_series f.
  Proof.
    intros.
    rewrite <- ex_finite_lim_series.
    apply ex_finite_lim_seq_incr with (M := B); trivial.
    intros.
    rewrite sum_Sn.
    unfold plus; simpl.
    specialize (H (S n)).
    lra.
  Qed.
  
  Lemma Abel_descending_convergence  (a b : nat -> R) :
    ex_series b ->
    (forall n, a n >= a (S n)) ->
    (exists M, forall n, a n >= M) ->
    ex_series (fun n => a n * b n).
  Proof.
    intros.
    pose (B := sum_n b).
    assert (forall n, sum_n (fun j => a j * b j) (S n) = 
                      (a (S n))*(B (S n)) + sum_n (fun j => (B j) * (a j - (a (S j)))) n).
    {
      intros.
      do 2 rewrite sum_n_Reals.
      induction n.
      - unfold B.
        rewrite sum_n_Reals.
        simpl.
        rewrite sum_O.
        ring_simplify; lra.
      - replace (S (S n)) with (S (n+1)) by lia.
        simpl.
        replace (n+1)%nat with (S n) by lia.
        rewrite IHn.
        apply Rplus_eq_reg_r with (r := sum_f_R0 (fun j : nat => B j * (a (j) - a (S j))) n).
        ring_simplify.
        apply Rplus_eq_reg_r with (r := - (a (S n) * B (S n))).
        ring_simplify.
        unfold B.
        do 2 rewrite sum_n_Reals.        
        replace (S n) with (n+1)%nat by lia.
        simpl.
        now ring_simplify.
    }
    rewrite <- ex_finite_lim_series.
    rewrite ex_finite_lim_seq_S.
    apply (ex_finite_lim_seq_ext _ _ H2).
    generalize (ex_series_bounded _ H); intros.
    rewrite <- ex_finite_lim_series in H.
    destruct H.
    assert (ex_finite_lim_seq a).
    {
      destruct H1.
      apply ex_finite_lim_seq_decr with (M := x0).
      - intros.
        specialize (H0 n).
        lra.
      - intros.
        specialize (H1 n).
        lra.
    }
    destruct H4.
    apply ex_finite_lim_seq_plus.
    - unfold ex_finite_lim_seq.
      exists (x0 * x).
      apply is_lim_seq_mult'.
      + now apply is_lim_seq_incr_1 in H4.
      + now apply is_lim_seq_incr_1 in H.
    - destruct H3.
      unfold B.
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 (sum_n (fun j : nat => scal x1 (Rabs (a j - a (S j)))) n)).
      {
        intros.
        apply sum_n_le_loc; intros.
        rewrite Rabs_mult.
        apply Rmult_le_compat_r; trivial.
        apply Rabs_pos.
      }
      assert (forall i h, a i >= a (i + h)%nat).
      {
        induction h.
        - replace (i + 0)%nat with i by lia; lra.
        - eapply Rge_trans.
          apply IHh.
          now replace (i + S h)%nat with (S (i + h))%nat by lia.
      }
      assert (forall i j, (i<=j)%nat -> a i >= a j).
      {
        intros.
        specialize (H6 i (j - i)%nat).
        now replace (i + (j - i))%nat with j in H6 by lia.
      }
      assert (forall n, sum_n (fun j => Rabs (a j - a (S j))) n = Rabs(a (0%nat) - a (S n))).
      {
        induction n.
        - now rewrite sum_O.
        - rewrite sum_Sn.
          rewrite IHn.
          unfold plus; simpl.
          rewrite Rabs_right, Rabs_right, Rabs_right.
          + ring.
          + specialize (H7 (0%nat) (S (S n))).
            cut_to H7; try lia.
            lra.
          + specialize (H0 (S n)); lra.
          + specialize (H7 (0%nat) (S n)).
            cut_to H7; try lia.
            lra.
     }
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 x1 * Rabs((a 0%nat) - a (S n))).
      {
        intros.
        specialize (H5 n).
        rewrite sum_n_scal_l in H5.
        unfold scal in H5; simpl in H5.
        unfold mult in H5; simpl in H5.
        now rewrite H8 in H5.
      }
      rewrite ex_finite_lim_series.
      apply ex_series_Rabs.
      destruct H1.
      assert (forall n, Rabs (a n) <= Rmax (a 0%nat) (-x2)).
      {
        intros.
        apply Rabs_le_between_Rmax.
        split; apply Rge_le; trivial.
        apply H7; lia.
      }
      assert (forall n, Rabs (a 0%nat - a (S n)) <= Rabs(a 0%nat) + Rmax (a 0%nat) (-x2)).
      {
        intros.
        unfold Rminus.
        generalize (Rabs_triang (a 0%nat) (- a (S n))); intros.
        eapply Rle_trans.
        apply H11.
        apply Rplus_le_compat_l.
        now rewrite Rabs_Ropp.
      }
      apply ex_series_pos_bounded with (B := x1 * (Rabs (a 0%nat) + Rmax (a 0%nat) (- x2))).
      + intros.
        apply Rabs_pos.
      + intros.
        eapply Rle_trans.
        apply H9.
        apply Rmult_le_compat_l.
        * specialize (H3 0%nat).
          apply Rle_trans with (r2 := Rabs (sum_n b 0%nat)); trivial.
          apply Rabs_pos.
        * apply H11.
  Qed.

  Lemma Abel_ascending_convergence  (a b : nat -> R) :
    ex_series b ->
    (forall n, a n <= a (S n)) ->
    (exists M, forall n, a n <= M) ->
    ex_series (fun n => a n * b n).
  Proof.
    intros.
    pose (B := sum_n b).
    assert (forall n, sum_n (fun j => a j * b j) (S n) = 
                      (a (S n))*(B (S n)) + sum_n (fun j => (B j) * (a j - (a (S j)))) n).
    {
      intros.
      do 2 rewrite sum_n_Reals.
      induction n.
      - unfold B.
        rewrite sum_n_Reals.
        simpl.
        rewrite sum_O.
        ring_simplify; lra.
      - replace (S (S n)) with (S (n+1)) by lia.
        simpl.
        replace (n+1)%nat with (S n) by lia.
        rewrite IHn.
        apply Rplus_eq_reg_r with (r := sum_f_R0 (fun j : nat => B j * (a (j) - a (S j))) n).
        ring_simplify.
        apply Rplus_eq_reg_r with (r := - (a (S n) * B (S n))).
        ring_simplify.
        unfold B.
        do 2 rewrite sum_n_Reals.        
        replace (S n) with (n+1)%nat by lia.
        simpl.
        now ring_simplify.
    }
    rewrite <- ex_finite_lim_series.
    rewrite ex_finite_lim_seq_S.
    apply (ex_finite_lim_seq_ext _ _ H2).
    generalize (ex_series_bounded _ H); intros.
    rewrite <- ex_finite_lim_series in H.
    destruct H.
    assert (ex_finite_lim_seq a).
    {
      destruct H1.
      apply ex_finite_lim_seq_incr with (M := x0).
      - intros.
        specialize (H0 n).
        lra.
      - intros.
        specialize (H1 n).
        lra.
    }
    destruct H4.
    apply ex_finite_lim_seq_plus.
    - unfold ex_finite_lim_seq.
      exists (x0 * x).
      apply is_lim_seq_mult'.
      + now apply is_lim_seq_incr_1 in H4.
      + now apply is_lim_seq_incr_1 in H.
    - destruct H3.
      unfold B.
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 (sum_n (fun j : nat => scal x1 (Rabs (a j - a (S j)))) n)).
      {
        intros.
        apply sum_n_le_loc; intros.
        rewrite Rabs_mult.
        apply Rmult_le_compat_r; trivial.
        apply Rabs_pos.
      }
      assert (forall i h, a i <= a (i + h)%nat).
      {
        induction h.
        - replace (i + 0)%nat with i by lia; lra.
        - eapply Rle_trans.
          apply IHh.
          now replace (i + S h)%nat with (S (i + h))%nat by lia.
      }
      assert (forall i j, (i<=j)%nat -> a i <= a j).
      {
        intros.
        specialize (H6 i (j - i)%nat).
        now replace (i + (j - i))%nat with j in H6 by lia.
      }
      assert (forall n, sum_n (fun j => Rabs (a j - a (S j))) n = Rabs(a (0%nat) - a (S n))).
      {
        induction n.
        - now rewrite sum_O.
        - rewrite sum_Sn.
          rewrite IHn.
          unfold plus; simpl.
          rewrite Rabs_left1, Rabs_left1, Rabs_left1.
          + ring.
          + specialize (H7 (0%nat) (S (S n))).
            cut_to H7; try lia.
            lra.
          + specialize (H0 (S n)); lra.
          + specialize (H7 (0%nat) (S n)).
            cut_to H7; try lia.
            lra.
     }
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 x1 * Rabs((a 0%nat) - a (S n))).
      {
        intros.
        specialize (H5 n).
        rewrite sum_n_scal_l in H5.
        unfold scal in H5; simpl in H5.
        unfold mult in H5; simpl in H5.
        now rewrite H8 in H5.
      }
      rewrite ex_finite_lim_series.
      apply ex_series_Rabs.
      destruct H1.
      assert (forall n, Rabs (a n) <= Rmax (x2) (- (a 0%nat))).
      {
        intros.
        apply Rabs_le_between_Rmax.
        split; trivial.
        apply H7; lia.
      }
      assert (forall n, Rabs (- a 0%nat + a (S n)) <= Rmax (x2) (- a 0%nat) + Rabs (a (S n)) ).
      {
        intros.
        unfold Rminus.
        generalize (Rabs_triang (- a 0%nat) (a (S n))); intros.
        eapply Rle_trans.
        apply H11.
        apply Rplus_le_compat_r.
        now rewrite Rabs_Ropp.
      }
      apply ex_series_pos_bounded with (B := x1 * (2* Rmax x2 (- a 0%nat))).
      + intros.
        apply Rabs_pos.
      + intros.
        eapply Rle_trans.
        apply H9.
        apply Rmult_le_compat_l.
        * specialize (H3 0%nat).
          apply Rle_trans with (r2 := Rabs (sum_n b 0%nat)); trivial.
          apply Rabs_pos.
        * rewrite <- Rabs_Ropp.
          rewrite Ropp_minus_distr.
          unfold Rminus.
          rewrite Rplus_comm.
          eapply Rle_trans.
          apply H11.
          specialize (H10 (S n)).
          lra.
  Qed.

  Lemma DS_1_helper (a b c delta zeta : nat -> R) (N0 N : nat)
    (b1pos :forall n, 0 <= b n) :
    (forall n, 
      (n>= N0)%nat -> 
      zeta (S n) <= Rmax (a n) ((1+b n)*zeta n + delta n - c n)) ->
    (N > N0)%nat ->
    let B := part_prod (fun i => mkposreal _ (pos1 (b i) (b1pos i))) in
    forall (n:nat),
      (n > N)%nat ->
      zeta (S n) <= Rmax (((B n)/(B (N-1)%nat))*(zeta N) +
                          (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) N n)
                         (Rmax_list
                            (map (fun k => 
                                    (B n)/(B k)*(a k)  +
                                    (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) (S k) n)
                                         (seq N (S (n-N))%nat))).
    Proof.
      intros.
      pose (h := (n - N)%nat).
      replace (n) with (h + N)%nat by lia.
      induction h.
      - replace (0 + N)%nat with (N) by lia.
        replace (N - N)%nat with 0%nat by lia.
        specialize (H N).
        cut_to H; try lia.
        rewrite sum_n_n.
        replace (B N / (B (N-1)%nat)) with (1 + b N).
        + simpl.
          assert (B N <> 0) by
            apply Rgt_not_eq, part_prod_n_pos.
          replace (B N / B N) with 1; try field; trivial.
          rewrite sum_n_m_zero; try lia.
          rewrite Rmult_0_r, Rplus_0_r, Rmult_1_l.
          replace (B N * ((delta N - c N) / B N)) with (delta N - c N); try field; trivial.
          rewrite Rmax_comm.
          eapply Rle_trans.
          * apply H.
          * right.
            f_equal.
            lra.
        + replace (N) with (S (N-1)%nat) at 2 by lia.
          subst B.
          unfold part_prod.
          rewrite part_prod_n_S; simpl; try lia.
          field_simplify.
          * now replace (S (N-1))%nat with N by lia.
          * apply Rgt_not_eq.
            apply part_prod_n_pos.
     - eapply Rle_trans.
       apply H; try lia.
       replace (S h + N - N)%nat with (S h) by lia.
       assert (0 <= (1 + b (S h + N)%nat) ) by (generalize (b1pos (S h + N)%nat); try lra).
       apply Rmult_le_compat_l with (r := (1 + b (S h + N)%nat) ) in IHh; trivial.
       apply Rplus_le_compat_r with (r := delta (S h + N)%nat) in IHh.
       apply Rplus_le_compat_r with (r := - c (S h + N)%nat) in IHh.
       unfold Rminus at 1.
       apply Rle_max_compat_l with (z := a (S h + N)%nat) in IHh.
       eapply Rle_trans.
       apply IHh.
       replace (h + N - N)%nat with (h) by lia.
       rewrite <- RmaxRmult; trivial.
       pose (f := fun j => (delta j - c j)/B j).
       replace (fun j => (delta j - c j)/B j) with f; try now subst f.
       replace ((1 + b (S h + N)%nat) *
                (B (h + N)%nat / B (N - 1)%nat * zeta N +
                 B (h + N)%nat * sum_n_m f N (h + N))) with
           (B (S h + N)%nat / B (N - 1)%nat * zeta N +
                 B (S h + N)%nat * sum_n_m f N (h + N)).
       + rewrite <- Rmax_list_map_const_mul; trivial.
         replace (seq N (S (S h))) with
             ((seq N (S h)) ++ [(S h + N)%nat]).
         * rewrite Rmax_list_app; [| apply seq_not_nil; lia].
           rewrite sum_n_m_zero with (n0 := (S (S h + N)%nat)); try lia.
           rewrite Rmult_0_r, Rplus_0_r.
           unfold Rdiv; rewrite Rinv_r_simpl_r; [|apply Rgt_not_eq, part_prod_n_pos].
           rewrite Rmax_comm.
           replace (S h + N)%nat with (S (h + N)%nat) by lia.
           rewrite sum_n_Sm; try lia.
           rewrite Rmax_assoc.
           apply Rle_max_compat_r.
           rewrite Rplus_max_distr_r.
           rewrite Rplus_max_distr_r.           
           apply Rmax_le_compat.
           -- do 2 rewrite Rplus_assoc.
              apply Rplus_le_compat_l.
              unfold plus; simpl.
              rewrite Rmult_plus_distr_l.
              apply Rplus_le_compat_l.
              subst f.
              simpl; right; field.
              apply Rgt_not_eq, part_prod_n_pos.
           -- rewrite Rplus_assoc.
              replace (delta (S (h + N)) + - c (S (h + N))) with
                  (B (S (h + N)%nat) * (f (S (h + N)%nat))).
              ++ right.
                 apply Rmax_list_plus_r.
                 intros.
                 subst B.
                 unfold part_prod.
                 rewrite part_prod_n_S; try lia.
                 simpl.
                 rewrite sum_n_Sm; try lia.
                 unfold plus; simpl.
                 field.
                 apply Rgt_not_eq, part_prod_n_pos.                 
              ++ subst f; simpl; field.
                 apply Rgt_not_eq, part_prod_n_pos.                 
         * symmetry.
           rewrite seq_S.
           now replace (N + S h)%nat with (S h + N)%nat by lia.
       + subst B.
         replace (S h + N)%nat with (S (h + N))%nat by lia.
         unfold part_prod.
         rewrite part_prod_n_S; try lia.
         simpl; field.
         apply Rgt_not_eq.
         apply part_prod_n_pos.

      Qed.

   Lemma sup_seq_pos (f : nat -> R) :
     (forall n, 0 <= f n) ->
     Rbar_le 0 (Sup_seq f).
   Proof.
     intros.
     replace (Finite 0) with (Sup_seq (fun _ => 0)).
     now apply Sup_seq_le.
     apply Sup_seq_const.
   Qed.
   
    Lemma DS_1_part1 (a b c delta zeta : nat -> R) (N0 N:nat)
          (b1pos : forall n, 0 <= b n) :
    (forall n, 0 <= a n) ->
    (N > N0)%nat ->
    (forall n, 0 <= c n) ->
    (forall n, 0 <= zeta n) ->
    is_lim_seq a 0 ->
    ex_series b ->
    ex_series delta ->
    is_lim_seq (sum_n c) p_infty ->
    (forall n, (n>= N0)%nat -> 
               zeta (S n) <= Rmax (a n) ((1+b n)*zeta n + delta n - c n)) ->
    let B := part_prod (fun i => mkposreal _ (pos1 (b i) (b1pos i))) in
    exists (N1 : nat),
      forall n, 
        (n > max N N1)%nat ->
        zeta (S n) <= (Rmax_list
                         (map (fun k => 
                                 (B n)/(B k)*(a k)  +
                                 (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) (S k) n)
                              (seq N (S (n-N))%nat))).
  Proof.
    intros.
    generalize (DS_1_helper a b c delta zeta N0 N b1pos); intros.
    cut_to H8; trivial.
    generalize (Fprod_B2 b b1pos H4); intros.
    destruct H9 as [BB ?].
    assert (Bincr:forall m, B m <= B (S m)).
    {
      intros.
      subst B.
      unfold part_prod.
      rewrite part_prod_n_S; try lia.
      simpl.
      replace
        (part_prod_n
           (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (b1pos n0) |}) 0 m) with
          ((part_prod_n
              (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (b1pos n0) |}) 0 m)*1) at 1 by lra.
      apply Rmult_le_compat_l.
      + left; apply pos_part_prod_n.
      + generalize (b1pos (S m)); lra.
    }
    assert (forall m, B m <= BB).
    {
      intros.
      assert (Rbar_le (B m) BB).
      - eapply Rbar_le_trans.
        shelve.
        apply H9.
        Unshelve.
        subst B.
        apply Lim_seq_increasing_le.
        apply Bincr.
      - now simpl in H10.
    }
    assert (BBpos: 0 < BB).
    {
      eapply Rlt_le_trans.
      shelve.
      apply (H10 0%nat).
      Unshelve.
      apply pos_part_prod_n.
    }
    assert (ex_series (fun j => (delta j)/(B j))).
    {
      unfold Rdiv.
      setoid_rewrite Rmult_comm.
      apply Abel_descending_convergence; trivial.
      - intros.
        apply Rle_ge.
        apply Rinv_le_contravar; trivial.
        apply pos_part_prod_n.
      - exists (/ BB).
        intros.
        apply Rle_ge.
        apply Rinv_le_contravar; trivial.
        apply pos_part_prod_n.
    }
    assert (is_lim_seq (sum_n (fun j => (c j)/(B j))) p_infty).
    {
      apply is_lim_seq_le_p_loc with (u := sum_n (fun j => (c j)/BB)).
      - exists (0%nat); intros.
        unfold sum_n.
        apply sum_n_m_le.
        intros.
        unfold Rdiv.
        apply Rmult_le_compat_l; trivial.
        apply Rinv_le_contravar; trivial.
        apply pos_part_prod_n.
      - apply (is_lim_seq_ext (fun n => scal (/BB) (sum_n c n))).
        + intros.
          rewrite <- (sum_n_scal_l (/BB) c).
          apply sum_n_ext; intros.
          unfold scal; simpl.
          unfold mult; simpl.
          unfold Rdiv; lra.
        + replace (p_infty) with (Rbar_mult (/ BB) p_infty).
          apply is_lim_seq_scal_l; trivial.
          apply Rbar_mult_p_infty_pos.
          now apply Rinv_0_lt_compat.
    }
    assert (is_lim_seq (sum_n (fun j => (delta j - (c j))/(B j))) m_infty).
    {
      apply is_lim_seq_ext with 
          (u := (fun n => (sum_n (fun j => (delta j)/(B j)) n) -
                          (sum_n (fun j => (c j)/(B j)) n))).
      - intros.
        unfold Rminus.
        rewrite Ropp_sum_Ropp with (a := (fun j : nat => c j / B j)).
        rewrite Ropp_involutive.
        generalize (sum_n_plus (fun j : nat => delta j / B j)
                               (fun j : nat => - (c j / B j)) n); intros.
        unfold plus in H13; simpl in H13.
        rewrite <- H13.
        apply sum_n_ext.
        intros.
        field_simplify; trivial; apply Rgt_not_eq, pos_part_prod_n.
      - apply ex_series_is_lim_seq in H11.
        apply is_lim_seq_minus with (l1 := Series (fun j : nat => delta j / B j))
                                    (l2 := p_infty); trivial.
        now unfold is_Rbar_minus, is_Rbar_plus; simpl.
    }
    assert (is_lim_seq 
              (fun n => (B n)* sum_n_m (fun j : nat => (delta j - c j) / B j) N n) m_infty).
    {
      assert (is_lim_seq 
              (fun n => sum_n_m (fun j : nat => (delta j - c j) / B j) N n) m_infty).
      - rewrite is_lim_seq_incr_n with (N := N).
        apply is_lim_seq_ext with
            (u := fun n => 
                    (sum_n_m (fun j : nat => (delta j - c j) / B j) 0 (n + N)) -
                    (sum_n_m (fun j : nat => (delta j - c j) / B j) 0 (N-1))).
        intros.
        rewrite sum_split with (m := (N-1)%nat); try lia.        
        unfold plus; simpl; ring_simplify.
        replace (S (N-1))%nat with N by lia; trivial.
        apply is_lim_seq_minus with 
            (l1 := m_infty)
            (l2 := sum_n_m (fun j : nat => (delta j - c j) / B j) 0 (N - 1)).
        + now rewrite is_lim_seq_incr_n with (N := N) in H13.
        + apply is_lim_seq_const.
        + now unfold is_Rbar_minus, is_Rbar_plus; simpl.
      - apply is_lim_seq_mult with (l1 := Lim_seq (fun n => B n)) (l2 := m_infty); trivial.
        + apply Lim_seq_correct.
          now apply ex_lim_seq_incr.
        + apply is_Rbar_mult_sym.
          apply is_Rbar_mult_m_infty_pos.
          apply Rbar_lt_le_trans with (y := B 0%nat).
          * unfold B; simpl.
            apply part_prod_n_pos.
          * replace (Finite (B 0%nat)) with (Lim_seq (const (B 0%nat))) by apply Lim_seq_const.
            apply Lim_seq_le_loc.
            exists (0%nat); intros.
            unfold const.
            induction n.
            -- lra.
            -- eapply Rle_trans.
               apply IHn; try lia.
               apply Bincr.
     }
    assert (
      exists (N1 : nat),
        forall n, 
          (n > max N N1)%nat ->
          (B n / B (N - 1)%nat * zeta N +
           B n * sum_n_m (fun j : nat => (delta j - c j) / B j) N n) < 0).
    {
      assert (is_lim_seq
                (fun n => B n / B (N - 1)%nat * zeta N +
                          B n * sum_n_m (fun j : nat => (delta j - c j) / B j) N n) m_infty).
      - assert (forall n, B n / B (N-1)%nat * zeta N <= BB / B(N-1)%nat * zeta N).
        {
          intros.
          unfold Rdiv.
          apply Rmult_le_compat_r; trivial.
          apply Rmult_le_compat_r; trivial.
          left; apply Rinv_0_lt_compat.
          apply part_prod_n_pos.
        }
        apply is_lim_seq_spec.
        unfold is_lim_seq'.
        intros.
        apply is_lim_seq_spec in H14.
        unfold is_lim_seq' in H14.
        specialize (H14 ((M - BB /B(N-1)%nat * zeta N))).
        destruct H14.
        exists x.
        intros.
        specialize (H14 n H16).
        specialize (H15 n).
        lra.
      - apply is_lim_seq_spec in H15.
        unfold is_lim_seq' in H15.
        specialize (H15 0).
        destruct H15.
        exists (max x N).
        intros.
        specialize (H15 n).
        now cut_to H15; try lia.
    }
    destruct H15.
    exists x; intros.
    specialize (H8 n).
    cut_to H8; try lia.
    rewrite Rmax_right in H8.
    now unfold B.
    left.
    eapply Rlt_le_trans.
    apply H15; try lia.
    apply Rmax_Rle in H8.
    destruct H8.
    - specialize (H15 n H16).
      specialize (H2 (S n)).
      unfold B in H15.
      lra.
    - specialize (H2 (S n)).
      lra.
  Qed.
  
  Lemma Rmult_le_compat2 (r1 r2 r3 r4 : R) :
    0 <= r1 -> 0 <= r2 -> 0 <= r4 ->
    r1 <= r2 -> r3 <= r4 ->
    r1 * r3 <= r2 * r4.
  Proof.
    intros.
    destruct (Rle_dec 0 r3).
    - now apply Rmult_le_compat.
    - apply Rle_trans with (r2 := 0).
      + rewrite Rmult_comm.
        apply Rmult_le_0_r; lra.
      + now apply Rmult_le_pos.
  Qed.

  Lemma DS_1_part2 (a b c delta zeta : nat -> R) (N0 N:nat)
        (b1pos : forall n, 0 <= b n) :
    (forall n, 0 <= a n) ->
    (N > N0)%nat ->
    (forall n, 0 <= c n) ->
    (forall n, 0 <= zeta n) ->
    is_lim_seq a 0 ->
    ex_series b ->
    ex_series delta ->
    is_lim_seq (sum_n c) p_infty ->
    (forall n, (n>= N0)%nat -> 
               zeta (S n) <= Rmax (a n) ((1+b n)*zeta n + delta n - c n)) ->
    let B := part_prod (fun i => mkposreal _ (pos1 (b i) (b1pos i))) in
    
    exists (N1 : nat),
      forall n, 
        (n > max N N1)%nat ->
        zeta (S n) <=
        (Lim_seq B) *
        (Sup_seq (fun n => a (n + N)%nat) +
         (Rmax_list
           (map (fun k => Rabs
                            (sum_n_m (fun j => (delta j)/(B j)) (S k) n))
                (seq N (S (n-N))%nat)))).
   Proof.
     intros.
     generalize (DS_1_part1 a b c delta zeta N0 N b1pos); intros.
     cut_to H8; trivial.
     destruct H8.
     exists x; intros.
     specialize (H8 n H9).
     eapply Rle_trans.
     apply H8.
     assert (Blim:Rbar_le (B n) (Lim_seq B)).
     {
       apply Lim_seq_increasing_le.
       intros.
       subst B.
       unfold part_prod.
       rewrite part_prod_n_S; try lia.
       simpl.
       replace
         (part_prod_n
            (fun i : nat => {| pos := 1 + b i; cond_pos := pos1 (b i) (b1pos i) |}) 0 n0) with
           ((part_prod_n
               (fun i : nat => {| pos := 1 + b i; cond_pos := pos1 (b i) (b1pos i) |}) 0 n0)*1) at 1 by lra.
       apply Rmult_le_compat_l.
       - left; apply pos_part_prod_n.
       - generalize (b1pos (S n0)); lra.
     }
     assert (fin_LimB: is_finite (Lim_seq B)).
     { 
       generalize (Fprod_B2 b b1pos H4); intros.
       destruct H10.
       apply bounded_is_finite with (a := 0) (b := x0); trivial.
       apply Lim_seq_pos.
       intros.
       left.
       apply pos_part_prod.
     }
     rewrite <- fin_LimB in Blim.
     simpl in Blim.
     generalize (Rmax_list_map_plus
                   (fun k => (B n)/(B k)*(a k))
                   (fun k =>
                      (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) (S k) n)
                   (seq N (S (n-N))%nat)); intros.
     eapply Rle_trans.
     apply H10.
     rewrite Rmult_plus_distr_l.
     apply Rplus_le_compat.
     - apply Rle_trans with
           (r2 :=  Rmax_list (map (fun k : nat => B n * a k) (seq N (S (n - N)))) ).
       + apply Rmax_list_fun_le.
         intros.
         apply Rmult_le_compat_r; trivial.
         unfold Rdiv.
         replace (B n) with ((B n)*1) at 2 by lra.
         apply Rmult_le_compat_l.
         * left.
           apply pos_part_prod.
         * replace (1) with (/1) by lra.
           apply Rinv_le_contravar; try lra.
           unfold B.
           assert (0 < 1) by lra.
           assert (part_prod (fun i => mkposreal _ H11) a0 <=
                   part_prod (fun i : nat => {| pos := 1 + b i; cond_pos := pos1 (b i) (b1pos i) |}) a0).
           {
             apply part_prod_le2.
             intros; simpl.
             generalize (b1pos j); lra.
           }
           eapply Rle_trans.
           shelve.
           apply H12.
           Unshelve.
           right.
           clear H12.
           induction a0.
           -- unfold part_prod, part_prod_n.
              simpl; lra.
           -- unfold part_prod.
              rewrite part_prod_n_S; try lia.
              unfold part_prod in IHa0.
              rewrite <- IHa0.
              simpl; lra.
       + assert (forall n, 0<B n).
         {
           intros.
           apply pos_part_prod.
         }
         rewrite Rmax_list_map_const_mul; [| now left].
         apply Rmult_le_compat; trivial.
         * now left.
         * now apply Rmax_list_map_nonneg.
         * generalize (Rmax_list_Sup_seq a N (n-N)%nat); intros.
           assert (is_finite (Sup_seq (fun n0 => a (n0 + N)%nat))).
           {
             apply is_lim_seq_bounded in H3.
             destruct H3 as [? ?].
             apply bounded_is_finite with (a := 0) (b := x0).
             - now apply sup_seq_pos.
             - apply sup_le_bound.
               intros.
               specialize (H3 (n0 + N)%nat).
               rewrite Rabs_right in H3; trivial.
               apply Rle_ge, H.
           }
           rewrite <- H13 in H12; apply H12.
     - rewrite <- Rmax_list_map_const_mul.
       + apply Rmax_list_fun_le.
         intros.
         apply Rmult_le_compat2.
         * left; apply pos_part_prod.
         * generalize (Lim_seq_pos B); intros.
           cut_to H11; [|left; apply pos_part_prod].
           now rewrite <- fin_LimB in H11.
         * apply Rabs_pos.
         * 
           assert (Bincr:forall m, B m <= B (S m)).
           {
             intros.
             subst B.
             unfold part_prod.
             rewrite part_prod_n_S; try lia.
             simpl.
             replace
               (part_prod_n
                  (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (b1pos n0) |}) 0 m) with
                 ((part_prod_n
                     (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (b1pos n0) |}) 0 m)*1) at 1 by lra.
             apply Rmult_le_compat_l.
             + left; apply pos_part_prod_n.
             + generalize (b1pos (S m)); lra.
           }
           generalize (Lim_seq_increasing_le B); intros.
           now cut_to H11.
         * assert (forall n,
                      ((fun j : nat => (delta j - c j) / B j) n) =
                      ((fun j : nat => plus (delta j/B j) (- c j / B j)) n)).
           {
             intros.
             unfold plus; simpl.
             field.
             apply Rgt_not_eq.
             apply pos_part_prod.
           }
           rewrite (sum_n_m_ext _ _ _ _ H11).
           rewrite sum_n_m_plus.
           unfold plus; simpl.
           replace  (Rabs (sum_n_m (fun j : nat => delta j / B j) (S a0) n)) with
               (Rabs (sum_n_m (fun j : nat => delta j / B j) (S a0) n) + 0) by lra.
           apply Rplus_le_compat.
           -- apply Rle_abs.
           -- replace (0) with (sum_n_m (const 0) (S a0) n).
              ++ apply sum_n_m_le.
                 intros.
                 unfold const.
                 unfold Rdiv.
                 apply Rmult_le_0_r.
                 ** specialize (H1 k).
                    lra.
                 ** left.
                    apply Rinv_0_lt_compat.
                    apply pos_part_prod.
              ++ replace (const 0) with (fun (n:nat) => (@zero R_AbelianGroup)).
                 ** rewrite sum_n_m_const_zero.
                    now unfold zero.
                 ** now unfold const, zero; simpl.
       + generalize (Lim_seq_pos B); intros.
         destruct (Lim_seq B); try now simpl.
         simpl in H11; apply H11.
         intros.
         left; apply part_prod_n_pos.
     Qed.

   Lemma Radd_minus (r1 r2 r3 : R) :
     r1 = r2 + r3 <-> r1 - r2 = r3.
   Proof.
     split; intros; try lra.
   Qed.

  Lemma Radd_radd_minus (r1 r2 r3 r4 : R):
    r1 + r2 = r3 + r4 <-> r3 - r1 = r2 - r4.
  Proof.
    split; intros; try lra.
  Qed.


  Lemma sum_n_m_Series_alt (f : nat -> R) (n m : nat) :
     (n <= m)%nat ->
     ex_series f ->
     sum_n_m f n m = Series (fun i => f (n + i)%nat) -
                     Series (fun i => f (S m + i)%nat).
   Proof.
     intros. 
     destruct (n == 0%nat).
     + setoid_rewrite e. clear H.
       induction m.
       -- cbn. rewrite (Series_incr_1); [lra |assumption].
       -- simpl. rewrite sum_n_Sm;[|lia].
          rewrite IHm. cbn.
          rewrite (Series_incr_1 (fun i => f (S(m + i)))).
          setoid_rewrite <-Nat.add_succ_l.
          replace (S m + 0)%nat with (S m) by lia.
          ring_simplify.
          now setoid_rewrite plus_n_Sm at 2.
          setoid_rewrite <-plus_Sn_m.
          now rewrite <-ex_series_incr_n.
     +
       assert (Hn : (0 < n)%nat).
       {
         destruct n.
         + intuition.
         + lia.
       }
     assert (Hm : (0 < S m)%nat) by lia.
     generalize (Series_incr_n f n Hn H0); intros.
     generalize (Series_incr_n f _ Hm H0); intros.
     rewrite H1 in H2.
     rewrite Radd_radd_minus in H2.
     rewrite <-H2. simpl.
     do 2 rewrite <-sum_n_Reals.
     replace n with (S (pred n)) by lia.
     rewrite sum_n_m_sum_n; try lia.
     reflexivity.
   Qed.
   
   Lemma sum_n_m_Series1 (f : nat -> R) (n m : nat) :
     (0 < n <= m)%nat ->
     ex_series f ->
     sum_n_m f n m = Series (fun i => f (n + i)%nat) -
                     Series (fun i => f (S m + i)%nat).
   Proof.
     intros.
     assert (Hn : (0 < n)%nat) by (now destruct H).
     assert (Hm : (0 < S m)%nat) by lia.
     generalize (Series_incr_n f n Hn H0); intros. 
     generalize (Series_incr_n f _ Hm H0); intros.
     rewrite H1 in H2.
     rewrite Radd_radd_minus in H2.
     rewrite <-H2. simpl.
     do 2 rewrite <-sum_n_Reals.
     replace n with (S (pred n)) by lia.
     rewrite sum_n_m_sum_n; try lia.
     reflexivity.
   Qed.
   

   Lemma sum_n_m_Series (f : nat -> R) (n m : nat) :
     (n <= m)%nat ->
     ex_series f ->
     sum_n_m f n m = Series (fun i => f (n + i)%nat) -
                     Series (fun i => f (S m + i)%nat).
   Proof.
     intros. 
     destruct (lt_dec 0 n).
     - apply sum_n_m_Series1; trivial; lia.
     - assert (n=0)%nat by lia.
       setoid_rewrite H1.
       assert (Hm : (0 < S m)%nat) by lia.
       generalize (Series_incr_n f _ Hm H0); intros.
       rewrite Series_ext with (b := f); [|now setoid_rewrite Nat.add_0_l].
       rewrite H2.
       unfold Rminus.
       rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
       replace (pred (S m)) with m by lia.
       now rewrite <- sum_n_Reals.
   Qed.

   Lemma sum_series_eps (f : nat -> R) :
     ex_series f ->
     forall (eps : posreal),
     exists (N : nat),
     forall (n k : nat),
       (n >= N)%nat ->
       Rabs (sum_n_m f n (n + k)%nat) < eps.
   Proof.
     intros.
     generalize (zerotails f H); intros.
     apply is_lim_seq_spec in H0.
     unfold is_lim_seq' in H0.
     assert (0 < eps) by apply cond_pos.
     assert (0 < eps/2) by lra.
     destruct (H0 (mkposreal _ H2)).
     exists (S x).
     intros.
     rewrite sum_n_m_Series; trivial; try lia.
     unfold Rminus.
     apply Rle_lt_trans with
         (r2 := (Rabs (Series (fun i : nat => f (n + i)%nat))) +
                (Rabs (- Series (fun i : nat => f (S (n + k) + i)%nat)) )).
     apply Rabs_triang.
     replace (pos eps) with ((mkposreal _ H2) + (mkposreal _ H2)); [|simpl; lra].
     apply Rplus_lt_compat.
     - specialize (H3 (n-1)%nat).
       cut_to H3; try lia.
       setoid_rewrite Rminus_0_r in H3.
       rewrite Series_ext with (b := (fun i : nat => f (n + i)%nat)) in H3; trivial.
       intros.
       f_equal; lia.
     - rewrite Rabs_Ropp.
       specialize (H3 (n + k)%nat).
       cut_to H3; try lia.
       setoid_rewrite Rminus_0_r in H3.
       rewrite Series_ext with (b := (fun i : nat => f (S (n + k) + i)%nat)) in H3; trivial.       
  Qed.

   (* cauchy convergence test *)
   Lemma Cauchy_convergence_test (f : nat -> R) :
       ex_series f <->
       forall (eps : posreal),
       exists (N : nat),
       forall (n p: nat),
         (n > N)%nat ->
         Rabs (sum_n_m f n (n+p)%nat) < eps.
  Proof.
    split; intros.
    - generalize (sum_series_eps f H eps); intros.
      destruct H0.
      exists (S x); intros.
      apply H0; lia.
    - Admitted.
         

   
  Lemma Rmax_list_map_seq_lt_gen (eps : R) {n0 n : nat} (X : nat -> R):
    (0 < n)%nat -> Rmax_list (map X (seq n0 n)) < eps <->
                   (forall k, (k < n)%nat -> X (n0 + k)%nat < eps).
  Proof.
    intros Hn. split.
    + intros Heps k Hk.
      rewrite Rmax_list_lt_iff in Heps; try (apply map_not_nil; now apply seq_not_nil).
      apply Heps.
      rewrite in_map_iff.
      exists (n0 + k)%nat; split; trivial.
      rewrite in_seq; lia.
    + intros Heps.
      rewrite Rmax_list_lt_iff; try (apply map_not_nil; now apply seq_not_nil).
      intros x Hx. rewrite in_map_iff in Hx.
      destruct Hx as [k [Hk1 Hk2]].
      rewrite <-Hk1.
      specialize (Heps (k-n0)%nat).
      apply in_seq in Hk2.
      replace (n0 + (k - n0))%nat with (k) in Heps; try lia.
      apply Heps; trivial; lia.
  Qed.


   Lemma Rmax_list_sum_series_eps (f : nat -> R) :
     ex_series f ->
     forall (eps : posreal),
     exists (NN : nat),
     forall (n N : nat),
       (N >= NN)%nat ->
       (n >= N)%nat ->
        Rmax_list
          (map
             (fun k : nat =>
                Rabs (sum_n_m f k n))
             (seq N (S (n - N)))) < eps. 
   Proof.
     intros.
     generalize (sum_series_eps _ H eps); intros.
     destruct H0.
     exists x.
     intros.
     apply Rmax_list_map_seq_lt_gen; try lia.
     intros.
     
     specialize (H0 (N + k)%nat (n - (N + k))%nat).
     replace ((N + k) + (n - (N + k)))%nat with (n) in H0; try lia.
     apply H0; lia.
   Qed.

 



   Lemma map_shiftn_seq (f : nat -> R) (n m : nat) :
     map f (seq n m) = map (fun n0 => f (n + n0)%nat) (seq 0 m).
   Proof.
     rewrite seq_shiftn_map.
     now rewrite map_map.
   Qed.

   Lemma Rmax_list_map_seq_mn (X : nat -> R) (n m : nat) :
     Rmax_list_map (seq n m) X = Rmax_list_map (seq 0 m) (fun k => X (n + k)%nat). 
   Proof.
     unfold Rmax_list_map.
     now rewrite map_shiftn_seq.
   Qed.

   Lemma map_shift1_seq (f : nat -> R) (n m : nat) :
     map f (seq (S n) m) = map (fun n0 => f (S n0)%nat) (seq n m).
   Proof.
     rewrite seq_shiftn_map.
     symmetry.
     rewrite seq_shiftn_map.
     do 2 rewrite map_map.
     apply map_ext.
     reflexivity.
   Qed.

   Lemma Rmax_list_map_seq_incr1 (X : nat -> R) (n m : nat) :
     Rmax_list (map X (seq (S n) m)) = Rmax_list (map (fun k => X (S k)) (seq n m)).
   Proof.
     now rewrite map_shift1_seq.
   Qed.

   Lemma Rmax_list_Sn (f : nat -> R) (n : nat) {m : nat} (hm : (0<m)%nat) :
     Rmax_list (map f (seq n (S m))) = Rmax (Rmax_list (map f (seq n m))) (f (n + m)%nat).
   Proof.
     rewrite seq_S. 
     rewrite Rmax_list_app.
     reflexivity.
     rewrite seq_shiftn_map.
     rewrite map_not_nil.
     now apply seq_not_nil.
   Qed. 
   
   (* to handle out of range limit *)
   Lemma Rmax_list_sum_series_eps2(f : nat -> R) :
     ex_series f ->
     forall (eps : posreal),
     exists (NN : nat),
     forall (n N : nat),
       (N >= NN)%nat ->
       (n > (S N))%nat ->
        Rmax_list
          (map
             (fun k : nat =>
                Rabs (sum_n_m f (S k) (n-1)%nat))
             (seq N (S ((n-1) - N)))) < eps.
   Proof.
     intros.
     generalize (sum_series_eps _ H eps); intros.
     destruct H0.
     exists x.
     intros.
     apply Rmax_list_map_seq_lt_gen; try lia.
     intros.
     specialize (H0 (S (N + k))%nat ((n-1) - (S (N + k)))%nat).
     destruct (lt_dec k (n - 1 - N)%nat).
     - replace (S (N + k) + (n-1 - (S (N + k))))%nat with (n-1)%nat in H0.
       + apply H0; lia.
       + lia.
     - assert (k = (n - 1 - N)%nat) by lia.
       assert ((S (N + k)) > (n - 1))%nat by lia.
       rewrite sum_n_m_zero; try lia.
       unfold zero; simpl.
       rewrite Rabs_R0.
       apply cond_pos.
   Qed.

          
  Lemma DS_lemma1 (a b c delta zeta : nat -> R)
        (b1pos : forall n, 0 <= b n) :
    (forall n, 0 <= a n) ->
    (forall n, 0 <= c n) ->
    (forall n, 0 <= zeta n) ->
    is_lim_seq a 0 ->
    ex_series b ->
    ex_series delta ->
    is_lim_seq (sum_n c) p_infty ->
    (exists (N0:nat),
      (forall n, (n>= N0)%nat -> 
               zeta (S n) <= Rmax (a n) ((1+b n)*zeta n + delta n - c n))) ->
    is_lim_seq zeta 0.
  Proof.
    intros.
    destruct H6 as [N0 ?].
    apply is_lim_seq_spec.
    unfold is_lim_seq'.
    intros.
    pose (B :=  part_prod (fun i : nat => {| pos := 1 + b i; cond_pos := pos1 (b i) (b1pos i) |})).
    assert (Bincr:forall m, B m <= B (S m)).
    {
      intros.
      subst B.
      unfold part_prod.
      rewrite part_prod_n_S; try lia.
      simpl.
      replace
        (part_prod_n
           (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (b1pos n0) |}) 0 m) with
          ((part_prod_n
              (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (b1pos n0) |}) 0 m)*1) at 1 by lra.
      apply Rmult_le_compat_l.
      + left; apply pos_part_prod_n.
      + generalize (b1pos (S m)); lra.
    }
    generalize (Fprod_B2 b b1pos H3); intros.
    destruct H7 as [BB ?].
    assert (forall m, B m <= BB).
    {
      intros.
      assert (Rbar_le (B m) BB).
      - eapply Rbar_le_trans.
        shelve.
        apply H7.
        Unshelve.
        subst B.
        apply Lim_seq_increasing_le.
        apply Bincr.
      - now simpl in H8.
    }
     assert (fin_LimB: is_finite (Lim_seq B)).
     { 
       apply bounded_is_finite with (a := 0) (b := BB); trivial.
       apply Lim_seq_pos.
       intros.
       left.
       apply pos_part_prod.
     }
    assert (ex_series (fun j => (delta j)/(B j))).
    {
      unfold Rdiv.
      setoid_rewrite Rmult_comm.
      apply Abel_descending_convergence; trivial.
      - intros.
        apply Rle_ge.
        apply Rinv_le_contravar; trivial.
        apply pos_part_prod_n.
      - exists (/ BB).
        intros.
        apply Rle_ge.
        apply Rinv_le_contravar; trivial.
        apply pos_part_prod_n.
    }
    assert (exists N2,
               forall NN, 
                 (NN >= N2)%nat ->
                 (Lim_seq B *
                  (Sup_seq (fun n0 : nat => a (n0 + NN)%nat))) <
                 (eps/2)).
    {
      apply is_lim_seq_spec in H2.
      unfold is_lim_seq' in H2.
      assert (0 < eps / ((2 * BB) + 1)).
      {
        apply Rdiv_lt_0_compat.
        - apply cond_pos.
        - assert (0 < BB).
          + apply Rlt_le_trans with (r2 := B 0%nat); trivial.
            apply pos_part_prod.
          + lra.
      }
      specialize (H2 (mkposreal _ H10)).
      destruct H2.
      exists x; intros.
      replace (eps/2) with (BB * (eps/(2*BB))).
      - apply Rle_lt_trans with
            (r2 := BB * Sup_seq (fun n0 : nat => a (n0 + NN)%nat)).
        + apply Rmult_le_compat_r.
          * generalize (sup_seq_pos (fun n0 : nat => a (n0 + NN)%nat)); intros.
            cut_to H12; trivial.
            destruct ( Sup_seq (fun n0 : nat => a (n0 + NN)%nat)); trivial.
            simpl; lra.
            simpl; lra.            
          * unfold B in fin_LimB.
            rewrite <- fin_LimB in H7.
            now simpl in H7.
        + apply Rmult_lt_compat_l.
          apply Rlt_le_trans with
              (r2 := (B 0%nat)); trivial.
          apply pos_part_prod.
          apply Rle_lt_trans with
              (r2 := eps / (2 * BB + 1)).
          * generalize (sup_le_bound  
                          (fun n0 : nat => a (n0 + NN)%nat)
                          (eps / (2 * BB + 1))); intros.
            destruct H12.
            cut_to H12.
            -- destruct ( Sup_seq (fun n0 : nat => a (n0 + NN)%nat)); trivial.
               simpl; lra.
               simpl; lra.
            -- intros.
               specialize (H2 (n + NN)%nat).
               cut_to H2; try lia.
               rewrite Rminus_0_r in H2.
               rewrite Rabs_right in H2.
               now left.
               apply Rle_ge, H.
          * unfold Rdiv.
            apply Rmult_lt_compat_l.
            -- apply cond_pos.
            -- apply Rinv_lt_contravar.
               ++ assert (0 < BB).
                  ** apply Rlt_le_trans with (r2 := B 0%nat); trivial.
                     apply pos_part_prod.
                  ** apply Rmult_lt_0_compat; lra.
               ++ lra.
      - field.
        apply Rgt_not_eq.
        apply Rlt_le_trans with
            (r2 := (B 0%nat)); trivial.
        apply pos_part_prod.
    }
        
    destruct H10 as [N2 ?].
    
    assert (exists N3,
               forall NN, 
                 (NN >= N3)%nat ->
                 forall n, 
                   (n > (S NN))%nat ->
                     (Lim_seq B *
                      Rmax_list
                        (map
                           (fun k : nat =>
                              Rabs (sum_n_m (fun j : nat => delta j / B j) (S k) (n-1)))
                           (seq NN (S (n-1 - NN))))) <
                     (eps/2)
           ).
    {
      generalize (Rmax_list_sum_series_eps2  (fun j : nat => delta j / B j) H9); intros.
       assert (0 < eps / ((2 * BB) + 1)).
      {
        apply Rdiv_lt_0_compat.
        - apply cond_pos.
        - assert (0 < BB).
          + apply Rlt_le_trans with (r2 := B 0%nat); trivial.
            apply pos_part_prod.
          + lra.
      }
      specialize (H11 (mkposreal _ H12)).
      destruct H11.
      exists x.
      intros.
      specialize (H11 n NN).
      cut_to H11; try lia.
      apply Rle_lt_trans with
          (r2 := BB * 
                 (Rmax_list
                      (map
                         (fun k : nat => Rabs (sum_n_m (fun j : nat => delta j / B j) 
                                                       (S k) (n - 1)))
                         (seq NN (S (n - 1 - NN)))))).
        + apply Rmult_le_compat_r.
          * apply Rmax_list_map_nonneg.
            intros.
            apply Rabs_pos.
          * unfold B in fin_LimB.
            rewrite <- fin_LimB in H7.
            now simpl in H7.
        + assert ( 0 < BB).
          {
            apply Rlt_le_trans with
                (r2 := B 0%nat); trivial.
            apply pos_part_prod.
          }
          apply Rlt_trans with
              (r2 := BB * (eps / (2 * BB + 1))).
          * apply Rmult_lt_compat_l; trivial.
          * field_simplify.
            rewrite Rmult_comm.
            unfold Rdiv.
            rewrite Rmult_assoc.
            apply Rmult_lt_compat_l.
            -- apply cond_pos.
            -- apply Rmult_lt_reg_l with (r := 2); try lra.
               replace (2 * / 2) with 1 by lra.
               rewrite <- Rmult_assoc.
               apply Rmult_lt_reg_r with (r := 2 * BB + 1); try lra.
               field_simplify; try lra.
            -- apply Rgt_not_eq; lra.
    }

    destruct H11 as [N3 ?].
    
    generalize (DS_1_part2 a b c delta zeta N0 (max (S N0) (max N2 N3)) b1pos); intros.
    cut_to H12; trivial; try lia.
    destruct H12 as [N1 ?].
    exists (S (S (max (max (S N0) (max N2 N3)) N1))); intros.
    specialize (H12 (n-1)%nat).
    cut_to H12; try lia.
    specialize (H10 (max (S N0) (max N2 N3))).
    specialize (H11 (max (S N0) (max N2 N3))).
    cut_to H10; try lia.
    cut_to H11; try lia.
    specialize (H11 n).
    cut_to H11; try lia.
    rewrite Rminus_0_r.
    rewrite Rabs_right; [|apply Rle_ge, (H1 n)].
    replace (S (n-1))%nat with n in H12 by lia.
    eapply Rle_lt_trans.
    apply H12.
    rewrite Rmult_plus_distr_l.
    replace (pos eps) with ((eps/2) + (eps/2)) by lra.
    apply Rplus_lt_compat.
    apply H10.
    apply H11.
  Qed.

   Lemma Paolo_div (a : nat -> R) :
    (forall n, 0 <= a n) ->
    ex_series a ->
    exists (b : nat -> R),
      (forall n, 0 < b n) /\
      is_lim_seq b 0 /\
      ex_series (fun n => a n / Rsqr (b n)).
    Proof.
      intros apos aconv.
      destruct (Paolo_final a apos).
      specialize (H aconv).
      destruct H as [? [? [? ?]]].
      exists (fun n => sqrt (/ (x n))).
      split.
      - intros.
        apply sqrt_lt_R0.
        now apply Rinv_0_lt_compat.
      - split.
        + replace (0) with (sqrt 0) by apply sqrt_0.
          apply is_lim_seq_continuous.
          apply continuity_pt_sqrt; lra.
          replace (Finite 0) with (Rbar_inv p_infty); [| now simpl].
          apply is_lim_seq_inv; trivial; discriminate.
        + apply ex_series_ext with
              (a0 := fun n => a n * x n); trivial.
          intros.
          unfold Rdiv.
          f_equal.
          rewrite Rsqr_sqrt.
          * rewrite Rinv_involutive; trivial.          
            now apply Rgt_not_eq, Rlt_gt.
          * left.
            now apply Rinv_0_lt_compat.
   Qed.

    Lemma DS_lemma1_stochastic (a b c delta zeta : nat -> Ts -> R)
          (b1pos : forall n x, 0 <= b n x) :
    (forall n x, 0 <= a n x) ->
    (forall n x, 0 <= c n x) ->
    (forall n x, 0 <= zeta n x) ->
    almost _ (fun x => is_lim_seq (fun n => a n x) 0) ->
    almost _ (fun x => ex_series (fun n => b n x)) ->
    almost _ (fun x => ex_series (fun n => delta n x)) ->
    almost _ (fun x => is_lim_seq (sum_n (fun n => c n x)) p_infty) ->
    almost _ (fun x =>
                (exists (N0:nat),
                    (forall n, 
                        (n>= N0)%nat -> 
                        (zeta (S n) x) <=
                         Rmax (a n x) ((1+ (b n x))*(zeta n x) + (delta n x) - (c n x))))) ->
    almost _ (fun x => (is_lim_seq (fun n => zeta n x) 0)).
  Proof.
    intros.
    revert H6; apply almost_impl.
    revert H5; apply almost_impl.
    revert H4; apply almost_impl.
    revert H3; apply almost_impl.
    revert H2; apply almost_impl.
    apply all_almost; 
    intros ?? ?? ??.
    apply DS_lemma1 with (a := fun n => a n x) 
                         (b := fun n => b n x) 
                         (c := fun n => c n x) 
                         (delta := fun n => delta n x); trivial.
  Qed.
    

     
      
  Lemma DS_Dvor_aa {a : nat -> R} {Y : nat -> Ts -> R}
        (isfe : forall n, IsFiniteExpectation prts (rvsqr (Y n))) :
    (forall n, 0 <= a n) ->
    is_lim_seq a 0 ->
    ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
    exists (aa : nat -> R),
      is_lim_seq aa 0 /\
      (forall n, 0 < aa n) /\
      (forall n, a n <= aa n) /\
      ex_series (fun n => FiniteExpectation prts (rvsqr (Y n)) / Rsqr (aa n)).
  Proof.
    intros.
    generalize (Paolo_div (fun n => FiniteExpectation prts (rvsqr (Y n)))); intros.
    cut_to H2; trivial.
    - destruct H2 as [? [? [? ?]]].
      exists (fun n => Rmax (a n) (x n)).
      split; try split; try split.
      + apply is_lim_seq_spec.
        apply is_lim_seq_spec in H0.
        apply is_lim_seq_spec in H3.
        unfold is_lim_seq' in *.
        intros.
        destruct (H0 eps).
        destruct (H3 eps).
        exists (max x0 x1).
        intros.
        specialize (H5 n); specialize (H6 n).
        cut_to H5; try lia.
        cut_to H6; try lia.
        rewrite Rminus_0_r in H5.
        rewrite Rminus_0_r in H6.
        rewrite Rminus_0_r.
        specialize (H n); specialize (H2 n).
        rewrite Rabs_right in *; try lra.
        * unfold Rmax; match_destr.
        * apply Rle_ge, Rmax_Rle; lra.
      + intros.
        apply Rlt_le_trans with (r2 := x n); trivial.
        apply Rmax_r.
      + intros.
        apply Rmax_l.
      + generalize (ex_series_le  (fun n : nat => FiniteExpectation prts (rvsqr (Y n)) / (Rmax (a n) (x n))²)
                                  (fun n : nat => FiniteExpectation prts (rvsqr (Y n)) / (x n)²)); intros.
        apply H5; trivial.
        intros.
        unfold norm; simpl.
        unfold abs; simpl.
        rewrite Rabs_right.
        * unfold Rdiv.
          apply Rmult_le_compat_l.
          -- apply FiniteExpectation_pos, nnfsqr.
          -- apply Rinv_le_contravar.
             ++ apply Rsqr_pos_lt.
                apply Rgt_not_eq.
                apply H2.
             ++ unfold Rmax; match_destr; try lra.
                assert (x n <= a n) by lra.
                apply Rsqr_le_abs_1.
                rewrite Rabs_right.
                ** rewrite Rabs_right; trivial.
                   now apply Rle_ge.
                ** apply Rle_ge; now left.                   
        * apply Rle_ge, Rdiv_le_0_compat.
          -- apply FiniteExpectation_pos, nnfsqr.
          -- apply Rsqr_pos_lt.
             apply Rgt_not_eq, Rlt_gt.
             apply Rlt_le_trans with (r2 := x n); trivial.
             apply Rmax_r.
    - intros.
      apply FiniteExpectation_pos.
      apply nnfsqr.
  Qed.

  Lemma DS_Dvor_aa_fun {a : nat -> Ts -> R} {Y : nat -> Ts -> R}
        (isfe : forall n, IsFiniteExpectation prts (rvsqr (Y n))) :
    (forall n omega , 0 <= a n omega) ->
    ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
    exists (aa : nat -> Ts -> R),
      (forall omega, is_lim_seq (fun n => a n omega) 0 ->
                     is_lim_seq (fun n => aa n omega) 0) /\
      (forall n omega, 0 < aa n omega) /\
      (forall n omega, a n omega <= aa n omega) /\
      forall omega,
        ex_series (fun n => FiniteExpectation prts (rvsqr (Y n)) / Rsqr (aa n omega)).
  Proof.
    intros.
    generalize (Paolo_div (fun n => FiniteExpectation prts (rvsqr (Y n)))); intros.
    cut_to H1; trivial.
    - destruct H1 as [? [? [? ?]]].
      exists (fun n omega => Rmax (a n omega) (x n)).
      split; try split; try split.
      + intros.
        apply is_lim_seq_spec.
        apply is_lim_seq_spec in H2.
        apply is_lim_seq_spec in H4.
        unfold is_lim_seq' in *.
        intros.
        destruct (H2 eps).
        destruct (H4 eps).
        exists (max x0 x1).
        intros.
        specialize (H5 n); specialize (H6 n).
        cut_to H5; try lia.
        cut_to H6; try lia.
        rewrite Rminus_0_r in H5.
        rewrite Rminus_0_r in H6.
        rewrite Rminus_0_r.
        specialize (H n); specialize (H1 n).
        rewrite Rabs_right in *; try lra.
        * unfold Rmax; match_destr.
        * apply Rle_ge, H.
        * apply Rle_ge, Rmax_Rle; lra.
      + intros.
        apply Rlt_le_trans with (r2 := x n); trivial.
        apply Rmax_r.
      + intros.
        apply Rmax_l.
      + intros.
generalize (ex_series_le  (fun n : nat => FiniteExpectation prts (rvsqr (Y n)) / (Rmax (a n omega) (x n))²)
                                  (fun n : nat => FiniteExpectation prts (rvsqr (Y n)) / (x n)²)); intros.
        apply H4; trivial.
        intros.
        unfold norm; simpl.
        unfold abs; simpl.
        rewrite Rabs_right.
        * unfold Rdiv.
          apply Rmult_le_compat_l.
          -- apply FiniteExpectation_pos, nnfsqr.
          -- apply Rinv_le_contravar.
             ++ apply Rsqr_pos_lt.
                apply Rgt_not_eq.
                apply H1.
             ++ unfold Rmax; match_destr; try lra.
                assert (x n <= a n omega) by lra.
                apply Rsqr_le_abs_1.
                rewrite Rabs_right.
                ** rewrite Rabs_right; trivial.
                   now apply Rle_ge.
                ** apply Rle_ge; now left.                   
        * apply Rle_ge, Rdiv_le_0_compat.
          -- apply FiniteExpectation_pos, nnfsqr.
          -- apply Rsqr_pos_lt.
             apply Rgt_not_eq, Rlt_gt.
             apply Rlt_le_trans with (r2 := x n); trivial.
             apply Rmax_r.
    - intros.
      apply FiniteExpectation_pos.
      apply nnfsqr.
  Qed.

  Lemma DS_Dvor_aa_stochastic {a : nat -> Ts -> R} {Y : nat -> Ts -> R}
        (isfe : forall n, IsFiniteExpectation prts (rvsqr (Y n))) :
    (forall n omega , 0 <= a n omega) ->
    almost _ (fun omega => is_lim_seq (fun n => a n omega) 0) ->
    ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
    exists (aa : nat -> Ts -> R),
      (almost _ (fun omega => is_lim_seq (fun n => aa n omega) 0)) /\
      (forall n omega, 0 < aa n omega) /\
      (forall n omega, a n omega <= aa n omega) /\
      forall omega, ex_series (fun n => FiniteExpectation prts (rvsqr (Y n)) / Rsqr (aa n omega)).
  Proof.
    intros.
    destruct (DS_Dvor_aa_fun isfe H H1) as [α [Hα1 [Hα0 [Hα2 Hα3]]]].
    exists α.
    split; try split; try split; trivial.
    - revert H0.
      apply almost_impl, all_almost; intros ??.
      now apply Hα1.
  Qed.

 Lemma DS_Dvor_11_12_Y (a : nat -> R) {Y : nat -> Ts -> R}
       (isfe : forall n, IsFiniteExpectation prts (rvsqr (Y n)))
       (rvy : forall n, RandomVariable _ borel_sa (Y n))
   :
   (forall n, 0 <= a n) ->
    is_lim_seq a 0 ->
    ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
    exists α : nat -> R,
      is_lim_seq α 0 /\
      almost _ (fun omega =>  exists N:nat, forall n, (N <= n)%nat -> rvabs (Y n) omega <= Rmax (α n) (a n)).
 Proof.
   intros Ha1 Ha2 HY.
   destruct (DS_Dvor_aa isfe Ha1 Ha2 HY) as [α [Hα1 [Hα0 [Hα2 Hα3]]]].
   exists α.
   assert (HEsa : forall n, sa_sigma (event_ge dom (rvabs (Y n)) (mkposreal _ (Hα0 n)))).
   {
     intros.
     apply sa_sigma_event_pre.
   }
   pose (frac := fun n => Rbar_div_pos (NonnegExpectation (rvsqr (Y n)))
                                    (mkposreal _ (rsqr_pos (mkposreal _ (Hα0 n))))).
   assert (isfin: forall n, is_finite (NonnegExpectation (rvsqr (Y n)))).
   {
     intros.
     now apply IsFiniteNonnegExpectation.
   }
   assert (Hfinu : forall n0, Rbar_le (frac n0) (FiniteExpectation prts (rvsqr (Y n0)) / (α n0)²)).
   {
     intros. unfold frac.
     rewrite <- (isfin n0).
     simpl.
     rewrite <- (isfin n0).
     simpl.
     unfold Rdiv.
     apply Rmult_le_compat_r.
     - left; apply Rinv_pos.
       apply Rlt_0_sqr.
       now apply Rgt_not_eq, Rlt_gt.
     - rewrite <- FiniteNonnegExpectation with (isfeX := (isfe n0)).
       now apply FiniteExpectation_le.
   }
   assert (Hfinb : forall n, Rbar_le 0 (frac n)).
   {
     intros. unfold frac.
     rewrite <- (isfin n).
     simpl.
     apply Rdiv_le_0_compat.
     generalize (NonnegExpectation_pos (rvsqr (Y n))).
     rewrite <- (isfin n); now simpl.
     apply Rlt_0_sqr.
     apply Rgt_not_eq.
     apply Hα0.
   }
   assert (Hisf : forall n, is_finite(frac n)) by (intros; eapply bounded_is_finite; auto).
   split; trivial.
   generalize (Borel_Cantelli prts _ (HEsa)); intros.
   cut_to H.
   + rewrite almost_alt_eq.
     unfold almost_alt. push_neg.
     simpl in H. eexists.
     split; [apply H|intros omega ?H].
     simpl. intros n. specialize (H0 n).
     destruct H0 as [n0 [Hn0 HZ]]. exists (n0-n)%nat.
     left. replace ((n0 - n + n)%nat) with n0 by lia.
     apply Rgt_lt in HZ. rewrite Rmax_Rlt in HZ.
     now destruct HZ.
   + simpl.
     eapply ex_series_nneg_bounded; eauto; intros.
     -- apply ps_pos.
     -- generalize(Chebyshev_ineq_div_mean0 _ (rvy n) ((mkposreal _ (Hα0 n)))); intros.
        eapply Rle_trans; eauto.
        unfold frac in Hisf. simpl in Hisf.
        rewrite <-(Hisf n) in H0. simpl in H0.
        apply H0.
        specialize (Hfinu n).
        rewrite <- Hisf in Hfinu.
        simpl in Hfinu.
        apply Hfinu.
 Qed.

 Lemma DS_Dvor_11_12_Y_stochastic (a : nat -> Ts -> R) {Y : nat -> Ts -> R}
       (isfe : forall n, IsFiniteExpectation prts (rvsqr (Y n)))
       (rvy : forall n, RandomVariable _ borel_sa (Y n))
   :
     (forall n omega, 0 <= a n omega) ->
      almost _ (fun omega => is_lim_seq (fun n => a n omega) 0) ->
     ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
     exists α : nat -> Ts -> R,
       (almost _ (fun omega => is_lim_seq (fun n => a n omega) 0)) /\
       almost _ (fun omega =>  exists N:nat, forall n, (N <= n)%nat -> rvabs (Y n) omega <= Rmax (α n omega) (a n omega)).
 Proof.
   intros Ha1 Ha2 HY.
   destruct (DS_Dvor_aa_stochastic isfe Ha1 Ha2 HY) as [α [Hα1 [Hα0 [Hα2 Hα3]]]].
   exists α.
   split; trivial.
   Admitted.

(*
   assert (HEsa : forall n, sa_sigma (event_ge dom (rvabs (Y n)) (mkposreal _ (Hα0 n)))).
   {
     intros.
     apply sa_sigma_event_pre.
   }

   pose (frac := fun n omega => Rbar_div_pos (NonnegExpectation (rvsqr (Y n)))
                                             (mkposreal _ (rsqr_pos (mkposreal _ (Hα0 n omega))))).
   assert (isfin: forall n, is_finite (NonnegExpectation (rvsqr (Y n)))).
   {
     intros.
     now apply IsFiniteNonnegExpectation.
   }
   assert (Hfinu : forall n0, Rbar_le (frac n0) (FiniteExpectation prts (rvsqr (Y n0)) / (α n0)²)).
   {
     intros. unfold frac.
     rewrite <- (isfin n0).
     simpl.
     rewrite <- (isfin n0).
     simpl.
     unfold Rdiv.
     apply Rmult_le_compat_r.
     - left; apply Rinv_pos.
       apply Rlt_0_sqr.
       now apply Rgt_not_eq, Rlt_gt.
     - rewrite <- FiniteNonnegExpectation with (isfeX := (isfe n0)).
       now apply FiniteExpectation_le.
   }
   assert (Hfinb : forall n, Rbar_le 0 (frac n)).
   {
     intros. unfold frac.
     rewrite <- (isfin n).
     simpl.
     apply Rdiv_le_0_compat.
     generalize (NonnegExpectation_pos (rvsqr (Y n))).
     rewrite <- (isfin n); now simpl.
     apply Rlt_0_sqr.
     apply Rgt_not_eq.
     apply Hα0.
   }
   assert (Hisf : forall n, is_finite(frac n)) by (intros; eapply bounded_is_finite; auto).
   split; trivial.
   generalize (Borel_Cantelli prts _ (HEsa)); intros.
   cut_to H.
   + rewrite almost_alt_eq.
     unfold almost_alt. push_neg.
     simpl in H. eexists.
     split; [apply H|intros omega ?H].
     simpl. intros n. specialize (H0 n).
     destruct H0 as [n0 [Hn0 HZ]]. exists (n0-n)%nat.
     left. replace ((n0 - n + n)%nat) with n0 by lia.
     apply Rgt_lt in HZ. rewrite Rmax_Rlt in HZ.
     now destruct HZ.
   + simpl.
     eapply ex_series_nneg_bounded; eauto; intros.
     -- apply ps_pos.
     -- generalize(Chebyshev_ineq_div_mean0 _ (rvy n) ((mkposreal _ (Hα0 n)))); intros.
        eapply Rle_trans; eauto.
        unfold frac in Hisf. simpl in Hisf.
        rewrite <-(Hisf n) in H0. simpl in H0.
        apply H0.
        specialize (Hfinu n).
        rewrite <- Hisf in Hfinu.
        simpl in Hfinu.
        apply Hfinu.
 Qed.
*)

 Lemma DS_Dvor_ash_6_2_1 (X Y T : nat -> Ts -> R)
       {F : nat -> SigmaAlgebra Ts}
       (isfilt : IsFiltration F)
       (filt_sub : forall n, sa_sub (F n) dom)
       {adaptX : IsAdapted borel_sa X F}
       {adaptT : IsAdapted borel_sa T F}       
       {rvX : forall (n:nat), RandomVariable dom borel_sa (X n)}
       {rvY : forall (n:nat), RandomVariable dom borel_sa (Y n)}
       {rvT : forall (n:nat), RandomVariable dom borel_sa (T n)}       
       {frf : forall (n:nat), FiniteRangeFunction (Y (n))}
       (HC : forall n, 
           almostR2 _ eq
                    (ConditionalExpectation _ (filt_sub (S n)) (Y (S n)))
                    (const 0))  :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
   ex_series (fun n => SimpleExpectation (rvsqr (Y n))) ->
   let Z := fun n => rvmult (Y n) (rvsign (T n)) in
   almost _ (fun (x : Ts) => ex_series (fun n => Z n x)).
 Proof.
   intros.
   assert (adaptY : IsAdapted borel_sa Y (fun n => F (S n))).
   {
     unfold IsAdapted; intros.
     specialize (H n).
     assert (rv_eq (Y n) (rvminus (X (S n)) (T n))).
     {
       rewrite H.
       intro x.
       unfold rvminus, rvplus, rvopp, rvscale; lra.
    }
     rewrite H1.
     apply rvminus_rv.
     - apply adaptX.
     - apply (RandomVariable_sa_sub (isfilt n)).
       apply adaptT.
  }
   assert (adaptZ : IsAdapted borel_sa Z (fun n => F (S n))).
   {
     unfold IsAdapted; intros.
     unfold Z.
     apply rvmult_rv; trivial.
     apply rvsign_rv; trivial.
     apply (RandomVariable_sa_sub (isfilt n)).
     apply adaptT.
   }
   assert (rvZ : forall n, RandomVariable dom borel_sa (Z n)).
   {
     intros.
     unfold Z.
     apply rvmult_rv; trivial.
     apply rvsign_rv; trivial.
   }
   assert (isfilt1 : IsFiltration (fun n => F (S n))).
   {
     unfold IsFiltration; intros.
     apply isfilt.
   }
   assert (frfz : forall (n:nat), FiniteRangeFunction (Z (n))).
   {
     intros.
     unfold Z.
     apply frfmult; trivial.
     apply frfsign; trivial.
  }
   apply Ash_6_2_1_filter with 
       (filt_sub0 := fun n => filt_sub (S n))
       (rv := rvZ)
       (frf0 := frfz); trivial.
   - intros.
     assert (isfef : IsFiniteExpectation prts (Y (S n))) by now apply IsFiniteExpectation_simple.
     assert (rvs: RandomVariable (F (S n)) borel_sa (rvsign (T (S n)))).
     {
       apply rvsign_rv.
       apply adaptT.
     }
     assert (isfe2 : IsFiniteExpectation prts (rvmult (Y (S n)) (rvsign (T (S n))))).
     {
       apply IsFiniteExpectation_simple; trivial.
       - apply rvmult_rv; trivial.
         now apply (RandomVariable_sa_sub (filt_sub (S n))).
       - typeclasses eauto.
     }
     generalize (Condexp_factor_out prts (filt_sub (S n))(Y (S n)) (rvsign (T (S n)))); intros.
     apply almost_prob_space_sa_sub_lift in H1.
     revert H1.
     apply almost_impl.
     specialize (HC n).
     revert HC.
     apply almost_impl, all_almost; intros ??.
     unfold impl; intros.
     unfold Z.
     rewrite H2.
     unfold Rbar_rvmult.
     rewrite H1.
     unfold const.
     now rewrite Rbar_mult_0_r.
   -  assert (Z2leY2: forall n0, rv_le (rvsqr (Z n0)) (rvsqr (Y n0))).
      {
     intros n0 x.
     unfold Z, rvsqr, rvmult, rvsign.
     replace (Rsqr (Y n0 x)) with ((Rsqr (Y n0 x)) * 1) by lra.
     rewrite Rsqr_mult.
     apply Rmult_le_compat_l.
     - apply Rle_0_sqr.
     - destruct (Rlt_dec 0 (T n0 x)).
       + rewrite sign_eq_1; unfold Rsqr; lra.
       + destruct (Rlt_dec (T n0 x) 0).
         * rewrite sign_eq_m1; unfold Rsqr; lra.
         * assert (T n0 x = 0) by lra.
           rewrite H1.
           rewrite sign_0; unfold Rsqr; lra.
      }
      apply ex_series_nneg_bounded with (g := fun n => SimpleExpectation (rvsqr (Y n))); trivial. 
      + intros.
        apply SimpleExpectation_nneg.
        apply nnfsqr.
      + intros.
        now apply SimpleExpectation_le.
  Qed.
        
 Lemma sign_sum {a b c : R} :
   Rabs a <= c -> Rabs b > c -> sign (b + a) = sign b.
 Proof.
   intros.
   destruct (Rle_dec b 0).
   + destruct r.
     -- rewrite (sign_eq_m1 b H1).
        apply sign_eq_m1.
        rewrite (Rabs_left _ H1) in H0.
        apply Rle_lt_trans with (r2 := b + Rabs a);
          [apply Rplus_le_compat_l; apply Rle_abs|].
        lra.
     -- subst. rewrite sign_0.
        rewrite Rabs_R0 in H0.
        rewrite Rplus_0_l.
        assert (Rabs a < 0) by lra.
        generalize (Rabs_pos a); intros.
        exfalso. apply (Rlt_irrefl 0); lra.
   + push_neg_in n.
     rewrite (sign_eq_1 b); trivial.
     apply sign_eq_1.
     rewrite Rabs_pos_eq in H0; try lra.
     destruct (Rle_dec a 0).
     -- rewrite (Rabs_left1 _ r) in H.
        lra.
     -- push_neg_in n0.
        lra.
 Qed.

 Lemma Rabs_sign (a : R) : Rabs a = (sign a)*a.
 Proof.
   split_Rabs.
   + rewrite sign_eq_m1; trivial; lra.
   + destruct Hge.
     -- rewrite sign_eq_1; trivial; lra.
     -- subst; lra.
 Qed.

 Lemma is_lim_seq_max (f g : nat -> R) (l : Rbar) :
   is_lim_seq f l ->
   is_lim_seq g l ->
   is_lim_seq (fun n => Rmax (f n) (g n)) l.
 Proof.
   intros.
   apply is_lim_seq_spec.
   apply is_lim_seq_spec in H.
   apply is_lim_seq_spec in H0.
   unfold is_lim_seq' in *; intros.
   destruct l; intros.
   - destruct (H eps); destruct (H0 eps).
     exists (max x x0); intros.
     specialize (H1 n); specialize (H2 n).
     cut_to H1; try lia.
     cut_to H2; try lia.
     unfold Rmax; match_destr.
   - destruct (H M); destruct (H0 M).
     exists (max x x0); intros.
     specialize (H1 n); specialize (H2 n).
     cut_to H1; try lia.
     cut_to H2; try lia.
     unfold Rmax; match_destr.
   - destruct (H M); destruct (H0 M).
     exists (max x x0); intros.
     specialize (H1 n); specialize (H2 n).
     cut_to H1; try lia.
     cut_to H2; try lia.
     unfold Rmax; match_destr.
 Qed.

 Theorem Dvoretzky_DS
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}       
        {alpha beta gamma : nat -> R}
        (hpos1 : forall n, 0 <= alpha n)
        (hpos2 : forall n, 0 <= beta n )(hpos3 : forall n, 0 <= gamma n)
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        (svy : forall n, FiniteRangeFunction (Y n)) 
        (rvx : forall n, RandomVariable dom borel_sa (X n)) 
        (svx: forall n, FiniteRangeFunction (X n))
        (rvt : forall n, RandomVariable _ borel_sa (fun r:Ts => T n r))
        (fey : forall n : nat, IsFiniteExpectation prts (rvsqr (Y n)))
        (svt: forall n, FiniteRangeFunction (fun r:Ts => T n r)) :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, (rvabs (T n) omega) <= Rmax (alpha n) ((1+beta n)*(rvabs (X n) omega) - gamma n)) ->
  ex_series (fun n => FiniteExpectation _ (rvsqr (Y n))) ->
  is_lim_seq alpha 0 ->
  ex_series beta ->
  is_lim_seq (sum_n gamma) p_infty ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   destruct (DS_Dvor_11_12_Y alpha fey) as [α [α0 [E [HE Hα]]]]; trivial.
   pose (Z := fun n => rvmult (Y n) (rvsign (T n))).
   pose (A := fun n => Rmax (α n) (alpha n)).
   assert (ZleY: forall n0, rv_le (rvabs (Z n0)) (rvabs (Y n0))).
   {
     intros n0 x.
     unfold Z, rvabs, rvmult, rvsign.
     replace (Rabs (Y n0 x)) with ((Rabs (Y n0 x)) * 1) by lra.
     rewrite Rabs_mult.
     apply Rmult_le_compat_l.
     - apply Rabs_pos.
     - destruct (Rlt_dec 0 (T n0 x)).
       + rewrite sign_eq_1; trivial. rewrite Rabs_R1; lra.
       + destruct (Rlt_dec (T n0 x) 0).
         * rewrite sign_eq_m1; trivial. rewrite Rabs_m1; lra.
         * assert (T n0 x = 0) by lra.
           rewrite H6.
           rewrite sign_0; try (rewrite Rabs_R0); lra.
   }
   assert (Haux : almost _ (fun omega => exists N, forall n, (N <= n)%nat -> rvabs (X (S n)) omega <=
                                           Rmax (2* A n)
                                                (((1+beta n)*(rvabs (X n) omega) + Z n omega - gamma n)))).
   {
     exists E. split; trivial.
     intros w Hw.
     destruct (Hα w Hw) as [N HN]. clear Hα.
     exists N; intros. rv_unfold. rewrite H.
     specialize (HN n H6). clear H6. clear Hw.
     rewrite Rmax_Rle.
     destruct (Rle_dec (Rabs(T n w)) (A n)).
     --  left. replace (2*A n) with (A n + A n) by lra.
        eapply Rle_trans; [apply Rle_abs|]. rewrite Rabs_Rabsolu.
        eapply Rle_trans;[apply Rabs_triang|].
        apply Rplus_le_compat; trivial.
     -- right.
        apply Rnot_le_gt in n0.
        eapply Rle_trans;[apply Rle_abs|].
        apply Rle_trans with (r2 := Rabs(T n w) + Z n w).
        ** rewrite Rabs_Rabsolu. rewrite Rabs_sign.
           rewrite (sign_sum HN n0). rewrite Rmult_plus_distr_l.
           rewrite <-Rabs_sign. right. unfold Z; lra.
        ** unfold Rminus. rewrite Rplus_assoc.
           rewrite (Rplus_comm (Z n w) (- gamma n)).
           rewrite <-Rplus_assoc.
           specialize (H1 n w).
           rewrite Rmax_Rle in H1.
           destruct H1.
           *** exfalso.
               apply Rgt_lt in n0.
               unfold A in n0. rewrite Rmax_Rlt in n0.
               destruct n0 as [_ ?H]; lra.
           *** apply Rplus_le_compat_r.
               eapply Rle_trans; [apply H1| now right].
   }
   generalize (DS_Dvor_ash_6_2_1 X Y T isfilt filt_sub); intros.
   cut_to H6; trivial.
   simpl in H6.
   revert H6; apply almost_impl.
   revert Haux; apply almost_impl.
   apply all_almost; intros ??.
   intro zser.
   assert (is_lim_seq (fun n => Rabs (X n x)) 0).
   - apply (DS_lemma1 (fun n => 2 * A n) beta gamma (fun n => Z n x) 
           (fun n => Rabs (X n x))); trivial.
     + intros; unfold A.
       apply Rmult_le_pos; try lra.
       apply Rle_trans with (r2 := alpha n).
       * apply hpos1.
       * apply Rmax_r.
     + intros; apply Rabs_pos.
     + replace (Finite 0) with (Rbar_mult 2 0) by apply Rbar_mult_0_r.
       apply is_lim_seq_scal_l.
       unfold A.
       now apply is_lim_seq_max.
   - apply is_lim_seq_spec in H7.
     apply is_lim_seq_spec.
     unfold is_lim_seq' in *; intros.
     specialize (H7 eps).
     destruct H7.
     exists x0; intros.
     specialize (H7 n H8).
     rewrite Rminus_0_r.
     now rewrite Rminus_0_r, Rabs_Rabsolu in H7.
   - apply ex_series_ext with (a := fun n => FiniteExpectation prts (rvsqr (Y n))); trivial.
     intros.
     now rewrite <- FiniteExpectation_simple with (isfe := (fey n)).
 Qed.


Theorem Dvoretzky_DS_extended
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}       
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )(hpos3 : forall n x, 0 <= gamma n x)
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        (svy : forall n, FiniteRangeFunction (Y n)) 
        (rvx : forall n, RandomVariable dom borel_sa (X n)) 
        (svx: forall n, FiniteRangeFunction (X n))
        (rvt : forall n, RandomVariable _ borel_sa (fun r:Ts => T n r))
        (fey : forall n : nat, IsFiniteExpectation prts (rvsqr (Y n)))
        (svt: forall n, FiniteRangeFunction (fun r:Ts => T n r)) :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, (rvabs (T n) omega) <= Rmax (alpha n omega) ((1+beta n omega)*(rvabs (X n) omega) - gamma n omega)) ->
  ex_series (fun n => FiniteExpectation _ (rvsqr (Y n))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_series (fun n => beta n omega))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   Admitted.

End Derman_Sacks.
