Require Import Reals Sums Lra Lia.
Require Import Coquelicot.Coquelicot.
Require Import LibUtils.
Require Import Expectation ConditionalExpectation.
Require Import infprod.

Require Import List Permutation.
Require Import Morphisms EquivDec Program.

Require Import Utils.
Import ListNotations.
Require Import Classical.

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

  Lemma Abel_descending_convergence (a b : nat -> R) :
    ex_series b ->
    (forall n, a n >= a (S n)) ->
    (exists M, forall n, a n >= M) ->
    ex_series (fun n => a n * b n).
  Proof.
  Admitted.

  Lemma Rmax_list_plus_r (f g : nat -> R) (r : R) (n h : nat) :
    (forall (c:nat), 
        (c <= h)%nat ->
        f (n + c)%nat + r = g (n + c)%nat) ->
    Rmax_list (map f (seq n (S h))) + r = Rmax_list (map g (seq n (S h))).
  Proof.
    Admitted.
                     

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

  Lemma DS_1 (a b c delta zeta : nat -> R) :
    (forall n, 0 <= a n) ->
    (forall n, 0 <= b n) ->
    (forall n, 0 <= c n) ->
    (forall n, 0 <= delta n) ->
    is_lim_seq a 0 ->
    ex_series b ->
    ex_series delta ->
    is_lim_seq (sum_n c) p_infty ->
    (exists (N : nat), 
        forall n, (n>= N)%nat -> 
                  zeta (S n) <= Rmax (a n) ((1+b n)*zeta n + delta n - c n)) ->
    is_lim_seq zeta 0.
  Proof.
    intros.
    pose (B := part_prod (fun i => mkposreal _ (pos1 (b i) (H0 i)))).
    destruct H7 as [N ?].
    assert (forall (n:nat),
               (n > N)%nat ->
               zeta (S n) <= Rmax (((B n)/(B (N-1)%nat))*(zeta N) +
                                   (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) N n)
                                  (Rmax_list
                                     (map (fun k => 
                                             (B n)/(B k)*(a k)  +
                                             (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) (S k) n) 
                                          (seq N (S (n-N))%nat)))) by admit.
    generalize (Fprod_B2 b H0 H4); intros.
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
           (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (H0 n0) |}) 0 m) with
          ((part_prod_n
              (fun n0 : nat => {| pos := 1 + b n0; cond_pos := pos1 (b n0) (H0 n0) |}) 0 m)*1) at 1 by lra.
      apply Rmult_le_compat_l.
      + left; apply pos_part_prod_n.
      + generalize (H0 (S m)); lra.
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
        
    assert (exists (N1:nat),
               forall (n:nat), 
                 (n > N1)%nat ->
                 (((B n)/(B (N-1)%nat))*(zeta N) +
                  (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) N n) < 0) by admit.
    apply is_lim_seq_le_le_loc with
        (u := const 0) (w := (fun n =>
                               (Rmax_list
                                     (map (fun k => 
                                             (B n)/(B k)*(a k)  +
                                             (B n) * sum_n_m (fun j => (delta j - c j)/(B j)) (S k) n) 
                                          (seq N (S (n-N))%nat))))).   
    
    
    Admitted.


  

End Derman_Sacks.    
  
