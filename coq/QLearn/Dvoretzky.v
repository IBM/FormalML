Require Import Reals Sums Lra Lia.
Require Import Coquelicot.Coquelicot.
Require Import LibUtils.
Require Import Expectation ConditionalExpectation RandomVariableLpR.
Require Import infprod.
Require Import PushNeg.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.

Require Import ProductSpace.
Require Import Utils.
Import ListNotations.
Require Import Classical.
Require Import slln.

Require Import DVector.
Set Bullet Behavior "Strict Subproofs".

Require Import LM.hilbert Classical IndefiniteDescription.

Ltac rv_unfold'_in_star := unfold
                    const,
                  id,
                  compose,
                  EventIndicator,
                  rvsqr,
                  rvpow,
                  rvpower,
                  rvsign,
                  rvabs,
                  rvmax, 
                  rvmin,
                  rvchoice,
                  bvmin_choice,
                  bvmax_choice,
                  pos_fun_part,
                  neg_fun_part,
                  rvopp,
                  rvscale,
                  rvplus,
                  rvmult in *; repeat rewrite rvminus_unfold in *.

Tactic Notation "rv_unfold'" "in" "*" := rv_unfold'_in_star.

Ltac rv_unfold'_goal := unfold
                    const,
                  id,
                  compose,
                  EventIndicator,
                  rvsqr,
                  rvpow,
                  rvpower,
                  rvsign,
                  rvabs,
                  rvmax, 
                  rvmin,
                  rvchoice,
                  bvmin_choice,
                  bvmax_choice,
                  pos_fun_part,
                  neg_fun_part,
                  rvopp,
                  rvscale,
                  rvplus,
                  rvmult; repeat rewrite rvminus_unfold.

Tactic Notation "rv_unfold'" := rv_unfold'_goal.

Ltac rv_unfold'_in_hyp H := unfold
                    const,
                  id,
                  compose,
                  EventIndicator,
                  rvsqr,
                  rvpow,
                  rvpower,
                  rvsign,
                  rvabs,
                  rvmax, 
                  rvmin,
                  rvchoice,
                  bvmin_choice,
                  bvmax_choice,
                  pos_fun_part,
                  neg_fun_part,
                  rvopp,
                  rvscale,
                  rvplus,
                  rvmult in H; repeat rewrite rvminus_unfold in H.

Tactic Notation "rv_unfold'" "in" hyp(H) := rv_unfold'_in_hyp H.

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
      (svy2 : IsFiniteExpectation prts (rvsqr (Y n))) 
      (rvx : RandomVariable dom borel_sa (X n)) 
      {isfexm:IsFiniteExpectation prts (rvsqr (rvminus (X n) (const theta)) )}
      (rvt : RandomVariable borel_sa borel_sa (fun r:R => T n r))        
      (svt: IsFiniteExpectation prts (fun r:Ts => T n (X n r))) 
      (svt2: IsFiniteExpectation prts (rvsqr (fun r:Ts => T n (X n r)))) 
      (rvx2 : RandomVariable dom borel_sa (X (S n)))
      {isfex2m:IsFiniteExpectation prts (rvsqr (rvminus (X (S n)) (const theta)) )}
      {isfety:IsFiniteExpectation prts (((fun r : Ts => T n (X n r)) .* Y n))} :
  (forall (n:nat), F n >= 0) ->
  (forall (n:nat) (r:R), Rle (Rabs ((T n r) - theta)) (F n * Rabs (r-theta))) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r => T n (X n r)) (Y n))) ->
  almostR2 prts eq (ConditionalExpectation_rv (X n) (Y n)) (const 0) ->
  Rle (FiniteExpectation prts (rvsqr (rvminus (X (S n)) (const theta)) ))
      ((Rsqr (F n)) * FiniteExpectation prts (rvsqr (rvminus (X n) (const (theta))))
       + FiniteExpectation prts (rvsqr (Y n))).
  Proof.
    intros.
    specialize (H1 n).
    assert (rv_eq (rvminus (X (S n)) (const theta)) 
                  (rvminus (rvplus (fun r => T n (X n r)) (Y n)) (const theta))).
    {
      now rewrite H1.
    } 
    rewrite (FiniteExpectation_ext_alt _ _ _ (rvsqr_proper _ _ H3)).
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
   rewrite (FiniteExpectation_ext_alt _ _ _ eqq1).
   assert (rvtx: RandomVariable dom borel_sa (fun r:Ts => T n (X n r)))
     by now apply (compose_rv (dom2 := borel_sa)).
   erewrite (FiniteExpectation_plus' _ _ _ ).
   erewrite (FiniteExpectation_plus' _ _ _ ).
   erewrite (FiniteExpectation_scale' _ _ _).
   rewrite <- Rplus_assoc.
   apply Rplus_le_compat_r.
   {
     Unshelve.
     - shelve.
     - rewrite rvsqr_minus_foil.
       apply IsFiniteExpectation_plus; try typeclasses eauto.
       apply IsFiniteExpectation_minus; try typeclasses eauto.
       apply IsFiniteExpectation_scale.
       rewrite rvmult_comm.
       assert (eqq2:rv_eq (const theta .* (fun r : Ts => T n (X n r)))
                          (rvscale theta (fun r : Ts => T n (X n r)))) by reflexivity.
       rewrite eqq2.
       now apply IsFiniteExpectation_scale.
     - apply IsFiniteExpectation_plus; try typeclasses eauto.
       apply IsFiniteExpectation_scale.
       rewrite rvmult_comm.
       rewrite rvmult_rvminus_distr.
       apply IsFiniteExpectation_minus; try typeclasses eauto.
       + now rewrite rvmult_comm.
       + rewrite rvmult_comm.
         assert (eqq2:rv_eq (const theta .* Y n)
                            (rvscale theta (Y n))) by reflexivity.
         rewrite eqq2.
         apply IsFiniteExpectation_scale.
         now apply IsFiniteExpectation_rvsqr_lower.
     - apply IsFiniteExpectation_scale.
       rewrite rvmult_comm.
       rewrite rvmult_rvminus_distr.
       apply IsFiniteExpectation_minus; try typeclasses eauto.
       + now rewrite rvmult_comm.
       + rewrite rvmult_comm.
         assert (eqq2:rv_eq (const theta .* Y n)
                            (rvscale theta (Y n))) by reflexivity.
         rewrite eqq2.
         apply IsFiniteExpectation_scale.
         now apply IsFiniteExpectation_rvsqr_lower.
     - rewrite rvmult_comm.
       rewrite rvmult_rvminus_distr.
       apply IsFiniteExpectation_minus; try typeclasses eauto.
       + now rewrite rvmult_comm.
       + rewrite rvmult_comm.
         assert (eqq2:rv_eq (const theta .* Y n)
                            (rvscale theta (Y n))) by reflexivity.
         rewrite eqq2.
         apply IsFiniteExpectation_scale.
         now apply IsFiniteExpectation_rvsqr_lower.
   }
   Unshelve.
   replace (FiniteExpectation prts (((fun r : Ts => T n (X n r)) .- const theta) .* Y n)) with 0.
   shelve.
   {
     symmetry.
     assert (isfef: IsFiniteExpectation prts (Y n)) by now apply IsFiniteExpectation_rvsqr_lower.
     eapply FiniteCondexp_factor_out_zero_swapped
       with (sub := (pullback_rv_sub dom borel_sa (X n) rvx)) (rvf := rvy); trivial.
     - apply rvminus_rv.
       + apply (compose_rv (dom2 := borel_sa)); trivial.
         apply pullback_rv.
       + typeclasses eauto.
     - 
       revert H2.
       apply almost_impl; apply all_almost; intros ??.
       unfold ConditionalExpectation_rv in H2.
       rewrite (FiniteCondexp_eq _ _ _) in H2.
       invcs H2.
       reflexivity.
   }
   Unshelve.
   specialize (H n).
   field_simplify.
   
   rewrite <- (FiniteExpectation_scale _ (Rsqr (F n))).
   apply FiniteExpectation_le; try typeclasses eauto.
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

  Lemma Dvoretzky_8_F_le_1 (theta:R) 
        (X Y : nat -> Ts -> R)
        (T : nat -> R -> R)
        (F : nat -> posreal)
        (rvy : forall n, RandomVariable dom borel_sa (Y n)) 
        (rvx : forall n, RandomVariable dom borel_sa (X n)) 
        (rvt : forall n, RandomVariable borel_sa borel_sa (fun r:R => T n r))
        (svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))) 
        {isfexm: forall n, IsFiniteExpectation prts (rvsqr (rvminus (X n) (const theta)) )}
        (svt: forall n, IsFiniteExpectation prts (fun r:Ts => T n (X n r)))
        {isfety:forall n, IsFiniteExpectation prts (((fun r : Ts => T n (X n r)) .* Y n))}
        (svt2: forall n, IsFiniteExpectation prts (rvsqr (fun r:Ts => T n (X n r)))) :
  (forall (n:nat), F n >= 0) ->
  (forall (n:nat) (r:R), Rle (Rabs ((T n r) - theta)) (F n * Rabs (r-theta))) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r => T n (X n r)) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation_rv (X n) (Y n)) (fun x : Ts => const 0 x)) ->
  (forall n, F n <= 1) ->
  ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
  is_lim_seq (part_prod F) 0 ->
  is_lim_seq (fun n => FiniteExpectation prts (rvsqr (rvminus (X n) (const theta)))) 0.
 Proof.
  intros.
  apply (Dvoretzky4B_Vpos F (fun n => FiniteExpectation prts (rvsqr (Y n)))); trivial.
  - intros.
    apply FiniteExpectation_sq_nneg.
  - intros.
    apply FiniteExpectation_sq_nneg.
  - intros.
    unfold pos_sq_fun, pos_sq; simpl.
    replace ((F n) * (F n)) with (Rsqr (F n)) by now simpl.
    generalize (Dvoretzky_rel n theta X Y T F (rvy n) _ (rvx n) 
                              (rvt n) (svt n) _ (rvx (S n))); intros rel.
    now apply rel.
 Qed.

End Dvoretzky.

Section Derman_Sacks.

 Context 
   {Ts : Type}
   {dom: SigmaAlgebra Ts}
   {prts: ProbSpace dom}.

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

 Lemma DS_Dvor_11_12_Y_fun (a : nat -> Ts -> R) {Y : nat -> Ts -> R}
       (isfe : forall n, IsFiniteExpectation prts (rvsqr (Y n)))
       (rvy : forall n, RandomVariable _ borel_sa (Y n))
   :
     (forall n omega, 0 <= a n omega) ->
     ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
     exists α : nat-> R,
       is_lim_seq (fun n => α n) 0 /\
       almost _ (fun omega =>  exists N:nat, forall n, (N <= n)%nat -> rvabs (Y n) omega <= Rmax (α n) (a n omega)).
 Proof.
   intros Ha1 HY.
   generalize (no_worst_converge_div (fun n => FiniteExpectation prts (rvsqr (Y n)))); intros.
   assert (forall n, 0 <= FiniteExpectation prts (rvsqr (Y n))).
   {
     intros.
     apply FiniteExpectation_pos.
     apply nnfsqr.
   }
   cut_to H; trivial.
   destruct H as [α [Hα0 [Hα1 Hα2]]].
   exists α.
   split; trivial.
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
   generalize (Borel_Cantelli prts (fun n => (event_ge dom (rvabs (Y n))(α n)))); intros.
   cut_to H.
   + rewrite almost_alt_eq.
     unfold almost_alt. push_neg.
     simpl in H. eexists.
     split; [apply H|intros omega ?H].
     simpl. intros n. specialize (H1 n).
     destruct H1 as [n0 [Hn0 HZ]]. exists (n0-n)%nat.
     left. replace ((n0 - n + n)%nat) with n0 by lia.
     apply Rgt_lt in HZ. rewrite Rmax_Rlt in HZ.
     now destruct HZ.
   + eapply ex_series_nneg_bounded; eauto; intros.
     -- apply ps_pos.
     -- generalize(Chebyshev_ineq_div_mean0 _ (rvy n) ((mkposreal _ (Hα0 n)))); intros.
        eapply Rle_trans; eauto.
        unfold frac in Hisf. simpl in Hisf.
        rewrite <-(Hisf n) in H1. simpl in H1.
        apply H1.
        specialize (Hfinu n).
        rewrite <- Hisf in Hfinu.
        simpl in Hfinu.
        apply Hfinu.
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
   intros.
   apply (DS_Dvor_11_12_Y_fun (fun (n:nat) (omega:Ts) => a n)) with (isfe0 := isfe); trivial.
 Qed.
 
 Global Instance IsFiniteExpectation_mult_sign (X : Ts -> R) f
        {rvX:RandomVariable dom borel_sa X}
        {rvf:RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts X} :
   IsFiniteExpectation prts (rvmult X (rvsign f)).
 Proof.
   apply IsFiniteExpectation_abs_id.
   - typeclasses eauto.
   - apply IsFiniteExpectation_abs in isfe; trivial.
     apply (IsFiniteExpectation_bounded _ (const 0) _ (rvabs X)).
     + intros ?; rv_unfold.
       apply Rabs_pos.
     + intros ?.
       rv_unfold.
       rewrite Rabs_mult.
       rewrite <- (Rmult_1_r (Rabs (X a))) at 2.
       apply Rmult_le_compat; try apply Rabs_pos; try reflexivity.
       unfold sign.
       repeat match_destr; unfold Rabs; match_destr; lra.
 Qed.

 Lemma DS_Dvor_ash_6_2_1 (X Y T : nat -> Ts -> R)
       {F : nat -> SigmaAlgebra Ts}
       (isfilt : IsFiltration F)
       (filt_sub : forall n, sa_sub (F n) dom)
       {adaptX : IsAdapted borel_sa X F}
       {adaptT : IsAdapted borel_sa T F}       
       {rvX : forall (n:nat), RandomVariable dom borel_sa (X n)}
       {rvY : forall (n:nat), RandomVariable dom borel_sa (Y n)}
       {rvT : forall (n:nat), RandomVariable dom borel_sa (T n)}
       (svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n)))
       (HC : forall n, 
           almostR2 _ eq
                    (ConditionalExpectation _ (filt_sub (S n)) (Y (S n)))
                    (const 0))  :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
   ex_series (fun n => FiniteExpectation prts (rvsqr (Y n))) ->
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
   assert (isfesqrZ : forall k : nat, IsFiniteExpectation prts (rvsqr (Z k))).
   {
     intros.
     unfold Z.
     apply IsFiniteExpectation_proper with
         (x := rvmult (rvmult (Y k) (rvsign (T k))) (rvmult (Y k) (rvsign (T k)))).
     - intros ?.
       unfold rvmult, rvsign, rvsqr.
       now unfold Rsqr.
       
     - rewrite <- rvmult_assoc.
       apply IsFiniteExpectation_mult_sign; try typeclasses eauto.
       rewrite rvmult_assoc.
       rewrite (rvmult_comm (rvsign (T k))).
       rewrite <- rvmult_assoc.
       apply IsFiniteExpectation_mult_sign; try typeclasses eauto.
   } 
   apply Ash_6_2_1_filter with 
       (filt_sub0 := fun n => filt_sub (S n))
       (rv := rvZ)
       (isfesqr:=isfesqrZ) ; trivial.
   - intros.
     assert (isfef : IsFiniteExpectation prts (Y (S n))) by (intros; now apply IsFiniteExpectation_rvsqr_lower).

     assert (rvs: RandomVariable (F (S n)) borel_sa (rvsign (T (S n)))).
     {
       apply rvsign_rv.
       apply adaptT.
     }
     assert (isfe2 : IsFiniteExpectation prts (rvmult (Y (S n)) (rvsign (T (S n)))))
       by typeclasses eauto.
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
      apply ex_series_nneg_bounded with (g := fun n => FiniteExpectation prts (rvsqr (Y n))); trivial. 
      + intros.
        apply FiniteExpectation_pos.
        apply nnfsqr.
      + intros.
        now apply FiniteExpectation_le.
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
        (hpos2 : forall n, 0 <= beta n )
        (hpos3 : forall n, 0 <= gamma n)
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        (svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n)))
   :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, (rvabs (T n) omega) <= Rmax (alpha n) ((1+beta n)*(rvabs (X n) omega) - gamma n)) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  is_lim_seq alpha 0 ->
  ex_finite_lim_seq (sum_n beta) ->
  is_lim_seq (sum_n gamma) p_infty ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   rewrite ex_finite_lim_series in H2.
   rewrite ex_finite_lim_series in H4.   
   assert (rvt:forall n : nat, RandomVariable dom borel_sa (T n)).
   {
     intros.
     generalize (adaptT n).
     apply RandomVariable_proper_le; try reflexivity.
     apply filt_sub.
   } 

   assert (rvx:forall n : nat, RandomVariable dom borel_sa (X n)).
   {
     intros.
     generalize (adaptX n).
     apply RandomVariable_proper_le; try reflexivity.
     apply filt_sub.
   } 

   assert (svy : forall n, IsFiniteExpectation prts (Y n)).
   {
     intros.
     apply (IsLp_Finite prts 2); trivial.
     - lra.
     - red.
       rewrite rvpower2.
       + now rewrite rvsqr_abs.
       + apply nnfabs.
   } 

   destruct (DS_Dvor_11_12_Y alpha svy2) as [α [α0 [E [HE Hα]]]]; trivial.
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
           rewrite (sign_sum_alt HN n0). rewrite Rmult_plus_distr_l.
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
   specialize (H6 svy2).
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
 Qed.

 Theorem Dvoretzky_DS_extended_almost
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}       
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n)) 
(*        (hpos3 : forall n x, 0 <=  gamma n x)         *)
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n, almostR2 prts Rle (rvabs (T n)) 
                      (rvmax (alpha n) 
                             (rvminus
                                (rvmult 
                                   (rvplus (const 1) (beta n))
                                   (rvabs (X n))) 
                                 (gamma n)))) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega)))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   rewrite ex_finite_lim_series in H2.
   setoid_rewrite ex_finite_lim_series in H4.   
   assert (rvt:forall n : nat, RandomVariable dom borel_sa (T n)).
   {
     intros.
     generalize (adaptT n).
     apply RandomVariable_proper_le; try reflexivity.
     apply filt_sub.
   } 

   assert (rvx:forall n : nat, RandomVariable dom borel_sa (X n)).
   {
     intros.
     generalize (adaptX n).
     apply RandomVariable_proper_le; try reflexivity.
     apply filt_sub.
   } 

   assert (svy : forall n, IsFiniteExpectation prts (Y n)).
   {
     intros.
     apply (IsLp_Finite prts 2); trivial.
     - lra.
     - red.
       rewrite rvpower2.
       + now rewrite rvsqr_abs.
       + apply nnfabs.
   } 

   destruct (DS_Dvor_11_12_Y_fun alpha svy2) as [α [α0 [E [HE Hα]]]]; trivial.

   pose (Z := fun n => rvmult (Y n) (rvsign (T n))).
   pose (A := fun n omega => Rmax (α n) (alpha n omega)).
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
                                           Rmax (2* A n omega)
                                                (((1+beta n omega)*(rvabs (X n) omega) + Z n omega - gamma n omega)))).
   {
     apply almost_forall in H1.
     destruct H1 as [E' [HE' H1]].
     exists (event_inter E E').
     split; [now rewrite ps_inter_l1 | ].
     intros w Hw.
     generalize (event_inter_sub_l E E' w Hw); intros Hw'.
     generalize (event_inter_sub_r E E' w Hw); intros H1'.           
     destruct (Hα w Hw') as [N HN]. clear Hα.
     exists N; intros. rv_unfold. rewrite H.
     specialize (HN n H6). clear H6. clear Hw' Hw.
     rewrite Rmax_Rle.
     destruct (Rle_dec (Rabs(T n w)) (A n w)).
     --  left. replace (2*A n w) with (A n w + A n w) by lra.
        eapply Rle_trans; [apply Rle_abs|]. rewrite Rabs_Rabsolu.
        eapply Rle_trans;[apply Rabs_triang|].
        apply Rplus_le_compat; trivial.
     -- right.
        apply Rnot_le_gt in n0.
        eapply Rle_trans;[apply Rle_abs|].
        apply Rle_trans with (r2 := Rabs(T n w) + Z n w).
        ** rewrite Rabs_Rabsolu. rewrite Rabs_sign.
           rewrite (sign_sum_alt HN n0). rewrite Rmult_plus_distr_l.
           rewrite <-Rabs_sign. right. unfold Z; lra.
        ** unfold Rminus. rewrite Rplus_assoc.
           rewrite (Rplus_comm (Z n w) (- gamma n w)).
           rewrite <-Rplus_assoc.
           specialize (H1 w H1' n).
           rewrite Rmax_Rle in H1.
           destruct H1.
           *** exfalso.
               apply Rgt_lt in n0.
               unfold A in n0. rewrite Rmax_Rlt in n0.
               destruct n0 as [_ ?H]; lra.
           *** apply Rplus_le_compat_r.
               eapply Rle_trans; [apply H1| lra].
   }
   generalize (DS_Dvor_ash_6_2_1 X Y T isfilt filt_sub); intros.
   specialize (H6 svy2).
   cut_to H6; trivial.

   simpl in H6.
   revert H6; apply almost_impl.
   revert Haux; apply almost_impl.
   revert H3; apply almost_impl.
   revert H4; apply almost_impl.
   revert H5; apply almost_impl.
   apply almost_forall in hpos3.
   revert hpos3; apply almost_impl.
   apply all_almost; unfold impl; intros.
   assert (is_lim_seq (fun n => Rabs (X n x)) 0).
   - apply (DS_lemma1 (fun n => 2 * A n x) (fun n => beta n x) 
                      (fun n => gamma n x) (fun n => Z n x) 
           (fun n => Rabs (X n x))); trivial.
     + intros; unfold A.
       apply Rmult_le_pos; try lra.
       apply Rle_trans with (r2 := alpha n x).
       * apply hpos1.
       * apply Rmax_r.
     + intros; apply Rabs_pos.
     + replace (Finite 0) with (Rbar_mult 2 0) by apply Rbar_mult_0_r.
       apply is_lim_seq_scal_l.
       unfold A.
       apply is_lim_seq_max; trivial.
   - apply is_lim_seq_spec in H9.
     apply is_lim_seq_spec.
     unfold is_lim_seq' in *; intros.
     specialize (H9 eps).
     destruct H9. 
     exists x0; intros.
     specialize (H9 n H10).
     rewrite Rminus_0_r.
     now rewrite Rminus_0_r, Rabs_Rabsolu in H9.
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
        (hpos2 : forall n x, 0 <= beta n x )
        (hpos3 : forall n x, 0 <=  gamma n x)   
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, (rvabs (T n) omega) <= Rmax (alpha n omega) ((1+beta n omega)*(rvabs (X n) omega) - gamma n omega)) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega)))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   assert (hpos3' : forall n, almostR2 prts Rle (const 0) (gamma n)).
   {
     intros.
     now apply all_almost.
   }
   apply (Dvoretzky_DS_extended_almost X Y T isfilt filt_sub hpos1 hpos2 hpos3' rvy); trivial.
   intros; apply all_almost; intros.
   now rv_unfold' in *.
 Qed.

 Theorem Dvoretzky_DS_theta (theta : R)
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}       
        {alpha beta gamma : nat -> R}
        (hpos1 : forall n, 0 <= alpha n)
        (hpos2 : forall n, 0 <= beta n )
        (hpos3 : forall n, 0 <= gamma n)
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        (svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n)))
   :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, (Rabs (T n omega - theta)) <= Rmax (alpha n) ((1+beta n)*(Rabs (X n omega - theta)) - gamma n)) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  is_lim_seq alpha 0 ->
  ex_finite_lim_seq (sum_n beta) ->
  is_lim_seq (sum_n gamma) p_infty ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) theta).
 Proof.
   intros.
   pose (X' := fun n => rvminus (X n) (const theta)).
   pose (T' := fun n => rvminus (T n) (const theta)).
   assert (adaptX' : IsAdapted borel_sa X' F).
   {
     unfold IsAdapted, X'; intros.
     apply rvminus_rv; trivial.
     typeclasses eauto.
  }
   assert (adaptT' : IsAdapted borel_sa T' F).
   {
     unfold IsAdapted, T'; intros.
     apply rvminus_rv; trivial.
     typeclasses eauto.
  }
   generalize (Dvoretzky_DS X' Y T' isfilt filt_sub hpos1 hpos2 hpos3 _ _); intros.
   cut_to H6; trivial.
   - revert H6.
     apply almost_impl, all_almost; intros ??.
     unfold X' in H6.
     unfold rvminus, const, rvplus, rvopp, rvscale in H6.
     apply is_lim_seq_ext with
         (u := fun n => (X n x + -1 * theta) + theta).
     + intros; lra.
     + apply is_lim_seq_plus with (l1 := 0) (l2 := theta); trivial.
       * apply is_lim_seq_const.
       * unfold is_Rbar_plus; simpl.
         now rewrite Rplus_0_l.
   - intros n x.
     unfold X', T'.
     rv_unfold.
     rewrite H; lra.
   - intros.
     unfold T', X', rvabs.
     now do 2 rewrite rvminus_unfold.
 Qed.
 
 Theorem Dvoretzky_DS_extended_theta_almost (theta : R)
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}       
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
(*        (hpos3 : forall n x, 0 <= gamma n x) *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n)) 
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
(*
  (forall n omega, Rabs (T n omega - theta) <= Rmax (alpha n omega) ((1+beta n omega)*(Rabs (X n omega - theta)) - gamma n omega)) ->
*)
  (forall n, almostR2 prts Rle (rvabs (rvminus (T n) (const theta)) )
                      (rvmax (alpha n) 
                             (rvminus
                                (rvmult 
                                   (rvplus (const 1) (beta n))
                                   (rvabs (rvminus (X n) (const theta)))) 
                                 (gamma n)))) ->

  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega)))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) theta).
Proof.
  intros.
   pose (X' := fun n => rvminus (X n) (const theta)).
   pose (T' := fun n => rvminus (T n) (const theta)).
   assert (adaptX' : IsAdapted borel_sa X' F).
   {
     unfold IsAdapted, X'; intros.
     apply rvminus_rv; trivial.
     typeclasses eauto.
  }
   assert (adaptT' : IsAdapted borel_sa T' F).
   {
     unfold IsAdapted, T'; intros.
     apply rvminus_rv; trivial.
     typeclasses eauto.
  }
   generalize (Dvoretzky_DS_extended_almost X' Y T' isfilt filt_sub hpos1 hpos2 hpos3 rvy); intros.
   cut_to H6; trivial.
  - revert H6; apply almost_impl.
    apply almost_forall in H1.
    revert H1.
     apply almost_impl, all_almost; intros ???.
     unfold X' in H6.
     unfold rvminus, const, rvplus, rvopp, rvscale in H6.
     apply is_lim_seq_ext with
         (u := fun n => (X n x + -1 * theta) + theta).
     + intros; lra.
     + apply is_lim_seq_plus with (l1 := 0) (l2 := theta); trivial.
       * apply is_lim_seq_const.
       * unfold is_Rbar_plus; simpl.
         now rewrite Rplus_0_l.
   - intros n x.
     unfold X', T'.
     rv_unfold.
     rewrite H; lra.
  Qed.
   
 
 Theorem Dvoretzky_DS_extended_theta (theta : R)
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}       
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
        (hpos3 : forall n x, 0 <= gamma n x) 
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, Rabs (T n omega - theta) <= Rmax (alpha n omega) ((1+beta n omega)*(Rabs (X n omega - theta)) - gamma n omega)) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega)))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) theta).
 Proof.
   intros.
   assert (hpos3' : forall n, almostR2 prts Rle (const 0) (gamma n)).
   {
     intros.
     now apply all_almost.
   }
   apply (Dvoretzky_DS_extended_theta_almost theta X Y T isfilt filt_sub hpos1 hpos2 hpos3' rvy); trivial.
   intros.
   apply all_almost.
   intros.
   specialize (H1 n x).
   now rv_unfold'.
 Qed.

Theorem Dvoretzky_DS_scale_prop
        (X : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {alpha beta gamma : nat -> R}
        (hpos1 : forall n , 0 <= alpha n)
        (hpos2 : forall n , 0 <= beta n )
        (hpos3 : forall n , 0 <= gamma n) :
  (forall n omega, Rabs (T n omega) <= Rmax (alpha n) ((1+beta n - gamma n)*(Rabs (X n omega)))) ->
  is_lim_seq alpha 0 ->
  ex_series beta ->
  is_lim_seq (sum_n gamma) p_infty ->
  exists (alpha2 gamma2 : nat -> R),
    (forall n, 0 <= alpha2 n) /\
    (forall n, 0 <= gamma2 n) /\
    is_lim_seq alpha2 0 /\
    is_lim_seq (sum_n gamma2) p_infty /\
    forall n omega, Rabs (T n omega) <= Rmax (alpha2 n) ((1+beta n)*(Rabs (X n omega)) - gamma2 n).
 Proof.
   intros.
   destruct (no_best_diverge gamma hpos3 H2) as [rho [? ?]].
   pose (alpha2 := fun n => Rmax (alpha n) ((1 + beta n) * rho n)).
   pose (gamma2 := fun n => (rho n) *(gamma n)).
   exists alpha2; exists gamma2.
   split; try split; try split; try split.
   - intros.
     unfold alpha2.
     eapply Rle_trans.
     apply (hpos1 n).
     apply Rmax_l.
   - intros.
     unfold gamma2.
     apply Rmult_le_pos; trivial.
     left; apply cond_pos.
   - unfold alpha2.
     apply is_lim_seq_max; trivial.
     apply is_lim_seq_ext with (u := fun n => rho n + (beta n) * (rho n)).
     + intros; lra.
     + replace (Finite 0) with (Rbar_plus 0 0) by apply Rbar_plus_0_r.
       apply is_lim_seq_plus'; trivial.
       replace (Finite 0) with (Rbar_mult 0 0) by apply Rbar_mult_0_r.
       apply is_lim_seq_mult'; trivial.
       now apply ex_series_lim_0.
   - apply H4.
   - intros.
     eapply Rle_trans.
     apply H.
     unfold alpha2, gamma2.
     apply Rmax_case.
     + apply Rle_trans with (r2 := Rmax (alpha n) ((1 + beta n) * rho n)); apply Rmax_l.
     + destruct (Rle_dec (rho n) (Rabs (X n omega))).
       * apply Rle_trans with (r2 :=  ((1 + beta n) * Rabs (X n omega) - rho n * gamma n)); try apply Rmax_r.
         replace ( (1 + beta n - gamma n) * Rabs (X n omega)) with
             ((1 + beta n) * Rabs (X n omega) - (gamma n) * Rabs (X n omega)) by lra.
         apply Rplus_le_compat_l.
         apply Ropp_le_contravar.
         rewrite Rmult_comm.
         apply Rmult_le_compat_l; trivial.
       * assert (rho n > Rabs (X n omega)) by lra.
         apply Rle_trans with (r2 := (Rmax (alpha n) ((1 + beta n) * rho n)) ); try apply Rmax_l.
         apply Rle_trans with (r2 := ((1 + beta n) * rho n)); try apply Rmax_r.
         apply Rle_trans with (r2 :=  (1 + beta n) * Rabs (X n omega)).
         -- apply Rmult_le_compat_r; try apply Rabs_pos.
            specialize (hpos3 n); lra.
         -- apply Rmult_le_compat_l; try lra.
            specialize (hpos2 n); lra.
 Qed.


  Lemma no_best_diverge_fun (gamma : nat -> Ts -> R) :
   (forall n omega, 0 <= gamma n omega) -> 
   (forall omega, is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
   exists (rho : nat -> Ts -> posreal),
   forall omega,
     is_lim_seq (fun n => rho n omega)  0 /\ 
     is_lim_seq (sum_n (fun n => rho n omega * gamma n omega)) p_infty.
  Proof.
    intros gpos glim.
    generalize (fun omega => no_best_diverge (fun n => gamma n omega)
                                    (fun n => gpos n omega)
                                    (glim omega)); intros.
    apply ClassicalChoice.choice in H.
    destruct H as [f ?].
    exists (fun n omega => f omega n).
    apply H.
  Qed.
  
  Lemma no_best_diverge_stochastic (gamma : nat -> Ts -> R) :
   (* (forall n omega, 0 <= gamma n omega) -> *)
   (forall n, almostR2 prts Rle (const 0) (gamma n)) ->
   almost _ (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
   exists (rho : nat -> Ts -> posreal),
     almost _ (fun omega => is_lim_seq (fun n => rho n omega)  0) /\ 
     almost _ (fun omega => is_lim_seq (sum_n (fun n => rho n omega * gamma n omega)) p_infty).
  Proof.
    intros gpos glim.
    apply almost_forall in gpos.
    destruct glim as [p [pone pH]].
    destruct gpos as [p' [pone' gpos']].
    destruct (no_best_diverge_fun
                  (fun n ts => if classic_dec (event_inter p p') ts then
                              gamma n ts
                            else 1))
      as [rho HH].
    - intros; match_destr; try lra.
      apply gpos'.
      generalize (event_inter_sub_r p p' omega); intros.
      tauto.
    - intros; match_destr.
      + apply pH.
        generalize (event_inter_sub_l p p' omega); intros.
        tauto.
      + generalize is_lim_seq_INR; intros HH.
        apply is_lim_seq_incr_1 in HH.
        revert HH.
        apply is_lim_seq_proper; trivial; intros ?.
        rewrite sum_n_const; lra.
    - exists rho; split.
      + exists p; split; trivial; intros.
        now destruct (HH x) as [HH1 _].
      + exists (event_inter p p'); split.
        * now rewrite ps_inter_r1.
        * intros.
          destruct (HH x) as [_ HH2].
          match_destr_in HH2; tauto.
  Qed.

 Theorem Dvoretzky_DS_scale_prop_stochastic
        (X : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n omega , 0 <= alpha n omega)
        (hpos2 : forall n omega, 0 <= beta n omega)
(*        (hpos3 : forall n omega, 0 <= gamma n omega)  *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n)) :

(*
  (forall n omega, Rabs (T n omega) <= Rmax (alpha n omega) ((1+beta n omega - gamma n omega)*(Rabs (X n omega)))) ->
*)
   (forall n, almostR2 prts Rle (rvabs (T n)) 
                       (rvmax (alpha n) 
                              (rvmult 
                                 (rvminus
                                    (rvplus (const 1) (beta n))
                                    (gamma n))
                                 (rvabs (X n))))) ->
  almost _ (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost _ (fun omega =>  ex_series (fun n => beta n omega)) ->
  almost _ (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  exists (alpha2 gamma2 : nat -> Ts -> R),
    (forall n omega, 0 <= alpha2 n omega) /\
    (forall n, almostR2 prts Rle (const 0) (gamma2 n)) /\
    almost _ (fun omega => is_lim_seq (fun n => alpha2 n omega) 0) /\
    almost _ (fun omega => is_lim_seq (sum_n (fun n => gamma2 n omega)) p_infty) /\
    (forall n, almostR2 prts Rle (rvabs (T n)) 
                       (rvmax (alpha2 n) 
                              (rvminus
                                 (rvmult 
                                    (rvplus (const 1) (beta n))
                                    (rvabs (X n))) 
                                 (gamma2 n)))).
 Proof.
   intros.
   destruct (no_best_diverge_stochastic gamma hpos3 H2) as [rho [? ?]].
   pose (alpha2 := fun n omega => Rmax (alpha n omega) ((1 + beta n omega) * rho n omega)).
   pose (gamma2 := fun n omega => (rho n omega) *(gamma n omega)).
   exists alpha2; exists gamma2.
   split; try split; try split; try split.
   - intros.
     unfold alpha2.
     eapply Rle_trans.
     apply (hpos1 n).
     apply Rmax_l.
   - intros.
     specialize (hpos3 n).
     revert hpos3.
     apply almost_impl, all_almost.
     unfold impl, const; intros.
     unfold gamma2.
     apply Rmult_le_pos; trivial.
     left; apply cond_pos.
   - revert H0; apply almost_impl.
     revert H1; apply almost_impl.
     revert H3.
     apply almost_impl, all_almost.
     intros ??; unfold impl; intros.
     unfold alpha2.
     apply is_lim_seq_max; trivial.
     apply is_lim_seq_ext with (u := fun n => rho n x + (beta n x) * (rho n x)).
     + intros; lra.
     + replace (Finite 0) with (Rbar_plus 0 0) by apply Rbar_plus_0_r.
       apply is_lim_seq_plus'; trivial.
       replace (Finite 0) with (Rbar_mult 0 0) by apply Rbar_mult_0_r.
       apply is_lim_seq_mult'; trivial.
       now apply ex_series_lim_0.
   - apply H4.
   - intros.
     specialize (hpos3 n).
     revert hpos3; apply almost_impl.
     specialize (H n).
     revert H; apply almost_impl.
     apply all_almost; intros omega ??.
     unfold const in H5.
     eapply Rle_trans.
     apply H.
     unfold alpha2, gamma2.
     rv_unfold.
     apply Rmax_case.
     + apply Rle_trans with (r2 := Rmax (alpha n omega) ((1 + beta n omega) * rho n omega)); apply Rmax_l.
     + destruct (Rle_dec (rho n omega) (Rabs (X n omega))).
       * apply Rle_trans with (r2 :=  ((1 + beta n omega) * Rabs (X n omega) + (-1 * (rho n omega * gamma n omega)))); try apply Rmax_r.
         rewrite Rmult_plus_distr_r.
         unfold Rminus.
         apply Rplus_le_compat_l.
         ring_simplify.
         apply Rge_le, Rmult_le_ge_compat_neg_l; trivial.
         lra.
       * assert (rho n omega > Rabs (X n omega)) by lra.
         apply Rle_trans with (r2 := (Rmax (alpha n omega) ((1 + beta n omega) * rho n omega)) ); try apply Rmax_l.
         apply Rle_trans with (r2 := ((1 + beta n omega) * rho n omega)); try apply Rmax_r.
         apply Rle_trans with (r2 :=  (1 + beta n omega) * Rabs (X n omega)).
         -- apply Rmult_le_compat_r; try apply Rabs_pos; lra.
         -- apply Rmult_le_compat_l; try lra.
            specialize (hpos2 n omega); lra.
  Qed.

 Let DS_X (X0:Ts->R) (T Y:nat->Ts->R) (n:nat) :=
       match n with
       | 0%nat => X0
       | S m => (rvplus (T m) (Y m))
       end.

 Corollary Dvoretzky_DS_extended_simpl
           (X0:Ts->R) 
           (Y : nat -> Ts -> R)
           (T : nat -> Ts -> R)
           {F : nat -> SigmaAlgebra Ts}
           (isfilt : IsFiltration F)
           (filt_sub : forall n, sa_sub (F n) dom)
           {adaptX : IsAdapted borel_sa (DS_X X0 T Y) F}
           {adaptT : IsAdapted borel_sa T F}       
           {alpha beta gamma : nat -> Ts -> R}
           (hpos1 : forall n x, 0 <= alpha n x)
           (hpos2 : forall n x, 0 <= beta n x )
(*           (hpos3 : forall n x, 0 <= gamma n x) *)
           (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n)) 
           (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
(*  (forall n omega, (rvabs (T n) omega) <= Rmax (alpha n omega) ((1+beta n omega)*(rvabs (DS_X X0 T Y n) omega) - gamma n omega)) ->
*)
  
  (forall n, almostR2 prts Rle (rvabs (T n)) 
                      (rvmax (alpha n) 
                             (rvminus
                                (rvmult 
                                   (rvplus (const 1) (beta n))
                                   (rvabs (DS_X  X0 T Y n))) 
                                 (gamma n)))) ->

  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega))) ->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => (DS_X X0 T Y) n omega) 0).
 Proof.
   intros.
   eapply (Dvoretzky_DS_extended_almost (DS_X X0 T Y) Y T isfilt filt_sub hpos1 hpos2 hpos3 rvy); simpl; trivial
   ; reflexivity.
 Qed.
 
 Corollary Dvoretzky_DS_extended_vector_almost
        (X Y : nat -> Ts -> R)
        (T : forall (n:nat), vector R (S n) -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa (fun n ts => T n ((vector_create 0 (S n) (fun m _ _ => X m ts))) ts) F}
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
(*        (hpos3 : forall n x, 0 <= gamma n x) *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n))

         (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (fun ts => T n (vector_create 0 (S n) (fun m _ _ => X m ts)) ts) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
(*
  (forall n v omega, (rvabs (T n v) omega) <= Rmax (alpha n omega) ((1+beta n omega)*(rvabs (X n) omega) - gamma n omega)) ->
*)
  (forall n, almostR2 prts Rle (rvabs 
                                  (fun ts => T n (vector_create 0 (S n) (fun m _ _ => X m ts)) ts ))
                      (rvmax (alpha n) 
                             (rvminus
                                (rvmult 
                                   (rvplus (const 1) (beta n))
                                   (rvabs (X n))) 
                                 (gamma n)))) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega))) ->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   eapply (Dvoretzky_DS_extended_almost
            X Y
            (fun n ts => T n (vector_create 0 (S n) (fun m _ _ => X m ts)) ts)
            isfilt filt_sub
            hpos1 hpos2 hpos3
          ); trivial.
  Qed.

 Corollary Dvoretzky_DS_extended1
        (X Y : nat -> Ts -> R)
        (T : nat -> R -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa (fun n ts => T n (X n ts) ts) F}
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
(*        (hpos3 : forall n x, 0 <= gamma n x)  *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n))
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (fun ts => T n (X n ts) ts) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
(*  (forall n v omega, (rvabs (T n v) omega) <= Rmax (alpha n omega) ((1+beta n omega)*(rvabs (X n) omega) - gamma n omega)) -> *)
 (forall n, almostR2 prts Rle (rvabs 
                                  (fun ts => T n (X n ts) ts) )
                      (rvmax (alpha n) 
                             (rvminus
                                (rvmult 
                                   (rvplus (const 1) (beta n))
                                   (rvabs (X n)))
                                 (gamma n)))) ->

  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega))) ->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   eapply (Dvoretzky_DS_extended_almost
            X Y
            (fun n ts => T n (X n ts) ts)
            isfilt filt_sub
            hpos1 hpos2 hpos3
          ); trivial.
 Qed.
 
 Fixpoint DS_X1 (X0:Ts->R) (T:nat->(R*Ts)->R) (Y:nat->Ts->R) (n:nat) : Ts -> R :=
   match n with
   | 0%nat => X0
   | S m => (rvplus (fun ts => T m ((DS_X1 X0 T Y m ts), ts)) (Y m))
   end.

 Corollary Dvoretzky_DS_extended_simple1
           (X0:Ts->R) 
        (Y : nat -> Ts -> R)
        (T : nat -> (R * Ts) -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa (DS_X1 X0 T Y) F}
        {rvT: IsAdapted borel_sa T (fun n => product_sa borel_sa (F n))}
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
(*        (hpos3 : forall n x, 0 <= gamma n x) *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n))
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n, almostR2 prts Rle (rvabs 
                                  (fun ts => T n ((DS_X1 X0 T Y n ts), ts) ))
                      (rvmax (alpha n) 
                             (rvminus
                                (rvmult 
                                   (rvplus (const 1) (beta n))
                                   (rvabs (DS_X1 X0 T Y n)))
                                 (gamma n)))) ->

(*  (forall n omega, (Rabs (T n (DS_X1 X0 T Y n omega, omega))) <= Rmax (alpha n omega) ((1+beta n omega)*(rvabs ((DS_X1 X0 T Y n)) omega) - gamma n omega)) ->
*)
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega))) ->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => (DS_X1 X0 T Y n omega)) 0).
 Proof.
   intros.
   eapply (Dvoretzky_DS_extended_almost
                 (DS_X1 X0 T Y) Y
                 (fun n ts => T n ((DS_X1 X0 T Y n ts),ts))
                 isfilt filt_sub
                 hpos1 hpos2 hpos3

          ); trivial.
   - reflexivity.
     Unshelve.
     intros n.
     cut (RandomVariable (F n) borel_sa (fun ts : Ts =>  (fun '(x, ts) => T n (x,ts)) ((DS_X1 X0 T Y n ts), ts))).
     {
       apply RandomVariable_proper; try reflexivity.
     }
     
     apply (compose_rv (fun ts => (DS_X1 X0 T Y n ts, ts)) (dom1:=F n) (dom2:=(product_sa borel_sa (F n)))); trivial.
     apply product_sa_rv.
     + apply adaptX.
     + apply id_rv.
 Qed.
 
 Fixpoint DS_Xn_v (X0:Ts->R) (T:forall (n:nat), (vector R n*Ts)->R) (Y:nat->Ts->R) (n:nat) : Ts -> vector R (S n) :=
   match n with
   | 0%nat => fun ts => vector_singleton (X0 ts)
   | S m => let prefix := DS_Xn_v X0 T Y m in
           fun ts =>
             vector_add_to_end
               (T (S m) (prefix ts, ts) + Y m ts) (prefix ts)
   end.

 Definition DS_Xn (X0:Ts->R) (T:forall (n:nat), (vector R n*Ts)->R) (Y:nat->Ts->R) (n:nat) :
   Ts -> R
   := fun ts => vector_nth n (Nat.lt_succ_diag_r _) (DS_Xn_v X0 T Y n ts).

 Definition DS_Tn (X0:Ts->R) (T:forall (n:nat), (vector R n*Ts)->R) (Y:nat->Ts->R) (n:nat) ts : R
   := T (S n) (DS_Xn_v X0 T Y n ts, ts).
     
 Corollary Dvoretzky_DS_extended_simple_vec
           (X0:Ts->R) 
        (Y : nat -> Ts -> R)
        (T : forall (n:nat), (vector R n*Ts)->R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa (DS_Xn X0 T Y) F}
        {adaptT : IsAdapted borel_sa (DS_Tn X0 T Y) F}
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
(*        (hpos3 : forall n x, 0 <= gamma n x) *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n))
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
(*  (forall n omega, (Rabs (DS_Tn X0 T Y n omega)) <= Rmax (alpha n omega) ((1+beta n omega)*(rvabs ((DS_Xn X0 T Y n)) omega) - gamma n omega)) ->
*)
  (forall n, almostR2 prts Rle (rvabs (DS_Tn X0 T Y n))
                      (rvmax (alpha n) 
                             (rvminus
                                (rvmult 
                                   (rvplus (const 1) (beta n))
                                   (rvabs (DS_Xn X0 T Y n)))
                                 (gamma n)))) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega))) ->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => (DS_Xn X0 T Y n omega)) 0).
 Proof.
   intros.
   eapply (Dvoretzky_DS_extended_almost
                 (DS_Xn X0 T Y) Y
                 (DS_Tn X0 T Y)
                 isfilt filt_sub
                 hpos1 hpos2 hpos3

          ); trivial.
   - intros ??.
     unfold DS_Tn, DS_Xn; simpl.
     rewrite vector_nth_add_to_end_suffix.
     unfold rvplus.
     reflexivity.
 Qed.
 
  (* establish a basic property of the history we are passing aroung: we always just append to it *)
 Lemma DS_Xn_v_same_prefix_plus_helper (X0:Ts->R) (T:forall (n:nat), (vector R n*Ts)->R) (Y:nat->Ts->R)
       (m n i:nat) pf1 pf2 ts : 
   vector_nth i pf1 (DS_Xn_v X0 T Y (m+n) ts) = vector_nth i pf2 (DS_Xn_v X0 T Y n ts).
 Proof.
   induction m; simpl.
   - apply vector_nth_ext.
   - simpl in pf2.
     erewrite vector_nth_add_to_end_prefix.
     rewrite IHm.
     reflexivity.
     Unshelve.
     lia.
 Qed.

 Lemma DS_Xn_v_same_prefix_le_helper (X0:Ts->R) (T:forall (n:nat), (vector R n*Ts)->R) (Y:nat->Ts->R)
       (m n i:nat) pf1 pf2 ts : (n <= m)%nat ->
   vector_nth i pf1 (DS_Xn_v X0 T Y m ts) = vector_nth i pf2 (DS_Xn_v X0 T Y n ts).
 Proof.
   intros.
   assert (m= ((m-n) + n)%nat) by lia.
   generalize (DS_Xn_v_same_prefix_plus_helper X0 T Y (((m-n))%nat) n i)
   ; intros HH.
   destruct H0.
   apply HH.
 Qed.

 (* Any common prefix is the same *)
 Theorem DS_Xn_v_same_prefix (X0:Ts->R) (T:forall (n:nat), (vector R n*Ts)->R) (Y:nat->Ts->R)
       (m n i:nat) pf1 pf2 ts :
   vector_nth i pf1 (DS_Xn_v X0 T Y m ts) = vector_nth i pf2 (DS_Xn_v X0 T Y n ts).
 Proof.
   destruct (le_dec n m).
   - now apply DS_Xn_v_same_prefix_le_helper.
   - symmetry.
     apply DS_Xn_v_same_prefix_le_helper.
     lia.
 Qed.

  Fixpoint DS_Xnd_v (X0:Ts->R) (T:forall (n:nat), (vector R n)->R) (Y:nat->Ts->R) (n:nat) : Ts -> vector R (S n) :=
   match n with
   | 0%nat => fun ts => vector_singleton (X0 ts)
   | S m => let prefix := DS_Xnd_v X0 T Y m in
           fun ts =>
             vector_add_to_end
               (T (S m) (prefix ts) + Y m ts) (prefix ts)
   end.

 Definition DS_Xdn (X0:Ts->R) (T:forall (n:nat), (vector R n)->R) (Y:nat->Ts->R) (n:nat) :
   Ts -> R
   := fun ts => vector_nth n (Nat.lt_succ_diag_r _) (DS_Xnd_v X0 T Y n ts).

 Definition DS_Tdn (X0:Ts->R) (T:forall (n:nat), (vector R n)->R) (Y:nat->Ts->R) (n:nat) ts : R
   := T (S n) (DS_Xnd_v X0 T Y n ts).

 Instance vector_singleton_rv : RandomVariable borel_sa (Rvector_borel_sa 1) vector_singleton.
 Proof.
   apply RealVectorMeasurableRandomVariable; intros ??; simpl.
   rewrite vector_nth_fun_to_vector.
   eapply RealMeasurable_proper.
   - intros ?.
     rewrite vector_nth_singleton.
     reflexivity.
   - apply rv_measurable.
     apply id_rv.
 Qed.

 Instance DS_Xdn_v_rv (X0:Ts->R) 
        (Y : nat -> Ts -> R)
        (T : forall (n:nat), vector R n->R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {rvT:(forall n, RandomVariable (Rvector_borel_sa n) borel_sa (T n))}
        {adaptX : IsAdapted borel_sa (DS_Xdn X0 T Y) F} :
   forall n,
     RandomVariable (F n) (Rvector_borel_sa (S n)) (DS_Xnd_v X0 T Y n).
 Proof.
   induction n; simpl.
   - apply (compose_rv (dom1:=F 0%nat) (dom2:=borel_sa) (dom3:=Rvector_borel_sa 1)%nat
                       X0).
     + apply (adaptX 0)%nat.
     + apply vector_singleton_rv.
   - apply RealVectorMeasurableRandomVariable; intros ??; simpl.
     rewrite vector_nth_fun_to_vector.
     destruct (Nat.eq_dec i (S n)).
     + subst.
       eapply RealMeasurable_proper.
       * intros ?.
         rewrite vector_nth_add_to_end_suffix.
         reflexivity.
       * specialize (adaptX (S n)).
         unfold DS_Xdn in adaptX.
         simpl in adaptX.
         apply rv_measurable.
         generalize adaptX.
         apply RandomVariable_proper; try reflexivity.
         intros ?.
         rewrite vector_nth_add_to_end_suffix.
         reflexivity.
     + assert (pf2:(i < S n)%nat) by lia.
       eapply RealMeasurable_proper.
       * intros ?.
         rewrite (vector_nth_add_to_end_prefix _ _ _ _ pf2).
         reflexivity.
       * apply RandomVariableRealVectorMeasurable in IHn.
         specialize (IHn i pf2).
         apply rv_measurable.
         apply measurable_rv in IHn.
         revert IHn.
         apply RandomVariable_proper_le; try reflexivity.
         -- apply isfilt.
         -- intros ?; simpl.
            rewrite vector_nth_fun_to_vector.
            reflexivity.
 Qed.

 Instance DS_Tdn_adapted  (X0:Ts->R) 
        (Y : nat -> Ts -> R)
        (T : forall (n:nat), vector R n->R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {rvT:(forall n, RandomVariable (Rvector_borel_sa n) borel_sa (T n))}
        {adaptX : IsAdapted borel_sa (DS_Xdn X0 T Y) F} :
   IsAdapted borel_sa (DS_Tdn X0 T Y) F.
 Proof.
   unfold DS_Tdn.
   intros n.
   apply (compose_rv (dom1:=F n) (dom2:=Rvector_borel_sa (S n)) (dom3:=borel_sa)
                     (DS_Xnd_v X0 T Y n)); trivial.
   now apply DS_Xdn_v_rv.
 Qed.   

 Corollary Dvoretzky_DS_simple_vec
           (X0:Ts->R) 
        (Y : nat -> Ts -> R)
        (T : forall (n:nat), vector R n->R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {rvT:(forall n, RandomVariable (Rvector_borel_sa n) borel_sa (T n))}
        {adaptX : IsAdapted borel_sa (DS_Xdn X0 T Y) F}
        {alpha beta gamma : nat -> R}
        (hpos1 : forall n, 0 <= alpha n)
        (hpos2 : forall n, 0 <= beta n)
        (hpos3 : forall n, 0 <= gamma n)
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, (Rabs (DS_Tdn X0 T Y n omega)) <= Rmax (alpha n) ((1+beta n)*(rvabs ((DS_Xdn X0 T Y n)) omega) - gamma n)) ->
  ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
  is_lim_seq alpha 0 ->
  ex_finite_lim_seq (sum_n beta) ->
  is_lim_seq (sum_n gamma) p_infty ->
  almost _ (fun omega => is_lim_seq (fun n => (DS_Xdn X0 T Y n omega)) 0).
 Proof.
   intros.
   eapply (Dvoretzky_DS
                 (DS_Xdn X0 T Y) Y
                 (DS_Tdn X0 T Y)
                 isfilt filt_sub
                 hpos1 hpos2 hpos3

          ); trivial.
   - intros ??.
     unfold DS_Tdn, DS_Xdn; simpl.
     rewrite vector_nth_add_to_end_suffix.
     unfold rvplus.
     reflexivity.
     Unshelve.
     now apply DS_Tdn_adapted.
 Qed.

 Theorem Dvoretzky_DS_extended_alt_almost
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
(*        (hpos3 : forall n x, 0 <= gamma n x) *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n)) 
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
(*  (forall n omega, Rabs (T n omega) <=
                   Rmax (alpha n omega) ((1+beta n omega - gamma n omega)*(Rabs (X n omega)))) -> *)
   (forall n, almostR2 prts Rle (rvabs (T n)) 
                       (rvmax (alpha n) 
                              (rvmult 
                                 (rvminus
                                    (rvplus (const 1) (beta n))
                                    (gamma n))
                                 (rvabs (X n))))) ->
  ex_series (fun n => FiniteExpectation _ (rvsqr (Y n))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_series (fun n => beta n omega))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   destruct (Dvoretzky_DS_scale_prop_stochastic X T hpos1 hpos2 hpos3 H1 H3 H4 H5) as [alpha2 [gamma2 [? [? [? [? ?]]]]]].
   apply (Dvoretzky_DS_extended_almost X Y T isfilt filt_sub H6 hpos2 H7 rvy); trivial.
 Qed.

 Theorem Dvoretzky_DS_extended_alt
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
        (hpos3 : forall n x, 0 <= gamma n x) 
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
  (forall n omega, Rabs (T n omega) <=
                   Rmax (alpha n omega) ((1+beta n omega - gamma n omega)*(Rabs (X n omega)))) -> 
  ex_series (fun n => FiniteExpectation _ (rvsqr (Y n))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_series (fun n => beta n omega))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) 0).
 Proof.
   intros.
   assert (hpos3': forall n, almostR2 prts Rle (const 0) (gamma n)).
   {
     intros.
     now apply all_almost.
   }
   apply (Dvoretzky_DS_extended_alt_almost X Y T isfilt filt_sub hpos1 hpos2 hpos3' rvy); trivial.
   intros; apply all_almost; intros.
   specialize (H1 n x).
   now rv_unfold'.
  Qed.

 Theorem Dvoretzky_DS_extended_alt_theta (theta : R)
        (X Y : nat -> Ts -> R)
        (T : nat -> Ts -> R)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)
        {adaptX : IsAdapted borel_sa X F}
        {adaptT : IsAdapted borel_sa T F}
        {alpha beta gamma : nat -> Ts -> R}
        (hpos1 : forall n x, 0 <= alpha n x)
        (hpos2 : forall n x, 0 <= beta n x )
(*        (hpos3 : forall n x, 0 <= gamma n x) *)
        (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n)) 
        (rvy : forall n, RandomVariable dom borel_sa (Y n))
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
   (forall (n:nat), rv_eq (X (S n)) (rvplus (T n) (Y n))) ->
  (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                     (fun x : Ts => const 0 x)) ->
(*  (forall n omega, Rabs (T n omega - theta) <=
                   Rmax (alpha n omega) ((1+beta n omega - gamma n omega)*(Rabs (X n omega - theta)))) ->
*)
   (forall n, almostR2 prts Rle (rvabs (rvminus (T n) (const theta)))
                       (rvmax (alpha n) 
                              (rvmult 
                                 (rvminus
                                    (rvplus (const 1) (beta n))
                                    (gamma n))
                                 (rvabs (rvminus (X n) (const theta)))))) ->

  ex_series (fun n => FiniteExpectation _ (rvsqr (Y n))) ->
  almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
  almost prts (fun omega => ex_series (fun n => beta n omega))->
  almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
  almost _ (fun omega => is_lim_seq (fun n => X n omega) theta).
 Proof.
   intros.
   pose (X' := fun n => rvminus (X n) (const theta)).
   pose (T' := fun n => rvminus (T n) (const theta)).
   destruct (Dvoretzky_DS_scale_prop_stochastic X' T' hpos1 hpos2 hpos3) as [alpha2 [gamma2 [? [? [? [? ?]]]]]]; trivial.
   apply (Dvoretzky_DS_extended_theta_almost theta X Y T isfilt filt_sub H6 hpos2 H7 rvy); trivial.
 Qed.

   Corollary Dvoretzky_DS_extended_alt_simple_vec_theta (theta : R)
             (X0:Ts->R) 
             (Y : nat -> Ts -> R)
             (T : forall (n:nat), (vector R n*Ts)->R)
             {F : nat -> SigmaAlgebra Ts}
             (isfilt : IsFiltration F)
             (filt_sub : forall n, sa_sub (F n) dom)
             {adaptX : IsAdapted borel_sa (DS_Xn X0 T Y) F}
             {adaptT : IsAdapted borel_sa (DS_Tn X0 T Y) F}
             {alpha beta gamma : nat -> Ts -> R}
             (hpos1 : forall n x, 0 <= alpha n x)
             (hpos2 : forall n x, 0 <= beta n x )
(*             (hpos3 : forall n x, 0 <= gamma n x) *)
             (hpos3 : forall n, almostR2 prts Rle (const 0) (gamma n)) 
             (rvy : forall n, RandomVariable dom borel_sa (Y n))
             {svy2 : forall n, IsFiniteExpectation prts (rvsqr (Y n))} :
     let X := (DS_Xn X0 T Y) in
     let T' := (DS_Tn X0 T Y) in     
     (forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (Y n))
                               (fun x : Ts => const 0 x)) ->
(*
     (forall n omega, (Rabs (T' n omega - theta)) <= Rmax (alpha n omega) ((1+beta n omega-gamma n omega)*(Rabs (X n omega - theta)))) ->
*)
   (forall n, almostR2 prts Rle (rvabs (rvminus (T' n) (const theta)))
                       (rvmax (alpha n) 
                              (rvmult 
                                 (rvminus
                                    (rvplus (const 1) (beta n))
                                    (gamma n))
                                 (rvabs (rvminus (X n) (const theta)))))) ->

     ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (Y n)))) ->
     almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0) ->
     almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega))) ->
     almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty) ->
     almost _ (fun omega => is_lim_seq (fun n => (X n omega)) theta).
 Proof.
   intros.
   eapply (Dvoretzky_DS_extended_alt_theta theta
                 X Y T'
                 isfilt filt_sub
                 hpos1 hpos2 hpos3
          ); trivial.
   - intros ??.
     unfold X, T', DS_Tn, DS_Xn; simpl.
     rewrite vector_nth_add_to_end_suffix.
     unfold rvplus.
     reflexivity.
 Qed.

End Derman_Sacks.

Section Results.

   (* Dvoretzky's Regular Theorem *)

   Corollary Dvoretzky_DS_simple_vec_theta
        (* Given an underlying probability space (Ts, dom, ps_P) *)
        {Ts : Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}

        (* and a filtration F of sub-σ-algebras of dom *)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)

        (* Let Xn, Wn, Tn be such that *)
        (X0: Ts -> R)
        (* Wn is measurable *)
        (W : nat -> Ts -> R)
        (rvW : forall n, RandomVariable dom borel_sa (W n))
        (* Tn is measurable for all n*)
        (T : forall n, vector R n->R)
        {rvT: forall n, (RandomVariable (Rvector_borel_sa n) borel_sa (T n))}

        (* The sequence {Xn = Tn + Wn} is F-adapted *)
        {adaptX : let X' := DS_Xdn X0 T W in IsAdapted borel_sa X' F}

        (* The conditional expectation of W_n wrt F_n is zero almost surely. *)
        (H7 : forall n, almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (W n)) (const 0))
        (* And its square has finite expectation *)
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (W n))}
        (* And it's series of expectations of it's square converges. *)
        (H8 : ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (W n)))))
        (*alpha beta gamma are nonnegative real number sequences *)
        {alpha beta gamma : nat -> R}
        (H10 : forall n, 0 <= alpha n)
        (H11 : forall n, 0 <= beta n)
        (H12 : forall n, 0 <= gamma n)
        (* the limit of alpha is zero*)
        (H13 : is_lim_seq alpha 0)
        (* the limit of partial sums of beta is finite*)
        (H14 : ex_finite_lim_seq (sum_n beta))
        (* the limit of partial sums of gamma goes to +infinity*)
        (H15 : is_lim_seq (sum_n gamma) p_infty)
        (*theta is a real number such that*)
        (theta : R)
        (* it satisfies the following bound for Tn for all n *)
        (H16 : let T' := DS_Tdn X0 T W in
              let X' := DS_Xdn X0 T W in
         forall n omega, (Rabs (T' n omega - theta)) <= Rmax (alpha n) ((1+beta n)*(Rabs (X' n omega - theta)) - gamma n))
   : let X' := DS_Xdn X0 T W in
     almost _ (fun omega => is_lim_seq (fun n => (X' n omega)) theta).
 Proof.
   eapply (Dvoretzky_DS_theta theta
                 (DS_Xdn X0 T W) W
                 (DS_Tdn X0 T W)
                 isfilt filt_sub
                 H10 H11 H12
          ); trivial.
   - intros ??.
     unfold DS_Tdn, DS_Xdn; simpl.
     now rewrite vector_nth_add_to_end_suffix.
     Unshelve.
     now apply DS_Tdn_adapted.
 Qed.


 (* Extended Dvoretzky theorem. *)
 Corollary Dvoretzky_DS_extended_simple_vec_theta
        (* Given an underlying probability space (Ts, dom, ps_P) *)
        {Ts : Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}

        (* and a filtration F of sub-σ-algebras of dom *)
        {F : nat -> SigmaAlgebra Ts}
        (isfilt : IsFiltration F)
        (filt_sub : forall n, sa_sub (F n) dom)

        (* Let Xn, Wn, Tn be such that *)
        (X0:Ts->R)
        (* Wn is measurable for all n *)
        (W : nat -> Ts -> R)
        (rvW : forall n, RandomVariable dom borel_sa (W n))

        (* Tn is measurable for all n*)
        (T : forall (n:nat), (vector R n*Ts)->R)
        (* The sequence {Xn = Tn + Wn} is F-adapted *)
        {adaptX : let X' := DS_Xn X0 T W in IsAdapted borel_sa X' F}
       (* The functions Tn are are F-adapted *)
        {adaptT : let T' := DS_Tn X0 T W in IsAdapted borel_sa T' F}
        (* The conditional expectation of W_n wrt F_n is zero almost surely. *)
        (H7 : forall (n:nat), almostR2 prts eq (ConditionalExpectation _ (filt_sub n) (W n)) (const 0))
        (* And its square has finite expectation *)
        {svy2 : forall n, IsFiniteExpectation prts (rvsqr (W n))}
        (* And it's series of expectations of it's square converges. *)
        (H8 : ex_finite_lim_seq (sum_n (fun n => FiniteExpectation _ (rvsqr (W n)))))

        (*alpha beta gamma are nonnegative real number functions *)
        {alpha beta gamma : nat -> Ts -> R}
        (H10 : forall n x, 0 <= alpha n x)
        (H11 : forall n x, 0 <= beta n x )
        (H12 : forall n x, 0 <= gamma n x)

        (* the limit of alpha is zero almost surely*)
        (H13 : almost prts (fun omega => is_lim_seq (fun n => alpha n omega) 0))
        (* the limit of partial sums of beta is finite almost surely*)
        (H14 : almost prts (fun omega => ex_finite_lim_seq (sum_n (fun n => beta n omega))))
        (* the limit of partial sums of gamma goes to +infinity almost surely*)
        (H15 : almost prts (fun omega => is_lim_seq (sum_n (fun n => gamma n omega)) p_infty))
        (*theta is a real number such that*)
        (theta : R)
        (* it satisfies the following bound for Tn for all n *)
        (H16: let T' := DS_Tn X0 T W in
              let X' := DS_Xn X0 T W in
              forall n omega, (Rabs (T' n omega - theta)) <=
                         Rmax (alpha n omega) ((1+beta n omega)*(Rabs (X' n omega - theta)) - gamma n omega))
   : let X' := DS_Xn X0 T W in
     almost _ (fun omega => is_lim_seq (fun n => (X' n omega)) theta).
 Proof.
   eapply (Dvoretzky_DS_extended_theta theta
                 (DS_Xn X0 T W) W
                 (DS_Tn X0 T W)
                 isfilt filt_sub
                 H10 H11 H12
          ); trivial.
   intros ??.
   unfold DS_Tn, DS_Xn; simpl.
   now rewrite vector_nth_add_to_end_suffix.
 Qed.

End Results.
