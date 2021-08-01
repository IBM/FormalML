Require Import Reals Sums Lra Lia.
Require Import Coquelicot.Coquelicot.
Require Import LibUtils.
Require Import Expectation.
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
   {dom: SigmaAlgebra R}
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

Lemma Dvoretzky_rel (n:nat) (theta:R) (T X Y : nat -> R -> R) (F : nat -> R)
      (rvy : RandomVariable dom borel_sa (Y n)) 
      (svy : FiniteRangeFunction (Y n)) 
      (rvx : RandomVariable dom borel_sa (X n)) 
      (svx: FiniteRangeFunction (X n))
      (rvt : RandomVariable dom borel_sa (fun r:R => T n (X n r))) 
      (svt: FiniteRangeFunction (fun r:R => T n (X n r))) 
      (rvx2 : RandomVariable dom borel_sa (X (S n)))
      (svx2: FiniteRangeFunction (X (S n))) :
  (forall (n:nat), F n >= 0) ->
  (forall (n:nat) (r:R), Rle (Rabs ((T n r) - theta)) (F n * Rabs (r-theta))) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r => T n (X n r)) (Y n))) ->
  rv_eq (SimpleConditionalExpectation (Y n) (X n)) (const 0) ->
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
   assert (eqq1:rv_eq (rvsqr (rvminus (rvplus (fun r : R => T n (X n r)) (Y n)) (const theta))) 
                      (rvplus (rvsqr (rvminus (fun r : R => T n (X n r)) (const theta)))
                              (rvplus
                                 (rvscale 2 (rvmult (rvminus (fun r : R => T n (X n r)) (const theta))
                                                    (Y n)))
                            (rvsqr (Y n))))).
   { intros r.
     unfold rvsqr, rvplus, rvminus, rvopp, rvscale, Rsqr, rvmult, const.
     unfold rvplus.
     lra.
   }
   rewrite (SimpleExpectation_transport _ eqq1).
   rewrite (SimpleExpectation_pf_irrel _ _).
   rewrite <- sumSimpleExpectation; try typeclasses eauto.
   rewrite <- sumSimpleExpectation; try typeclasses eauto.
   rewrite <- scaleSimpleExpectation.
   rewrite <- Rplus_assoc.
   apply Rplus_le_compat_r.
   generalize (conditional_tower_law (rvmult (rvminus (fun r : R => T n (X n r)) (const theta))
                                             (Y n)) 
                                     (X n) _ _) ; intros tower.
   generalize (conditional_scale_measurable (rvminus (fun r:R => T n (X n r)) (const theta))
                                            (Y n) (X n)); intros cond_scale.
   cut_to cond_scale.
   - rewrite <- tower.
     rewrite (SimpleExpectation_transport _ cond_scale).
     assert (eqq4:rv_eq  (rvmult (rvminus (fun r : R => T n (X n r)) (const theta))
                                 (SimpleConditionalExpectation (Y n) (X n)))
                         (const 0)).
     {
       rewrite H2.
       unfold rvmult, const; intros ?; simpl; field.
     } 
     rewrite (SimpleExpectation_transport _ eqq4).
     rewrite (SimpleExpectation_pf_irrel _ (frfconst _)).
     rewrite SimpleExpectation_const.
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
     unfold Rminus in H0.
     replace (-1 * theta) with (-theta) by lra.
     apply H0.
   - unfold simple_sigma_measurable.
     unfold event_preimage, event_singleton.
     destruct svx.
     destruct svt.
     unfold RandomVariable.frf_vals; simpl.
     unfold rvminus, rvopp, rvplus, rvscale, const.
     intros.
     
     destruct (classic ( exists x, X n x = c2)).
     + exists (T n c2 + (-1)*theta).
       intros x; simpl.
       unfold pre_event_preimage, pre_event_singleton; intros eqq2.
       now rewrite eqq2.
     + exists (T n (X n 0) + (-1)*theta).
       intros ?; simpl.
       unfold pre_event_preimage, pre_event_singleton; intros eqq2.
       elim H5.
       eauto.
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

End Dvoretzky.
