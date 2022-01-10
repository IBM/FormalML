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
