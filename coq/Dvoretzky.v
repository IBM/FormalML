Require Import Reals Sums Lra Lia.
Require Import Coquelicot.Coquelicot.
Require Import LibUtils.
Require Import ProbSpace SigmaAlgebras BorelSigmaAlgebra RandomVariable.
Require Import infprod.

Require Import List Permutation.
Require Import Morphisms EquivDec Program.

Require Import Utils.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Require Import LM.hilbert Classical IndefiniteDescription.

Program Definition ortho_projection_hilbert (E:PreHilbert) 
           (phi: E -> Prop) (phi_mod: compatible_m phi) (phi_compl: complete_subset phi)
           (u : E) : E.
  generalize (ortho_projection_subspace phi phi_mod phi_compl u);intros.
  cut_to H.
  apply constructive_definite_description in H.
  exact (proj1_sig H).
  intro; apply classic.
Qed.

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


 Require Import Classical.
      
 Lemma srv_vals_offset
        (offset: R)
        (vals : list R) :
    map (fun ab : R * R => fst ab + snd ab) (list_prod vals [offset]) =  
    map (fun v => v + offset) vals.
 Proof.
   induction vals; simpl; trivial.
   now f_equal.
 Qed.

Lemma Dvoretzky_rel (n:nat) (theta:R) (T X Y : nat -> R -> R) (F : nat -> R)
      (rvy : RandomVariable prts borel_sa (Y n)) 
      (svy : SimpleRandomVariable (Y n)) 
      (rvx : RandomVariable prts borel_sa (X n)) 
      (svx: SimpleRandomVariable (X n))
      (rvt : RandomVariable prts borel_sa (fun r:R => T n (X n r))) 
      (svt: SimpleRandomVariable (fun r:R => T n (X n r))) 
      (svx2: SimpleRandomVariable (X (S n))) :
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
    rewrite (SimpleExpectation_transport (srvsqr (rvminus (X (S n)) (const theta)))
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
                                     (X n)) ; intros tower.
   generalize (conditional_scale_measurable (rvminus (fun r:R => T n (X n r)) (const theta))
                                            (Y n) (X n)); intros cond_scale.
   cut_to cond_scale.
   - specialize (tower (rvmult_rv _ (Y n)) rvx).
     specialize (tower (srvmult _ (Y n)) svx).
     rewrite <- tower.
     rewrite (SimpleExpectation_transport _ cond_scale).
     assert (eqq4:rv_eq  (rvmult (rvminus (fun r : R => T n (X n r)) (const theta))
                                 (SimpleConditionalExpectation (Y n) (X n)))
                         (const 0)).
     {
       rewrite H2.
       unfold rvmult, const; intros ?; simpl; field.
     } 
     rewrite (SimpleExpectation_transport _ eqq4).
     rewrite SimpleExpectation_const.
     rewrite Rmult_0_r, Rplus_0_r.
     specialize (H n).
     rewrite (scaleSimpleExpectation (Rsqr (F n))).
     
     apply SimpleExpectation_le; try typeclasses eauto.
     unfold RealRandomVariable_le.
     intros.
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
     unfold event_preimage, singleton_event.
     destruct svx.
     destruct svt.
     unfold RandomVariable.srv_vals; simpl.
     unfold rvminus, rvopp, rvplus, rvscale, const.
     unfold RandomVariable.srvconst_obligation_1.
     intros.
     
     destruct (classic ( exists x, X n x = c2)).
     + exists (T n c2 + (-1)*theta).
       split.
       * destruct H5 as [??].
         subst.
         assert (In (T n (X n x)) srv_vals0); auto.
         rewrite srv_vals_offset, in_map_iff.
         exists (T n (X n x)).
         split; trivial.
       * intros x eqq2.
         now rewrite eqq2.
     + exists (T n (X n 0) + (-1)*theta).
       split.
       * assert (In (T n (X n 0)) srv_vals0); auto.
         rewrite srv_vals_offset, in_map_iff.
         exists (T n (X n 0)).
         split; trivial.
       * intros ??.
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

  Lemma Fprod_0 (a : nat -> R) (a1_pos : forall n, 0 < 1 - a n) :
    (forall n, 0 <= a n < 1) ->
    l1_divergent a ->
    is_lim_seq (part_prod (fun n => (mkposreal (1 - a n)  (a1_pos n)))) 0.
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
        apply (is_lim_seq_ext (sum_n a)); [apply Ropp_sum_Ropp | apply H0].
      + apply is_lim_seq_spec in H1; unfold is_lim_seq' in H1.
        unfold eventually in H1.
        specialize (H1 (ln eps)); destruct H1.
        exists x; intros.
        specialize (H1 n H2).
        rewrite Rminus_0_r, Rabs_right by (left; apply exp_pos).
        replace (pos eps) with (exp (ln eps)); [| apply exp_ln, cond_pos].
        now apply exp_increasing.
  Qed.

  Lemma Markov_ineq {Ts:Type} {dom:SigmaAlgebra Ts} {prts : ProbSpace dom}
        (X : Ts -> R)
        (rv : RandomVariable prts borel_sa X)
        (posrv : PositiveRandomVariable X)
        (a : posreal) :
    Rbar_le (a * (ps_P (fun omega => X omega >= a))) (Expectation_posRV X).
  Proof.
    generalize (SimpleExpectation_EventIndicator (fun omega => Rge_dec (X omega) a)); intros.
    generalize simple_Expectation_posRV; intros.
    rewrite <- H.
    rewrite scaleSimpleExpectation.
    generalize (positive_scale_prv a (EventIndicator (fun omega : Ts => Rge_dec (X omega) a))); intros
    .
    assert (Hrv:RandomVariable prts borel_sa (rvscale a (EventIndicator (fun omega : Ts => Rge_dec (X omega) a)))).
    { apply rvscale_rv.
      apply EventIndicator_rv.
      apply sa_le_ge.
      now rewrite borel_sa_preimage2.
    }
    rewrite H0 with (prv := H1); trivial.
    apply Expectation_posRV_le; trivial.
    unfold RealRandomVariable_le, EventIndicator, rvscale; intros.
    specialize (posrv x).
    destruct (Rge_dec (X x) a); lra.
Qed.    
      
  Lemma Markov_ineq_div {Ts:Type} {dom:SigmaAlgebra Ts} {prts : ProbSpace dom}
        (X : Ts -> R)
        (rv : RandomVariable prts borel_sa X)
        (posrv : PositiveRandomVariable X)
        (a : posreal) :
    Rbar_le (ps_P (fun omega => X omega >= a)) (Rbar_div_pos (Expectation_posRV X) a).
  Proof.
    generalize (Markov_ineq X rv posrv a); intros.
    rewrite Rbar_div_pos_le with (z := a) in H.
    rewrite Rmult_comm in H.
    unfold Rbar_div_pos at 1 in H.
    unfold Rdiv in H.
    rewrite Rmult_assoc in H.
    rewrite <- Rinv_r_sym in H; [| apply Rgt_not_eq, cond_pos].
    now rewrite Rmult_1_r in H.
  Qed.

  Lemma Rbar_div_div_pos (a:posreal) (x: Rbar) :
    Rbar_div x a = Rbar_div_pos x a.
  Proof.
    unfold Rbar_div, Rbar_div_pos.
    assert (0 < / a).
    apply Rinv_0_lt_compat.
    apply cond_pos.
    destruct x.
    - simpl.
      now unfold Rdiv.
    - unfold Rbar_div, Rbar_div_pos.
      simpl.
      destruct (Rle_dec 0 (/ a)); [| lra].
      destruct (Rle_lt_or_eq_dec 0 (/ a) r); [|lra].
      trivial.
    - unfold Rbar_div, Rbar_div_pos.
      simpl.
      destruct (Rle_dec 0 (/ a)); [| lra].
      destruct (Rle_lt_or_eq_dec 0 (/ a) r); [|lra].
      trivial.
  Qed.
    
    
    
        
