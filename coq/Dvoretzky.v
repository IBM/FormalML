Require Import Reals Sums Lra Lia.
Require Import Coquelicot.Coquelicot.
Require Import LibUtils.
Require Import Expectation.
Require Import infprod.

Require Import List Permutation.
Require Import Morphisms EquivDec Program.

Require Import Utils.
Import ListNotations.


Set Bullet Behavior "Strict Subproofs".

Require Import LM.hilbert Classical IndefiniteDescription.
Require Import RandomVariableL2.

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
      (rvy : RandomVariable dom borel_sa (Y n)) 
      (svy : SimpleRandomVariable (Y n)) 
      (rvx : RandomVariable dom borel_sa (X n)) 
      (svx: SimpleRandomVariable (X n))
      (rvt : RandomVariable dom borel_sa (fun r:R => T n (X n r))) 
      (svt: SimpleRandomVariable (fun r:R => T n (X n r))) 
      (rvx2 : RandomVariable dom borel_sa (X (S n)))
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
     rewrite (SimpleExpectation_pf_irrel _ (srvconst _)).
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
     unfold RandomVariable.srv_vals; simpl.
     unfold rvminus, rvopp, rvplus, rvscale, const.
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
       * intros x; simpl.
         unfold pre_event_preimage, pre_event_singleton; intros eqq2.
         now rewrite eqq2.
     + exists (T n (X n 0) + (-1)*theta).
       split.
       * assert (In (T n (X n 0)) srv_vals0); auto.
         rewrite srv_vals_offset, in_map_iff.
         exists (T n (X n 0)).
         split; trivial.
       * intros ?; simpl.
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

  Lemma sa_le_ge_rv  {Ts:Type} {dom:SigmaAlgebra Ts}
        (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : sa_sigma (fun omega => rv_X omega >= x).
  Proof.
    apply sa_le_ge.
    now apply rv_measurable.
  Qed.

  Definition event_ge {Ts:Type} {dom:SigmaAlgebra Ts}
        (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : event dom
    := @exist (pre_event Ts) _ _ (sa_le_ge_rv rv_X x).

  Lemma Markov_ineq {Ts:Type} {dom:SigmaAlgebra Ts} {prts : ProbSpace dom}
        (X : Ts -> R)
        (rv : RandomVariable dom borel_sa X)
        (posrv : PositiveRandomVariable X)
        (a : posreal) :
    Rbar_le (a * (ps_P (event_ge X a))) (Expectation_posRV X).
  Proof.
    generalize (SimpleExpectation_pre_EventIndicator (sa_le_ge_rv X a) (fun x => Rge_dec (X x) a)); intros.
    unfold event_ge.
    rewrite <- H.
    generalize simple_Expectation_posRV; intros.
    rewrite scaleSimpleExpectation.
    erewrite H0.
    apply Expectation_posRV_le.
    unfold EventIndicator, rvscale; intros x.
    specialize (posrv x).
    destruct (Rge_dec (X x) a); lra.
  Qed.    
      
  Lemma Markov_ineq_div {Ts:Type} {dom:SigmaAlgebra Ts} {prts : ProbSpace dom}
        (X : Ts -> R)
        (rv : RandomVariable dom borel_sa X)
        (posrv : PositiveRandomVariable X)
        (a : posreal) :
    Rbar_le (ps_P (event_ge X a)) (Rbar_div_pos (Expectation_posRV X) a).
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
    
  Lemma Rsqr_pos (a : posreal) :
    0 < Rsqr a.
  Proof.
    generalize (Rle_0_sqr a); intros.
    destruct H; trivial.
    generalize (cond_pos a); intros.
    symmetry in H; apply Rsqr_eq_0 in H.
    lra.
  Qed.

  Lemma mkpos_Rsqr (a : posreal) :
    Rsqr a = mkposreal _ (Rsqr_pos a).
  Proof.
    now simpl.
  Qed.

  Lemma conv_l2_prob_le_div {Ts:Type} {dom:SigmaAlgebra Ts} {prts: ProbSpace dom}
        (eps : posreal) 
        (X : Ts -> R) 
        (rv : RandomVariable dom borel_sa X)
        (posrv: PositiveRandomVariable X) :
  Rbar_le (ps_P (event_ge X eps))
          (Rbar_div (Expectation_posRV (rvsqr X)) 
                    (Rsqr eps)).
    Proof.
      assert (event_equiv (event_ge X eps)
                          (event_ge (rvsqr X) (Rsqr eps))).
      - intro x.
        split; intros.
        + apply Rge_le in H.
          apply Rle_ge.
          apply Rsqr_incr_1; trivial.
          left; apply cond_pos.
        + apply Rge_le in H.
          apply Rle_ge.
          apply Rsqr_incr_0; trivial.
          left; apply cond_pos.
      - rewrite H.
        rewrite mkpos_Rsqr.
        rewrite Rbar_div_div_pos.
        apply Markov_ineq_div.
    Qed.


  Lemma conv_l2_prob_le {Ts:Type} {dom:SigmaAlgebra Ts} {prts: ProbSpace dom}
        (eps : posreal) 
        (X Xn: Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : RandomVariable dom borel_sa Xn) :
    is_finite (Expectation_posRV (rvsqr (rvabs (rvminus X Xn)))) ->
    ps_P (event_ge (rvabs (rvminus X Xn)) eps) <=
    (Expectation_posRV (rvsqr (rvabs (rvminus X Xn)))) / (Rsqr eps).
    Proof.
      assert (RandomVariable dom borel_sa (rvabs (rvminus X Xn))).
      - apply rvabs_rv.
        now apply rvminus_rv.
      - assert (PositiveRandomVariable (rvabs (rvminus X Xn))).
        now apply prvabs.
        intros.
        generalize (conv_l2_prob_le_div eps (rvabs (rvminus X Xn)) H H0).
        rewrite <- H1.
        simpl.
        intros.
        erewrite ps_proper; try eapply H2.
        intros ?; simpl.
        reflexivity.
    Qed.

  Lemma conv_l1_prob_le {Ts:Type} {dom:SigmaAlgebra Ts} {prts: ProbSpace dom}
        (eps : posreal) 
        (X Xn: Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : RandomVariable dom borel_sa Xn) :
    is_finite (Expectation_posRV (rvabs (rvminus X Xn))) ->
    ps_P (event_ge (rvabs (rvminus X Xn)) eps) <=
    (Expectation_posRV (rvabs (rvminus X Xn))) / eps.
    Proof.
      assert (RandomVariable dom borel_sa (rvabs (rvminus X Xn))).
      - apply rvabs_rv.
        now apply rvminus_rv.
      - assert (PositiveRandomVariable (rvabs (rvminus X Xn))).
        now apply prvabs.
        intros.
        generalize (Markov_ineq_div (rvabs (rvminus X Xn)) H H0 eps); intros.
        rewrite <- H1 in H2.
        intros.
        erewrite ps_proper; try eapply H2.
        intros ?; simpl.
        reflexivity.
    Qed.
        
  Lemma conv_l2_prob {Ts:Type} {dom:SigmaAlgebra Ts} {prts: ProbSpace dom}
        (eps : posreal) 
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) :
    (forall n, is_finite (Expectation_posRV (rvsqr (rvabs (rvminus X (Xn n)))))) ->
    is_lim_seq (fun n => Expectation_posRV (rvsqr (rvabs (rvminus X (Xn n))))) 0 ->
    is_lim_seq (fun n => ps_P (event_ge (rvabs (rvminus X (Xn n))) eps)) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                    (w := (fun n => (Expectation_posRV (rvsqr (rvabs (rvminus X (Xn n))))) / (Rsqr eps))).
    - unfold eventually.
      exists (0%nat).
      intros.
      split.
      + apply ps_pos.
      + apply conv_l2_prob_le; trivial.
    - apply is_lim_seq_const.
    - apply is_lim_seq_div with (l1 := 0) (l2 := Rsqr eps); trivial.
      + apply is_lim_seq_const.
      + apply Rbar_finite_neq.
        apply Rgt_not_eq.
        apply Rsqr_pos.
      + unfold is_Rbar_div.
        simpl.
        unfold is_Rbar_mult, Rbar_mult'.
        f_equal.
        now rewrite Rmult_0_l.
  Qed.

    Lemma conv_l1_prob {Ts:Type} {dom:SigmaAlgebra Ts} {prts: ProbSpace dom}
        (eps : posreal) 
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) :
    (forall n, is_finite (Expectation_posRV (rvabs (rvminus X (Xn n))))) ->
    is_lim_seq (fun n => Expectation_posRV (rvabs (rvminus X (Xn n)))) 0 ->
    is_lim_seq (fun n => ps_P (event_ge (rvabs (rvminus X (Xn n))) eps)) 0.
  Proof.
    intros.
    apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                    (w := (fun n => (Expectation_posRV (rvabs (rvminus X (Xn n)))) / eps)).
    - unfold eventually.
      exists (0%nat).
      intros.
      split.
      + apply ps_pos.
      + apply conv_l1_prob_le; trivial.
    - apply is_lim_seq_const.
    - apply is_lim_seq_div with (l1 := 0) (l2 := eps); trivial.
      + apply is_lim_seq_const.
      + apply Rbar_finite_neq.
        apply Rgt_not_eq.
        apply cond_pos.
      + unfold is_Rbar_div.
        simpl.
        unfold is_Rbar_mult, Rbar_mult'.
        f_equal.
        now rewrite Rmult_0_l.
  Qed.

  Ltac L2RRV_simpl
    := repeat match goal with
              | [H : LpRRV _ _ |- _ ] => destruct H as [???]
              end
       ; unfold LpRRVplus, LpRRVminus, LpRRVopp, LpRRVscale
       ; simpl.

   Lemma L2RRV_L2_L1   {Ts:Type} {dom:SigmaAlgebra Ts} {prts: ProbSpace dom}
         (x : LpRRV prts 2) :
    Rsqr (FiniteExpectation prts x) <= FiniteExpectation prts (rvsqr x).
   Proof.
     generalize (L2RRV_Cauchy_Schwarz prts x (LpRRVconst prts 1)); intros.
     assert (L2RRVinner prts (LpRRVconst prts 1) (LpRRVconst prts 1) = 1).
     unfold L2RRVinner.
     L2RRV_simpl.
     unfold rvmult.
     rewrite (FiniteExpectation_ext prts _ (const 1)).
     - apply FiniteExpectation_const.
     - intro x0.
       unfold const; lra.
     - rewrite H0 in H.
       rewrite Rmult_1_r in H.
       assert (L2RRVinner prts x (LpRRVconst prts 1) = FiniteExpectation prts x).
       + unfold L2RRVinner.
         rewrite (FiniteExpectation_ext _ _  x); trivial.
         intro x0.
         L2RRV_simpl.
         unfold rvmult, const.
         lra.
       + rewrite H1 in H.
         unfold L2RRVinner in H.
         rewrite (FiniteExpectation_ext _ _ _ (symmetry (rvsqr_eq _))) in H.
         apply H; lra.
  Qed.

    Definition Rsqrt_abs (r : R) : R := Rsqrt (mknonnegreal (Rabs r) (Rabs_pos r)).

    Lemma Rsqrt_abs_0 :
      Rsqrt_abs 0 = 0.
     Proof.
      unfold Rsqrt_abs, Rsqrt; simpl.
      match_destr; destruct a.
      rewrite Rabs_R0 in H0.
      now apply Rsqr_eq_0.
    Qed.

    Lemma continuity_pt_Rsqrt_abs_0 :
      continuity_pt Rsqrt_abs 0.
    Proof.
      unfold continuity_pt, continue_in.
      unfold limit1_in, limit_in.
      intros.
      unfold dist; simpl.
      unfold R_dist, D_x, no_cond.
      exists (Rsqr eps).
      split.
      - unfold Rsqr.
        now apply Rmult_gt_0_compat.
      - intros.
        destruct H0 as [[? ?] ?].
        rewrite Rminus_0_r in H2.
        rewrite Rsqrt_abs_0, Rminus_0_r.
        unfold Rsqrt_abs.
        rewrite Rabs_right by (apply Rle_ge, Rsqrt_positivity).
        generalize Rsqr_lt_to_Rsqrt; intros.
        assert (0 <= eps) by lra.
        specialize (H3 (mknonnegreal _ H4) (mknonnegreal _ (Rabs_pos x))).
        rewrite <- H3.
        now simpl.
     Qed.

    (* TODO(Kody):
       Move these to someplace more canonical. Like RealAdd.
       Delete identical copies in mdp.v *)
    Lemma nonneg_pf_irrel r1 (cond1 cond2:0 <= r1) :
      mknonnegreal r1 cond1 = mknonnegreal r1 cond2.
    Proof.
      f_equal.
      apply proof_irrelevance.
    Qed.

    Lemma nonneg_ext r1 cond1 r2 cond2:
      r1 = r2 ->
      mknonnegreal r1 cond1 = mknonnegreal r2 cond2.
    Proof.
      intros; subst.
      apply nonneg_pf_irrel.
    Qed.

    Lemma conv_l2_l1 {Ts:Type} {dom:SigmaAlgebra Ts} {prts: ProbSpace dom}
        (X: Ts -> R)
        (Xn: nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) 
        (isl: forall n, IsLp prts 2 (rvabs (rvminus X (Xn n)))) :
    is_lim_seq (fun n => FiniteExpectation prts (rvsqr (rvabs (rvminus X (Xn n))))) 0 ->
    is_lim_seq (fun n => FiniteExpectation prts (rvabs (rvminus X (Xn n)))) 0.
    Proof.
      intros.
      assert (forall n, 0 <= FiniteExpectation prts (rvsqr (rvabs (rvminus X (Xn n))))).
      - intros.
        apply FiniteExpectation_pos.
        unfold PositiveRandomVariable, rvabs, rvminus, rvopp, rvplus, rvsqr; intros.
        apply Rle_0_sqr.
      - apply is_lim_seq_le_le_loc with 
            (u := fun _ => 0) 
            (w := (fun n => Rsqrt (mknonnegreal (FiniteExpectation prts (rvsqr (rvabs (rvminus X (Xn n))))) (H0 n)))).
        + exists (0%nat); intros.
          assert (0 <= FiniteExpectation prts (rvabs (rvminus X (Xn n)))).
          * apply FiniteExpectation_pos.
            unfold rvabs, rvminus, rvopp, rvplus, PositiveRandomVariable; intros.
            apply Rabs_pos.
          * split; trivial.
            generalize (L2RRV_L2_L1 (pack_LpRRV prts (rvabs (rvminus X (Xn n)))));intros.
            generalize Rsqr_le_to_Rsqrt; intros.
            specialize (H4 (mknonnegreal _ (H0 n))
                           (mknonnegreal _ H2)).
            apply H4; simpl.
            apply H3.
        + apply is_lim_seq_const.
        + apply is_lim_seq_ext with 
          (u := fun n=> Rsqrt_abs (FiniteExpectation prts (rvsqr (rvabs (rvminus X (Xn n)))))).
          * intros.
            unfold Rsqrt_abs; f_equal.
            apply nonneg_ext. (* CAUTION : This uses proof irrelevance. *)
            now rewrite Rabs_pos_eq.
          * replace (0) with (Rsqrt_abs 0) by apply Rsqrt_abs_0.
            apply is_lim_seq_continuous; [|trivial].
            apply continuity_pt_Rsqrt_abs_0.
    Qed.

