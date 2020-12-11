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
