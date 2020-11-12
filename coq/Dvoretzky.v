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

 Context 
   {dom: SigmaAlgebra R}
   {prts: ProbSpace dom}.

 (* scalar version of T *)

 Global Instance rvsqr_proper {Ts} : Proper (rv_eq ==> rv_eq) (@rvsqr Ts).
 Proof.
   unfold rv_eq, rvsqr, Proper, respectful, pointwise_relation.
   intros x y eqq z.
   unfold Rsqr.
   rewrite eqq.
   trivial.
 Qed.

 Global Instance R_nonempty : NonEmpty R
   := R0.

 Global Instance rvmult_proper {Ts} : Proper (rv_eq ==> rv_eq ==> rv_eq) (@rvmult Ts).
 Proof.
   unfold rv_eq, rvmult.
   intros ???????.
   now rewrite H, H0.
 Qed.


 Lemma SimpleExpectation_const c srv : SimpleExpectation (const c) (srv:=srv) = c.
 Proof.
   rewrite (SimpleExpectation_pf_irrel _ (srvconst c)).
   unfold SimpleExpectation; simpl.
   unfold RandomVariable.srvconst_obligation_1.
   unfold event_preimage, singleton_event, const.
   erewrite ps_proper.
     - erewrite ps_one.
       lra.
     - unfold Ω.
       red; intros; intuition.
 Qed.

 Existing Instance rvscale_rv.
 Existing Instance rvplus_rv.
Existing Instance rvmult_rv.

 Declare Scope rv.

 Infix ".+" := rvplus (left associativity, at level 50) : rv.
 Infix ".-" := rvminus (left associativity, at level 50) : rv.
 Infix ".*" := rvmult (left associativity, at level 40) : rv.
 Infix ".*." := rvscale (no associativity, at level 40) : rv.
 Notation "x .²" := (rvsqr x) (at level 1) : rv.

 Local Open Scope rv.

   
Lemma Dvoretzky_rel00 (n:nat) (T X Y : nat -> R -> R) (F : nat -> R) {nempty:NonEmpty R}
      (rvy : RandomVariable prts borel_sa (Y n)) 
      (svy : SimpleRandomVariable (Y n)) 
      (rvx : RandomVariable prts borel_sa (X n)) 
      (svx: SimpleRandomVariable (X n))
      (rvt : RandomVariable prts borel_sa (fun r:R => T n (X n r))) 
      (svt: SimpleRandomVariable (fun r:R => T n (X n r))) :
  (forall (n:nat) (r:R), Rle (Rabs (T n r)) (F n * Rabs r)) ->
  (forall (n:nat), F n >= 0) ->
  rv_eq (SimpleConditionalExpectation (Y n) (X n)) (const 0) ->
  Rle (SimpleExpectation
         (rvplus (rvsqr (fun r : R => T n (X n r)))
                 (rvplus
                    (rvscale 2 (rvmult (fun r : R => T n (X n r))
                                       (Y n)))
                    (rvsqr (Y n)))))
      ((Rsqr (F n)) * SimpleExpectation (rvsqr (X n))
       + SimpleExpectation (rvsqr (Y n))).
 Proof.
   intros.
   rewrite <- sumSimpleExpectation; try typeclasses eauto.
   rewrite <- sumSimpleExpectation; try typeclasses eauto.
   rewrite <- scaleSimpleExpectation.
   rewrite <- Rplus_assoc.
   apply Rplus_le_compat_r.
   generalize (conditional_tower_law (rvmult (fun r : R => T n (X n r)) (Y n)) (X n)) ; intros.
   generalize (conditional_scale_measurable (fun r:R => T n (X n r)) (Y n) (X n)); intros.
   cut_to H3.
   - specialize (H2 (rvmult_rv (fun r : R => T n (X n r)) (Y n)) rvx).
     specialize (H2 (srvmult (fun r : R => T n (X n r)) (Y n)) svx).
     rewrite <- H2.
     rewrite (SimpleExpectation_transport _ H3).
     assert (eqq4:rv_eq  (rvmult (fun r : R => T n (X n r)) (SimpleConditionalExpectation (Y n) (X n)))
                         (const 0)).
     {
       rewrite H1.
       unfold rvmult, const; intros ?; simpl; field.
     } 
     rewrite (SimpleExpectation_transport _ eqq4).
     rewrite SimpleExpectation_const.
     rewrite Rmult_0_r .
     rewrite Rplus_0_r .
     specialize (H n).
     rewrite (scaleSimpleExpectation (Rsqr (F n))).

     apply SimpleExpectation_le; try typeclasses eauto.
     unfold RealRandomVariable_le.
     intros.
     unfold rvsqr, rvscale.
     specialize (H (X n x)).
     rewrite <- Rabs_right with (r:=F n) in H; trivial.
     rewrite <- Rabs_mult in H.
     apply Rsqr_le_abs_1 in H.
     rewrite Rsqr_mult in H.
     apply H.
   - admit.
 Admitted.

 
Lemma Dvoretzky_rel0 (n:nat) (T X Y : nat -> R -> R) (F : nat -> R)
      (svy : SimpleRandomVariable (Y n)) 
      (svx: SimpleRandomVariable (X n))
      (svx2: SimpleRandomVariable (X (S n))) :
  (forall (n:nat) (r:R), Rle (Rabs (T n r)) (F n * Rabs r)) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r =>  T n (X n r)) (Y n))) ->
  rv_eq (SimpleConditionalExpectation (Y n) (X n)) (const 0) ->
  Rle (SimpleExpectation (rvsqr (X (S n)) ))
      ((Rsqr (F n)) * SimpleExpectation (rvsqr (X n))
       + SimpleExpectation (rvsqr (Y n))).
 Proof.
   intros.
   specialize (H0 n).
   rewrite (SimpleExpectation_transport (srvsqr (X (S n))) (rvsqr_proper _ _ H0)).
   assert (eqq1:rv_eq (rvsqr (rvplus (fun r : R => T n (X n r)) (Y n))) 
                 (rvplus (rvsqr (fun r : R => T n (X n r)))
                         (rvplus
                            (rvscale 2 (rvmult (fun r : R => T n (X n r))
                                               (Y n)))
                            (rvsqr (Y n))))).
   { intros r.
     unfold rvsqr, rvplus, rvscale, Rsqr, rvmult.
     lra.
   }
   rewrite (SimpleExpectation_transport _ eqq1).
   apply Dvoretzky_rel00.
   
Admitted.
   
                         
Lemma Dvoretzky_rel (n:nat) (theta:R) (T X Y : nat -> R -> R) (F : nat -> R)
      (svy : SimpleRandomVariable (Y n)) 
      (svx: SimpleRandomVariable (X n))
      (svx2: SimpleRandomVariable (X (S n))) :
  (forall (n:nat) (r:R), Rle (Rabs ((T n r) - theta)) (F n * Rabs (r-theta))) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r => T n (X n r)) (Y n))) ->
  rv_eq (SimpleConditionalExpectation (Y n) (X n)) (const 0) ->
  Rle (SimpleExpectation (rvsqr (rvminus (X (S n)) (const theta)) ))
      ((Rsqr (F n)) * SimpleExpectation (rvsqr (X n))
       + SimpleExpectation (rvsqr (rvminus (Y n) (const theta)))).
  Proof.
    intros.
    specialize (H0 n).
    rewrite (SimpleExpectation_transport (srvsqr (rvminus (X (S n)) (const theta)))
                                        (rvsqr_proper _ _ H0)).    
