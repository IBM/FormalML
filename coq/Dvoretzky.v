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
   

Lemma Dvoretzky_rel0 (n:nat) (T X Y : nat -> R -> R) (F : nat -> R)
      (svy : SimpleRandomVariable (Y n)) 
      (svx: SimpleRandomVariable (X n))
      (svx2: SimpleRandomVariable (X (S n))) :
  (forall (n:nat) (r:R), Rle (Rabs (T n r)) (F n * Rabs r)) ->
  (forall (n:nat), rv_eq (X (S n)) (rvplus (fun r =>  T n (X n r)) (Y n))) ->
  Rle (SimpleExpectation (rvsqr (X (S n)) ))
      ((Rsqr (F n)) * SimpleExpectation (rvsqr (X n))
       + SimpleExpectation (rvsqr (Y n))).
 Proof.
   intros.
   specialize (H0 n).
   rewrite (SimpleExpectation_transport (srvsqr (X (S n))) (rvsqr_proper _ _ H0)).

Admitted.
   
                         
Lemma Dvoretzky_rel (n:nat) (theta:R) (T X Y : nat -> R -> R) (F : nat -> R)
      (svy : SimpleRandomVariable (Y n)) 
      (svx: SimpleRandomVariable (X n))
      (svx2: SimpleRandomVariable (X (S n))) :
  (forall (n:nat) (r:R), Rle (Rabs ((T n r) - theta)) (F n * Rabs (r-theta))) ->
  (forall (n:nat) (r:R), X (S n) r = T n (X n r) + Y n r) ->
  Rle (SimpleExpectation (rvsqr (rvminus (X (S n)) (const theta)) ))
      ((Rsqr (F n)) * SimpleExpectation (rvsqr (X n))
       + SimpleExpectation (rvsqr (rvminus (Y n) (const theta)))).
