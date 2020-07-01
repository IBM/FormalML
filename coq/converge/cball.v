(** * Closed balls *)

Require Import PArith Psatz Reals.
Require Import Coquelicot.Coquelicot.

From Coq Require Import ssreflect.

Require Import posreal_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition subset T (A B : T -> Prop) := forall t,  A t -> B t.

Lemma subset_trans T (B A C : T -> Prop) :
  subset A B -> subset B C -> subset A C.
Proof. by move=> sAB sBC t At; apply/sBC/sAB. Qed.

Lemma subset_refl T (A : T -> Prop)  : subset A A. Proof. by move=> t. Qed.



Section Cball.
Variable U : UniformSpace.
Implicit Types (x y z : U).

Definition cball x r y := forall e : posreal, ball x (r+e) y.

Lemma cball_le x r1 r2 : r1 <= r2 -> forall y, cball x r1 y -> cball x r2 y.
Proof.
  move => Hr y Hr1 e.
  eapply ball_le; first apply Rplus_le_compat_r, Hr.
  exact: Hr1.
Qed.

Lemma cball_center x (r : nonnegreal) : cball x r x.
Proof.
  move => e.
  have Hre : 0 < r+e by case: r => r Hr; case: e => e He /=; lra.
  exact: (ball_center x (mkposreal Hre)).
Qed.

Lemma cball_sym x y r : cball x r y -> cball y r x.
Proof.
  move => Hr e.
  apply ball_sym, Hr.
Qed.

Lemma cball_triangle x y z r1 r2 : cball x r1 y -> cball y r2 z -> cball x (r1+r2) z.
Proof.
  move => Hr1 Hr2 e.
  have He2 : 0 < e/2 by case: e => e He /=; lra.
  replace (r1+r2+e) with ((r1+e/2) + (r2+e/2)).
  eapply ball_triangle; [apply Hr1 | apply Hr2].
  rewrite /=; lra.
Qed.

Lemma ball_cball_subset x r : subset (ball x r) (cball x r).
Proof. move => y Hy e; eapply ball_le; last apply Hy; move: (cond_pos e); lra. Qed.

Lemma cball_ball_subset x r1 r2 : r1 < r2 -> subset (cball x r1) (ball x r2).
Proof.
  move => Hr y Hy.
  have He : 0 < r2-r1 by lra.
  set e := mkposreal He.
  replace r2 with (r1+e); last by rewrite /=; ring.
  apply Hy.
Qed.

Lemma cball_close x y r : (forall e : posreal, exists z, cball x r z /\ ball y e z) -> cball x r y.
Proof.
  move => H e.
  replace (r+e) with (r+e/2+e/2); last lra.
  move: (H (e/2)%:posreal) => [z /= [Hxz /ball_sym Hyz]].
  by eapply ball_triangle.
Qed.

Lemma cball_0_close x y : close x y <-> cball x 0 y.
Proof.
  split.
+ move => H e; rewrite Rplus_0_l; exact: H.
+ move => H e; move: (H e); by rewrite Rplus_0_l.
Qed.


End Cball.


Notation ball0 := (@ball (AbsRing_UniformSpace _) zero).
Notation cball0 := (@cball (AbsRing_UniformSpace _) zero).

Section AbsRing_cball.
Variable (K : AbsRing).
Implicit Types (x y : K).

Lemma AbsRing_ballE x y r : ball x r y <-> abs (minus y x) < r.
Proof. by []. Qed.

Lemma AbsRing_ball0E x r : ball0 r x <-> abs x < r.
Proof. by rewrite /ball /= /AbsRing_ball minus_zero_r. Qed.

Lemma AbsRing_cballE x y r : cball x r y <-> abs (minus y x) <= r.
Proof.
  split.
+ move => H; ecase (Rle_lt_dec _ _) => H'; first exact: H'.
  have He : 0 < abs (minus y x) - r by lra. 
  set e := mkposreal He.
  move: (H e) => /AbsRing_ballE HH; move: HH; rewrite /=; lra.
+ move => H e; apply AbsRing_ballE; case: e => e He /=; lra.
Qed.

Lemma AbsRing_cball0E x r : cball0 r x <-> abs x <= r.
Proof.
  replace (abs x) with (abs (minus x zero)); last by rewrite minus_zero_r.
  apply AbsRing_cballE.
Qed.

End AbsRing_cball.


Section R_cball.
Implicit Types (x y : R).

Lemma R_ballE x y r : ball x r y <-> Rabs (y - x) < r.
Proof. by []. Qed.

Lemma R_ball0E x r : ball0 r x <-> Rabs x < r.
Proof. exact: AbsRing_ball0E. Qed.

Lemma R_cballE x y r : cball x r y <-> Rabs (y - x) <= r.
Proof. exact: AbsRing_cballE. Qed.

Lemma R_cball0E x r : cball0 r x <-> Rabs x <= r.
Proof. exact: AbsRing_cball0E. Qed.

End R_cball.


