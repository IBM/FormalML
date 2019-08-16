Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Coquelicot.Coquelicot.
Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Reals.R_sqrt.
Require Import Rtrigo_def.
Require Import Rtrigo1.
Require Import Reals.Rtrigo_calc.
Require Import Lra.

Require Import LibUtils.

Set Bullet Behavior "Strict Subproofs".

Lemma sqrt2_neq0 :
  sqrt 2 <> 0.
Proof.
  apply Rgt_not_eq.
  apply Rlt_gt.
  apply Rlt_sqrt2_0.
Qed.

Lemma sqrt_2PI_nzero : sqrt(2*PI) <> 0.
Proof.
  assert (PI > 0) by apply PI_RGT_0.

  apply Rgt_not_eq.
  apply sqrt_lt_R0.
  lra.
Qed.

Lemma ex_Rbar_plus_Finite_l x y : ex_Rbar_plus (Finite x) y.
  destruct y; simpl; trivial.
Qed.

Lemma ex_Rbar_plus_Finite_r x y : ex_Rbar_plus x (Finite y).
  destruct x; simpl; trivial.
Qed.

Lemma ex_Rbar_minus_Finite_l x y : ex_Rbar_minus (Finite x) y.
  destruct y; simpl; trivial.
Qed.

Lemma ex_Rbar_minus_Finite_r x y : ex_Rbar_minus x (Finite y).
  destruct x; simpl; trivial.
Qed.