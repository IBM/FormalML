(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Local Set Warnings "ambiguous-path, typechecker".
Require Export Reals Coquelicot.Coquelicot.

Open Scope R_scope.

Section RC.

(** If a degree-2 polynomial is always nonnegative, its dicriminant is nonpositive *)

Lemma discr_neg: forall a b c,
  (forall x, 0 <= a*x*x+b*x+c) ->
     b*b-4*a*c <= 0.
intros.
case (Req_dec a 0); intros H'.
cut (b=0).
intros H1; rewrite H'; rewrite H1.
right; ring.
case (Req_dec b 0); trivial; intros.
absurd (0 <= a*((-c-1)/b)*((-c-1)/b)+b*((-c-1)/b)+c).
2: apply H.
apply Rlt_not_le.
rewrite H'; apply Rle_lt_trans with (-1).
right; field; trivial.
apply Ropp_lt_gt_0_contravar; apply Rlt_gt; auto with real.
assert (0 <= c).
apply Rle_trans with (a*0*0+b*0+c);[idtac|right; ring].
apply H.
assert (0 < a).
cut (0 <= a).
intros T; case T;auto with real.
intros T'; absurd (a=0); auto.
case (Req_dec b 0); intros.
case (Rle_or_lt 0 a); trivial; intros.
absurd (0 <= a* sqrt ((c+1)/(-a)) * sqrt ((c+1)/(-a)) +b*sqrt ((c+1)/(-a))+c).
2: apply H.
apply Rlt_not_le.
rewrite H1; ring_simplify ( 0 * sqrt ((c + 1) / - a)).
rewrite Rmult_assoc.
rewrite sqrt_sqrt.
apply Rle_lt_trans with (-1).
right; field; auto with real.
apply Ropp_lt_gt_0_contravar; apply Rlt_gt; auto with real.
unfold Rdiv; apply Rmult_le_pos; auto with real.
case H0; intros.
apply Rmult_le_reg_l with (c*c/(b*b)).
unfold Rdiv; apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat; trivial.
apply Rinv_0_lt_compat.
fold (Rsqr b); auto with real.
ring_simplify.
apply Rle_trans with (a*(-c/b)*(-c/b)+b*(-c/b)+c).
apply H.
right; field; trivial.
apply Rmult_le_reg_l with (b*b).
fold (Rsqr b); auto with real.
ring_simplify.
apply Rle_trans with (Rsqr b); auto with real.
apply Rplus_le_reg_l with (-Rsqr b); ring_simplify.
apply Rle_trans with (a*(-b)*(-b)+b*(-b)+c).
apply H.
rewrite <- H2; unfold Rsqr; right; ring.
case (Rle_or_lt (b * b - 4 * a * c) 0); trivial.
intros H2.
absurd ( 0 <= a * (-b/(2*a)) * (-b/(2*a)) + b * (-b/(2*a)) + c).
apply Rlt_not_le.
replace (a * (- b / (2*a)) * (- b / (2*a)) + b * (- b / (2*a)) + c) with
  (-b*b/(4*a)+c).
apply Rmult_lt_reg_l with (4*a).
repeat apply Rmult_lt_0_compat; auto with real.
apply Rplus_lt_reg_r with (b*b-4*a*c).
apply Rle_lt_trans with 0%R.
right; field; auto.
apply Rlt_le_trans with (1:=H2); right; ring.
field; auto.
apply H.
Qed.

Lemma contraction_lt_any: forall k d, 0 <= k < 1 -> 0 < d -> exists N, pow k N < d.
Proof.
intros k d Hk Hd.
case (proj1 Hk); intros Hk'.
(* 0 < k *)
assert (ln k < 0).
rewrite <- ln_1.
apply ln_increasing; try apply Hk; assumption.
exists (Z.abs_nat (up (ln d / ln k))).
apply ln_lt_inv; try assumption.
now apply pow_lt.
rewrite <- Rpower_pow; trivial.
unfold Rpower.
rewrite ln_exp.
apply Rmult_lt_reg_l with (- /ln k).
apply Ropp_gt_lt_0_contravar.
now apply Rinv_lt_0_compat.
apply Rle_lt_trans with (-(INR (Z.abs_nat (up (ln d / ln k))))).
right; field.
now apply Rlt_not_eq.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_contravar.
generalize (archimed (ln d / ln k)); intros (Y1,_).
rewrite Rmult_comm.
apply Rlt_le_trans with (1:=Y1).
generalize (up (ln d / ln k)); clear; intros x.
rewrite INR_IZR_INZ, Zabs2Nat.id_abs.
apply IZR_le.
case (Zabs_spec x); intros (T1,T2); rewrite T2; auto with zarith.
(* k = 0 *)
exists 1%nat.
rewrite <- Hk';simpl.
now rewrite Rmult_0_l.
Qed.

Lemma contraction_lt_any': forall k d, 0 <= k < 1 -> 0 < d -> exists N, (0 < N)%nat /\ pow k N < d.
Proof.
intros k d H1 H2.
destruct (contraction_lt_any k d H1 H2) as (N,HN).
case_eq N.
intros H3; exists 1%nat; split.
now apply le_n.
rewrite H3 in HN; simpl in HN.
simpl; rewrite Rmult_1_r.
now apply Rlt_trans with 1.
intros m Hm.
exists N; split; try assumption.
rewrite Hm.
now auto with arith.
Qed.

Lemma Rinv_le_cancel: forall x y : R, 0 < y -> / y <= / x -> x <= y.
Proof.
intros x y H1 H2.
case (Req_dec x 0); intros Hx.
rewrite Hx; now left.
destruct H2.
left; now apply Rinv_lt_cancel.
right; rewrite <- Rinv_involutive.
2: now apply Rgt_not_eq.
rewrite H.
now apply sym_eq, Rinv_involutive.
Qed.

Lemma Rlt_R1_pow: forall x n, 0 <= x < 1 -> (0 < n)%nat -> x ^ n < 1.
Proof.
intros x n (Hx1,Hx2) Hn.
case (Req_dec x 0); intros H'.
rewrite H', pow_i; try assumption.
apply Rlt_0_1.
apply Rinv_lt_cancel.
apply Rlt_0_1.
rewrite Rinv_1.
rewrite Rinv_pow; try assumption.
apply Rlt_pow_R1; try assumption.
rewrite <- Rinv_1.
apply Rinv_lt_contravar; try assumption.
rewrite Rmult_1_r.
destruct Hx1; trivial.
contradict H; now apply not_eq_sym.
Qed.

Lemma Rle_pow_le: forall (x : R) (m n : nat), 0 < x <= 1 -> (m <= n)%nat -> x ^ n <= x ^ m.
Proof.
intros x m n (Hx1,Hx2) H.
apply Rinv_le_cancel.
now apply pow_lt.
rewrite 2!Rinv_pow; try now apply Rgt_not_eq.
apply Rle_pow; try assumption.
rewrite <- Rinv_1.
apply Rinv_le_contravar; try assumption.
Qed.

Lemma is_finite_betw: forall x y z,
  Rbar_le (Finite x) y -> Rbar_le y (Finite z) -> is_finite y.
Proof.
intros x y z; destruct y; easy.
Qed.

Lemma Rplus_plus_reg_l : forall (a b c:R), b = c -> plus a b = a + c.
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma Rplus_plus_reg_r : forall a b c, b = c -> plus b a = c + a.
Proof.
intros. rewrite H. reflexivity.
Qed.

Context {E : NormedModule R_AbsRing}.

Lemma norm_scal_R: forall l (x:E), norm (scal l x) = abs l * norm x.
Proof.
intros l x.
apply Rle_antisym; try apply norm_scal.
case (Req_dec l 0); intros V.
rewrite V; unfold abs; simpl.
rewrite Rabs_R0, Rmult_0_l.
apply norm_ge_0.
apply Rmult_le_reg_l with (abs (/l)).
unfold abs; simpl.
apply Rabs_pos_lt.
now apply Rinv_neq_0_compat.
apply Rle_trans with (norm x).
rewrite <- Rmult_assoc.
unfold abs; simpl.
rewrite <- Rabs_mult.
rewrite Rinv_l; trivial.
rewrite Rabs_R1, Rmult_1_l.
apply Rle_refl.
apply Rle_trans with (norm (scal (/l) (scal l x))).
right; apply f_equal.
rewrite scal_assoc.
apply trans_eq with (scal one x).
apply sym_eq, scal_one.
apply f_equal2; trivial.
unfold one, mult; simpl.
now field.
apply (norm_scal (/l) (scal l x)).
Qed.

Lemma sum_n_eq_zero: forall m (L:nat -> E),
  (forall i, (i <= m)%nat -> L i = zero) ->
   sum_n L m = zero.
Proof.
intros m L H.
apply trans_eq with (sum_n (fun n => zero) m).
now apply sum_n_ext_loc.
clear; induction m.
now rewrite sum_O.
rewrite sum_Sn, IHm.
apply plus_zero_l.
Qed.

End RC.
