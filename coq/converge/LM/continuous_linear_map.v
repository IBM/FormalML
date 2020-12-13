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

Require Export linear_map.
Require Export fixed_point.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Decidable.

(** Properties of linear_maps of NormedModule *)

Section DefsLin.

Context {E : NormedModule R_AbsRing}.
Context {F : NormedModule R_AbsRing}.

Definition is_bounded (f:E->F) :=
    exists M : R, 0 <= M /\
         (forall x : E, norm (f x) <= M * norm x).

Definition is_bounded_linear_mapping (f : E -> F) :=
     is_linear_mapping f /\ is_bounded f.

End DefsLin.

(** Decidability Is_only_zero_set *)

Section IOZ.

Variable E : NormedModule R_AbsRing.

Definition Is_only_zero_set: Prop :=
  (Empty (fun x => exists u:E, u <> zero /\ x = norm u)).

Lemma Is_only_zero_set_correct1:
   Is_only_zero_set -> forall x:E, x = zero.
Proof.
unfold Is_only_zero_set.
intros H1.
specialize (Empty_correct_1 _ H1).
intros H2.
intros x.
specialize (H2 (norm x)).
assert (norm x = 0).
case (Req_dec (norm x) 0); trivial.
intros H3.
elimtype False.
apply H2.
exists x.
split; trivial.
intros H4; apply H3.
rewrite H4.
apply norm_zero.
apply norm_eq_zero.
exact H.
Qed.

Lemma Is_only_zero_set_correct2:
   (forall (x:E), x = zero) -> Is_only_zero_set.
Proof.
intros H.
unfold Is_only_zero_set.
apply Empty_correct_2.
intros x (u,(H1,H2)).
apply H1.
apply H.
Qed.

Lemma Is_only_zero_set_correct3:
  ~ Is_only_zero_set -> ~ forall (x:E), x = zero.
Proof.
intros H1 H2.
apply H1.
now apply Is_only_zero_set_correct2.
Qed.

Lemma Is_only_zero_set_correct4: forall A,
  ~ Is_only_zero_set -> decidable A ->
     ((exists (x:E), x <> zero) -> A) -> A.
Proof.
intros A H1 H2 H3.
case H2; trivial.
intros H4.
elimtype False.
specialize (Is_only_zero_set_correct3 H1).
intros H5.
assert (~(exists x : E, x <> zero)).
intros T.
now apply H4, H3.
apply H5.
intros x.
case (Req_dec (norm x) 0).
apply norm_eq_zero.
intros H6.
elimtype False.
apply H.
exists x.
intros H7; apply H6.
rewrite H7.
apply norm_zero.
Qed.

Lemma Is_only_zero_set_dec:
  {~Is_only_zero_set}+{Is_only_zero_set}.
Proof.
unfold Is_only_zero_set.
apply Empty_dec.
Qed.

End IOZ.

(** Continuous Linear Maps *)

Section ContinuousLinearMap.

Context {E : NormedModule R_AbsRing}.
Context {F : NormedModule R_AbsRing}.

(** Additional properties *)

Lemma norm_gt_0: forall (x:E),  x <> zero -> 0 < norm x.
Proof.
intros x Hx.
case (norm_ge_0 x); intros H; trivial.
absurd (x = zero); trivial.
now apply norm_eq_zero.
Qed.

Lemma is_zero_dec: forall (x:E), x = zero \/ x <> zero.
Proof.
intros x.
case (Req_dec (norm x) 0); intros Hx.
left.
now apply norm_eq_zero.
right.
intros H1; apply Hx.
now rewrite H1 norm_zero.
Qed.

Lemma norm_unit_vector: forall (u:E), u <> zero -> norm (scal (/norm u) u) = 1.
Proof.
intros u Hu.
assert (0 < norm u) by apply (norm_gt_0 _ Hu).
apply trans_eq with (abs (/norm u) * norm u).
apply (norm_scal_R (/norm u) u).
unfold abs; simpl.
rewrite Rabs_right.
field.
now apply Rgt_not_eq.
left; now apply Rinv_0_lt_compat.
Qed.

Lemma norm_of_image_of_unit_vector: forall (f:E->F), forall (u:E), is_linear_mapping f -> u <> zero ->
   norm (f (scal (/norm u) u)) = norm (f u) / norm u.
Proof.
intros f u (_,Hf) Hu.
rewrite Hf.
apply trans_eq with (abs (/norm u) * norm (f u)).
apply (norm_scal_R (/norm u) _).
unfold abs; simpl; rewrite Rabs_right.
unfold Rdiv; apply Rmult_comm.
left; apply Rinv_0_lt_compat.
now apply norm_gt_0.
Qed.

Lemma norm_of_image_of_unit_vector': forall (f:E->F), forall (u:E),
  is_linear_mapping f ->
    norm (f (scal (/norm u) u)) * norm u = norm (f u).
Proof.
intros f u Hf.
case (is_zero_dec u); intros Hu.
rewrite Hu norm_zero.
rewrite Rmult_0_r.
rewrite is_linear_mapping_zero; try assumption.
now rewrite <- (@norm_zero _ F).
rewrite (proj2 Hf).
apply trans_eq with ((abs (/norm u) * norm (f u))*norm u).
apply Rmult_eq_compat_r.
apply (norm_scal_R (/norm u) _).
unfold abs; simpl; rewrite Rabs_right.
unfold Rdiv; field.
apply Rgt_not_eq; now apply norm_gt_0.
left; apply Rinv_0_lt_compat.
now apply norm_gt_0.
Qed.

(** Operator norms *)

Definition operator_norm (f:E->F) : Rbar :=
   match Is_only_zero_set_dec E with
    | left _ => Lub_Rbar (fun x => exists u:E, u <> zero /\
                   x = norm (f u) / norm u)
    | right _ => 0
  end.

Lemma operator_norm_ge_0: forall f,
  Rbar_le 0 (operator_norm f).
Proof.
intros f.
unfold operator_norm.
case Is_only_zero_set_dec.
2: intros _; apply Rle_refl.
intros H.
apply (Is_only_zero_set_correct4 E); trivial.
unfold decidable.
case (Rbar_le_dec 0
   (Lub_Rbar (fun x : R => exists u : E, u <> zero /\ x = norm (f u) / norm u))).
now left.
now right.
intros (x,Hx).
apply Rbar_le_trans with (norm (f x)/norm x).
apply Rmult_le_pos.
apply norm_ge_0.
left; apply Rinv_0_lt_compat.
now apply norm_gt_0.
apply Lub_Rbar_correct.
exists x.
now split.
Qed.

Lemma operator_norm_ge_0': forall f,
  0 <= (operator_norm f).
Proof.
intros f.
generalize (operator_norm_ge_0 f).
destruct (operator_norm f); try easy.
intros _; apply Rle_refl; simpl.
Qed.

Lemma operator_norm_helper:
    forall f, is_linear_mapping f -> is_finite (operator_norm f) ->
       (Is_only_zero_set E/\ operator_norm f = 0)
     \/ (~Is_only_zero_set E/\ forall u, norm (f u) <= operator_norm f * norm u).
Proof.
intros f Hf1; unfold operator_norm.
case Is_only_zero_set_dec; intros K Hf2.
right.
split; try exact K.
intros u.
case (is_zero_dec u); intros Hu.
rewrite Hu.
rewrite is_linear_mapping_zero; try assumption.
rewrite 2!norm_zero.
right; ring.
apply Rmult_le_reg_r with (/ norm u).
apply Rinv_0_lt_compat.
now apply norm_gt_0.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
assert (Y: Rbar_le (norm (f u) * / norm u)
    (Lub_Rbar
     (fun x : R => exists u0 : E, u0 <> zero /\ x = norm (f u0) / norm u0))).
apply Lub_Rbar_correct.
exists u; split; easy.
rewrite <- Hf2 in Y.
easy.
now apply Rgt_not_eq, norm_gt_0.
left.
split; easy.
Qed.

Lemma operator_norm_helper':
    forall f, is_finite (operator_norm f) ->
        (forall u, u <> zero -> norm (f u) <= operator_norm f * norm u).
Proof.
intros f; unfold operator_norm.
case Is_only_zero_set_dec; intros K Hf1 u Hu.
apply Rmult_le_reg_r with (/ norm u).
apply Rinv_0_lt_compat.
now apply norm_gt_0.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
assert (Y: Rbar_le (norm (f u) * / norm u)
    (Lub_Rbar
     (fun x : R => exists u0 : E, u0 <> zero /\ x = norm (f u0) / norm u0))).
apply Lub_Rbar_correct.
exists u; split; easy.
rewrite <- Hf1 in Y.
easy.
now apply Rgt_not_eq, norm_gt_0.
absurd (u=zero); try assumption.
now apply Is_only_zero_set_correct1.
Qed.

Lemma operator_norm_helper2:
    forall f, is_finite (operator_norm f) ->
       (Is_only_zero_set E /\ operator_norm f = 0)
     \/ (~Is_only_zero_set E /\ forall M, 0 <= M ->
         (forall u, u <> zero -> norm (f u) <= M * norm u) ->
            operator_norm f <= M).
Proof.
intros f; unfold operator_norm.
case Is_only_zero_set_dec; intros K Hf2.
(* . *)
right.
split; try exact K.
intros M HM1 HM2.
assert (Y: Rbar_le (Lub_Rbar (fun x : R => exists u : E, u <> zero /\ x = norm (f u) / norm u)) M).
apply Lub_Rbar_correct.
intros x (u,(Hu1,Hu2)).
assert (x <= M); try easy.
rewrite Hu2; apply Rmult_le_reg_r with (norm u).
now apply norm_gt_0.
apply Rle_trans with (2:=HM2 u Hu1).
right; field.
now apply Rgt_not_eq, norm_gt_0.
rewrite <- Hf2 in Y;easy.
(* . *)
left.
split; easy.
Qed.

Lemma operator_norm_helper3:
    forall f, forall M, 0 <= M ->
       (forall u, u <> zero ->  norm (f u) <= M * norm u) ->
         is_finite (operator_norm f).
Proof.
intros f M H1 H2.
apply is_finite_betw with 0 M.
apply operator_norm_ge_0.
unfold operator_norm.
case Is_only_zero_set_dec; intros H.
apply Lub_Rbar_correct.
intros x (u,(Hu1,Hu2)).
assert (x <= M); try easy.
rewrite Hu2.
apply Rmult_le_reg_r with (norm u).
now apply norm_gt_0.
apply Rle_trans with (norm (f u)).
right; field.
now apply Rgt_not_eq, norm_gt_0.
now apply H2.
easy.
Qed.

Lemma operator_norm_helper3':
    forall f, forall M, 0 <= M ->
       (forall u, u <> zero -> norm (f u) <= M * norm u) ->
         (operator_norm f <= M).
Proof.
intros f M H1 H2.
case operator_norm_helper2 with f.
now apply operator_norm_helper3 with M.
intros (_,K); now rewrite K.
intros (_,K); apply K; easy.
Qed.

(** Equivalent definitions of continuity for linear maps *)

(** Equivalence of several assertions for continuity :
   More precisely, given (f:E->F),  is_linear_mapping f, then
   the followings are equivalent:
  (1) continuous f zero
  (2) forall (x:E), continuous f x
  (3) forall (eps:posreal), exists (delta:posreal), forall x y,
      ball x delta y -> ball (f x) eps (f y)
     {uniform continuity}
  (4) exists k, is_Lipschitz f k
  (5) is_bounded f
  (6) is_finite (operator_norm f)
  (7) exists M : R, 0 <= M /\
         (forall x : E, norm x = 1 -> norm (f x) <= M).
  (8) exists M : R, 0 <= M /\
         (forall x : E, norm x <= 1 -> norm (f x) <= M).
*)

(* the is_linear_mapping hypothesis is sometimes useless *)
Lemma continuous_linear_map_2_1:
   forall (f:E->F),
   (forall (x:E), continuous f x) ->
      continuous f zero.
Proof.
intros f H; apply H.
Qed.

Lemma continuous_linear_map_3_2:
  forall (f:E->F),
    (forall (eps:posreal), exists (delta:posreal), forall x y,
       ball x delta y -> ball (f x) eps (f y)) ->
    (forall (x:E), continuous f x).
Proof.
intros f H x.
intros P (eps,HP).
destruct (H eps) as (d,Hd).
exists d.
intros y Hy.
apply HP.
now apply Hd.
Qed.

Lemma continuous_linear_map_4_3:
  forall (f:E->F),
    (exists k, is_Lipschitz f k) ->
    (forall (eps:posreal), exists (delta:posreal), forall x y,
       ball x delta y -> ball (f x) eps (f y)).
Proof.
intros f (k,(Hk1,Hk2)) eps.
case Hk1; intros Hk1'.
(* *)
assert (Y: 0 < eps / k).
apply Rdiv_lt_0_compat; try assumption.
apply cond_pos.
exists (mkposreal _ Y).
intros x y H.
replace (pos eps) with (k*(eps/k)).
apply Hk2; try assumption.
field.
now apply Rgt_not_eq.
(* k = 0 *)
exists (mkposreal _ Rlt_0_1).
intros x y H.
apply ball_le with (k*1).
rewrite <- Hk1', Rmult_0_l; left; apply cond_pos.
apply Hk2; try assumption.
apply Rlt_0_1.
Qed.

Lemma continuous_linear_map_5_4:
   forall (f:E->F), is_linear_mapping f ->
     is_bounded f ->
      (exists k, is_Lipschitz f k).
Proof.
intros f Hf (k,(Hk1,Hk2)).
exists ((k+1)*(@norm_factor _ E))%R; split.
apply Rmult_le_pos.
apply Rplus_le_le_0_compat; try apply Rle_0_1; assumption.
left; apply norm_factor_gt_0.
intros x y r Hr H.
apply norm_compat1.
apply Rle_lt_trans with (norm (f (minus y x))).
right; apply f_equal.
unfold minus.
rewrite (proj1 Hf); apply f_equal.
apply sym_eq.
now apply (is_linear_mapping_opp f).
apply Rle_lt_trans with (1:=Hk2 _).
rewrite Rmult_assoc.
apply Rle_lt_trans with (k*((@norm_factor _ E)*r)).
apply Rmult_le_compat_l; try assumption.
left.
now apply (norm_compat2 x y (mkposreal _ Hr)).
apply Rmult_lt_compat_r.
apply Rmult_lt_0_compat; trivial.
apply norm_factor_gt_0.
apply Rplus_lt_reg_l with (-k).
ring_simplify.
apply Rlt_0_1.
Qed.

Lemma continuous_linear_map_6_5:
   forall (f:E->F), is_linear_mapping f ->
   is_finite (operator_norm f) ->
   is_bounded f.
Proof.
intros f Hf H1.
exists (real (operator_norm f)).
split.
+ apply operator_norm_ge_0'.
+ intros x.
  case (operator_norm_helper f); try assumption.
  * intros (H2,H3).
    rewrite (Is_only_zero_set_correct1 E H2 x).
    rewrite (is_linear_mapping_zero _ Hf).
    rewrite 2!norm_zero.
    right; ring.
  * intros (H2,H3); apply H3.
Qed.

Lemma continuous_linear_map_7_6:
   forall (f:E->F), is_linear_mapping f ->
    (exists M : R, 0 <= M /\
         (forall x : E, norm x = 1 -> norm (f x) <= M)) ->
   is_finite (operator_norm f).
Proof.
intros f Hf (M,(HM1,HM2)).
apply is_finite_betw with 0 M.
apply operator_norm_ge_0.
unfold operator_norm.
case Is_only_zero_set_dec; intros H.
apply Lub_Rbar_correct.
intros x (u,(Hu1,Hu2)).
assert (x <= M); try easy.
apply Rle_trans with (norm (f (scal (/ norm u) u))).
rewrite Hu2.
right.
now apply sym_eq, norm_of_image_of_unit_vector.
apply HM2.
rewrite norm_scal_R.
unfold abs; simpl; rewrite Rabs_right.
field.
now apply Rgt_not_eq, norm_gt_0.
left.
now apply Rinv_0_lt_compat, norm_gt_0.
easy.
Qed.

Lemma continuous_linear_map_8_7:
   forall (f:E->F),
    (exists M : R, 0 <= M /\
         (forall x : E, norm x <= 1 -> norm (f x) <= M)) ->
    (exists M : R, 0 <= M /\
         (forall x : E, norm x = 1 -> norm (f x) <= M)).
Proof.
intros f (M,(H1,H2)).
exists M; split; try assumption.
intros x Hx; apply H2.
now right.
Qed.

Lemma continuous_linear_map_1_8:
   forall (f:E->F), is_linear_mapping f ->
     continuous f zero ->
   (exists M : R, 0 <= M /\
          (forall x : E, norm x <= 1 -> norm (f x) <= M)).
Proof.
intros f Hf Cf.
specialize (Cf (fun x => (norm x <= @norm_factor _ F))).
destruct Cf as (e,He).
rewrite is_linear_mapping_zero; try assumption.
exists (mkposreal _ Rlt_0_1).
intros y Hy.
rewrite <- Rmult_1_r.
replace y with (minus y zero) by apply minus_zero_r.
replace 1 with (pos (mkposreal _ Rlt_0_1)) by reflexivity.
left; now apply norm_compat2.
exists (@norm_factor _ F/e*2); split.
left; apply Rmult_lt_0_compat.
apply Rdiv_lt_0_compat.
apply norm_factor_gt_0.
apply cond_pos.
apply Rlt_0_2.
intros x Hx.
apply Rmult_le_reg_l with (e/2).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_0_2.
apply Rle_trans with (@norm_factor _ F).
2: right; field.
2: apply Rgt_not_eq, cond_pos.
apply Rle_trans with (norm (f (scal (e/2) x))).
rewrite (proj2 Hf).
rewrite norm_scal_R.
right; apply f_equal2; trivial.
unfold abs; simpl; rewrite Rabs_right; trivial.
left;apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_0_2.
apply He.
apply norm_compat1.
rewrite minus_zero_r.
rewrite norm_scal_R.
case (Rle_lt_or_eq_dec 0 (norm x)).
apply norm_ge_0.
intros Hx'.
unfold abs; simpl; rewrite Rabs_right.
rewrite <- Rmult_1_r.
unfold Rdiv; rewrite Rmult_assoc.
apply Rmult_lt_compat_l.
apply cond_pos.
apply Rlt_le_trans with (2:=Hx).
rewrite <- Rmult_1_l.
apply Rmult_lt_compat_r; try assumption.
rewrite <- Rinv_1.
apply Rinv_1_lt_contravar.
apply Rle_refl.
apply Rlt_plus_1.
left; apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_0_2.
intros Hx'; rewrite <- Hx', Rmult_0_r.
apply cond_pos.
Qed.

End ContinuousLinearMap.

(** Finiteness properties of operator norm *)

Section avantV.

Context {E : NormedModule R_AbsRing}.
Context {F : NormedModule R_AbsRing}.

Lemma is_finite_norm_zero:
   is_finite (operator_norm (fun (x:E) => @zero F)).
Proof.
apply operator_norm_helper3 with 0.
apply Rle_refl.
intros u; rewrite norm_zero.
right; ring.
Qed.

Lemma operator_norm_zero:
   real (operator_norm (fun (x:E) => @zero F)) = 0.
Proof.
apply Rle_antisym.
apply operator_norm_helper3'.
apply Rle_refl.
intros u; rewrite norm_zero.
right; ring.
apply operator_norm_ge_0'.
Qed.

Lemma is_finite_operator_norm_plus: forall (f g:E->F),
    is_finite (operator_norm f) ->
    is_finite (operator_norm g) ->
    is_finite (operator_norm (plus f g)).
Proof.
intros f g H1 H2.
apply operator_norm_helper3 with (operator_norm f + operator_norm g).
apply Rplus_le_le_0_compat; apply operator_norm_ge_0'.
intros u Hu; unfold plus; simpl; unfold fct_plus.
apply Rle_trans with (norm (f u)+norm (g u)).
apply: norm_triangle.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat; apply operator_norm_helper'; assumption.
Qed.

Lemma is_finite_operator_norm_opp: forall (f:E->F),
    is_finite (operator_norm f) ->
    is_finite (operator_norm (opp f)).
Proof.
intros f H.
apply operator_norm_helper3 with (operator_norm f).
apply operator_norm_ge_0'.
intros u; rewrite norm_opp.
now apply operator_norm_helper'.
Qed.

Lemma is_finite_operator_norm_scal: forall l, forall (f:E->F),
    is_finite (operator_norm f) ->
    is_finite (operator_norm (scal l f)).
Proof.
intros l f H.
apply operator_norm_helper3 with (Rabs l * operator_norm f).
apply Rmult_le_pos.
apply Rabs_pos.
apply operator_norm_ge_0'.
intros u Hu.
unfold scal; simpl; unfold fct_scal.
apply Rle_trans with (1:=norm_scal l (f u)).
unfold abs; simpl; rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rabs_pos.
now apply operator_norm_helper'.
Qed.

Lemma operator_norm_triangle: forall (f g:E->F),
  is_finite (operator_norm f) ->  is_finite (operator_norm g) ->
    operator_norm (plus f g) <= operator_norm f + operator_norm g.
Proof.
intros f g H1 H2.
apply operator_norm_helper3'.
apply Rplus_le_le_0_compat; apply operator_norm_ge_0'.
intros u Hu; unfold plus; simpl; unfold fct_plus.
apply Rle_trans with (norm (f u)+norm (g u)).
apply: norm_triangle.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat; apply operator_norm_helper'; assumption.
Qed.

Lemma operator_norm_opp: forall (f:E->F),
   operator_norm (opp f) = operator_norm f.
Proof.
intros f.
unfold operator_norm.
case Is_only_zero_set_dec; try easy.
intros H.
apply Lub_Rbar_eqset.
intros x; split.
intros (u,(Hu1,Hu2)).
exists u; split; trivial.
rewrite Hu2.
unfold opp; simpl; unfold fct_opp; now rewrite norm_opp.
intros (u,(Hu1,Hu2)).
exists u; split; trivial.
rewrite Hu2.
unfold opp; simpl; unfold fct_opp; now rewrite norm_opp.
Qed.

Lemma operator_norm_scal: forall l, forall (f:E->F),
    is_linear_mapping f -> is_finite (operator_norm f) ->
    real (operator_norm (scal l f)) = Rabs l * operator_norm f.
Proof.
intros l f H1 H2.
apply Rle_antisym.
(* *)
apply operator_norm_helper3'.
apply Rmult_le_pos.
apply Rabs_pos.
apply operator_norm_ge_0'.
intros u Hu.
unfold scal; simpl; unfold fct_scal.
apply Rle_trans with (1:=norm_scal l (f u)).
unfold abs; simpl; rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rabs_pos.
now apply operator_norm_helper'.
(* *)
case (Req_dec l 0); intros Hl.
rewrite Hl Rabs_R0 Rmult_0_l.
apply operator_norm_ge_0'.
assert (0 < Rabs l) by now apply Rabs_pos_lt.
apply Rmult_le_reg_l with (/Rabs l).
now apply Rinv_0_lt_compat.
rewrite <- Rmult_assoc; rewrite Rinv_l.
2: now apply Rgt_not_eq.
rewrite Rmult_1_l.
apply operator_norm_helper3'.
apply Rmult_le_pos.
left; now apply Rinv_0_lt_compat.
apply operator_norm_ge_0'.
intros u Hu.
apply Rmult_le_reg_l with (Rabs l); try assumption.
apply Rle_trans with (operator_norm (scal l f) * norm u).
apply Rle_trans with (norm (scal l f u)).
unfold scal; simpl; unfold fct_scal.
right; apply sym_eq, norm_scal_R.
apply operator_norm_helper'; try assumption.
now apply is_finite_operator_norm_scal.
rewrite <- 2!Rmult_assoc.
rewrite Rinv_r.
right; rewrite Rmult_assoc; apply sym_eq, Rmult_1_l.
now apply Rgt_not_eq.
Qed.

(** Composition and operator norm *)

Context {G : NormedModule R_AbsRing}.

Lemma is_linear_mapping_compose: forall (f:E->F), forall (g:F->G),
    is_linear_mapping f -> is_linear_mapping g ->
      is_linear_mapping (fun x => g (f x)).
Proof.
intros f g (H1,K1) (H2,K2); split.
intros x y; now rewrite H1 H2.
intros x l; now rewrite K1 K2.
Qed.

Lemma operator_norm_compose:
  forall (f:E -> F), forall (g:F -> G), (g zero = zero) ->
   is_finite (operator_norm f) -> is_finite (operator_norm g) ->
     operator_norm (fun (x:E) => g (f x)) <= operator_norm g * operator_norm f.
Proof.
intros f g H H1 H2.
apply operator_norm_helper3'.
apply Rmult_le_pos; apply operator_norm_ge_0'.
intros u Hu.
case (is_zero_dec (f u)); intros L.
 + rewrite L H norm_zero.
   apply Rmult_le_pos.
   apply Rmult_le_pos; apply operator_norm_ge_0'.
   apply norm_ge_0.
 + apply Rle_trans with (operator_norm g * norm (f u)).
   apply operator_norm_helper'; assumption.
   rewrite Rmult_assoc.
   apply Rmult_le_compat_l.
   apply operator_norm_ge_0'.
   apply operator_norm_helper'; assumption.
Qed.

Lemma is_finite_operator_norm_compose: forall (f:E->F), forall (g:F->G),
    (g zero = zero) -> is_finite (operator_norm f) -> is_finite (operator_norm g) ->
       is_finite (operator_norm (fun x => g (f x))).
Proof.
intros f g H H1 H2.
apply operator_norm_helper3 with (operator_norm g * operator_norm f).
apply Rmult_le_pos; apply operator_norm_ge_0'.
intros u Hu.
case (is_zero_dec (f u)); intros L.
 + rewrite L H norm_zero.
   apply Rmult_le_pos.
   apply Rmult_le_pos; apply operator_norm_ge_0'.
   apply norm_ge_0.
 + apply Rle_trans with (operator_norm g * norm (f u)).
   apply operator_norm_helper'; assumption.
   rewrite Rmult_assoc.
   apply Rmult_le_compat_l.
   apply operator_norm_ge_0'.
   apply operator_norm_helper'; assumption.
Qed.

End avantV.

Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

Section Clm.

Variable E : NormedModule R_AbsRing.
Variable F : NormedModule R_AbsRing.

(** Definition of clm *)

Record clm := Clm {
  m:> E->F ;
  Lf: is_linear_mapping m;
  Cf: is_finite (operator_norm m)
}.

(** Clm is AbelianGroup *)

Definition clm_zero : clm := Clm (fun _ => zero)
    is_linear_mapping_f_zero is_finite_norm_zero.

Definition clm_plus (f:clm) (g:clm) := Clm
    (plus (m f) (m g))
    (is_linear_mapping_f_plus _ _ (Lf f) (Lf g))
    (is_finite_operator_norm_plus _ _ (Cf f) (Cf g)).

Definition clm_opp (f:clm) := Clm
    (opp (m f))
    (is_linear_mapping_f_opp _  (Lf f))
    (is_finite_operator_norm_opp  _ (Cf f)).

Definition clm_scal (l:R) (f:clm) := Clm
    (scal l (m f))
    (is_linear_mapping_f_scal l _  (Lf f))
    (is_finite_operator_norm_scal l  _ (Cf f)).

Lemma clm_eq: forall (f g:clm), (m f = m g) -> f = g.
Proof.
intros f g H.
destruct f; destruct g.
simpl in H.
revert Lf1 Cf1.
rewrite <- H.
intros Lf1 Cf1; f_equal.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma clm_eq_ext: forall (f g:clm), (forall x, f x = g x) -> f = g.
Proof.
intros f g H.
destruct f; destruct g.
simpl in H.
apply functional_extensionality in H.
revert Lf1 Cf1.
rewrite <- H.
intros Lf1 Cf1; f_equal.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma clm_plus_comm: forall (f g:clm), clm_plus f g = clm_plus g f.
Proof.
intros f g.
apply clm_eq.
unfold clm_plus; simpl.
apply plus_comm.
Qed.

Lemma clm_plus_assoc:
  forall (x y z:clm), clm_plus x (clm_plus y z) = clm_plus (clm_plus x y) z.
Proof.
intros x y z.
apply clm_eq.
unfold clm_plus; simpl.
apply plus_assoc.
Qed.

Lemma clm_plus_zero_r: forall x:clm, clm_plus x clm_zero = x.
Proof.
intros x.
apply clm_eq.
unfold clm_plus; simpl.
apply: plus_zero_r.
Qed.

Lemma clm_plus_opp_r: forall x:clm, clm_plus x (clm_opp x) = clm_zero.
Proof.
intros x.
apply clm_eq.
unfold clm_plus, clm_opp; simpl.
apply: plus_opp_r.
Qed.

Definition clm_AbelianGroup_mixin :=
  AbelianGroup.Mixin clm clm_plus clm_opp clm_zero clm_plus_comm
   clm_plus_assoc clm_plus_zero_r clm_plus_opp_r.

Canonical clm_AbelianGroup :=
  AbelianGroup.Pack clm (clm_AbelianGroup_mixin) clm.

(** Clm is ModuleSpace *)

Lemma clm_scal_assoc: forall x y (u:clm),
   clm_scal x (clm_scal y u) = clm_scal (mult x y) u.
Proof.
intros x y u; apply clm_eq.
apply scal_assoc.
Qed.

Lemma clm_scal_one: forall (u:clm), clm_scal one u = u.
Proof.
intros u; apply clm_eq.
apply scal_one.
Qed.

Lemma clm_scal_distr_l: forall x (u v:clm), clm_scal x (plus u v)
        = clm_plus (clm_scal x u) (clm_scal x v).
Proof.
intros x u v; apply clm_eq.
apply: scal_distr_l.
Qed.

Lemma clm_scal_distr_r: forall (x y:R) (u:clm), clm_scal (Rplus x y) u
         = clm_plus (clm_scal x u) (clm_scal y u).
Proof.
intros x y u; apply clm_eq.
apply: scal_distr_r.
Qed.

Definition clm_ModuleSpace_mixin :=
  ModuleSpace.Mixin R_Ring clm_AbelianGroup clm_scal clm_scal_assoc
     clm_scal_one clm_scal_distr_l clm_scal_distr_r.

Canonical clm_ModuleSpace :=
  ModuleSpace.Pack R_Ring clm
   (ModuleSpace.Class R_Ring clm _ clm_ModuleSpace_mixin) clm.

(** Clm is UniformSpace *)

Definition clm_ball := fun (x:clm) eps y => operator_norm (minus y x) < eps.

Lemma clm_ball_center : forall (x : clm) (e : posreal),
  clm_ball x e x.
Proof.
intros x e; unfold clm_ball.
unfold minus; rewrite plus_opp_r.
rewrite operator_norm_zero.
now destruct e.
Qed.

Lemma clm_ball_sym :
  forall (x y : clm) (e : R),
  clm_ball x e y -> clm_ball y e x.
Proof.
intros x y e; unfold clm_ball; intros H.
apply Rle_lt_trans with (2:=H); right.
rewrite <- operator_norm_opp.
now rewrite opp_minus.
Qed.

Lemma clm_ball_triangle :
  forall (x y z : clm) (e1 e2 : R),
  clm_ball x e1 y -> clm_ball y e2 z -> clm_ball x (e1 + e2) z.
Proof.
intros x y z e1 e2; unfold clm_ball; intros H1 H2.
replace (minus z x) with (plus (minus z y) (minus y x)).
apply Rle_lt_trans with (operator_norm (minus z y) + operator_norm (minus y x)).
apply operator_norm_triangle.
apply is_finite_operator_norm_plus.
destruct z; easy.
apply is_finite_operator_norm_opp.
destruct y; easy.
apply is_finite_operator_norm_plus.
destruct y; easy.
apply is_finite_operator_norm_opp.
destruct x; easy.
rewrite Rplus_comm; now apply Rplus_lt_compat.
apply sym_eq, minus_trans.
Qed.

Definition clm_UniformSpace_mixin :=
  UniformSpace.Mixin clm zero clm_ball clm_ball_center clm_ball_sym clm_ball_triangle.

Canonical clm_UniformSpace :=
  UniformSpace.Pack clm (clm_UniformSpace_mixin) clm.

(** Clm is NormedModule *)

Canonical clm_NormedModuleAux :=
  NormedModuleAux.Pack R_AbsRing clm
   (NormedModuleAux.Class R_AbsRing clm
     (ModuleSpace.class _ clm_ModuleSpace)
        clm_UniformSpace_mixin) clm.

Lemma clm_norm_triangle: forall (x y:clm), operator_norm (plus x y) <= operator_norm x + operator_norm y.
Proof.
intros x y.
apply operator_norm_triangle.
destruct x; easy.
destruct y; easy.
Qed.

Lemma clm_norm_ball1 : forall (x y : clm) (eps : R),
        operator_norm (minus y x) < eps -> Hierarchy.ball x eps y.
Proof.
intros x y eps H; unfold ball; simpl.
now unfold clm_ball.
Qed.

Lemma clm_norm_ball2: forall (x y : clm) (eps : posreal),
          Hierarchy.ball x eps y -> operator_norm (minus y x) < 1 * eps.
Proof.
intros x y eps; unfold ball; simpl; unfold clm_ball.
now rewrite Rmult_1_l.
Qed.

Lemma clm_norm_scal_aux:
  (forall (l : R) (x : clm), operator_norm (scal l x) <= abs l * operator_norm x).
Proof.
intros l x.
unfold abs; simpl; right.
apply operator_norm_scal.
destruct x; easy.
destruct x; easy.
Qed.

Lemma clm_norm_eq_0: forall (x:clm),  real (operator_norm x) = 0 -> x = zero.
Proof.
intros x H.
apply clm_eq_ext.
intros u; simpl.
case (is_zero_dec u); intros Hu.
rewrite Hu is_linear_mapping_zero; try reflexivity.
destruct x; easy.
apply norm_eq_zero.
apply Rle_antisym.
2: apply norm_ge_0.
apply Rle_trans with (operator_norm x*norm u).
apply (operator_norm_helper' x); try exact Hu.
destruct x; easy.
rewrite H; right; apply Rmult_0_l.
Qed.

Definition clm_NormedModule_mixin :=
  NormedModule.Mixin R_AbsRing _
   (fun f => real (operator_norm (m f))) 1%R clm_norm_triangle clm_norm_scal_aux clm_norm_ball1 clm_norm_ball2 clm_norm_eq_0.

Canonical clm_NormedModule :=
  NormedModule.Pack R_AbsRing clm
     (NormedModule.Class _ _ _ clm_NormedModule_mixin) clm.

End Clm.

Arguments m [E] [F] _ _.

(** Composition of clm *)

Section Composition_lcm.

Variable E : NormedModule R_AbsRing.
Variable F : NormedModule R_AbsRing.
Variable G : NormedModule R_AbsRing.

Lemma operator_norm_estimation:
   forall (f:clm E F), forall (u:E),
      norm (f u) <= norm f * norm u.
Proof.
intros f u; destruct f; unfold norm at 2; simpl.
case (operator_norm_helper m0); try assumption.
intros (H1,H2).
generalize (Is_only_zero_set_correct1 E H1).
intros H3; rewrite H2 (H3 u).
replace (m0 zero) with (@zero F).
rewrite norm_zero.
right; simpl; ring.
apply sym_eq.
apply (is_linear_mapping_zero m0 Lf0).
intros (_,K); easy.
Qed.

(* compatibility of composition with continuity *)
Definition compose_lcm (g:clm F G) (f:clm E F) :=
   Clm E G (fun x => g (f x))
    (is_linear_mapping_compose _ _ (Lf _ _ f) (Lf _ _ g))
    (is_finite_operator_norm_compose _ _
        (is_linear_mapping_zero _ (Lf _ _ g)) (Cf _ _ f) (Cf _ _ g)).

Lemma norm_compose_lcm:
  forall (f:clm E F), forall (g:clm F G),
     norm (compose_lcm g f) <= norm g * norm f.
Proof.
intros f g.
unfold norm; simpl.
apply operator_norm_compose.
apply: is_linear_mapping_zero.
destruct g; easy.
destruct f; easy.
destruct g; easy.
Qed.

End Composition_lcm.

(** Topo_dual *)

Section topo_dual_sec.

Definition topo_dual (E : NormedModule R_AbsRing)
  := clm_NormedModule E R_NormedModule.

End topo_dual_sec.

(** Bilinear maps *)

Section DefsBilin.

Context {E : NormedModule R_AbsRing}.
Context {F : NormedModule R_AbsRing}.
Context {G : NormedModule R_AbsRing}.

Definition is_bounded_bi (f:E->F->G) (M:R) :=
   0 <= M /\
     (forall (x:E) (y:F), norm (f x y) <= M * norm x * norm y).

Definition is_bounded_bilinear_mapping (f : E -> F -> G) (M:R) :=
     is_bilinear_mapping f /\ is_bounded_bi f M.

Definition is_coercive (f : E -> E -> R) (M:R):=
  0 < M /\
    (forall x : E, M * norm x * norm x <= (f x x)).

End DefsBilin.

Section Bilin_rep.

Context {E : NormedModule R_AbsRing}.

(* representation for bounded bilinear form *)
Lemma is_bounded_bilinear_mapping_representation':
   forall phi M,
     is_bounded_bilinear_mapping phi M ->
       exists (A:clm E (topo_dual E)),
           forall (u v:E), phi u v = (A u) v.
Proof.
intros phi M Hphi.
assert (L1:(forall u, is_linear_mapping (phi u))).
intros u; split.
intros x y; apply Hphi.
intros x l; apply Hphi.
assert (C1:(forall u, is_finite (operator_norm (phi u)))).
intros u.
destruct Hphi as (_,(T1,T2)).
apply operator_norm_helper3 with (M*norm u).
apply Rmult_le_pos.
exact T1.
apply norm_ge_0.
intros z Hz.
apply T2.
pose (AA:= fun u => Clm _ _ _ (L1 u) (C1 u): (topo_dual E)).
assert (K1: is_linear_mapping AA).
split.
intros x y; apply clm_eq_ext; intros u.
unfold AA; simpl.
apply Hphi.
intros x l; apply clm_eq_ext; intros u.
unfold AA; simpl.
apply Hphi.
assert (K2: is_finite (operator_norm AA)).
destruct Hphi as (_,(T1,T2)).
apply operator_norm_helper3 with (M).
exact T1.
intros u Hu.
apply Rle_trans with (operator_norm (phi u)).
right; reflexivity.
apply operator_norm_helper3'.
apply Rmult_le_pos.
exact T1.
apply norm_ge_0.
intros v Hv.
apply T2.
exists (Clm _ _ AA K1 K2).
reflexivity.
Qed.

Lemma is_bounded_bilinear_mapping_representation_unique:
   forall (phi:E->E-> R),
       forall (A B :clm E (topo_dual E)),
           phi = (m A) -> phi = (m B) -> A = B.
Proof.
intros phi A B H1 H2.
apply clm_eq_ext; intros x.
apply clm_eq_ext; intros y.
apply trans_eq with (phi x y).
now rewrite H1.
now rewrite H2.
Qed.

Lemma is_bounded_bilinear_mapping_representation:
   forall phi M,
     is_bounded_bilinear_mapping phi M ->
       exists! (A:clm E (topo_dual E)),
           forall (u v:E), phi u v = (A u) v.
Proof.
intros phi M H.
apply unique_existence1.
split.
now apply is_bounded_bilinear_mapping_representation' with M.
unfold uniqueness.
intros A B HA HB.
apply is_bounded_bilinear_mapping_representation_unique with phi.
apply functional_extensionality; intros u.
apply functional_extensionality; now intros v.
apply functional_extensionality; intros u.
apply functional_extensionality; now intros v.
Qed.

Lemma is_bounded_bilinear_mapping_representation_moreover:
    forall phi M (A:clm E (topo_dual E)),
       is_bounded_bilinear_mapping phi M ->
       (forall (u v:E), phi u v = (A u) v) ->
          norm A <= M.
Proof.
intros phi M A Hphi HA.
unfold norm; simpl.
case (operator_norm_helper2 A).
destruct A; simpl; easy.
intros (H1,H2); rewrite H2.
apply Hphi.
intros (H1,H2).
apply H2; try assumption.
apply Hphi.
intros u.
unfold norm at 1; simpl.
case (operator_norm_helper2 (A u)).
destruct (A u); simpl; easy.
intros (H1',H2'); rewrite H2'.
intros Hu; apply Rmult_le_pos; try assumption.
apply Hphi.
apply norm_ge_0.
intros (H1',H2') Hu.
apply H2'.
apply Rmult_le_pos; try assumption.
apply Hphi.
apply norm_ge_0.
intros v Hv.
rewrite <- HA.
apply Hphi.
Qed.

(* coercivity constant is less than continuity constant *)
Lemma coercivity_le_continuity:
   ~ (Is_only_zero_set E) ->
   forall (phi:E->E->R) M1 M2,
     is_bounded_bilinear_mapping phi M1 ->
     is_coercive phi M2 ->
       M2 <= M1.
intros H phi M1 M2 (H1,(H2,H3)) (H4,H5).
apply (Is_only_zero_set_correct4 E _ H).
case (Rle_or_lt M2 M1); intros K.
now left.
right; now apply Rlt_not_le.
intros (x,Hx).
apply Rmult_le_reg_r with (norm x * norm x).
apply Rmult_lt_0_compat; now apply norm_gt_0.
rewrite <- 2!Rmult_assoc.
apply Rle_trans with (1:=H5 x).
apply Rle_trans with (2:=H3 x x).
unfold norm.
simpl.
unfold abs; simpl.
unfold Rabs.
destruct (Rcase_abs (phi x x)).
apply Rle_trans with 0.
intuition.
apply Ropp_0_ge_le_contravar.
apply Rle_ge.
intuition.
right; reflexivity.
Qed.

End Bilin_rep.

(** * Clm with subset *)

(** Decidability Is_only_zero_set subset *)

Section IOZsub.

Variable E : NormedModule R_AbsRing.
Variable phi :E -> Prop.

Definition Is_only_zero_set_phi : Prop :=
  (Empty (fun x => exists u:E, u <> zero /\ phi u /\ x = norm u)).

Lemma Is_only_zero_set_dec_phi:
  {~Is_only_zero_set_phi}+{Is_only_zero_set_phi}.
Proof.
unfold Is_only_zero_set_phi.
apply Empty_dec.
Qed.

Lemma Is_only_zero_set_correct1_phi:
   Is_only_zero_set_phi -> forall x:E, phi x -> x = zero.
Proof.
unfold Is_only_zero_set_phi.
intros H1.
specialize (Empty_correct_1 _ H1).
intros H2.
intros x Hx.
specialize (H2 (norm x)).
assert (norm x = 0).
case (Req_dec (norm x) 0); trivial.
intros H3.
elimtype False.
apply H2.
exists x.
split; trivial.
intros H4; apply H3.
rewrite H4.
apply norm_zero.
split; try reflexivity.
trivial.
apply norm_eq_zero.
exact H.
Qed.

Lemma Is_only_zero_set_correct2_phi:
   (forall (x:E), x = zero ) -> Is_only_zero_set_phi.
Proof.
intros H.
unfold Is_only_zero_set_phi.
apply Empty_correct_2.
intros x (u,(H1,H2)).
apply H1.
apply H.
Qed.

Lemma Is_only_zero_set_correct2'_phi:
   (forall (x:E), ~phi x ) -> Is_only_zero_set_phi.
Proof.
intros H.
unfold Is_only_zero_set_phi.
apply Empty_correct_2.
intros x (u,(H1,H2)).
specialize (H u).
intuition.
Qed.

Lemma Is_only_zero_set_correct2''_phi:
   (forall (x:E), x = zero \/ ~phi x ) -> Is_only_zero_set_phi.
Proof.
intros H.
unfold Is_only_zero_set_phi.
apply Empty_correct_2.
intros x (u,(H1,H2)).
specialize (H u).
intuition.
Qed.

Lemma Is_only_zero_set_correct3_phi:
  ~ Is_only_zero_set_phi -> ~ (forall (x:E), ~phi x /\ x = zero).
Proof.
intros H1 H2.
apply H1.
apply Is_only_zero_set_correct2_phi.
intros x.
specialize (H2 x).
exact (proj2 H2).
Qed.

Lemma Is_only_zero_set_correct3'_phi:
  ~ Is_only_zero_set_phi -> ~ (forall (x:E), x = zero).
Proof.
intros H1 H2.
apply H1.
apply Is_only_zero_set_correct2_phi.
trivial.
Qed.

Lemma Is_only_zero_set_correct3''_phi:
  ~ Is_only_zero_set_phi -> ~ (forall (x:E), ~phi x).
Proof.
intros H1 H2.
apply H1.
apply Is_only_zero_set_correct2'_phi.
trivial.
Qed.

Lemma Is_only_zero_set_correct4_phi: forall A,
  ~ Is_only_zero_set_phi -> decidable A ->
     ((exists (x:E), phi x /\ x <> zero) -> A) -> A.
Proof.
intros A H1 H2 H3.
case H2; trivial.
intros H4.
apply H3.
elimtype False.
apply H1.
apply Is_only_zero_set_correct2''_phi.
intros x.
destruct (is_zero_dec x).
left.
trivial.
right.
intro Hh.
assert (HA : A).
apply H3.
exists x.
intuition.
now apply H4.
Qed.

End IOZsub.

(** Operator norm subset *)

Section Op_norm_sub.

Context {E : NormedModule R_AbsRing}.
Context {F : NormedModule R_AbsRing}.
Variable phi :E -> Prop.

Definition operator_norm_phi (f:E->F) : Rbar :=
   match Is_only_zero_set_dec_phi E phi with
    | left _ => Lub_Rbar (fun x => exists u:E, u <> zero /\
                   phi u /\ x = norm (f u) / norm u)
    | right _ => 0
  end.

Lemma operator_norm_ge_0_phi: forall f,
  Rbar_le 0 (operator_norm_phi f).
Proof.
intros f.
unfold operator_norm_phi.
case Is_only_zero_set_dec_phi.
2: intros _; apply Rle_refl.
intros H.
apply (Is_only_zero_set_correct4_phi E phi); trivial.
unfold decidable.
case (Rbar_le_dec 0
   (Lub_Rbar (fun x : R =>
       exists u : E, u <> zero /\ phi u /\ x = norm (f u) / norm u))).
now left.
now right.
intros (x,Hx).
apply Rbar_le_trans with (norm (f x)/norm x).
apply Rmult_le_pos.
apply norm_ge_0.
left; apply Rinv_0_lt_compat.
now apply norm_gt_0.
apply Lub_Rbar_correct.
exists x.
split.
exact (proj2 Hx).
split.
exact (proj1 Hx).
reflexivity.
Qed.

Lemma operator_norm_ge_0'_phi : forall f,
  0 <= (operator_norm_phi f).
Proof.
intros f.
generalize (operator_norm_ge_0_phi f).
destruct (operator_norm_phi f); try easy.
intros _; apply Rle_refl; simpl.
Qed.

Lemma operator_norm_helper'_phi:
    forall f, is_finite (operator_norm_phi f) ->
        (forall u, u <> zero -> phi u -> norm (f u) <= operator_norm_phi f * norm u).
Proof.
intros f; unfold operator_norm_phi.
case Is_only_zero_set_dec_phi; intros K Hf1 u Hu Hpu.
apply Rmult_le_reg_r with (/ norm u).
apply Rinv_0_lt_compat.
now apply norm_gt_0.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
assert (Y: Rbar_le (norm (f u) * / norm u)
    (Lub_Rbar
     (fun x : R => exists u0 : E, u0 <> zero /\ phi u0 /\ x = norm (f u0) / norm u0))).
apply Lub_Rbar_correct.
exists u; split.
trivial.
split; trivial.
rewrite <- Hf1 in Y.
easy.
now apply Rgt_not_eq, norm_gt_0.
absurd (u=zero); try assumption.
now apply Is_only_zero_set_correct1_phi with phi.
Qed.

Lemma operator_norm_helper2_phi:
    forall f, is_finite (operator_norm_phi f) ->
       (Is_only_zero_set_phi E phi /\ operator_norm_phi f = 0)
     \/ (~Is_only_zero_set_phi E phi /\ forall M, 0 <= M ->
         (forall u, u <> zero -> norm (f u) <= M * norm u) ->
            operator_norm_phi f <= M).
Proof.
intros f; unfold operator_norm_phi.
case Is_only_zero_set_dec_phi; intros K Hf2.
(* . *)
right.
split; try exact K.
intros M HM1 HM2.
assert (Y: Rbar_le (Lub_Rbar (fun x : R => exists u : E, u <> zero /\ phi u /\
          x = norm (f u) / norm u)) M).
apply Lub_Rbar_correct.
intros x (u,(Hu1,Hu2)).
assert (x <= M); try easy.
rewrite (proj2 Hu2); apply Rmult_le_reg_r with (norm u).
now apply norm_gt_0.
apply Rle_trans with (2:=HM2 u Hu1).
right; field.
now apply Rgt_not_eq, norm_gt_0.
rewrite <- Hf2 in Y;easy.
(* . *)
left.
split; easy.
Qed.

Lemma operator_norm_helper2'_phi:
    forall f, is_finite (operator_norm_phi f) ->
       (Is_only_zero_set_phi E phi /\ operator_norm_phi f = 0)
     \/ (~Is_only_zero_set_phi E phi /\ forall M, 0 <= M ->
         (forall u, u <> zero -> phi u -> norm (f u) <= M * norm u) ->
            operator_norm_phi f <= M).
Proof.
intros f; unfold operator_norm_phi.
case Is_only_zero_set_dec_phi; intros K Hf2.
(* . *)
right.
split; try exact K.
intros M HM1 HM2.
assert (Y: Rbar_le (Lub_Rbar (fun x : R => exists u : E, u <> zero /\ phi u /\
          x = norm (f u) / norm u)) M).
apply Lub_Rbar_correct.
intros x (u,(Hu1,Hu2)).
assert (x <= M); try easy.
rewrite (proj2 Hu2); apply Rmult_le_reg_r with (norm u).
now apply norm_gt_0.
apply Rle_trans with (2:=HM2 u Hu1 (proj1 Hu2)).
right; field.
now apply Rgt_not_eq, norm_gt_0.
rewrite <- Hf2 in Y;easy.
(* . *)
left.
split; easy.
Qed.

Lemma operator_norm_helper3_phi :
    forall f, forall M, 0 <= M ->
       (forall u, u <> zero ->  phi u -> norm (f u) <= M * norm u) ->
         is_finite (operator_norm_phi f).
Proof.
intros f M H1 H2.
apply is_finite_betw with 0 M.
apply operator_norm_ge_0_phi.
unfold operator_norm_phi.
case Is_only_zero_set_dec_phi; intros H.
apply Lub_Rbar_correct.
intros x (u,(Hu1,Hu2)).
assert (x <= M); try easy.
rewrite (proj2 Hu2).
apply Rmult_le_reg_r with (norm u).
now apply norm_gt_0.
apply Rle_trans with (norm (f u)).
right; field.
now apply Rgt_not_eq, norm_gt_0.
now apply H2.
easy.
Qed.

Lemma operator_norm_helper3b_phi:
    forall f, forall M, 0 <= M ->
       (forall u, u <> zero -> norm (f u) <= M * norm u) ->
         is_finite (operator_norm_phi f).
Proof.
intros f M H1 H2.
apply is_finite_betw with 0 M.
apply operator_norm_ge_0_phi.
unfold operator_norm_phi.
case Is_only_zero_set_dec_phi; intros H.
apply Lub_Rbar_correct.
intros x (u,(Hu1,Hu2)).
assert (x <= M); try easy.
rewrite (proj2 Hu2).
apply Rmult_le_reg_r with (norm u).
now apply norm_gt_0.
apply Rle_trans with (norm (f u)).
right; field.
now apply Rgt_not_eq, norm_gt_0.
now apply H2.
easy.
Qed.

Lemma operator_norm_helper3'_phi:
    forall f, forall M, 0 <= M ->
       (forall u, u <> zero -> phi u -> norm (f u) <= M * norm u) ->
         (operator_norm_phi f <= M).
Proof.
intros f M H1 H2.
case operator_norm_helper2'_phi with f.
now apply operator_norm_helper3_phi with M.
intros (_,K); now rewrite K.
intros (_,K); apply K; easy.
Qed.

(* coercivity constant is less than continuity constant *)
Lemma coercivity_le_continuity_phi:
   ~ (Is_only_zero_set_phi E phi) ->
   forall (p:E->E->R) M1 M2,
     is_bounded_bilinear_mapping p M1 ->
     is_coercive p M2 ->
       M2 <= M1.
intros H p M1 M2 (H1,(H2,H3)) (H4,H5).
pose (A := M2 <= M1).
apply: (Is_only_zero_set_correct4_phi E phi _ H).
trivial.
case (Rle_or_lt M2 M1); intros K.
now left.
right; now apply Rlt_not_le.
intros (x,Hx).
apply Rmult_le_reg_r with (norm x * norm x).
apply Rmult_lt_0_compat; now apply norm_gt_0.
rewrite <- 2!Rmult_assoc.
apply Rle_trans with (1:=H5 x).
apply Rle_trans with (2:=H3 x x).
unfold norm.
simpl.
unfold abs; simpl.
unfold Rabs.
destruct (Rcase_abs (p x x)).
apply Rle_trans with 0.
intuition.
apply Ropp_0_ge_le_contravar.
apply Rle_ge.
intuition.
right; reflexivity.
Qed.

Lemma op_norm_finite_phi : forall f, is_finite (operator_norm f)
                  -> is_finite (operator_norm_phi f).
Proof.
intros f Hf.
generalize (operator_norm_ge_0_phi f) => Hpo.
unfold operator_norm_phi in Hpo.
unfold operator_norm_phi.
unfold operator_norm in Hf.
destruct (Is_only_zero_set_dec_phi E).
destruct (Is_only_zero_set_dec E).
unfold Lub_Rbar in *.
destruct (ex_lub_Rbar
 (fun x : R => exists u0 : E,
 u0 <> zero /\ phi u0 /\ x = norm (f u0) / norm u0)).
simpl.
destruct (ex_lub_Rbar (fun x : R => exists u : E,
        u <> zero /\ x = norm (f u) / norm u)).
simpl in Hf.
assert (Rbar_le x x0).
unfold is_lub_Rbar in i.
unfold is_ub_Rbar in i.
apply i.
intros x1 Hx1.
destruct Hx1 as (u0,Hx1).
unfold is_lub_Rbar in i0.
unfold is_ub_Rbar in i0.
apply i0.
exists u0; intuition.
destruct x.
unfold is_finite.
reflexivity.
exfalso.
unfold Rbar_le in H.
destruct x0.
trivial.
unfold is_finite in Hf.
simpl in Hf.
discriminate.
trivial.
simpl in Hpo.
exfalso.
trivial.
apply Is_only_zero_set_correct3'_phi in n.
destruct ((Lub_Rbar
     (fun x : R =>
      exists u : E, u <> zero /\ phi u /\ x = norm (f u) / norm u))).
unfold is_finite.
reflexivity.
exfalso.
generalize (Is_only_zero_set_correct1) => hO.
specialize (hO E i).
now apply n.
generalize (Is_only_zero_set_correct1) => hO.
specialize (hO E i).
exfalso.
now apply n.
unfold is_finite.
reflexivity.
Qed.

End Op_norm_sub.
