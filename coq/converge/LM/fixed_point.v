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

Require Export Reals Coquelicot.Coquelicot.
Require Export R_compl.
Require Export logic_tricks.

(** * Fixed Point Theorem without subspaces *)

Section FixedPoint_1.

Context {X : UniformSpace}.
Context {Y : UniformSpace}.

Definition ball_x : X -> R -> X -> Prop := UniformSpace.ball _ (UniformSpace.class X).
Definition ball_y : Y -> R -> Y -> Prop := UniformSpace.ball _ (UniformSpace.class Y).

(** Lispchitz functions *)

Definition is_Lipschitz (f: X -> Y) (k:R) :=
  0 <= k /\
    forall x1 x2 r, 0 < r ->
      ball_x x1 r x2 -> ball_y (f x1) (k*r) (f x2).

Definition is_contraction (f: X -> Y) :=
  exists k, k < 1 /\ is_Lipschitz f k.

End FixedPoint_1.

(** Balls and iterations *)

Section iter_dist.

Context {X : UniformSpace}.

Fixpoint iter (f:X -> X) (n:nat) (x:X) := match n with
   | O => x
   | S m => f (iter f m x)
  end.

Lemma dist_iter_aux_aux: forall (f:X->X) a k p D, 0 < k < 1 -> is_Lipschitz f k ->
    0 < D -> ball a D (f a) ->
   ball (iter f p a) (k ^ p * D) (iter f (p + 1) a).
Proof.
intros f a k p D (Hk1',Hk2') (_,Hk2) HD H.
induction p.
(* *)
simpl.
now rewrite Rmult_1_l.
(* *)
simpl.
rewrite Rmult_assoc.
apply Hk2.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
assumption.
Qed.

Lemma dist_iter_aux: forall (f:X->X) a k p m D, 0 < k < 1 -> is_Lipschitz f k ->
    0 < D -> ball a D (f a) -> (0 < m)%nat ->
    ball (iter f p a) (k^p*(1-k^m)/(1-k) *D)  (iter f (p+m) a).
intros f a k p m D (Hk1',Hk2') (Hk1,Hk2) HD H Hm.
case_eq m.
intros Y; rewrite Y in Hm.
now contradict Hm.
intros n _; clear Hm.
induction n.
(* . *)
simpl.
rewrite Rmult_1_r.
replace (k ^ p * (1 - k) / (1 - k) * D) with (k^p*D).
2: field.
2: now apply Rgt_not_eq, Rlt_Rminus.
apply dist_iter_aux_aux; try split; assumption.
(* . *)
replace (k ^ p * (1 - k ^ S (S n)) / (1 - k) * D) with
   ((k ^ p * (1 - k ^ S n) / (1 - k) * D)+(k ^ (p+S n) * D)).
apply ball_triangle with (iter f (p + S n) a).
exact IHn.
replace (p + S (S n))%nat with ((p+S n)+1)%nat.
apply dist_iter_aux_aux; try split; assumption.
ring.
rewrite pow_add.
simpl; field.
now apply Rgt_not_eq, Rlt_Rminus.
Qed.

Lemma dist_iter: forall (f:X->X) a k p m D, 0 < k < 1 -> is_Lipschitz f k ->
    0 < D -> ball a D (f a) ->
    ball (iter f p a) (k^p/(1-k) *D)  (iter f (p+m) a).
Proof.
intros f a k p m D H1 H2 H3 H4.
case_eq m.
(* *)
intros _; rewrite plus_0_r.
assert (L:(0 < k ^ p / (1 - k) * D)).
apply Rmult_lt_0_compat; trivial.
apply Rdiv_lt_0_compat.
now apply pow_lt.
now apply Rlt_Rminus.
replace (k ^ p / (1 - k) * D) with (pos (mkposreal _ L)) by reflexivity.
apply ball_center.
(* *)
intros n Hn.
apply ball_le with (k^p*(1-k^m)/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
rewrite <- (Rmult_1_r (k^p)) at 2.
apply Rmult_le_compat_l.
left; now apply pow_lt.
apply Rplus_le_reg_l with (-1).
ring_simplify.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
left; now apply pow_lt.
rewrite Hn.
apply dist_iter_aux; try assumption.
auto with arith.
Qed.

Variable f: X -> X.
Variable phi: X -> Prop.
Hypothesis phi_f: forall x:X, phi x -> phi (f x).
Hypothesis phi_distanceable:
   forall (x y:X), phi x -> phi y-> exists M, 0 <= M /\ ball x M y.

Lemma phi_iter_f: forall a n, phi a -> phi (iter f n a).
Proof.
intros a; induction n; intros Phi_a.
now simpl.
simpl.
now apply phi_f, IHn.
Qed.

Lemma dist_iter_aux_zero: forall (a:X) p m,
    phi a ->
    is_Lipschitz f 0 ->
    (0 < p)%nat -> (0 < m)%nat ->
   ball (iter f p a) 0 (iter f m a).
Proof.
intros a p m phi_a (_,H) Hp Hm.
case_eq p.
intros V; rewrite V in Hp; now contradict Hp.
intros n1 Hn1.
case_eq m.
intros V; rewrite V in Hm; now contradict Hm.
intros n2 Hn2.
simpl.
destruct (phi_distanceable (iter f n1 a) (iter f n2 a)) as (M,(HM1,HM2)).
now apply phi_iter_f.
now apply phi_iter_f.
replace 0 with (0*(M+1)) by ring.
apply H; try assumption.
apply Rle_lt_trans with (M+0).
now rewrite Rplus_0_r.
apply Rplus_lt_compat_l, Rlt_0_1.
apply ball_le with M; try assumption.
apply Rle_trans with (M+0).
right; ring.
apply Rplus_le_compat_l, Rle_0_1.
Qed.

Lemma dist_iter_gen: forall a k p m n D, 0 <= k < 1 -> is_Lipschitz f k ->
   phi a ->
   0 < D -> ball a D (f a) -> (n <= p)%nat -> (n <= m)%nat -> (0 < n)%nat ->
    ball (iter f p a) (k^n/(1-k) *D) (iter f m a).
Proof.
intros a k p m n D (H1,H1') H2 Phi_a H3 H4 Hp Hm Hn.
case H1; intros P.
(* *)
case (le_or_lt p m); intros H5.
(* . *)
replace m with (p+(m-p))%nat.
apply ball_le with (k^p/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
apply Rle_pow_le; try assumption.
split; try left; try assumption.
apply dist_iter; try assumption.
split; assumption.
now apply le_plus_minus_r.
(* . *)
apply ball_sym.
replace p with (m+(p-m))%nat.
apply ball_le with (k^m/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
apply Rle_pow_le; try assumption.
split; try left; assumption.
apply dist_iter; try assumption.
split; assumption.
now apply le_plus_minus_r, lt_le_weak.
(* *)
apply ball_le with 0.
rewrite <- P.
rewrite pow_i; try assumption.
right; unfold Rdiv; ring.
apply dist_iter_aux_zero; try assumption.
now rewrite P.
now apply lt_le_trans with n.
now apply lt_le_trans with n.
Qed.

End iter_dist.

(** My_complete *)

Section closed_compl.

Context {X : CompleteSpace}.
Definition lim : ((X -> Prop) -> Prop) -> X := CompleteSpace.lim _ (CompleteSpace.class X).

Definition my_complete (phi:X->Prop) := (forall (F:(X -> Prop) -> Prop),
    ProperFilter F -> cauchy F ->
   (forall P, F P -> ~~(exists x, P x /\ phi x)) -> phi (lim F)).

Lemma closed_my_complete: forall phi,
     closed phi -> my_complete phi.
Proof.
intros phi phi_closed F H1 H2 H3.
generalize (@complete_cauchy X F H1 H2).
intros H4.
unfold closed in *; unfold open in *.
(*apply H5.*)
apply phi_closed.
intros H6'.
destruct H6' as (eps,H6).
specialize (H3 (ball (lim F) eps)).
apply H3.
apply H4.
intros (y,(Hy1,Hy2)).
specialize (H6 y Hy1).
now apply H6.
Qed.

End closed_compl.

Section closed_compl2.

Context {X : CompleteNormedModule R_AbsRing}.

Variable phi: X -> Prop.

Lemma my_complete_closed:
   my_complete phi -> closed phi.
Proof.
intros H x Hx.
pose (F:= locally x).
assert (ProperFilter F).
apply locally_filter.
assert (cauchy F).
intros e; unfold F.
exists x.
now exists e.
replace x with (lim F).
apply H; try assumption.
unfold F; intros P T1 T2.
destruct T1 as (e,He).
apply Hx.
exists e.
intros y Hy1 Hy2.
apply T2.
exists y; split; try easy.
now apply He.
apply sym_eq, eq_close.
intros e.
generalize (complete_cauchy F H0 H1 e).
unfold F; simpl.
intros (ee,Hee).
apply ball_sym.
apply Hee.
apply ball_center.
Qed.

End closed_compl2.

(** Fixed Point Theorem *)

Section FixedPoint_2.

Context {X : CompleteSpace}.

Variable (f:X->X).

(* subset *)
Variable phi: X -> Prop.

Hypothesis phi_f: forall x:X, phi x -> phi (f x).
Hypothesis phi_distanceable:
   forall (x y:X), phi x -> phi y-> exists M, 0 <= M /\ ball x M y.

Lemma FixedPoint_uniqueness_weak: forall a b, is_contraction f
      -> phi a -> phi b
      -> close (f a) a -> close (f b) b ->
        close a b.
Proof.
intros a b (k,(Hk1,(Hk2,Hf))) Phi_a Phi_b Ha Hb eps.
destruct (phi_distanceable a b) as (M,(HM1,HM2)); try assumption.
destruct HM1.
(* *)
pose (k' := (k + 1)/2).
assert (k < k').
unfold k'; apply Rmult_lt_reg_l with 2%R.
apply Rlt_0_2.
apply Rplus_lt_reg_l with (-k).
replace (-k+2*k) with k by ring.
replace (-k + 2 * ((k + 1) / 2)) with 1 by field.
assumption.
assert (0 < k' < 1).
split.
apply Rle_lt_trans with k; assumption.
unfold k'; apply Rmult_lt_reg_l with 2%R.
apply Rlt_0_2.
apply Rplus_lt_reg_l with (-1).
replace (-1+2*1) with 1 by ring.
replace (-1 + 2 * ((k + 1) / 2)) with k by field.
assumption.
(* *)
destruct (contraction_lt_any k' (eps/M)) as (N,HN).
now (split; try left).
apply Rdiv_lt_0_compat; trivial.
destruct eps; simpl; easy.
apply ball_le with (M*k'^N).
apply Rmult_le_reg_r with (/M).
now apply Rinv_0_lt_compat.
left; apply Rle_lt_trans with (2:=HN).
right; field.
now apply Rgt_not_eq.
(* *)
clear HN; induction N.
simpl; rewrite Rmult_1_r.
assumption.
assert (L:(0 < M*k'^S N*(k'-k)/2)).
apply Rdiv_lt_0_compat; try apply Rlt_0_2.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
now apply Rlt_Rminus.
specialize (Ha (mkposreal _ L)).
specialize (Hb (mkposreal _ L)).
apply ball_le with ((M * k' ^ (S N) * (k' - k) / 2) + ((k*(M * k' ^ N)) + (M * k' ^ (S N) * (k' - k) / 2))).
simpl.
apply Rle_trans with ((k'*(k' - k)  + k)*M*k'^N).
right; field.
apply Rle_trans with (k'*M*k'^N).
2: right; ring.
apply Rmult_le_compat_r.
left; now apply pow_lt.
apply Rmult_le_compat_r.
now left.
apply Rplus_le_reg_l with (-k'*(k'-k)-k).
apply Rle_trans with 0.
right; ring.
apply Rle_trans with (Rsqr ((k-1)/2)).
apply Rle_0_sqr.
right; unfold Rsqr, k'.
field.
apply ball_triangle with (f a).
apply ball_sym, Ha.
apply ball_triangle with (f b).
apply Hf; try assumption.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
apply Hb.
(* *)
apply ball_le with M; try assumption.
rewrite <- H; destruct eps; simpl; left; easy.
Qed.

Lemma Fixed_Point_aux_Proper: forall (a:X),
    ProperFilter (fun P => eventually (fun n => P (iter f n a))).
Proof.
intros a; split.
intros P (N,HN).
exists (iter f N a).
apply HN.
apply le_n.
split.
exists 0%nat; easy.
intros P Q (N1,H1) (N2,H2).
exists (max N1 N2).
intros n Hn; split.
apply H1.
apply le_trans with (2:=Hn).
apply Max.le_max_l.
apply H2.
apply le_trans with (2:=Hn).
apply Max.le_max_r.
intros P Q H (N,HN).
exists N.
intros n Hn.
apply H.
now apply HN.
Qed.

Lemma Fixed_Point_aux_cauchy: forall (a:X), is_contraction f ->
    phi a -> cauchy (fun P => eventually (fun n => P (iter f n a))).
intros a (k,(Hk1,(Hk2,Hf))) Phi_a.
generalize (@cauchy_distance X _ (Fixed_Point_aux_Proper a)).
unfold cauchy; intros (_,T); apply T; clear T.
intros eps.
destruct (phi_distanceable a (f a)) as (M,(HM1,HM2)).
assumption.
now apply phi_f.
destruct HM1.
(* 0 < M *)
destruct (contraction_lt_any' k (eps/M*(1-k)*/3)) as (n,(Hn',Hn)).
now split.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply Rdiv_lt_0_compat; trivial.
destruct eps; now simpl.
now apply Rlt_Rminus.
apply Rinv_0_lt_compat.
apply Rplus_lt_0_compat; try apply Rlt_0_1; apply Rlt_0_2.
exists (fun x => exists m:nat, (n <= m)%nat /\ close x (iter f m a)).
split.
(* . *)
exists n.
intros l Hl.
exists l; split; try easy.
intros E; apply ball_center.
(* . *)
intros u v (n1,(Hn1,Hu)) (n2,(Hn2,Hv)).
assert (L:(0 < eps/3)).
apply Rdiv_lt_0_compat.
destruct eps; now simpl.
apply Rplus_lt_0_compat; try apply Rlt_0_1; apply Rlt_0_2.
pose (e:=mkposreal _ L).
replace (pos eps) with (pos e+(pos e+pos e))%R by (simpl;field).
apply ball_triangle with (iter f n1 a).
apply Hu.
apply ball_triangle with (iter f n2 a).
2: apply ball_sym, Hv.
apply ball_le with (k ^ n / (1 - k) * M).
unfold e; simpl.
apply Rmult_le_reg_l with (/M).
now apply Rinv_0_lt_compat.
apply Rmult_le_reg_l with (1-k).
now apply Rlt_Rminus.
apply Rle_trans with (eps / M * (1 - k) * / 3).
2: right; unfold Rdiv; ring.
left; apply Rle_lt_trans with (2:=Hn).
right; field.
split; apply Rgt_not_eq; try assumption.
now apply Rlt_Rminus.
apply dist_iter_gen with phi; try assumption.
now split.
now split.
(* M = 0 *)
rewrite <- H in HM2.
assert (forall n, close (iter f n a) a).
apply strong_induction with (P:= fun n => close (iter f n a) a).
intros n; case n.
simpl; intros _.
intros e; apply ball_center.
clear n; intros n; case n.
intros _; simpl.
intros e; apply ball_sym, ball_le with 0; try assumption.
destruct e; left; now simpl.
clear n; intros n IH.
apply close_trans with (iter f (S n) a).
2: apply IH.
2: apply le_n.
simpl; intros e.
apply ball_le with (k*e).
rewrite <- (Rmult_1_l e) at 2.
apply Rmult_le_compat_r.
destruct e; left; now simpl.
now left.
apply Hf.
apply cond_pos.
assert (L:(close (iter f (S n) a) (iter f n a))).
apply close_trans with a.
apply IH.
apply le_n.
apply close_sym.
apply IH.
apply le_S, le_n.
apply L.
exists (fun x => close x a).
split.
exists 0%nat.
intros n _; apply H0.
intros u v Hu Hv.
assert (close u v).
apply close_trans with a; try assumption.
now apply close_sym.
apply H1.
Qed.

Lemma FixedPoint_aux1: forall (a:X), is_contraction f -> phi a ->
  let  x := lim  (fun P => eventually (fun n => P (iter f n a))) in
      close (f x) x.
Proof.
intros a Hf Phi_a x.
generalize (complete_cauchy
   (fun P => eventually (fun n => P (iter f n a)))
    (Fixed_Point_aux_Proper a)
    (Fixed_Point_aux_cauchy a Hf Phi_a)).
replace ((Hierarchy.lim
         (fun P : X -> Prop => eventually (fun n0 : nat => P (iter f n0 a))))) with x by reflexivity.
intros H eps.
pose (e2 :=mkposreal _ (is_pos_div_2 eps)).
specialize (H e2).
destruct H as (n,Hn).
replace (pos eps) with (pos e2 + pos e2).
2: simpl; field.
apply ball_sym.
apply ball_triangle with (iter f (S n) a).
apply Hn.
apply le_S, le_n.
destruct Hf as (k,(Hk1,(Hk2,Hk3))).
apply ball_le with (k*e2).
rewrite <- (Rmult_1_l e2) at 2.
apply Rmult_le_compat_r.
destruct e2; left; now simpl.
now left.
simpl.
apply Hk3.
apply (cond_pos e2).
apply ball_sym.
apply Hn.
apply le_n.
Qed.

Hypothesis phi_X_not_empty: exists (a:X), phi a.
Hypothesis phi_closed: my_complete phi.

Lemma FixedPoint_aux2: forall (a:X), is_contraction f -> phi a ->
  let  x := lim
  (fun P => eventually (fun n => P (iter f n a))) in
      phi x.
Proof.
intros a Hf Phi_a x.
apply phi_closed.
apply Fixed_Point_aux_Proper.
now apply Fixed_Point_aux_cauchy.
intros P (N,HN).
intros K; apply K.
exists (iter f N a).
split.
apply HN.
apply le_n.
now apply phi_iter_f.
Qed.

Theorem FixedPoint_C: is_contraction f ->
   exists a:X,
     phi a
      /\ close (f a) a
      /\ (forall b, phi b -> close (f b) b -> close b a) /\
    forall x, phi x -> close (lim  (fun P => eventually (fun n => P (iter f n x)))) a.
Proof.
intros Hf.
destruct phi_X_not_empty as (a, Ha).
exists (lim (fun P => eventually (fun n => P (iter f n a)))).
split.
now apply FixedPoint_aux2.
split.
now apply FixedPoint_aux1.
split.
intros b Phi_b Hb.
apply FixedPoint_uniqueness_weak; try assumption.
now apply FixedPoint_aux2.
now apply FixedPoint_aux1.
intros x Phi_x.
apply FixedPoint_uniqueness_weak; try assumption.
now apply FixedPoint_aux2.
now apply FixedPoint_aux2.
now apply FixedPoint_aux1.
now apply FixedPoint_aux1.
Qed.

End FixedPoint_2.

(** Fixed Point Theorem without norms *)

Section FixedPoint_Normed.

Variable K : AbsRing.
Context {X : CompleteNormedModule K}.

Variable (f:X->X).

Variable phi: X -> Prop.
Hypothesis phi_f: forall x:X, phi x -> phi (f x).
Hypothesis phi_X_not_empty: exists (a:X), phi a.
Hypothesis phi_closed: my_complete phi.


Theorem FixedPoint: is_contraction f ->
   exists a:X,
     phi a
      /\ f a = a
      /\ (forall b, phi b -> f b = b -> b = a) /\
    forall x, phi x -> lim  (fun P => eventually (fun n => P (iter f n x))) = a.
Proof.
intros Hf.
destruct (FixedPoint_C f phi) as (a,Ha); try assumption.
intros x y _ _.
case (Rle_lt_or_eq_dec 0 (norm (minus y x))).
apply norm_ge_0.
intros H1.
(* . *)
assert (Y: 0 < 2*norm (minus y x)).
apply Rmult_lt_0_compat; try apply Rlt_0_2; assumption.
exists (mkposreal _ Y).
split.
left; apply cond_pos.
apply (norm_compat1 x y).
simpl.
apply Rplus_lt_reg_r with (-norm (minus y x)).
ring_simplify.
apply Rle_lt_trans with (2:=H1).
apply Rle_minus.
right; reflexivity.
(* . *)
intros H1.
exists (mkposreal _ Rlt_0_1).
split.
left; apply cond_pos.
replace x with y.
apply ball_center.
apply plus_reg_r with (opp x).
rewrite plus_opp_r.
apply (norm_eq_zero (plus y (opp x))).
now apply sym_eq.
(* *)
destruct Ha as (Ha1,(Ha2,(Ha3,Ha4))).
exists a.
split; [assumption|split].
now apply eq_close.
split.
intros b Hb1 Hb2.
apply eq_close, Ha3; try assumption.
rewrite Hb2; now apply close_refl.
intros x Hx.
apply eq_close, Ha4; try assumption.
Qed.

End FixedPoint_Normed.

(** * Fixed Point Theorem with subsets *)

Section FixedPoint_1_sub.

Context {X : UniformSpace}.
Context {Y : UniformSpace}.

(** Lispchitz functions with subsets *)

Definition is_Lipschitz_phi (f: X -> Y) (k:R) (P : X -> Prop) :=
  0 <= k /\
    forall x1 x2 r, 0 < r -> P x1 -> P x2 ->
      ball_x x1 r x2 -> ball_y (f x1) (k*r) (f x2).

Definition is_contraction_phi (f: X -> Y) (P : X -> Prop) :=
  exists k, k < 1 /\ is_Lipschitz_phi f k P.

End FixedPoint_1_sub.

(** Balls and iterations with subsets *)

Section iter_dist_sub.

Context {X : UniformSpace}.

Lemma dist_iter_aux_aux_phi: forall (f:X->X) (P : X -> Prop) a k p D, 0 < k < 1
   -> (forall p, P (iter f p a)) -> is_Lipschitz_phi f k P -> 0 < D -> ball a D (f a) ->
   ball (iter f p a) (k ^ p * D) (iter f (p + 1) a).
Proof.
intros f P a k p D (Hk1',Hk2') HH (_,Hk2) HD H.
induction p.
(* *)
simpl.
now rewrite Rmult_1_l.
(* *)
simpl.
rewrite Rmult_assoc.
apply Hk2.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
apply HH.
apply HH.
assumption.
Qed.

Lemma dist_iter_aux_phi : forall (f:X->X) (P : X -> Prop) a k p m D,
    0 < k < 1 ->  (forall p, P (iter f p a)) -> is_Lipschitz_phi f k P ->
    0 < D -> ball a D (f a) -> (0 < m)%nat ->
    ball (iter f p a) (k^p*(1-k^m)/(1-k) *D)  (iter f (p+m) a).
intros f P a k p m D (Hk1',Hk2') HH (Hk1,Hk2) HD H Hm.
case_eq m.
intros Y; rewrite Y in Hm.
now contradict Hm.
intros n _; clear Hm.
induction n.
(* . *)
simpl.
rewrite Rmult_1_r.
replace (k ^ p * (1 - k) / (1 - k) * D) with (k^p*D).
2: field.
2: now apply Rgt_not_eq, Rlt_Rminus.
apply dist_iter_aux_aux_phi with P; try split; assumption.
(* . *)
replace (k ^ p * (1 - k ^ S (S n)) / (1 - k) * D) with
   ((k ^ p * (1 - k ^ S n) / (1 - k) * D)+(k ^ (p+S n) * D)).
apply ball_triangle with (iter f (p + S n) a).
exact IHn.
replace (p + S (S n))%nat with ((p+S n)+1)%nat.
apply dist_iter_aux_aux_phi with P; try split; assumption.
ring.
rewrite pow_add.
simpl; field.
now apply Rgt_not_eq, Rlt_Rminus.
Qed.

Lemma dist_iter_phi: forall (f:X->X) (P:X-> Prop) a k p m D, 0 < k < 1
    -> (forall p, P (iter f p a)) -> is_Lipschitz_phi f k P ->
    0 < D -> ball a D (f a) ->
    ball (iter f p a) (k^p/(1-k) *D)  (iter f (p+m) a).
Proof.
intros f P a k p m D H1 H2 HH H3 H4.
case_eq m.
(* *)
intros _; rewrite plus_0_r.
assert (L:(0 < k ^ p / (1 - k) * D)).
apply Rmult_lt_0_compat; trivial.
apply Rdiv_lt_0_compat.
now apply pow_lt.
now apply Rlt_Rminus.
replace (k ^ p / (1 - k) * D) with (pos (mkposreal _ L)) by reflexivity.
apply ball_center.
(* *)
intros n Hn.
apply ball_le with (k^p*(1-k^m)/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
rewrite <- (Rmult_1_r (k^p)) at 2.
apply Rmult_le_compat_l.
left; now apply pow_lt.
apply Rplus_le_reg_l with (-1).
ring_simplify.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
left; now apply pow_lt.
rewrite Hn.
apply dist_iter_aux_phi with P; try assumption.
auto with arith.
Qed.

Variable f: X -> X.
Variable phi: X -> Prop.

Hypothesis phi_f: forall x:X, phi x -> phi (f x).

Hypothesis phi_distanceable:
   forall (x y:X), phi x -> phi y-> exists M, 0 <= M /\ ball x M y.

Lemma dist_iter_aux_zero_phi : forall (a:X) p m,
    phi a ->
    is_Lipschitz_phi f 0 phi ->
    (0 < p)%nat -> (0 < m)%nat ->
   ball (iter f p a) 0 (iter f m a).
Proof.
intros a p m phi_a (_,H) Hp Hm.
case_eq p.
intros V; rewrite V in Hp; now contradict Hp.
intros n1 Hn1.
case_eq m.
intros V; rewrite V in Hm; now contradict Hm.
intros n2 Hn2.
simpl.
destruct (phi_distanceable (iter f n1 a) (iter f n2 a)) as (M,(HM1,HM2)).
now apply phi_iter_f.
now apply phi_iter_f.
replace 0 with (0*(M+1)) by ring.
apply H; try assumption.
apply Rle_lt_trans with (M+0).
now rewrite Rplus_0_r.
apply Rplus_lt_compat_l, Rlt_0_1.
apply phi_iter_f.
trivial.
trivial.
apply phi_iter_f.
trivial.
trivial.
apply ball_le with M; try assumption.
apply Rle_trans with (M+0).
right; ring.
apply Rplus_le_compat_l, Rle_0_1.
Qed.

Lemma dist_iter_gen_phi : forall a k p m n D, 0 <= k < 1 -> is_Lipschitz_phi  f k phi ->
   phi a ->
   0 < D -> ball a D (f a) -> (n <= p)%nat -> (n <= m)%nat -> (0 < n)%nat ->
    ball (iter f p a) (k^n/(1-k) *D) (iter f m a).
Proof.
intros a k p m n D (H1,H1') H2 Phi_a H3 H4 Hp Hm Hn.
case H1; intros P0.
(* *)
case (le_or_lt p m); intros H5.
(* . *)
replace m with (p+(m-p))%nat.
apply ball_le with (k^p/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
apply Rle_pow_le; try assumption.
split; try left; try assumption.
apply dist_iter_phi with phi; try assumption.
split; assumption.
intros p0.
apply phi_iter_f.
trivial.
trivial.
now apply le_plus_minus_r.
(* . *)
apply ball_sym.
replace p with (m+(p-m))%nat.
apply ball_le with (k^m/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
apply Rle_pow_le; try assumption.
split; try left; assumption.
apply dist_iter_phi with phi; try assumption.
split; assumption.
intros p0.
apply phi_iter_f; trivial.
now apply le_plus_minus_r, lt_le_weak.
(* *)
apply ball_le with 0.
rewrite <- P0.
rewrite pow_i; try assumption.
right; unfold Rdiv; ring.
apply dist_iter_aux_zero_phi; try assumption.
now rewrite P0.
now apply lt_le_trans with n.
now apply lt_le_trans with n.
Qed.

End iter_dist_sub.

(** Fixed Point Theorem with subsets *)

Section FixedPoint_2_sub.

Context {X : CompleteSpace}.

Variable (f:X->X).

Variable phi: X -> Prop.

Hypothesis phi_f: forall x:X, phi x -> phi (f x).
Hypothesis phi_distanceable:
   forall (x y:X), phi x -> phi y-> exists M, 0 <= M /\ ball x M y.
Hypothesis phi_c : my_complete phi.

Lemma FixedPoint_uniqueness_weak_phi : forall a b, is_contraction_phi f phi
      -> phi a -> phi b
      -> close (f a) a -> close (f b) b ->
        close a b.
Proof.
intros a b (k,(Hk1,(Hk2,Hf))) Phi_a Phi_b Ha Hb eps.
destruct (phi_distanceable a b) as (M,(HM1,HM2)); try assumption.
destruct HM1.
(* *)
pose (k' := (k + 1)/2).
assert (k < k').
unfold k'; apply Rmult_lt_reg_l with 2%R.
apply Rlt_0_2.
apply Rplus_lt_reg_l with (-k).
replace (-k+2*k) with k by ring.
replace (-k + 2 * ((k + 1) / 2)) with 1 by field.
assumption.
assert (0 < k' < 1).
split.
apply Rle_lt_trans with k; assumption.
unfold k'; apply Rmult_lt_reg_l with 2%R.
apply Rlt_0_2.
apply Rplus_lt_reg_l with (-1).
replace (-1+2*1) with 1 by ring.
replace (-1 + 2 * ((k + 1) / 2)) with k by field.
assumption.
(* *)
destruct (contraction_lt_any k' (eps/M)) as (N,HN).
now (split; try left).
apply Rdiv_lt_0_compat; trivial.
destruct eps; simpl; easy.
apply ball_le with (M*k'^N).
apply Rmult_le_reg_r with (/M).
now apply Rinv_0_lt_compat.
left; apply Rle_lt_trans with (2:=HN).
right; field.
now apply Rgt_not_eq.
(* *)
clear HN; induction N.
simpl; rewrite Rmult_1_r.
assumption.
assert (L:(0 < M*k'^S N*(k'-k)/2)).
apply Rdiv_lt_0_compat; try apply Rlt_0_2.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
now apply Rlt_Rminus.
specialize (Ha (mkposreal _ L)).
specialize (Hb (mkposreal _ L)).
apply ball_le with ((M * k' ^ (S N) * (k' - k) / 2) + ((k*(M * k' ^ N)) + (M * k' ^ (S N) * (k' - k) / 2))).
simpl.
apply Rle_trans with ((k'*(k' - k)  + k)*M*k'^N).
right; field.
apply Rle_trans with (k'*M*k'^N).
2: right; ring.
apply Rmult_le_compat_r.
left; now apply pow_lt.
apply Rmult_le_compat_r.
now left.
apply Rplus_le_reg_l with (-k'*(k'-k)-k).
apply Rle_trans with 0.
right; ring.
apply Rle_trans with (Rsqr ((k-1)/2)).
apply Rle_0_sqr.
right; unfold Rsqr, k'.
field.
apply ball_triangle with (f a).
apply ball_sym, Ha.
apply ball_triangle with (f b).
apply Hf; try assumption.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
apply Hb.
(* *)
apply ball_le with M; try assumption.
rewrite <- H; destruct eps; simpl; left; easy.
Qed.

Lemma Fixed_Point_aux_Proper_phi : forall (a:X),
    ProperFilter (fun P => eventually (fun n => P (iter f n a))).
Proof.
intros a; split.
intros P (N,HN).
exists (iter f N a).
apply HN.
apply le_n.
split.
exists 0%nat; easy.
intros P Q (N1,H1) (N2,H2).
exists (max N1 N2).
intros n Hn; split.
apply H1.
apply le_trans with (2:=Hn).
apply Max.le_max_l.
apply H2.
apply le_trans with (2:=Hn).
apply Max.le_max_r.
intros P Q H (N,HN).
exists N.
intros n Hn.
apply H.
now apply HN.
Qed.

Lemma Fixed_Point_aux_cauchy_phi : forall (a:X), is_contraction_phi f phi ->
    phi a -> cauchy (fun P => eventually (fun n => P (iter f n a))).
intros a (k,(Hk1,(Hk2,Hf))) Phi_a.
generalize (@cauchy_distance X _ (Fixed_Point_aux_Proper_phi a)).
unfold cauchy; intros (_,T); apply T; clear T.
intros eps.
destruct (phi_distanceable a (f a)) as (M,(HM1,HM2)).
assumption.
now apply phi_f.
destruct HM1.
(* 0 < M *)
destruct (contraction_lt_any' k (eps/M*(1-k)*/3)) as (n,(Hn',Hn)).
now split.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply Rdiv_lt_0_compat; trivial.
destruct eps; now simpl.
now apply Rlt_Rminus.
apply Rinv_0_lt_compat.
apply Rplus_lt_0_compat; try apply Rlt_0_1; apply Rlt_0_2.
exists (fun x => exists m:nat, (n <= m)%nat /\ close x (iter f m a)).
split.
(* . *)
exists n.
intros l Hl.
exists l; split; try easy.
intros E; apply ball_center.
(* . *)
intros u v (n1,(Hn1,Hu)) (n2,(Hn2,Hv)).
assert (L:(0 < eps/3)).
apply Rdiv_lt_0_compat.
destruct eps; now simpl.
apply Rplus_lt_0_compat; try apply Rlt_0_1; apply Rlt_0_2.
pose (e:=mkposreal _ L).
replace (pos eps) with (pos e+(pos e+pos e))%R by (simpl;field).
apply ball_triangle with (iter f n1 a).
apply Hu.
apply ball_triangle with (iter f n2 a).
2: apply ball_sym, Hv.
apply ball_le with (k ^ n / (1 - k) * M).
unfold e; simpl.
apply Rmult_le_reg_l with (/M).
now apply Rinv_0_lt_compat.
apply Rmult_le_reg_l with (1-k).
now apply Rlt_Rminus.
apply Rle_trans with (eps / M * (1 - k) * / 3).
2: right; unfold Rdiv; ring.
left; apply Rle_lt_trans with (2:=Hn).
right; field.
split; apply Rgt_not_eq; try assumption.
now apply Rlt_Rminus.
apply dist_iter_gen_phi with phi; try assumption.
now split.
now split.
(* M = 0 *)
rewrite <- H in HM2.
assert (forall n, close (iter f n a) a).
apply strong_induction with (P:= fun n => close (iter f n a) a).
intros n; case n.
simpl; intros _.
intros e; apply ball_center.
clear n; intros n; case n.
intros _; simpl.
intros e; apply ball_sym, ball_le with 0; try assumption.
destruct e; left; now simpl.
clear n; intros n IH.
apply close_trans with (iter f (S n) a).
2: apply IH.
2: apply le_n.
simpl; intros e.
apply ball_le with (k*e).
rewrite <- (Rmult_1_l e) at 2.
apply Rmult_le_compat_r.
destruct e; left; now simpl.
now left.
apply Hf.
apply cond_pos.
apply phi_iter_f.
intros x Hx.
apply phi_f; trivial.
apply phi_f; trivial.
apply phi_iter_f.
apply phi_f; trivial.
trivial.
assert (L:(close (iter f (S n) a) (iter f n a))).
apply close_trans with a.
apply IH.
apply le_n.
apply close_sym.
apply IH.
apply le_S, le_n.
apply L.
exists (fun x => close x a).
split.
exists 0%nat.
intros n _; apply H0.
intros u v Hu Hv.
assert (close u v).
apply close_trans with a; try assumption.
now apply close_sym.
apply H1.
Qed.

Lemma FixedPoint_aux1_phi : forall (a:X), is_contraction_phi f phi -> phi a ->
  let  x := lim  (fun P => eventually (fun n => P (iter f n a))) in
      close (f x) x.
Proof.
intros a Hf Phi_a x.
generalize (complete_cauchy
   (fun P => eventually (fun n => P (iter f n a)))
    (Fixed_Point_aux_Proper_phi a)
    (Fixed_Point_aux_cauchy_phi _ Hf Phi_a)).
replace ((Hierarchy.lim
         (fun P : X -> Prop => eventually (fun n0 : nat => P (iter f n0 a))))) with x by reflexivity.
intros H eps.
pose (e2 :=mkposreal _ (is_pos_div_2 eps)).
specialize (H e2).
destruct H as (n,Hn).
replace (pos eps) with (pos e2 + pos e2).
2: simpl; field.
apply ball_sym.
apply ball_triangle with (iter f (S n) a).
apply Hn.
apply le_S, le_n.
generalize Hf; intro Hf'.
destruct Hf as (k,(Hk1,(Hk2,Hk3))).
apply ball_le with (k*e2).
rewrite <- (Rmult_1_l e2) at 2.
apply Rmult_le_compat_r.
destruct e2; left; now simpl.
now left.
simpl.
apply Hk3.
apply (cond_pos e2).
apply phi_iter_f.
intros xx Hxx.
apply phi_f; trivial.
trivial.
unfold x.
unfold my_complete in phi_c.
apply phi_c.
apply Fixed_Point_aux_Proper_phi.
apply Fixed_Point_aux_cauchy_phi.
trivial.
trivial.
intros P Hev.
intro.
apply H.
unfold eventually in Hev.
destruct Hev as (N,Hev).
specialize (Hev (N+1)%nat).
assert (Hev' : P (iter f (N+1) a)).
apply Hev.
intuition.
exists (iter f (N+1) a).
split; try assumption.
apply phi_iter_f.
trivial.
trivial.
apply ball_sym.
apply Hn.
apply le_n.
Qed.

Hypothesis phi_X_not_empty: exists (a:X), phi a.
Hypothesis phi_closed: my_complete phi.

Lemma FixedPoint_aux2_phi : forall (a:X), is_contraction_phi f phi -> phi a ->
  let  x := lim
  (fun P => eventually (fun n => P (iter f n a))) in
      phi x.
Proof.
intros a Hf Phi_a x.
apply phi_closed.
apply Fixed_Point_aux_Proper_phi.
now apply Fixed_Point_aux_cauchy_phi.
intros P (N,HN).
intros K; apply K.
exists (iter f N a).
split.
apply HN.
apply le_n.
now apply phi_iter_f.
Qed.

Theorem FixedPoint_C_phi : is_contraction_phi f phi ->
   exists a:X,
     phi a
      /\ close (f a) a
      /\ (forall b, phi b -> close (f b) b -> close b a) /\
    forall x, phi x -> close (lim  (fun P => eventually (fun n => P (iter f n x)))) a.
Proof.
intros Hf.
destruct phi_X_not_empty as (a, Ha).
exists (lim (fun P => eventually (fun n => P (iter f n a)))).
split.
now apply FixedPoint_aux2_phi.
split.
now apply FixedPoint_aux1_phi.
split.
intros b Phi_b Hb.
apply FixedPoint_uniqueness_weak_phi; try assumption.
now apply FixedPoint_aux2_phi.
now apply FixedPoint_aux1_phi.
intros x Phi_x.
apply FixedPoint_uniqueness_weak_phi; try assumption.
now apply FixedPoint_aux2_phi.
now apply FixedPoint_aux2_phi.
now apply FixedPoint_aux1_phi.
now apply FixedPoint_aux1_phi.
Qed.

End FixedPoint_2_sub.
