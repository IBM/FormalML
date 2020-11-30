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
Require Export R_compl.
Require Import mathcomp.ssreflect.ssreflect.
Require Import FunctionalExtensionality.
Require Import Decidable.
Require Export logic_tricks.
Require Import Equivalence Morphisms.

Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.

(** Complete subsets *)

Section CompleteSubset.

Context {E : NormedModule R_AbsRing}.

Definition complete_subset (phi:E->Prop) :=
  exists (lime : ((E -> Prop) -> Prop) -> E),
  (forall F, ProperFilter F -> cauchy F ->
     (forall P, F P -> ~~(exists x, P x /\ phi x)) ->
          phi (lime F) /\
          forall eps : posreal, F (ball (lime F) eps)).

End CompleteSubset.

(** * PreHilbert spaces *)

Module PreHilbert.

Record mixin_of (E : ModuleSpace R_Ring) (RE:E->E->Prop) {eqRE:Equivalence RE} := Mixin {
  inner : E -> E -> R ;
  prop : Proper (equiv ==> equiv ==> eq) inner;
  ax1 : forall (x y : E), inner x y = inner y x ;
  ax2 : forall (x : E), 0 <= inner x x ;
  ax3 : forall (x : E), inner x x = 0 -> RE x zero ;
  ax4 : forall (x y : E) (l:R), inner (scal l x) y = l * inner x y ;
  ax5 : forall (x y z : E), inner (plus x y) z = inner x z + inner y z
}.

Section ClassDef.

Record class_of (T : Type) := Class {
 base : ModuleSpace.class_of R_Ring T ;
 
 RE : ModuleSpace.Pack R_Ring T base T -> ModuleSpace.Pack R_Ring T base T -> Prop ;
 eqRE : Equivalence RE ;
  mixin : mixin_of (ModuleSpace.Pack R_Ring T base T) RE (eqRE:=eqRE)
                                }.

Local Coercion base : class_of >-> ModuleSpace.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> ModuleSpace.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.

Notation PreHilbert := type.

End Exports.

End PreHilbert.

Export PreHilbert.Exports.

Section AboutPreHilbert.

Context {E : PreHilbert}.
Definition RE := PreHilbert.RE _ (PreHilbert.class E).
Definition eqRE := PreHilbert.eqRE _ (PreHilbert.class E).
Existing Instance eqRE.


Definition inner : E -> E -> R := PreHilbert.inner E RE (PreHilbert.mixin _ (PreHilbert.class E)).

Definition Hnorm x := sqrt (inner x x).

Lemma inner_is_bilinear_form: is_bilinear_mapping inner.
Proof.
split.
apply PreHilbert.ax4.
split.
 + intros x0 y0 l0.
  replace (inner x0 (scal l0 y0)) with (inner (scal l0 y0) x0).
  replace (inner x0 y0) with (inner y0 x0).
  apply PreHilbert.ax4.
  apply PreHilbert.ax1.
  apply PreHilbert.ax1.
+  split.
  apply PreHilbert.ax5.
+  intros x2 y2 z0.
  replace (inner x2 (plus y2 z0)) with (inner (plus y2 z0) x2).
  replace (inner x2 y2) with (inner y2 x2).
  replace (inner x2 z0) with (inner z0 x2).
  apply PreHilbert.ax5.
  apply PreHilbert.ax1.
  apply PreHilbert.ax1.
  apply PreHilbert.ax1.
Qed.

Lemma inner_sym: forall x y,  inner x y = inner y x.
Proof.
apply PreHilbert.ax1.
Qed.

Lemma inner_ge_0: forall x, 0 <= inner x x.
Proof.
apply PreHilbert.ax2.
Qed.

Lemma inner_eq_0 : forall x, inner x x = 0 -> RE x zero.
Proof.
apply PreHilbert.ax3.
Qed.

Lemma norm_ge_0: forall x,  0 <= Hnorm x.
Proof.
intros x; apply sqrt_pos.
Qed.

Lemma norm_eq_0: forall x,  Hnorm x = 0 -> RE x zero.
Proof.
intros x; unfold norm; intros H.
assert (inner x x = 0).
apply sqrt_eq_0; trivial.
apply inner_ge_0.
apply (PreHilbert.ax3 _ _ _ _ H0).
Qed.

Lemma inner_scal_l: forall (x y :E) (l:R), inner (scal l x) y = l * inner x y.
Proof.
apply PreHilbert.ax4.
Qed.

Lemma inner_scal_r: forall (x y :E) (l:R), inner x (scal l y) = l * inner x y.
Proof.
intros x y l.
now rewrite inner_sym inner_scal_l inner_sym.
Qed.

Lemma inner_zero_l: forall x, inner zero x = 0.
Proof.
intros x.
apply trans_eq with (inner (scal 0 zero) x).
now rewrite scal_zero_r.
rewrite inner_scal_l.
apply Rmult_0_l.
Qed.

Lemma inner_zero_r: forall x, inner x zero = 0.
Proof.
intros x.
rewrite inner_sym; apply inner_zero_l.
Qed.

Lemma inner_plus_l : forall (x y z : E), inner (plus x y) z = inner x z + inner y z.
Proof.
apply PreHilbert.ax5.
Qed.

Lemma inner_plus_r : forall (x y z : E), inner x (plus y z) = inner x y + inner x z.
Proof.
intros x y z.
now rewrite inner_sym inner_plus_l 2!(inner_sym x).
Qed.

Lemma inner_opp_r: forall (x y : E), inner x (opp y) = - inner x y.
Proof.
intros x y.
rewrite - (scal_opp_one y).
rewrite inner_scal_r.
unfold opp, one; simpl; ring.
Qed.

Lemma inner_opp_l: forall (x y : E), inner (opp x) y = - inner x y.
intros x y.
now rewrite inner_sym inner_opp_r inner_sym.
Qed.

Lemma norm_zero: Hnorm zero = 0.
Proof.
unfold Hnorm; now rewrite inner_zero_l sqrt_0.
Qed.

Lemma norm_opp: forall x, Hnorm (opp x) = Hnorm x.
Proof.
intros x; unfold Hnorm; apply f_equal.
replace (opp x) with (scal (opp one) x).
rewrite inner_scal_l inner_scal_r.
unfold opp, one; simpl.
ring.
now rewrite (scal_opp_one x).
Qed.

Lemma norm_scal : forall l x, Hnorm (scal l x) = Rabs l * Hnorm x.
intros l x; unfold Hnorm.
rewrite <- sqrt_Rsqr_abs.
rewrite <- sqrt_mult.
2: apply Rle_0_sqr.
2: apply inner_ge_0.
apply f_equal.
rewrite inner_scal_l inner_scal_r.
unfold Rsqr; ring.
Qed.

Lemma squared_norm: forall x, Hnorm x * Hnorm x = inner x x.
Proof.
intros x; unfold norm.
apply sqrt_sqrt.
apply inner_ge_0.
Qed.

Lemma square_expansion_plus: forall x y,
  inner (plus x y) (plus x y) = inner x x + 2 * inner x y + inner y y.
Proof.
intros x y.
rewrite inner_plus_l 2!inner_plus_r.
rewrite (inner_sym x y).
ring.
Qed.

Lemma square_expansion_minus: forall x y,
  inner (minus x y) (minus x y) = inner x x - 2 * inner x y + inner y y.
Proof.
intros x y.
rewrite inner_plus_l 2!inner_plus_r.
rewrite inner_opp_r.
rewrite inner_opp_l.
rewrite inner_opp_r.
rewrite inner_opp_l.
rewrite inner_sym.
ring.
Qed.

(** Equalities and inequalities *)

Lemma parallelogram_id: forall x y,
  (inner (plus x y) (plus x y)) + (inner (minus x y) (minus x y))
  = 2*((inner x x) + (inner y y)).
Proof.
intros x y.
rewrite square_expansion_plus.
rewrite square_expansion_minus.
ring.
Qed.

Lemma Cauchy_Schwartz: forall x y,
   Rsqr (inner x y) <= inner x x * inner y y.
Proof.
intros x y.
apply Rmult_le_reg_l with 4%R.
apply Rmult_lt_0_compat; apply Rlt_0_2.
apply Rminus_le; rewrite <- Rmult_assoc.
replace (4*Rsqr (inner x y)) with ((2*inner x y)*(2*inner x y)).
2: unfold Rsqr; ring.
apply discr_neg.
intros l.
apply Rle_trans with (inner (plus (scal l x) y) (plus (scal l x) y)).
apply inner_ge_0.
rewrite square_expansion_plus.
rewrite 2!inner_scal_l inner_scal_r.
right; ring.
Qed.

Lemma Cauchy_Schwartz_with_norm: forall x y,
   Rabs (inner x y) <= Hnorm x * Hnorm y.
Proof.
intros x y.
apply Rsqr_incr_0_var.
rewrite <- Rsqr_abs.
apply Rle_trans with (1:=Cauchy_Schwartz _ _).
rewrite Rsqr_mult; unfold Rsqr; right.
now rewrite 2!squared_norm.
apply Rmult_le_pos; apply norm_ge_0.
Qed.

Lemma norm_triangle: forall x y, Hnorm (plus x y) <= Hnorm x + Hnorm y.
Proof.
intros x y.
apply Rsqr_incr_0_var; unfold Rsqr.
rewrite squared_norm.
rewrite square_expansion_plus.
rewrite <- 2!squared_norm.
apply Rle_trans with (Hnorm x * Hnorm x + 2 * (Hnorm x*Hnorm y) + Hnorm y * Hnorm y).
apply Rplus_le_compat_r, Rplus_le_compat_l, Rmult_le_compat_l.
left; apply Rlt_0_2.
apply Rle_trans with (1:=RRle_abs _).
apply Cauchy_Schwartz_with_norm.
right; ring.
apply Rplus_le_le_0_compat; apply norm_ge_0.
Qed.

End AboutPreHilbert.

(** PreHilbert is NormedModule *)

Section PreHNormedModule.

Context {E : PreHilbert}.

Definition ball := fun (x:E) eps y => Hnorm (minus x y) < eps.

Lemma ball_center :
  forall (x : E) (e : posreal),
  ball x e x.
Proof.
intros x z; unfold ball, minus.
rewrite plus_opp_r norm_zero.
apply cond_pos.
Qed.

Lemma ball_sym :
  forall (x y : E) (e : R),
  ball x e y -> ball y e x.
Proof.
intros x y e; unfold ball; intros H.
apply Rle_lt_trans with (2:=H); right.
rewrite <- norm_opp.
apply f_equal.
unfold minus; rewrite opp_plus.
now rewrite plus_comm opp_opp.
Qed.

Lemma ball_triangle :
  forall (x y z : E) (e1 e2 : R),
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof.
intros x y z e1 e2; unfold ball; intros H1 H2.
replace (minus x z) with (plus (minus x y) (minus y z)).
apply Rle_lt_trans with (1:=norm_triangle _ _).
now apply Rplus_lt_compat.
unfold minus; rewrite plus_assoc.
apply f_equal2; trivial.
rewrite <- plus_assoc, plus_opp_l.
apply plus_zero_r.
Qed.

Definition PreHilbert_UniformSpace_mixin :=
  UniformSpace.Mixin E ball ball_center ball_sym ball_triangle.

Canonical PreHilbert_UniformSpace :=
  UniformSpace.Pack E (PreHilbert_UniformSpace_mixin) E.

Canonical PreHilbert_NormedModuleAux :=
  NormedModuleAux.Pack R_AbsRing E
   (NormedModuleAux.Class R_AbsRing E
     (ModuleSpace.class _ (PreHilbert.ModuleSpace E))
        PreHilbert_UniformSpace_mixin) E.

Lemma norm_ball1 : forall (x y : E) (eps : R),
          Hnorm (minus y x) < eps -> Hierarchy.ball x eps y.
Proof.
intros x y eps H.
unfold Hierarchy.ball; simpl.
apply ball_sym.
unfold ball; now simpl.
Qed.

Lemma norm_ball2: forall (x y : E) (eps : posreal),
          Hierarchy.ball x eps y -> Hnorm (minus y x) < 1 * eps.
Proof.
intros x y eps.
rewrite Rmult_1_l.
unfold Hierarchy.ball; simpl.
intros H; apply ball_sym in H.
exact H.
Qed.

Lemma norm_scal_aux:
  (forall (l : R) (x : E), Hnorm (scal l x) <= abs l * Hnorm x).
Proof.
intros l r.
rewrite norm_scal.
apply Rle_refl.
Qed.

Definition PreHilbert_NormedModule_mixin :=
  NormedModule.Mixin R_AbsRing _
   Hnorm 1%R norm_triangle norm_scal_aux norm_ball1 norm_ball2 norm_eq_0.

Canonical PreHilbert_NormedModule :=
  NormedModule.Pack R_AbsRing E
     (NormedModule.Class _ _ _ PreHilbert_NormedModule_mixin) E.

End PreHNormedModule.
(** * Hilbert spaces *)

Module Hilbert.

Record mixin_of (E : PreHilbert) := Mixin {
  lim : ((E -> Prop) -> Prop) -> E ;
  ax1 : forall F, ProperFilter F -> cauchy F ->
          forall eps : posreal, F (ball (lim F) eps)
}.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : PreHilbert.class_of T ;
  mixin : mixin_of (PreHilbert.Pack T base T)
}.

Local Coercion base : class_of >-> PreHilbert.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition PreHilbert := PreHilbert.Pack cT xclass xT.
End ClassDef.

Module Exports.

Coercion base : class_of >-> PreHilbert.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion PreHilbert : type >-> PreHilbert.type.
Canonical PreHilbert.

Notation Hilbert := type.

End Exports.

End Hilbert.

Export Hilbert.Exports.

Canonical Hilbert_UniformSpace (E : Hilbert) :=
  UniformSpace.Pack E (PreHilbert_UniformSpace_mixin) E.

Canonical Hilbert_NormedModule (E : Hilbert) :=
  NormedModule.Pack R_AbsRing E
     (NormedModule.Class _ _ _ PreHilbert_NormedModule_mixin) E.

Coercion Hilbert_NormedModule: Hilbert >-> NormedModule.

(** Hilbert is a CompleteScape *)

Section Hilbert_aux.

Context {E : Hilbert}.

Definition lim : ((E -> Prop) -> Prop) -> E :=
   Hilbert.lim _ (Hilbert.class E).

Lemma Hilbert_complete:
   forall (F:(E->Prop)->Prop), ProperFilter F
       -> cauchy F ->
          forall eps : posreal, F (ball (lim F) eps).
Proof.
intros F H1 H2 eps.
apply (Hilbert.ax1 _ _ F H1 H2 eps).
Qed.

Lemma Hilbert_close_lim : 
   forall F1 F2 : (E -> Prop) -> Prop,
      filter_le F1 F2 ->
      filter_le F2 F1 -> close (lim F1) (lim F2).
Proof.
intros F1 F2 H1 H2.
replace F1 with F2.
apply close_refl.
apply functional_extensionality.
intros x.
unfold filter_le in *.
apply prop_extensionality; split.
apply H1.
apply H2.
Qed.

Definition Hilbert_CompleteSpace_mixin :=
  CompleteSpace.Mixin PreHilbert_UniformSpace lim Hilbert_complete Hilbert_close_lim.

Canonical Hilbert_CompleteSpace :=
  CompleteSpace.Pack E (CompleteSpace.Class _ _ Hilbert_CompleteSpace_mixin) E.

Canonical Hilbert_CompleteNormedModule :=
  CompleteNormedModule.Pack R_AbsRing E
    (CompleteNormedModule.Class R_AbsRing E
       (NormedModule.class _ PreHilbert_NormedModule)
        Hilbert_CompleteSpace_mixin) E.

End Hilbert_aux.

(** Convexity *)

Section Convex.

Context {E : ModuleSpace R_Ring}.

Definition convex (phi:E ->Prop) :=
   forall (u v:E) (theta:R), phi u -> phi v -> 0 <= theta <=1
     -> phi (plus (scal theta u) (scal (1-theta) v)).

End Convex.

(** Orthogonal projection *)

Section OrthogonalP.

Context {E : PreHilbert}.

Variable phi:E -> Prop.

Hypothesis phi_nonempty: exists y:E, phi y.
Hypothesis phi_convex: convex phi.

(* orthogonal projection onto nonempty complete convex *)
Lemma ortho_projection_aux: forall u:E,
  is_finite (Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w))).
Proof.
intros u.
destruct phi_nonempty as (y,Hy).
apply is_finite_betw with 0 (norm (minus u y)).
apply Glb_Rbar_correct.
intros x (w,(H1,H2)).
rewrite H2; simpl.
apply norm_ge_0.
apply Glb_Rbar_correct.
exists y; now split.
Qed.

Theorem ortho_projection_convex': complete_subset phi ->
   forall u:E,
   (forall eps:posreal, decidable (exists w:E, phi w /\ norm (minus u w) < eps)) ->
  exists v:E,
    phi v /\ norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)).
Proof.
intros (lime, Hlime) u Du.
destruct phi_nonempty as (y,Hy).
(* *)
pose (delta:= real (Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)))).
assert (Hdelta:0 <= delta).
assert (Rbar_le 0 (Glb_Rbar
              (fun r : R => exists w : E, phi w /\ r = norm (minus u w)))).
apply Glb_Rbar_correct.
intros x (w,(H1,H2)).
rewrite H2; simpl.
apply norm_ge_0.
unfold delta in H; rewrite <- (ortho_projection_aux u) in H; easy.
assert (V: forall eps:posreal, 0 < delta + eps).
intros eps.
apply Rlt_le_trans with eps.
apply cond_pos.
apply Rplus_le_reg_l with (-eps); ring_simplify; assumption.
(* *)
assert (Kr: forall eps:posreal, ~~exists x, phi x /\ norm (minus u x) < delta + eps).
intros eps H.
absurd (Rbar_lt (Glb_Rbar
              (fun r : R => exists w : E, phi w /\ r = norm (minus u w))) (delta + eps)).
apply Rbar_le_not_lt.
apply Glb_Rbar_correct.
intros r Hr; simpl.
case (Rle_or_lt (delta + eps) r); try easy.
intros Hr'.
exfalso; apply H.
destruct Hr as (w, (J1,J2)).
exists w; split; try assumption.
now rewrite <- J2.
rewrite <- (ortho_projection_aux u); simpl; fold delta.
apply Rplus_lt_reg_l with (-delta); ring_simplify.
apply cond_pos.
assert (Kr': forall eps:posreal, exists x, phi x /\ norm (minus u x) < delta + eps).
intros eps.
apply logic_dec_notnot.
apply (Du (mkposreal _ (V eps))).
exact (Kr eps).
pose (F:=fun (f:E->Prop) => exists eps:posreal, forall x, phi x ->
                  norm (minus u x) < delta + eps -> f x).
(* *)
assert (ProperFilter F).
split.
(* . *)
unfold F; intros P (eps,Heps).
destruct (Kr' eps) as (x,(Hx1,Hx2)).
exists x.
now apply Heps.
(* . *)
split.
(* .. *)
unfold F; simpl.
exists (mkposreal _ Rlt_0_1); easy.
(* .. *)
intros P Q (e1,HP2) (e2,HQ2).
assert (V':0 < Rmin e1 e2).
apply Rmin_pos; apply cond_pos.
exists (mkposreal _ V').
intros x Hx1 Hx2; split.
apply HP2; try assumption.
apply Rlt_le_trans with (1:=Hx2).
apply Rplus_le_compat_l.
simpl; apply Rmin_l.
apply HQ2; try assumption.
apply Rlt_le_trans with (1:=Hx2).
apply Rplus_le_compat_l.
simpl; apply Rmin_r.
(* .. *)
intros P Q H (e,HP2).
exists e.
intros x Hx1 Hx2.
apply H.
now apply HP2.
(* *)
assert (cauchy F); unfold cauchy.
intros eps.
pose (eta:= match (Req_EM_T delta 0) with
  | left _ => eps/2
  | right _ => Rmin ((eps*eps)/(16*delta)) (eps/(2*sqrt 2))
    end).
assert (Keta: 0 < eta).
unfold eta; case (Req_EM_T delta 0); intros Hd.
apply Rlt_le_trans with (pos (pos_div_2 eps)).
apply cond_pos.
right; reflexivity.
apply Rmin_pos.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat; apply cond_pos.
apply Rinv_0_lt_compat.
apply Rmult_lt_0_compat.
repeat apply Rmult_lt_0_compat; apply Rlt_0_2.
case Hdelta; try easy.
intros Hd'; contradict Hd'.
now apply sym_not_eq.
apply Rmult_lt_0_compat.
apply cond_pos.
apply Rinv_0_lt_compat.
apply Rmult_lt_0_compat.
apply Rlt_0_2.
apply Rlt_sqrt2_0.
destruct (Kr' (mkposreal _ Keta)) as (f,(Hf1,Hf2)).
exists f.
exists (mkposreal _ Keta).
intros g Hg1 Hg2.
unfold Hierarchy.ball; simpl; unfold ball; simpl.
simpl in Hf2, Hg2.
(* . *)
assert (M:4*Rsqr (norm (minus u (scal (/2) (plus f g)))) + Rsqr (norm (minus f g)) =
           2*Rsqr (norm (minus u f)) + 2*Rsqr (norm (minus u g))).
unfold Rsqr at 3 4; rewrite 2!squared_norm.
rewrite <- Rmult_plus_distr_l.
rewrite <- parallelogram_id.
f_equal.
apply trans_eq with (Rsqr (2*norm (minus u (scal (/ 2) (plus f g))))).
unfold Rsqr; ring.
replace 2 with (abs 2) at 1.
2: apply Rabs_right; left; apply Rlt_0_2.
rewrite <- norm_scal_R, <- squared_norm.
fold (Rsqr (Hnorm (plus (minus u f) (minus u g)))).
f_equal.
unfold norm; simpl; f_equal.
rewrite scal_distr_l scal_opp_r scal_assoc.
replace (@mult R_AbsRing 2 (/2)) with 1.
2: unfold mult; simpl; field.
rewrite scal_one.
replace 2 with (plus 1 1).
2: unfold plus; simpl; ring.
rewrite scal_distr_r scal_one.
unfold minus; rewrite <- 2!plus_assoc; f_equal.
rewrite opp_plus 2!plus_assoc; f_equal.
apply plus_comm.
rewrite <- squared_norm.
fold (Rsqr (Hnorm (minus (minus u f) (minus u g)))).
f_equal.
rewrite <- norm_opp.
unfold norm; simpl; f_equal.
unfold minus.
rewrite 2!opp_plus 2!opp_opp.
rewrite plus_assoc; f_equal.
rewrite plus_comm plus_assoc.
now rewrite plus_opp_r plus_zero_l.
(* . *)
apply Rsqr_incrst_0.
2: apply norm_ge_0.
2: left; apply cond_pos.
apply Rle_lt_trans with (-4 * (norm (minus u (scal (/ 2) (plus f g))))² +
    2 * (norm (minus u f))² + 2 * (norm (minus u g))²).
right.
apply Rplus_eq_reg_l with (4 * (norm (minus u (scal (/ 2) (plus f g))))²).
rewrite M; ring.
apply Rle_lt_trans with (-4*Rsqr delta+2 * (norm (minus u f))² +2 * (norm (minus u g))²).
apply Rplus_le_compat_r, Rplus_le_compat_r.
apply Rmult_le_compat_neg_l.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply Rmult_le_pos; left; apply Rlt_0_2.
apply Rsqr_incr_1; try assumption.
assert (H2:Rbar_le (Glb_Rbar (fun r : R => exists w0 : E, phi w0
  /\ r = norm (minus u w0))) (norm (minus u (scal (/ 2) (plus f g))))).
apply Glb_Rbar_correct.
exists (scal (/ 2) (plus f g)); split; try easy.
replace (scal (/ 2) (plus f g)) with
   (plus (scal (/2) f) (scal (1-/2) g)).
apply phi_convex; try assumption.
split.
left; apply pos_half_prf.
apply Rmult_le_reg_l with 2.
apply Rlt_0_2.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply Rplus_le_reg_l with (-1); ring_simplify.
apply Rle_0_1.
apply Rgt_not_eq, Rlt_0_2.
replace (1-/2) with (/2) by field.
now rewrite scal_distr_l.
rewrite <- ortho_projection_aux in H2; easy.
apply norm_ge_0.
apply Rlt_le_trans with (-4*delta²+2*(delta+eta)²+2*(delta+eta)²).
apply Rplus_lt_compat.
apply Rplus_lt_compat_l.
apply Rmult_lt_compat_l.
apply Rlt_0_2.
apply Rsqr_incrst_1; try assumption.
apply norm_ge_0.
apply Rplus_le_le_0_compat; try assumption; now left.
apply Rmult_lt_compat_l.
apply Rlt_0_2.
apply Rsqr_incrst_1; try assumption.
apply norm_ge_0.
apply Rplus_le_le_0_compat; try assumption; now left.
apply Rle_trans with  (8*delta*eta+4*eta*eta).
right; unfold Rsqr; ring.
apply Rle_trans with ((Rsqr eps) / 2 + (Rsqr eps) / 2).
2: right; field.
case (Req_EM_T delta 0); intros Y.
replace eta with (eps/2).
rewrite Y; right; unfold Rsqr; field.
unfold eta; case (Req_EM_T delta 0); easy.
apply Rplus_le_compat.
apply Rle_trans with (8*delta*(eps * eps / (16 * delta))).
apply Rmult_le_compat_l.
apply Rmult_le_pos; try assumption.
apply Rmult_le_pos; try apply Rmult_le_pos; left; apply Rlt_0_2.
unfold eta; case (Req_EM_T delta 0); try easy.
intros _; apply Rmin_l.
unfold Rsqr; right; field; assumption.
assert (eta <= eps / (2 * sqrt 2)).
unfold eta; case (Req_EM_T delta 0); try easy.
intros _; apply Rmin_r.
apply Rle_trans with (4*(eps / (2 * sqrt 2))*(eps / (2 * sqrt 2))).
apply Rmult_le_compat; try (left; exact Keta); try assumption.
apply Rmult_le_pos; try (left; exact Keta).
apply Rmult_le_pos; left; apply Rlt_0_2.
apply Rmult_le_compat_l; try assumption.
apply Rmult_le_pos; left; apply Rlt_0_2.
apply Rle_trans with (eps²/((sqrt 2)²)).
right; unfold Rsqr; field.
apply Rgt_not_eq; apply Rlt_sqrt2_0.
rewrite Rsqr_sqrt.
now right.
left; apply Rlt_0_2.
(* *)
assert (forall P, F P -> ~ ~ (exists x : PreHilbert_NormedModule, P x /\ phi x)).
unfold F; intros P (n,Hn) K.
apply K.
destruct (Kr' n) as (x,(Hx1,Hx2)).
exists x; split; try assumption.
now apply Hn.
specialize (Hlime F H H0 H1).
destruct Hlime as (T1,T2).
exists (lime F).
split.
exact T1.
fold delta.
apply @filterlim_locally_unique with (F:=F)
   (f:=fun x => norm (minus u x)).
now apply Proper_StrongProper.
apply filterlim_comp with (G:=locally (minus u (lime F))).
unfold filterlim, filter_le, filtermap.
intros P (e,He).
pose (v:=@norm_factor R_AbsRing (@PreHilbert_NormedModule E)).
assert (J: 0 < e/v).
apply Rmult_lt_0_compat.
apply cond_pos.
apply Rinv_0_lt_compat.
apply norm_factor_gt_0.
destruct (T2 (mkposreal _ J)) as (eps, Heps).
exists eps.
intros w Hw1 Hw2.
apply He.
apply: norm_compat1.
unfold norm at 1; simpl.
apply Rle_lt_trans with (Hnorm (minus (lime F) w)).
right; f_equal.
unfold minus; rewrite plus_comm.
rewrite plus_assoc; f_equal.
rewrite opp_plus plus_comm.
rewrite plus_assoc.
rewrite plus_opp_r plus_zero_l.
apply opp_opp.
replace (pos e) with (v*(mkposreal _ J)).
unfold v at 1.
apply (norm_compat2 w (lime F) (mkposreal _ J)).
apply ball_sym.
now apply Heps.
simpl; field.
apply Rgt_not_eq, norm_factor_gt_0.
apply: filterlim_norm.
unfold filterlim, filter_le, filtermap, F.
intros P (e,He).
exists e; intros w Hw1 Hw2.
apply He.
apply norm_compat1.
unfold norm at 1; simpl.
unfold abs; simpl.
rewrite Rabs_right.
unfold minus at 1; unfold plus, opp; simpl.
apply Rplus_lt_reg_l with delta; ring_simplify.
exact Hw2.
unfold minus at 1; unfold plus, opp; simpl.
apply Rle_ge.
apply Rplus_le_reg_l with delta; ring_simplify.
assert (H2:Rbar_le (Glb_Rbar (fun r : R => exists w0 : E, phi w0
  /\ r = norm (minus u w0))) (norm (minus u w))).
apply Glb_Rbar_correct.
exists w; now split.
rewrite <- ortho_projection_aux in H2; easy.
Qed.

Theorem ortho_projection_convex_unique: complete_subset phi ->
   forall u:E, forall v v':E,
    phi v -> norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w))
   -> phi v' -> norm (minus u v')
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w))
   -> v = v'.
intros H u v v' H0 H1 H2 H3.
rewrite <- H3 in H1.
pose (a := minus u v').
pose (b := minus u v).
pose (v'' := scal (1/2) (plus v v')).
pose (d := norm (minus u v)).
assert (E1 : plus (4*((norm (minus u v''))*(norm (minus u v''))))
                  ((norm (minus v v'))*(norm (minus v v')))
             = 4*(d*d)).
assert (E2 : plus ((norm (plus a b))*(norm (plus a b)))
                  ((norm (minus a b))*(norm (minus a b)))
             = 4*(d*d)).
rewrite squared_norm.
rewrite squared_norm.
replace ((plus
       (inner (plus a b) (plus a b))
       (inner (minus a b) (minus a b))))
       with
       ((inner (plus a b) (plus a b)) +
       (inner (minus a b) (minus a b)))
       by reflexivity.
rewrite parallelogram_id.
unfold d, a, b.
repeat (rewrite <- squared_norm).
replace ( Hnorm (minus u v')) with (norm ((minus u v')))
        by reflexivity.
replace ( Hnorm (minus u v)) with (norm ((minus u v)))
        by reflexivity.
rewrite <- H1.
ring_simplify.
reflexivity.
replace (plus (norm (plus a b) * norm (plus a b))
             (norm (minus a b) * norm (minus a b)))
         with
        (plus (4 * (norm (minus u v'') * norm (minus u v'')))
            (norm (minus v v') * norm (minus v v'))) in E2.
trivial.
replace (norm (minus a b)) with (norm (minus v v')).
unfold a, b.
unfold v''.
rewrite plus_comm.
rewrite (plus_comm _ ((norm (minus v v') * norm (minus v v')))).
apply Rplus_eq_compat_l.
replace (plus (minus u v') (minus u v))
       with (minus ((scal 2) u) (plus v v')).
unfold minus.
assert (H42 : (4 *(norm (plus u (opp (scal (1 / 2) (plus v v')))) *
             norm (plus u (opp (scal (1 / 2) (plus v v'))))))
       =((2*(norm (plus u (opp (scal (1 / 2) (plus v v'))))))*
         (2*(norm (plus u (opp (scal (1 / 2) (plus v v')))))))).
ring.
rewrite H42.
replace 2 with (Rabs 2) at 1.
replace 2 with (Rabs 2) at 3.
unfold norm; simpl.
rewrite <- norm_scal.
rewrite scal_distr_l.
rewrite <- scal_opp_r.
rewrite scal_assoc.
replace (mult 2 (1/2)) with 1.
rewrite scal_one.
reflexivity.
unfold mult.
simpl.
field.
unfold Rabs.
destruct (Rcase_abs 2).
absurd (2 < 0).
apply Rle_not_lt.
intuition.
trivial.
reflexivity.
unfold Rabs.
destruct (Rcase_abs 2).
absurd (2 < 0).
apply Rle_not_lt.
intuition.
trivial.
reflexivity.
unfold minus.
rewrite scal_distr_r.
rewrite scal_one.
rewrite opp_plus.
rewrite plus_assoc_gen.
rewrite plus_comm.
reflexivity.
unfold a, b.
unfold minus.
rewrite opp_plus.
rewrite plus_comm.
rewrite opp_opp.
rewrite (plus_comm (opp u) v).
rewrite plus_assoc.
rewrite <- (plus_assoc u (opp v') v).
rewrite (plus_comm u (plus (opp v') v)).
rewrite <- (plus_assoc (plus (opp v') v) u (opp u)).
rewrite plus_opp_r.
rewrite plus_zero_r.
reflexivity.
assert (Hmin : norm (minus v v') * norm (minus v v') <= 0).
replace 0 with (plus (4*(d*d)) (-4*(d*d))).
replace (norm (minus v v') * norm (minus v v')) with
       (minus (4*(d*d))
       (4 * (norm (minus u v'') * norm (minus u v'')))).
unfold minus.
apply Rplus_le_compat_l.
replace (-4 * (d * d)) with (opp (4*(d*d))).
assert (Has: opp (4 * (norm (plus u (opp v'')) * norm (plus u (opp v''))))
        = (-((4 * (norm (plus u (opp v'')) * norm (plus u (opp v''))))))).
reflexivity.
rewrite Has.
clear Has.
replace (opp (4 * (d * d))) with (-(4*(d*d))) by reflexivity.
apply Ropp_le_contravar.
assert (Hd : d <= norm (minus u v'')).
assert (HdGlb : d =
        Glb_Rbar (fun r : R => exists w : E, phi w
        /\ r = norm (minus u w))).
unfold d.
rewrite H1.
rewrite H3.
reflexivity.
unfold Glb_Rbar in HdGlb.
destruct (ex_glb_Rbar
  (fun r : R => exists w : E,
   phi w /\ r = norm (minus u w))).
simpl in HdGlb.
unfold is_glb_Rbar in HdGlb.
unfold is_glb_Rbar in i.
unfold is_lb_Rbar in i.
destruct i as (Hi1,Hi2).
assert (Hp :forall w : E,
    phi w -> (Rbar_le x) (norm (minus u w))).
intros. apply Hi1.
exists w.
split; trivial.
assert (Hf :Rbar_le x (norm (minus u v''))).
apply Hp.
unfold v''.
unfold convex in phi_convex.
replace (scal (1 / 2) (plus v v'))
        with
        (plus (scal (1/2) v) (scal (1/2) v')).
replace (1 / 2) with (1 - (1 / 2)) at 2 by field.
apply phi_convex; trivial.
split.
assert (Hs : 0 < 1 / 2).
apply Rdiv_lt_0_compat; intuition.
intuition.
apply Rmult_le_reg_r with 2.
intuition.
replace (1 / 2 * 2) with 1 by field.
replace 1 with (1*1) at 1 by ring.
apply Rmult_le_compat.
intuition. intuition.
apply Rle_refl.
intuition.
rewrite scal_distr_l.
reflexivity.
assert (Hrx : real x <= norm (minus u v'')).
unfold Rbar_le in Hf.
destruct x.
trivial.
intuition.
simpl.
apply norm_ge_0.
rewrite HdGlb.
trivial.
apply Rmult_le_compat; intuition.
apply Rmult_le_pos;
unfold d;
apply norm_ge_0.
apply Rmult_le_compat; trivial.
unfold d; apply norm_ge_0.
unfold d; apply norm_ge_0.
replace (opp (4 * (d * d))) with
        (opp (scal 4 (d*d))) by reflexivity.
rewrite <- scal_opp_l.
reflexivity.
rewrite <- E1.
unfold minus.
rewrite plus_comm.
rewrite plus_assoc.
rewrite plus_opp_l.
rewrite plus_zero_l.
reflexivity.
replace ((-4 * (d * d))) with (opp (4*(d*d))).
rewrite plus_opp_r.
reflexivity.
replace (opp (4 * (d * d))) with
        (opp (scal 4 (d*d))) by reflexivity.
rewrite <- scal_opp_l.
reflexivity.
assert (norm (minus v v') * norm (minus v v') = 0).
apply Rle_antisym.
trivial.
apply Rle_0_sqr.
assert (Hsq : norm (minus v v') = 0).
apply Rmult_integral in H4.
destruct H4; trivial.
apply norm_eq_zero in Hsq.
unfold minus in Hsq.
apply plus_reg_r with (opp v').
rewrite plus_opp_r.
trivial.
Qed.

Theorem ortho_projection_convex: complete_subset phi ->
   forall u:E,
  (forall eps:posreal, decidable (exists w:E, phi w /\ norm (minus u w) < eps)) ->
   exists! v:E,
    phi v /\ norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)).
Proof.
intros H u Hu.
apply unique_existence1; split.
now apply ortho_projection_convex'.
intros v v' Hv Hv'.
now apply ortho_projection_convex_unique with u.
Qed.

Lemma charac_ortho_projection_convex_aux1sq : forall u v w : E, forall t : R,
     phi v -> phi w -> 0 < t <= 1
      -> (norm (minus u v)) = (Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)))
     -> (((norm (minus u v)) <=
     (norm (minus u (plus (scal t w) (scal (1-t) v)))))).
Proof.
intros. unfold convex in *. simpl.
assert
     (is_glb_Rbar ((fun r : R => exists w : E, phi w /\ r = norm (minus u w)))
     (Glb_Rbar (fun r : R => exists w : E, phi w /\ r = norm (minus u w)))).
apply Glb_Rbar_correct.
destruct H3.
rewrite <- (ortho_projection_aux u) in H3, H4.
rewrite <- H2 in H3, H4. unfold is_lb_Rbar in H4.
intros. unfold is_lb_Rbar in H3. apply H3.
exists ((plus (scal t w) (scal (1 - t) v))); intuition.
Qed.

Lemma charac_ortho_projection_convex_aux1 : forall u v w : E, forall t : R,
    phi v -> phi w -> 0 < t <= 1
     -> (norm (minus u v)) = (Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)))
     -> (((norm (minus u v))*(norm (minus u v))) <=
       ((norm (minus u (plus (scal t w) (scal (1-t) v)))
        *(norm (minus u (plus (scal t w) (scal (1-t) v))))))).
Proof.
intros. unfold convex in *. simpl.
apply Rmult_le_compat.
apply norm_ge_0. apply norm_ge_0.
apply charac_ortho_projection_convex_aux1sq; intuition.
apply charac_ortho_projection_convex_aux1sq; intuition.
Qed.

Lemma charac_ortho_projection_convex_aux2 : forall u v w : E, forall t : R,
    phi v -> phi w -> 0 < t <= 1
    -> minus u (plus (scal t w) (scal (1-t) v))
        = plus (minus u v) (scal t (minus v w)).
Proof.
intros. unfold minus at 1.
rewrite scal_distr_r. rewrite scal_one. rewrite scal_opp_l.
rewrite opp_plus. rewrite (opp_plus v (opp (scal t v))).
rewrite opp_opp. rewrite plus_assoc. rewrite plus_assoc.
rewrite (plus_comm (plus u (opp (scal t w))) (opp v)).
rewrite plus_assoc. unfold minus at 1.
rewrite (plus_comm (opp v) u). unfold minus.
rewrite <- plus_assoc. rewrite <- scal_opp_l.
rewrite scal_distr_l.
rewrite (plus_comm (scal t v) (scal t (opp w))).
rewrite (scal_opp_l t w). rewrite (scal_opp_r t w).
reflexivity.
Qed.

Lemma charac_ortho_projection_convex_aux3 : forall u v w : E, forall t : R,
   phi v -> phi w -> 0 < t <= 1
   -> (norm (minus u (plus (scal t w) (scal (1-t) v))))*
       (norm (minus u (plus (scal t w) (scal (1-t) v))))
     =  (minus ((norm (minus u v))*(norm (minus u v)))
             ((2*t)*(inner (minus u v) (minus w v)))) +
            (t*t)*((norm (minus v w))*(norm (minus v w))).
Proof.
intros. rewrite charac_ortho_projection_convex_aux2; trivial.
rewrite squared_norm. rewrite square_expansion_plus.
rewrite squared_norm. rewrite squared_norm.
rewrite inner_scal_r. rewrite inner_scal_l.
rewrite inner_scal_r.
rewrite <- (opp_minus v w). rewrite inner_opp_r.
assert
      (t * (t * inner (minus v w) (minus v w)) =
       t * t * inner (minus v w) (minus v w)).
rewrite Rmult_assoc. trivial.
rewrite H2.
ring_simplify.
rewrite (Rplus_comm (inner (minus u v) (minus u v))
(t ^ 2 * inner (minus v w) (minus v w))).
rewrite Rplus_assoc.
f_equal.
rewrite Rplus_comm. symmetry.
unfold minus. rewrite plus_comm.
apply Rplus_plus_reg_r. rewrite <- opp_opp.
assert (Hminus : forall a, -a = opp a).
intros; reflexivity. rewrite Hminus.
assert (Hscal : forall a b, a*b = scal a b).
intros; reflexivity. rewrite Hscal.
rewrite scal_opp_r.
symmetry. rewrite Hscal. reflexivity.
Qed.

Lemma charac_ortho_projection_convex_aux4 : forall u v w : E, forall t : R,
   phi v -> phi w -> 0 < t <= 1
    -> (norm (minus u v))
        = (Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)))
    -> 0 <= (-(2*t*inner (minus u v) (minus w v))
            +(t*t)*((norm (minus v w))*(norm (minus v w)))).
Proof.
intros.
assert (Hminus : forall a, -a = opp a).
intros; reflexivity. rewrite Hminus.
apply Rplus_le_reg_l with
((norm (minus u v))*(norm (minus u v))).
rewrite Rplus_0_r.
assert (Hrew : norm (minus u v) * norm (minus u v) +
       (opp (2 * t * inner (minus u v) (minus w v)) +
       t * t * (norm (minus v w) * norm (minus v w)))
       =
        (minus ((norm (minus u v))*(norm (minus u v)))
              ((2*t)*(inner (minus u v) (minus w v)))) +
        (t*t)*((norm (minus v w))*(norm (minus v w)))).
assert (Hperm : forall a b c, a + (opp b + c) = (minus a b) + c).
intros. unfold minus. rewrite Rplus_assoc. reflexivity.
rewrite Hperm. reflexivity.
rewrite Hrew.
rewrite <- charac_ortho_projection_convex_aux3; trivial.
apply charac_ortho_projection_convex_aux1;
trivial.
Qed.

Lemma charac_ortho_projection_convex_aux5 :  forall u v w : E, forall t : R,
 phi v -> phi w -> 0 < t <= 1
  -> (norm (minus u v))
      = (Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)))
  -> (2*(inner (minus u v) (minus w v)))
          <= t*((norm (minus v w))*(norm (minus v w))) .
Proof.
intros.
apply Rmult_le_reg_l with t.
intuition.
apply Rplus_le_reg_l
   with (opp (t*(2 * inner (minus u v) (minus w v)))).
assert (Hplus : forall a b, a + b = plus a b).
intros; reflexivity.
assert (Hminus : forall a, -a = opp a).
intros; reflexivity.
rewrite Hplus. rewrite plus_opp_l.
rewrite <- Rmult_assoc. rewrite (Rmult_comm t 2).
rewrite <- Hminus.
rewrite <- (Rmult_assoc t t
  (norm (minus v w) * norm (minus v w))).
apply charac_ortho_projection_convex_aux4; intuition.
Qed.

Lemma charac_ortho_projection_convex_aux1_r : forall u v w :E, phi v ->
         phi w -> inner (minus u v) (minus w v) <= 0
         -> ((norm (minus u v) * norm (minus u v))
            <= ((norm (minus u w) * norm (minus u w)))).
intros.
assert (minus u w = plus (minus u v) (minus v w)).
unfold minus. rewrite (plus_comm u (opp v)).
rewrite plus_assoc_gen. rewrite plus_opp_l.
rewrite plus_zero_l. reflexivity.
rewrite H2.
rewrite (squared_norm (plus (minus u v) (minus v w))).
rewrite (square_expansion_plus (minus u v) (minus v w)).
apply Rle_trans with (inner (minus u v) (minus u v) +
  2 * inner (minus u v) (minus v w)).
rewrite squared_norm.
rewrite <- (Rplus_0_r (inner (minus u v) (minus u v))) at 1.
apply Rplus_le_compat_l; intuition.
apply Rmult_le_compat_l
  with 2 (inner (minus u v) (minus w v)) 0 in H1; intuition.
rewrite Rmult_0_r in H1.
assert ((minus v w) = opp (minus w v)).
rewrite opp_minus. reflexivity.
rewrite H3. rewrite inner_opp_r.
assert (Hscal : forall a b, a*b = scal a b).
intros; reflexivity.
rewrite Hscal.
assert (Hminus : forall a, -a = opp a).
intros; reflexivity.
rewrite Hminus.
rewrite scal_opp_r.
rewrite Hscal in H1. intuition.
rewrite <- (Rplus_0_r (inner (minus u v) (minus u v) +
            2 * inner (minus u v) (minus v w))) at 1.
apply Rplus_le_compat_l. rewrite <- squared_norm.
apply Rle_0_sqr.
Qed.

Definition th (u v w : E)  := Rmin 1 ((inner (minus u v) (minus w v))
                        /((norm (minus v w))*(norm (minus v w)))).

(* characterization of orthogonal projection onto convex *)
Lemma charac_ortho_projection_convex: forall u:E, forall v:E, phi v ->
   (norm (minus u v) = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w))
      <->
   (forall w:E, phi w -> inner (minus u v) (minus w v) <= 0)).
Proof.
intros; split.
+intros.
 destruct (Req_dec (norm (minus v w)*norm (minus v w)) 0).
 - assert (1*(norm (minus v w) * norm (minus v w)) = 0).
   rewrite H2. ring_simplify; reflexivity.
   apply Rmult_le_reg_l with 2%R. intuition.
   ring_simplify. rewrite <-H3.
   apply charac_ortho_projection_convex_aux5; intuition.
 - apply Rdichotomy in H2. destruct H2.
   absurd (norm (minus v w) * norm (minus v w) < 0).
   apply Rle_not_lt. apply (Rle_0_sqr (norm (minus v w))).
   trivial.
   destruct (Rle_lt_dec (inner (minus u v) (minus w v)) 0).
   * trivial.
   * absurd (0 < inner (minus u v) (minus w v)).
     assert
          (2*(inner (minus u v) (minus w v))
           <= (th u v w)*((norm (minus v w) * norm (minus v w)))).
     apply charac_ortho_projection_convex_aux5; intuition.
     unfold th. unfold Rmin.
     destruct (Rle_dec 1 (inner (minus u v) (minus w v)
               / (norm (minus v w) * norm (minus v w)))).
     intuition. apply Rdiv_lt_0_compat; intuition.
     apply Rmin_l.
     assert ((th u v w)*((norm (minus v w) * norm (minus v w)))
             <= (inner (minus u v) (minus w v))).
     apply Rmult_le_reg_r with
     (1 / (norm (minus v w) * norm (minus v w))).
     apply Rdiv_lt_0_compat; intuition.
     field_simplify.
     apply Rle_trans with ((th u v w) * / 1).
     field_simplify. intuition.
     rewrite Rinv_1.
     rewrite Rmult_1_r.
     apply Rle_trans with (1:=Rmin_r _ _).
     right; unfold pow, Rdiv.
     now rewrite Rmult_1_r.
     destruct (Req_dec (norm (minus v w)) 0).
     absurd (0 = 0). rewrite H4 in H2.
     ring_simplify in H2. apply Rlt_not_eq.
     intuition. intuition. trivial.
     destruct (Req_dec (norm (minus v w)) 0).
     absurd (0 = 0). rewrite H4 in H2.
     ring_simplify in H2. apply Rlt_not_eq.
     intuition. intuition. trivial.
     assert (2*(inner (minus u v) (minus w v)) <=
            (inner (minus u v) (minus w v))).
     apply Rle_trans with
     (th u v w * (norm (minus v w) * norm (minus v w))); trivial.
     destruct (Rlt_dec 0 (inner (minus u v) (minus w v))).
     absurd ( 2 * inner (minus u v) (minus w v)
             <= inner (minus u v) (minus w v)).
     apply Rgt_not_le.
     rewrite <- (Rmult_1_l (inner (minus u v) (minus w v))).
     rewrite <- Rmult_assoc.
     apply Rmult_gt_compat_r. trivial. ring_simplify; intuition.
     trivial.
     trivial. trivial.
+intros.
 assert
      (forall w : E, phi w -> (norm (minus u v) <=
                              (norm (minus u w)))).
 intros.
 assert
      (forall w, minus u w = plus (minus u v) (minus v w)).
 unfold minus. symmetry. rewrite (plus_comm u (opp v)).
 rewrite plus_assoc_gen. rewrite plus_opp_l.
 rewrite plus_zero_l. reflexivity.
 assert
      (forall w : E, phi w -> ((norm (minus u v))*(norm (minus u v)) <=
      ((norm (minus u w)))*((norm (minus u w))))).
 intros. rewrite (H2 w0).
 rewrite (squared_norm (plus (minus u v) (minus v w0))).
 rewrite square_expansion_plus.
 rewrite <- (squared_norm (minus u v)).
 rewrite <- (squared_norm (minus v w0)).
 rewrite Rplus_assoc.
 rewrite <- (Rplus_0_r (norm (minus u v) * norm (minus u v))).
 rewrite squared_norm. rewrite <- squared_norm.
 apply (Rplus_le_compat_l (Hnorm (minus u v) * Hnorm (minus u v))
                             0 (2 * inner (minus u v) (minus v w0)
          + Hnorm (minus v w0) * Hnorm (minus v w0))).
 apply Rplus_le_le_0_compat.
 assert (2*0 = 0). ring_simplify; reflexivity.
 rewrite <- H4.
 apply Rmult_le_compat_l. intuition.
 rewrite <- (opp_minus w0 v). rewrite inner_opp_r.
 apply Ropp_le_cancel. ring_simplify. apply H0. trivial.
 apply Rle_0_sqr.
 destruct
 (Rle_dec (norm (minus u v)) (norm (plus (minus u v) (minus v w)))).
 rewrite <- (H2 w) in r. trivial.
 absurd (
       norm (minus u v) * norm (minus u v) <=
       norm (minus u w) * norm (minus u w)).
 apply Rlt_not_le. rewrite <- (H2 w) in n.
 apply Rnot_le_lt in n.
 apply (Rmult_le_0_lt_compat (norm (minus u w))
                             (norm (minus u v))
                             (norm (minus u w))
                             (norm (minus u v)))
 in n; trivial. apply norm_ge_0. apply norm_ge_0.
 apply H3; trivial.
 trivial.
 unfold Glb_Rbar.
 destruct (ex_glb_Rbar
 (fun r : R => exists w : E,
 phi w /\ r = norm (minus u w))). simpl.
 unfold is_glb_Rbar in i.
 unfold is_lb_Rbar in i.
 destruct i.
 assert (forall w : E,
 phi w -> (Rbar_le x) (norm (minus u w))).
 intros. apply H2.
 exists w. split; trivial.
 assert (Rbar_le x (norm (minus u v))).
 apply H2. exists v. split; trivial.
 assert (Rbar_le (norm (minus u v)) x).
 apply H3. intros.
 destruct H6 as (w0,(H61,H62)).
 rewrite H62. apply H1. trivial.
 apply Rbar_finite_eq.
 apply Rbar_le_antisym.
 destruct x.
 trivial. trivial. simpl in H5.
 exfalso. trivial.
 simpl in H6. exfalso. trivial.
 destruct x.
 trivial. trivial. simpl in H5.
 exfalso. trivial.
 simpl in H6. exfalso. trivial.
Qed.

End OrthogonalP.

Section OrthogonalQ.

Context {E : PreHilbert}.

Variable phi:E -> Prop.

Hypothesis phi_mod: compatible_m phi.
Hypothesis phi_compl: complete_subset phi.

Theorem ortho_projection_subspace:
   forall u:E, (forall eps:posreal, decidable (exists w:E, phi w /\ norm (minus u w) < eps)) ->
   exists! v:E,
    phi v /\ norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)).
Proof.
intros u Hu.
assert (phi_convex : convex phi).
unfold convex.
intros u0 v0 t Hu0 Hv0 Th01.
destruct phi_mod as ((g1,(s,g2)),mod2).
assert (H0 : scal (1 - t) v0 = opp (scal (opp (1 - t)) v0)).
rewrite scal_opp_l.
rewrite opp_opp. reflexivity.
rewrite H0.
apply g1.
apply mod2.
trivial.
apply mod2.
trivial.
apply unique_existence1; split.
apply ortho_projection_convex'; try easy.
exists zero.
apply (compatible_m_zero phi phi_mod).
intros v v' Hv Hv'.
apply (ortho_projection_convex_unique phi phi_convex phi_compl u); intuition.
Qed.

Lemma charac_ortho_projection_subspace1: forall u:E, forall v:E, phi v ->
   (norm (minus u v) = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w))
      <->
   (forall w:E, phi w -> inner (minus u v) (minus w v) <= 0)).
split.
+ apply charac_ortho_projection_convex; intuition.
  apply phi_mod. unfold convex. intros.
  assert
       (scal (1 - theta) v0 = opp (scal (1 - theta) (opp v0))).
  rewrite scal_opp_r. rewrite opp_opp; reflexivity.
  rewrite H3. apply phi_mod. apply phi_mod. trivial.
  apply phi_mod. rewrite <- scal_opp_one. apply phi_mod. trivial.
+ intros. apply charac_ortho_projection_convex; intuition.
  apply phi_mod. unfold convex. intros.
  assert
       (scal (1 - theta) v0 = opp (scal (1 - theta) (opp v0))).
  rewrite scal_opp_r. rewrite opp_opp; reflexivity.
  rewrite H4. apply phi_mod. apply phi_mod. trivial.
  apply phi_mod. rewrite <- scal_opp_one. apply phi_mod. trivial.
Qed.

End OrthogonalQ.

(** Orthogonal complement *)

Section ortho_compl.

Context {E : PreHilbert}.

Variable phi:E -> Prop.
Hypothesis phi_compat: compatible_m phi.
Hypothesis phi_compl: complete_subset phi.

Definition orth_compl := fun x:E => forall (y:E), phi y -> inner x y = 0.

Lemma orth_compl_compat: compatible_m orth_compl.
Proof.
repeat split; unfold orth_compl.
intros x y H1 H2 z Hz.
rewrite inner_plus_l (H1 _ Hz).
rewrite inner_opp_l.
rewrite (H2 _ Hz).
ring.
exists zero.
intros y Hy; apply inner_zero_l.
intros x l H1 y Hy.
rewrite inner_scal_l.
rewrite (H1 _ Hy); ring.
Qed.

Lemma trivial_orth_compl : forall u : E, ((forall v : E, inner u v = 0) <-> u = zero).
intros; split.
intro H0. assert (inner u u = 0). apply H0; trivial.
apply PreHilbert.ax3 in H. trivial.
intros. rewrite H. rewrite inner_zero_l; reflexivity.
Qed.

Lemma trivial_orth_compl' : forall (phi : E -> Prop) (u : E),
       closed phi -> phi u -> ((forall v : E, phi v -> inner u v = 0) <-> u = zero).
intros; split.
intro H1. assert (inner u u = 0). apply H1; trivial.
apply PreHilbert.ax3 in H2. trivial.
intros. rewrite H1. rewrite inner_zero_l; reflexivity.
Qed.

(* direct sum with orthogonal complement when complete *)
Lemma direct_sumable_with_orth_compl: direct_sumable phi orth_compl.
Proof.
intros x H1 H2.
apply: norm_eq_zero.
unfold norm; simpl; unfold Hnorm; simpl.
rewrite (H2 _ H1).
apply sqrt_0.
Qed.

(* characterization of orthogonal projection onto subspace *)
Lemma charac_ortho_projection_subspace2:
  forall u:E, forall v:E, phi v ->
     (norm (minus u v) = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w))
         <->
     (forall w:E, phi w -> inner v w = inner u w)).
split; intros.
+ assert
     (forall w:E, phi w -> inner (minus u v) (minus w v) <= 0).
  apply charac_ortho_projection_subspace1; intuition.
  pose (w' := plus w v).
  assert (inner (minus u v) w <= 0).
  assert (Hm1 : w = minus w' v).
  unfold minus.
  unfold w'.
  rewrite <- plus_assoc.
  rewrite plus_opp_r.
  rewrite plus_zero_r.
  reflexivity.
  assert (phi w').
  unfold w'.
  destruct phi_compat as ((G1,(z,G2)),M).
  rewrite <- (opp_opp v).
  apply G1; trivial.
  rewrite <- plus_zero_l.
  apply G1.
  apply (M z zero) in G2.
  rewrite scal_zero_l in G2; trivial.
  trivial.
  rewrite Hm1.
  apply H2; trivial.
  pose (w'' := plus (opp w) v).
  assert (inner (minus u v) (opp w) <= 0).
  assert (Hm1 : opp w = minus w'' v).
  unfold minus.
  unfold w''.
  rewrite <- plus_assoc.
  rewrite plus_opp_r.
  rewrite plus_zero_r.
  reflexivity.
  assert (phi w'').
  unfold w''.
  destruct phi_compat as ((G1,(z,G2)),M).
  rewrite plus_comm.
  apply G1; trivial.
  rewrite Hm1.
  apply H2; trivial.
  assert (HF : (inner (minus u v) w) <= 0
            /\ (opp (inner (minus u v) w) <= 0)).
  split. trivial.
  rewrite inner_opp_r in H4. trivial.
  destruct HF as (HF1,HF2).
  assert (inner (minus u v) w = 0).
  apply Rle_antisym. trivial.
  apply Ropp_le_contravar in HF2.
  ring_simplify in HF2.
  assert (opp (opp (inner (minus u v) w))
         = - (opp (inner (minus u v) w))).
  reflexivity.
  rewrite <- H5 in HF2.
  rewrite opp_opp in HF2; trivial.
  symmetry.
  unfold minus in H5.
  rewrite inner_plus_l in H5.
  apply Rplus_opp_r_uniq in H5; symmetry in H5.
  rewrite inner_opp_l in H5.
  apply Ropp_eq_compat in H5; ring_simplify in H5.
  trivial.
+ destruct phi_compat as ((G1,(z,G2)),M).
  assert
      (forall w : E, phi w -> inner (minus u v) (minus w v) <= 0).
  intros w phiw.
  pose (w' := minus w v).
  assert (inner (minus u v) (minus w v)
          = minus (inner u w') (inner v w')).
  unfold w'. unfold minus in *.
  rewrite inner_plus_l.
  rewrite inner_opp_l.
  reflexivity.
  rewrite H1.
  assert (inner u w' = inner v w').
  symmetry. apply H0.
  unfold w'.
  unfold minus.
  apply G1; trivial.
  assert (minus (inner u w') (inner v w') = 0).
  rewrite H2.
  unfold minus.
  rewrite plus_opp_r.
  reflexivity.
  intuition.
  apply charac_ortho_projection_subspace1; trivial.
Qed.

Lemma direct_sum_with_orth_compl: forall x, m_plus phi orth_compl x.
Proof.
intros x. unfold m_plus. unfold orth_compl.
exists x. exists zero. intro. intros.
rewrite Hierarchy.plus_zero_r. reflexivity.
Qed.

Lemma direct_sum_with_orth_compl_decomp: forall u v,
    phi v -> norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)) ->
      orth_compl (minus u v).
Proof.
intros. unfold orth_compl.
assert
     (forall w:E, phi w -> inner v w = inner u w).
apply charac_ortho_projection_subspace2; intuition.
intros.
assert (inner v y = inner u y).
apply H1; trivial.
unfold minus.
rewrite inner_plus_l.
rewrite <- H3.
rewrite <- inner_plus_l.
rewrite plus_opp_r.
rewrite inner_zero_l; reflexivity.
Qed.

Lemma direct_sum_with_orth_compl_charac1: forall u v,
    phi v -> norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)) ->
      (phi u <-> v = u).
split; intros.
+ assert
       (norm (minus u u) =
        Glb_Rbar (fun r : R => exists w : E, phi w
                   /\ r = norm (minus u w))).
  apply charac_ortho_projection_subspace1. trivial.
  trivial.
  assert (minus u u = zero).
  unfold minus. rewrite plus_opp_r. reflexivity.
  rewrite H2. intros. rewrite inner_zero_l. intuition.
  assert (phi_convex : convex phi).
  unfold convex.
  intros u0 v0 t Hu0 Hv0 Th01.
  destruct phi_compat as ((g1,(s,g2)),mod2).
  assert (H3 : scal (1 - t) v0 = opp (scal (opp (1 - t)) v0)).
  rewrite scal_opp_l.
  rewrite opp_opp. reflexivity.
  rewrite H3.
  apply g1.
  apply mod2.
  trivial.
  apply mod2.
  trivial.
  apply (ortho_projection_convex_unique phi phi_convex phi_compl u).
  trivial. trivial. trivial. trivial.
+ rewrite H1 in H; trivial.
Qed.

Lemma direct_sum_with_orth_compl_charac2: forall u v,
    phi v -> norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, phi w /\ r = norm (minus u w)) ->
      (orth_compl u <-> v = zero).
split; intros.
+ unfold orth_compl in H1.
  assert
       (norm (minus u zero) =
        Glb_Rbar (fun r : R => exists w : E, phi w
                   /\ r = norm (minus u w))).
  apply charac_ortho_projection_subspace1.
  destruct phi_compat. trivial.
  assert (zero = scal zero v).
  rewrite scal_zero_l. reflexivity.
  rewrite H2.
  destruct phi_compat.
  destruct H3.
  apply H4; trivial.
  intros.
  apply direct_sum_with_orth_compl_decomp in H0.
  assert
       (forall x : E, phi x -> orth_compl x -> x = zero).
  apply direct_sumable_with_orth_compl. unfold orth_compl in H0.
  assert (inner (minus u zero) (minus w zero) = 0).
  unfold minus. rewrite opp_zero.
  rewrite plus_zero_r. rewrite plus_zero_r. apply H1.
  trivial. unfold minus. rewrite opp_zero.
  rewrite plus_zero_r. rewrite plus_zero_r.
  unfold minus in H4. rewrite opp_zero in H4.
  rewrite plus_zero_r in H4. rewrite plus_zero_r in H4.
  rewrite H4; intuition. trivial.
  assert (phi_convex : convex phi).
  unfold convex.
  intros u0 v0 t Hu0 Hv0 Th01.
  destruct phi_compat as ((g1,(s,g2)),mod2).
  assert (H3 : scal (1 - t) v0 = opp (scal (opp (1 - t)) v0)).
  rewrite scal_opp_l.
  rewrite opp_opp. reflexivity.
  rewrite H3.
  apply g1.
  apply mod2.
  trivial.
  apply mod2.
  trivial.
  apply (ortho_projection_convex_unique phi phi_convex phi_compl u); trivial.
  assert (zero = scal zero v).
  rewrite scal_zero_l. reflexivity. destruct phi_compat.
  rewrite H3. apply H5; trivial.
+ assert (minus u v = u).
  rewrite H1. unfold minus. rewrite opp_zero.
  rewrite plus_zero_r. reflexivity.
  rewrite <- H2.
  apply direct_sum_with_orth_compl_decomp; trivial.
Qed.

End ortho_compl.
