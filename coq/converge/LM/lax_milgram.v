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

Require Import hilbert.
Require Export continuous_linear_map.
Require Export Decidable.
Require Export FunctionalExtensionality.
Require Export mathcomp.ssreflect.ssreflect.
Require Export Coquelicot.Hierarchy.
Require Export Reals.
Require Export logic_tricks.
Require Export ProofIrrelevanceFacts.
Require Export Reals Coquelicot.Coquelicot.
Require Export LM.R_compl.
Require Export logic_tricks.
Require Export compatible.

Section ker_generic.

Context {E : Hilbert}.
Context {F : NormedModule R_AbsRing}.

(**  Kernel of an application *)

Definition ker (f : E -> F) := fun x:E => f x = zero.

Lemma compatible_m_ker : forall (f : E -> F), is_linear_mapping f ->
                  compatible_m (ker f).
Proof.
intros.
unfold compatible_m; unfold compatible_g.
split; intros.
split; intros.
unfold ker in *.
unfold is_linear_mapping in H.
intuition. rewrite H2. rewrite H0.
rewrite <- scal_opp_one. rewrite H3.
rewrite H1. rewrite scal_zero_r.
rewrite plus_zero_r; reflexivity.
exists zero. unfold ker.
apply: is_linear_mapping_zero; trivial.
unfold is_linear_mapping in H.
unfold ker. destruct H. rewrite H1.
unfold ker in H0. rewrite H0.
rewrite scal_zero_r; reflexivity.
Qed.

Lemma clm_ker_convex : forall (f : E->F), is_linear_mapping f ->
                 convex (ker f).
Proof.
intros f H x y t Hx Hy Ht.
unfold ker in *.
destruct H as (G1,G2).
rewrite G1.
repeat (rewrite G2).
rewrite Hx; rewrite Hy.
repeat (rewrite scal_zero_r).
rewrite plus_zero_l.
reflexivity.
Qed.

End ker_generic.

(** Kernel of an application in the topo dual *)

Section ker_dual.

Context {E : Hilbert}.

Lemma ker_nnker_equiv : forall (f : topo_dual E) x,
                        (ker (m f) x) <-> ~~(ker (m f) x).
Proof.
intros f x.
apply (logic_dec_notnot E (ker f) x).
apply Req_dec.
Qed.

Lemma clm_ker_closed : forall (f : topo_dual E),
                  closed (ker f).
Proof.
intros f x Hx.
unfold ker in *.
cut (continuous f x).
unfold continuous, filterlim, filter_le, filtermap.
intros H; specialize H with (P:=fun y => y <> 0).
case (Req_dec (f x) 0); try easy; intros H1.
assert (K: 0 < Rabs (f x)).
apply Rabs_pos_lt.
trivial.
exfalso.
apply Hx.
apply H.
exists (pos_div_2 (mkposreal _ K)).
simpl; unfold ball; simpl.
unfold AbsRing_ball; simpl.
unfold abs; simpl.
intros y Hy.
destruct (Req_dec y 0).
rewrite H0 in Hy.
unfold minus in *.
rewrite plus_zero_l in Hy.
rewrite Rabs_Ropp in Hy.
assert (Rabs (f x) / 2 < Rabs (f x)).
apply Rmult_lt_reg_l with 2.
intuition.
assert (H1':2 * (Rabs (f x) / 2) = (Rabs (f x))).
field.
rewrite H1'.
replace (Rabs (f x)) with (1*(Rabs (f x))) at 1.
apply Rmult_lt_compat_r; intuition.
ring_simplify; reflexivity.
exfalso.
apply Rlt_not_le in Hy.
apply Hy.
intuition.
trivial.
apply continuous_linear_map_3_2.
apply continuous_linear_map_4_3.
apply continuous_linear_map_5_4.
apply f.
apply continuous_linear_map_6_5.
apply f.
apply Cf.
Qed.

Lemma clm_ker_my_complete : forall (f : topo_dual E),
                  my_complete (ker f).
Proof.
intros f.
apply closed_my_complete.
apply clm_ker_closed.
Qed.

Lemma compatible_m_nnker : forall (f : topo_dual E),
                  compatible_m  (ker f).
Proof.
intros.
unfold compatible_m; unfold compatible_g.
assert (is_linear_mapping f).
apply Lf.
intros.
split; intros.
split; intros.
apply compatible_m_ker; try easy.
exists zero.
apply: is_linear_mapping_zero; trivial.
apply compatible_m_ker; try assumption.
Qed.

Lemma clm_ker_complete : forall (f : topo_dual E),
                  complete_subset (ker f).
Proof.
intros f.
generalize (closed_my_complete (ker f) (clm_ker_closed f)).
intros H.
unfold my_complete in H.
exists fixed_point.lim.
intros F HF1 HF2 HF3.
split.
apply H; try assumption.
apply: complete_cauchy; easy.
Qed.

Lemma clm_ker_convex2 : forall (f : topo_dual E),
                 convex (ker f).
Proof.
intros f x y t Hx Hy Ht.
apply clm_ker_convex; trivial.
apply f.
Qed.

End ker_dual.

(** * RIESZ-FRECHET *)

Section Riesz_Frechet.

Context {E : Hilbert}.

Variable phi : E -> Prop.

Hypothesis phi_C : my_complete phi.

Hypothesis m_C : compatible_m phi.

Definition f_phi_neq_zero (f : topo_dual E) :=
                     (exists u0, phi u0 /\ f u0 <> 0).

(** Riesz-Frechet theorem *)

Theorem Riesz_Frechet'_zero_phi : forall (f:topo_dual E),
   ~f_phi_neq_zero f ->  exists (u:E), phi u /\ forall (v:E),
     phi v -> f v = inner u v.
Proof.
intros f H.
exists zero.
split.
destruct m_C as ((CG1,(z,CG2)),CS).
unfold compatible_m in m_C.
assert (C0 := CS z 0%R CG2).
now rewrite scal_zero_l in C0.
intros v Hv.
rewrite inner_zero_l.
destruct (Req_dec (f v) 0).
trivial.
exfalso.
apply H.
exists v.
split; trivial.
Qed.

Lemma compatible_m_and : forall (phi phi' : E -> Prop), compatible_m phi ->
          compatible_m phi' -> compatible_m (fun x : E => phi x /\ phi' x).
Proof.
intros phi0 phi0' C C'.
unfold compatible_m.
split.
unfold compatible_g.
split.
intros x y H H0.
destruct H as (H1,H2).
destruct H0 as (H01,H02).
destruct C as (C1,C2).
destruct C1 as (C1,C11).
destruct C' as (C1',C2').
destruct C1' as (C1',C11').
split.
apply C1; trivial.
apply C1'; trivial.
exists zero.
split.
apply compatible_m_zero.
apply C.
apply compatible_m_zero.
apply C'.
intros x l.
split.
destruct C as (_,C).
apply C.
exact (proj1 H).
destruct C' as (_,C').
apply C'.
exact (proj2 H).
Qed.

Lemma closed_and : forall (phi phi' : E -> Prop), my_complete phi ->
    my_complete phi' -> my_complete (fun x : E => phi x /\ phi' x).
Proof.
intros phi0 phi0' C C' F HPf Hcf H.
split.
unfold my_complete in C, C'.
apply C; try assumption.
intros P HFP.
intro.
specialize (H P HFP).
apply H.
intro.
apply H0.
destruct H1 as (x,(H1,(H2,_))).
exists x; try intuition.
apply C'; try assumption.
intros P HFP.
intro.
specialize (H P HFP).
apply H.
intro.
apply H0.
destruct H1 as (x,(H1,(_,H2))).
exists x; try intuition.
Qed.

Lemma Riesz_Frechet'_nzero_phi : forall (f:topo_dual E),
   (forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
   f_phi_neq_zero f ->  exists (u:E), phi u /\ forall (v:E),
     phi v -> f v = inner u v.
Proof.
intros f HD2 H.
destruct H as (u0,H).
pose (PHI := fun w : E => ker f w /\ phi w).
assert (forall u v,
    PHI v -> norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, PHI w /\ r = norm (minus u w)) ->
      (PHI u <-> v = u)).
apply: direct_sum_with_orth_compl_charac1.
apply compatible_m_and.
apply compatible_m_ker.
apply f.
trivial.
unfold complete_subset.
exists (fixed_point.lim).
intros F K K0 K1.
split.
assert (PHI_C : my_complete PHI).
apply closed_and.
(*apply closed_my_complete.*)
apply clm_ker_my_complete.
apply phi_C; try assumption.
apply PHI_C; try assumption.
apply: complete_cauchy; easy.
assert (forall u, exists! v:E,
       PHI v /\ norm (minus u v)
       = Glb_Rbar (fun r => exists w:E, PHI w
        /\ r = norm (minus u w))).
intros u; apply: ortho_projection_convex.
exists zero.
split.
(*apply ker_nnker_equiv.*)
apply: compatible_m_zero.
apply compatible_m_ker, f.
destruct m_C as ((CG1,(z,CG2)),CS).
specialize (CS z 0%R CG2).
now rewrite scal_zero_l in CS.
split.
assert (compatible_m (fun x : E => ker f x)).
apply compatible_m_ker, f.
destruct H4 as ((G1,G2),G3).
replace (scal (1 - theta) v)
        with (opp (opp (scal (1 - theta) v))).
apply G1.
apply G3.
apply H1.
rewrite <- scal_opp_one.
apply G3.
apply G3.
apply H2.
now rewrite opp_opp.
destruct m_C as ((G1,G2),G3).
replace (scal (1 - theta) v)
        with (opp (opp (scal (1 - theta) v))).
apply G1.
apply G3.
apply H1.
rewrite <- scal_opp_one.
apply G3.
apply G3.
apply H2.
now rewrite opp_opp.
unfold complete_subset.
exists (fixed_point.lim).
intros F K K0 K1.
split.
assert (PHI_C : my_complete PHI).
apply closed_and.
(*apply closed_my_complete.*)
apply clm_ker_my_complete.
apply phi_C; try assumption.
apply PHI_C; try assumption.
apply: complete_cauchy; easy.
apply HD2.
destruct (H1 u0).
assert (~(x = u0)).
rewrite <- H0.
intro hF.
unfold PHI in hF.
destruct hF as (hF1,hF2).
(*rewrite <- ker_nnker_equiv in hF1.*)
unfold ker in hF1.
intuition.
apply H2.
apply H2.
pose (v0 := minus u0 x).
assert (v0 <> zero).
unfold v0. intro.
absurd (x = u0).
trivial.
apply plus_reg_r with (opp x).
unfold minus in H4.
rewrite plus_opp_r.
symmetry; trivial.
pose (e0 := scal (/ (norm v0)) v0).
pose (u := scal (f e0) e0).
exists u.
split.
unfold u.
destruct m_C as ((P1,P2),P3).
apply P3.
unfold e0.
apply P3.
unfold v0.
unfold minus.
apply P1.
intuition.
apply H2.
intros v Hv.
assert (e0 <> zero).
assert (f e0  <> zero).
unfold e0.
assert (Lin : (is_linear_mapping f)).
apply Lf.
destruct Lin as (Lin1,Lin2).
rewrite Lin2.
unfold scal.
simpl.
apply Rmult_integral_contrapositive.
split.
apply Rinv_neq_0_compat.
intro.
apply NormedModule.ax5 in H5.
intuition.
unfold v0. unfold minus.
rewrite Lin1.
assert (f (opp x) = 0).
assert (opp x = scal (opp one) x).
rewrite scal_opp_one.
reflexivity.
rewrite H5.
rewrite Lin2.
assert (ker f x).
apply H2.
(*rewrite <- ker_nnker_equiv in H6.*)
unfold ker in H6.
rewrite H6.
rewrite scal_zero_r.
reflexivity.
rewrite H5.
rewrite plus_zero_r.
intuition.
trivial.
intro. rewrite H6 in H5.
rewrite is_linear_mapping_zero in H5.
intuition.
apply Lf.
assert (norm e0 = 1).
unfold e0.
rewrite norm_scal_R.
assert (abs (/norm v0) = /norm v0).
assert (forall x : R, (0 <= x) -> abs(x) = x).
intros.
unfold abs.
simpl.
apply Rabs_pos_eq.
trivial.
apply H6.
assert (0 < / norm v0).
apply Rinv_0_lt_compat.
apply norm_gt_0.
intuition.
intuition.
rewrite H6.
field. intro.
apply NormedModule.ax5 in H7.
intuition.
pose (lambda := (f v) / (f e0)).
pose (w := minus v (scal lambda e0)).
assert (f w = 0).
unfold w. unfold lambda. unfold minus.
assert (is_linear_mapping f).
apply Lf.
destruct H7.
rewrite H7.
assert (f (opp (scal (f v / f e0) e0))
        = opp ((scal (f v / f e0) (f e0)))).
rewrite <- scal_opp_one.
rewrite H8.
symmetry.
rewrite H8. rewrite scal_opp_one.
rewrite <- H8. rewrite <- H8. unfold e0.
reflexivity.
rewrite H9. unfold scal. simpl.
assert (mult (f v / f e0) (f e0) = f v).
assert ((f v / f e0) = mult (f v) (/f e0)).
intuition. rewrite H10.
rewrite <- mult_assoc.
change ((mult (/ f e0) (f e0)))
        with ((/ f e0)*(f e0)).
rewrite Rinv_l. rewrite mult_one_r. reflexivity.
unfold e0.
assert (Lin : (is_linear_mapping f)).
apply Lf. destruct Lin as (Lin1,Lin2).
rewrite Lin2. unfold scal; simpl.
apply Rmult_integral_contrapositive.
split. assert (0 < / norm v0).
apply Rinv_0_lt_compat.
apply norm_gt_0.
intuition.
intro. apply Rlt_not_le in H11.
apply H11.
intuition.
unfold v0. unfold minus.
rewrite Lin1.
assert (f (opp x) = 0).
assert (opp x = scal (opp one) x).
rewrite scal_opp_one.
reflexivity.
rewrite H11.
rewrite Lin2.
assert (ker f x).
apply H2.
(*rewrite <- ker_nnker_equiv in H12.*)
unfold ker in H12.
rewrite H12.
rewrite scal_zero_r.
reflexivity.
rewrite H11.
rewrite plus_zero_r.
intuition.
rewrite H10.
rewrite plus_opp_r.
reflexivity.
assert (orth_compl (fun x => PHI x) v0).
unfold v0.
apply: direct_sum_with_orth_compl_decomp.
apply compatible_m_and.
apply compatible_m_ker, f.
trivial.
apply H2.
apply H2.
assert (orth_compl (fun x => PHI x) e0).
unfold e0.
assert (compatible_m
                (orth_compl (fun x0 : E => PHI x0))).
apply orth_compl_compat.
destruct H9 as ((G1,(a,G2)),G3).
apply G3; trivial.
assert (orth_compl (fun x => PHI x) u).
unfold u.
assert (compatible_m
                (orth_compl (fun x0 : E => PHI x0))).
apply orth_compl_compat.
destruct H10 as ((G1,(a,G2)),G3).
apply G3; trivial.
assert (inner u w = 0).
unfold orth_compl in H10.
apply H10.
split.
(*apply ker_nnker_equiv.*)
trivial.
unfold w.
destruct m_C as ((P1,P2),P3).
unfold minus.
apply P1.
trivial.
apply P3.
unfold e0.
apply P3.
unfold v0.
unfold minus.
apply P1.
intuition.
apply H2.
assert (inner u w = minus (inner u v) (f v)).
assert (minus (inner u v) (f v)
        = minus (inner u v) (scal lambda (inner u e0))).
unfold lambda. unfold u at 3.
rewrite (inner_scal_l e0 e0 (f e0)).
unfold scal. simpl.
rewrite mult_assoc.
assert (inner e0 e0 = 1).
rewrite <- squared_norm.
unfold norm in H6. simpl in H6.
rewrite H6.
ring_simplify; reflexivity.
rewrite H12.
rewrite mult_one_r.
assert ((f v / f e0) = mult (f v) (/ f e0)).
reflexivity.
rewrite H13.
rewrite <- mult_assoc.
rewrite <- Rinv_l_sym.
rewrite mult_one_r.
reflexivity.
assert (f e0  <> zero).
unfold e0.
assert (Lin : (is_linear_mapping f)).
apply Lf.
destruct Lin as (Lin1,Lin2).
rewrite Lin2.
unfold scal.
simpl.
apply Rmult_integral_contrapositive.
split.
apply Rinv_neq_0_compat.
intro.
apply NormedModule.ax5 in H14.
intuition.
unfold v0. unfold minus.
rewrite Lin1.
assert (f (opp x) = 0).
assert (opp x = scal (opp one) x).
rewrite scal_opp_one.
reflexivity.
rewrite H14.
rewrite Lin2.
assert (ker f x).
apply H2.
(*rewrite <- ker_nnker_equiv in H15.*)
unfold ker in H15.
rewrite H15.
rewrite scal_zero_r.
reflexivity.
rewrite H14.
rewrite plus_zero_r.
intuition.
apply H14.
rewrite H12.
unfold w.
unfold minus.
rewrite inner_plus_r.
rewrite <- inner_scal_r.
rewrite <- inner_opp_r.
reflexivity.
rewrite H11 in H12.
apply plus_reg_r with (opp (f v)).
rewrite plus_opp_r.
unfold minus in H12.
trivial.
Qed.

Theorem Riesz_Frechet_uniqueness_phi: forall (f:topo_dual E),
    forall u u',
     ((phi u) /\ forall (v:E),  phi v -> f v = inner u v) ->
     ((phi u') /\  forall (v:E), phi v -> f v = inner u' v) -> u = u'.
Proof.
intros f u u' H H0.
assert (forall v : E, phi v -> inner u v = inner u' v).
intros.
transitivity (f v).
symmetry.
apply H.
trivial.
apply H0.
trivial.
assert (forall v : E, phi v -> inner (minus u u') v = 0).
intros. unfold minus.
rewrite inner_plus_l. rewrite inner_opp_l.
ring_simplify. rewrite H1. ring_simplify; reflexivity.
trivial.
apply trivial_orth_compl' in H2.
unfold minus in H2. apply plus_reg_r with (opp u').
rewrite plus_opp_r. trivial.
now apply: my_complete_closed.
unfold minus; apply m_C; intuition.
Qed.

Theorem Riesz_Frechet_zero_phi : forall (f:topo_dual E),
      (~ f_phi_neq_zero f) -> exists! (u:E), phi u /\ (forall (v:E),
      phi v -> f v = inner u v).
Proof.
intros f H.
apply unique_existence1; split.
apply Riesz_Frechet'_zero_phi.
trivial.
unfold uniqueness.
apply Riesz_Frechet_uniqueness_phi.
Qed.

Theorem Riesz_Frechet_nzero_phi : forall (f:topo_dual E),
       (forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
      f_phi_neq_zero f -> exists! (u:E), phi u /\ (forall (v:E),
      phi v -> f v = inner u v).
Proof.
intros f HD2 H.
apply unique_existence1; split.
apply Riesz_Frechet'_nzero_phi.
trivial.
trivial.
trivial.
unfold uniqueness.
apply Riesz_Frechet_uniqueness_phi.
Qed.

Theorem Riesz_Frechet_strong_phi : forall (f:topo_dual E),
    (forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
    (decidable (f_phi_neq_zero f)) ->  exists! (u:E), phi u /\ (forall (v:E),
    phi v -> f v = inner u v).
Proof.
intros f J Hor.
destruct Hor.
now apply Riesz_Frechet_nzero_phi.
now apply Riesz_Frechet_zero_phi.
Qed.

(** Riesz representation function *)

Context {F : Hilbert}.

Definition tau := fun (f:topo_dual E) =>
  (iota (fun u : E => phi u /\ forall v : E, phi v -> f v = inner u v)).

Lemma iota_elim : forall (P : E->Prop) (v : E),
     (unique (fun x : E => P x) v) ->  iota P = v.
Proof.
intros P v Hu.
assert (exists! v, P v).
exists v.
trivial.
apply iota_correct in H.
assert (P v).
apply Hu.
unfold unique in Hu.
destruct Hu as (_,Hu).
symmetry.
apply Hu.
trivial.
Qed.

Lemma iota_elimE (H : (CompleteNormedModule R_AbsRing)) : forall (P : H->Prop) (v : H),
     (unique (fun x : H => P x) v) ->  iota P = v.
Proof.
intros P v Hu.
assert (H' : exists! v, P v).
exists v.
trivial.
apply iota_correct in H'.
assert (P v).
apply Hu.
unfold unique in Hu.
destruct Hu as (_,Hu).
symmetry.
apply Hu.
trivial.
Qed.

Lemma phi_tau :
    forall (f : topo_dual E),
     (forall u, forall eps:posreal,
        decidable (exists w:E, ((ker f w /\ phi w) /\ norm (minus u w) < eps))) ->
    (decidable (f_phi_neq_zero f)) -> phi (tau f).
Proof.
intros f Hd Hd'.
unfold tau.
assert (H : exists! (w:E), phi w /\ forall (v:E),
      phi v -> f v = inner w v).
apply Riesz_Frechet_strong_phi; trivial.
destruct H as (w,H).
generalize H.
intros H'.
apply (iota_elim _ _) in H.
rewrite H.
apply H'.
Qed.

Theorem Riesz_Frechet_moreover1_zero_phi :
   forall (f:topo_dual E),
       (~ f_phi_neq_zero f) -> operator_norm_phi phi f
                                   = norm (tau f).
Proof.
intros f H.
simpl.
assert (exists! (u:E), phi u /\ forall (v:E), phi v ->
      f v = inner u v).
apply Riesz_Frechet_zero_phi.
intro Hf.
destruct Hf as (vf,Hf).
apply H.
exists vf; trivial.
destruct H0 as (u,H0).
apply (iota_elim _ _ ) in H0.
unfold tau.
rewrite H0.
assert (forall v, phi v -> f v = 0).
intros v HV.
destruct (Req_dec (f v) 0).
trivial.
exfalso.
apply H.
exists v.
split; trivial.
assert (u = zero).
rewrite <- H0.
assert (exists! (u:E), phi u /\ forall (v:E),
      phi v -> f v = inner u v).
apply Riesz_Frechet_zero_phi.
intro Hf.
destruct Hf as (vf,Hf).
apply H.
exists vf; trivial.
destruct H2 as (u2,H2).
assert (forall v, phi v -> inner u2 v = zero).
intros v0 Hv0.
assert (f v0 = inner u2 v0).
apply H2.
trivial.
rewrite <- H3.
unfold f_phi_neq_zero in H.
destruct (is_zero_dec (f v0)).
trivial.
exfalso.
apply H.
exists v0; split; trivial.
generalize H2; intro H2'.
apply (iota_elim _ _ ) in H2.
rewrite H2.
specialize (H3 u2).
apply PreHilbert.ax3 in H3.
trivial.
apply H2'.
rewrite H2.
rewrite norm_zero.
assert (forall u, u <> zero -> phi u -> norm (f u) <= 0 * norm u).
intros u0 H3 H3'.
unfold f_phi_neq_zero.
rewrite H1.
rewrite norm_zero.
ring_simplify; intuition.
trivial.
apply (operator_norm_helper3'_phi phi) in H3.
assert (Rbar_le 0 (operator_norm_phi phi f)).
apply operator_norm_ge_0_phi.
try assumption.
apply Rbar_le_antisym.
assert (is_finite (operator_norm_phi phi f)).
apply operator_norm_helper3_phi with 0.
try assumption.
apply Rle_refl.
intros u0 Hu0 Hu0'.
rewrite H1.
rewrite norm_zero.
ring_simplify; intuition.
trivial.
unfold Rbar_le.
rewrite <- H5.
trivial.
trivial.
try assumption.
now apply Rle_refl.
Qed.

Theorem Riesz_Frechet_moreover1_nzero_phi :
   forall (f:topo_dual E),
    (forall u, forall eps:posreal, decidable (exists w:E, ((ker f w
                                                          /\ (phi w))
                                                          /\ norm (minus u w) < eps))) ->
        (f_phi_neq_zero f) -> operator_norm_phi phi f = norm (tau f).
Proof.
intros f K H.
simpl.
assert (exists! (u:E), phi u /\forall (v:E), phi v ->
      f v = inner u v).
apply Riesz_Frechet_nzero_phi; trivial.
destruct H as (v,H).
destruct H0 as (u,H0).
assert (exists! (u:E), phi u /\ forall (v:E), phi v ->
      f v = inner u v).
apply Riesz_Frechet_nzero_phi; trivial.
exists v.
trivial.
destruct H1 as (u1,H1).
assert (Heq : u = u1).
unfold unique in H1.
destruct H1 as (H11,H12).
symmetry.
apply H12.
apply H0.
apply (iota_elim _ _ ) in H0.
unfold tau.
rewrite H0.
assert (u <> zero).
rewrite Heq.
destruct H1 as (H11,H12).
assert (f v = inner u1 v).
apply H11.
exact (proj1 H).
intro.
absurd (f v = zero).
trivial.
rewrite H2 in H1.
rewrite inner_zero_l in H1.
trivial.
assert (norm u <> 0).
intro.
apply norm_eq_zero in H3.
intuition.
exfalso; intuition.
rewrite H2 in H1.
rewrite inner_zero_l in H1.
trivial.
assert (Haf : (norm(f u))/(norm u)=norm u).
assert (f u = inner u u).
rewrite <- Heq in H1.
apply H1.
apply H1.
rewrite H3.
rewrite <- squared_norm.
assert (norm (Hnorm u * Hnorm u) = norm u * norm u).
assert (HnN : Hnorm u = norm u).
reflexivity.
rewrite HnN.
assert (Hnorm : forall x, 0 <= x -> norm(x) = x).
intros x Posx.
unfold norm.
simpl.
unfold abs.
simpl.
unfold Rabs.
destruct (Rcase_abs x).
absurd (0 <= x); trivial.
apply Rlt_not_le in r.
trivial.
trivial.
apply Hnorm.
apply Rle_0_sqr.
rewrite H4.
field.
destruct (Req_dec (norm u) 0).
apply norm_eq_zero in H5.
exfalso; intuition.
trivial.
assert (HG : Rbar_le (norm u) (operator_norm_phi phi f)).
rewrite <- Haf.
unfold operator_norm_phi.
destruct (Is_only_zero_set_dec_phi E).
unfold Lub_Rbar.
destruct (ex_lub_Rbar
 (fun x : R => exists u0 : Hilbert_NormedModule E,
 u0 <> zero /\ phi u0 /\ x = norm (f u0) / norm u0)).
simpl. destruct x.
unfold is_lub_Rbar in i.
unfold is_ub_Rbar in i.
destruct i.
apply H3.
exists u; intuition.
rewrite <- Heq in H1.
apply H1.
trivial.
trivial.
destruct i.
unfold is_ub_Rbar in H3.
simpl in H3.
apply H3 with (norm (f u) / norm u).
exists u.
rewrite <- Heq in H1.
split; try assumption.
split; try reflexivity.
apply H1.
apply (Is_only_zero_set_correct1_phi E phi) with u in i.
absurd (norm u = 0).
exfalso; intuition.
rewrite i.
rewrite norm_zero.
reflexivity.
rewrite <- Heq in H1.
apply H1.
assert (HD : Rbar_le (operator_norm_phi phi f) (norm u)).
destruct (operator_norm_helper2'_phi phi f).
destruct f.
apply op_norm_finite_phi; try assumption.
destruct H3 as (HZ,Hof).
rewrite Hof.
apply norm_ge_0.
destruct H3 as (HZ,Hof).
assert (Hfin : is_finite (operator_norm_phi phi f)).
destruct f; trivial.
apply op_norm_finite_phi; try assumption.
destruct (operator_norm_phi phi f).
apply Hof.
apply norm_ge_0.
intros u0 Hu0 Hp0.
assert (HU0 : (Rabs (f u0) / (norm u0)) <= norm u).
assert (HU02 : f u0 = inner u u0).
rewrite <- Heq in H1.
apply H1.
trivial.
rewrite HU02.
assert (HU03 : Rabs (inner u u0) <= norm u *  norm u0).
apply Cauchy_Schwartz_with_norm.
apply Rmult_le_reg_r with (norm u0).
assert (Hvnz : u0 <> zero).
intro.
absurd (u0 <> zero).
intuition.
trivial.
apply norm_gt_0.
trivial.
field_simplify.
assert (forall x, x / 1 = x).
intro x.
field.
repeat (rewrite H4).
rewrite Rmult_comm.
field_simplify in HU03.
trivial.
assert (Hvnz : u0 <> zero).
trivial.
apply Rgt_not_eq.
apply Rlt_gt.
apply norm_gt_0.
trivial.
assert (RaN : Rabs (f u0) = norm (f u0)).
unfold norm; simpl.
reflexivity.
rewrite RaN in HU0.
apply (Rmult_le_compat_r (norm u0)
                         (norm (f u0) / norm u0)
                         (norm u)) in HU0.
field_simplify in HU0.
assert (Hx1 : forall x, x / 1 = x).
intro x; field.
repeat (rewrite Hx1 in HU0).
rewrite Rmult_comm.
trivial.
absurd (norm u0 = 0).
apply Rgt_not_eq.
apply Rlt_gt.
apply norm_gt_0.
trivial.
trivial.
apply norm_ge_0.
simpl.
apply is_finite_correct in Hfin.
destruct Hfin as (y,Hy).
absurd (Rbar_lt (Finite y) p_infty).
apply Rbar_le_not_lt.
rewrite Hy.
apply Rbar_le_refl.
intuition.
apply is_finite_correct in Hfin.
destruct Hfin as (y,Hy).
absurd (Rbar_lt m_infty (Finite y)).
apply Rbar_le_not_lt.
rewrite Hy.
apply Rbar_le_refl.
simpl.
trivial.
apply Rbar_le_antisym; trivial.
Qed.

Theorem Riesz_Frechet_moreover1_phi:
   forall (f:topo_dual E),
     (decidable (f_phi_neq_zero f)) ->
      (forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
         operator_norm_phi phi f = norm (tau f).
Proof.
intros f Hd Hd0.
destruct Hd.
apply Riesz_Frechet_moreover1_nzero_phi; trivial.
apply Riesz_Frechet_moreover1_zero_phi; trivial.
Qed.

Theorem Riesz_Frechet_moreover2_phi :
    (forall f:topo_dual E,
     decidable (f_phi_neq_zero f)) ->
  (forall (f:topo_dual E), forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
     is_linear_mapping tau.
Proof.
intros H HhH; split.
intros x y.
apply Riesz_Frechet_uniqueness_phi with (plus x y).
apply (iota_correct (fun u : E => phi u /\ forall v0 : E, phi v0 ->
                                  (plus x y) v0 = inner u v0)).
apply Riesz_Frechet_strong_phi.
apply HhH.
trivial.
split.
destruct m_C as ((P1,P2),P3).
replace (tau y) with (opp (opp (tau y))).
apply P1.
apply phi_tau.
trivial.
trivial.
trivial.
replace (opp (tau y)) with (scal (opp one) (tau y)).
apply P3.
apply phi_tau.
trivial. trivial. trivial.
rewrite scal_opp_one.
reflexivity.
rewrite opp_opp.
reflexivity.
intros v Hv.
rewrite inner_plus_l.
apply trans_eq with (x v + y v).
reflexivity.
f_equal.
apply (iota_correct (fun u : E => phi u /\ forall v0 : E,
                              phi v0 -> x v0 = inner u v0)).
apply Riesz_Frechet_strong_phi; trivial.
trivial.
apply (iota_correct (fun u : E => phi u /\ forall v0 : E,
                              phi v0 -> y v0 = inner u v0)).
apply Riesz_Frechet_strong_phi.
trivial.
trivial.
trivial.
intros x l.
apply Riesz_Frechet_uniqueness_phi with (scal l x).
apply (iota_correct (fun u : E => phi u /\ forall v0 : E,
                     phi v0 -> (scal l x) v0 = inner u v0)).
apply Riesz_Frechet_strong_phi.
trivial.
trivial.
split.
destruct m_C as ((P1,P2),P3).
apply P3.
apply phi_tau.
trivial. trivial. trivial.
intros v Hv.
rewrite inner_scal_l.
apply trans_eq with (l*x v).
reflexivity.
f_equal.
apply (iota_correct (fun u : E => phi u /\ forall v0 : E,
                         phi v0 -> x v0 = inner u v0)).
apply Riesz_Frechet_strong_phi.
trivial.
trivial.
trivial.
Qed.

End Riesz_Frechet.

(** * LAX-MILGRAM *)

Section LM_aux.

Context {E : Hilbert}.

Variable a : E -> E -> R.
Variable M : R.
Variable alpha : R.
Variable phi : E -> Prop.

Hypothesis phi_C : my_complete phi.
Hypothesis phi_m : compatible_m phi.
Hypothesis Hba : is_bounded_bilinear_mapping a M.
Hypothesis Hca : is_coercive a alpha.

Definition is_sol_linear_pb_phi (f:E -> R) (u:E):=
    phi u /\ forall v:E, phi v -> a u v = f v.

Definition Tau := fun (f:topo_dual E) =>
  (iota (fun u : E => phi u /\ forall v : E, phi v -> f v = inner u v)).

Lemma phi_Tau : forall (f : topo_dual E),
    (forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
    (decidable (f_phi_neq_zero phi f)) -> phi (Tau f).
Proof.
intros f HdH Hd.
unfold Tau.
assert (H : exists! (w:E), phi w /\ forall (v:E),
      phi v -> f v = inner w v).
apply Riesz_Frechet_strong_phi; trivial.
destruct H as (w,H).
generalize H.
intros H'.
apply (iota_elim _ _) in H.
rewrite H.
apply H'.
Qed.

(** Calculations *)

Variable A : (clm E (topo_dual E)).
Hypothesis A_bil : unique (fun A : (clm E (topo_dual E)) =>
                                    forall (u v:E), a u v = (A u) v) A.
Hypothesis A_dec : forall (u0 : E), decidable (exists u : E, phi u /\ A u0 u <> 0).
Hypothesis A_dec2 : forall (u0 : E), decidable (exists u : E, A u0 u <> 0).

Lemma comp_lm_aux_phi : forall (C : R),
     (0 < alpha <= C) -> (forall (rho : R), 0 < rho < (2*alpha)/(C*C)
     -> 0 <= ((1 - (2*rho*alpha)) + rho*rho*C*C)).
Proof.
intros C Halpha rho Hrho.
assert (HR : (-(alpha*alpha)/(C*C)) + ((Rsqr ((rho*C) - (alpha/C))) + 1)
       =
        1 - 2 * rho * alpha + rho * rho * C * C).
rewrite Rsqr_minus.
assert (Hra :  2 * (rho * C) * (alpha / C) = 2*rho*alpha).
rewrite Rmult_assoc.
assert (Hra2 : (Rmult (Rmult rho C) (Rdiv alpha C))
               =
               (Rmult rho (Rmult C (Rdiv alpha C)))).
ring.
rewrite Hra2.
assert (Hra3 : Rdiv alpha C = Rmult alpha (Rinv C)).
field.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
rewrite Hra3.
assert (Hra4 : (C * (alpha * / C)) = alpha).
field.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
trivial.
rewrite Hra4.
rewrite Rmult_assoc.
reflexivity.
rewrite Hra.
ring_simplify.
assert (Hp : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r).
intros r r1 r2 Heq.
rewrite Heq; reflexivity.
apply Hp.
rewrite Rsqr_mult.
assert (Hqd : (alpha * alpha) / (C * C)
       = (alpha / C)²).
rewrite Rsqr_div.
reflexivity.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
rewrite <- Hqd.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
assert (Aa : alpha * alpha / (C * C)
      + - (alpha * alpha) / (C * C) = 0).
field.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
rewrite Aa.
ring_simplify.
assert (Hpowr : Rsqr rho = pow rho (S (S O))).
unfold Rsqr.
ring_simplify.
reflexivity.
assert (Hpowc : Rsqr C = pow C (S (S O))).
unfold Rsqr.
ring_simplify.
reflexivity.
rewrite Hpowr.
rewrite Hpowc.
reflexivity.
rewrite <- HR.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
apply Rplus_le_le_0_compat.
assert (H2 : (alpha * alpha) / (C * C) <= 1).
apply Rmult_le_reg_r with (C*C).
apply Rlt_0_sqr.
trivial.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
field_simplify; trivial.
assert (Hd1 : forall x, x / 1 = x).
intros x.
field.
repeat (rewrite Hd1).
assert (Hpowc : Rsqr C = pow C (S (S O))).
unfold Rsqr.
ring_simplify.
reflexivity.
assert (Hpowa : Rsqr alpha = pow alpha (S (S O))).
unfold Rsqr.
ring_simplify.
reflexivity.
rewrite <- Hpowc. rewrite <- Hpowa.
apply Rsqr_le_abs_1.
unfold Rabs.
destruct (Rcase_abs alpha).
absurd (0 < alpha); trivial.
apply Rle_not_lt.
intuition.
trivial.
apply Halpha.
destruct (Rcase_abs C).
absurd (0 < C); trivial.
apply Rle_not_lt.
intuition.
trivial.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
apply Halpha.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
apply Rplus_le_reg_r with (alpha * alpha / (C * C)).
ring_simplify.
rewrite Ropp_div.
ring_simplify.
trivial.
apply Rle_0_sqr.
Qed.

Lemma comp_lax_milgram_phi : forall (C : R),
     (0 < alpha <= C) -> (forall (rho : R), 0 < rho < (2*alpha)/(C*C)
     -> 0 <= (sqrt ((1 - (2*rho*alpha)) + rho*rho*C*C)) < 1).
Proof.
intros C Halpha rho Hrho.
assert (Hc : C <> 0).
replace C with (0 + C).
apply tech_Rplus.
intuition.
apply Rlt_le_trans with alpha.
apply Halpha.
apply Halpha.
ring.
split.
apply sqrt_pos.
assert ((rho*rho*C*C < (2*rho*alpha))).
rewrite (Rmult_comm 2 rho).
rewrite (Rmult_assoc (Rmult rho rho) C).
assert (H : (Rmult (Rmult rho rho) (Rmult C C))
       = Rmult rho (Rmult rho (Rmult C C))).
ring.
rewrite H.
assert (H0 : rho * 2 * alpha = Rmult rho (Rmult 2 alpha)).
ring.
rewrite H0.
clear H.
clear H0.
apply Rmult_lt_compat_l.
intuition.
apply Rmult_lt_reg_r with (/(C*C)).
apply Rinv_0_lt_compat.
apply Rlt_0_sqr.
trivial.
field_simplify.
assert (H : rho / 1 = rho).
field.
assert (Hcarre : C ^ 2 = C * C).
field.
rewrite Hcarre.
clear Hcarre.
apply Hrho.
trivial. trivial.
assert (H' : 1 - 2 * rho * alpha + rho * rho * C * C < 1).
assert (H0 : (1 - (2*rho*alpha)) + rho * rho * C * C
           =
            Rplus 1 (Rplus (-2*rho*alpha) (rho*rho*C*C))).
ring_simplify.
assert (Hp : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r).
intros r r1 r2 Heq.
rewrite Heq; reflexivity.
apply Hp.
ring_simplify.
reflexivity.
rewrite H0.
replace 1 with (Rplus 1 0) at 2.
apply Rplus_lt_compat_l.
apply Rplus_lt_reg_r with (2 * rho * alpha).
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
ring_simplify.
ring_simplify in H.
trivial.
ring.
rewrite <- sqrt_1 at 2.
apply sqrt_lt_1_alt.
split.
assert (HR : (-(alpha*alpha)/(C*C)) + ((Rsqr ((rho*C) - (alpha/C))) + 1)
       =
        1 - 2 * rho * alpha + rho * rho * C * C).
rewrite Rsqr_minus.
assert (Hra :  2 * (rho * C) * (alpha / C) = 2*rho*alpha).
rewrite Rmult_assoc.
assert (Hra2 : (Rmult (Rmult rho C) (Rdiv alpha C))
               =
               (Rmult rho (Rmult C (Rdiv alpha C)))).
ring.
rewrite Hra2.
assert (Hra3 : Rdiv alpha C = Rmult alpha (Rinv C)).
field.
trivial.
rewrite Hra3.
assert (Hra4 : (C * (alpha * / C)) = alpha).
field.
trivial.
rewrite Hra4.
rewrite Rmult_assoc.
reflexivity.
rewrite Hra.
ring_simplify.
assert (Hp : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r).
intros r r1 r2 Heq.
rewrite Heq; reflexivity.
apply Hp.
rewrite Rsqr_mult.
assert (Hqd : (alpha * alpha) / (C * C)
       = (alpha / C)²).
rewrite Rsqr_div.
reflexivity.
trivial.
rewrite <- Hqd.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
assert (Aa : alpha * alpha / (C * C)
      + - (alpha * alpha) / (C * C) = 0).
field.
trivial.
rewrite Aa.
ring_simplify.
assert (Hpowr : Rsqr rho = pow rho (S (S O))).
unfold Rsqr.
ring_simplify.
reflexivity.
assert (Hpowc : Rsqr C = pow C (S (S O))).
unfold Rsqr.
ring_simplify.
reflexivity.
rewrite Hpowr.
rewrite Hpowc.
reflexivity.
apply comp_lm_aux_phi.
trivial.
trivial.
trivial.
Qed.

Theorem Lax_Milgram_115
   (f:topo_dual E):
  forall u : E, alpha*(Rsqr (norm u)) <= ((a u) u).
Proof.
intros u.
unfold is_coercive in Hca.
unfold Rsqr.
rewrite <- Rmult_assoc.
apply (proj2 Hca).
Qed.

Theorem Lax_Milgram_116_phi :
               forall u : E, operator_norm_phi phi (A u) <= M*(norm u).
Proof.
intros u.
unfold operator_norm_phi.
destruct (Is_only_zero_set_dec_phi E).
unfold Lub_Rbar.
destruct (ex_lub_Rbar
 (fun x : R => exists u0 : Hilbert_NormedModule E,
     u0 <> zero /\ phi u0 /\ x = (norm (A u u0) / norm u0))).
simpl.
unfold is_lub_Rbar in i.
unfold is_ub_Rbar in i.
destruct i.
assert (HM : exists M', M' = M*norm u).
exists (M*norm u).
reflexivity.
destruct HM as (N,HN).
rewrite <- HN.
assert (H' : Rbar_le x N).
apply H0.
intros x0 HH.
simpl.
destruct HH as (u0,(Hu01,(Hu00,Hu02))).
rewrite Hu02.
rewrite HN.
apply Rmult_le_reg_r with (norm u0).
apply norm_gt_0; trivial.
replace (norm ((A u) u0)
        / norm u0 * norm u0) with
        (norm ((A u) u0)).
destruct Hba as (Hba1,(Hba2,Hba3)).
replace ((A u) u0) with (a u u0).
apply Hba3.
apply A_bil.
field.
assert (Hg : 0 < norm u0).
apply norm_gt_0; trivial.
apply Rgt_not_eq.
apply Rlt_gt; trivial.
unfold Rbar_le in H'.
destruct x.
trivial.
simpl.
rewrite HN.
replace 0 with (0*0) by ring.
apply Rmult_le_compat; trivial.
apply Rle_refl.
apply Rle_refl.
apply (proj1 (proj2 Hba)).
apply norm_ge_0.
simpl.
replace 0 with (0*0) by ring.
rewrite HN.
apply Rmult_le_compat; trivial.
apply Rle_refl.
apply Rle_refl.
apply (proj1 (proj2 Hba)).
apply norm_ge_0.
simpl.
replace 0 with (0*0) by ring.
apply Rmult_le_compat; trivial.
apply Rle_refl.
apply Rle_refl.
apply (proj1 (proj2 Hba)).
apply norm_ge_0.
Qed.

Theorem Lax_Milgram_117_phi (f:topo_dual E) : (forall g : topo_dual E, decidable (f_phi_neq_zero phi g)) ->
  (forall (f:topo_dual E), forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
  forall u : E, phi u -> - (inner (Tau (A u)) u) <= - (alpha*(Rsqr (norm u))).
Proof.
intros HdD HD u Hu.
apply Ropp_le_contravar.
apply Rle_trans with (a u u).
apply Lax_Milgram_115.
apply f.
assert (H : (A u) u = inner (Tau (A u)) u).
unfold Tau.
assert (H0 : exists! (u0:E), phi u0 /\ forall (v:E),
             phi v -> ((A u) v = inner u0 v)).
apply Riesz_Frechet_strong_phi; trivial.
destruct H0 as (w,H0).
assert (H0' : iota (fun u0 : E => phi u0 /\ forall v : E, phi v ->
       ((A u) v = inner u0 v)) = w).
apply iota_elim.
trivial.
rewrite H0'.
apply H0.
trivial.
rewrite <- H.
assert (Hr : a u u = (A u) u).
apply A_bil.
rewrite Hr.
apply Rle_refl.
Qed.

Theorem Lax_Milgram_118_phi (f:topo_dual E) :
             (forall (f:topo_dual E), forall u, forall eps:posreal,
                     decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps))) ->
             (forall f: topo_dual E, decidable (f_phi_neq_zero phi f)) ->
             forall u : E, norm (Tau (A u)) <= M*(norm u).
Proof.
intros HH HD u.
apply Rle_trans with (operator_norm_phi phi (A u)).
unfold Tau.
rewrite (Riesz_Frechet_moreover1_phi phi).
apply Rle_refl.
trivial.
trivial.
try assumption.
trivial.
trivial.
apply Lax_Milgram_116_phi; trivial.
Qed.

(** Implication (2) -> (1) *)

Theorem Lax_Milgram'_aux1_phi (f:topo_dual  E)  :
     (forall f : topo_dual E, decidable (f_phi_neq_zero phi f))
  -> (forall g : topo_dual E, forall u, forall eps:posreal, decidable (exists w:E, ((ker g w /\ phi w)
                                                          /\ norm (minus u w) < eps)))
  -> ((exists! u:E, phi u /\ Tau ((A u)) = Tau f)
  -> (exists! u:E, (is_sol_linear_pb_phi f u))).
Proof.
intros Hd Hdec H.
destruct H as (u,H).
exists u.
assert (HA : forall v, (A u) v = a u v).
intros v.
symmetry.
apply A_bil.
unfold unique.
split.
unfold is_sol_linear_pb_phi.
split.
apply H.
intros v phi_V.
assert (H1 : exists! (w:E), phi w /\ forall (v:E),
      phi v -> f v = inner w v).
apply Riesz_Frechet_strong_phi; try assumption.
intro xx.
trivial.
trivial.
destruct H1 as (uf,Huf).
assert (Huf' : iota (fun w : E => phi w /\ forall v0 : E, phi v0 ->
                                  f v0 = inner w v0) = uf).
apply iota_elim.
trivial.
unfold Tau in H.
rewrite Huf' in H.
assert (H2 : exists! (w:E), phi w /\ forall (v:E),
      phi v -> (A u) v = inner w v).
apply Riesz_Frechet_strong_phi; trivial.
trivial.
destruct H2 as (uA,HuA).
assert (HuA' : iota (fun w : E => phi w /\ forall v0 : E, phi v0 ->
                                           (A u) v0 = inner w v0) = uA).
apply iota_elim.
trivial.
assert (Haf : uA = uf).
rewrite <- HuA'.
destruct H as (H,Hun).
rewrite <- (proj2 H).
trivial.
assert (HH1 : a u v = inner uA v).
rewrite <- HA.
apply HuA.
trivial.
assert (HH2 : f v = inner uA v).
rewrite Haf.
apply Huf.
trivial.
rewrite HH1 HH2.
reflexivity.
intros x' Hx'.
destruct H as (H,Hun).
apply Hun.
unfold is_sol_linear_pb_phi in Hx'.
unfold Tau.
assert (H1 : exists! (w:E), phi w /\ forall (v:E),
      phi v -> ((A u) v = inner w v)).
apply Riesz_Frechet_strong_phi; trivial.
split.
exact (proj1 Hx').
assert (H2 : exists! (w:E), phi w /\ forall (v:E),
      phi v -> f v = inner w v).
apply Riesz_Frechet_strong_phi; trivial.
destruct H1 as (wa,H1).
destruct H2 as (wf,H2).
assert (H1' : iota (fun u0 : E => phi u0 /\
       forall v : E, phi v -> ((A u) v = inner u0 v)) = wa).
apply iota_elim.
trivial.
assert (H2' : iota (fun u0 : E => phi u0 /\
       forall v : E, phi v -> f v = inner u0 v) = wf).
apply iota_elim.
trivial.
rewrite H2'.
assert (forall v: E, phi v -> f v = inner wf v).
intros v'.
apply H2.
assert (forall v: E, phi v -> a x' v = inner wf v).
intros v' Hv'.
rewrite (proj2 Hx').
apply H0.
trivial.
trivial.
assert ((iota (fun u0 : E => phi u0 /\ forall v : E, phi v ->
   ((A x') v = inner u0 v))) = wf).
apply iota_elim.
assert (H5 : exists! (w:E), phi w /\ forall (v:E),
             phi v -> ((A x') v = inner w v)).
apply Riesz_Frechet_strong_phi; trivial.
unfold unique; split.
split.
rewrite <- H2'.
assert (Hphi: exists! (w:E), phi w /\ forall (v:E),
      phi v -> f v = inner w v).
apply Riesz_Frechet_strong_phi; trivial.
destruct Hphi as (w,Hphi).
generalize Hphi.
intros Hphi'.
apply (iota_elim _ _) in Hphi.
rewrite Hphi.
apply Hphi'.
intros v Hv.
transitivity (a x' v).
symmetry.
apply A_bil.
apply H3.
trivial.
intros x'0 Hh.
destruct H5 as (y,H5).
destruct H5 as (H51,H52).
assert (y = x'0).
apply H52.
trivial.
assert (y = wf).
apply H52.
split.
rewrite <- H2'.
assert (Hphi: exists! (w:E), phi w /\ forall (v:E),
      phi v -> f v = inner w v).
apply Riesz_Frechet_strong_phi; trivial.
destruct Hphi as (w,Hphi).
generalize Hphi.
intros Hphi'.
apply (iota_elim _ _) in Hphi.
rewrite Hphi.
apply Hphi'.
intros v Hv.
transitivity (a x' v).
symmetry.
apply A_bil.
apply H3.
trivial.
rewrite <- H5, H4.
reflexivity.
trivial.
Qed.

(** Implication (3) -> (2) *)

Definition g_map_app (r : R) (f : topo_dual E) :=
      (fun u:E =>  plus (minus u (scal r (Tau (A u)))) (scal r (Tau f))).

Theorem Lax_Milgram'_aux2_phi (r : R) (f:topo_dual  E) :
     0 < r < ((2*alpha)/(M*M))
  -> (forall (f : topo_dual E), decidable (f_phi_neq_zero phi f))
  -> (forall (g : topo_dual E), forall u, forall eps:posreal, decidable (exists w:E, ((ker g w /\ phi w)
                                                          /\ norm (minus u w) < eps)))
  -> (exists! u:E, phi u /\ (g_map_app r f u = u))
  -> (exists! u:E, (is_sol_linear_pb_phi f u)).
Proof.
intros Hr Hd Hd0 H.
destruct H as (u,H).
apply Lax_Milgram'_aux1_phi; trivial.
exists u.
unfold g_map_app in H.
unfold minus in H.
destruct H as (H,H2).
rewrite <- plus_assoc in H.
destruct H as (Pu,H).
symmetry in H.
assert (Hu0 : plus u zero = u).
rewrite plus_zero_r. reflexivity.
rewrite <- Hu0 in H at 1.
apply plus_reg_l in H.
clear Hu0.
symmetry in H.
assert (H0 : minus (scal r (Tau f))
              (scal r (Tau (A u))) = zero).
unfold minus.
rewrite plus_comm.
trivial.
assert (Hm : minus (scal r (Tau f))
        (scal r (Tau (A u))) =
       scal r (minus (Tau f) (Tau (A  u)))).
rewrite scal_minus_distr_l.
reflexivity.
rewrite Hm in H0.
assert (minus (Tau f) (Tau (A u)) = zero).
destruct (is_zero_dec
          (minus (Tau f) (Tau (A u)))).
trivial.
absurd (norm
       (scal r (minus (Tau f)
        (Tau (A u))))= 0).
apply Rgt_not_eq.
apply Rlt_gt.
rewrite norm_scal_R.
apply Rmult_lt_0_compat.
unfold abs.
simpl.
unfold Rabs.
destruct (Rcase_abs r).
absurd (0 < r).
apply Rle_not_lt.
intuition.
apply Hr.
apply Hr.
apply norm_gt_0.
trivial.
rewrite H0.
rewrite norm_zero.
reflexivity.
split.
unfold minus in H1.
split; try assumption.
apply plus_reg_r with (opp (Tau (A u))).
rewrite plus_opp_r.
symmetry.
trivial.
intros x' Hbil.
apply H2.
split.
exact (proj1 Hbil).
rewrite (proj2 Hbil).
rewrite <- plus_assoc.
rewrite plus_opp_l.
rewrite plus_zero_r.
reflexivity.
Qed.

(** Contraction and Fixpoint *)

Lemma g_map_diff_phi (r : R) (f:topo_dual  E) :
       (forall (f0 : topo_dual E), decidable (f_phi_neq_zero phi f0))
     ->  (forall (f : topo_dual E), forall u, forall eps:posreal, decidable (exists w:E, ((ker f w /\ phi w)
                                                          /\ norm (minus u w) < eps)))
    -> 0 < r < ((2*alpha)/(M*M))
    -> forall (v v' : E), phi v -> phi v' ->
       Rsqr (norm (minus (g_map_app r f v) (g_map_app r f v')))
       <= (1 - 2 * r * alpha + r * r * M * M)
          * Rsqr (norm (minus v v')).
Proof.
intros Hd Hd0 Hr v v'.
assert (H :(norm (minus (g_map_app r f v)
                     (g_map_app r f v')))²
         = (plus (norm (minus v v'))² (-
   2 * r * inner (Tau (A (minus v v'))) (minus v v') +
   r * r * (norm (Tau (A (minus v v'))))²))).
assert (Haux : minus (g_map_app r f v)
                     (g_map_app r f v')
              = (minus (minus v v')
               (scal r (Tau (A (minus v v')))))).
unfold g_map_app.
unfold minus.
rewrite opp_plus.
rewrite opp_plus.
rewrite <- plus_assoc.
rewrite <- plus_assoc.
rewrite <- plus_assoc.
rewrite <- plus_assoc.
rewrite plus_comm.
rewrite (plus_comm (opp v') _).
assert (Hp1 : forall a b, plus (plus a b) v
              = plus a (plus b v)).
intros.
rewrite plus_assoc.
reflexivity.
rewrite Hp1.
rewrite Hp1.
rewrite Hp1.
rewrite (plus_assoc v (opp v') _).
assert (Hp2 : forall a b, plus a (plus b
          (plus (opp v') v)) =
          plus (plus a b) (plus (opp v') v)).
intros.
rewrite plus_assoc. reflexivity.
rewrite Hp2.
rewrite Hp2.
rewrite plus_comm.
rewrite (plus_comm (opp v') v).
assert (Hpaux : ((plus (opp (scal r (Tau (A v))))
     (plus (scal r (Tau f))
        (plus (opp (opp (scal r (Tau (A v')))))
           (opp (scal r (Tau f)))))))
   = (opp (scal r (Tau (A (plus v (opp v'))))))).
rewrite plus_assoc.
rewrite opp_opp.
rewrite (plus_comm _ (opp (scal r (Tau f)))).
assert (Hg : forall a b c d : E, plus (plus a b) (plus c d)
                           = plus (plus a d) (plus b c)).
intros.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite plus_comm.
rewrite (plus_comm a0 d).
rewrite <- (plus_assoc d a0 b).
rewrite <- (plus_assoc d _ _).
reflexivity.
rewrite Hg.
rewrite plus_opp_r.
rewrite plus_zero_r.
replace (opp (scal r (Tau (A (plus v (opp v'))))))
        with
        (scal r (Tau (A (opp (plus v (opp v')))))).
replace ((opp (scal r (Tau (A v)))))
        with
        (scal r (Tau (A (opp v)))).
rewrite opp_plus.
rewrite opp_opp.
assert (ALf : is_linear_mapping A).
apply A.
destruct ALf as (Alf1,Alf2).
assert (H : is_linear_mapping Tau).
apply Riesz_Frechet_moreover2_phi; trivial.
destruct H as (Hl1,Hl2).
rewrite Alf1.
rewrite Hl1.
rewrite scal_distr_l.
reflexivity.
rewrite <- scal_opp_one.
rewrite scal_assoc.
assert (H : is_linear_mapping Tau).
apply Riesz_Frechet_moreover2_phi; trivial.
destruct H as (Hl1,Hl2).
rewrite <- Hl2.
rewrite <- Hl2.
assert (ALf : is_linear_mapping A).
apply A.
destruct ALf as (Alf1,Alf2).
rewrite <- Alf2.
rewrite <- Alf2.
assert (Hsr : (scal r (opp v))
        = (scal (mult (opp one) r) v)).
rewrite <- scal_assoc.
rewrite scal_opp_one.
rewrite scal_opp_r.
reflexivity.
rewrite Hsr.
reflexivity.
rewrite <- scal_opp_r.
rewrite <- scal_opp_one.
replace ((scal (opp one) (Tau (A (plus v (opp v'))))))
        with
        ((Tau (scal (opp one) (A (plus v (opp v')))))).
assert (H : is_linear_mapping Tau).
apply Riesz_Frechet_moreover2_phi; trivial.
destruct H as (Hl1,Hl2).
replace (Tau (A (opp (plus v (opp v')))))
     with (Tau (scal (opp one) (A (plus v (opp v'))))).
reflexivity.
clear Hp1 Hp2 Hg.
assert (Hlb : forall l y, scal l (A y)
                      = A (scal l y)).
intros l y.
apply clm_eq_ext.
intro x.
replace ((A (scal l y)) x) with (a (scal l y) x).
replace ((scal l (A y) x)) with (scal l (a y x)).
destruct Hba as (Hba1,Hba2).
destruct Hba1 as (Hba11,(Hba12,(Hba13,Hba14))).
symmetry; apply Hba11.
replace (a y x) with ((A y) x).
reflexivity.
symmetry.
apply A_bil.
assert (HAa : (A (scal l y)) x = a (scal l y) x).
symmetry; apply A_bil.
rewrite HAa.
reflexivity.
symmetry.
rewrite Hlb.
rewrite scal_opp_one.
reflexivity.
assert (HL : is_linear_mapping Tau).
apply Riesz_Frechet_moreover2_phi; trivial.
destruct HL as (Hl1,Hl2).
rewrite Hl2.
reflexivity.
rewrite Hpaux.
reflexivity.
rewrite Haux.
transitivity ((Hnorm (minus (minus v v')
              (scal r (Tau (A (minus v v'))))))*
              (Hnorm (minus (minus v v')
              (scal r (Tau (A (minus v v'))))))).
unfold norm; simpl.
reflexivity.
rewrite squared_norm.
rewrite square_expansion_minus.
rewrite <- squared_norm.
replace (Hnorm (minus v v')
       * Hnorm (minus v v')) with
         ((norm (minus v v'))²).
replace ((norm (minus v v'))² -
   2 * inner (minus v v') (scal r (Tau (A (minus v v')))) +
       inner (scal r (Tau (A (minus v v'))))
     (scal r (Tau (A (minus v v')))))
  with
   (plus ((norm (minus v v'))²)
     (- 2 * inner (minus v v') (scal r (Tau (A (minus v v')))) +
       inner (scal r (Tau (A (minus v v'))))
     (scal r (Tau (A (minus v v')))))).
apply Rplus_eq_compat_l.
rewrite <- squared_norm.
replace (Hnorm (scal r (Tau (A (minus v v')))))
      with (r* (Hnorm (Tau (A (minus v v'))))).
replace (r * Hnorm (Tau (A (minus v v'))) *
        (r * Hnorm (Tau (A (minus v v')))))
       with (r * r * (norm (Tau (A (minus v v'))))²).
rewrite Rplus_comm.
rewrite (Rplus_comm (-2 * r * inner (Tau (A
                 (minus v v'))) (minus v v')) _ ).
apply Rplus_eq_compat_l.
rewrite inner_scal_r.
rewrite inner_sym.
ring.
ring_simplify.
replace (Hnorm (Tau (A (minus v v'))) ^ 2)
   with ((norm (Tau (A (minus v v'))))²).
reflexivity.
unfold Rsqr.
unfold pow.
ring_simplify.
reflexivity.
replace r with (Rabs r) at 1.
rewrite hilbert.norm_scal.
reflexivity.
unfold Rabs.
destruct (Rcase_abs r).
absurd (r < 0).
apply Rle_not_lt.
intuition.
trivial.
reflexivity.
rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
ring.
reflexivity.
intros Hv Hv'.
rewrite H.
assert (H2 : (1 - 2 * r * alpha + r * r * M * M)
            * (norm (minus v v'))²
           = plus (Rsqr (norm (minus v v')))
             (- 2*r*alpha*(Rsqr (norm (minus v v')))
              + r*r*M*M*(Rsqr (norm (minus v v'))))).
rewrite Rmult_plus_distr_r.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite (Rplus_comm
        ((norm (minus v v'))²
         + -2 * r * alpha * (norm (minus v v'))²) _).
apply Rplus_eq_compat_l.
rewrite Rmult_plus_distr_r.
ring_simplify.
reflexivity.
rewrite H2.
apply Rplus_le_compat_l.
apply Rplus_le_compat.
replace (-2 * r * alpha * (norm (minus v v'))²)
    with ((-2*r)*(alpha *(norm (minus v v'))²)).
replace (-2 * r * inner
     (Tau (A (minus v v'))) (minus v v'))
    with
     ((2*r)*(- inner
     (Tau (A (minus v v'))) (minus v v')))
    by ring.
replace (-2 * r * (alpha * (norm (minus v v'))²))
    with
     ((2*r)*(-alpha * (norm (minus v v'))²))
    by ring.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
intuition.
intuition.
replace (- alpha * (norm (minus v v'))²)
        with (- (alpha*(Rsqr (norm (minus v v'))))).
apply Lax_Milgram_117_phi; trivial.
unfold minus.
apply (proj1 phi_m); trivial.
ring.
replace (norm (inner (Tau (A (minus v v'))) (minus v v')))
    with (abs ((inner (Tau (A (minus v v'))) (minus v v')))).
ring.
reflexivity.
replace (r*r * (norm (Tau (A (minus v v'))))²)
        with
        ((r*r) * (norm (Tau (A (minus v v'))))²).
replace (r*r * M*M * (norm (minus v v'))²)
        with
        ((r*r) *(M*M * (norm (minus v v'))²)).
apply Rmult_le_compat_l.
apply Rle_0_sqr.
replace (M * M * (norm (minus v v'))²)
        with (Rsqr (M * (norm (minus v v')))).
apply sqrt_le_0.
apply Rle_0_sqr.
apply Rle_0_sqr.
repeat (rewrite sqrt_Rsqr).
apply Lax_Milgram_118_phi; trivial.
apply Rmult_le_pos.
apply Hba.
apply norm_ge_0.
apply norm_ge_0.
ring_simplify.
rewrite Rsqr_mult.
apply Rmult_eq_compat_r.
unfold pow.
replace (M*1) with M by ring.
reflexivity.
ring.
reflexivity.
Qed.

Theorem Lax_Milgram'_aux3_phi (r : R)(f:topo_dual  E) :
     (forall f0 : topo_dual E, decidable (f_phi_neq_zero phi f0))
  -> (forall f0 : topo_dual E, forall u, forall eps:posreal, decidable (exists w:E, ((ker f0 w /\ phi w)
                                                          /\ norm (minus u w) < eps)))
  -> (~ Is_only_zero_set_phi E (fun x:E => phi x))
  -> 0 < r < ((2*alpha)/(M*M))
  -> (exists! u:E, phi u /\ (g_map_app r f u = u)).
Proof.
intros Hd Hd0 HE Hr.
assert (HC : is_contraction_phi (g_map_app r f) phi).
unfold is_contraction_phi.
destruct (Req_dec ((1 - (2*r*alpha)) + r*r*M*M) 0).
assert (forall v v', phi v -> phi v' -> Rsqr (norm (minus (g_map_app r f v) (g_map_app r f v')))
         = 0).
assert (forall v v', phi v -> phi v' -> Rsqr (norm (minus (g_map_app r f v) (g_map_app r f v')))
         <= 0).
intros v v' Hv Hv'.
replace 0 with ((1 - 2 * r * alpha + r * r * M * M)
          * Rsqr (norm (minus v v'))).
apply g_map_diff_phi; trivial.
rewrite H.
ring.
intros v v' Hv Hv'.
destruct (Req_dec (norm (minus (g_map_app r f v)
         (g_map_app r f v')))² 0).
trivial.
destruct (Rlt_le_dec
     (norm (minus (g_map_app r f v)
     (g_map_app r f v')))² 0).
absurd ((norm (minus (g_map_app r f v)
           (g_map_app r f v')))² < 0).
apply Rle_not_gt.
apply Rle_0_sqr.
trivial.
apply Rle_le_eq.
split; trivial.
apply H0; trivial.
exists (1 / 2).
split.
apply Rmult_lt_reg_r with 2.
intuition.
field_simplify.
replace (1 / 1) with 1 by field.
replace (2/1) with 2 by field.
intuition.
unfold is_Lipschitz_phi.
split.
assert (Hstrong : 0 < 1/2).
apply Rdiv_lt_0_compat.
intuition.
intuition.
intuition.
intros x1 x2 r0 Hr0 Hp1 Hp2 Hx2.
unfold ball_x in Hx2.
simpl in Hx2.
unfold hilbert.ball in Hx2.
unfold ball_y.
simpl.
unfold hilbert.ball.
specialize (H0 x1 x2).
unfold norm in H0; simpl in H0.
apply Rsqr_0_uniq in H0.
rewrite H0.
apply Rmult_lt_0_compat.
apply Rdiv_lt_0_compat.
intuition.
intuition.
trivial.
trivial.
trivial.
exists ((sqrt ((1 - (2*r*alpha)) + r*r*M*M))).
split.
apply comp_lax_milgram_phi; trivial.
split.
apply (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
unfold is_Lipschitz_phi.
split.
apply comp_lax_milgram_phi; trivial.
split.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
intros x1 x2 r1 Hr0 Hp1 Hp2 Hx2.
unfold ball_x in Hx2.
simpl in Hx2.
unfold hilbert.ball in Hx2.
unfold ball_y.
simpl.
unfold hilbert.ball.
apply Rle_lt_trans with
    (sqrt (1 - 2 * r * alpha + r * r * M * M)
   * (Hnorm (minus x1 x2))).
assert (Hsq : Hnorm (minus (g_map_app r f x1)
       (g_map_app r f x2))
     = (sqrt (Rsqr (norm (minus (g_map_app r f x1)
          (g_map_app r f x2)))))).
rewrite sqrt_Rsqr.
unfold norm; simpl.
reflexivity.
apply norm_ge_0.
rewrite Hsq.
assert (Hsq2 : sqrt (1 - 2 * r * alpha + r * r * M * M)
               * Hnorm (minus x1 x2)
              =
               sqrt ((1 - 2 * r * alpha + r * r * M * M)
                     * Rsqr (Hnorm (minus x1 x2)))).
rewrite sqrt_mult_alt.
rewrite sqrt_Rsqr.
reflexivity.
assert (Hh : Hnorm (minus x1 x2) = norm (minus x1 x2)).
unfold norm; simpl; reflexivity.
rewrite Hh.
apply norm_ge_0.
apply comp_lm_aux_phi.
split.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
trivial.
rewrite Hsq2.
apply sqrt_le_1.
apply Rle_0_sqr.
apply Rmult_le_pos.
apply comp_lm_aux_phi.
split.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
trivial.
apply Rle_0_sqr.
apply g_map_diff_phi; trivial.
apply Rmult_lt_compat_l.
apply sqrt_lt_R0.
assert (0 <= 1 - 2 * r * alpha + r * r * M * M).
apply comp_lm_aux_phi.
split.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
trivial.
apply Rdichotomy in H.
destruct H.
absurd (0 <= 1 - 2 * r * alpha + r * r * M * M).
apply Rlt_not_le.
trivial.
trivial.
trivial.
trivial.
destruct (FixedPoint_C_phi (g_map_app r f) phi); trivial.
intros x Hx.
unfold g_map_app.
destruct phi_m as ((P1,P2),P3).
replace (scal r (Tau f)) with (opp (scal (opp r) (Tau f))).
apply P1.
unfold minus.
apply P1.
trivial.
apply P3.
apply phi_Tau.
trivial.
trivial.
trivial.
apply P3.
apply phi_Tau.
trivial. trivial.
trivial.
rewrite scal_opp_l.
rewrite opp_opp; reflexivity.
intros x y _ _.
exists (2*(norm (minus x y)) + 1).
split.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos.
intuition.
apply norm_ge_0.
intuition.
unfold ball. simpl. unfold hilbert.ball.
unfold norm. simpl.
rewrite <- Rplus_0_r at 1.
apply Rplus_le_lt_compat.
assert (Hh : Hnorm (minus x y) = 1*Hnorm (minus x y)).
ring.
rewrite Hh.
apply Rmult_le_compat.
intuition.
destruct (norm_ge_0 (minus x y)).
unfold norm in H. simpl in H.
intuition.
rewrite H.
unfold norm; simpl.
intuition.
intuition.
ring_simplify.
intuition.
intuition.
destruct phi_m as ((_,HH),_).
apply HH.
exists x.
unfold unique.
split.
split.
exact (proj1 H).
apply eq_close.
apply (proj1 (proj2 H)).
intros y Hy.
apply eq_close.
apply close_sym.
apply (proj1 (proj2 (proj2 H))).
exact (proj1 Hy).
rewrite (proj2 Hy); apply close_refl.
Qed.

(** Weak versions of Lax-Milgram theorem *)

Theorem Lax_Milgram''_phi (f:topo_dual E):
  (forall f0 : topo_dual E, decidable (f_phi_neq_zero phi f0))
  -> (forall f0 : topo_dual E, forall u, forall eps:posreal,
                               decidable (exists w:E, ((ker f0 w /\ phi w)
                               /\ norm (minus u w) < eps)))
  -> exists u:E, is_sol_linear_pb_phi f u /\
          (forall u', is_sol_linear_pb_phi f u' -> u'=u).
Proof.
intros Hd Hd0.
destruct (Is_only_zero_set_dec_phi E phi).
assert (Haux : forall r, 0 < r < ((2*alpha)/(M*M))
             -> exists! u:E, (is_sol_linear_pb_phi f u)).
intros r Hr.
apply Lax_Milgram'_aux2_phi with r; trivial.
trivial.
apply Lax_Milgram'_aux3_phi; trivial.
specialize (Haux (alpha / (M * M))).
assert (Haux' : exists ! u : E, is_sol_linear_pb_phi f u).
apply Haux.
split.
apply Rdiv_lt_0_compat.
exact (proj1 Hca).
apply Rmult_lt_0_compat.
apply Rlt_le_trans with alpha.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
apply Rlt_le_trans with alpha.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
replace (alpha / (M * M)) with (1 * (alpha / (M * M))).
replace (2 * alpha / (M * M)) with (2* (alpha / (M * M))).
apply Rmult_lt_compat_r.
apply Rdiv_lt_0_compat.
exact (proj1 Hca).
apply Rmult_lt_0_compat.
apply Rlt_le_trans with alpha.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
apply Rlt_le_trans with alpha.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
intuition.
replace (alpha / (M * M)) with (alpha * (/ (M*M))).
replace (2* alpha / (M * M)) with (2* alpha * (/ (M*M))).
rewrite Rmult_assoc.
reflexivity.
field.
assert (HM : 0 < M).
apply Rlt_le_trans with alpha.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
apply Rgt_not_eq.
apply Rlt_gt.
trivial.
field.
assert (HM : 0 < M).
apply Rlt_le_trans with alpha.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
apply Rgt_not_eq.
apply Rlt_gt.
trivial.
field.
assert (HM : 0 < M).
apply Rlt_le_trans with alpha.
exact (proj1 Hca).
apply coercivity_le_continuity_phi with phi a; trivial.
apply Rgt_not_eq.
apply Rlt_gt.
trivial.
destruct Haux' as (u,Hu).
unfold unique in Hu.
exists u.
split.
exact (proj1 Hu).
intros u' Hu'.
symmetry.
apply (proj2 Hu).
trivial.
exists zero.
split.
unfold is_sol_linear_pb_phi.
split.
apply (compatible_m_zero phi).
trivial.
intros v Hv.
apply Is_only_zero_set_correct1_phi with E phi v in i.
rewrite i.
destruct Hba as ((Hba1,(Hba2,Hba3)),Hba4).
assert (a zero zero = a (scal zero zero) zero).
rewrite scal_zero_l.
reflexivity.
rewrite H.
replace (a (scal zero zero) zero)
        with (scal zero (a zero zero)).
rewrite scal_zero_l.
assert (is_linear_mapping f).
apply f.
destruct H0 as (H01,H02).
replace (f zero) with (f (scal zero zero)).
transitivity (scal zero (f zero)).
rewrite scal_zero_l.
reflexivity.
symmetry.
apply H02.
rewrite scal_zero_l.
reflexivity.
symmetry.
apply Hba1.
trivial.
intros u' Hu'.
apply Is_only_zero_set_correct1_phi with E phi u' in i.
rewrite i.
reflexivity.
exact (proj1 Hu').
Qed.

Theorem Lax_Milgram_Aux_phi (f:topo_dual E):
  (forall f0 : topo_dual E, decidable (f_phi_neq_zero phi f0))
  -> (forall f0 : topo_dual E, forall u, forall eps:posreal,
      decidable (exists w:E, ((ker f0 w /\ phi w)
      /\ norm (minus u w) < eps)))
  -> exists u:E, is_sol_linear_pb_phi f u /\
          (forall u', is_sol_linear_pb_phi f u' -> u'=u) /\
           norm u <= /alpha * norm f.
Proof.
intros Hd Hd0.
assert (H' : exists u : E,
             is_sol_linear_pb_phi f u /\
             (forall u' : E, is_sol_linear_pb_phi f u' -> u' = u)).
apply Lax_Milgram''_phi; trivial.
destruct H' as (u,(He,Hu)).
exists u.
split; trivial.
split; trivial.
destruct (is_zero_dec u).
+ rewrite H.
  rewrite norm_zero.
  destruct Hca as (Hca',_).
  apply Rmult_le_pos.
  assert (Hsp : 0 < / alpha).
  apply Rinv_0_lt_compat.
  trivial.
  intuition.
  apply norm_ge_0.
+ assert (alpha*(Rsqr (norm u)) <= norm f * norm u).
  apply Rle_trans with (norm (f u)).
  apply Rle_trans with (norm (a u u)).
  destruct Hca as (Hca1,Hca2).
  specialize (Hca2 u).
  unfold norm; simpl.
  unfold abs; simpl.
  unfold Rsqr.
  unfold norm in Hca2; simpl in Hca2.
  rewrite <- Rmult_assoc.
  apply Rle_trans with (a u u).
  exact Hca2.
  unfold Rabs.
  destruct (Rcase_abs (a u u)).
  apply Rle_trans with 0.
  intuition.
  apply Ropp_0_ge_le_contravar.
  apply Rle_ge.
  intuition.
  right; reflexivity.
  specialize ((proj2 He) u).
  intros Heu.
  specialize (Heu (proj1 He)).
  rewrite Heu.
  apply Rle_refl.
  apply operator_norm_estimation.
  apply Rmult_le_reg_l with (norm u).
  apply norm_gt_0; trivial.
  rewrite (Rmult_comm (norm u) (/ alpha * norm f)).
  apply Rmult_le_reg_l with alpha.
  apply Hca.
  assert (Ha : alpha * (/ alpha * norm f * norm u)
               = norm f * norm u).
  field.
  apply Rgt_not_eq.
  apply Rlt_gt.
  apply Hca.
  rewrite Ha.
  intuition.
Qed.

End LM_aux.

(** Lax-Milgram theorem *)

Section Lax_Milgram.

Context {E : Hilbert}.

Variable a : E -> E -> R.
Variable M : R.
Variable alpha : R.
Variable phi : E -> Prop.
Hypothesis phi_C : my_complete phi.
Hypothesis phi_m : compatible_m phi.
Hypothesis Hba : is_bounded_bilinear_mapping a M.
Hypothesis Hca : is_coercive a alpha.

Theorem Lax_Milgram_phi (f:topo_dual E):
  (forall f0 : topo_dual E, decidable (f_phi_neq_zero phi f0))
  -> (forall f0 : topo_dual E, forall u, forall eps:posreal,
      decidable (exists w:E, ((ker f0 w /\ phi w)
      /\ norm (minus u w) < eps)))
  -> exists u:E, is_sol_linear_pb_phi a phi f u /\
          (forall u', is_sol_linear_pb_phi a phi f u' -> u'=u) /\
           norm u <= /alpha * norm f.
Proof.
intros Hd Hd0.
assert (Hbil : exists! (A:(clm E (topo_dual E))),
             forall (u v:E), a u v = (A u) v).
apply is_bounded_bilinear_mapping_representation with M.
trivial.
destruct Hbil as (A0,Hbil).
apply Lax_Milgram_Aux_phi with M A0; try assumption.

Qed.

End Lax_Milgram.

Section LM_True.

Context{E : Hilbert}.
Variable a : E -> E -> R.
Variable M : R.
Variable alpha : R.
Hypothesis Hba : is_bounded_bilinear_mapping a M.
Hypothesis Hca : is_coercive a alpha.

Theorem Lax_Milgram_true (f:topo_dual E):
  (forall g: topo_dual E, decidable (exists u0, g u0 <> 0)) ->
  (forall f0 : topo_dual E, forall u, forall eps:posreal,
      decidable (exists w:E, ((ker f0 w)
      /\ norm (minus u w) < eps)))
  -> exists u:E, is_sol_linear_pb_phi a (fun _ => True) f u /\
          (forall u', is_sol_linear_pb_phi a (fun _ => True) f u' -> u'=u) /\
           norm u <= /alpha * norm f.
Proof.
intros Hd HD.
assert (Hdd : decidable (f_phi_neq_zero (fun _ => True) f)).
unfold f_phi_neq_zero.
destruct (Hd f).
left.
destruct H as (u,H).
exists u; now split.
right.
intros (u,J).
apply H.
exists u; intuition.
assert (Hmc : my_complete (fun x : E => True)).
easy.
assert (Hmm : compatible_m (fun x : E =>  True)).
split; try split; try easy.
now exists zero.
generalize (Lax_Milgram_phi a M alpha (fun x : E => True)
 Hmc Hmm Hba Hca) => LMP.
specialize (LMP f).
assert (Haa : (forall f0 : topo_dual E,
       decidable (f_phi_neq_zero (fun _ : E => True) f0))).
intros g.
destruct (Hd g).
destruct H as (v,H).
left.
exists v.
split; try easy.
right.
intro Hh.
apply H.
destruct Hh as (h,(_,Hhh)).
now exists h.
specialize (LMP Haa).
assert (HD' : (forall (f0 : topo_dual E) (u : E) (eps : posreal),
       decidable
         (exists w : E,
            (ker f0 w /\ True) /\ norm (minus u w) < eps))).
intros g u e.
destruct (HD g u e).
left.
destruct H as (w,H).
exists w.
split; try intuition.
right.
intro Hh.
apply H.
destruct Hh as (w,Hh).
exists w.
intuition.
specialize (LMP HD').
trivial.
Qed.

End LM_True.
