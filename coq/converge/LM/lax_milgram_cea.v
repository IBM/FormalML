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
Require Import hilbert.
Require Export Decidable.
Require Export FunctionalExtensionality.
Require Export mathcomp.ssreflect.ssreflect.
Require Export Coquelicot.Hierarchy.
Require Export Reals.
Require Export logic_tricks.
Require Export ProofIrrelevanceFacts.
Require Export lax_milgram.

(** Lax-Milgram-Cea's Theorem *)

Section LMC.

Context { E : Hilbert }.

Variable a : E -> E -> R.
Variable M : R.
Variable alpha : R.
Hypothesis Hba : is_bounded_bilinear_mapping a M.
Hypothesis Hca : is_coercive a alpha.

Lemma Galerkin_orthogonality (u uh : E)
               (f:topo_dual E) (phi : E -> Prop) :
      (forall (f : topo_dual E), decidable (exists u : E, f u <> 0)) ->
      phi uh ->
      is_sol_linear_pb_phi a (fun x:E => True) f u ->
      is_sol_linear_pb_phi a phi f uh ->
      (forall vh : E, phi vh -> a (minus u uh) vh = 0).
Proof.
intros Hd phi_uh Hle Hleh vh SubEh.
unfold minus.
destruct Hba as ((Hba1,(Hba2,(Hba3,Hba4))),_).
rewrite Hba3.
replace (opp uh) with (scal (opp one) uh).
rewrite Hba1.
rewrite scal_opp_one.
unfold is_sol_linear_pb_phi in Hle.
destruct Hle as (_,Hle).
rewrite Hle.
rewrite (proj2 Hleh).
rewrite plus_opp_r.
reflexivity.
trivial.
trivial.
rewrite scal_opp_one.
reflexivity.
Qed.

Lemma Lax_Milgram_Cea (u uh : E) (f:topo_dual E)  (phi : E -> Prop) :
      (forall (f : topo_dual E), decidable (exists u : E, f u <> 0)) ->
      phi uh -> compatible_m phi -> my_complete phi ->
      is_sol_linear_pb_phi a (fun x:E => True) f u ->
      is_sol_linear_pb_phi a phi f uh -> (forall vh : E, phi vh ->
      norm (minus u uh) <= (M/alpha) * norm (minus u vh)).
Proof.
intros Hdf Huh HM HC H1 H2 vh Hvh.
destruct (is_zero_dec (minus u uh)).
rewrite H.
rewrite norm_zero.
apply Rmult_le_pos.
destruct Hba as (_,(Hb,_)).
replace (M / alpha) with (M * / alpha); try trivial.
replace 0 with (0*0).
apply Rmult_le_compat; intuition.
intuition.
destruct Hca as (Hc,_).
apply Rinv_0_lt_compat in Hc.
intuition. ring.
apply norm_ge_0.
assert (Ha : a (minus u uh) (minus u vh) = a (minus u uh) u).
transitivity (minus (a (minus u uh) u) (a (minus u uh) vh)).
destruct Hba as ((Hba1,(Hba2,(Hba3,Hba4))),_).
rewrite Hba4.
unfold minus at 3.
replace (a (minus u uh) (opp vh)) with (opp (a (minus u uh) vh)).
reflexivity.
replace (opp vh) with (scal (opp one) vh).
rewrite Hba2.
rewrite scal_opp_one.
reflexivity.
rewrite scal_opp_one.
reflexivity.
replace (a (minus u uh) vh) with 0.
unfold minus at 1.
rewrite opp_zero.
rewrite plus_zero_r.
reflexivity.
symmetry.
apply Galerkin_orthogonality with f phi; try assumption.
apply Rmult_le_reg_l with alpha.
apply Hca.
field_simplify.
replace (alpha * norm (minus u uh) / 1) with (alpha * norm (minus u uh))
        by field.
replace (M * norm (minus u vh) / 1) with (M * norm (minus u vh)) by field.
apply Rmult_le_reg_r with (norm (minus u uh)).
now apply norm_gt_0.
unfold is_bounded_bilinear_mapping in Hba.
destruct Hba as (H0,H3).
unfold is_bounded_bi in H3.
destruct H3 as (H3,H4).
specialize (H4 (minus u uh) (minus u vh)).
apply Rle_trans with (norm (a (minus u uh) (minus u vh)));
      try assumption.
rewrite Ha.
destruct Hca as (H5,H6).
unfold is_sol_linear_pb_phi in *.
destruct H1 as (X1,H1).
destruct H2 as (X2,H2).
replace (a (minus u uh) u)
        with (a (minus u uh) (minus u uh)).
specialize (H6 (minus u uh)).
unfold norm at 3.
simpl.
apply Rle_trans with (a (minus u uh) (minus u uh)).
trivial.
unfold abs.
simpl.
apply Rle_abs.
destruct H0 as (H0,H7).
destruct H7 as (H7,(H8,H9)).
unfold minus.
rewrite H9.
replace (a (plus u (opp uh)) u) with
        (plus (a (plus u (opp uh)) u) 0).
f_equal.
now rewrite plus_zero_r.
specialize (H1 uh).
apply H1 in X1.
specialize (H2 uh).
apply H2 in X2.
clear H1 H2.
rewrite H8.
replace (a u (opp uh)) with (opp (a u uh)).
rewrite X1.
replace (a (opp uh) (opp uh)) with (a uh uh).
rewrite X2.
rewrite plus_opp_l; reflexivity.
replace (opp uh) with (scal (opp one) uh).
replace (opp uh) with (scal (opp one) uh).
rewrite H0 H7 2!scal_opp_l scal_one opp_opp scal_one.
reflexivity.
rewrite scal_opp_one.
reflexivity.
rewrite scal_opp_one; reflexivity.
replace (opp uh) with (scal (opp one) uh).
rewrite H7 scal_opp_one.
reflexivity.
rewrite scal_opp_one.
reflexivity.
rewrite plus_zero_r; reflexivity.
replace (M * norm (minus u vh) * norm (minus u uh)) with
        (M * norm (minus u uh) * norm (minus u vh)) by ring.
assumption.
destruct Hca.
intro Hk.
rewrite Hk in H0.
absurd (0 < 0); try assumption.
exact (Rlt_irrefl 0).
Qed.

End LMC.
