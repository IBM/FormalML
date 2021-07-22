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

Require Import FunctionalExtensionality.
Require Export compatible.

(** About functions from E to F *)

(** Note that Coquelicot has: U UniformSpace, then T->U UniformSpace,
   and similar for CompleteSpace *)

(** Functions to a ModuleSpace are a ModuleSpace *)

Section Fcts.

Context {E : Type}.
Context {F : ModuleSpace R_Ring}.

Definition fct_plus (f:E->F) (g:E->F) : (E->F) :=
  fun x => plus (f x) (g x).

Definition fct_scal (l:R) (f:E->F) : (E->F) :=
  fun x => scal l (f x).

Definition fct_opp (f:E->F) : (E -> F) :=
  fun x => opp (f x).

Definition fct_zero:E->F := fun _ => zero.

Lemma fct_plus_comm: forall (f g:E->F), fct_plus f g = fct_plus g f.
Proof.
intros f g.
apply functional_extensionality.
intros x; apply plus_comm.
Qed.

Lemma fct_plus_assoc:
  forall (f g h:E->F), fct_plus f (fct_plus g h) = fct_plus (fct_plus f g) h.
Proof.
intros f g h.
apply functional_extensionality.
intros x; apply plus_assoc.
Qed.

Lemma fct_plus_zero_r: forall f:E->F, fct_plus f fct_zero = f.
Proof.
intros f.
apply functional_extensionality.
intros x; apply plus_zero_r.
Qed.

Lemma fct_plus_opp_r: forall f:E->F, fct_plus f (fct_opp f) = fct_zero.
Proof.
intros f.
apply functional_extensionality.
intros x; apply plus_opp_r.
Qed.

Definition fct_AbelianGroup_mixin :=
  AbelianGroup.Mixin (E->F) fct_plus fct_opp fct_zero fct_plus_comm
   fct_plus_assoc fct_plus_zero_r fct_plus_opp_r.

Canonical fct_AbelianGroup :=
  AbelianGroup.Pack (E->F) (fct_AbelianGroup_mixin) (E->F).

Lemma fct_scal_assoc: forall x y (u:E->F),
   fct_scal x (fct_scal y u) = fct_scal (mult x y) u.
Proof.
intros x y u.
apply functional_extensionality.
intros x0; apply scal_assoc.
Qed.

Lemma fct_scal_one: forall (u:E->F), fct_scal one u = u.
Proof.
intros u.
apply functional_extensionality.
intros x; apply scal_one.
Qed.

Lemma fct_scal_distr_l: forall x (u v:E->F), fct_scal x (plus u v) = fct_plus (fct_scal x u) (fct_scal x v).
Proof.
intros x u v.
apply functional_extensionality.
intros x0; apply scal_distr_l.
Qed.

Lemma fct_scal_distr_r: forall (x y:R) (u:E->F), fct_scal (Rplus x y) u = fct_plus (fct_scal x u) (fct_scal y u).
Proof.
intros x y u.
apply functional_extensionality.
intros x0.
apply (scal_distr_r x y).
Qed.

Definition fct_ModuleSpace_mixin :=
  ModuleSpace.Mixin R_Ring fct_AbelianGroup fct_scal fct_scal_assoc
     fct_scal_one fct_scal_distr_l fct_scal_distr_r.

Canonical fct_ModuleSpace :=
  ModuleSpace.Pack R_Ring (E->F)
   (ModuleSpace.Class R_Ring (E->F) _ fct_ModuleSpace_mixin) (E->F).

End Fcts.

(** Linear Mapping *)

Section SSG_linear_mapping.

Context {E : ModuleSpace R_Ring}.
Context {F : ModuleSpace R_Ring}.

(* p18, def 55 *)
Definition is_linear_mapping (phi: E -> F) :=
  (forall (x y : E), phi (plus x y) = plus (phi x) (phi y))
     /\ (forall (x : E) (l:R), phi (scal l x) = scal l (phi x)).

Theorem compatible_g_is_linear_mapping:
    compatible_g is_linear_mapping.
Proof.
split.
intros f g (Hf1,Hf2) (Hg1,Hg2).
split.
 + intros x y.
   unfold plus at 1 4 5; unfold opp; simpl.
   unfold fct_plus, fct_opp.
   rewrite Hf1, Hg1.
   rewrite opp_plus.
   repeat rewrite <- plus_assoc.
   apply f_equal.
   repeat rewrite plus_assoc.
   apply f_equal2; try easy.
   apply plus_comm.
 + intros x l.
  unfold plus, opp;simpl.
  unfold fct_plus, fct_opp.
  rewrite Hf2, Hg2.
  rewrite <- scal_opp_l.
  rewrite scal_distr_l.
  apply f_equal.
  rewrite scal_opp_l.
  now rewrite scal_opp_r.
 + exists zero.
   split; unfold zero; intros; simpl; unfold fct_zero.
   now rewrite plus_zero_l.
   now rewrite scal_zero_r.
Qed.

Lemma is_linear_mapping_zero: forall f,
   is_linear_mapping f -> f zero = zero.
Proof.
intros f (Hf1,Hf2).
apply trans_eq with (f (scal zero zero)).
now rewrite scal_zero_l.
rewrite Hf2.
apply scal_zero_l.
Qed.

Lemma is_linear_mapping_opp: forall f x,
   is_linear_mapping f -> f (opp x) = opp (f x).
Proof.
intros f y (Hf1,Hf2).
rewrite <- scal_opp_one.
rewrite Hf2.
now rewrite scal_opp_one.
Qed.

Lemma is_linear_mapping_f_zero:
   is_linear_mapping (fun (x:E) => @zero F).
Proof.
split; intros.
apply sym_eq, plus_zero_l.
apply sym_eq, scal_zero_r.
Qed.

Lemma is_linear_mapping_f_opp: forall (f:E->F),
    is_linear_mapping f ->
      is_linear_mapping (opp f).
Proof.
intros f (H1,H2); split.
intros x y; unfold opp; simpl; unfold fct_opp.
rewrite H1.
apply opp_plus.
intros x l; unfold opp; simpl; unfold fct_opp.
rewrite H2.
now rewrite <- scal_opp_r.
Qed.

Lemma is_linear_mapping_f_plus: forall (f g:E->F),
    is_linear_mapping f -> is_linear_mapping g ->
      is_linear_mapping (plus f g).
Proof.
intros f g (H1,K1) (H2,K2); split.
intros x y; unfold plus at 1 4 5; simpl; unfold fct_plus.
rewrite H1, H2.
rewrite <- 2!plus_assoc; apply f_equal.
rewrite plus_comm, plus_assoc.
rewrite <- 2!plus_assoc; apply f_equal, plus_comm.
intros x l; unfold plus; simpl; unfold fct_plus.
rewrite K1, K2.
now rewrite scal_distr_l.
Qed.

Lemma is_linear_mapping_f_scal: forall l, forall (f:E->F),
    is_linear_mapping f ->
      is_linear_mapping (scal l f).
Proof.
intros l f (H1,H2); split.
intros x y; unfold scal; simpl; unfold fct_scal.
now rewrite H1, scal_distr_l.
intros x k.
unfold scal at 1 4; simpl; unfold fct_scal.
rewrite H2, 2!scal_assoc.
unfold mult; simpl.
now rewrite Rmult_comm.
Qed.

End SSG_linear_mapping.

Section SSG_bilinear_mapping.

Context {E : ModuleSpace R_Ring}.
Context {F : ModuleSpace R_Ring}.
Context {G : ModuleSpace R_Ring}.

Definition is_bilinear_mapping (phi: E -> F -> G) :=
  (forall (x:E) (y:F) (l:R), phi (scal l x) y = scal l (phi x y)) /\
  (forall (x:E) (y:F) (l:R), phi x (scal l y) = scal l (phi x y)) /\
  (forall (x y: E) (z:F), phi (plus x y) z = plus (phi x z) (phi y z)) /\
  (forall (x:E) (y z : F), phi x (plus y z) = plus (phi x y) (phi x z)).

Theorem compatible_g_is_bilinear_mapping:
    compatible_g is_bilinear_mapping.
split.
intros f g (Hf1,(Hf2,(Hf3,Hf4))) (Hg1,(Hg2,(Hg3,Hg4))).
split.
intros x y l;unfold plus; unfold opp; simpl;unfold fct_plus, fct_opp;unfold plus, opp; simpl;
   unfold fct_plus, fct_opp;rewrite Hf1,Hg1;rewrite <- scal_opp_r;now rewrite scal_distr_l.
split.
intros x y l;unfold plus; unfold opp; simpl;unfold fct_plus, fct_opp;unfold plus, opp; simpl;
   unfold fct_plus, fct_opp;rewrite Hf2,Hg2;rewrite <- scal_opp_r;now rewrite scal_distr_l.
split.
intros x y z; unfold plus at 1 4 5; unfold opp;simpl; unfold fct_plus, fct_opp;
  unfold plus at 1 5 6;unfold opp;simpl;unfold fct_plus, fct_opp;rewrite Hf3,Hg3;
  rewrite opp_plus;rewrite plus_assoc;rewrite plus_assoc;apply f_equal2;trivial.
 rewrite <- plus_assoc;rewrite (plus_comm (f y z) (opp (g x z)));now rewrite plus_assoc.
intros x y z; unfold plus at 1 4 5; unfold opp;simpl; unfold fct_plus, fct_opp.
  unfold plus at 1 4 5;unfold opp;simpl;unfold fct_plus, fct_opp. rewrite Hf4,Hg4;
  rewrite opp_plus;rewrite plus_assoc;rewrite plus_assoc;apply f_equal2;trivial.
 rewrite <- plus_assoc;rewrite (plus_comm (f x z) (opp (g x y)));now rewrite plus_assoc.
exists zero;split.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite scal_zero_r.
split.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite scal_zero_r.
split.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite plus_zero_l.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite plus_zero_l.
Qed.

End SSG_bilinear_mapping.

(** Injections, surjections, bijections *)

Section Inj_Surj_Bij.

Context {E : ModuleSpace R_Ring}.
Context {F : ModuleSpace R_Ring}.

Definition is_injective (f: E -> F) :=
  forall (x y : E), f x = f y -> x = y.

Definition is_surjective (f: E -> F) :=
  forall (y : F), exists (x : E), f x = y.

Definition is_bijective (f: E -> F) :=
           (is_injective f) /\ (is_surjective f).

End Inj_Surj_Bij.
