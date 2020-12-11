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

(** AbelianGroup-compatibility *)

Section AboutCompatibleG.

Context {E : AbelianGroup}.

Definition compatible_g (P: E -> Prop) : Prop :=
   (forall (x y:E), P x -> P y -> P (plus x (opp y))) /\
      (exists (x:E), P x).

Lemma compatible_g_zero: forall P, compatible_g P -> P zero.
Proof.
intros P HP; destruct HP as (H1,(e,He)).
specialize (H1 e e).
rewrite plus_opp_r in H1.
now apply H1.
Qed.

Lemma compatible_g_opp: forall P x, compatible_g P
    -> P x -> P (opp x).
Proof.
intros P x HP Hx.
rewrite <- plus_zero_l.
apply HP; try assumption.
now apply compatible_g_zero.
Qed.

Lemma compatible_g_plus: forall P x y, compatible_g P
    -> P x -> P y -> P (plus x y).
Proof.
intros P x y HP Hx Hy.
rewrite <- (opp_opp y).
apply HP; try assumption.
now apply compatible_g_opp.
Qed.

End AboutCompatibleG.

(** ModuleSpace-compatibility *)

Section AboutCompatibleM.

Context {E : ModuleSpace R_Ring}.

Definition compatible_m (phi:E->Prop):=
  compatible_g phi /\
  (forall (x:E) (l:R), phi x -> phi (scal l x)).

Lemma compatible_m_zero: forall P, compatible_m P -> P zero.
Proof.
intros. destruct H.
apply (compatible_g_zero P); trivial.
Qed.

Lemma compatible_m_plus: forall P x y, compatible_m P
    -> P x -> P y -> P (plus x y).
Proof.
intros P x y Hp Hx Hy.
destruct Hp.
apply (compatible_g_plus P x y); trivial.
Qed.

Lemma compatible_m_scal: forall P a y, compatible_m P
    -> P y -> P (scal a y).
Proof.
intros P x y HP Hy.
apply HP; trivial.
Qed.

Lemma compatible_m_opp: forall P x, compatible_m P
    -> P x -> P (opp x).
Proof.
intros. destruct H.
apply (compatible_g_opp P); trivial.
Qed.

End AboutCompatibleM.

(** Sums and direct sums  *)

Section Compat_m.

Context {E : ModuleSpace R_Ring}.

Variable phi:E->Prop.
Variable phi':E->Prop.

Definition m_plus (phi phi':E -> Prop)
   := (fun (x:E) => exists u u', phi u -> phi' u' -> x=plus u u').

Hypothesis Cphi: compatible_m phi.
Hypothesis Cphi': compatible_m phi'.

Lemma compatible_m_plus2: compatible_m (m_plus phi phi').
unfold compatible_m in *; unfold compatible_g in *.
destruct Cphi as ((Cphi1,(a,Cphi2)),Cphi3).
destruct Cphi' as ((Cphi1',(a',Cphi2')),Cphi3').
unfold m_plus in *.
split.
split; intros. exists (plus x (opp y)). exists zero.
intros. rewrite plus_zero_r. reflexivity.
exists (plus a a'). exists a. exists a'. intros.
reflexivity.
intros. exists (scal l x). exists (scal zero x).
intros. rewrite <- scal_distr_r. rewrite plus_zero_r.
reflexivity.
Qed.

Definition direct_sumable := forall x, phi x -> phi' x -> x = zero.

Lemma direct_sum_eq1:
   direct_sumable ->
    (forall u u' , phi u -> phi' u' -> plus u u' = zero -> u=zero /\ u'=zero).
intros. split.
unfold compatible_m in *.
unfold compatible_g in *.
assert (u = opp u').
rewrite <- plus_opp_r with u' in H2.
rewrite plus_comm in H2.
apply plus_reg_l in H2.
trivial.
assert (phi' u).
rewrite H3 in H2.
rewrite H3.
rewrite <- scal_opp_one.
apply (proj2 Cphi'). trivial.
apply H; trivial.
assert (u' = opp u).
rewrite <- plus_opp_r with u in H2.
apply plus_reg_l in H2. trivial.
assert (phi u').
rewrite H3 in H2.
rewrite H3.
rewrite <- scal_opp_one.
apply (proj2 Cphi). trivial.
apply H; trivial.
Qed.

Lemma plus_u_opp_v : forall (u v : E), u = v <-> (plus u (opp v) = zero).
intros; split.
+ intros. rewrite H. rewrite plus_opp_r. reflexivity.
+ intros. apply plus_reg_r with (opp v). rewrite plus_opp_r; trivial.
Qed.

Lemma plus_assoc_gen : forall (a b c d : E),
     plus (plus a b) (plus c d) = plus (plus a c) (plus b d).
intros. rewrite plus_assoc. symmetry. rewrite plus_assoc.
assert (plus a (plus b c) = plus (plus a b) c).
apply plus_assoc.
assert (plus a (plus c b) = plus (plus a c) b).
apply plus_assoc.
rewrite <- H; rewrite <-H0.
rewrite (plus_comm c b). reflexivity.
Qed.

Lemma direct_sum_eq2:
  (forall u u' , phi u -> phi' u' -> plus u u' = zero -> u=zero /\ u'=zero) ->
   (forall u v u' v', phi u -> phi v -> phi' u' -> phi' v' -> plus u u' = plus v v' -> u=v /\ u'=v').
intros. unfold compatible_m in *; unfold compatible_g in *.
destruct Cphi as ((Cphi1,(x,Cphi2)),Cphi3).
destruct Cphi' as ((Cphi'1,(x',Cphi'2)),Cphi'3).
assert (plus (plus u (opp v)) (plus u' (opp v')) = zero).
rewrite plus_assoc_gen. rewrite H4.
rewrite plus_assoc_gen. rewrite plus_opp_r. rewrite plus_opp_r.
rewrite plus_zero_r. reflexivity.
rewrite plus_u_opp_v.
rewrite (plus_u_opp_v u' v').
apply H.
apply Cphi1; trivial.
apply Cphi'1; trivial.
trivial.
Qed.

Lemma direct_sum_eq3:
   (forall u v u' v', phi u -> phi v -> phi' u' -> phi' v' -> plus u u' = plus v v' -> u=v /\ u'=v')
     -> direct_sumable.
intros.
unfold compatible_m in *; unfold compatible_g in *; unfold direct_sumable.
intros.
destruct Cphi as ((Cphi1,(y,Cphi2)),Cphi3).
destruct Cphi' as ((Cphi'1,(y',Cphi'2)),Cphi'3).
apply (Cphi3 y zero) in Cphi2.
apply (Cphi'3 y' zero) in Cphi'2.
apply (Cphi'3 x (opp one)) in H1.
assert ((x = zero) /\ (opp x = zero)).
apply H. trivial. rewrite <- (scal_zero_l y). trivial.
rewrite <- scal_opp_one. trivial.
rewrite <- (scal_zero_l y'). trivial.
rewrite plus_opp_r.
rewrite plus_zero_l. reflexivity.
intuition.
Qed.

End Compat_m.
