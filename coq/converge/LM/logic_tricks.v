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

Require Import Decidable.
Require Import Arith.

(** Intuitionistic tricks for decidability *)

Section LT.

Lemma logic_not_not : forall Q, False <-> ((Q \/~Q) -> False).
split.
now intros H H'.
intros H'.
apply H'.
right.
intros H.
apply H'.
now left.
Qed.

Lemma logic_notex_forall (T : Type) :
  forall (P : T -> Prop) (x : T),
 (forall x, P x) -> (~ exists x, ~ P x).
Proof.
intros P x H.
intro H0.
destruct H0 as (t,H0).
apply H0.
apply H.
Qed.

Lemma logic_dec_notnot (T : Type) :
  forall P : T -> Prop, forall x : T,
    (decidable (P x)) -> (P x <-> ~~ P x).
Proof.
intros P x Dec.
split.
+ intro H.
  intuition.
+ intro H.
  unfold decidable in Dec.
  destruct Dec.
  trivial.
  exfalso.
  apply H.
  exact H0.
Qed.

Lemma decidable_ext: forall P Q, decidable P -> (P <->Q) -> decidable Q.
Proof.
intros P Q HP (H1,H2).
case HP; intros HP'.
left; now apply H1.
right; intros HQ.
now apply HP', H2.
Qed.

Lemma decidable_ext_aux: forall (T : Type), forall P1 P2 Q,
  decidable (exists w:T, P1 w  /\ Q w) ->
    (forall x, P1 x <-> P2 x) ->
      decidable (exists w, P2 w  /\ Q w).
Proof.
intros T P1 P2 Q H H1.
case H.
intros (w,(Hw1,Hw2)).
left; exists w; split; try assumption.
now apply H1.
intros H2; right; intros (w,(Hw1,Hw2)).
apply H2; exists w; split; try assumption.
now apply H1.
Qed.

Lemma decidable_and: forall (T : Type), forall P1 P2 (w : T),
   decidable (P1 w) -> decidable (P2 w) -> decidable (P1 w /\ P2 w).
Proof.
intros T P1 P2 w H1 H2.
unfold decidable.
destruct H1.
destruct H2.
left; intuition.
right.
intro.
now apply H0.
destruct H2.
right.
intro.
now apply H.
right.
intro.
now apply H.
Qed.

(** Strong induction *)

Theorem strong_induction:
 forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, ((k < n)%nat -> P k)) -> P n) ->
       forall n : nat, P n.
Proof.
intros P H n.
assert (forall k, (k < S n)%nat -> P k).
induction n.
intros k Hk.
replace k with 0%nat.
apply H.
intros m Hm; contradict Hm.
apply lt_n_0.
generalize Hk; case k; trivial.
intros m Hm; contradict Hm.
apply le_not_lt.
now auto with arith.
intros k Hk.
apply H.
intros m Hm.
apply IHn.
apply lt_le_trans with (1:=Hm).
now apply gt_S_le.
apply H0.
apply le_n.
Qed.

(** Equivalent definition for existence + uniqueness *)

Lemma unique_existence1: forall (A : Type) (P : A -> Prop),
     (exists x : A, P x) /\ uniqueness P -> (exists ! x : A, P x).
Proof.
intros A P.
apply unique_existence.
Qed.

End LT.
