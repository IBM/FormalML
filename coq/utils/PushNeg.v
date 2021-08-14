Require Import Classical ClassicalFacts.
Require Import Reals.
Require Import micromega.Lra.

(*
****************************************************************************************
This file develops the tactic `push_neg` which pushes negations into nested quantifiers.
For example, if we have a hypothesis like this in the local context:

 (H : ~ (forall ϵ:posreal, exists δ:posreal, forall x, (Rabs(x - x0) <= δ)%R ->
                                             ((Rabs (f x - f x0))< ϵ)%R))

`push_neg_in H` transforms it to:

 (H : exists x : posreal,
        forall x1 : posreal,
        exists x2 : R, (Rabs (x2 - x0) <= x1)%R /\ (Rabs (f x2 - f x0) >= x)%R

****************************************************************************************
*)


Section rewrites.

  Lemma not_not (P : Prop): ~(~ P) <-> P.
  Proof.
    split; intros.
    + now apply NNPP.
    + firstorder.
  Qed.

  Lemma not_and (P Q:Prop) : ~(P /\ Q) <-> (P -> ~Q).
  Proof.
    firstorder.
  Qed.

  Lemma not_or (P Q:Prop) : ~(P \/ Q) <-> (~ P /\ ~ Q).
  Proof.
    firstorder.
  Qed.

  Lemma not_forall {A : Type} (S : A -> Prop): ~(forall x, S x) <-> exists x, ~ S x.
  Proof.
    split; intros.
    + now apply not_all_ex_not.
    + firstorder.
  Qed.

  Lemma not_exists {A : Type} (S : A -> Prop): ~(exists x, S x) <-> forall x, ~ S x.
  Proof.
    firstorder.
  Qed.

  Lemma not_imply : forall P Q:Prop, ~ (P -> Q) <-> P /\ ~ Q.
  Proof.
    intros P Q.
    split; intros.
    - now apply imply_to_and.
    - firstorder.
  Qed.

  Lemma not_lt (a b : R): ~ (a < b)%R <-> (a >= b)%R.
  Proof.
    lra.
  Qed.

  Lemma not_le (a b : R): ~ (a <= b)%R <-> (a > b)%R.
  Proof.
    lra.
  Qed.

  Lemma not_gt (a b : R): ~ (a > b)%R <-> (a <= b)%R.
  Proof.
    lra.
  Qed.

  Lemma not_ge (a b : R): ~ (a >= b)%R <-> (a < b)%R.
  Proof.
    lra.
  Qed.

  Lemma not_eq {A : Type} (a b : A) : ~(a = b) <-> a <> b.
  Proof.
    reflexivity.
  Qed.

End rewrites.

Ltac push_neg :=
  repeat match goal with
  | [ |- context[~ (_ < _)%R]] => setoid_rewrite not_lt
  | [ |- context[~ (_ <= _)%R]] => setoid_rewrite not_le
  | [ |- context[~ (_ > _)%R]] => setoid_rewrite not_gt
  | [ |- context[~ (_ >= _)%R]] => setoid_rewrite not_ge
  | [ |- context[~ (~ _)]] => setoid_rewrite not_not
  | [ |- context[~ (_ /\ _)]] => setoid_rewrite not_and
  | [ |- context[~(_ \/ _)]] => setoid_rewrite not_or
  | [ |- context[~(_ -> _)]] => setoid_rewrite not_imply
  | [ |- context[~(_ = _)]] => setoid_rewrite not_eq
  | [ |- context[~ exists _, _]] => setoid_rewrite not_exists
  | [ |- context[~ (forall _, _)]] => setoid_rewrite not_forall
  end.


Ltac push_neg_in H :=
  repeat match type of H with
  | context[~ (_ < _)%R] => setoid_rewrite not_lt in H
  | context[~ (_ <= _)%R] => setoid_rewrite not_le in H
  | context[~ (_ > _)%R] => setoid_rewrite not_gt in H
  | context[~ (_ >= _)%R] => setoid_rewrite not_ge in H
  | context[~ (~ _)] => setoid_rewrite not_not in H
  | context[~ (_ /\ _)] => setoid_rewrite not_and in H
  | context[~(_ \/ _)] => setoid_rewrite not_or in H
  | context[~(_ -> _)] => setoid_rewrite not_imply in H
  | context[~(_ = _)] => setoid_rewrite not_eq in H
  | context[~ exists _, _] => setoid_rewrite not_exists in H
  | context[~ (forall _, _)] => setoid_rewrite not_forall in H
  end.

Lemma tests1
      (p q : Prop)
      (P : nat -> Prop) (x y z : R)
      (H1 : ~ exists x : nat, P x)
      (H2 : ~ forall x : nat, P x)
      (H3 : ~ (x < y)%R)
      (H4 : ~ (x <= y)%R)
      (H5 : ~ (x > y)%R)
      (H6 : ~ (~ q))
      (H7 : ~ (p -> (p -> q)))
      (H8 : ~ (p /\ q))
      (H9 : ~ (p \/ q)): True.
Proof.
  push_neg_in H1.
  push_neg_in H2.
  push_neg_in H3.
  push_neg_in H4.
  push_neg_in H5.
  push_neg_in H6.
  push_neg_in H7.
  push_neg_in H8.
  push_neg_in H9.
  trivial.
Qed.

Lemma tests2 {x : nat -> R}
      (H1 : ~ exists x y : nat, forall z:nat, x = z \/ y = z)
      (H2 : ~ forall x y : nat, x = y /\ y = x)
      (H3 : ~(forall eps : R, exists N:nat, forall m n : nat, m >= N -> n >= N -> (Rabs (x n - x m)%R <= eps)%R))
  : True.
Proof.
  push_neg_in H1.
  push_neg_in H2.
  push_neg_in H3.
  trivial.
Qed.

Lemma test3 {f : R -> R}(x0 : R)
      (H : ~ (forall ϵ:posreal, exists δ:posreal, forall x, (Rabs(x - x0) <= δ)%R ->
                                             ((Rabs (f x - f x0))< ϵ)%R)) : True.
Proof.
  push_neg_in H.
  trivial.
Qed.
