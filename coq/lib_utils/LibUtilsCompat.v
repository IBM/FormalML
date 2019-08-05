(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(** This module defines a notion of compatibility between two
association lists. Two association lists are compatible if the values
for their common keys are equal. *)

Require Import List.
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Permutation.
Require Import Equivalence.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Orders.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import LibUtilsSortingAdd.
Require Import LibUtilsAssoc.

Section Compat.
  Context {A B:Type} `{EqDec A eq} `{EqDec B eq}.

  Definition compatible_with  {A B:Type} `{EqDec A eq} `{EqDec B eq} 
             (a:A) (b:B) (l₂:list (A * B)) : bool
    := match assoc_lookupr equiv_dec l₂ a with
       | Some d' => if equiv_dec b d' then true else false
       | None => true
       end.

  Definition compatible {A B:Type} `{EqDec A eq} `{EqDec B eq} (l₁ l₂:list (A * B)) : bool
    := forallb (fun xy => compatible_with (fst xy) (snd xy) l₂) l₁.

  Lemma compatible_nil_l (l:list (A * B))  : compatible nil l = true.
  Proof.
    reflexivity.
  Qed.

  Lemma compatible_nil_r (l:list (A * B))  : compatible l nil = true.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma compatible_with_cons_inv  {x:A} {y:B} {a l} :
    compatible_with x y (a :: l) = true ->
    compatible_with x y l = true.
  Proof.
    destruct a.
    unfold compatible_with; simpl; intros.
    match_case; intros.
    rewrite H2 in H1.
    trivial.
  Qed.

  Lemma compatible_cons_inv_r {a} {l1 l2:list (A*B)} :
    compatible l1 (a::l2) = true -> compatible l1 l2 = true.
  Proof.
    unfold compatible.
    repeat rewrite forallb_forall. intros.
    eapply compatible_with_cons_inv; eauto.
  Qed.

  Ltac case_eqdec :=
    match goal with 
    | [|- context [@equiv_dec ?a ?b ?c ?d ?x ?y]] =>
      let HH:=(fresh "eqs") in  case_eq (@equiv_dec a b c d x y); [intros ? HH|intros HH]; try rewrite HH
    | [H: context [@equiv_dec ?a ?b ?c ?d ?x ?y] |- _] => 
      let HH:=(fresh "eqs") in case_eq (@equiv_dec a b c d x y); [intros ? HH|intros HH]; try rewrite HH in H
    end; unfold equiv, complement in *; try subst.

  Lemma compatible_middle (l1 l2 l3:list (A * B)) a :
    compatible (l1 ++ a :: l2) l3 = compatible (a::l1++l2) l3.
  Proof.
    induction l1; simpl; trivial.
    rewrite IHl1. simpl.
    repeat rewrite andb_assoc.
    f_equal.
    rewrite andb_comm.
    auto.
  Qed.

  Lemma compatible_cons_r (l l':list (A * B)) a : 
    NoDup (domain l) ->
    compatible l l' = true ->
    compatible_with (fst a) (snd a) l = true ->
    compatible l (a :: l') = true.
  Proof.
    intros.
    apply forallb_forall.
    unfold compatible in *.
    rewrite forallb_forall in H2.
    intros.
    specialize (H2 _ H4).
    unfold compatible_with in *; simpl in *.
    destruct a as [y yv]; destruct x as [x xv]; simpl in *.
    repeat dest_eqdec; intuition.
    generalize H4.
    apply in_dom in H4.
    apply (@in_dom_lookupr A B l y equiv_dec) in H4.
    elim H4; clear H4; intros.
    unfold not in H4.
    rewrite H4 in H3.
    unfold not in *.
    destruct (@assoc_lookupr A B (@eq A) (fun x0 y0 : A => @eq A x0 y0 -> False)
                             (@equiv_dec A (@eq A) equiv0 H) l' y).
    destruct (equiv_dec xv b); congruence.
    revert H3.
    dest_eqdec; intuition.  
    apply assoc_lookupr_in in H4.
    assert (x = xv). apply (nodup_in_eq H1 H4 H5); eauto.
    rewrite H6. destruct (equiv_dec xv xv); congruence.
    destruct (@assoc_lookupr A B (@eq A) (fun x0 y0 : A => @eq A x0 y0 -> False)
                             (@equiv_dec A (@eq A) equiv0 H) l' x); congruence.
  Qed.

  Lemma compatible_perm_proper_l (l1 l2 l3:list (A * B)) :
    Permutation l1 l2 ->
    NoDup (domain l3) -> 
    compatible l1 l3 = true ->
    compatible l2 l3 = true.
  Proof.
    revert l2 l3. induction l1; simpl; intros.
    - apply Permutation_nil in H1. subst. simpl. trivial.
    - assert (inl:In a l2)
        by (apply (Permutation_in _ H1); simpl; intuition).
      destruct (in_split _ _ inl) as [l21 [l22 ?]]; subst.
      rewrite <- Permutation_middle in H1.
      apply Permutation_cons_inv in H1.
      rewrite andb_true_iff in H3; intuition.
      specialize (IHl1 _ _ H1 H2 H5).
      rewrite compatible_middle. simpl.
      rewrite H4, IHl1. simpl; trivial.
  Qed.

  Lemma compatible_refl (l:list (A * B)) : 
    NoDup (domain l) -> compatible l l = true.
  Proof.
    intros.
    induction l; try reflexivity.
    inversion H1; clear H1; subst.
    specialize (IHl H5).
    simpl.
    rewrite andb_true_inversion.
    split.
    - destruct a; simpl in *.
      unfold compatible_with.
      simpl.
      assert (assoc_lookupr equiv_dec l a = None) by
          (apply assoc_lookupr_nin_none; assumption).
      rewrite H1; simpl.
      destruct (equiv_dec a a); try congruence.
      destruct (equiv_dec b b); congruence.
    - apply compatible_cons_r; try assumption.
      destruct a; simpl in *.
      unfold compatible_with.
      assert (assoc_lookupr equiv_dec l a = None) by
          (apply assoc_lookupr_nin_none; assumption).
      rewrite H1; simpl.
      reflexivity.
  Qed.

  Lemma compatible_single_nin (b:list (A*B)) x d : 
    ~ In x (domain b) ->
    compatible b ((x, d) :: nil) = true.
  Proof.
    revert x d. induction b; simpl; trivial.
    destruct a; simpl. intuition.
    rewrite IHb; trivial.
    rewrite andb_true_iff; intuition.
    unfold compatible_with.
    simpl.
    destruct (equiv_dec a x); intuition.
  Qed.

  Lemma compatible_true_sym (l1 l2:list (A*B)) :
    NoDup (domain l2) -> compatible l1 l2 = true ->
    compatible l2 l1 = true.
  Proof.
    unfold compatible. repeat rewrite forallb_forall.
    intros.
    unfold compatible_with in *.
    match_case; intros.
    apply assoc_lookupr_in in H4.
    specialize (H2 _ H4); simpl in *.
    destruct x.
    rewrite (in_assoc_lookupr_nodup _ _ _ equiv_dec H1 H3) in H2.
    simpl. match_destr. match_destr_in H2. congruence.
  Qed.

  Lemma compatible_false_sym (l1 l2:list (A*B)) :
    NoDup (domain l1) -> compatible l1 l2 = false ->
    compatible l2 l1 = false.
  Proof.
    unfold compatible.
    repeat rewrite forallb_not_existb, negb_false_iff, existsb_exists.
    intros ? [?[??]].
    rewrite negb_true_iff in *.
    unfold compatible_with in H3.
    match_case_in H3; intros; rewrite H4 in H3; try discriminate.
    match_destr_in H3.
    destruct x; simpl in *.
    exists (a, b). split.
    - eapply assoc_lookupr_in; eauto.
    - simpl. rewrite negb_true_iff. unfold compatible_with.
      rewrite (in_assoc_lookupr_nodup _ _ _ equiv_dec H1 H2).
      match_destr.
      congruence.
  Qed.
  
  Lemma compatible_sym (l1 l2:list (A*B)) :
    NoDup (domain l1) -> NoDup (domain l2) ->
    compatible l1 l2 = compatible l2 l1.
  Proof.
    intros.
    case_eq (compatible l1 l2); intros.
    - symmetry. eapply compatible_true_sym; trivial.
    - symmetry. eapply compatible_false_sym; trivial.
  Qed.

  Lemma same_domain_compatible (l₁ l₂:list (A*B)) :
    NoDup (domain l₁) ->
    domain l₁ = domain l₂ ->
    compatible l₁ l₂ = true ->
    l₁ = l₂.
  Proof.
    intros nd eqq.
    rewrite eqq in nd.
    revert nd eqq.
    revert l₂.
    induction l₁; destruct l₂; simpl
    ; try discriminate; trivial.
    destruct a; destruct p; simpl.
    intros nd eqq; invcs nd; invcs eqq.
    rewrite andb_true_iff; intros [cw c].
    f_equal.
    - unfold compatible_with in cw.
      simpl in cw.
      rewrite (assoc_lookupr_nin_none l₂ a0 equiv_dec) in cw by trivial.
      destruct (equiv_dec a0 a0); [|congruence].
      match_destr_in cw.
      congruence.
    - apply compatible_cons_inv_r in c.
      auto.
  Qed.

End Compat.

