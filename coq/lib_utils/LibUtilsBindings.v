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

(** This module provides support for bindings, which are association
lists for which the keys are ordered and without duplicates.

Bindings are used as a representation for records and environments. *)


Require Import List.
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Permutation.
Require Import Equivalence.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Orders.
Require Import Permutation.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import LibUtilsSortingAdd.
Require Import LibUtilsAssoc.
Require Import LibUtilsSublist.
Require Import LibUtilsCompat.
Require Import String.
Require Import LibUtilsStringAdd.

Section Bindings.

  Class ODT {K:Type}
    := mkODT { ODT_eqdec:>EqDec K eq;
               ODT_lt:K -> K -> Prop;
               ODT_lt_strorder:>StrictOrder ODT_lt;
               ODT_lt_dec: forall (a b:K), {ODT_lt a b} + {~ODT_lt a b};
               ODT_compare:K -> K -> comparison;
               ODT_compare_spec: forall x y : K,
                   CompareSpec (eq x y) (ODT_lt x y) (ODT_lt y x) (ODT_compare x y) }.

  Generalizable Variables K.
  Context `{odt:@ODT K}.

  Lemma ODT_lt_irr (k:K) :
    ~(ODT_lt k k).
  Proof.
    apply irreflexivity.
  Qed.

  Ltac dest_strlt :=
    match goal with
    | [|- context [ODT_lt_dec ?x ?y]] => destruct (ODT_lt_dec x y); simpl
    | [H:ODT_lt ?x ?x|- _] => (assert False by (apply (ODT_lt_irr x); auto); contradiction)
    end.

  (* trichotemy *)
  Lemma trichotemy a b : {ODT_lt a b} + {eq a b} + {ODT_lt b a}.
  Proof.
    generalize (ODT_compare_spec a b); intros nc.
    destruct (ODT_compare a b); [left; right|left;left|right]; inversion nc; trivial.
  Defined.

  Lemma compare_refl_eq a: ODT_compare a a = Eq.
  Proof.
    destruct (ODT_compare_spec a a);[reflexivity|dest_strlt|dest_strlt].
  Qed.

  Lemma compare_eq_iff x y : (ODT_compare x y) = Eq <-> x=y.
  Proof.
    case ODT_compare_spec; intro H; split; try easy; intro EQ;
      contradict H;rewrite EQ; apply irreflexivity.
  Qed.
  
  Lemma ODT_lt_contr (x y : K) : ~ ODT_lt x y -> ~ ODT_lt y x -> x = y.
  Proof.
    destruct (trichotemy x y) as [[?|?]|?]; intuition.
  Qed.
  
  (* Starting here ... *)

  Definition rec_field_lt {A} (a b:K*A) :=
    ODT_lt (fst a) (fst b).

  Global Instance rec_field_lt_strict {A} : StrictOrder (@rec_field_lt A).
  Proof.
    unfold rec_field_lt.
    inversion odt.
    constructor.
    + unfold Irreflexive, Reflexive, complement in *; intros.
      destruct x; simpl in odt.
      apply (StrictOrder_Irreflexive k H).
    + unfold Transitive in *; intros.
      destruct x; destruct y; destruct z; simpl in *.
      apply (StrictOrder_Transitive k k0 k1 H H0).
  Qed.

  Lemma rec_field_lt_dec {A} (a b:K*A) :
    {rec_field_lt a b} + {~rec_field_lt a b}.
  Proof.
    destruct a.
    destruct b.
    unfold rec_field_lt; simpl.
    apply ODT_lt_dec.
  Defined.

  Lemma rec_field_lt_irr {A} (a:K*A) :
    ~(rec_field_lt a a).
  Proof.
    apply StrictOrder_Irreflexive.
  Qed.

  Lemma Forall_rec_field_lt {A} (a:K*A) l :
    Forall (rec_field_lt a) l <-> Forall (ODT_lt (fst a)) (domain l).
  Proof.
    destruct a; simpl.
    induction l; simpl.
    - intuition.
    - destruct IHl as [H1 H2].
      split; inversion 1; subst; constructor; eauto.
  Qed.
  
  Definition rec_cons_sort {A} :=
    @insertion_sort_insert (K*A) rec_field_lt rec_field_lt_dec.

  Definition rec_sort {A} :=
    @insertion_sort (K*A) rec_field_lt rec_field_lt_dec.

  Definition rec_concat_sort {A} (l1 l2:list (K*A)) : (list (K*A)) :=
    rec_sort (l1++l2).

  (* Lifted from LibUtilsSortingAdd *)
  
  Lemma sorted_rec_nil {A} :
    is_list_sorted ODT_lt_dec (@domain K A nil) = true.
  Proof.
    reflexivity.
  Qed.

  Lemma sort_rec_single_type {A} (k:K) (a:A):
    is_list_sorted ODT_lt_dec (domain ((k,a)::nil)) = true.
  Proof.
    reflexivity.
  Defined.

  Lemma field_less_is_neq (a1 a2:K) :
    ODT_lt a1 a2 -> a1 <> a2.
  Proof.
    unfold not; intros.
    subst; dest_strlt.
  Qed.
  
  Lemma field_less_is_not_more (a1 a2:K) :
    ODT_lt a1 a2 -> ~(ODT_lt a2 a1).
  Proof.
    elim ODT_lt_strorder; intros.
    unfold Transitive, Irreflexive, Reflexive, complement in *.
    unfold not; intros.
    specialize (StrictOrder_Transitive a1 a2 a1 H H0).
    specialize (StrictOrder_Irreflexive a1 StrictOrder_Transitive).
    assumption.
  Qed.

  Lemma field_not_less_and_neq_is_more (a1 a2:K) :
    ~(ODT_lt a1 a2) -> ~(eq a1 a2) -> ODT_lt a2 a1.
  Proof.
    unfold not; intros.
    generalize (ODT_compare_spec a1 a2).
    intros.
    inversion H1.
    congruence.
    assert False.
    apply H.
    assumption.
    contradiction.
    assumption.
  Qed.

  Lemma rec_cons_lt {A} (l1:list (K*A)) (a1 a2:K*A) :
    is_list_sorted ODT_lt_dec (domain (a2 :: l1)) = true ->
    ODT_lt (fst a1) (fst a2) ->
    is_list_sorted ODT_lt_dec (domain (a1 :: a2 :: l1)) = true.
  Proof.
    simpl; intros.
    revert H0; elim (ODT_lt_dec (fst a1) (fst a2)); intros.
    assumption.
    contradiction.
  Qed.

  Lemma rec_sorted_skip_first {A} (l1:list (K*A)) (a:K*A) :
    is_list_sorted ODT_lt_dec (domain (a :: l1)) = true ->
    is_list_sorted ODT_lt_dec (domain l1) = true.
  Proof.
    simpl.
    intros.
    revert H; elim (domain l1); intros.
    reflexivity.
    destruct (ODT_lt_dec (fst a) a0); congruence.
  Qed.    

  Lemma rec_sorted_skip_second {A} (l:list (K*A)) (a1 a2:K*A) :
    is_list_sorted ODT_lt_dec (domain (a1 :: a2 :: l)) = true ->
    is_list_sorted ODT_lt_dec (domain (a1 :: l)) = true.
  Proof.
    intros; simpl in *.
    revert H; destruct l; try reflexivity; simpl.
    elim (ODT_lt_dec (fst a1) (fst a2));
      elim (ODT_lt_dec (fst a2) (fst p));
      elim (ODT_lt_dec (fst a1) (fst p));
      intros; try congruence.
    assert (ODT_lt (fst a1) (fst p))
      by (apply transitivity with (y := (fst a2)); assumption).
    contradiction.
  Qed.

  Lemma rec_sorted_skip_third {A} (l:list (K*A)) (a1 a2 a3:K*A) :
    is_list_sorted ODT_lt_dec (domain (a1 :: a2 :: a3 :: l)) = true ->
    is_list_sorted ODT_lt_dec (domain (a1 :: a2 :: l)) = true.
  Proof.
    intros; simpl in *.
    revert H; destruct l; simpl.
    - simpl.
      elim (ODT_lt_dec (fst a1) (fst a2));
        elim (ODT_lt_dec (fst a2) (fst a3));
        elim (ODT_lt_dec (fst a1) (fst a3)); intros; try congruence.
    - elim (ODT_lt_dec (fst a1) (fst a2));
        elim (ODT_lt_dec (fst a2) (fst a3));
        elim (ODT_lt_dec (fst a3) (fst p));
        elim (ODT_lt_dec (fst a2) (fst p));
        intros; try congruence.
      assert (ODT_lt (fst a2) (fst p))
        by (apply transitivity with (y := (fst a3)); assumption).
      contradiction.
  Qed.

  Lemma rec_sorted_distinct {A} (l:list (K*A)) (a1 a2:K*A) :
    is_list_sorted ODT_lt_dec (domain (a1 :: a2 :: l)) = true ->
    (fst a1) <> (fst a2).
  Proof.
    intros.
    induction l.
    simpl in *.
    revert H.
    elim (ODT_lt_dec (fst a1) (fst a2)); intros.
    apply field_less_is_neq ; assumption.
    congruence.
    apply IHl; clear IHl.
    apply (rec_sorted_skip_third l a1 a2 a); assumption.
  Qed.

  Lemma rec_sorted_lt {A} (l:list (K*A)) (a1 a2:K*A) :
    is_list_sorted ODT_lt_dec (domain (a1 :: a2 :: l)) = true ->
    ODT_lt (fst a1) (fst a2).
  Proof.
    simpl.
    elim (ODT_lt_dec (fst a1) (fst a2)); intros.
    assumption.
    congruence.
  Qed.

  Lemma sorted_cons_in {A} (l:list (K*A)) (a a':K*A) :
    is_list_sorted ODT_lt_dec (domain (a :: l)) = true ->
    In a' l ->
    ODT_lt (fst a) (fst a').
  Proof.
    intros.
    induction l.
    - simpl in H0; contradiction.
    - simpl in H0.
      elim H0; clear H0; intros.
      + rewrite H0 in *; clear H0 a0.
        simpl in H.
        destruct (ODT_lt_dec (fst a) (fst a')); try congruence.
      + assert (is_list_sorted ODT_lt_dec (domain (a :: l)) = true)
          by (apply rec_sorted_skip_second with (a2 := a0); assumption).
        apply (IHl H1 H0).
  Qed.

  (* Back here... *)

  Lemma rec_cons_lt_first {A} (l1:list (K*A)) (a1 a2:K*A) :
    is_list_sorted ODT_lt_dec (domain (a2 :: l1)) = true ->
    ODT_lt (fst a1) (fst a2) ->
    rec_cons_sort a1 (a2 :: l1) = (a1 :: a2 :: l1).
  Proof.
    simpl; intros.
    elim (rec_field_lt_dec a1 a2); intros.
    reflexivity.
    unfold rec_field_lt in *.
    congruence.
  Qed.

  Lemma sort_sorted_is_id {A} (l:list (K*A)) :
    is_list_sorted ODT_lt_dec (domain l) = true ->
    rec_sort l = l.
  Proof.
    induction l; intros; simpl in *.
    reflexivity.
    assert (is_list_sorted ODT_lt_dec (domain l) = true).
    destruct l; simpl in *; try reflexivity.
    destruct (ODT_lt_dec (fst a) (fst p)); congruence.
    specialize (IHl H0).
    rewrite IHl; clear IHl.
    destruct l; simpl in *; try reflexivity.
    revert H.
    destruct (ODT_lt_dec (fst a) (fst p)); intros.
    destruct (rec_field_lt_dec a p); intros.
    reflexivity.
    unfold rec_field_lt in n.
    congruence.
    congruence.
  Qed.

  Lemma rec_concat_sort_concats {A} (l1 l2:list (K*A)) :
    rec_concat_sort l1 l2 = rec_sort (l1++l2).
  Proof.
    reflexivity.
  Qed.

  Lemma rec_cons_sorted_id {A} (l:list (K*A)) (a:K*A) :
    is_list_sorted ODT_lt_dec (domain (a :: l)) = true ->
    rec_cons_sort a l = a::l.
  Proof.
    intros.
    destruct l.
    reflexivity.
    assert (ODT_lt (fst a) (fst p))
      by (apply (rec_sorted_lt l a p); assumption).
    apply (rec_cons_lt_first l a p).
    apply (rec_sorted_skip_first (p::l) a); assumption.
    assumption.
  Qed.
  
  Lemma rec_sorted_id {A} (l:list (K*A)) :
    is_list_sorted ODT_lt_dec (domain l) = true ->
    rec_sort l = l.
  Proof.
    induction l.
    reflexivity.
    simpl; intros.
    assert (is_list_sorted ODT_lt_dec (domain l) = true).
    revert H.
    destruct l; try reflexivity.
    simpl.
    destruct (ODT_lt_dec (fst a) (fst p)); congruence.
    specialize (IHl H0); clear H0.
    rewrite IHl.
    simpl.
    assert (is_list_sorted ODT_lt_dec (domain (a :: l)) = true).
    unfold is_list_sorted.
    simpl.
    revert H.
    destruct l; try reflexivity.
    intros.
    simpl in *; revert H.
    destruct (ODT_lt_dec (fst a) (fst p)); intros.
    - revert H; destruct (domain l); try reflexivity.
      destruct (ODT_lt_dec (fst p) k); try congruence.
      intros.
      simpl in H.
      assumption.
    - congruence.
    - generalize (rec_cons_sorted_id l a H0); intros.
      unfold rec_cons_sort in H1.
      assumption.
  Qed.

  Lemma rec_cons_gt_first {A} (l' l:list (K*A)) (a1 a2:K*A) :
    rec_cons_sort a1 l = l' ->
    is_list_sorted ODT_lt_dec (domain (a2 :: l)) = true ->
    ODT_lt (fst a2) (fst a1) ->
    (exists a3, exists l'', rec_cons_sort a1 l = (a3 :: l'')
                            /\ ODT_lt (fst a2) (fst a3)).
  Proof.
    revert a1 a2 l'.
    induction l; intros.
    - simpl in *; intros; exists a1, nil; split; [reflexivity|assumption].
    - simpl in *.
      revert H; elim (rec_field_lt_dec a1 a); intros.
      inversion H.
      exists a1,(a::l).
      split; [reflexivity|assumption].
      revert H; elim (rec_field_lt_dec a a1); intros.
      destruct l'; try congruence.
      rewrite H in *.
      exists p,l'.
      + split; try reflexivity.
        inversion H.
        rewrite <- H3 in *; clear H3.
        revert H0.
        elim (ODT_lt_dec (fst a2) (fst a)); intros.
        assumption.
        congruence.
      + exists a,l.
        split. reflexivity.
        revert H0.
        elim (ODT_lt_dec (fst a2) (fst a)); intros.
        assumption.
        congruence.
  Qed.

  Lemma rec_cons_sorted {A} (l1 l2:list (K*A)) (a:K*A) :
    is_list_sorted ODT_lt_dec (domain l1) = true ->
    rec_cons_sort a l1 = l2 ->
    is_list_sorted ODT_lt_dec (domain l2) = true.
  Proof.
    revert l2 a.
    induction l1; intros.
    simpl in *; rewrite <- H0; reflexivity.
    simpl in *.
    assert (is_list_sorted ODT_lt_dec (domain (a::l1)) = true)
      by assumption.
    revert H0.
    elim (rec_field_lt_dec a0 a); intros.
    rewrite <- H0.
    apply rec_cons_lt; assumption.
    rewrite <- H0.
    destruct (rec_field_lt_dec a a0); intros. clear b.
    - assert (exists a3, exists l'', rec_cons_sort a0 l1 = (a3 :: l'')
                                     /\ ODT_lt (fst a) (fst a3)).
      apply (rec_cons_gt_first (rec_cons_sort a0 l1) l1).
      reflexivity.
      assumption.
      assumption.
      elim H2; clear H2; intros.
      elim H2; clear H2; intros.
      elim H2; clear H2; intros.
      destruct l2; try congruence.
      inversion H0.
      rewrite <- H5 in *; clear H5.
      specialize (IHl1 l2 a0).
      assert (is_list_sorted ODT_lt_dec (domain l1) = true).
      apply (rec_sorted_skip_first l1 a); assumption.
      specialize (IHl1 H4 H6).
      rewrite H2 in *.
      rewrite <- H6 in *.
      apply rec_cons_lt; assumption.
    - assumption.
  Qed.

  Lemma rec_sort_sorted {A} (l1 l2:list (K*A)) :
    rec_sort l1 = l2 -> is_list_sorted ODT_lt_dec (domain l2) = true.
  Proof.
    revert l2.
    induction l1; intros.
    simpl; inversion H; reflexivity.
    simpl in *.
    assert (exists l'', rec_sort l1 = l'').
    revert H.
    elim (rec_sort l1); intros.
    exists nil; reflexivity.
    exists (a0::l); reflexivity.
    elim H0; intros; clear H0.
    rewrite H1 in H.
    assert (is_list_sorted ODT_lt_dec (domain x) = true).
    apply (IHl1 x H1); assumption.
    apply (rec_cons_sorted x l2 a); assumption.
  Qed.

  Lemma rec_sort_pf {A} {l1: list (K*A)} :
    is_list_sorted ODT_lt_dec (domain (rec_sort l1)) = true.
  Proof.
    exact (rec_sort_sorted _ _ (eq_refl _)).
  Qed.
  
  Lemma rec_concat_sort_sorted {A} (l1 l2 x:list (K*A)) :
    rec_concat_sort l1 l2 = x ->
    is_list_sorted ODT_lt_dec (domain x) = true.
  Proof.
    intros.
    assert (rec_sort (l1++l2) = x).
    rewrite <- rec_concat_sort_concats; assumption.
    apply (rec_sort_sorted (l1++l2) x); assumption.
  Qed.

  Lemma same_domain_same_sorted {A} {B} (l1:list (K*A)) (l2:list (K*B)) :
    domain l1 = domain l2 ->
    is_list_sorted ODT_lt_dec (domain l1) = true ->
    is_list_sorted ODT_lt_dec (domain l2) = true.
  Proof.
    intros.
    rewrite <- H; assumption.
  Qed.

  Lemma same_domain_insert {A} {B}
        (l1:list (K*A)) (l2:list (K*B))
        (a:K*A) (b:K*B):
    domain l1 = domain l2 ->
    fst a = fst b ->
    domain (rec_cons_sort a l1) = domain (rec_cons_sort b l2).
  Proof.
    intros.
    revert l2 H.
    induction l1.
    induction l2; simpl in *; congruence.
    intros; simpl in *.    
    induction l2; simpl in *; try congruence.
    clear IHl2.
    inversion H.
    elim (rec_field_lt_dec a a0); intros.
    elim (rec_field_lt_dec b a1); intros.
    simpl.
    rewrite H2; rewrite H0; rewrite H3; reflexivity.
    unfold rec_field_lt in *.
    destruct a; destruct a0; destruct b; destruct a1; simpl in *.
    subst. congruence.
    unfold rec_field_lt in *.
    destruct a; destruct a0; destruct b; destruct a1; simpl in *.
    subst.
    inversion H.
    destruct (ODT_lt_dec k1 k2); try congruence.
    destruct (ODT_lt_dec k2 k1); try congruence; simpl.
    - rewrite (IHl1 l2 H1); reflexivity.
    - rewrite H1; reflexivity.
  Qed.

  Lemma same_domain_rec_sort {A} {B}
        (l1:list (K*A)) (l2:list (K*B)) :
    domain l1 = domain l2 ->
    domain (rec_sort l1) = domain (rec_sort l2).
  Proof.
    revert l2; induction l1; simpl; intros.
    - symmetry in H; apply domain_nil in H; subst; simpl; trivial.
    - destruct l2; simpl in *; try discriminate.
      inversion H.
      fold (@rec_cons_sort A).
      fold (@rec_cons_sort B).
      apply same_domain_insert; auto.
  Qed.

  Lemma insertion_sort_insert_nin_perm {A:Type} l a :
    ~ In (fst a) (@domain _ A l) ->
    Permutation (a::l) (insertion_sort_insert rec_field_lt_dec a l).
  Proof.
    induction l; simpl; auto.
    intuition.
    destruct (rec_field_lt_dec a a0); trivial.
    generalize (field_not_less_and_neq_is_more _ _ n).
    destruct (rec_field_lt_dec a0 a); intuition.
    rewrite perm_swap.
    rewrite Permutation_cons; try eassumption; trivial.
  Qed.

  Lemma insertion_sort_perm_proper {A:Type} (l l':list (K*A)) a :
    ~ In (fst a) (domain l) ->
    Permutation l l' ->
    Permutation
      (insertion_sort_insert rec_field_lt_dec a l)
      (insertion_sort_insert rec_field_lt_dec a l').
  Proof.
    revert l l'.
    induction l; simpl; intros.
    - apply Permutation_nil in H0; subst; auto.
    - assert (inl:In a0 l')
        by (apply (Permutation_in _ H0); simpl; intuition).
      destruct (in_split _ _ inl) as [l1 [l2 ?]]; subst.
      rewrite <- Permutation_middle in H0.
      apply Permutation_cons_inv in H0.
      intuition.
      destruct (rec_field_lt_dec a a0).
      + rewrite H0.
        rewrite <- insertion_sort_insert_nin_perm.
        * apply Permutation_cons; trivial.
          apply Permutation_middle.
        * intros nin.
          apply (@Permutation_in _ (domain (l1 ++ a0 :: l2)) (domain (a0::l))) in nin.
          simpl in nin; intuition.
          apply dom_perm. rewrite <- Permutation_middle.
          rewrite H0; trivial.
      + assert (rec_field_lt a0 a)
          by (apply field_not_less_and_neq_is_more; auto).
        destruct (rec_field_lt_dec a0 a); intuition.
        rewrite (IHl _ H2 H0).
        assert (nin:~ In (fst a) (domain l1)).
        intro nin; apply H2.
        eapply Permutation_in; [apply dom_perm;symmetry;apply H0|]. 
        unfold domain; rewrite map_app; apply in_or_app; intuition.
        revert H1 n H nin. clear. revert l2 a a0.
        induction l1; simpl; intros.
        * destruct (rec_field_lt_dec a a0); intuition.
          destruct (rec_field_lt_dec a0 a); intuition.
        * intuition.
          destruct (rec_field_lt_dec a0 a); intuition.
          rewrite perm_swap. apply Permutation_cons; trivial.
          rewrite perm_swap. apply Permutation_cons; trivial.
          apply Permutation_middle.
          assert (rec_field_lt a a0)
            by (apply field_not_less_and_neq_is_more; auto).
          destruct (rec_field_lt_dec a a0); intuition.
          rewrite perm_swap.
          rewrite IHl1; auto.
  Qed.

  Lemma rec_sort_perm  {A:Type} l :
    NoDup (@domain _ A l) -> Permutation l (rec_sort l).
  Proof.
    induction l; simpl; auto.
    inversion 1; subst.
    rewrite insertion_sort_perm_proper; [| |symmetry; auto].
    apply insertion_sort_insert_nin_perm; trivial.
    intros nin; apply H2.
    eapply Permutation_in; [|eapply nin].
    symmetry. apply dom_perm.
    auto.
  Qed.

  Lemma insertion_sort_insert_insertion_nin {A} (a:K*A) a0 l : 
    ~ rec_field_lt a0 a ->
    ~ rec_field_lt a a0 ->
    insertion_sort_insert rec_field_lt_dec a0
                          (insertion_sort_insert rec_field_lt_dec a l)
    = insertion_sort_insert rec_field_lt_dec a l.
  Proof.
    revert a a0. induction l; simpl; intros.
    - destruct (rec_field_lt_dec a0 a); intuition.
      destruct (rec_field_lt_dec a a0); intuition.
    - destruct (rec_field_lt_dec a0 a); intuition.
      + simpl.
        destruct (rec_field_lt_dec a1 a0); intuition.
        destruct (rec_field_lt_dec a0 a1); intuition.
      + destruct (rec_field_lt_dec a a0); simpl.
        * destruct (rec_field_lt_dec a1 a).
          rewrite r in r0; intuition.
          destruct (rec_field_lt_dec a a1); trivial.
          f_equal; eauto.
        * (* we crucially need trichotomy *)
          destruct (trichotemy (fst a0) (fst a1)) as [[?|?]|?]; intuition.
          destruct (trichotemy (fst a) (fst a0)) as [[?|?]|?]; intuition.
          destruct a0; destruct a1; destruct a; simpl in *.
          subst.
          destruct (ODT_lt_dec k0 k0); try congruence.
          assert False by (apply (ODT_lt_irr k0); auto).
          contradiction.
  Qed.

  Lemma insertion_sort_insert_cons_app {A} (a:K*A) l l2 :
    insertion_sort rec_field_lt_dec (insertion_sort_insert rec_field_lt_dec a l ++ l2) = insertion_sort rec_field_lt_dec (a::l ++ l2).
  Proof.
    revert a l2.
    induction l; simpl; trivial; intros.
    destruct (rec_field_lt_dec a0 a); simpl; trivial.
    destruct (rec_field_lt_dec a a0); simpl; trivial.
    - rewrite IHl; simpl. apply insertion_sort_insert_swap; eauto.
      apply rec_field_lt_strict.
    - rewrite insertion_sort_insert_insertion_nin; eauto.
  Qed.

  Lemma insertion_sort_insertion_sort_app1 {A} l1 l2 :
    insertion_sort rec_field_lt_dec (insertion_sort (@rec_field_lt_dec A) l1 ++ l2) =
    insertion_sort rec_field_lt_dec (l1 ++ l2).
  Proof.
    revert l2.
    induction l1; simpl; trivial; intros.
    rewrite insertion_sort_insert_cons_app.
    simpl.
    rewrite IHl1.
    trivial.
  Qed.

  Lemma insertion_sort_insertion_sort_app {A} l1 l2 l3 :
    insertion_sort rec_field_lt_dec (l1 ++ insertion_sort (@rec_field_lt_dec A) l2 ++ l3) =
    insertion_sort rec_field_lt_dec (l1 ++ l2 ++ l3).
  Proof.
    induction l1; simpl.
    - apply insertion_sort_insertion_sort_app1.
    - rewrite IHl1; trivial.
  Qed.

  Lemma insertion_sort_eq_app1 {A l1 l1'} l2 :
    insertion_sort (@rec_field_lt_dec A) l1 = insertion_sort rec_field_lt_dec l1' -> 
    insertion_sort rec_field_lt_dec (l1 ++ l2) =
    insertion_sort rec_field_lt_dec (l1' ++ l2).
  Proof.
    intros.
    rewrite <- (insertion_sort_insertion_sort_app1 l1 l2).
    rewrite <- (insertion_sort_insertion_sort_app1 l1' l2).
    rewrite H.
    trivial.
  Qed.

  Lemma rec_sort_rec_sort_app1 {A} l1 l2 :
    rec_sort ((@rec_sort A) l1 ++ l2) =
    rec_sort (l1 ++ l2).
  Proof.
    apply insertion_sort_insertion_sort_app1.
  Qed.

  Lemma rec_sort_rec_sort_app {A} l1 l2 l3 :
    rec_sort (l1 ++ (@rec_sort A) l2 ++ l3) =
    rec_sort (l1 ++ l2 ++ l3).
  Proof.
    apply insertion_sort_insertion_sort_app.
  Qed.

  Lemma rec_sort_rec_sort_app2 {A} l1 l2 :
    rec_sort (l1 ++ (@rec_sort A) l2) =
    rec_sort (l1 ++ l2).
  Proof.
    generalize (rec_sort_rec_sort_app l1 l2 nil).
    repeat rewrite app_nil_r.
    trivial.
  Qed.

  Lemma rec_sort_eq_app1  {A l1 l1'} l2 :
    (@rec_sort A) l1 = rec_sort l1' ->
    rec_sort (l1 ++ l2) =
    rec_sort (l1' ++ l2).
  Proof.
    apply insertion_sort_eq_app1.
  Qed.

  Lemma rec_cons_sort_Forall2 {A B} P l1 l2 a b :
    Forall2 P l1 l2 ->
    P a b ->
    (domain l1) = (domain l2) ->
    fst a = fst b ->
    Forall2 P 
            (insertion_sort_insert (@rec_field_lt_dec A) a l1)
            (insertion_sort_insert (@rec_field_lt_dec B) b l2).
  Proof.
    revert a b l2; induction l1; simpl; inversion 1; intros; subst; simpl; [eauto|].
    destruct (rec_field_lt_dec a0 a); 
      destruct (rec_field_lt_dec b y); 
      unfold rec_field_lt in *; rewrite H7 in *;
        simpl in *; inversion H6; rewrite H1 in *; intuition.
    destruct (rec_field_lt_dec a a0);  unfold rec_field_lt in *;
      rewrite H7,H1 in *;
      destruct (rec_field_lt_dec y b);  unfold rec_field_lt in *; intuition.
  Qed.

  Lemma rec_sort_Forall2 {A B} P l1 l2 :
    (domain l1) = (domain l2) ->
    Forall2 P l1 l2 ->
    Forall2 P (@rec_sort A l1) (@rec_sort B l2).
  Proof.
    Hint Constructors Forall2.
    revert l2; induction l1; simpl; inversion 2; subst; eauto.
    simpl in *; inversion H.
    apply rec_cons_sort_Forall2; auto.
    apply same_domain_rec_sort; auto.
  Qed.

  Lemma rec_concat_sort_nil_r {A} g :
    @rec_concat_sort A g nil = rec_sort g.
  Proof.
    unfold rec_concat_sort. rewrite app_nil_r. trivial.
  Qed.

  Lemma rec_concat_sort_nil_l {A} g :
    @rec_concat_sort A nil g = rec_sort g.
  Proof.
    unfold rec_concat_sort. simpl. trivial.
  Qed.

  Lemma drec_sort_idempotent {A} l : @rec_sort A (rec_sort l) = rec_sort l.
  Proof.
    apply rec_sorted_id.
    eapply rec_sort_sorted; eauto.
  Qed.

  Lemma insertion_sort_insert_equiv_domain {A:Type} x a (l:list (K*A)) :
    In x
       (domain (LibUtilsSortingAdd.insertion_sort_insert rec_field_lt_dec a l)) <->
    fst a = x \/ In x (domain l).
  Proof.
    induction l; simpl; [intuition|].
    destruct a; destruct a0; simpl in *.
    destruct (ODT_lt_dec k k0); simpl; [intuition|].
    destruct (ODT_lt_dec k0 k); simpl; intuition. subst; clear H.
    destruct (trichotemy x k0); intuition.
  Qed.

  Lemma drec_sort_equiv_domain {A} l : 
    equivlist (domain (@rec_sort A l)) (domain l).
  Proof.
    unfold equivlist.
    induction l; simpl; [intuition|]; intros x.
    rewrite <- IHl. apply insertion_sort_insert_equiv_domain.
  Qed.

  Hint Resolve ODT_lt_strorder.
  
  Lemma insertion_sort_insert_swap_neq {A} a1 (b1:A) a2 b2 l :
    ~(eq a1 a2) ->
    insertion_sort_insert rec_field_lt_dec (a1, b1)
                          (insertion_sort_insert rec_field_lt_dec 
                                                 (a2, b2) l) =
    insertion_sort_insert rec_field_lt_dec (a2, b2)
                          (insertion_sort_insert rec_field_lt_dec 
                                                 (a1, b1) l).
  Proof.
    revert a1 b1 a2 b2. induction l; simpl; intros.
    - destruct (ODT_lt_dec a1 a2); 
        destruct (ODT_lt_dec a2 a1); trivial.
      + eelim @asymmetry; eauto.
        unfold Asymmetric; intros.
        apply (@asymmetry _ _ _ x y); assumption.
      + destruct (trichotemy a1 a2) as [[?|?]|?];
          intuition.
    - destruct a; simpl.
      Ltac t := try (solve[eelim @asymmetry; eauto]); intuition.
      repeat dest_strlt; 
        intuition;
        try solve[
              rewrite o0 in *; t
            | destruct (trichotemy a1 a2) as [[?|?]|?]; intuition].
      rewrite o0 in o2.
      dest_strlt.
      rewrite IHl; [reflexivity|assumption].
  Qed.

  Lemma insertion_sort_insert_middle {A} l1 l2 a (b:A) :
    ~ In a (domain l1) ->
    LibUtilsSortingAdd.insertion_sort_insert rec_field_lt_dec (a, b)
                                     (LibUtilsSortingAdd.insertion_sort rec_field_lt_dec (l1 ++ l2)) =
    LibUtilsSortingAdd.insertion_sort rec_field_lt_dec (l1 ++ (a, b) :: l2).
  Proof.
    revert l2 a b.
    induction l1; simpl; trivial; intros.
    intuition.
    rewrite <- IHl1; auto.
    destruct a; simpl in *.
    apply insertion_sort_insert_swap_neq; auto.
  Qed.

  Lemma drec_sort_perm_eq {A} l l' :
    NoDup (@domain _ A l) ->
    Permutation l l' -> 
    rec_sort l = rec_sort l'.
  Proof.
    unfold rec_sort.
    revert l'. induction l; simpl; intros.
    - apply Permutation_nil in H0; subst; simpl; trivial.
    - inversion H; subst.
      destruct a as [a b].
      assert (inl:In (a,b) l')
        by (apply (Permutation_in _ H0); simpl; intuition).
      destruct (in_split _ _ inl) as [l1 [l2 ?]]; subst.
      rewrite <- Permutation_middle in H0.
      apply Permutation_cons_inv in H0.
      inversion H; subst.
      rewrite (IHl (l1 ++ l2)); auto.
      apply insertion_sort_insert_middle.
      intros nin; apply H5.
      apply dom_perm in H0.
      symmetry in H0.
      eapply Permutation_in; try eapply H0.
      rewrite domain_app, in_app_iff.
      intuition.
  Qed.

  Lemma drec_sorted_perm_eq {A : Type} (l l' : list (K * A)) :
    is_list_sorted ODT_lt_dec (domain l) = true ->
    is_list_sorted ODT_lt_dec (domain l') = true ->
    Permutation l l' ->
    l = l'.
  Proof.
    intros.
    assert (rec_sort l = rec_sort l').
    - apply drec_sort_perm_eq; trivial.
      apply (is_list_sorted_NoDup ODT_lt_dec); trivial.
    - repeat rewrite sort_sorted_is_id in H2 by trivial.
      trivial.
  Qed.
  
  Lemma drec_concat_sort_app_comm {A} l l': 
    NoDup (@domain _ A (l ++l')) ->
    rec_concat_sort l l' = rec_concat_sort l' l.
  Proof.
    intros.
    unfold rec_concat_sort.
    apply drec_sort_perm_eq; auto.
    apply Permutation_app_comm.
  Qed.

  Lemma in_dom_rec_sort {B} {l x}:
    In x (domain (rec_sort l)) <-> In x (@domain _ B l).
  Proof.
    intros.
    apply  drec_sort_equiv_domain; trivial.
  Qed.

  Lemma drec_sort_sorted {A} l :
    LibUtilsSortingAdd.is_list_sorted ODT_lt_dec
                              (@domain _ A
                                       (rec_sort l)) = true.
  Proof.
    eapply rec_sort_sorted; eauto.
  Qed.

  Lemma drec_concat_sort_sorted {A} l l' :
    LibUtilsSortingAdd.is_list_sorted ODT_lt_dec
                              (@domain _ A
                                       (rec_concat_sort l l')) = true.
  Proof.
    unfold rec_concat_sort.
    eapply rec_sort_sorted; eauto.
  Qed.

  Lemma drec_sort_drec_sort_concat {A} l l' :
    (rec_sort (@rec_concat_sort A l l')) = rec_concat_sort l l'.
  Proof.
    unfold rec_sort, rec_concat_sort.
    apply insertion_sort_idempotent.
  Qed.

  Lemma assoc_lookupr_insertion_sort_insert_neq {B:Type} a x (b:B) l :
    ~(eq x a)->
    assoc_lookupr ODT_eqdec 
                  (LibUtilsSortingAdd.insertion_sort_insert rec_field_lt_dec (a, b) l)
                  x 
    = assoc_lookupr ODT_eqdec l x.
  Proof.
    revert a x b.
    induction l; simpl; intros.
    - destruct (ODT_eqdec x a); intuition.
    - destruct a; simpl.
      destruct (ODT_lt_dec a0 k);
        destruct (ODT_lt_dec k a0); simpl.
      + destruct (assoc_lookupr ODT_eqdec l x); trivial.
        destruct (ODT_eqdec x k); trivial.
        destruct (ODT_eqdec x a0); intuition.
      + destruct (assoc_lookupr ODT_eqdec l x); trivial.
        destruct (ODT_eqdec x k); trivial.
        destruct (ODT_eqdec x a0); intuition.
      + rewrite IHl; trivial.
      + destruct (trichotemy a0 k); intuition.
  Qed.

  Lemma assoc_lookupr_insertion_sort_fresh {B:Type} x (d:B) b :
    ~ In x (domain b) ->
    assoc_lookupr ODT_eqdec
                  (LibUtilsSortingAdd.insertion_sort rec_field_lt_dec (b ++ (x, d) :: nil)) x = 
    Some d.
  Proof.
    revert x d.
    induction b; simpl; intuition.
    - destruct (ODT_eqdec x x); intuition.
    - rewrite assoc_lookupr_insertion_sort_insert_neq; auto.
  Qed.

  Lemma is_list_sorted_NoDup_strlt {A} l :
    is_list_sorted ODT_lt_dec (@domain _ A l) = true ->
    NoDup (domain l).
  Proof.
    eapply is_list_sorted_NoDup.
    eapply ODT_lt_strorder.
  Qed.

  Lemma rec_sort_self_cons_middle {A} (l:list (K*A)) (a:K*A):
    is_list_sorted ODT_lt_dec (domain (a::l)) = true ->
    rec_sort (l ++ a :: l) = rec_sort ((a :: l) ++ l).
  Proof.
    unfold rec_sort; intros.
    assert (l ++ a :: l = (l++(a::nil))++l) by apply app_cons_middle.
    rewrite H0.
    apply insertion_sort_eq_app1.
    generalize (drec_sort_perm_eq (a :: l) (l++(a::nil))); intros.
    unfold rec_sort in H1.
    rewrite H1; try reflexivity.
    apply is_list_sorted_NoDup_strlt; assumption.
    rewrite Permutation_app_comm.
    simpl.
    reflexivity.
  Qed.

  Lemma rec_field_anti {A} a:
    ~ (@rec_field_lt A) a a.
  Proof.
    generalize ODT_lt_strorder; intros.
    unfold Irreflexive, Reflexive, complement in *.
    destruct a; unfold rec_field_lt; simpl.
    inversion H. apply StrictOrder_Irreflexive.
  Qed.

  Lemma lt_not_not k1 k2:
    ~ODT_lt k1 k2 -> ~ODT_lt k2 k1 -> eq k1 k2.
  Proof.
    unfold not; intros.
    generalize (trichotemy k1 k2); intros.
    inversion H1.
    elim H2; intros.
    congruence.
    assumption.
    congruence.
  Qed.
  
  Lemma rec_concat_sort_self {A} (l:list (K*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    rec_concat_sort l l = l.
  Proof.
    intros.
    induction l; try reflexivity.
    unfold rec_concat_sort.
    assert (is_list_sorted ODT_lt_dec (domain l) = true)
      by (apply (rec_sorted_skip_first l a); assumption).
    specialize (IHl H0).
    simpl.
    rewrite rec_sort_self_cons_middle; try assumption.
    simpl.
    unfold rec_concat_sort in IHl.
    rewrite IHl.
    simpl.
    rewrite insertion_sort_insert_insertion_nin.
    generalize (rec_sorted_id (a :: l) H); intros.
    simpl in H1.
    assert (rec_sort l = l). apply rec_sorted_id; assumption.
    rewrite H2 in H1; assumption.
    apply rec_field_anti.
    apply rec_field_anti.
  Qed.

  Lemma insert_first_into_app {A} (l l0:list (K*A)) (a:K*A):
    is_list_sorted ODT_lt_dec (domain (a :: l)) = true ->
    rec_sort (l ++ insertion_sort_insert rec_field_lt_dec a (rec_sort (l ++ l0))) =
    insertion_sort_insert rec_field_lt_dec a (rec_sort (l ++ rec_sort (l ++ l0))).
  Proof.
    intros.
    assert (NoDup (domain (a::l))) by (apply is_list_sorted_NoDup_strlt; assumption).
    inversion H0; subst.
    assert (is_list_sorted ODT_lt_dec (domain l) = true)
      by (apply (rec_sorted_skip_first l a); assumption).
    assert (is_list_sorted ODT_lt_dec (domain (rec_sort (l++l0))) = true).
    apply (rec_sort_sorted (l++l0)); reflexivity.
    revert H3.
    generalize (rec_sort (l++l0)); intros.    
    generalize (@rec_cons_sorted_id A l a H); intros.
    generalize (@insertion_sort_insert_middle A l l1 (fst a) (snd a) H3); intros.
    destruct a; simpl in *.
    unfold rec_sort.
    rewrite H6.
    clear H5 H6 H H0 H3 H4 H1 H2.
    induction l.
    simpl.
    generalize (insertion_sort_insert_cons_app (k, a) l1 nil); intros.
    repeat rewrite app_nil_r in H.
    rewrite H; reflexivity.
    simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma rec_concat_sort_idem {A} (l l0:list (K*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    is_list_sorted ODT_lt_dec (domain l0) = true ->
    rec_concat_sort l (rec_concat_sort l l0) = rec_concat_sort l l0.
  Proof.
    intros.
    assert (NoDup (domain l)) by (apply is_list_sorted_NoDup_strlt; assumption).
    assert (NoDup (domain l0)) by (apply is_list_sorted_NoDup_strlt; assumption).
    unfold rec_concat_sort.
    induction l; simpl.
    - rewrite drec_sort_idempotent; reflexivity.
    - assert (is_list_sorted ODT_lt_dec (domain l) = true)
        by (apply (rec_sorted_skip_first l a); assumption).
      inversion H1; subst.
      specialize (IHl H3 H7).
      assert ((rec_sort
                 (l ++ insertion_sort_insert rec_field_lt_dec a (rec_sort (l ++ l0))))
              =
              insertion_sort_insert rec_field_lt_dec a ((rec_sort (l ++ rec_sort (l ++ l0))))).
      apply insert_first_into_app; assumption.
      rewrite H4.
      rewrite insertion_sort_insert_insertion_nin.
      rewrite IHl.
      reflexivity.
      apply rec_field_anti.
      apply rec_field_anti.
  Qed.

  Instance In_equivlist_proper {A}:
    Proper (eq ==> equivlist ==> iff) (@In A).
  Proof.
    unfold Proper, respectful, equivlist; intros; subst; trivial.
  Qed.

  Lemma assoc_lookupr_insert B s (d:B) l x :
    assoc_lookupr ODT_eqdec  
                  (LibUtilsSortingAdd.insertion_sort_insert rec_field_lt_dec (s, d) l) x =
    match assoc_lookupr ODT_eqdec l x with
    | Some d' => Some d'
    | None => if ODT_eqdec x s then Some d else None
    end.
  Proof.
    revert s d x. induction l; simpl; trivial; intros.
    destruct a.
    destruct (ODT_lt_dec s k); simpl; trivial.
    destruct (ODT_lt_dec k s); simpl; trivial.
    - rewrite IHl; simpl.
      destruct (assoc_lookupr ODT_eqdec l); trivial.
      destruct (ODT_eqdec x s).
      + subst. destruct (ODT_eqdec x k); intuition.
        rewrite <- e0 in *. rewrite <- e in *.
        dest_strlt.
      + destruct (ODT_eqdec x k); trivial.
    - destruct (trichotemy s k); intuition.
      subst.
      destruct (assoc_lookupr ODT_eqdec l x); try reflexivity.
      destruct (ODT_eqdec x k); trivial.
  Qed.

  Lemma assoc_lookupr_drec_sort {A} l x :
    assoc_lookupr ODT_eqdec (@rec_sort A l) x = 
    assoc_lookupr ODT_eqdec l x.
  Proof.
    revert x. induction l; simpl; trivial; intros.
    destruct a; simpl.
    rewrite assoc_lookupr_insert, IHl.
    trivial.
  Qed.

  Lemma assoc_lookupr_drec_sort_app_nin {A} l l' x: 
    ~ In x (domain l') ->
    assoc_lookupr ODT_eqdec (@rec_sort A (l ++ l')) x
    = assoc_lookupr ODT_eqdec (rec_sort l) x.
  Proof.
    repeat rewrite assoc_lookupr_drec_sort.
    intros.
    rewrite (assoc_lookupr_app l l'); intros.
    case_eq (assoc_lookupr ODT_eqdec l' x); trivial; intros.
    apply assoc_lookupr_in in H0.
    apply in_dom in H0; intuition.
    idtac.
    assert ((@assoc_lookupr K A
                            (@Equivalence.equiv K (@eq K) (@eq_equivalence K))
                            (@complement K
                                         (@Equivalence.equiv K (@eq K) (@eq_equivalence K)))
                            (@ODT_eqdec K odt) l' x) =
            (@assoc_lookupr K A (@eq K) (fun x0 y : K => not (@eq K x0 y))
                            (@ODT_eqdec K odt) l' x)) by reflexivity.
    rewrite H1 in *.
    rewrite H0; reflexivity.
  Qed.

  Lemma insertion_sort_insert_domain {B:Type} x a (b:B) l : 
    In x (domain
            (LibUtilsSortingAdd.insertion_sort_insert rec_field_lt_dec 
                                              (a, b) l)) ->
    a = x \/ In x (domain l).
  Proof.
    revert x a b. induction l; simpl; intuition.
    destruct (ODT_lt_dec a a0); simpl in *; [intuition|].
    destruct (ODT_lt_dec a0 a); simpl in *; [|intuition].
    intuition. destruct (IHl _ _ _ H0); auto.
  Qed.

  Lemma drec_sort_domain {A} x l :
    In x (domain (@rec_sort A l)) -> In x (domain l).
  Proof.
    revert x.
    induction l; simpl; intuition.
    apply insertion_sort_insert_domain in H. intuition.
  Qed.

  Lemma drec_concat_sort_pullout {A} b x xv y yv : 
    NoDup (x::y::(domain b)) ->
    (@ rec_concat_sort A (rec_concat_sort b ((x, xv) :: nil))
       ((y, yv) :: nil))
    =
    (rec_concat_sort (rec_concat_sort b ((y, yv) :: nil))
                     ((x, xv) :: nil)).
  Proof.
    intros.
    inversion H; subst.
    inversion H3; subst.
    simpl in *.
    apply drec_sort_perm_eq; simpl.
    -  rewrite Permutation_app_comm; simpl.
       constructor; simpl.
       + intros nin. 
         unfold rec_concat_sort in nin;
           apply drec_sort_domain in nin.
         rewrite domain_app, in_app_iff in nin.
         simpl in *.
         intuition.
       + unfold rec_concat_sort.
         simpl in *.
         rewrite <- rec_sort_perm;
           rewrite Permutation_app_comm; simpl; constructor; intuition.
    - unfold rec_concat_sort.
      simpl. rewrite Permutation_app_comm. simpl.
      rewrite <- rec_sort_perm.
      rewrite Permutation_app_comm; simpl.
      rewrite Permutation_app_comm.
      simpl.
      intuition.
      rewrite <- rec_sort_perm.
      rewrite Permutation_app_comm. simpl.
      apply perm_swap.
      rewrite domain_app; simpl.
      assert (Permutation (y::domain b) (domain b++y::nil)).
      rewrite Permutation_app_comm. reflexivity.
      rewrite <- H2; assumption.
      assert (NoDup (x :: domain b)).
      constructor.
      inversion H. subst.
      simpl in H6.
      unfold not in *.
      intros. apply H6. right; assumption.
      assumption.
      rewrite domain_app; simpl.
      assert (Permutation (x::domain b) (domain b++x::nil)).
      rewrite Permutation_app_comm. reflexivity.
      rewrite <- H1; assumption.
  Qed.

  Lemma sorted_cons_filter_in_domain {A} (l l':list (K*A)) f a :
    filter f l = a :: l' -> In a l.
  Proof.
    induction l; intros.
    simpl in H; congruence.
    simpl in *.
    destruct (f a0).
    - inversion H; left; reflexivity.
    - right; apply (IHl H).
  Qed.
  
  Lemma filter_choice {A} (l:list(K*A)) f:
    filter f l = nil \/ (exists a, exists l', filter f l = a :: l').
  Proof.
    induction l.
    left; reflexivity.
    simpl in *.
    elim IHl; clear IHl; intros.
    rewrite H.
    destruct (f a).
    right; exists a; exists nil; reflexivity.
    left; reflexivity.
    elim H; clear H; intros.
    elim H; clear H; intros.
    rewrite H.
    destruct (f a).
    right; exists a; exists (x :: x0); reflexivity.
    right; exists x; exists x0; reflexivity.
  Qed.

  Lemma sorted_over_filter {A} (l:list (K*A)) f:
    is_list_sorted ODT_lt_dec (domain l) = true ->
    is_list_sorted ODT_lt_dec (domain (filter f l)) = true.
  Proof.
    intros.
    induction l.
    reflexivity.
    simpl.
    case_eq (f a); intros.
    - generalize (filter_choice l f); intros.
      elim H1; clear H1; intros.
      + rewrite H1 in *. reflexivity.
      + elim H1; clear H1; intros.
        elim H1; clear H1; intros.
        rewrite H1 in *.
        assert (In x l) by (apply (sorted_cons_filter_in_domain l x0 f); assumption).
        assert (ODT_lt (fst a) (fst x)) by (apply (sorted_cons_in l a x); assumption).
        apply rec_cons_lt.
        apply IHl.
        simpl in H.
        destruct (domain l).
        reflexivity.
        destruct (ODT_lt_dec (fst a) k); try congruence; assumption.
        assumption.
    - apply IHl.
      simpl in H.
      destruct (domain l). reflexivity.
      destruct (ODT_lt_dec (fst a) k).
      assumption.
      congruence.
  Qed.

  Lemma rec_sort_insert_filter_fst_true {A:Type} f  
        (a:K*A) (l:list (K*A)) 
        (fstonly:forall a b c, f (a,b) = f (a,c)) :
    StronglySorted rec_field_lt l ->
    f a = true ->
    filter f (insertion_sort_insert rec_field_lt_dec a l)
    = insertion_sort_insert rec_field_lt_dec a (filter f l).
  Proof.
    revert a.
    induction l; simpl; intros b lsort fb.
    - rewrite fb; trivial.
    - inversion lsort; subst.
      case_eq (f a); simpl; intros fa.
      +  destruct (rec_field_lt_dec b a); simpl.
         * rewrite fb.
           simpl. match_destr.
         * rewrite <- IHl; trivial.
           match_destr; simpl; rewrite fa; trivial.
      + match_destr.
        * simpl. rewrite fb, fa.
          rewrite insertion_sort_insert_forall_lt; trivial.
          apply Forall_filter.
          revert H2.
          apply Forall_impl_in; intros.
          etransitivity; eauto.
        * rewrite <- IHl; trivial.
          match_destr; simpl; rewrite fa; trivial.
          unfold rec_field_lt in *.
          destruct (trichotemy (fst a) (fst b)) as [[?|?]|?]; try congruence.
          destruct a; destruct b; simpl in *; subst.
          specialize (fstonly k0 a a0). congruence.
  Qed.
  
  Lemma rec_sort_insert_filter_fst_false {A:Type} f  
        (a:K*A) (l:list (K*A)) 
        (fstonly:forall a b c, f (a,b) = f (a,c)) :
    f a = false ->
    filter f (insertion_sort_insert rec_field_lt_dec a l) =
    filter f l.
  Proof.
    revert a.
    induction l; simpl; intros ? fa.
    - rewrite fa; trivial.
    - match_destr; simpl.
      + rewrite fa; trivial.
      + match_destr; simpl.
        rewrite IHl; trivial.
  Qed.
  
  Lemma rec_sort_filter_fst_commute {A:Type} f (l:list (K*A))
        (fstonly:forall a b c, f (a,b) = f (a,c)) :
    filter f (rec_sort l)
    = rec_sort (filter f l).
  Proof.
    induction l; simpl; trivial.
    case_eq (f a); intros fa; simpl.
    - rewrite <- IHl, rec_sort_insert_filter_fst_true; trivial.
      eapply Sorted_StronglySorted.
      + apply StrictOrder_Transitive.
      + eapply insertion_sort_Sorted.
    - rewrite <- IHl, rec_sort_insert_filter_fst_false; trivial.
  Qed.
  
  Lemma forallb_rec_sort {A} f (l:list (K*A)) :
    forallb f l = true ->
    forallb f (rec_sort l) = true.
  Proof.
    repeat rewrite forallb_forall; intros.
    apply H.
    unfold rec_sort in *.
    eapply in_insertion_sort; eauto.
  Qed.

  Lemma forallb_rec_sort_inv {A} f (l:list (K*A)) :
    NoDup (domain l) ->
    forallb f (rec_sort l) = true ->
    forallb f l = true.
  Proof.
    repeat rewrite forallb_forall; intros.
    apply H0.
    eapply Permutation_in; try eassumption.
    apply rec_sort_perm; trivial.
  Qed.
  
  Lemma domain_rec_sort_insert {B} (a:K*B) l :
    domain (insertion_sort_insert rec_field_lt_dec a l) =
    insertion_sort_insert ODT_lt_dec (fst a) (domain l).
  Proof.
    revert a.
    induction l; simpl; trivial; intros.
    destruct a; destruct a0.
    simpl.
    match_destr.
    match_destr.
    simpl. rewrite IHl; trivial.
  Qed.

  Lemma domain_rec_sort {B} (l:list (K*B)) :
    domain (rec_sort l) = insertion_sort ODT_lt_dec (domain l).
  Proof.
    unfold rec_sort.
    induction l; simpl; trivial.
    rewrite domain_rec_sort_insert, IHl; trivial.
  Qed.

  Lemma is_list_sorted_domain_rec_field {B} (l:list (K*B)) :
    is_list_sorted rec_field_lt_dec l
    = is_list_sorted ODT_lt_dec (domain l).
  Proof.
    induction l; simpl; trivial.
    match_destr.
    destruct a; destruct p; simpl.
    match_destr.
  Qed.

  Lemma rec_sort_insert_in_dom {B} a (l:list (K*B)) : 
    In (fst a) (domain l) ->
    is_list_sorted ODT_lt_dec (domain l) = true ->
    insertion_sort_insert rec_field_lt_dec a l = l.
  Proof.
    induction l.
    - intuition.
    - intros.
      destruct a; destruct a0; simpl.
      simpl in H.
      destruct H.
      + subst. match_destr.
        apply ODT_lt_irr in o.
        intuition.
      + rewrite IHl; trivial.
        { match_destr.
          - assert (is_list_sorted ODT_lt_dec (domain ((k,b)::(k0, b0) :: l)) = true).
            + simpl; match_destr; intuition.
            + eapply is_list_sorted_NoDup_strlt in H1.
              simpl in H1. inversion H1; subst.
              elim H4. simpl; intuition.
          - match_destr.
        }
        apply is_list_sorted_cons_inv in H0; trivial.
  Qed.
  
  Lemma in_rec_sort_insert {A} `{EqDec A eq} (x:K*A) (k:K) (a:A) l:
    In x (insertion_sort_insert rec_field_lt_dec (k, a) l) ->
    x = (k, a) \/ In x l.
  Proof.
    revert x a. induction l; simpl; [intuition | ].
    intros x a0.
    destruct a; simpl in *.
    destruct (ODT_lt_dec k k0); simpl; intros; trivial.
    - elim H0; clear H0; intros; [left|]; auto.
    - destruct (ODT_lt_dec k0 k); simpl; intros; intuition.
      simpl in H0.
      elim H0; clear H0; intros.
      + intuition.
      + destruct (IHl _ _ H0); intuition.
  Qed.

  Lemma rec_sort_filter_latter_from_former {B} s (l1 l2:list (K*B)) :
    In s (domain l2) ->
    rec_sort (l1 ++ l2) =
    rec_sort (filter (fun x : K * B => s <>b fst x) l1 ++ l2).
  Proof.
    revert l2.
    induction l1; simpl; trivial; intros.
    rewrite IHl1; trivial.
    match_case; intros eqq.
    unfold nequiv_decb, equiv_decb in eqq.
    destruct (equiv_dec s (fst a)); try discriminate.
    red in e; subst.
    apply rec_sort_insert_in_dom.
    - rewrite drec_sort_equiv_domain.
      rewrite domain_app, in_app_iff; intuition.
    - apply rec_sort_pf.
  Qed.

  Section Forall.

    Lemma Forall_sorted {A} (P:(K*A) -> Prop) (l:list (K*A)):
      Forall P l -> Forall P (rec_sort l).
    Proof.
      apply Forall_insertion_sort.
    Qed.

  End Forall.
  
  Section CompatSort.

    Lemma compatible_app_compatible {A} `{EqDec A eq} {l1 l2:list (K*A)} :
      is_list_sorted ODT_lt_dec (domain l1) = true ->
      is_list_sorted ODT_lt_dec (domain l2) = true ->
      compatible l1 l2 = true ->
      compatible (l1++l2) (l1++l2) = true.
    Proof.
      unfold compatible.
      repeat rewrite forallb_forall; intros.
      apply in_app_iff in H3.
      unfold compatible_with in *.
      match_case; intros.
      match_destr; intros; unfold equiv, complement in *.
      elim c; clear c.
      destruct x.
      apply assoc_lookupr_in in H4.
      apply in_app_iff in H4; simpl in *.
      apply is_list_sorted_NoDup_strlt in H0.
      apply is_list_sorted_NoDup_strlt in H1.
      intuition.
      - generalize (nodup_in_eq H0 H3 H5); intros; subst; reflexivity.
      - specialize (H2 _ H5). match_case_in H2; simpl in *; intros.
        + rewrite H4 in H2. apply assoc_lookupr_in in H4.
          generalize (nodup_in_eq H1 H3 H4); intros; subst.
          match_destr_in H2.
        + apply in_dom in H3. apply assoc_lookupr_none_nin in H4.
          intuition.
      - specialize (H2 _ H3). match_case_in H2; simpl in *; intros.
        + rewrite H4 in H2. apply assoc_lookupr_in in H4.
          generalize (nodup_in_eq H1 H5 H4); intros; subst.
          match_destr_in H2.
          congruence.
        + apply in_dom in H5. apply assoc_lookupr_none_nin in H4.
          intuition.
      - generalize (nodup_in_eq H1 H3 H5); intros; subst; reflexivity.
    Qed.
    
    Lemma compatible_asymmetric_over {A} `{EqDec A eq} {l:list(K*A)} :
      compatible l l = true ->
      asymmetric_over rec_field_lt l.
    Proof.
      unfold asymmetric_over; intros.
      destruct x; destruct y; unfold rec_field_lt in *.
      simpl in *.
      generalize (lt_not_not k k0 H3 H4); intros eqq.
      subst.
      unfold compatible in *.
      rewrite forallb_forall in H0.
      generalize (H0 _ H1); simpl in *.
      specialize (H0 _ H2); simpl in *; intros.
      unfold compatible_with in *.
      match_case_in H0; intros.
      - rewrite H6 in *. match_destr_in H0; match_destr_in H5.
        congruence.
      - apply assoc_lookupr_none_nin in H6. apply in_dom in H2.
        congruence.
    Qed.

    Lemma compatible_sort_equivlist {A} `{EqDec A eq} {l:list(K*A)} :
      compatible l l = true ->
      equivlist l (rec_sort l).
    Proof.
      split; intros.
      - apply insertion_sort_in_strong; trivial.
        apply compatible_asymmetric_over.
        trivial.
      - unfold rec_sort in *. unfold rec_sort in H0. eapply in_insertion_sort; eauto.
    Qed.

  End CompatSort.

  Section sublist.
    
    Lemma sublist_rec_concat_sort_bounded {A} r srl :
      incl (domain r) (domain srl) ->
      domain (@rec_concat_sort A r srl) = domain (rec_sort srl).
    Proof.
      unfold rec_concat_sort.
      repeat rewrite domain_rec_sort.
      rewrite domain_app; intros.
      apply insertion_sort_equivlist; [apply ODT_lt_contr | ].
      rewrite app_commutative_equivlist.
      rewrite app_contained_equivlist; [ reflexivity | ].
      rewrite H; reflexivity.
    Qed.

    Lemma domain_rec_concat_sort_app_comm:
      forall (A : Type) (l l' : list (K * A)),
        domain (rec_concat_sort l l') = domain (rec_concat_sort l' l).
    Proof.
      intros.
      unfold rec_concat_sort.
      repeat rewrite domain_rec_sort.
      apply insertion_sort_equivlist; [apply ODT_lt_contr | ].
      repeat rewrite domain_app.
      rewrite app_commutative_equivlist.
      reflexivity.
    Qed.

    Lemma incl_sort_sublist {A B} a b :
      incl (@domain _ A a) (@domain _ B b) ->        
      sublist (domain (rec_sort a)) (domain (rec_sort b)).
    Proof.
      intros.
      repeat erewrite domain_rec_sort.
      apply Sorted_incl_sublist.
      - apply insertion_sort_Sorted.
      - apply insertion_sort_Sorted.
      - intros. apply in_insertion_sort in H0.
        specialize (H _ H0).
        apply insertion_sort_in; [apply ODT_lt_contr | ].
        trivial.
    Qed.

    Lemma rec_concat_sort_sublist {B} l1 l2 :
      sublist (@domain _ B (rec_sort l1)) (domain (rec_concat_sort l1 l2)).
    Proof.
      apply incl_sort_sublist.
      rewrite incl_appl; try reflexivity.
      rewrite domain_app. reflexivity.
    Qed.
    
    Lemma rec_concat_sort_sublist_sorted {B} l1 l2 :
      is_list_sorted ODT_lt_dec (domain l1) = true ->
      sublist (@domain _ B l1) (domain (rec_concat_sort l1 l2)).
    Proof.
      intros.
      rewrite <- rec_concat_sort_sublist.
      rewrite rec_sorted_id; trivial.
      reflexivity.
    Qed.

  End sublist.

  Global Instance assoc_lookupr_equiv_rec_sort  {A : Type} :
    Proper (assoc_lookupr_equiv ==> assoc_lookupr_equiv) (@rec_sort A).
  Proof.
    unfold Proper, respectful, assoc_lookupr_equiv; intros.
    repeat rewrite assoc_lookupr_drec_sort.
    trivial.
  Qed.

  Section rev.
    Lemma lookup_rev_rec_sort {B} (x:K) (l:list (K*B)) :
      lookup ODT_eqdec (rev (rec_sort l)) x = lookup ODT_eqdec (rec_sort l) x.
    Proof.
      case_eq (lookup ODT_eqdec (rec_sort l) x); intros.
      - apply (@lookup_some_nodup_perm _ _ _ (rec_sort l) (rev (rec_sort l))).
        + apply StronglySorted_NoDup.
          rewrite <- (sorted_StronglySorted ODT_lt_dec).
          apply rec_sort_pf.
        + apply Permutation.Permutation_rev.
        + assumption.
      - apply (@lookup_none_perm _ _ _ (rec_sort l) (rev (rec_sort l))).
        + apply Permutation.Permutation_rev.
        + assumption.
    Qed.
  End rev.

  Lemma insertion_sort_nin_inv {B} (s:K) (x₁:B) l₁ x₂  l₂:
    ~ In s (domain l₁) ->
    ~ In s (domain l₂) ->
    insertion_sort_insert rec_field_lt_dec (s, x₁) l₁ =
    insertion_sort_insert rec_field_lt_dec (s, x₂) l₂ ->
    x₁ = x₂ /\ l₁ = l₂.
  Proof.
    intros nin1 nin2 eqq1.
    generalize (insertion_sort_insert_nin_perm l₁ (s,x₁) nin1); intros perm1.
    generalize (insertion_sort_insert_nin_perm l₂ (s,x₂) nin2); intros perm2.
    rewrite eqq1 in perm1.
    rewrite <- perm1 in perm2.
    apply Permutation_cons_nin_map with (f:=fst) in perm2; simpl; trivial.
    destruct perm2 as [eqq2 perm2].
    invcs eqq2.
    split; trivial.
    apply insertion_sort_insert_nin_eq_inv in eqq1; trivial
    ; intros inn; apply in_dom in inn; tauto.
  Qed.

  Lemma rec_sort_cons_nin_inv {B} (s:K) (x₁:B) l₁ x₂  l₂:
    ~ In s (domain l₁) ->
    ~ In s (domain l₂) ->
    rec_sort ((s, x₁) :: l₁) =
    rec_sort ((s, x₂) :: l₂) ->
    x₁ = x₂ /\ rec_sort l₁ = rec_sort l₂.
  Proof.
    simpl.
    intros.
    eapply insertion_sort_nin_inv; eauto
    ; rewrite drec_sort_equiv_domain; trivial.
  Qed.

End Bindings.

Section Map.

  Lemma map_rec_sort {A B C D} `{odta:ODT A} `{odtb:ODT B} (f:A*C->B*D) (l:list(A*C))
        (consistent:forall x y, rec_field_lt x y <->
                                rec_field_lt (f x) (f y)) :
    map f (rec_sort l) = rec_sort (map f l).
  Proof.
    unfold rec_sort.
    apply map_insertion_sort.
    trivial.
  Qed.
End Map.

Section BindingsString.
  
  Global Program Instance ODT_string : (@ODT string)
    := mkODT _ _ StringOrder.lt _ StringOrder.lt_dec StringOrder.compare StringOrder.compare_spec.

End BindingsString.

Section Edot.
  (* note: right-rec so that new fields hide old fields *)
  Definition edot {A} (r:list (string*A)) (a:string) : option A :=
    assoc_lookupr ODT_eqdec r a.

  Lemma edot_nodup_perm {A:Type} (l l':list (string*A)) x :
    NoDup (domain l) -> Permutation l l' -> edot l x = edot l' x.
  Proof.
    apply assoc_lookupr_nodup_perm.
  Qed.
  
  Lemma edot_fresh_concat {A} x (d:A) b :
    ~ In x (domain b) ->
    edot (rec_concat_sort b ((x,d)::nil)) x = Some d.
  Proof.
    intros.
    apply (@assoc_lookupr_insertion_sort_fresh string ODT_string); trivial.
  Qed.

End Edot.

Hint Unfold rec_sort rec_concat_sort.
Hint Resolve drec_sort_sorted drec_concat_sort_sorted.
Hint Resolve is_list_sorted_NoDup_strlt.

Section MergeBindings.
  (* Merge record stuff *)

  Definition merge_bindings {A} `{EqDec A eq} (l₁ l₂:list (string * A)) : option (list (string * A)) :=
    if compatible l₁ l₂
    then Some (rec_concat_sort l₁ l₂)
    else None.

  Lemma merge_bindings_nil_l {A} `{EqDec A eq} l : merge_bindings nil l = Some (rec_sort l).
  Proof.
    unfold merge_bindings.
    simpl.
    unfold rec_concat_sort; simpl.
    trivial.
  Qed.

  Lemma merge_bindings_nil_r {A} `{EqDec A eq} l : merge_bindings l nil = Some (rec_sort l).
  Proof.
    unfold merge_bindings.
    simpl.
    rewrite compatible_nil_r.
    unfold rec_concat_sort.
    rewrite app_nil_r.
    trivial.
  Qed.

  Lemma merge_bindings_single_nin {A} `{EqDec A eq} b x d :
    ~ In x (domain b) ->
    merge_bindings b ((x,d)::nil) =
    Some (rec_concat_sort b ((x,d)::nil)).
  Proof.
    intro nin.
    unfold merge_bindings.
    rewrite compatible_single_nin; auto.
  Qed.

  Lemma merge_bindings_sorted {A} `{EqDec A eq} {g g1 g2} :
    Some g = merge_bindings g1 g2 ->
    is_list_sorted ODT_lt_dec (@domain string A g) = true.
  Proof.
    unfold merge_bindings. intros.
    destruct (compatible g1 g2); try discriminate.
    inversion H0; subst.
    unfold rec_concat_sort, rec_concat_sort in *.
    eauto.
  Qed.

  Lemma edot_merge_bindings {A} `{EqDec A eq} (l1 l2:list (string*A)) (s:string) (x:A) :
    merge_bindings l1 ((s, x)::nil) = Some l2 ->
    edot l2 s = Some x.
  Proof.
    intros.
    unfold merge_bindings in *.
    case_eq (compatible l1 ((s, x)::nil)); intros; rewrite H1 in *; try congruence.
    inversion H0; clear H0.
    unfold edot.
    unfold rec_concat_sort in *.
    rewrite (@assoc_lookupr_drec_sort string ODT_string) in *.
    rewrite (@assoc_lookupr_app).
    simpl.
    destruct (string_eqdec s s); [reflexivity|congruence].
  Qed.

  Lemma merge_bindings_nodup {A} `{EqDec A eq} (l l0 l1:list (string*A)):
    merge_bindings l l0 = Some l1 -> NoDup (domain l1).
  Proof.
    intros.
    unfold merge_bindings in *.
    destruct (compatible l l0); try congruence.
    inversion H0.
    apply is_list_sorted_NoDup_strlt.
    apply (rec_concat_sort_sorted l l0).
    reflexivity.
  Qed.
  
  Lemma merge_bindings_compatible {A} `{EqDec A eq} (l l0 l1:list (string*A)):
    merge_bindings l l0 = Some l1 -> compatible l l0 = true.
  Proof.
    intros.
    unfold merge_bindings in H0.
    destruct (compatible l l0); congruence.
  Qed.

  Lemma sorted_cons_is_compatible {A} `{EqDec A eq} (l:list (string*A)) (a:string*A):
    is_list_sorted ODT_lt_dec (domain (a :: l)) = true ->
    compatible_with (fst a) (snd a) l = true.
  Proof.
    intros.
    assert (NoDup (domain (a :: l)))
      by (apply is_list_sorted_NoDup_strlt; assumption).
    unfold compatible_with.
    destruct a; simpl.
    inversion H1. subst.
    assert (assoc_lookupr equiv_dec l s = None) by
        (apply assoc_lookupr_nin_none; assumption).
    rewrite H2.
    reflexivity.
  Qed.

  Lemma compatible_self {A} `{EqDec A eq} (l:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    compatible l l = true.
  Proof.
    intros.
    induction l; try reflexivity.
    assert (is_list_sorted ODT_lt_dec (domain l) = true)
      by (apply (@rec_sorted_skip_first string ODT_string _ l a); assumption).
    assert (NoDup (domain (a::l)))
      by (apply is_list_sorted_NoDup_strlt; assumption).
    inversion H2. subst.
    specialize (IHl H1).
    simpl. rewrite andb_true_inversion.
    destruct a; simpl.
    unfold compatible_with; simpl.
    assert (assoc_lookupr equiv_dec l s = None) by
        (apply assoc_lookupr_nin_none; assumption).
    rewrite H3.
    destruct (equiv_dec s s); try congruence.
    destruct (equiv_dec a a); try congruence.
    split; try reflexivity.
    apply compatible_cons_r; try assumption.
    simpl.
    unfold compatible_with.
    assert (assoc_lookupr equiv_dec l s = None) by
        (apply assoc_lookupr_nin_none; assumption).
    rewrite H4; reflexivity.
  Qed.

  Lemma merge_self_sorted {A} `{EqDec A eq} (l:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    merge_bindings l l = Some l.
  Proof.
    intros.
    unfold merge_bindings.
    rewrite compatible_self; try assumption.
    f_equal.
    apply rec_concat_sort_self; assumption.
  Qed.

  Lemma merge_self_sorted_r {A} `{EqDec A eq} (l:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    merge_bindings l (rec_sort l) = Some (rec_sort l).
  Proof.
    intros.
    rewrite rec_sorted_id; try assumption.
    apply merge_self_sorted; assumption.
  Qed.

  Lemma same_domain_merge_bindings_eq
        {A} `{EqDec A eq} (l₁ l₂ l₃:list (string*A)) :
    NoDup (domain l₁) ->
    domain l₁ = domain l₂ ->
    merge_bindings l₁ l₂ = Some l₃ ->
    l₁ = l₂.
  Proof.
    unfold merge_bindings.
    match_case; intros compat nd eqd eqq.
    invcs eqq.
    apply (same_domain_compatible _ _ nd eqd compat).
  Qed.

  Definition compatible {A:Type} `{x:EqDec A eq} := @compatible string A _ _ _ _.
  
  Lemma merge_returns_compatible {A} `{equiv:EqDec A eq} (l1 l2 l3:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l1) = true ->
    is_list_sorted ODT_lt_dec (domain l2) = true ->
    compatible l1 l2 = true ->
    rec_concat_sort l1 l2 = l3 ->
    compatible l1 l3 = true.
  Proof.
    intros.
    assert (NoDup (domain l1)) by (apply is_list_sorted_NoDup_strlt; assumption).
    assert (NoDup (domain l2)) by (apply is_list_sorted_NoDup_strlt; assumption).
    unfold merge_bindings in H2.
    unfold compatible, LibUtilsCompat.compatible in *.
    rewrite forallb_forall in H1.
    rewrite forallb_forall; intros.
    destruct x; simpl in *.
    specialize (H1 (s,a) H5).
    simpl in *.
    rewrite <- H2.
    unfold compatible_with in *.
    unfold rec_concat_sort.
    rewrite (@assoc_lookupr_drec_sort string ODT_string).
    simpl in *; unfold equiv_dec, string_eqdec in *.
    rewrite (@assoc_lookupr_app string).
    case_eq (assoc_lookupr string_dec l2 s); intros.
    assert ((@assoc_lookupr string A
                            (@Equivalence.equiv string (@eq string)
                                                (@eq_equivalence string))
                            (@complement string
                                         (@Equivalence.equiv string (@eq string)
                                                             (@eq_equivalence string))) string_dec l2 s ) =
            (@assoc_lookupr string A (@eq string)
                            (fun s1 s2 : string => not (@eq string s1 s2)) string_dec l2 s)) by reflexivity.
    rewrite H7 in *.
    rewrite H6 in H1.
    - assumption.
    - assert (assoc_lookupr string_dec l1 s = Some a).
      apply in_assoc_lookupr_nodup; assumption.
      unfold string_eqdec.
      rewrite H7.
      destruct (equiv a a); congruence.
  Qed.
  
  Lemma merge_idem {A} `{EqDec A eq} (l l0 l1:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    is_list_sorted ODT_lt_dec (domain l0) = true ->
    merge_bindings l l0 = Some l1 ->
    merge_bindings l l1 = Some l1.
  Proof.
    intros.
    unfold merge_bindings in *.
    case_eq (compatible l l0); intros;
      unfold compatible in *; rewrite H3 in H2; try congruence.
    inversion H2; clear H2.
    assert (compatible l (rec_concat_sort l l0) = true)
      by (apply (merge_returns_compatible l l0 (rec_concat_sort l l0) H0 H1 H3); reflexivity).
    unfold compatible in *. rewrite H2.
    rewrite rec_concat_sort_idem; try assumption; reflexivity.
  Qed.

(* merge_idem isn't true unless l is without duplicates! Here is a
     counter example.
   Open Scope string.
   Definition tup1 := ("a",1) :: ("b",2) :: ("a", 3) :: nil.
   Definition tup2 := ("c",2) :: nil.
   Eval compute in (merge_bindings tup1 tup2).
   Definition tup3 := [("a", 3); ("b", 2); ("c", 2)].
   Eval compute in (compatible tup1 tup3).
 *)

End MergeBindings.

Hint Resolve @merge_bindings_sorted.

