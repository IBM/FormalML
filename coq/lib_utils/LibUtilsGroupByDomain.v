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

(** This module defines grouping by the domain of an association list
    and the derived equivalence relation, grouped_equiv.
    This equivalence allows elements with different keys to 
    be freely rearranged.
 *)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Permutation.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Equivalence.
Require Import RelationClasses.
Require Import Lia.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsLift.
Require Import LibUtilsListAdd.
Require Import LibUtilsAssoc.
Require Import LibUtilsSublist.
Require Import LibUtilsBag.

Section groupbydomain.

  (* There may be some relation here to groupby *)
  Fixpoint groupby_domain {A B} {dec: EqDec A eq} (l:list (A*B)): list (A*list B)
    := match l with
       | nil => nil
       | (a,b)::l' =>
         let rest := groupby_domain l' in
         match lookup dec rest a with
         | Some bs => update_first dec rest a (b::bs)
         | None => (a, (b::nil))::rest
         end
       end.

  Definition grouped_equiv {A B} {dec:EqDec A eq} (l1 l2 :list (A*B))
    := Permutation (groupby_domain l1) (groupby_domain l2).

  Definition list_unnest {A B} (l:list (A*list B)) : list (list (A*B))
    := map (fun x => map (fun y => (fst x, y)) (snd x)) l.

  Global Instance grouped_equiv_equiv {A B} {dec:EqDec A eq} : Equivalence (@grouped_equiv A B dec).
  Proof.
    unfold grouped_equiv.
    constructor; red; intros.
    - reflexivity.
    - symmetry; trivial.
    - etransitivity; eauto.
  Qed.

  Lemma groupby_domain_concat_list_unest_perm {A B} {dec: EqDec A eq} (l:list (A*B))
    : Permutation (concat (list_unnest (groupby_domain l))) l.
  Proof.
    induction l; simpl; trivial.
    destruct a.
    case_eq (lookup dec (groupby_domain l) a); simpl; intros.
    - destruct (in_update_break dec H (b::l0))
        as [l1 [l2 [eqq1 eqq2]]].
      rewrite eqq2.
      unfold list_unnest in *.
      rewrite eqq1 in *.
      rewrite map_app, concat_app in *.
      simpl in *.
      rewrite <- IHl.
      repeat rewrite Permutation_middle.
      reflexivity.
    - constructor; trivial.
  Qed.

  Global Instance grouped_equiv_perm {A B} {dec: EqDec A eq} :
    subrelation (@grouped_equiv A B dec) (@Permutation (A*B)).
  Proof.
    unfold grouped_equiv; intros l1 l2 perm.
    rewrite <- (groupby_domain_concat_list_unest_perm l1).
    rewrite <- (groupby_domain_concat_list_unest_perm l2).      
    apply Permutation_concat.
    apply Permutation_map.
    trivial.
  Qed.

  Lemma groupby_domain_NoDup {A B} {dec: EqDec A eq} (l:list (A*B)) :
    NoDup (domain (groupby_domain l)).
  Proof.
    induction l; simpl.
    - constructor.
    - destruct a.
      match_option.
      + rewrite domain_update_first; trivial.
      + simpl; constructor; trivial.
        apply lookup_none_nin in eqq; trivial.
  Qed.

  Lemma groupby_domain_nnil {A B} {dec: EqDec A eq} (l:list (A*B)) :
    ~ In nil (codomain (groupby_domain l)).
  Proof.
    induction l; simpl.
    - tauto.
    - destruct a.
      match_option; simpl.
      + destruct (in_update_break dec eqq (b::l0))
          as [m1 [m2 [meqq mueqq]]].
        rewrite mueqq; simpl.
        rewrite meqq in IHl.
        rewrite codomain_app, in_app_iff in IHl |- *; simpl in *.
        intuition discriminate.
      + intuition discriminate.
  Qed.

  Lemma groupby_domain_concat_list_unest_equiv {A B} {dec: EqDec A eq} (l:list (A*B))
    : lookup_equiv (concat (list_unnest (groupby_domain l))) l.
  Proof.
    unfold lookup_equiv.
    induction l; simpl; trivial.
    destruct a.
    intros x.
    case_eq (lookup dec (groupby_domain l) a); simpl; intros.
    - generalize (groupby_domain_nnil l); intros nn.
      destruct (in_update_break_first dec H (b::l0))
        as [l1 [l2 [eqq1 [eqq2 nin]]]].
      rewrite eqq2.
      unfold list_unnest in *.
      rewrite eqq1 in *.
      rewrite map_app, concat_app in *.
      simpl in *.
      rewrite <- IHl.
      repeat (rewrite lookup_app; simpl).
      destruct (dec x a); unfold equiv, complement in *; trivial.
      subst.
      match_option.
      apply lookup_in in eqq.
      apply concat_In in eqq.
      destruct eqq as [? [inn1 inn2]].
      apply in_map_iff in inn1.
      destruct inn1 as [? [? inn1]]; subst.
      apply in_map_iff in inn2.
      destruct inn2 as [? [eqq inn2]].
      invcs eqq.
      destruct x0; apply in_dom in inn1.
      contradiction.
    - rewrite IHl; trivial.
  Qed.

  Lemma grouped_equiv_cons {A B} {dec: EqDec A eq} {l1 l2:list (A*B)} :
    grouped_equiv l1 l2 ->
    forall a, grouped_equiv (a::l1) (a::l2).
  Proof.
    unfold grouped_equiv; simpl; intros eqq1 a.
    destruct a.
    rewrite (lookup_equiv_perm_nodup (groupby_domain_NoDup l1) eqq1 a).
    match_option.
    - apply update_first_NoDup_perm_proper; trivial.
      apply (groupby_domain_NoDup l1).
    - eauto.
  Qed.

  Lemma grouped_equiv_cons_invs {A B} {dec: EqDec A eq} {a b b'} {l1 l2:list (A*B)} :
    grouped_equiv ((a,b)::l1) ((a,b')::l2) ->
    b = b' /\ grouped_equiv l1 l2.
  Proof.
    unfold grouped_equiv; simpl; intros eqq1.
    repeat match_option_in eqq1; try discriminate.
    - destruct (update_first_NoDup_perm_invs 
                  (fun x => b::x) (fun y => b'::y)
                  (groupby_domain_NoDup l1) eqq1 eqq eqq0)
        as [perm2 [eqq21 eqq22]].
      + intros ? ? injeq.
        invcs injeq; trivial.
      + invcs eqq22; tauto.
    - destruct (in_update_break dec eqq (b::l))
        as [m1 [m2 [meqq mueqq]]].
      rewrite mueqq in eqq1.
      rewrite <- Permutation_middle in eqq1.
      assert (inn:In (a, b::l) ((a, b::l) :: m1 ++ m2)).
      { simpl; eauto. }
      rewrite eqq1 in inn.
      simpl in inn.
      destruct inn.
      + invcs H.
        elim (groupby_domain_nnil l1); trivial.
        rewrite meqq.
        rewrite codomain_app, in_app_iff; simpl; tauto.
      + apply in_dom in H; apply lookup_none_nin in eqq0.
        contradiction.
    - destruct (in_update_break dec eqq0 (b'::l))
        as [m1 [m2 [meqq mueqq]]].
      rewrite mueqq in eqq1.
      rewrite <- Permutation_middle in eqq1.
      assert (inn:In (a, b'::l) ((a, b'::l) :: m1 ++ m2)).
      { simpl; eauto. }
      rewrite <- eqq1 in inn.
      simpl in inn.
      destruct inn.
      + invcs H.
        elim (groupby_domain_nnil l2); trivial.
        rewrite meqq.
        rewrite codomain_app, in_app_iff; simpl; tauto.
      + apply in_dom in H; apply lookup_none_nin in eqq.
        contradiction.
    - assert (lo1:lookup dec ((a, (b::nil)) :: groupby_domain l1) a = Some (b::nil)).
      { simpl; match_destr; congruence. }
      assert (nd:NoDup (domain ((a, (b::nil)) :: groupby_domain l1))).
      { simpl; constructor.
        - apply lookup_none_nin in eqq; trivial.
        - apply groupby_domain_NoDup.
      } 
      rewrite (lookup_equiv_perm_nodup nd eqq1 a) in lo1.
      simpl in lo1.
      match_destr_in lo1; [| congruence].
      invcs lo1.
      apply Permutation_cons_inv in eqq1.
      tauto.
  Qed.

  Lemma concat_list_unnest_lookup_none {A B} {dec:EqDec A eq} {l1:list (A*list B)} {a} :
    lookup dec l1 a = None ->
    lookup dec (concat (list_unnest l1)) a = None.
  Proof.
    intros lo.
    apply lookup_none_nin in lo.
    apply lookup_nin_none.
    unfold list_unnest, domain.
    rewrite concat_map.
    intros inn.
    apply concat_In in inn.
    destruct inn as [? [inn1 inn2]].
    rewrite map_map in inn1.
    apply in_map_iff in inn1.
    destruct inn1 as [? [? inn1]]; subst.
    rewrite map_map in inn2; simpl in inn2.
    apply in_map_iff in inn2.
    destruct inn2 as [? [? inn2]]; subst.
    destruct x0; apply in_dom in inn1.
    contradiction.
  Qed.

  Lemma concat_list_unnest_lookup_some {A B} {dec:EqDec A eq} {l1:list (A*list B)} {a b l'} :
    lookup dec l1 a = Some (b::l') -> 
    lookup dec (concat (list_unnest l1)) a = Some b.
  Proof.
    intros lo.
    destruct (lookup_split dec lo) as [m1 [m2 [? nin]]]; subst.
    unfold list_unnest.
    rewrite map_app, concat_app, lookup_app; simpl.
    match_option.
    - apply lookup_in in eqq.
      apply concat_In in eqq.
      destruct eqq as [? [inn1 inn2]].
      apply in_map_iff in inn1.
      destruct inn1 as [? [? inn1]]; subst.
      apply in_map_iff in inn2.
      destruct inn2 as [? [eqq inn2]].
      invcs eqq.
      destruct x0; apply in_dom in inn1.
      contradiction.
    - match_destr.
      congruence.
  Qed.
  
  Lemma concat_list_unnest_lookup_equiv {A B} {dec:EqDec A eq} (l1 l2:list (A*list B)) :
    ~ In nil (codomain l1) ->
    lookup_equiv l1 l2 ->
    lookup_equiv (concat (list_unnest l1)) (concat (list_unnest l2)).
  Proof.
    intros nnil lo a.
    specialize (lo a).
    case_eq (lookup dec l1 a); [intros ? eqq1 | intros eqq1]
    ; rewrite eqq1 in *.
    - destruct l.
      + apply lookup_in in eqq1.
        apply in_codom in eqq1.
        contradiction.
      + rewrite (concat_list_unnest_lookup_some eqq1).
        rewrite (concat_list_unnest_lookup_some (symmetry lo)).
        trivial.
    - rewrite (concat_list_unnest_lookup_none eqq1).
      rewrite (concat_list_unnest_lookup_none (symmetry lo)).
      trivial.
  Qed.
  
  Global Instance grouped_equiv_lookup_equiv {A B} {dec:EqDec A eq} :
    subrelation (@grouped_equiv A B dec) lookup_equiv.
  Proof.
    intros l1 l2.
    unfold grouped_equiv.
    intros perm.
    apply lookup_equiv_perm_nodup in perm.
    - rewrite <- (groupby_domain_concat_list_unest_equiv l1).
      rewrite <- (groupby_domain_concat_list_unest_equiv l2).
      apply concat_list_unnest_lookup_equiv; trivial.
      apply groupby_domain_nnil.
    - apply groupby_domain_NoDup.
  Qed.

  Lemma groupby_domain_equivlist {A B} {dec:EqDec A eq} (l:list (A*B)):
    equivlist (domain (groupby_domain l)) (domain l).
  Proof.
    unfold equivlist.
    induction l; simpl; [tauto | ].
    destruct a; simpl.
    intros x.
    match_option.
    - rewrite domain_update_first.
      rewrite IHl.
      apply lookup_in_domain in eqq.
      rewrite IHl in eqq.
      intuition; congruence.
    - simpl; rewrite IHl; tauto.
  Qed.
  
  Lemma groupby_domain_update_first_some {A B} {dec:EqDec A eq} {l:list (A*B)} {v b l'} :
    lookup dec (groupby_domain l) v = Some (b::l') ->
    forall d,
      groupby_domain (update_first dec l v d) = update_first dec (groupby_domain l) v (d::l').
  Proof.
    revert b l'.
    induction l; intros b l' inn d; simpl; try discriminate.
    destruct a; simpl in inn.
    destruct (dec v a); unfold equiv, complement in *
    ; subst; simpl.
    - match_option
      ; rewrite eqq in inn.
      + apply lookup_update_eq in inn.
        invcs inn.
        rewrite update_first_update_first_eq; trivial.
      + simpl in *.
        match_destr; try congruence.
    - match_option_in inn.
      + generalize (@lookup_update_neq _ _ dec (groupby_domain l) a v (b0::l0)).
        unfold equiv_dec; intros re; rewrite re in inn by congruence; clear re.            
        rewrite update_first_update_first_neq_swap by congruence.
        rewrite (IHl _ _ inn).
        generalize (@lookup_update_neq _ _ dec (groupby_domain l) v a (d::l')).
        unfold equiv_dec; intros re; rewrite re by congruence; clear re.
        rewrite eqq; trivial.
      + simpl in inn.
        match_destr_in inn; try congruence.
        rewrite (IHl _ _ inn).
        simpl.
        destruct (dec v a); try congruence.
        generalize (@lookup_update_neq _ _ dec (groupby_domain l) v a (d::l')).
        unfold equiv_dec; intros re; rewrite re by congruence; clear re.
        rewrite eqq; trivial.
  Qed.
  
  Lemma grouped_equiv_update_first {A B} {dec:EqDec A eq} (l1 l2:list (A*B)) v d :
    grouped_equiv l1 l2 ->
    grouped_equiv (update_first dec l1 v d) (update_first dec l2 v d).
  Proof.
    unfold grouped_equiv; intros.
    case_eq (lookup dec (groupby_domain l1) v); [intros ? inn1|intros eqq1].
    - destruct l.
      + elim (groupby_domain_nnil l1).
        apply lookup_in in inn1.
        apply in_codom in inn1; trivial.
      + generalize H; intros perm.
        apply lookup_equiv_perm_nodup in perm; [ | apply groupby_domain_NoDup].
        rewrite (groupby_domain_update_first_some inn1).
        rewrite perm in inn1.
        rewrite (groupby_domain_update_first_some inn1).
        apply update_first_NoDup_perm_proper; trivial.
        apply groupby_domain_NoDup.
    - repeat rewrite nin_update; trivial.
      + apply lookup_none_nin in eqq1.
        rewrite (dom_perm _ _ H) in eqq1.
        apply lookup_nin_none with (dec0:=dec) in eqq1.
        generalize (concat_list_unnest_lookup_none eqq1); intros inn1.
        rewrite groupby_domain_concat_list_unest_equiv in inn1; trivial.
      + generalize (concat_list_unnest_lookup_none eqq1); intros inn1.
        rewrite groupby_domain_concat_list_unest_equiv in inn1; trivial.
  Qed.

  Lemma grouped_equiv_singleton {A B} {dec:EqDec A eq} a (l:list (A*B)) :
    grouped_equiv (a::nil) l -> l = a::nil.
  Proof.
    destruct a.
    unfold grouped_equiv; simpl; intros ge.
    apply Permutation_length_1_inv in ge.
    generalize (groupby_domain_concat_list_unest_perm l).
    rewrite ge; simpl; intros perm.
    apply Permutation_length_1_inv in perm.
    trivial.
  Qed.

  Lemma groupby_domain_lookup_app_nin {A B} {dec:EqDec A eq} (l1 l2 l3 : list (A*B)) x :
    ~ In x (domain l2) ->
    lookup dec (groupby_domain (l1++l2++l3)) x =
    lookup dec (groupby_domain (l1++l3)) x.
  Proof.
    induction l2; simpl; trivial.
    intros nin.
    apply notand in nin.
    destruct nin.
    destruct a; simpl in *.
    rewrite <- (IHl2 H0).
    clear IHl2 H0.
    generalize (l2++l3); clear l2 l3; intros l2.
    induction l1; simpl in *.
    - match_option.
      + replace dec with (@equiv_dec _ _ _ dec) in * by trivial.
        rewrite lookup_update_neq; tauto.
      + simpl.
        match_destr; try congruence.
    - destruct a0; simpl in *.
      destruct (dec a0 x); unfold equiv, complement in *.
      + subst.
        rewrite IHl1.
        match_option; simpl.
        * replace dec with (@equiv_dec _ _ _ dec) in * by trivial.
          { repeat rewrite lookup_update_eq_in; trivial.
            - apply lookup_in_domain in eqq; trivial.
            - apply lookup_in_domain in eqq.
              rewrite groupby_domain_equivlist in *.
              rewrite domain_app, in_app_iff in *; simpl; tauto.
          }
        * match_destr.
      + match_option; simpl.
        * replace dec with (@equiv_dec _ _ _ dec) in * by trivial.
          rewrite lookup_update_neq by tauto.
          rewrite IHl1.
          { match_option.
            - repeat rewrite lookup_update_neq by tauto.
              trivial.
            - simpl.
              match_destr; congruence.
          }
        * destruct (dec x a0); try congruence.
          rewrite IHl1.
          { match_option.
            - replace dec with (@equiv_dec _ _ _ dec) in * by trivial.
              rewrite lookup_update_neq by tauto.
              trivial.
            -  simpl.
               match_destr; congruence.
          }
  Qed.

End groupbydomain.
