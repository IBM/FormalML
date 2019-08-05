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

(** This module defines possible interleavings of lists. *)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Permutation.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Equivalence.
Require Import RelationClasses.
Require Import Omega.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsLift.
Require Import LibUtilsListAdd.
Require Import LibUtilsAssoc.
Require Import LibUtilsSublist.
Require Import LibUtilsBag.

Section interleaving.

  Inductive is_interleaved {A} : list (list A) -> list A -> Prop
    :=
      is_interleaved_concat (ls1 ls2:list (list A)) :
        Permutation ls1 ls2 ->
        is_interleaved ls2 (concat ls1)
    | is_interleaved_cons lh ls1 ls2 l x :
        is_interleaved (lh::ls1) l ->
        Permutation ((x::lh)::ls1) ls2 ->
        is_interleaved ls2 (x::l).

  Lemma is_interleaved_concat_simple {A:Type} (l:list (list A)) :
    is_interleaved l (concat l).
  Proof.
    apply is_interleaved_concat.
    reflexivity.
  Qed.

  Lemma is_interleaved_cons_simple {A:Type} (x:A) lh ls l :
    is_interleaved (lh::ls) l ->
    is_interleaved ((x::lh)::ls) (x::l).
  Proof.
    intros isl.
    eapply is_interleaved_cons; try eassumption.
    reflexivity.
  Qed.

  Global Instance is_interleaved_perm_proper {A}  :
    Proper ((@Permutation (list A)) ==> eq ==> iff) (@is_interleaved A).
  Proof.
    cut (Proper ((@Permutation (list A)) ==> eq ==> Basics.impl) (@is_interleaved A)); unfold Proper, respectful; [intros H | ]; intros l1 l2 perm ? l ?; subst.
    { split; intros isl.
      - eapply H; eauto.
      - symmetry in perm.
        eapply H; eauto.
    }
    intros isl.
    revert l2 perm.
    induction isl; simpl; intros l2 perm.
    - rewrite perm in H.
      constructor; trivial.
    - assert (inn:In (x::lh) ls2).
      { rewrite <- H; simpl; eauto. }
      destruct (in_split _ _ inn) as [ls11 [ls12 ?]]; subst.
      clear inn.
      apply Permutation_cons_app_inv in H.
      specialize (IHisl (lh::ls11++ls12)).
      econstructor.
      + apply IHisl.
        rewrite H; trivial.
      + rewrite <- perm.
        apply Permutation_cons_app; trivial.
  Qed.

  Lemma is_interleaved_refl {A} (l:list A) : is_interleaved (l::nil) l.
  Proof.
    generalize (is_interleaved_concat_simple (l::nil)); simpl.
    rewrite app_nil_r; trivial.
  Qed.

  Lemma is_interleaved_nil_l {A:Type} (l:list A) : is_interleaved nil l <-> l = nil.
  Proof.
    split; intros H.
    - cut (forall x, Permutation nil x -> is_interleaved x l -> l = nil).
      { intros HH; apply (HH nil); trivial. }
      clear; intros.
      revert H.
      induction H0; simpl; trivial; intros perm.
      + apply Permutation_nil in perm; subst; simpl; trivial.
        symmetry in H; apply Permutation_nil in H; subst; simpl; trivial.
      +  apply Permutation_nil in perm; subst; simpl; trivial.
         symmetry in H; apply Permutation_nil in H; subst; simpl; trivial.
         discriminate.
    - subst.
      apply (is_interleaved_concat_simple nil).
  Qed.

  Lemma is_interleaved_perm_concat {A} {ls} {l:list A}:
    is_interleaved ls l -> Permutation l (concat ls).
  Proof.
    induction 1; simpl.
    - apply Permutation_concat; trivial.
    - rewrite IHis_interleaved.
      rewrite <- H0.
      simpl; reflexivity.
  Qed.

  Lemma is_interleaved_both_perm {A:Type} {ls} {l1 l2:list A} :
    is_interleaved ls l1 ->
    is_interleaved ls l2 ->
    Permutation l1 l2.
  Proof.
    intros isl1 isl2.
    rewrite (is_interleaved_perm_concat isl1).
    rewrite (is_interleaved_perm_concat isl2).
    reflexivity.
  Qed.

  Lemma is_interleaved_In {A:Type} (ls:list (list A)) l x :
    is_interleaved ls l ->
    In x l <-> exists l', In l' ls /\ In x l'.
  Proof.
    intros isl.
    rewrite (is_interleaved_perm_concat isl).
    apply concat_In.
  Qed.

  Lemma is_interleaved_sublist {A:Type} {ls} {l:list A} :
    is_interleaved ls l ->
    Forall (fun x => sublist x l) ls.
  Proof.
    induction 1.
    - rewrite <- H.
      apply concat_sublist.
    - invcs IHis_interleaved.
      rewrite <- H0.
      constructor.
      + constructor; trivial.
      + revert H4.
        apply Forall_impl; intros ? subl.
        constructor; trivial.
  Qed.

  Lemma is_interleaved_cons_nil_f {A} {ls:list (list A)} {l:list A} :
    is_interleaved ls l -> is_interleaved (nil :: ls) l.
  Proof.
    intros isl.
    induction isl.
    - rewrite <- H.
      generalize (is_interleaved_concat_simple (nil::ls1)); simpl; trivial. 
    - rewrite <- H.
      rewrite perm_swap in IHisl.
      rewrite perm_swap.
      apply is_interleaved_cons_simple; trivial.
  Qed.

  Lemma is_interleaved_cons_list {A} a ls2 (l2:list A) :
    is_interleaved ls2 l2 ->
    is_interleaved (a::ls2) (a++l2).
  Proof.
    intros isl.
    induction a; simpl.
    - apply is_interleaved_cons_nil_f; trivial.
    - apply is_interleaved_cons_simple; trivial.
  Qed.

  Lemma is_interleaved_app {A} ls1 l1 ls2 (l2:list A) :
    is_interleaved ls1 l1 ->
    is_interleaved ls2 l2 ->
    is_interleaved (ls1++ls2) (l1++l2).
  Proof.
    intros isl1 isl2.
    induction isl1; rewrite <- H; clear ls0 H.
    - induction ls1; simpl; trivial.
      destruct a; simpl.
      + apply is_interleaved_cons_nil_f; trivial.
      + apply is_interleaved_cons_simple. 
        rewrite app_ass.
        apply is_interleaved_cons_list; trivial.
    - apply is_interleaved_cons_simple; trivial.
  Qed.

  Lemma is_interleaved_map {A B:Type} (f:A->B) ls (l:list A) :
    is_interleaved ls l ->
    is_interleaved (map (map f) ls) (map f l).
  Proof.
    intros isl.
    induction isl; simpl; intros.
    - rewrite concat_map.
      apply is_interleaved_concat.
      apply Permutation_map; trivial.
    - rewrite <- H; simpl.
      apply is_interleaved_cons_simple; trivial.
  Qed.

  Lemma is_interleaved_filter {A:Type} f ls (l:list A) :
    is_interleaved ls l ->
    is_interleaved (map (filter f) ls) (filter f l).
  Proof.
    intros isl.
    induction isl; simpl; intros.
    - rewrite concat_filter.
      apply is_interleaved_concat.
      apply Permutation_map; trivial.
    - rewrite <- H; simpl.
      destruct (f x); trivial.
      apply is_interleaved_cons_simple; trivial.
  Qed.

  Lemma is_interleaved_filter_nil_f {A:Type} {ls} {l:list A} :
    is_interleaved ls l ->
    is_interleaved (filter_nil ls) l.
  Proof.
    intros isl.
    - induction isl; simpl in *.
      + unfold filter_nil. rewrite <- (Permutation_filter _ _ _ H).
        generalize (is_interleaved_concat_simple (filter_nil ls1)); intros isl.
        rewrite concat_filter_nil in isl; trivial.
      + rewrite <- H; simpl.
        apply is_interleaved_cons_simple.
        destruct lh; simpl; trivial.
        apply is_interleaved_cons_nil_f; trivial.
  Qed.

  Lemma is_interleaved_filter_nil {A:Type} ls (l:list A) :
    is_interleaved ls l <->
    is_interleaved (filter_nil ls) l.
  Proof.
    split; intros isl.
    - apply is_interleaved_filter_nil_f; trivial.
    - revert ls isl.
      induction l; simpl; intros ls isl.
      + invcs isl.
        rewrite H.
        apply concat_nil_r in H.
        induction ls; trivial.
        * apply (is_interleaved_concat_simple nil).
        * { destruct a; simpl in *.
            - apply is_interleaved_cons_nil_f; auto.
            - rewrite H1 in H.
              invcs H.
              discriminate.
          } 
      + invcs isl.
        * symmetry in H1.
          destruct (Permutation_filter_pullback_r H1) as [ll [? perm2]]; subst.
          fold (@filter_nil A) in *; rewrite concat_filter_nil in *.
          apply is_interleaved_concat; symmetry; trivial.
        * symmetry in H3.
          destruct (filter_perm_head H3).
          symmetry in H3.
          rewrite H; simpl.
          apply is_interleaved_cons_simple.
          apply IHl.
          { replace (filter_nil (lh :: ls1 ++ x)) with (filter_nil (lh::ls1)); trivial.
            - apply is_interleaved_filter_nil_f; trivial.
            - generalize (Permutation_filter not_nil _ _ H); intros perm2.
              rewrite <- H3 in perm2.
              rewrite filter_app in perm2.
              generalize (Permutation_filter not_nil _ _ H3); intros perm3.
              unfold filter_nil in *.
              rewrite filter_filter in perm3.
              rewrite <- H3 in perm3.
              rewrite <- perm3 in perm2.
              rewrite filter_filter in perm2.
              generalize (Permutation_app_inv_l (filter not_nil ((a :: lh) :: ls1)) nil (filter not_nil x)); intros inv.
              rewrite app_nil_r in inv.
              specialize (inv perm2).
              apply Permutation_nil in inv.
              simpl.
              rewrite filter_app, inv.
              rewrite app_nil_r; trivial.
          } 
  Qed.

  Lemma is_interleaved_cons_nil {A} ls (l:list A) :
    is_interleaved ls l <-> is_interleaved (nil :: ls) l.
  Proof.
    split; intros isl.
    - apply is_interleaved_cons_nil_f; trivial.
    - apply is_interleaved_filter_nil in isl.
      simpl in isl.
      apply is_interleaved_filter_nil; trivial.
  Qed.

  Lemma is_interleaved_app_cons_nil {A} ls1 ls2 (l:list A) :
    is_interleaved (ls1 ++ nil :: ls2) l <-> is_interleaved (ls1++ls2) l.
  Proof.
    rewrite <- (@Permutation_cons_app (list A) (ls1 ++ ls2) ls1 ls2)
    ; try reflexivity.
    symmetry.
    apply is_interleaved_cons_nil.
  Qed.
  
  Lemma is_interleaved_nil_r {A:Type} (ls:list (list A)) :
    is_interleaved ls nil <-> Forall (eq nil) ls.
  Proof.
    split; intros H.
    - apply is_interleaved_perm_concat in H.
      apply Permutation_nil in H.
      apply concat_nil_r in H.
      trivial.
    - generalize (is_interleaved_concat_simple ls); intros isl.
      apply concat_nil_r in H.
      rewrite H in isl; trivial.
  Qed.

  (*
    Lemma is_interleaved_concat_inside {A} {ls1 ls2 ls3} {l:list A} :
      is_interleaved (ls1++(concat ls2)::ls3) l ->
      is_interleaved (ls1++ls2++ls3) l.
    Proof.

    Lemma is_interleaved_distr {A} ls1 ls2 ls3 l2 (l:list A) :
          is_interleaved (ls1++ls2++ls3) l ->
          is_interleaved ls2 l2 ->
          is_interleaved (ls1++l2::ls3) l.
    Proof.
   *)

  (*
    Lemma is_interleaved_In {A:Type} (ls:list (list A)) l x :
      is_interleaved ls l ->
      In x l <-> exists l', In l' ls /\ In x l'.
    Proof.
      intros isl.
      rewrite (is_interleaved_perm_concat isl).
      apply concat_In.
    Qed.
   *)

  Lemma is_interleaved_lookup_none {A B} {dec:EqDec A eq} {ls:list (list (A*B))} l x :
    is_interleaved ls l ->
    lookup dec l x = None <->
    Forall (fun ll => lookup dec ll x = None) ls.
  Proof.
    intros isl.
    split; intros.
    - rewrite Forall_forall; intros.
      case_eq (lookup dec x0 x); trivial; intros.
      apply lookup_in in H1.
      generalize (is_interleaved_In _ _ (x,b) isl); intros [Hf Hb].
      cut_to Hb.
      + apply in_dom in Hb.
        destruct (in_dom_lookup dec Hb); congruence.
      + eauto.
    - apply is_interleaved_perm_concat in isl.
      case_eq (lookup dec l x); trivial; intros.
      apply lookup_in in H0.
      rewrite isl in H0.
      apply concat_In in H0.
      destruct H0 as [? [inn1 inn2]].
      rewrite Forall_forall in H.
      specialize (H _ inn1).
      apply lookup_none_nin in H.
      apply in_dom in inn2.
      congruence.
  Qed.
  
  Lemma is_interleaved_lookup_some {A B} {dec:EqDec A eq} {ls:list (list (A*B))} l x v :
    is_interleaved ls l ->
    lookup dec l x = Some v ->
    exists ll, In ll ls /\ lookup dec ll x = Some v.
  Proof.
    intros isl; induction isl; intros lo.
    - destruct (concat_lookup_some_break lo) as [ll1 [ll2 [ll3 [eqq [inn nin]]]]].
      subst.
      exists ll2; split; trivial.
      rewrite <- H.
      rewrite in_app_iff; simpl; eauto.
    - simpl in lo.
      destruct x0.
      destruct (dec x a); unfold equiv in *.
      + invcs lo.
        exists ((a,v)::lh); simpl.
        split.
        * rewrite <- H; simpl; eauto.
        * match_destr; congruence.
      + destruct (IHisl lo) as [ll [inn1 inn2]].
        simpl in inn1.
        destruct inn1.
        * subst.
          exists ((a,b)::ll); simpl.
          { split.
            - rewrite <- H; simpl; eauto.
            - rewrite inn2.
              destruct (dec x a); congruence.
          }
        * exists ll; split; trivial.
          rewrite <- H; simpl; eauto.
  Qed.

  Lemma is_interleaved_disjoint_lookup_equiv {A B} {dec:EqDec A eq} {ls:list (list (A*B))} :
    all_disjoint (map domain ls) ->
    forall l1 l2,
      is_interleaved ls l1 ->
      is_interleaved ls l2 ->
      lookup_equiv l1 l2.
  Proof.
    intros ad l1 l2 isl1 isl2 x.
    case_eq (lookup dec l1 x).
    - intros ? inn.
      destruct (is_interleaved_lookup_some _ _ _ isl1 inn)
        as [ll [inn1 inn2]].
      case_eq (lookup dec l2 x).
      + intros ? inn'.
        destruct (is_interleaved_lookup_some _ _ _ isl2 inn')
          as [ll' [inn1' inn2']].
        cut (ll = ll').
        { congruence. }
        generalize (is_interleaved_both_perm isl1 isl2); intros perm.
        apply lookup_in in inn.
        apply lookup_in in inn'.
        rewrite perm in inn.
        apply lookup_in_domain in inn2.
        apply lookup_in_domain in inn2'.
        eapply all_disjoint_domain_has_same_eq; eauto.
      + intros inn'.
        apply (is_interleaved_lookup_none _ x isl2) in inn'.
        apply (is_interleaved_lookup_none _ x isl1) in inn'.
        congruence.
    - intros inn'.
      apply (is_interleaved_lookup_none _ x isl1) in inn'.
      apply (is_interleaved_lookup_none _ x isl2) in inn'.
      congruence.
  Qed.

  Lemma is_interleaved_disjoint_update_first {A B} dec ls (l:list (A*B)) v d:
    all_disjoint (map domain ls) ->
    is_interleaved ls l -> 
    is_interleaved (map (fun l0 : list (A * B) => update_first dec l0 v d) ls)
                   (update_first dec l v d).
  Proof.
    intros disj isl.
    revert disj.
    induction isl; intros disj.
    - rewrite <- (Permutation_map domain H) in disj.
      rewrite update_first_concat_disjoint_push by trivial.
      econstructor.
      rewrite H; trivial.
    - rewrite <- (Permutation_map domain H) in disj.
      destruct x; simpl in *.
      cut_to IHisl.
      + rewrite <- H; clear ls2 H; simpl.
        assert (nin: Forall (fun x => ~ In a x) (map domain ls1)).
        { invcs disj.
          revert H1; apply Forall_impl.
          intros ? disj.
          apply disjoint_cons_inv1 in disj; tauto.
        } 
        destruct (dec v a); simpl.
        * subst.
          { replace (map (fun l0 : list (A * B) => update_first dec l0 a d) ls1)
              with (map id ls1).
            - rewrite map_id.
              eapply is_interleaved_cons; eauto.
            - apply map_ext_in; intros.
              rewrite nin_update; trivial.
              apply lookup_nin_none.
              rewrite Forall_forall in nin.
              apply nin.
              apply in_map_iff.
              eauto.
          } 
        * econstructor; eauto.
      + invcs disj.
        constructor; trivial.
        revert H2; apply Forall_impl.
        intros ? disj.
        apply disjoint_cons_inv1 in disj; tauto.
  Qed.

  Lemma is_interleaved_singleton_inv {A B} (l1 l2:list (A*B)) :
    is_interleaved (l1::nil) l2 -> l1 = l2.
  Proof.
    revert l1; induction l2; intros l1 isl.
    - apply is_interleaved_nil_r in isl.
      invcs isl; trivial.
    - invcs isl.
      + symmetry in H1; apply Permutation_length_1_inv in H1; subst.
        simpl in H; rewrite app_nil_r in H; subst; simpl.
        rewrite app_nil_r; trivial.
      + symmetry in H3.
        apply Permutation_length_1_inv in H3.
        invcs H3.
        f_equal; auto.
  Qed.

  
  Lemma is_interleaved_cons_inv {A B} {dec:EqDec A eq} (a:(A*B)) l1 l2 l3 :
    all_disjoint (map domain ((a::l1)::l2)) ->
    is_interleaved ((a::l1)::l2) (a::l3) ->
    is_interleaved (l1::l2) l3.
  Proof.
    revert l1 l3.
    induction l2; simpl; intros l1 l3 disj isl.
    - apply is_interleaved_singleton_inv in isl.
      invcs isl.
      apply is_interleaved_refl.
    - invcs isl.
      + assert (inn1:In(a::l1) ls1).
        { rewrite H1; trivial; simpl; eauto. }
        destruct (in_split _ _ inn1)
          as [ll1 [ll2 eqq]]; subst; clear inn1.
        symmetry in H1.
        apply Permutation_cons_app_inv in H1.
        assert (nin:~ In a (concat ll1)).
        { intros inn.
          assert (inn1:In a (concat (ll1 ++ ll2))).
          { rewrite concat_app, in_app_iff; eauto. }
          rewrite <- H1 in inn1; simpl in inn1.
          rewrite in_app_iff in inn1.
          invcs disj.
          invcs H3.
          destruct a; simpl in *.
          destruct inn1 as [inn1|inn1].
          - apply in_dom in inn1.
            apply (H5 a); simpl; eauto.
          - apply concat_In in inn1.
            destruct inn1 as [? [inn1 inn2]].
            rewrite Forall_forall in H6.
            specialize (H6 (domain x)).
            cut_to H6.
            + apply in_dom in inn2.
              apply (H6 a); simpl; eauto.
            + apply in_map; trivial.
        }
        rewrite concat_app in H.
        case_eq (concat ll1); [intros eqq | intros ?? eqq]
        ; rewrite eqq in *.
        * simpl in H; invcs H.
          apply concat_nil_r in eqq.
          change (is_interleaved ((l1::nil)++a0 :: l2) (l1 ++ nil++concat ll2)).
          { apply is_interleaved_app.
            - apply is_interleaved_refl.
            - rewrite H1.
              apply is_interleaved_app.
              + apply is_interleaved_nil_r; trivial.
              + apply is_interleaved_concat_simple.
          } 
        * invcs H.
          simpl in nin; intuition.
      + destruct (Permutation_in_nin_inv H3 a) as [eqq perm].
        * simpl; eauto.
        * invcs disj.
          invcs H1.
          rewrite Forall_forall in *.
          destruct a; simpl in *.
          { rewrite in_app_iff; intros [inn|inn].
            - apply in_dom in inn.
              apply (H5 a); simpl; eauto.
            - apply concat_In in inn.
              destruct inn as [? [inn1 inn2]].
              specialize (H6 (domain x)).
              cut_to H6.
              + apply in_dom in inn2.
                apply (H6 a); simpl; eauto.
              + apply in_map; trivial.
          }
        * invcs eqq.
          rewrite perm in H2; trivial.
  Qed.

  Lemma is_interleaved_in_dom_cons_inv {A B} {dec:EqDec A eq} {a:(A*B)} {l1 l2 l3} :
    is_interleaved (l1::l2) (a::l3) ->
    all_disjoint (map domain (l1::l2)) ->
    In (fst a) (domain l1) ->
    exists l1', l1 = a::l1'.
  Proof.
    intros isl disj inn.
    destruct a; simpl in *.
    invcs isl.
    - assert (perm:Permutation (filter_nil ls1) (filter_nil (l1::l2))).
      { apply Permutation_filter; trivial. }
      rewrite <- concat_filter_nil in H.
      assert (nnil:not_nil l1 = true).
      { destruct l1; simpl in *; tauto. }
      simpl in perm; rewrite nnil in perm.
      case_eq (filter_nil ls1); [intros eqq | intros ?? eqq]
      ; rewrite eqq in *; simpl in *; try discriminate.
      destruct l; simpl in *.
      + cut False; [contradiction | ].
        revert eqq; clear.
        induction ls1; simpl; try discriminate.
        destruct a; simpl; trivial; try discriminate.
      + invcs H.
        destruct (Permutation_in_nin_inv perm (a,b))
          as [eqq2 perm2].
        * simpl; eauto.
        * rewrite concat_In.
          intros [x [inn1 inn2]].
          invcs disj.
          rewrite Forall_forall in H2.
          specialize (H2 (domain x)).
          { cut_to H2.
            - apply (H2 a); trivial; eapply in_dom; eauto.
            - apply in_map; trivial.
              unfold filter_nil in inn1.
              apply filter_In in inn1; tauto.
          }
        * subst; eauto.
    - destruct (Permutation_in_nin_inv H3 (a,b))
        as [eqq perm].
      + simpl; eauto.
      + rewrite concat_In.
        intros [x [inn1 inn2]].
        invcs disj.
        rewrite Forall_forall in H1.
        specialize (H1 (domain x)).
        cut_to H1.
        * apply (H1 a); trivial; eapply in_dom; eauto.
        * apply in_map; trivial.
      + subst; eauto.
  Qed.
  
  Lemma is_interleaved_in_cons_inv {A B} {dec:EqDec A eq} {a:(A*B)} {l1 l2 l3} :
    is_interleaved (l1::l2) (a::l3) ->
    all_disjoint (map domain (l1::l2)) ->
    In a l1 ->
    exists l1', l1 = a::l1'.
  Proof.
    intros; eapply is_interleaved_in_dom_cons_inv; eauto.
    destruct a.
    eapply in_dom; eauto.
  Qed.

  Lemma is_interleaved_cons_dom_eq {A B} {dec:EqDec A eq} {a:A} {b b':B} {l1 l2 l3} :
    is_interleaved (((a, b)::l1)::l2) ((a,b')::l3) ->
    all_disjoint (map domain (((a,b)::l1)::l2)) ->
    b = b'.
  Proof.
    intros isl disj.
    destruct (is_interleaved_in_dom_cons_inv isl disj); simpl; [eauto | ].
    invcs H; trivial.
  Qed.

  
  Lemma is_interleaved_cons_dom_inv {A B} {dec:EqDec A eq} {a:A} {b b':B} {l1 l2 l3} :
    is_interleaved (((a, b)::l1)::l2) ((a,b')::l3) ->
    all_disjoint (map domain (((a,b)::l1)::l2)) ->
    is_interleaved (l1::l2) l3.
  Proof.
    intros isl disj.
    rewrite <- (is_interleaved_cons_dom_eq isl disj) in isl.
    eapply is_interleaved_cons_inv; eauto.
  Qed.

End interleaving.

Section close_enough.
  
  Definition close_enough_lists {A B:Type} (l1 l2:list (A*B)) :=
    exists (ls:list (list (A*B))), 
      all_disjoint (map domain ls) /\
      is_interleaved ls l1 /\
      is_interleaved ls l2.

  Global Instance close_enough_lists_refl {A B} : Reflexive (@close_enough_lists A B).
  Proof.
    intros x.
    exists (x::nil); simpl; repeat split.
    - repeat constructor.
    - apply is_interleaved_refl.
    - apply is_interleaved_refl.
  Qed.        

  Global Instance close_enough_lists_symm {A B} : Symmetric (@close_enough_lists A B).
  Proof.
    intros x y [l [disj [isl1 isl2]]].
    exists l; eauto.
  Qed.
  
  (* This should be true, but would take more work to prove.
       This can be proven by exhibiting a finer witness.  In general, in fact,
       we can group things by clumping all the same domain stuff together *)
  (*
    Global Instance close_enough_lists_trans {A B} : Transitive (@close_enough_lists A B).
    Proof.
      intros x y z [xyl [xydisj [xyisl1 xyisl2]]] [yzl [yzdisj [yzisl1 yzisl2]]].
      red.
      assert (perm:Permutation xyl yzl).
      - apply is_interleaved_perm_concat in xyisl2.
        apply is_interleaved_perm_concat in yzisl1.
        rewrite xyisl2 in yzisl1.
      
    Qed.
   *)
  
  Global Instance close_enough_lists_lookup_equiv {A B} {dec:EqDec A eq} :
    subrelation (@close_enough_lists A B) lookup_equiv.
  Proof.
    intros l1 l2 [l [disj [isl1 isl2]]].
    eapply is_interleaved_disjoint_lookup_equiv; eauto.
  Qed.

  Lemma close_enough_update_first {A B} dec (l1 l2:list (A*B)) v d :
    close_enough_lists l1 l2 ->
    close_enough_lists (update_first dec l1 v d) (update_first dec l2 v d).
  Proof.
    intros [l [disj [isl1 isl2]]].
    red.
    exists (map (fun l => update_first dec l v d) l).
    repeat split.
    - rewrite map_map.
      replace (map (fun x : list (A * B) => domain (update_first dec x v d)) l)
        with (map domain l); trivial.
      apply map_ext; intros.
      rewrite domain_update_first; trivial.
    - apply is_interleaved_disjoint_update_first; trivial.
    - apply is_interleaved_disjoint_update_first; trivial.
  Qed.

  Hint Resolve disjoint_nil_l disjoint_nil_r : list.
  
  Lemma close_enough_lists_cons {A B} {dec:EqDec A eq} (a:(A*B)) l1 l2 : 
    close_enough_lists l1 l2 ->
    close_enough_lists (a::l1) (a::l2).
  Proof.
    destruct a.
    intros [l [disj [isl1 isl2]]].
    destruct (in_in_split_domain_or dec l a)
      as [[m1 [ma [m2 [eqq [inn nin]]]]]|nin].
    - subst.
      exists (m1++((a,b)::ma)::m2).
      assert (perm1: Permutation (m1 ++ ((a, b) :: ma) :: m2) (((a, b) :: ma)::m1 ++ m2)).
      { rewrite <- Permutation_cons_app; try reflexivity. }
      assert (perm2: Permutation (m1 ++ ma :: m2) (ma::m1 ++ m2)).
      { rewrite <- Permutation_cons_app; try reflexivity. }
      repeat rewrite perm1.
      repeat rewrite perm2 in *.
      repeat split.
      + repeat rewrite map_app in *; simpl in *.
        invcs disj.
        constructor; trivial.
        revert H1; apply Forall_impl; intros.
        intros ?; simpl; intros inn1 inn2.
        eapply H; try eapply inn2.
        destruct inn1; subst; trivial.
      + econstructor; eauto.
      + econstructor; eauto.
    - exists (((a,b)::nil)::l); simpl.
      repeat split.
      + constructor; trivial.
        rewrite Forall_map.
        revert nin; apply Forall_impl; intros.
        apply disjoint_cons1; auto with list.
      + econstructor; eauto.
        apply is_interleaved_cons_nil in isl1; trivial.
      + econstructor; eauto.
        apply is_interleaved_cons_nil in isl2; trivial.
  Qed.

  Lemma close_enough_lists_cons_invs {A B} {dec:EqDec A eq} (a:A) (b b':B) l1 l2 :
    close_enough_lists ((a,b)::l1) ((a,b')::l2) ->
    b = b' /\ close_enough_lists l1 l2.
  Proof.
    intros [ll [disj [isl1 isl2]]].
    assert (inn1:In a (domain (concat ll))).
    { apply is_interleaved_perm_concat in isl1.
      rewrite <- isl1; simpl; eauto.
    }
    destruct (in_in_split_domain_first dec inn1)
      as [m1 [ma [m2 [eqq [inn nin]]]]]
    ; subst; clear inn1.
    rewrite <- Permutation_cons_app in isl1; try reflexivity.
    rewrite <- Permutation_cons_app in isl2; try reflexivity.
    rewrite <- Permutation_cons_app in disj; try reflexivity.
    assert(inn1:In (a, b) ma).
    { apply is_interleaved_perm_concat in isl1.
      assert (inn2:In (a,b) (concat (ma :: m1 ++ m2))).
      { rewrite <- isl1; simpl; eauto. }
      simpl in inn2.
      rewrite concat_app in inn2.
      repeat rewrite in_app_iff in inn2.
      invcs disj; rewrite Forall_forall in H1.
      destruct inn2 as [inn2|[inn2|inn2]]; trivial.
      - apply concat_In in inn2.
        destruct inn2 as [x [inn3 inn4]].
        specialize (H1 (domain x)).
        cut_to H1.
        + elim (H1 a); trivial; eapply in_dom; eauto.
        + rewrite map_app, in_app_iff.
          left; apply in_map; trivial.
      - apply concat_In in inn2.
        destruct inn2 as [x [inn3 inn4]].
        specialize (H1 (domain x)).
        cut_to H1.
        + elim (H1 a); trivial; eapply in_dom; eauto.
        + rewrite map_app, in_app_iff.
          right; apply in_map; trivial.
    }
    destruct (is_interleaved_in_cons_inv isl1 disj inn1) as [mm ?]; subst.
    apply is_interleaved_cons_inv in isl1; trivial.
    split.
    - apply (is_interleaved_cons_dom_eq isl2); trivial.
    - apply is_interleaved_cons_dom_inv in isl2; trivial.
      exists (mm::m1++m2); repeat split; trivial.
      simpl in disj.
      apply all_disjoint_cons_inv in disj.
      tauto.
  Qed.
  
  Lemma close_enough_lists_cons_inv {A B} {dec:EqDec A eq} (a:(A*B)) l1 l2 :
    close_enough_lists (a::l1) (a::l2) ->
    close_enough_lists l1 l2.
  Proof.
    destruct a.
    apply close_enough_lists_cons_invs.
  Qed.
  
End close_enough.