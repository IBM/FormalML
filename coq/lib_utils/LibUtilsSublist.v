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

(** Support for defining and reasoning about sub-lists. *)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Permutation.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Lia.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import LibUtilsSortingAdd.
Require Import LibUtilsAssoc.
Require Import Program.

Section Sublist.
  (** * Sublists *)
  
  Section sublist.
    Context {A:Type}.
    Inductive sublist : list A -> list A -> Prop :=
    | sublist_nil : sublist nil nil
    | sublist_cons :
        forall x l1 l2, sublist l1 l2 -> sublist (x::l1) (x::l2)
    | sublist_skip : 
        forall x l1 l2, sublist l1 l2 -> sublist l1 (x::l2)
    .
    
    Hint Constructors sublist : fml.
    
    Lemma sublist_In {l1 l2:list A} :
      sublist l1 l2 -> forall x, In x l1 -> In x l2.
    Proof.
      induction 1; simpl; intuition.
    Qed.

    Lemma sublist_nil_l l : sublist nil l.
    Proof.
      induction l; intuition.
    Qed.

    Lemma sublist_nil_r l : sublist l nil -> l = nil.
    Proof.
      inversion 1; trivial.
    Qed.
    
    Global Instance sublist_incl_sub : subrelation sublist (@incl A).
    Proof.
      intros l1 l2 subl x inx.
      eapply sublist_In; eauto.
    Qed.

    
    Hint Immediate sublist_nil_l : fml.
    
    Global Instance sublist_pre : PreOrder sublist.
    Proof.
      constructor; red; intros l; [induction l; intuition | ].
      intros y z; revert l y. induction z.
      - intros.
        apply sublist_nil_r in H0; subst.
        apply sublist_nil_r in H; subst.
        auto with fml.
      - intros.
        inversion H0; subst; eauto 3 with fml.
        inversion H; subst; eauto 3 with fml.
    Qed.

    Lemma sublist_trans l1 l2 l3:
      sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
    Proof.
      intros.
      apply (PreOrder_Transitive l1 l2 l3); assumption.
    Qed.
    
    Lemma sublist_length {l1 l2} : sublist l1 l2 -> length l1 <= length l2.
    Proof.
      revert l1. induction l2; simpl; intros.
      - apply sublist_nil_r in H; subst; auto.
      - inversion H; subst; simpl; auto with arith.
    Qed.

    Lemma sublist_length_eq {l1 l2} :
      sublist l1 l2 -> length l1 = length l2 -> l1 = l2.
    Proof.
      revert l1; induction l2; simpl.
      - intros; apply sublist_nil_r in H; subst; auto.
      - inversion 1; subst; simpl; intros.
        + f_equal; auto with arith.
        + apply sublist_length in H2. lia.
    Qed.

    Global Instance sublist_antisymm : Antisymmetric (list A) eq sublist.
    Proof.
      red; intros x y sub1 sub2.
      apply (sublist_length_eq sub1).
      apply sublist_length in sub1.
      apply sublist_length in sub2.
      lia.
    Qed.

    Global Instance sublist_part : PartialOrder eq sublist.
    Proof.
      unfold PartialOrder, relation_equivalence, relation_conjunction,
      predicate_equivalence, predicate_intersection, Basics.flip; simpl.
      split; intros; subst; trivial; intuition.
      apply sublist_antisymm; trivial.
    Qed.
    
    Global Instance sublist_NoDup : Proper (sublist --> impl) (@NoDup A).
    Proof.
      repeat red; unfold flip.
      induction x; simpl; intros.
      - apply sublist_nil_r in H; subst; auto.
      - inversion H0; subst.
        inversion H; subst; auto.
        constructor; auto.
        intro inn; apply H3.
        eapply sublist_In; eauto.
    Qed.

    Hint Constructors sublist : fml.
    
    Lemma sublist_app {a1 b1 a2 b2:list A}:
      sublist a1 b1 ->
      sublist a2 b2 ->
      sublist (a1 ++ a2) (b1 ++ b2).
    Proof.
      revert a1 a2 b2.
      induction b1; inversion 1; subst; simpl; eauto with fml.
    Qed.

    Lemma sublist_app_l (l1 l2:list A) : sublist l1 (l1 ++ l2).
    Proof.
      induction l1; simpl.
      - apply sublist_nil_l.
      - apply sublist_cons. trivial.
    Qed.

    Lemma sublist_app_r (l1 l2:list A) : sublist l2 (l1 ++ l2).
    Proof.
      induction l1; simpl.
      - reflexivity.
      - apply sublist_skip. trivial.
    Qed.

    Lemma filter_sublist f (l:list A) : sublist (filter f l) l.
    Proof.
      induction l; simpl.
      - reflexivity.
      - match_destr.
        + apply sublist_cons; trivial.
        + apply sublist_skip; trivial.
    Qed.
    
  End sublist.

  Lemma cut_down_to_sublist
        {A B} {dec:EqDec A eq}
        (l:list (A*B)) (l2:list A) :
    sublist (cut_down_to l l2) l.
  Proof.
    unfold cut_down_to.
    apply filter_sublist.
  Qed.

  Hint Constructors sublist : fml.

  Lemma sublist_map {A B} {l1 l2} (f:A->B) :
    sublist l1 l2 -> sublist (map f l1) (map f l2).
  Proof.
    revert l1; induction l2; intros.
    - apply sublist_nil_r in H; subst; simpl; auto with fml.
    - inversion H; subst; simpl; auto with fml.
  Qed.

  Lemma sublist_domain {A B} {l1 l2:list(A*B)} :
    sublist l1 l2 -> sublist (domain l1) (domain l2).
  Proof.
    intros; apply sublist_map; trivial.
  Qed.

  Lemma sublist_set_inter {A} dec (l1 l2 l3:list A):
    sublist l1 l3 ->
    sublist (set_inter dec l1 l2) l3.
  Proof.
    revert l1 l2.
    induction l3; intros.
    - apply sublist_nil_r in H; subst; simpl; trivial with fml.
    - inversion H; subst.
      + simpl.
        match_destr; eauto with fml.
      + eauto with fml.
  Qed.
  
  Global Instance Forall_sublist {A} {P:A->Prop} :
    Proper (sublist --> impl) (Forall P).
  Proof.
    repeat red; unfold flip.
    induction x; intros.
    - apply sublist_nil_r in H; subst; trivial.
    - inversion H0; clear H0; subst.
      inversion H; clear H; subst; auto.
  Qed.

  Lemma forallb_sublist {A} f (l1 l2:list A) :
    sublist l1 l2 ->
    forallb f l2 = true ->
    forallb f l1 = true.
  Proof.
    intros.
    eapply forallb_incl; eauto.
    apply sublist_incl_sub; trivial.
  Qed.

  Lemma forallb_ordpairs_sublist {A} f (l1 l2:list A) :
    sublist l1 l2 ->
    forallb_ordpairs f l2 = true ->
    forallb_ordpairs f l1 = true.
  Proof.
    revert l2.
    induction l1; simpl; trivial; intros.
    induction l2; simpl; inversion H; subst; simpl in * ;
      rewrite andb_true_iff in *.
    - rewrite (IHl1 l2); intuition.
      eapply forallb_sublist; eauto.
    - intuition.
  Qed.

  Lemma forallb_ordpairs_refl_sublist {A} f (l1 l2:list A) :
    sublist l1 l2 ->
    forallb_ordpairs_refl f l2 = true ->
    forallb_ordpairs_refl f l1 = true.
  Proof.
    repeat rewrite forallb_ordpairs_refl_conj.
    repeat rewrite andb_true_iff; intuition.
    - eapply forallb_ordpairs_sublist; eauto.
    - eapply forallb_sublist; eauto.
  Qed.

  Global Instance StronglySorted_sublist {A} {R:A->A->Prop} : Proper (sublist --> impl) (StronglySorted R).
  Proof.
    repeat red; unfold flip.
    induction x; simpl; intros.
    - apply sublist_nil_r in H; subst; trivial.
    - inversion H0; clear H0; subst.
      inversion H; clear H; subst; auto 3.
      rewrite <- H2 in H4; constructor; auto.
  Qed.

  Lemma is_list_sorted_sublist {A} {R} {Rdec} {l l':list A}
        `{Transitive A R} :
    @is_list_sorted A R Rdec l = true ->
    sublist l' l ->
    is_list_sorted Rdec l' = true.
  Proof.
    repeat rewrite sorted_StronglySorted by auto.
    intros ? sl.
    rewrite sl.
    trivial.
  Qed.

  Hint Immediate sublist_nil_l : fml.

  Lemma StronglySorted_incl_sublist {A R l1 l2} `{EqDec A eq} `{StrictOrder A R} : 
    StronglySorted R l1 ->
    StronglySorted R l2 ->
    (forall x : A, In x l1 -> In x l2) ->
    sublist l1 l2.
  Proof.
    intros. 
    generalize (StronglySorted_NoDup _ H1).
    generalize (StronglySorted_NoDup _ H2).
    revert l1 H1 H2 H3.
    induction l2; simpl.
    - destruct l1; simpl; auto 1 with fml.
      intros. specialize (H3 a); intuition.
    - intros. inversion H2; subst.
      destruct l1; auto 1 with fml.
      simpl in *.
      inversion H1; subst.
      inversion H4; inversion H5; subst.
      destruct (a == a0); unfold Equivalence.equiv, complement in *; subst.
      unfold equiv in *.
      + apply sublist_cons. apply IHl2; trivial.
        intros x inn.
        specialize (H3 x); intuition. subst; intuition.
      + apply sublist_skip. apply IHl2; auto.
        simpl; intros x inn.
        generalize (H3 a0).
        specialize (H3 _ inn). intuition; subst.
        * intuition.
        * rewrite Forall_forall in H9,H11.
          specialize (H11 _ H3).
          specialize (H9 _ H14).
          rewrite H9 in H11.
          eelim irreflexivity; eauto.
  Qed.

  Lemma Sorted_incl_sublist {A R l1 l2} `{EqDec A eq} `{StrictOrder A R}: 
    Sorted R l1 ->
    Sorted R l2 ->
    (forall x : A, In x l1 -> In x l2) ->
    sublist l1 l2.
  Proof.
    intros.
    apply StronglySorted_incl_sublist; trivial;
      apply Sorted_StronglySorted; trivial; apply StrictOrder_Transitive.
  Qed.

  Lemma Sorted_incl_both_eq {A R l1 l2} `{EqDec A eq} `{StrictOrder A R}: 
    Sorted R l1 ->
    Sorted R l2 ->
    (forall x : A, In x l1 -> In x l2) ->
    (forall x : A, In x l2 -> In x l1) ->
    l1 = l2.
  Proof.
    intros.
    apply sublist_antisymm; apply Sorted_incl_sublist; trivial.
  Qed.

  Lemma insertion_sort_equivlist_strong {A R R_dec} `{EqDec A eq} `{StrictOrder A R} l l' (contr:asymmetric_over R l) :
    equivlist l l' ->
    @insertion_sort A R R_dec l = 
    @insertion_sort A R R_dec l'.
  Proof.
    intros.
    generalize (equivlist_insertion_sort_strong R_dec contr H1); intros.
    apply Sorted_incl_both_eq; try apply insertion_sort_Sorted.
    intros. eapply equivlist_in; eauto.
    intros. symmetry in H2. eapply equivlist_in; eauto.
  Qed.

  Lemma insertion_sort_equivlist {A R R_dec} `{EqDec A eq} `{StrictOrder A R}  (contr:forall x y,  ~R x y -> ~R y x -> x = y) l l' :
    equivlist l l' ->
    @insertion_sort A R R_dec l = 
    @insertion_sort A R R_dec l'.
  Proof.
    intros.
    apply insertion_sort_equivlist_strong; eauto.
    eapply asymmetric_asymmetric_over; trivial.
  Qed.

  Lemma sublist_skip_l {A} (a:A) {l1 l2} :
    sublist (a::l1) l2 ->
    sublist l1 l2.
  Proof.
    revert l1.
    induction l2; inversion 1; subst.
    - apply sublist_skip; trivial.
    - apply sublist_skip. eauto.
  Qed.

  Lemma sublist_cons_eq_inv {A a l1 l2} :
    @sublist A (a::l1) (a::l2) ->
    sublist l1 l2.
  Proof.
    inversion 1; subst; trivial.
    rewrite <- H2. apply sublist_skip; reflexivity.
  Qed.
  
  Lemma sublist_filter {A} (f:A->bool) {l1 l2} :
    sublist l1 l2 -> sublist (filter f l1) (filter f l2).
  Proof.
    revert l1. induction l2; simpl; intros.
    - apply sublist_nil_r in H; subst; simpl; auto 1 with fml.
    - inversion H; subst.
      + specialize (IHl2 _ H2); simpl.
        destruct (f a); [apply sublist_cons | ]; congruence.
      + specialize (IHl2 _ H2); simpl.
        destruct (f a); [apply sublist_skip | ]; congruence.
  Qed.
  
  Lemma sublist_cons_inv' {A B l1 a l2} :
    sublist l1(a::l2) ->
    NoDup (@domain A B (a::l2)) ->
    (exists l',
        l1 = a::l' /\ sublist l' l2)
    \/
    (~ In (fst a) (domain l1)
     /\ sublist l1 l2).
  Proof.
    inversion 1; subst.
    intuition; eauto.
    intros; right. split; trivial.
    generalize (sublist_In (sublist_domain H2)); intros inn.
    inversion H0; subst.
    auto.
  Qed.

  Lemma sublist_cons_inv {A B l1 a l2 R R_dec} `{StrictOrder A R}:
    sublist l1(a::l2) ->
    @is_list_sorted A R R_dec (@domain _ B (a::l2)) = true ->
    (exists l',
        l1 = a::l' /\ sublist l' l2)
    \/
    (~ In (fst a) (domain l1)
     /\ sublist l1 l2).
  Proof.
    inversion 1; subst.
    intuition; eauto.
    intros; right. split; trivial.
    generalize (sublist_In (sublist_domain H3)); intros inn.
    apply is_list_sorted_NoDup in H1; eauto.
    inversion H1; subst.
    auto.
  Qed.

  Lemma sublist_cons_inv_simple {A l1} {a:A} {l2} :
    sublist l1(a::l2) ->
    NoDup (a::l2) ->
    (exists l',
        l1 = a::l' /\ sublist l' l2)
    \/
    (~ In a l1
     /\ sublist l1 l2).
  Proof.
    inversion 1; subst.
    intuition; eauto.
    intros; right. split; trivial.
    generalize (sublist_In H2); intros inn.
    inversion H0; subst.
    auto.
  Qed.
  
  Lemma sublist_dec {A}  {dec:EqDec A eq} (l1 l2 : list A) :
    {sublist l1 l2} + { ~ sublist l1 l2}.
  Proof.
    revert l1.
    induction l2; intros l1; destruct l1.
    - left; trivial with fml.
    - right; inversion 1.
    - left; apply sublist_nil_l.
    - destruct (a0 == a).
      + destruct (IHl2 l1).
        * left. rewrite e. eauto with fml.
        * right. rewrite e. intro subl.
          apply sublist_cons_eq_inv in subl.
          intuition.
      + destruct (IHl2 (a0::l1)).
        * left. apply sublist_skip; trivial.
        * right; inversion 1; subst; intuition.
  Defined.

  Lemma sublist_remove {A} dec (x:A) l1 l2 :
    sublist l1 l2 ->
    sublist (remove dec x l1) (remove dec x l2).
  Proof.
    revert l1. induction l2; simpl; intros.
    - apply sublist_nil_r in H; subst; simpl; auto 1 with fml.
    - inversion H; subst.
      + specialize (IHl2 _ H2); simpl.
        match_destr. apply sublist_cons; auto.
      + specialize (IHl2 _ H2); simpl.
        match_destr.
        apply sublist_skip; auto.
  Qed.

  Lemma sublist_nin_remove {A} dec (l1 l2:list (A)) a :
    ~ In a l1 -> sublist l1 l2 -> sublist l1 (remove dec a l2).
  Proof.
    intros.
    apply (sublist_remove dec a) in H0.
    rewrite (nin_remove dec l1 a) in H0 by trivial.
    trivial.
  Qed.

  
  Lemma assoc_lookupr_nodup_sublist {A B} {R_dec:forall a a' : A, {a = a'} + {a <> a'}} {l1 l2} {a:A} {b:B} :
    NoDup (domain l2) ->
    sublist l1 l2 ->
    assoc_lookupr R_dec l1 a = Some b ->
    assoc_lookupr R_dec l2 a = Some b.
  Proof.
    revert a b l1.  induction l2; simpl; intros.
    - apply sublist_nil_r in H0; subst. simpl in *; discriminate.
    - destruct a; simpl.
      generalize (sublist_cons_inv' H0 H).
      inversion H; subst.
      destruct 1.
      + destruct H2 as [? [??]]; subst.
        simpl in H1.
        case_eq (assoc_lookupr R_dec x a0); [ intros? eqq | intros eqq]
        ; rewrite eqq in H1. 
        * inversion H1; clear H1; subst.
          rewrite (IHl2 _ _ _ H5 H3 eqq); trivial.
        * destruct (R_dec a0 a); inversion H1; subst.
          case_eq (assoc_lookupr R_dec l2 a); trivial.
          intros.
          apply assoc_lookupr_in in H2.
          apply in_dom in H2.
          congruence.
      + simpl in H2. destruct H2.
        rewrite (IHl2 _ _ _ H5 H3 H1); trivial.
  Qed.

  
  Lemma insertion_sort_insert_sublist_self {A R}
        R_dec (a:A) l :
    sublist l (@insertion_sort_insert A R R_dec a l).
  Proof.
    induction l; simpl.
    - apply sublist_skip; reflexivity.
    - match_destr.
      + apply sublist_skip; apply sublist_cons; reflexivity.
      + match_destr; try reflexivity.
        apply sublist_cons.
        eauto.
  Qed.

  Lemma insertion_sort_insert_sublist_prop {A R} {rstrict:StrictOrder R}
        (trich:forall a b, {R a b} + {a = b} + {R b a})
        R_dec a l1 l2:
    is_list_sorted R_dec l2 = true ->
    sublist l1 l2 ->
    sublist (@insertion_sort_insert A R R_dec a l1)
            (@insertion_sort_insert A R R_dec a l2).
  Proof.
    unfold Proper, respectful; intros; subst.
    revert l1 H H0. induction l2.
    - inversion 2; subst; simpl; reflexivity.
    - intros. apply sublist_cons_inv_simple in H0;
                [ | apply (is_list_sorted_NoDup R_dec); trivial].
      destruct H0 as [[?[??]]|[??]]; subst.
      + simpl. match_destr.
        * do 2 apply sublist_cons; eauto.
        * match_destr; apply sublist_cons; trivial.
          apply IHl2; trivial.
          eapply is_list_sorted_cons_inv; eauto.
      + simpl. match_destr.
        * rewrite IHl2; trivial; [| eapply is_list_sorted_cons_inv; eauto].
          rewrite insertion_sort_insert_forall_lt.
          { apply sublist_cons; apply sublist_skip; reflexivity. }
          apply sorted_StronglySorted in H; [| eapply StrictOrder_Transitive].
          inversion H; subst.
          revert H5. apply Forall_impl; intros.
          rewrite <- H2; trivial.
        * specialize (IHl2 l1).
          cut_to IHl2; trivial; [| eapply is_list_sorted_cons_inv; eauto].
          match_destr; [apply sublist_skip; trivial | ].
          destruct (trich a a0) as [[?|?]|?]; try congruence.
          subst.
          rewrite insertion_sort_insert_forall_lt; [ apply sublist_cons; trivial | ].
          rewrite H1.
          apply sorted_StronglySorted in H; [| eapply StrictOrder_Transitive].
          inversion H; subst. trivial.
  Qed.

  Lemma insertion_sort_sublist_proper {A R} {rstrict:StrictOrder R}
        (trich:forall a b, {R a b} + {a = b} + {R b a}) R_dec :
    Proper (sublist ==> sublist) (@insertion_sort A R R_dec).
  Proof.
    unfold Proper, respectful; intros.
    revert x H. induction y; simpl; inversion 1; subst; simpl; trivial.
    - specialize (IHy _ H2).
      apply insertion_sort_insert_sublist_prop; trivial.
      apply is_list_sorted_Sorted_iff.
      apply insertion_sort_Sorted.
    - rewrite IHy; trivial.
      apply insertion_sort_insert_sublist_self.
  Qed.
  
  Lemma sublist_of_sorted_sublist {A R} {rstrict:StrictOrder R}
        (trich:forall a b, {R a b} + {a = b} + {R b a})
        R_dec {l1 l2} : 
    sublist (@insertion_sort A R R_dec l1) l2 ->
    forall l1',
      sublist l1' l1 -> 
      sublist (insertion_sort R_dec l1') l2.
  Proof.
    intros.
    transitivity (insertion_sort R_dec l1); trivial.
    apply insertion_sort_sublist_proper; trivial.
  Qed.

  Lemma incl_NoDup_sublist_perm {A} {dec:EqDec A eq} {l1 l2:list A} :
    NoDup l1 ->
    incl l1 l2 ->
    exists l1', Permutation l1 l1' /\ sublist l1' l2.
  Proof.
    unfold incl.
    revert l1.
    induction l2; simpl.
    - destruct l1; simpl; eauto 3 with fml.
      intros ? inn.
      specialize (inn a); intuition.
    - intros.
      case_eq (In_dec dec a l1); intros.
      + destruct (in_split _ _ i) as [x [y ?]]; subst.
        assert (perm:Permutation (x ++ a :: y) (a::x ++ y))
          by (rewrite Permutation_middle; reflexivity).
        rewrite perm in H.
        inversion H; clear H; subst.
        destruct (IHl2 (x++y)) as [l1' [l1'perm l1'incl]]; trivial.
        * intros ? inn.
          { destruct (H0 a0); trivial.
            - rewrite perm; simpl; intuition.
            - subst. intuition.
          } 
        * exists (a::l1').
          { split.
            - rewrite perm.
              eauto.
            - apply sublist_cons.
              trivial.
          } 
      + destruct (IHl2 l1 H) as [x [perm subl]].
        * intros ? inn.
          destruct (H0 _ inn); subst; intuition.
        * exists x; split; trivial.
          apply sublist_skip.
          trivial.
  Qed.    

  Lemma incl_NoDup_length_le {A} {dec:EqDec A eq} {l1 l2:list A} :
    NoDup l1 ->
    incl l1 l2 ->
    length l1 <= length l2.
  Proof.
    intros nd inc.
    destruct (incl_NoDup_sublist_perm nd inc) as [l1' [perm subl]].
    rewrite (Permutation_length perm).
    apply sublist_length.
    trivial.
  Qed.

  Lemma find_fresh_from {A} {dec:EqDec A eq} (bad l:list A) :
    length l > length bad ->
    NoDup l ->
    {y | find (fun x : A => if in_dec equiv_dec x bad then false else true) l = Some y}.
  Proof.
    rewrite find_filter.
    unfold hd_error.
    match_case; eauto; intros.
    generalize (filter_nil_implies_not_pred _ l H); intros.
    cut (length l <= length bad); [intuition|].
    apply incl_NoDup_length_le; trivial.
    intros ? inn.
    specialize (H2 _ inn).
    match_destr_in H2.
  Defined.

  Lemma concat_sublist {A} (ls:list (list A)) : 
    Forall (fun x : list A => sublist x (concat ls)) ls.
  Proof.
    induction ls; simpl; trivial.
    constructor.
    - apply sublist_app_l.
    - revert IHls.
      apply Forall_impl; intros ? subl.
      rewrite subl.
      apply sublist_app_r.
  Qed.

  Lemma sublist_perm_head {A:Type} {l1 l2 : list A} :
    sublist l1 l2 ->
    exists t,
      Permutation (l1++t) l2.
  Proof.
    intros subl; induction subl.
    - exists nil; simpl; reflexivity.
    - destruct IHsubl as [t perm].
      simpl.
      exists t.
      rewrite <- perm.
      reflexivity.
    - destruct IHsubl as [t perm].
      exists (x::t).
      rewrite <- perm.
      rewrite <- Permutation_cons_app; reflexivity.
  Qed.

  Lemma Permutation_sublist_pullback_r {A:Type} {l1 l1' l2:list A} : 
    sublist l1 l1' ->
    Permutation l1 l2 ->
    exists l2',
      Permutation l1' l2' /\
      sublist l2 l2'.
  Proof.
    intros subl perm.
    revert l1' subl.
    revert l1 l2 perm.
    change (forall l1 l2 : list A,
               Permutation l1 l2 ->
               (fun l1 l2 => forall l1' : list A, sublist l1 l1' -> exists l2' : list A, Permutation l1' l2' /\ sublist l2 l2') l1 l2).
    apply Permutation_ind_bis; simpl; intros.
    - exists l1'; split; trivial.
    - dependent induction H1.
      + destruct (H0 _ H1) as [ll [perm subl]].
        exists (x::ll).
        split.
        * eauto.
        * constructor; trivial.
      + destruct (IHsublist x l l' H H0 (eq_refl _)) as [ll [perm subl]].
        exists (x0::ll).
        split.
        * eauto.
        * constructor; trivial.
    - revert l' H H0 H1.
      induction l1'; intros l' perm IH subl.
      + invcs subl.
      + specialize (IHl1' _ perm IH).
        invcs subl.
        * clear IHl1'.
          { revert l' H0 perm IH.
            induction l1'; intros l' subl perm1 IH1.
            - invcs subl.
            - invcs subl.
              + destruct (IH1 _ H0) as [ll [perm2 subl2]].
                exists (a0::a::ll); split.
                * rewrite perm_swap, perm2; trivial.
                * do 2 constructor; trivial.
              + destruct (IHl1' _ H1 perm1 IH1) as [ll [perm2 subl2]].
                exists (a0::ll); split.
                * rewrite <- perm2, perm_swap; trivial.
                * constructor; trivial.
          } 
        * destruct (IHl1' H1) as [ll [perm2 subl2]].
          exists (a::ll).
          { split.
            - constructor; trivial.
            - constructor; trivial.
          }
    - destruct (H0 _ H3) as [ll [perm1 subl1]].
      destruct (H2 _ subl1) as [ll' [perm2 subl2]].
      exists ll'.
      split; trivial.
      rewrite <- perm2; trivial.
  Qed.

  Lemma Permutation_filter_pullback_r {A:Type} {f:A->bool} {l1 l2} :
    Permutation (filter f l1) l2 ->
    exists l2',
      l2 = filter f l2' /\ Permutation l1 l2'.
  Proof.
    cut (forall l1 l2 : list A,
            Permutation l1 l2 ->
            (fun l1 l2 => forall l1', l1 = filter f l1' ->
                                      exists l2',
                                        l2 = filter f l2' /\ Permutation l1' l2') l1 l2).
    { intros H; intros.
      specialize (H _ _ H0); simpl in H.
      specialize (H _ (eq_refl _)).
      eauto.
    } 
    apply Permutation_ind_bis; simpl; intros.
    - exists l1'; split; trivial.
    - induction l1'; simpl in *; try discriminate.
      match_case_in H1; intros eqq; rewrite eqq in H1.
      + invcs H1.
        destruct (H0 _ (eq_refl _))
          as [ll [? perm]]; subst.
        exists (a::ll); split; simpl.
        * rewrite eqq; trivial.
        * constructor; trivial.
      + destruct (IHl1' H1) 
          as [ll [? perm]]; subst.
        exists (a::ll); split; simpl.
        * rewrite eqq; trivial.
        * constructor; trivial.
    - induction l1'; simpl in *; try discriminate.
      match_case_in H1; intros eqq1; rewrite eqq1 in H1.
      + invcs H1.
        clear IHl1'.
        revert l H H0 H4.
        induction l1'; simpl in *; try discriminate; intros.
        { match_case_in H4; intros eqq2; rewrite eqq2 in *.
          + invcs H4.
            destruct (H0 _ (eq_refl _))
              as [ll [? perm]]; subst.
            exists (a0::a::ll); split; simpl.
            * rewrite eqq1, eqq2; trivial.
            * rewrite perm_swap, perm; trivial. 
          + destruct (IHl1' _ H H0 H4) 
              as [ll [? perm]]; subst.
            exists (a0::ll); split; simpl.
            * rewrite eqq2; trivial.
            * rewrite perm_swap, perm; trivial.
        }
      + { destruct (IHl1' H1) 
            as [ll [? perm]]; subst.
          exists (a::ll); split.
          + simpl; rewrite eqq1; trivial.
          + constructor; trivial.
        }
    - subst.
      destruct (H0 _ (eq_refl _))
        as [ll [? perm]]; subst.
      destruct (H2 _ (eq_refl _))
        as [ll2 [? perm2]]; subst.
      exists ll2; split; trivial.
      rewrite perm; trivial.
  Qed.

  Lemma filter_perm_head {A:Type} {f:A->bool} {l1 l2} :
    Permutation (filter f l1) l2 ->
    exists t,
      Permutation l1 (l2++t).
  Proof.
    intros.
    generalize (filter_sublist f l1); intros subl.
    destruct (sublist_perm_head subl)
      as [x perm].
    rewrite H in perm.
    symmetry in perm.
    eauto.
  Qed.

  Lemma Permutation_filter {A : Type} (f : A -> bool) (l l' : list A) :
    Permutation l l' -> Permutation (filter f l) (filter f l').
  Proof.
    revert l l'.
    apply Permutation_ind_bis; simpl; intros.
    - trivial.
    - match_case; eauto.
    - repeat match_case; eauto 2; intros.
      rewrite perm_swap; eauto.
    - rewrite H0, H2; trivial.
  Qed.

End Sublist.

#[global]
Hint Immediate sublist_nil_l : fml.
