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

(** This module defines a simple (inefficient) insert sort, used in
various parts of the specification. *)

Require Export Sorting.
Require Import EquivDec.
Require Import List.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import Permutation.
Require Import Eqdep_dec.
Require Import RelationClasses.

Section SortingAdd.

  (** * Insertion sort *)

  Section InsertionSort.
    Context {A:Type}.
    Context {R:A->A->Prop}.
    Context (R_dec : forall a a', {R a a'} + {~R a a'}).

    (* if elements are not comparable, the left one is dropped *)
    Fixpoint insertion_sort_insert a l 
      := match l with
         | nil => a :: nil
         | b::xs => if (R_dec a b) 
                    then a::b::xs
                    else if (R_dec b a) then
                           b::insertion_sort_insert a xs
                         else b::xs
         end.

    Fixpoint insertion_sort (l:list A) 
      := match l with
         | nil => nil
         | a::xs => insertion_sort_insert a (insertion_sort xs)
         end.

    Lemma insertion_sort_insert_Sorted a (l:list A) :
      Sorted R l -> Sorted R (insertion_sort_insert a l).
    Proof.
      Hint Constructors LocallySorted.
      repeat rewrite Sorted_LocallySorted_iff.
      induction l; inversion 1; subst; simpl in *;
        repeat match goal with
               | [|- context [R_dec ?x ?y]] => destruct (R_dec x y)
               end; eauto.
    Qed.

    Lemma insertion_sort_Sorted (l:list A) : Sorted R (insertion_sort l).
    Proof.
      Hint Resolve insertion_sort_insert_Sorted.
      induction l; simpl; eauto.
    Qed.

    Fixpoint is_list_sorted (l:list A) :=
      match l with
      | nil => true
      | x::xs => match xs with
                 | nil => true
                 | y::ls => if R_dec x y then is_list_sorted xs else false
                 end
      end.

    Lemma is_list_sorted_Sorted_iff l: 
      is_list_sorted l = true <-> Sorted R l.
    Proof.
      induction l; simpl; intuition.
      - destruct l; simpl; eauto.
        destruct (R_dec a a0); simpl; intuition; try discriminate.
      - inversion H1; subst. rewrite H0; auto.
        destruct l; auto.
        inversion H5; subst.
        destruct (R_dec a a0); eauto.
    Qed.

    Lemma is_list_sorted_ext : forall l (p1 p2:is_list_sorted l = true), p1 = p2.
    Proof.
      intros. apply eq_proofs_unicity. decide equality.
    Qed.

    Lemma sorted_StronglySorted `{Transitive A R}:
      forall l, is_list_sorted l = true <-> StronglySorted R l.
    Proof.
      intros.
      rewrite is_list_sorted_Sorted_iff.
      split.
      apply Sorted_StronglySorted. 
      red. apply transitivity. 
      apply StronglySorted_Sorted.
    Qed.

    Lemma Forall_nin_irr `{Irreflexive A R}:
      forall a l, Forall (R a) l -> ~ In a l.
    Proof.
      induction l; [auto|intros].
      inversion H0; subst; intro.
      inversion H1; subst. 
      eapply irreflexivity; eauto.
      elim IHl; auto.
    Qed.

    Lemma StronglySorted_NoDup `{Irreflexive A R}: 
      forall l, StronglySorted R l -> NoDup l.
    Proof.
      induction l; intros.
      constructor.
      inversion H0; subst.
      constructor; auto. eapply Forall_nin_irr; eauto.
    Qed.

    Lemma Sorted_NoDup `{StrictOrder A R}: 
      forall l, Sorted R l -> NoDup l.
    Proof.
      intros.
      apply StronglySorted_NoDup; eauto.
      apply Sorted_StronglySorted; eauto.
      red; intros; etransitivity; eauto.
    Qed.

    Lemma is_list_sorted_NoDup `{StrictOrder A R} : 
      forall l, is_list_sorted l = true -> NoDup l.
    Proof.
      intros. 
      eapply Sorted_NoDup; eapply is_list_sorted_Sorted_iff; eauto.
    Defined.

    Lemma is_list_sorted_cons a r :
      is_list_sorted  (a::r) = true 
      <->
      (is_list_sorted r = true 
       /\ match r with
          | nil => True
          | y::_ => R a y
          end).
    Proof.
      simpl; destruct r; intuition;
        destruct (R_dec a a0); intuition congruence.
    Qed.

    Lemma is_list_sorted_cons_inv {a r} :
      is_list_sorted (a::r) = true ->
      is_list_sorted r = true.
    Proof.
      rewrite is_list_sorted_cons. intuition.
    Qed.

    Lemma StronglySorted_cons_in {x a l} :
      StronglySorted R (a::l) ->
      In x l ->
      R a x.
    Proof.
      inversion 1; subst; intros iin.
      rewrite Forall_forall in H3.
      auto.
    Qed.

    Lemma insertion_sort_sorted_is_id l :
      is_list_sorted l = true ->
      insertion_sort l = l.
    Proof.
      induction l; intros; simpl in *.
      reflexivity.
      assert (is_list_sorted l = true).
      destruct l; simpl in *; try reflexivity.
      destruct (R_dec a a0); congruence.
      specialize (IHl H0).
      rewrite IHl; clear IHl.
      destruct l; simpl in *; try reflexivity.
      revert H.
      destruct (R_dec a a0); intros; trivial.
      destruct (R_dec a0 a); congruence.
    Qed.

    Lemma insertion_sort_idempotent l :
      insertion_sort (insertion_sort l) =
      insertion_sort l.
    Proof.
      apply insertion_sort_sorted_is_id.
      apply is_list_sorted_Sorted_iff.
      apply insertion_sort_Sorted.
    Qed.

    Lemma insertion_sort_insert_not_nil a l :
      insertion_sort_insert a l <> nil.
    Proof.
      induction l; simpl; intuition; try discriminate.
      destruct (R_dec a a0); simpl in *; try discriminate.
      destruct (R_dec a0 a); simpl in *; try discriminate.
    Qed.
    
    Lemma insertion_sort_nil l :
      insertion_sort l = nil -> l = nil.
    Proof.
      induction l; simpl; intuition.
      apply insertion_sort_insert_not_nil in H; intuition.
    Qed.
    
    Lemma insertion_sort_insert_swap a a0 l  `{StrictOrder A R}:
      R a a0 ->
      insertion_sort_insert a (insertion_sort_insert a0 l) = 
      insertion_sort_insert a0 (insertion_sort_insert a l).
    Proof.
      revert a a0.
      induction l; simpl; intros.
      - destruct (R_dec a a0); simpl; intuition.
        destruct (R_dec a0 a); simpl; intuition.
        rewrite r0 in r. eelim irreflexivity; eauto.
      - destruct (R_dec a1 a).
        + destruct (R_dec a0 a).
          * simpl.
            destruct (R_dec a0 a1); intuition.
            destruct (R_dec a1 a); intuition.
            destruct (R_dec a1 a0); intuition.
            rewrite r3 in H0; eelim irreflexivity; eauto.
          * rewrite r in H0; intuition.
        + destruct (R_dec a0 a); simpl.
          * destruct (R_dec a1 a); intuition.
            destruct (R_dec a0 a1); intuition.
            destruct (R_dec a1 a0).
            rewrite r1 in r0; eelim irreflexivity; eauto.
            destruct (R_dec a a1); simpl;
              destruct (R_dec a0 a); intuition.
          * destruct (R_dec a a1); destruct (R_dec a a0); simpl.
            destruct (R_dec a0 a).
            rewrite r1 in r0; eelim irreflexivity; eauto.
            destruct (R_dec a a0); intuition.
            destruct (R_dec a1 a).
            rewrite r2 in r; eelim irreflexivity; eauto.
            destruct (R_dec a a1); intuition.
            f_equal; eauto.
            destruct (R_dec a a0); intuition.
            destruct (R_dec a1 a).
            rewrite r0 in r; eelim irreflexivity; eauto.
            destruct (R_dec a0 a); intuition.
            destruct (R_dec a a1); intuition.
            rewrite H0 in r; intuition.            
            destruct (R_dec a0 a); intuition.
            destruct (R_dec a a0); intuition.
            destruct (R_dec a1 a); intuition.            
            destruct (R_dec a a1); intuition.
    Qed.

  End InsertionSort.

  (** * Properties of [filter] on sorted lists *)
  
  Section Filter.
    Lemma StronglySorted_filter {A} {R} f {l} :
      @StronglySorted A R l -> StronglySorted R (filter f l).
    Proof.
      induction l; simpl; trivial.
      inversion 1; simpl; subst.
      destruct (f a); auto.
      constructor; auto.
      apply Forall_filter; trivial.
    Qed.
  End Filter.

  (** * Properties of [In] on sorted lists *)
  
  Section In.
    Lemma in_insertion_sort_insert {A R R_dec} {x l a} :
      In x (@insertion_sort_insert A R R_dec a l) -> a = x \/ In x l.
    Proof.
      revert x a. induction l; simpl; [intuition | ].
      intros x a0.
      case_eq (R_dec a0 a); simpl; intros; trivial.
      revert H0.
      case_eq (R_dec a a0); simpl; intros; intuition.
      destruct (IHl _ _ H2); intuition.
    Qed.

    Lemma in_insertion_sort {A R R_dec} {x l} :
      In x (@insertion_sort A R R_dec l) -> In x l.
    Proof.
      induction l; simpl; trivial.
      intros inn. apply in_insertion_sort_insert in inn.
      intuition.
    Qed.

    Hint Resolve asymmetric_over_cons_inv.
    Lemma insertion_sort_insert_in_strong {A R R_dec} {x l a} 
          (contr:asymmetric_over R (a::l)) :
      a = x \/ In x l -> In x (@insertion_sort_insert A R R_dec a l).
    Proof.
      revert x a contr. induction l; simpl; [intuition | ].
      intros x a0.
      case_eq (R_dec a0 a); simpl; intros; trivial.
      revert H0.
      case_eq (R_dec a a0); simpl; intros; intuition; subst; intuition.
      - right; apply (IHl x x); intuition.
        apply asymmetric_over_swap in contr. eauto. 
      - right. apply (IHl x a0); intuition.
        apply asymmetric_over_swap in contr. eauto.
    Qed.

    Lemma insertion_sort_insert_in {A R R_dec} {x l a}
          (contr:forall x y,  ~R x y -> ~R y x -> x = y) :
      a = x \/ In x l -> In x (@insertion_sort_insert A R R_dec a l).
    Proof.
      apply insertion_sort_insert_in_strong.
      apply asymmetric_asymmetric_over; eauto.
    Qed.

    Lemma insertion_sort_in_strong {A R R_dec} {x l}
          (contr:asymmetric_over R l) :
      In x l -> In x (@insertion_sort A R R_dec l).
    Proof.
      revert x.
      induction l; simpl; trivial; intros.
      specialize (IHl (asymmetric_over_cons_inv contr)).
      apply insertion_sort_insert_in_strong; trivial.
      - apply (asymmetric_over_incl contr). clear. simpl; intuition.
        apply in_insertion_sort in H0; eauto.
      - intuition.
    Qed.

    Hint Resolve asymmetric_asymmetric_over.

    Lemma insertion_sort_in {A R R_dec} {x l}
          (contr:forall x y,  ~R x y -> ~R y x -> x = y) :
      In x l -> In x (@insertion_sort A R R_dec l).
    Proof.
      apply insertion_sort_in_strong; intuition.
    Qed.

    Lemma equivlist_insertion_sort_strong {A R} R_dec {l l'}
          (contr:asymmetric_over R l)  :
      equivlist l l' ->
      equivlist (@insertion_sort A R R_dec l) (@insertion_sort A R R_dec l').
    Proof.
      cut (forall l l', (asymmetric_over R l) -> equivlist l l' ->
                        (forall x, In x (@insertion_sort A R R_dec l) -> In x (@insertion_sort A R R_dec l'))).
      - intros C eq x. split; intros inn.
        + specialize (C _ _ contr eq); intuition.
        + eapply C; try eapply inn.
          rewrite <- (asymmetric_over_equivlist eq); trivial.
          symmetry; trivial.
      - clear l l' contr. intros l l' asym incl x inn.
        apply in_insertion_sort in inn. apply incl in inn.
        apply insertion_sort_in_strong; trivial.
        eapply asymmetric_over_equivlist; eauto.
        symmetry. trivial.
    Qed.

    Lemma equivlist_insertion_sort {A R} R_dec {l l'}
          (contr:forall x y,  ~R x y -> ~R y x -> x = y)  :
      equivlist l l' ->
      equivlist (@insertion_sort A R R_dec l) (@insertion_sort A R R_dec l').
    Proof.
      intros.
      eapply equivlist_insertion_sort_strong; trivial.
      apply asymmetric_asymmetric_over; trivial.
    Qed.

    Lemma insertion_sort_insert_insertion_nin  {A:Type} lt dec
          `{StrictOrder A lt}
          (trich:forall a b, {lt a b} + {eq a b} + {lt b a})
          (a:A) a0 l :
      ~ lt a0 a ->
      ~ lt a a0 ->
      insertion_sort_insert dec a0
                            (insertion_sort_insert dec a l)
      = @insertion_sort_insert A lt dec a l.
    Proof.
      revert a a0. induction l; simpl; intros.
      - repeat (match_destr; try congruence).
      - repeat (match_destr; try congruence);
          simpl; repeat (match_destr; try congruence); trivial.
        + rewrite l0 in l1. intuition.
        + rewrite IHl; trivial.
        + destruct (trich a a0) as [[?|?]|?];
            try congruence.
        + destruct (trich a a0) as [[?|?]|?];
            try congruence.
    Qed.

    Lemma insertion_sort_insert_cons_app {A:Type} lt dec
          `{StrictOrder A lt}
          (trich:forall a b, {lt a b} + {eq a b} + {lt b a}) a l l2 :
      insertion_sort dec (insertion_sort_insert dec a l ++ l2) = @insertion_sort A lt dec (a::l ++ l2).
    Proof.
      revert a l2.
      induction l; simpl; trivial; intros.
      destruct (dec a0 a); simpl; trivial.
      destruct (dec a a0); simpl; trivial.
      - rewrite IHl; simpl. apply insertion_sort_insert_swap; eauto.
      - rewrite insertion_sort_insert_insertion_nin; eauto.
    Qed.

    Lemma insertion_sort_insertion_sort_app1 {A} lt dec `{StrictOrder A lt}
          (trich:forall a b, {lt a b} + {eq a b} + {lt b a}) l1 l2 :
      insertion_sort dec (insertion_sort dec l1 ++ l2) =
      @insertion_sort A lt dec (l1 ++ l2).
    Proof.
      revert l2.
      induction l1; simpl; trivial; intros.
      rewrite insertion_sort_insert_cons_app; trivial.
      simpl.
      rewrite IHl1; trivial.
    Qed.

    
    Lemma insertion_sort_trich_equiv {A:Type} lt dec
          (trich:forall a b, {lt a b} + {eq a b} + {lt b a}) (l:list A)
      : equivlist (@insertion_sort A lt dec l) l.
    Proof.
      intros; split; intros.
      - apply in_insertion_sort in H; trivial.
      - eapply insertion_sort_in in H; eauto.
        intros.
        destruct (trich x0 y) as [[?|?]|?]; intuition.
    Qed.

    Lemma insertion_sort_insert_forall_lt 
          {A:Type} lt dec (a:A) (l:list A) :
      Forall (lt a) l ->
      @insertion_sort_insert A lt dec a l = a :: l.
    Proof.
      destruct l; simpl; trivial.
      inversion 1; subst.
      match_destr; intuition.
    Qed.

    Lemma sort_insert_filter_true {A:Type} f lt dec `{StrictOrder A lt}
          (trich:forall a b, {lt a b} + {eq a b} + {lt b a}) 
          (a:A) (l:list A) :
      StronglySorted lt l ->
      f a = true ->
      filter f (@insertion_sort_insert A lt dec a l)
      = insertion_sort_insert dec a (filter f l).
    Proof.
      revert a.
      induction l; simpl; intros b lsort fb.
      - rewrite fb; trivial.
      - inversion lsort; subst.
        case_eq (f a); simpl; intros fa.
        +  destruct (dec b a); simpl.
           * rewrite fb.
             simpl. match_destr.
           * rewrite <- IHl; trivial.
             match_destr; simpl; rewrite fa; trivial.
        + match_destr.
          * simpl. rewrite fb, fa.
            rewrite insertion_sort_insert_forall_lt; trivial.
            apply Forall_filter.
            revert H3.
            apply Forall_impl_in; intros.
            etransitivity; eauto.
          * rewrite <- IHl; trivial.
            match_destr; simpl; rewrite fa; trivial.
            destruct (trich a b) as [[?|?]|?]; try congruence.
    Qed.
    
    Lemma sort_insert_filter_false {A:Type} f lt dec (a:A) (l:list A) :
      f a = false ->
      filter f (@insertion_sort_insert A lt dec a l) =
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
    
    Lemma sort_filter_commute {A:Type} f lt dec
          `{StrictOrder A lt} 
          (trich:forall a b, {lt a b} + {eq a b} + {lt b a})
          (l:list A) :
      filter f (@insertion_sort A lt dec l)
      = insertion_sort dec (filter f l).
    Proof.
      induction l; simpl; trivial.
      case_eq (f a); intros fa; simpl.
      - rewrite <- IHl, sort_insert_filter_true; trivial.
        eapply Sorted_StronglySorted.
        + apply StrictOrder_Transitive.
        + eapply insertion_sort_Sorted.
      - rewrite <- IHl, sort_insert_filter_false; trivial.
    Qed.

    Lemma Forall_insertion_sort {A R R_dec} {P} l :
      Forall P l -> Forall P (@insertion_sort A R R_dec l).
    Proof.
      repeat rewrite Forall_forall.
      intros fp x inx.
      apply in_insertion_sort in inx.
      auto.
    Qed.
    
  End In.

  (** * Properties of [map] on sorted lists *)
  
  Section Map.

    Lemma map_insertion_sort_insert {A B}
          {R1 R2}
          (R1_dec : forall a a' : A, {R1 a a'} + {~ R1 a a'})
          (R2_dec : forall b b' : B, {R2 b b'} + {~ R2 b b'})
          (f:A->B)
          (consistent:forall x y, R1 x y <->
                                  R2 (f x) (f y)) a l :
      map f (insertion_sort_insert R1_dec a l) =
      insertion_sort_insert R2_dec (f a) (map f l).
    Proof.
      induction l; simpl; trivial.
      rewrite <- IHl.
      destruct (consistent a a0); destruct (consistent a0 a).
      repeat match_destr; simpl; try tauto.
    Qed.
    
    Lemma map_insertion_sort {A B}
          {R1 R2}
          (R1_dec : forall a a' : A, {R1 a a'} + {~ R1 a a'})
          (R2_dec : forall b b' : B, {R2 b b'} + {~ R2 b b'})
          (f:A->B)
          (consistent:forall x y, R1 x y <->
                                  R2 (f x) (f y)) l :
      map f (insertion_sort R1_dec l) =
      insertion_sort R2_dec (map f l).
    Proof.
      induction l; simpl; trivial.
      rewrite <- IHl.
      erewrite map_insertion_sort_insert; eauto.
    Qed.

  End Map.

  Lemma insertion_sort_insert_nin_eq_inv {A R} dec (a:A) l₁ l₂ :
    insertion_sort_insert (R:=R) dec a l₁ = insertion_sort_insert dec a l₂ ->
    ~ In a l₁ ->
    ~ In a l₂ ->
    l₁ = l₂.
  Proof.
    revert l₂.
    induction l₁; destruct l₂; simpl; intros eqq; trivial.
    - intuition.
      destruct (dec a a0); simpl in *.
      + invcs eqq.
      + destruct (dec a0 a); invcs eqq; tauto.
    - intuition.
      destruct (dec a a0); simpl in *.
      + invcs eqq.
      + destruct (dec a0 a); invcs eqq; tauto.
    - intuition.
      destruct (dec a a0); simpl in *.
      + invcs eqq.
        destruct (dec a a1); simpl.
        * invcs H4; trivial.
        * destruct (dec a1 a); invcs H4; tauto.
      + destruct (dec a0 a).
        * destruct (dec a a1); invcs eqq; try tauto.
          destruct (dec a1 a); invcs H4; try tauto.
          f_equal; eauto.
        * { destruct (dec a a1).
            - invcs eqq; tauto.
            - destruct (dec a1 a); invcs eqq; try tauto.
          } 
  Qed.
End SortingAdd.

