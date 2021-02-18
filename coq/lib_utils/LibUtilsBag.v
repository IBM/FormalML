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

(** This module provides support for bags (or multisets). *)

Require Import Arith.
Require Import Min.
Require Import Max.
Require Import ZArith.
Require Import Lia.
Require Import Permutation.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import List.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import LibUtilsSublist.
Require Import LibUtilsAssoc.

Section Bag.

  Context {A:Type}.
  Context {eqdec:EqDec A eq}.

  Definition rbag := list A.

  Definition bunion := (@app A).

  Declare Scope rbag_scope.
  Delimit Scope rbag_scope with rbag.
  Bind Scope rbag_scope with rbag.
  Open Scope rbag_scope.

  Notation "X ≅ Y" := (ldeqA X Y) (at level 70) : rbag_scope.                              (* ≅ = \cong *)
  Notation "b1 ⊎ b2" := (bunion b1 b2) (right associativity, at level 70) : rbag_scope.    (* ⊎ = \uplus *)

  Global Instance bunion_proper : Proper (ldeqA ==> ldeqA ==> ldeqA) bunion.
  Proof.
    unfold Proper, respectful.
    intros. unfold bunion.
    apply Permutation_app; assumption.
  Qed.

  Lemma bunion_nil_r:
    forall (l:list A),
      (l ⊎ nil) = l.
  Proof.
    intros; unfold bunion; rewrite app_nil_r; reflexivity.
  Qed.

  Lemma bunion_nil_l:
    forall (l:list A),
      (nil ⊎ l) = l.
  Proof. reflexivity. Qed.

  Lemma bunion_assoc:
    forall (l1 l2 l3:list A),
      ((l1 ⊎ l2) ⊎ l3) = (l1 ⊎ (l2 ⊎ l3)).
  Proof.
    intros; unfold bunion; rewrite app_assoc; reflexivity.
  Qed.

  Lemma bunion_comm (l1 l2: list A) :
    (l1 ⊎ l2) ≅ (l2 ⊎ l1).
  Proof.
    intros.
    unfold bunion.
    apply Permutation_app_comm; try assumption.
  Qed.

  Lemma bunion_Forall P (l1 l2 : list A) :
    Forall P l1 -> Forall P l2 -> Forall P (bunion l1 l2).
  Proof.
    unfold bunion; intros.
    apply Forall_app; trivial.
  Qed.

  Fixpoint remove_one (x : A) (l : list A) : list A :=
    match l with
      | nil => nil
      | y::tl => if (x == y) then tl else y::(remove_one x tl)
    end.

  Hint Unfold ldeqA : fml.

  Ltac tac
    := repeat progress (intros; simpl in *; try autorewrite with bag in *; try match goal with
         | [H: ?a = ?a |- _ ] => clear H
         | [H: ?a = ?a -> False |- _ ] => elim H; reflexivity
         | [H: ?a <> ?a |- _ ] => elim H; reflexivity
         | [H: {_ | _ } |- _ ] => destruct H
         | [H: ?a ≅ ?b |- _ ] => rewrite H in *

         | [H: context [@equiv_dec ?A ?eqA ?eqvA ?eqdecA ?x ?x ] |- _] => 
           let HH:=(fresh "eqH") in 
           destruct (@equiv_dec A eqA eqvA eqdecA x x) as [eqH|eqH];
                                                         [|elim eqH; reflexivity]
         | [|- context [@equiv_dec ?A ?eqA ?eqvA ?eqdecA ?x ?x ]] => 
           let HH:=(fresh "eqH") in 
           destruct (@equiv_dec A eqA eqvA eqdecA x x) as [eqH|eqH];
                                                         [|elim eqH; reflexivity]
         | [|- ?x :: ?l ≅ ?x :: ?l' ] => apply perm_skip; fold ldeqA
         | [|- ?x :: ?y :: ?l ≅ ?y :: ?x :: ?l' ] => apply perm_swap; fold ldeqA

        | [H: ?a + {?b} |- _ ] => destruct H
        | [H: {?a} + {?b} |- _ ] => destruct H
         | [H: context [@equiv_dec ?A ?eqA ?eqvA ?eqdecA ?x ?y ] |- _] => 
           destruct (@equiv_dec A eqA eqvA eqdecA x y)
         | [|- context [@equiv_dec ?A ?eqA ?eqvA ?eqdecA ?x ?y ]] => 
           destruct (@equiv_dec A eqA eqvA eqdecA x y)
       end;
                        unfold complement, Equivalence.equiv in *;
                          try subst; try reflexivity; eauto with fml).

  Global Instance remove_one_proper : Proper (eq ==> ldeqA ==> ldeqA) remove_one.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    elim H0; tac.
  Qed.

  (** Bag minus
   * Remove elements of d from x.
   * Note the order of arguments: (bminus d x) is "x ⊖ d" *)
  Fixpoint bminus (d x:list A) {struct d} : list A :=
    match d with
      | nil => x
      | d1 :: d' => bminus d' (remove_one d1 x)
    end.

  Notation "b1 ⊖ b2" := (bminus b2 b1) (right associativity, at level 70) : rbag_scope.    (* ⊖ = \ominus *)

  Lemma bminus_over_app_delta :
    forall (d1 d2:list A), forall (s:list A),
      ((s ⊖ d1) ⊖ d2) = (s ⊖ (d1 ++ d2)).
  Proof.
    induction d1; tac.
  Qed.

  Lemma bminus_to_nil:
    forall (d:list A), (nil ⊖ d) = nil.
  Proof.
    induction d; tac.
  Qed.

  Lemma bminus_nil_to_self:
    forall (x:list A), (x ⊖ nil) = x.
  Proof.
    induction x; tac.
  Qed.

  Global Instance bminus_proper_lem : Proper (eq ==> ldeqA ==> ldeqA) bminus.
  Proof.
    unfold Proper, respectful.
    intros x y H; subst.
    induction y; tac.
    eapply IHy; rewrite H; reflexivity.
  Qed.

  Lemma remove_one_comm:
    forall (x1 x2:A), forall x:list A,
      (remove_one x1 (remove_one x2 x)) = (remove_one x2 (remove_one x1 x)).
  Proof.
    intros.
    induction x; tac.
    congruence.
  Qed.

  Lemma remove_one_not_first:
    forall (x1 x2:A), forall s:list A,
      x1 <> x2 -> (remove_one x1 (x2 :: s)) = x2 :: (remove_one x1 s).
  Proof.
    intros.
    simpl.
    elim (equiv_dec x1 x2); intros; [contradiction|reflexivity].
  Qed.

  Global Instance bminus_proper : Proper (ldeqA ==> ldeqA ==> ldeqA) bminus.
  Proof.
    unfold Proper, respectful.
    intros x y H.
    elim H; tac.
    - rewrite remove_one_comm; eauto with fml.
    - rewrite H1; eauto.
      symmetry; eauto.
  Qed. 

  (* some useful properties *)

  Lemma bminus_self : forall (x:list A), (x ⊖ x) = nil.
  Proof.
    intros; induction x; tac.
  Qed.

  Lemma bminus_naught : forall (x:list A), (x ⊖ nil) = x.
  Proof.
    reflexivity.
  Qed.  

  Hint Rewrite bminus_nil_to_self bminus_to_nil bminus_self bminus_naught : bag.
  
  Lemma bminus_cons :
    forall (a:A) (x y:list A), ((a :: x) ⊖ (a :: y)) = (x ⊖ y).
  Proof.
    tac.
  Qed.

  Hint Rewrite bminus_cons : bag.
  Hint Rewrite app_nil_r : bag.

  Lemma bunion_bminus :
    forall (x y: list A), ((y ⊎ x) ⊖ y) = x.
  Proof.
    intros.
    induction x; unfold bunion in *; tac.
    induction y; tac.
  Qed.

  Lemma remove_one_consed:
    forall (x:list A), forall (a:A),
      (remove_one a (a :: x)) = x.
  Proof.
    tac.
  Qed.

  Lemma remove_one_In (a x:A) (l1 l2:list A) :
    In x (bminus l1 (remove_one a l2)) -> In x (bminus l1 l2).
  Proof.
    revert l2 a x.
    induction l1; intros; simpl in *.
    - induction l2; intros; simpl in *.
      assumption.
      destruct (equiv_dec a a0).
      rewrite e in *; clear e.
      right; assumption.
      simpl in H.
      elim H; clear H; intros.
      left; assumption.
      right; apply (IHl2 H).
    - apply (IHl1 (remove_one a l2) a0 x).
      rewrite remove_one_comm.
      assumption.
  Qed.

  Lemma remove_one_sublist l a : sublist (remove_one a l) l.
  Proof.
    induction l; simpl.
    - constructor.
    - match_destr.
      + constructor; reflexivity.
      + constructor.
         trivial.
  Qed.
  
  Lemma bminus_sublist (l1 l2:list A) :
    sublist (bminus l1 l2) l2.
  Proof.
    revert l2.
    induction l1; simpl; intros.
    - reflexivity.
    - rewrite IHl1.
      apply remove_one_sublist.
  Qed.

  Lemma bminus_Forall (l1 l2:list A) p :
    Forall p l2 -> Forall p (bminus l1 l2).
  Proof.
    intros.
    rewrite bminus_sublist.
    trivial.
  Qed.

  Lemma bminus_NoDup  (l1 l2:list A) : NoDup l2 -> NoDup (bminus l1 l2).
  Proof.
    intros.
    rewrite bminus_sublist.
    trivial.
  Qed.
                                       
  Hint Rewrite bunion_bminus remove_one_consed : bag.
  
  (* not used, unfollowed thought from now... *)
  Lemma pick_an_a:
    forall (l:list A) (a:A),
      ({l':list A | a::l' ≅ l}) + {remove_one a l ≅ l}.
  Proof.
    intros; induction l; tac.
    left; exists (a0::x).
    rewrite perm_swap, l0; eauto with fml.
  Qed.

  (* It seems some properties are easier to check on a different representation with
     the multiplicity explicit. Some conversion operations. *)

  Global Instance filter_proper : forall (p:A -> bool), Proper (ldeqA ==> ldeqA) (filter p).
  Proof.
    unfold Proper, respectful.
    intros.
    elim H; tac;
    repeat match goal with 
        [|- context [if ?a then _ else _ ] ] => case_eq a
    end; tac.
  Qed.

  Section MBag.

    Fixpoint mult (l:list A) (a:A) : nat :=
      match l with
        | nil => O
        | b :: l' => if (equiv_dec a b) then S (mult l' a) else (mult l' a)
      end.

    Definition mult_equiv l l' := (forall a, mult l a = mult l' a).
    
    Notation "X ≅# Y" := (mult_equiv X Y) (at level 70) : rbag_scope.                              (* ≅ = \cong *)

    Hint Unfold mult_equiv : fml.

    Global Instance mult_proper : Proper (ldeqA ==> eq ==> eq) mult.
    Proof.
      unfold Proper, respectful; intros.
      elim H; intros; simpl.
      - reflexivity.
      - rewrite H0 in *.
        destruct (equiv_dec y0 x1).
        rewrite H2; reflexivity.
        assumption.
      - rewrite H0 in *.
        destruct (equiv_dec y0 y1).
        rewrite e in *.
        destruct (equiv_dec y1 x1); reflexivity.
        destruct (equiv_dec y0 x1); reflexivity.
      - rewrite H0 in *; rewrite H2; assumption.
    Qed.

    Lemma bags_equal_same_mult1:
      forall (l1 l2:list A), 
        l1 ≅ l2 -> l1 ≅# l2.
    Proof.
      unfold mult_equiv.
      intros.
      induction H; tac.
      congruence.
    Qed.

    Fixpoint groupby (l:list A) : list (A*nat)
      := match l with
           | nil => nil
           | (a::ls) => let rest := groupby ls in 
                        match lookup equiv_dec rest a with
                          | None => (a,1)::rest
                          | Some x => update_first equiv_dec rest a (S x)
                        end
         end.

    Lemma groupby_noDup l : NoDup (domain (groupby l)).
    Proof.
      Hint Constructors NoDup : fml.
      induction l; simpl; trivial with fml.
      case_eq (lookup equiv_dec (groupby l) a); [intros ? ?| intros neq].
      - rewrite domain_update_first; trivial.
      - simpl; constructor; auto. apply lookup_none_nin in neq; trivial.
    Qed.

    Fixpoint rep (a:A) n : list A :=
      match n with
        | 0 => nil
        | S m => a::(rep a m)
      end.

    Fixpoint smush (l:list (A*nat)) : list A
      := match l with
           | nil => nil
           | ((d,n)::ls) => rep d n ++ smush ls
         end.

    Global Instance smush_perm_proper : Proper ((@Permutation (A*nat)) ==> ldeqA) smush.
    Proof.
      unfold respectful, Proper.
      apply Permutation_ind_bis; intros; try reflexivity; simpl.
      - destruct x. rewrite H0. reflexivity.
      - destruct x; destruct y. rewrite H0. repeat rewrite app_assoc. apply Permutation_app_tail.
        apply Permutation_app_comm.
      - transitivity (smush l'); auto.
    Qed.
  
    Lemma smush1 a n x : smush ((a,S n)::x) = a::(smush ((a,n)::x)).
    Proof.
      trivial.
    Qed.
    
    Hint Resolve groupby_noDup : fml.

    Lemma smush_groupby l : Permutation (smush (groupby l)) l.
    Proof.
      induction l; simpl; trivial.
      case_eq (lookup equiv_dec (groupby l) a); [intros n eqn | intros neq].
      - destruct (lookup_to_front equiv_dec eqn).
        assert (perm1:Permutation (update_first equiv_dec (groupby l) a (S n)) (update_first equiv_dec ((a, n) :: x) a (S n))) by (apply update_first_NoDup_perm_proper; auto with fml). 
        rewrite perm1.
        simpl. destruct (equiv_dec a a); try congruence.
        rewrite smush1.
        apply perm_skip.
        rewrite <- H, IHl.
        trivial.
      - simpl. apply perm_skip; trivial.
    Qed.

(* {mult l a = 0} + {{l':list A | a::l' ≅ l}}. *)
    Lemma pick_an_a_or_absent:
      forall (l:list A) (a:A),
        (mult l a = 0) \/ (exists l':list A, a::l' ≅ l).
    Proof.
      induction l; intros; simpl.
      left; reflexivity.
      elim (equiv_dec a a0); intros.
      rewrite a1 in *; clear a1.
      elim (equiv_dec a0 a0); intros.
      - right.
        generalize (IHl a0); intros; clear IHl.
        elim H; intros; clear H.
        exists l; reflexivity.
        exists l; reflexivity.
      - generalize (IHl a0); intros; clear IHl.
        elim H; intros; clear H.
        left; assumption.
        right.
        exists l; reflexivity.
      - elim (equiv_dec a0 a); intros.
        rewrite a1 in *; congruence.
        generalize (IHl a0); intros; clear IHl.
        elim H; intros; clear H.
        left; assumption.
        right.
        elim H0; intros.
        exists (a::x).
        rewrite <- H.
        apply perm_swap.
    Qed.
  
    Lemma lookup_none_mult0 l d : lookup equiv_dec (groupby l) d = None -> mult l d = 0.
    Proof.
      revert d.
      induction l; simpl; trivial; intros.
      case_eq (lookup equiv_dec (groupby l) a); intros; rewrite H0 in H; destruct (equiv_dec d a); subst.
      - apply lookup_none_nin in H. elim H.
        rewrite domain_update_first.
        rewrite e in *.
        eapply in_dom; eapply lookup_in; eauto.
      - apply IHl.
        apply lookup_none_nin in H.
        rewrite domain_update_first in H.
        case_eq (lookup equiv_dec (groupby l) d); try congruence; intros.
        apply lookup_in in H1. apply in_dom in H1. congruence.
      - simpl in H. rewrite e in *; destruct (equiv_dec a a); try congruence.
      - simpl in H. destruct (equiv_dec d a); try congruence.
        auto.
    Qed.    

    Lemma lookup_update_eq {B:Type }{l a} {n n':B} : lookup equiv_dec (update_first equiv_dec l a n') a = Some n -> n = n'.
    Proof.
      revert a n n'.
      induction l; simpl; try congruence.
      intros. destruct a.
      destruct (equiv_dec a0 a); simpl in *; subst.
      - rewrite e in*; destruct (equiv_dec a a); try congruence.
      - destruct (equiv_dec a0 a); try congruence.
        eauto.
    Qed.

    Lemma domain_groupby {l a} : In a (domain (groupby l)) <-> In a l.
    Proof.
      revert a.
      induction l; simpl; intuition; subst.
      - case_eq (lookup equiv_dec (groupby l) a); intros; rewrite H0 in H; simpl in *.
        + rewrite domain_update_first in H. right; apply IHl; auto.
        + intuition. right; apply IHl; auto.
      - case_eq (lookup equiv_dec (groupby l) a0); intros; simpl in *.
        + rewrite domain_update_first. eapply in_dom; eapply lookup_in; eauto.
        + intuition.
      - case_eq (lookup equiv_dec (groupby l) a); intros; simpl in *.
        + rewrite domain_update_first. apply IHl; eauto. 
        + right; eapply IHl; eauto.
    Qed.
    
    Lemma groupby_mult_in {l d n} : In (d, n) (groupby l) -> mult l d = n.
    Proof.
      revert n. induction l; simpl; intuition.
      case_eq (lookup equiv_dec (groupby l) a); intros; rewrite H0 in H.
      - apply (in_lookup_nodup equiv_dec) in H; [|rewrite domain_update_first; apply groupby_noDup].
        case_eq (equiv_dec d a); trivial; intros; try rewrite e in * ; subst.
        + apply lookup_update_eq in H. rewrite (IHl n0); auto.
          eapply lookup_in; eauto.
        + apply IHl. rewrite lookup_update_neq in H; try congruence. eapply lookup_in; eauto.
      - destruct H.
        + inversion H; subst. case_eq (equiv_dec d d); try congruence; intros.
          rewrite lookup_none_mult0; auto.
        + rewrite (IHl _ H). case_eq (equiv_dec d a); trivial; intros; subst.
          apply lookup_none_nin in H0.
          apply in_dom in H. congruence.
    Qed.
    
    Lemma groupby_mult_in_pos {l d n} : In (d, n) (groupby l) -> n <> 0.
    Proof.
      revert n. induction l; simpl; intuition; subst.
      case_eq (lookup equiv_dec (groupby l) a); intros; rewrite H0 in H.
      - apply (in_lookup_nodup equiv_dec) in H; [|rewrite domain_update_first; apply groupby_noDup].
        case_eq (equiv_dec d a); trivial; intros; subst; try rewrite e in *.
        + apply lookup_update_eq in H; discriminate.
        + rewrite lookup_update_neq in H; auto. apply (IHl 0); trivial.
          eapply lookup_in; eauto.
      - destruct H.
        + inversion H; congruence.
        + eauto.
    Qed.

    Lemma mult_in_groupby {l d n} : mult l d = S n -> In (d, S n) (groupby l).
    Proof.
      revert d n. induction l; simpl; try congruence; intros.
      case_eq (lookup equiv_dec (groupby l) a); intros;
      case_eq (equiv_dec d a); intros; rewrite H1 in H; subst; simpl; try rewrite e in *.
      - inversion H. 
        rewrite H3.
        assert (mn0:mult l a = n0).
        + apply groupby_mult_in. apply (lookup_in equiv_dec); auto.
        + rewrite H3 in mn0. subst n0.
          apply (lookup_in equiv_dec).
          apply lookup_update_eq_in. apply lookup_in, in_dom in H0. trivial.
      - apply (lookup_in equiv_dec). rewrite lookup_update_neq; auto.
        apply in_lookup_nodup; try apply groupby_noDup; auto.
      - destruct n; intuition. apply lookup_none_nin in H0.
        inversion H. specialize (IHl _ _ H3).
        apply in_dom in IHl. intuition.
      - auto.
    Qed.

    Lemma mult_nin_groupby {l d} : mult l d = 0 -> ~ In d (domain (groupby l)).
    Proof.
      intros mu ind.
      destruct (in_domain_in ind).
      rewrite (groupby_mult_in H) in mu.
      generalize (groupby_mult_in_pos H); intuition.
    Qed.
  
    Lemma bags_same_mult_has_equal :
      forall (l1 l2:list A),
        (forall (a:A), (mult l1 a) = (mult l2 a)) ->  (l1 ≅ l2).
    Proof.
      red. intros.
      rewrite <- (smush_groupby l1), <- (smush_groupby l2).
      apply smush_perm_proper.
      apply NoDup_Permutation.
      - apply NoDup_domain_NoDup; apply groupby_noDup.
      - apply NoDup_domain_NoDup; apply groupby_noDup.
      - intros. destruct x. destruct n.
        + split; intros HH; elim (groupby_mult_in_pos HH); trivial.
        + split; intros HH; apply groupby_mult_in in HH; apply mult_in_groupby.
          * congruence. 
          * congruence.
    Qed.

  End MBag.

  (* Formally defined with 'min' over arity in the [GL95] paper *)
  Definition bmin (l1 l2:list A) :=
    l1 ⊖ (l1 ⊖ l2).
  Notation "b1 min-b b2" := (bmin b1 b2) (right associativity, at level 70) : rbag_scope.

  (* Formally defined with 'max' over arity in the [GL95] paper *)
  Definition bmax (l1 l2:list A) :=
    l1 ⊎ (l2 ⊖ l1).
  Notation "b1 max-b b2" := (bmax b1 b2) (right associativity, at level 70) : rbag_scope.

  (* counting *)

  Definition bcount {A} (l:list A) := length l.

  Lemma bcount_map_id {B} (f:A -> B) (l:list A) :
    @bcount A l = @bcount B (map f l).
  Proof.
    induction l; [reflexivity|].
    simpl.
    auto.
  Qed.

  (* Formally defined with 'max' over arity in the [GL95] paper *)
  Fixpoint bdistinct (l:list A) :=
    match l with
      | nil => nil
      | x :: l' =>
        let dl' := bdistinct l' in
        match mult dl' x with
          | O => x :: dl'
          | _ => dl'
        end
    end.

  Lemma bdistinct_sublist l : sublist (bdistinct l) l.
  Proof.
    induction l; simpl.
    - reflexivity.
    - match_destr.
      + apply sublist_cons; trivial.
      + apply sublist_skip; trivial.
  Qed.

  Lemma bdistinct_Forall {P} {l} :
      Forall P l -> Forall P (bdistinct l).
  Proof.
    intros.
    apply (Forall_sublist _ _ (bdistinct_sublist l)) in H.
    trivial.
  Qed.
  
  Lemma bdistinct_at_most_one:
    forall (l:list A), forall (x:A),
      (mult (bdistinct l) x) = 0 \/ (mult (bdistinct l) x) = 1.
  Proof.
    induction l; simpl; intros.
    left; reflexivity.
    generalize (IHl x); generalize (IHl a); intros; clear IHl.
    elim H0; intro; clear H0; elim H; intro; clear H;
    try rewrite H0; simpl; elim (equiv_dec x a); intro aH.
    - right; auto.
    - left; assumption.
    - rewrite aH in *; auto.
    - left; assumption.
    - rewrite aH in *; auto.
    - right; assumption.
    - right; assumption.
    - right; assumption.
  Qed.

  (* I am going too brute-force here... wondering if that's a good sign... -JS *)

  Global Instance bdistinct_proper : Proper (ldeqA ==> ldeqA) bdistinct.
  Proof.
    unfold Proper, respectful.
    intros.
    generalize bags_equal_same_mult1; intros.
    elim H; simpl; intros.
    - reflexivity.
    - apply bags_same_mult_has_equal; intros.
      assert ((mult (bdistinct l) x0) = (mult (bdistinct l') x0)).
      apply H0; assumption.
      apply H0; rewrite H3.
      generalize bdistinct_at_most_one; intros.
      elim (H4 l' x0); intros; clear H4; rewrite H5.
      rewrite H2; reflexivity.
      assumption.
    - apply bags_same_mult_has_equal; intros.
      assert (((mult (bdistinct l) x0) = 0) \/ ((mult (bdistinct l) x0) = 1)).
      apply bdistinct_at_most_one.
      assert (((mult (bdistinct l) y0) = 0) \/ ((mult (bdistinct l) y0) = 1)).
      apply bdistinct_at_most_one.
      elim H1; intros; clear H1; elim H2; intros; clear H2; rewrite H3; rewrite H1.
      simpl.
      + elim (equiv_dec y0 x0); intros.
        rewrite a0 in *; clear a0; simpl.
        elim (equiv_dec a x0); intros.
        elim (equiv_dec x0 x0); intros; simpl.
        elim (equiv_dec a x0); intros; try reflexivity; try contradiction; try congruence.
        elim (equiv_dec x0 x0); intros; simpl.
        elim (equiv_dec a x0); intros; try reflexivity; try contradiction; try congruence.
        rewrite H3; congruence.
        elim (equiv_dec x0 x0); intros; simpl.
        elim (equiv_dec a x0); intros; try reflexivity; try contradiction; try congruence.
        rewrite H3.
        congruence.
        rewrite H1.
        elim (equiv_dec x0 y0); intros; simpl.
        congruence.
        rewrite H3.
        elim (equiv_dec a y0); intros; simpl.
        elim (equiv_dec a x0); intros; simpl.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
        elim (equiv_dec a x0); intros; try reflexivity; try contradiction; try congruence.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
      + simpl; rewrite H3.
        elim (equiv_dec y0 x0); intros; simpl; try reflexivity; try contradiction; try congruence.
        rewrite H1.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
      + simpl.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
        elim (equiv_dec x0 y0); intros; simpl; try reflexivity; try contradiction; try congruence.
        rewrite H3; simpl.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
        elim (equiv_dec x0 y0); intros; simpl; try reflexivity; try contradiction; try congruence.
        rewrite H3.
        simpl.
        elim (equiv_dec a y0); intros; try reflexivity; try contradiction; try congruence.
      + rewrite H3.
        reflexivity.
    - apply perm_trans with (l' := bdistinct l'); assumption.
  Qed.
  
  Lemma bdistinct_exactly_zero:
    forall (l:list A), forall (x:A),
      (mult l x) = 0 -> (mult (bdistinct l) x) = 0.
  Proof.
    induction l.
    intros; simpl; reflexivity.
    simpl.
    intro.
    elim (equiv_dec x a); intros.
    - congruence.
    - assert (((mult (bdistinct l) a) = 0) \/ ((mult (bdistinct l) a) = 1)).
      apply bdistinct_at_most_one.
      elim H0; intros; rewrite H1.
      simpl.
      elim (equiv_dec x a); intros.
      + contradiction.
      + apply IHl; assumption.
      + apply IHl; assumption.
  Qed.

  Lemma bdistinct_exactly_zero_back:
    forall (l:list A), forall (x:A),
      (mult (bdistinct l) x) = 0 -> (mult l x) = 0.
  Proof.
    intros.
    generalize (pick_an_a_or_absent l x); intros.
    elim H0; intros.
    - assumption.
    - elim H1; intros.
      assert ((mult (bdistinct (x :: x0)) x) = 0).
      rewrite <- H.
      apply bags_equal_same_mult1.
      rewrite H2; reflexivity.
      simpl in H3.
      assert (((mult (bdistinct x0) x) = 0) \/ ((mult (bdistinct x0) x) = 1)).
      apply bdistinct_at_most_one.
      elim H4; intros; clear H4.
      rewrite H5 in H3.
      simpl in H3.
      revert H3.
      elim (equiv_dec x x); intros.
      congruence.
      congruence.
      rewrite H5 in H3.
      congruence.
  Qed.

  Lemma bdistinct_exactly_one:
    forall (l:list A), forall (x:A),
      (mult l x) <> 0 -> (mult (bdistinct l) x) = 1.
  Proof.
    intros.
    generalize (bdistinct_at_most_one l x).
    intros.
    elim H0; intro.
    assert False.
    apply H.
    apply bdistinct_exactly_zero_back; assumption.
    contradiction.
    assumption.
  Qed.

  Lemma bdistinct_exactly_one_back:
    forall (l:list A), forall (x:A),
      (mult (bdistinct l) x) = 1 -> (mult l x) <> 0.
  Proof.
    induction l; simpl; intros.
    congruence.
    assert (((mult (bdistinct l) a) = 0) \/ ((mult (bdistinct l) a) = 1)).
    apply bdistinct_at_most_one.
    revert H.
    elim H0; intro; clear H0; rewrite H; simpl.
    elim (equiv_dec x a); intros.
    rewrite a0 in *; clear a0.
    auto.
    apply IHl; assumption.
    intros.
    elim (equiv_dec x a); intros.
    rewrite a0 in *; clear a0.
    auto.
    apply IHl; assumption.
  Qed.

  Lemma bdistinct_exactly_one_back_diff:
    forall (l:list A), forall (x:A),
      (mult (bdistinct l) x) = 1 -> (mult l x) >= 1.
  Proof.
    intros.
    assert ((mult l x) <> 0). 
    apply bdistinct_exactly_one_back; assumption.
    lia.
  Qed.

  Lemma exist_or_zero:
    forall (s:list A), forall (x:A),
      (exists (rs:list A), (x::rs) ≅ s) \/ (mult s x) = 0.
  Proof.
    induction s.
    intros.
    - right; simpl; reflexivity.
    - intros. destruct (equiv_dec x a).
      left; elim (IHs a); intro; elim H; intros; rewrite e in *; exists s; reflexivity.
      elim (IHs x); intro; elim H; intros.
      + left.
        exists (a::x0).
        rewrite <- H0.
        rewrite perm_swap; reflexivity.
      + right.
        simpl.
        destruct (equiv_dec x a).
        contradiction.
        reflexivity.
  Qed.

  Lemma bdistinct_mult:
    forall (l:list A), forall (x:A),
      mult (bdistinct l) x = min (mult l x) 1.
  Proof.
    induction l; simpl; intros.
    reflexivity.
    elim (equiv_dec x a); intro.
    rewrite a0 in *; clear a0.
    generalize (IHl a); intro; rewrite H; clear H.
    generalize (exist_or_zero l a); intro.
    elim H; intro.
    elim H0; intros.
    assert (min (mult l a) 1 = 1).
    rewrite <- H1; simpl.
    elim (equiv_dec a a); intro; try congruence.
    generalize (mult x0 a); intro; auto with arith.
    rewrite H2.
    rewrite IHl; rewrite H2.
    generalize (mult l a); intro; rewrite <- succ_min_distr; auto with arith.
    rewrite H0; rewrite min_0_l; simpl.
    elim (equiv_dec a a); intro; try congruence.
    rewrite IHl; rewrite H0; auto with arith.
    rewrite IHl.
    generalize (min_against_one (mult l a)); intro.
    elim H; intro; clear H; rewrite H0.
    simpl; elim (equiv_dec x a); intro; try congruence.
    rewrite IHl; reflexivity.
  Qed.

  Lemma mult_pos_equiv_in:
    forall l,
    forall x,
      mult l x > 0 <-> In x l.
  Proof.
    split.
    - (* Case "->" *)
      induction l; simpl; try lia.
      case (equiv_dec x a).
      + intros Hx.
        rewrite Hx in *; clear Hx.
        left.
        reflexivity.
      + intros Hx Hl.
        right.
        apply IHl.
        assumption.
    - (* Case "<-" *)
      induction l; simpl; try contradiction.
      intros Hx.
      destruct Hx.
      + rewrite H in *; clear H.
        case (equiv_dec x x); try congruence.
        intros.
        apply gt_Sn_O.
      + case (equiv_dec x a).
        * intros.
          apply gt_Sn_O.
        * intros.
          apply IHl.
          assumption.
  Qed.

  Lemma bdistinct_same_elemts:
    forall l,
    forall x,
      In x l -> In x (bdistinct l).
  Proof.
    intros l x Hx.
    apply mult_pos_equiv_in.
    apply mult_pos_equiv_in in Hx.
    rewrite bdistinct_mult.
    apply min_case; auto.
  Qed.

  Lemma bdistinct_nil {l:list A} :
    bdistinct l = nil -> l = nil.
  Proof.
    induction l; simpl; trivial.
    destruct (bdistinct l); simpl.
    - discriminate.
    - match_destr.
  Qed.

  Lemma bdistinct_NoDup (l : list A) :
    NoDup (bdistinct l).
  Proof.
    induction l; simpl; [constructor | ].
    match_case; intros.
    constructor; trivial.
    rewrite <- mult_pos_equiv_in.
    lia.
  Qed.

  Lemma NoDup_bdistinct {l:list A} :
    NoDup l -> bdistinct l = l.
  Proof.
    induction l; simpl; trivial.
    inversion 1; subst.
    rewrite IHl by trivial.
    rewrite <- mult_pos_equiv_in in H2.
    match_case.
    intros; lia.
  Qed.

  Lemma bdistinct_idem {l:list A} :
    bdistinct (bdistinct l) = bdistinct l.
  Proof.
    apply (@NoDup_bdistinct (bdistinct l)); trivial.
    apply bdistinct_NoDup.
  Qed.

  Lemma bdistinct_equivlist  (l : list A) :
    equivlist l (bdistinct l).
  Proof.
    intros.
    apply equivlist_incls.
    split.
    - intros ? inn.
      apply bdistinct_same_elemts; trivial.
    - rewrite bdistinct_sublist; reflexivity.
  Qed.

  
  Lemma fold_right_bdistinct (f : A -> A -> A)
        (assoc:forall x y z : A, f x (f y z) = f (f x y) z) 
        (comm:forall x y : A, f x y = f y x) 
        (idem:forall x  : A, f x x = x) (l:list A) (unit:A) :
    fold_right f unit l = fold_right f unit (bdistinct l).
  Proof.
    induction l; simpl; trivial.
    match_case; simpl; rewrite IHl; trivial; intros.
    assert (inn:In a (bdistinct l))
      by (apply mult_pos_equiv_in; lia).
    destruct (in_split _ _ inn) as [t1 [t2 teq]].
    rewrite teq.
    assert (perm:Permutation (t1 ++ a :: t2) (a::t1++ t2))
      by (rewrite Permutation_middle; reflexivity).
    rewrite (fold_right_perm _ assoc comm (t1 ++ a :: t2) (a :: t1 ++ t2))
      by trivial.
    simpl.
    rewrite assoc, idem.
    trivial.
  Qed.
  
  Lemma fold_right_equivlist (f : A -> A -> A)
  (assoc:forall x y z : A, f x (f y z) = f (f x y) z) 
  (comm:forall x y : A, f x y = f y x) 
  (idem:forall x  : A, f x x = x) (l1 l2:list A) (unit:A) :
    equivlist l1 l2 ->
    fold_right f unit l1 = fold_right f unit l2.
  Proof.
    intros.
    rewrite (fold_right_bdistinct _ assoc comm idem l1);
      rewrite (fold_right_bdistinct _ assoc comm idem l2).
    apply fold_right_perm; trivial.
    apply NoDup_Permutation'; trivial.
    - apply bdistinct_NoDup.
    - apply bdistinct_NoDup.
    - repeat rewrite <- bdistinct_equivlist.
      trivial.
  Qed.
  
  Lemma bunion_mult:
    forall (s t:list A), forall (x:A), mult (s ⊎ t) x = (mult s x) + (mult t x).
  Proof.
    intros.
    induction s.
    - unfold bunion; rewrite app_nil_l; simpl; reflexivity.
    - unfold bunion in *; simpl.
      destruct (equiv_dec x a).
      + rewrite IHs; auto.
      + assumption.
  Qed.

  Lemma remove_one_mult:
    forall (s:list A), forall (x:A), mult (remove_one x s) x = pred (mult s x).
  Proof.
    intros.
    induction s; simpl.
    - reflexivity.
    - destruct (equiv_dec x a).
      + auto.
      + simpl.
        destruct (equiv_dec x a).
        contradiction.
        assumption.
  Qed.

  Lemma mult_on_remove:
    forall (s:list A), forall (a x:A),
      x <> a -> mult (remove_one a s) x = mult s x.
  Proof.
    intros; induction s.
    simpl; reflexivity.
    simpl.
    elim (equiv_dec a a0); intro; simpl.
    - rewrite a1 in *; clear a1.
      elim (equiv_dec x a0); intro. 
      rewrite a1 in *; clear a1; congruence.
      elim (equiv_dec a a); intro; [reflexivity|congruence].
    - elim (equiv_dec x a0); intro; auto; assumption.
  Qed.

  Lemma bminus_mult:
    forall (s t:list A), forall (x:A), mult (s ⊖ t) x = (mult s x) - (mult t x).
  Proof.
    intros; revert s.
    induction t; simpl.
    intro. rewrite <- minus_n_O; reflexivity.
    intros; rewrite IHt.
    destruct (equiv_dec x a).
    rewrite e in *; clear e.
    rewrite remove_one_mult.
    generalize (exist_or_zero s a); intros.
    elim H; intros; clear H.
    elim H0; intros; clear H0.
    rewrite <- H in *; simpl.
    elim (equiv_dec a a); intro; try congruence; auto.
    rewrite H0; auto.
    generalize (mult_on_remove s a x); intro.
    unfold complement,equiv in c.
    auto.
  Qed.
      
  Lemma bmin_on_nil_r:
    forall (s:list A), (s min-b nil) = nil.
  Proof.
    intros.
    induction s; unfold bmin.
    rewrite bminus_naught; reflexivity.
    simpl; destruct (equiv_dec a a).
    rewrite bminus_self; reflexivity.
    congruence.
  Qed.

  Lemma bmin_on_nil_l:
    forall (s:list A), (nil min-b s) = nil.
  Proof.
    intros.
    induction s; unfold bmin; rewrite bminus_to_nil; reflexivity.
  Qed.

  Lemma bmax_on_nil_r:
    forall (s:list A), (s max-b nil) = s.
  Proof.
    intros.
    induction s; unfold bmax.
    rewrite bminus_naught; reflexivity.
    simpl; destruct (equiv_dec a a); rewrite bminus_to_nil; rewrite bunion_nil_r; reflexivity.
  Qed.

  Lemma bmax_on_nil_l:
    forall (s:list A), (nil max-b s) = s.
  Proof.
    intros; unfold bmax; reflexivity.
  Qed.

    Lemma bmin_Forall P (l1 l2 : list A) :
    Forall P l1 -> Forall P l2 -> Forall P (bmin l1 l2).
  Proof.
    unfold bmin.
    intros.
    repeat apply bminus_Forall; trivial.
  Qed.

  Lemma bmax_Forall P (l1 l2 : list A) :
    Forall P l1 -> Forall P l2 -> Forall P (bmax l1 l2).
  Proof.
    unfold bmax.
    intros.
    apply bunion_Forall; trivial.
    apply bminus_Forall; trivial.
  Qed.

  Lemma minus_min:
    forall (n n0:nat), n0 - (n0 - n) = min n0 n.
  Proof.
    induction n.
    intros; rewrite min_0_r; rewrite <- minus_n_O; rewrite minus_diag; reflexivity.
    intros.
    generalize eq_nat_dec; intro.
    elim (H n n0); intro; clear H.
    rewrite a in *; clear a.
    assert (n0 <= (S n0)); auto.
    rewrite (min_l n0 (S n0) H); lia.
    generalize (compare_either n0 (S n)); intro.
    elim H; intro; clear H.
    - rewrite min_l; try assumption; lia.
    - rewrite min_r; try assumption; lia.
  Qed.    

  Lemma minus_max:
    forall (n n0:nat), n0 + (n - n0) = max n0 n.
  Proof.
    induction n; intros.
    rewrite max_0_r; auto with arith.
    generalize eq_nat_dec; intro.
    elim (H n n0); intro; clear H.
    rewrite a in *; clear a.
    assert (n0 <= (S n0)); auto.
    rewrite (max_r n0 (S n0) H); lia.
    generalize (compare_either n0 (S n)); intro.
    elim H; intro; clear H.
    - rewrite max_r; try assumption; lia.
    - rewrite max_l; try assumption; lia.
  Qed.

  Lemma bmin_mult:
    forall (s t:list A), forall (x:A), (mult (s min-b t) x) = min (mult s x) (mult t x).
  Proof.
    intros.
    unfold bmin.
    repeat rewrite bminus_mult; induction s; simpl.
    - reflexivity.
    - elim (equiv_dec x a); intro.
      + rewrite a0 in *; clear a0.
        revert IHs; generalize (mult s a); generalize (mult t a); intros.
        rewrite minus_min; reflexivity.
      + generalize (mult s x); generalize (mult t x); intros.
        rewrite minus_min; reflexivity.
  Qed.

  Lemma bmax_mult:
    forall (s t:list A), forall (x:A), (mult (s max-b t) x) = max (mult s x) (mult t x).
  Proof.
    intros.
    unfold bmax.
    rewrite bunion_mult; rewrite bminus_mult; induction s; simpl.
    - auto with arith.
    - elim (equiv_dec x a); intro.
      + rewrite a0 in *; clear a0.
        revert IHs; generalize (mult s a); generalize (mult t a); intros.
        rewrite minus_max; reflexivity.
      + generalize (mult s x); generalize (mult t x); intros.
        rewrite minus_max; reflexivity.
  Qed.

  (* This is a first proof that relies on Avi's nice mult-based lemma *)
  Lemma bmin_comm:
    forall (s t:list A), (s min-b t) ≅ (t min-b s).
  Proof.
    intros.
    apply bags_same_mult_has_equal.
    intro.
    rewrite (bmin_mult s t a).
    rewrite (bmin_mult t s a).
    rewrite min_comm.
    reflexivity.
  Qed.

  Lemma bmax_comm:
    forall (s t:list A), (s max-b t) ≅ (t max-b s).
  Proof.
    intros.
    apply bags_same_mult_has_equal.
    intro.
    rewrite (bmax_mult s t a).
    rewrite (bmax_mult t s a).
    rewrite max_comm.
    reflexivity.
  Qed.

  (* Some other lemmas... *)

  Lemma select_not_select:
    forall (p:A -> bool), forall (s:list A), 
      ((filter p s) ⊎ (filter (fun x => negb (p x)) s)) ≅ s.
  Proof.
    intros.
    induction s.
    simpl; reflexivity.
    simpl.
    generalize (two_cases p a); intro.
    elim H; intro; rewrite H0; simpl;
    rewrite bunion_comm in *; unfold bunion in *;
    try rewrite <- app_comm_cons; rewrite IHs; reflexivity.
  Qed.

  Lemma bdistinct_over_bunion_empty_r:
    forall (l1 l2:list A), forall (x:A),
      (mult (bdistinct (l1 ⊎ l2)) x = 0) -> (mult (bdistinct l2) x = 0).
  Proof.
    unfold bunion in *.
    induction l1; intros; simpl in *; try assumption.
    elim (equiv_dec x a); intro.
    rewrite a0 in *; clear a0.
    assert (((mult (bdistinct (l1++l2)) a) = 0) \/ ((mult (bdistinct (l1++l2)) a) = 1)).
    apply bdistinct_at_most_one.
    elim H0; intros; clear H0.
    apply (IHl1 l2 a); try assumption.
    rewrite H1 in H.
    congruence.
    apply (IHl1 l2 x); simpl in H.
    assert (((mult (bdistinct (l1++l2)) a) = 0) \/ ((mult (bdistinct (l1++l2)) a) = 1)).
    apply bdistinct_at_most_one.
    elim H0; intros; clear H0.
    rewrite H1 in H.
    simpl in H.
    revert H.
    elim (equiv_dec x a); intro.
    rewrite a0 in *; clear a0.
    congruence.
    intro; assumption.
    rewrite H1 in H.
    assumption.
  Qed.

  Lemma bdistinct_over_bunion_empty_l:
    forall (l1 l2:list A), forall (x:A),
      (mult (bdistinct (l1 ⊎ l2)) x = 0) -> (mult (bdistinct l1) x = 0).
  Proof.
    intros; rewrite bdistinct_mult in *; rewrite bunion_mult in *.
    induction l1; simpl in *; try reflexivity.
    revert H; elim (equiv_dec x a); intros.
    rewrite a0 in *; clear a0; simpl in *.
    - congruence.
    - apply IHl1; assumption.
  Qed.

  Lemma bdistinct_over_bunion_singleton2:
    forall (l1 l2:list A), forall (x:A),
      (mult (bdistinct l2) x = 0) -> (mult (bdistinct l1) x = 1) -> (mult (bdistinct (l1 ⊎ l2)) x = 1).
  Proof.
    intros; rewrite bdistinct_mult in *; rewrite bunion_mult in *.
    induction l1; simpl in *; try congruence.
    revert H0; elim (equiv_dec x a); intros.
    - rewrite a0 in *; clear a0; simpl in *.
      revert H IHl1 H0; generalize (mult l1 a); generalize (mult l2 a); intros.
      assert (n = 0).
      + apply min_zero with (n2 := 0); assumption.
      + clear H; rewrite H1 in *; rewrite plus_0_r in *; assumption.
    - apply IHl1; assumption.
  Qed.
  
  Lemma bdistinct_over_bunion:
    forall (l1 l2:list A),
      (bdistinct (l1 ⊎ l2)) ≅ ((bdistinct l1) max-b (bdistinct l2)).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bmax_mult.
    repeat rewrite bdistinct_mult.
    rewrite bunion_mult.
    generalize (mult l1 a); generalize (mult l2 a); intros.
    generalize (min_against_one n); generalize (min_against_one n0); intros.
    elim H; elim H0; intros; clear H H0; rewrite H1; rewrite H2; simpl.
    - assert (n = 0).
      apply min_zero with (n2 := 0); assumption.
      assert (n0 = 0).
      apply min_zero with (n2 := 0); assumption.
      rewrite H; rewrite H0; reflexivity.
    - assert (n0 = 0).
      apply min_zero with (n2 := 0); assumption.
      rewrite H; assumption.
    - assert (n = 0).
      apply min_zero with (n2 := 0); assumption.
      rewrite H; rewrite plus_0_r; assumption.
    - assert (1 <= n).
      apply min_one_yields_one; assumption.
      assert (1 <= n0).
      apply min_one_yields_one; assumption.
      generalize (compare_either (n+n0) 1); intro; elim H; intros; clear H.
      rewrite min_r; try reflexivity.
      lia.
      rewrite <- plus_n_Sm.
      simpl.
      rewrite min_r.
      reflexivity.
      auto with arith.
  Qed. 

  Lemma bmin_zero:
    forall (l1 l2:list A), forall (x:A),
      mult (l1 min-b l2) x = 0 -> (mult l1 x = 0) \/ (mult l2 x = 0).
  Proof.
    induction l2; simpl; intros.
    right; reflexivity.
    rewrite bmin_mult in H.
    simpl in H.
    revert H; elim (equiv_dec x a); intro.
    rewrite a0 in *; clear a0.
    intro; left; apply (min_zero (mult l1 a) (mult l2 a)); assumption.
    intro.
    rewrite <- bmin_mult in H.
    apply (IHl2 x); assumption.
  Qed.

  Lemma bmin_zero_back:
    forall (l1 l2:list A), forall (x:A),
      (mult l1 x = 0) \/ (mult l2 x = 0) -> mult (l1 min-b l2) x = 0.
  Proof.
    induction l2; simpl; intros; rewrite bmin_mult; simpl.
    rewrite min_0_r; reflexivity.
    revert H; elim (equiv_dec x a); intros.
    rewrite a0 in *; clear a0.
    elim H; intro; clear H.
    rewrite H0 in *.
    generalize (mult l2 a); auto.
    rewrite H0 in *.
    generalize (mult l1 a); intro; rewrite min_0_r; reflexivity.
    elim H; intro; clear H; rewrite H0.
    generalize (mult l1 a); auto.
    generalize (mult l1 a); intro; rewrite min_0_r; reflexivity.
  Qed.

  Lemma bdistinct_over_bmin:
    forall (l2 l1:list A),
      (bdistinct (l1 min-b l2)) ≅ ((bdistinct l1) min-b (bdistinct l2)).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intro.
    rewrite bdistinct_mult.
    repeat rewrite bmin_mult.
    repeat rewrite bdistinct_mult.
    generalize (mult l1 a); intro.
    generalize (mult l2 a); intro.
    generalize (min_against_one n); intro.
    generalize (min_against_one n0); intro.
    elim H; intro; clear H; elim H0; intro; clear H0; rewrite H; rewrite H1.
    assert (n = 0); try (apply (min_zero n 0); assumption).
    assert (n0 = 0); try (apply (min_zero n0 0); assumption).
    rewrite H0; rewrite H2; auto with arith.
    assert (n = 0); try (apply (min_zero n 0); assumption).
    rewrite H0; auto with arith.
    assert (n0 = 0); try (apply (min_zero n0 0); assumption).
    rewrite H0; rewrite min_0_r; auto with arith.
    simpl; generalize (compare_either n n0); intro.
    elim H0; intro; clear H0.
    assert (min n n0 = n). try (rewrite min_l; [reflexivity|assumption]).
    rewrite H0; assumption.
    assert (min n n0 = n0). try (rewrite min_r; [reflexivity|assumption]).
    rewrite H0; assumption.
  Qed.

  Lemma split_select:
    forall (p:A -> bool), forall (s:list A),
      exists (sp nsp:list A),
        (sp ⊎ nsp) ≅ s /\
        (filter p sp) = sp /\
        (filter p nsp) = nil.
  Proof.
    intros.
    assert (s ≅ ((filter p s) ⊎ (filter (fun x => negb (p x)) s))).
    rewrite (select_not_select p) with (s := s); reflexivity.
    exists (filter p s).
    exists (filter (fun x : A => negb (p x)) s).
    split;[rewrite <- H; reflexivity|split].
    - rewrite filter_filter; reflexivity.
    - rewrite filter_not_filter; reflexivity.
  Qed.      

  Lemma mult_filter_true l {p a} : 
    p a = true -> 
    mult (filter p l) a = mult l a.
  Proof.
    intros eqf.
    induction l; simpl; trivial.
    case_eq (equiv_dec a a0); intros; try rewrite e in *; subst.
    - rewrite eqf; simpl. rewrite H; auto.
    - destruct (p a0); auto; simpl. rewrite H; auto.
  Qed.

  Lemma mult_filter_false l {p a} : 
    p a = false -> 
    mult (filter p l) a = 0.
  Proof.
    intros eqf.
    induction l; simpl; trivial.
    case_eq (p a0); auto; simpl; intros. 
    case_eq (equiv_dec a a0); intros; subst; intuition; congruence.
  Qed.

  (* Minimal solution support *)

  Definition bminus_delta2 (Q dQm dQp:list A) :=
    (Q min-b dQm) ⊖ dQp.

  Definition bplus_delta2 (Q dQm dQp:list A) :=
    dQp ⊖ (Q min-b dQm).

  Definition apply_deltas (Q dQm dQp: list A) :=
    (Q ⊖ dQm) ⊎ dQp.

  Lemma theorem2_a:
    forall (Q dQm dQp: list A),
      (apply_deltas Q dQm dQp) ≅
      (apply_deltas Q (bminus_delta2 Q dQm dQp) (bplus_delta2 Q dQm dQp)).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intro.
    unfold apply_deltas.
    unfold bminus_delta2; unfold bplus_delta2.
    repeat rewrite bunion_mult.
    repeat rewrite bminus_mult.
    repeat rewrite bmin_mult.
    generalize (mult Q a) as nQ; intro.
    generalize (mult dQm a) as ndQm; intro.
    generalize (mult dQp a) as ndQp; intro.
    generalize (compare_either nQ ndQm); intro.
    elim H; intro; clear H.
    - rewrite min_l; try assumption; lia.
    - rewrite min_r; try assumption; lia.
  Qed.

  Lemma theorem2_b:
    forall (Q dQm dQp: list A),
      ((bminus_delta2 Q dQm dQp) ⊖ Q) ≅ nil.
  Proof.
    intros.
    apply bags_same_mult_has_equal; intro; simpl.
    unfold bminus_delta2.
    repeat rewrite bminus_mult.
    rewrite bmin_mult.
    generalize (mult Q a) as nQ; intro.
    generalize (mult dQm a) as ndQm; intro.
    generalize (mult dQp a) as ndQp; intro.
    generalize (compare_either nQ ndQm); intro.
    elim H; intro; clear H.
    - rewrite min_l; try assumption; lia.
    - rewrite min_r; try assumption; lia.
  Qed.

  Lemma theorem2_c:
    forall (Q dQm dQp: list A),
      ((bminus_delta2 Q dQm dQp) min-b (bplus_delta2 Q dQm dQp)) ≅ nil.
  Proof.
    intros.
    apply bags_same_mult_has_equal; intro; simpl.
    unfold bminus_delta2; unfold bplus_delta2.
    rewrite bmin_mult.
    repeat rewrite bminus_mult.
    repeat rewrite bmin_mult.
    generalize (mult Q a) as nQ; intro.
    generalize (mult dQm a) as ndQm; intro.
    generalize (mult dQp a) as ndQp; intro.
    generalize (compare_either nQ ndQm); intro.
    elim H; intros; clear H.
    - assert (min nQ ndQm = nQ).
      rewrite min_l; [reflexivity|assumption].
      rewrite H.
      generalize (compare_either nQ ndQp); intro.
      elim H1; intros; clear H1.
      + rewrite min_l; lia.
      + rewrite min_r; lia.
    - assert (min nQ ndQm = ndQm).
      rewrite min_r; [reflexivity|assumption].
      rewrite H.
      generalize (compare_either ndQm ndQp); intro.
      elim H1; intros; clear H1.
      + rewrite min_l; lia.
      + rewrite min_r; lia.
  Qed.

  Lemma remove_one_bminus r s a:
    ((remove_one a s) ⊖ r) = (s ⊖ (a :: r)).
  Proof.
    revert s r. induction r; intros; reflexivity.
  Qed.

  Lemma remove_bminus_comm r s a:
    ((remove_one a s) ⊖ r) = (remove_one a (s ⊖ r)).
  Proof.
    revert r s.
    induction r; intros; simpl.
    - reflexivity.
    - rewrite remove_one_comm.
      rewrite (IHr (remove_one a0 s)).
      reflexivity.
  Qed.

  Lemma filter_remove_one_false s {p a} : p a = false ->
      (filter p (remove_one a s)) = filter p s.
  Proof.
    intros eqf.
    induction s; simpl; trivial.
    case_eq (equiv_dec a a0); intros; subst; simpl.
    rewrite e in *.
    - rewrite eqf; auto.
    - case_eq (p a0); intros eqf0; rewrite IHs; reflexivity.
  Qed.

  Lemma filter_remove_one s {p a} :
      (filter p (remove_one a s)) = remove_one a (filter p s).
  Proof.
    induction s; simpl; trivial.
    case_eq (equiv_dec a a0); intros; subst; simpl.
    - red in e; subst.
      case_eq (p a0); intros eqf0; simpl.
      elim (equiv_dec a0 a0); intro.
      reflexivity.
      congruence.
      rewrite filter_remove_one_false in IHs; auto.
    - case_eq (p a0); intros eqf0; simpl.
      elim (EquivDec.equiv_dec a a0); intro.
      congruence.
      rewrite IHs; reflexivity.
      assumption.
  Qed.

  Lemma bunion_filter (s:list A) (ds:list A) (p:A -> bool):
      (filter p (s ⊎ ds)) = ((filter p s) ⊎ (filter p ds)).
  Proof.
    intros; unfold bunion.
    induction s; simpl.
    - reflexivity.
    - generalize (two_cases p a); intro.
      elim H; intro; rewrite H0; try rewrite <- app_comm_cons; rewrite IHs; reflexivity.
  Qed.

  Lemma bminus_filter (p:A -> bool) (s ds:list A) : (filter p (s ⊖ ds)) = ((filter p s) ⊖ (filter p ds)).
  Proof.
    revert s.
    induction ds; simpl; auto; intros.
    rewrite IHds.
    case_eq (p a); intros eqf; simpl.
    - rewrite filter_remove_one; auto.
    - rewrite filter_remove_one_false; trivial.
  Qed.

End Bag.

Section NumMinMax.
  Open Scope Z_scope.

  Definition bnummin (l:list Z) :=
    match l with
    | nil => 0
    | x0 :: l' =>
      fold_right (fun x y => Z.min x y) x0 l'
    end.

  Definition bnummax (l:list Z) :=
    match l with
    | nil => 0
    | x0 :: l' =>
      fold_right (fun x y => Z.max x y) x0 l'
    end.
  
End NumMinMax.

(* Post section rewrites and notations *)
Hint Rewrite 
     bminus_nil_to_self 
     bminus_to_nil
     bminus_self 
     bminus_naught 
     bminus_cons 
     app_nil_r 
     bunion_bminus 
     remove_one_consed : bag.

#[global]
Hint Unfold ldeqA : fml.
#[global]
Hint Unfold mult_equiv : fml.

