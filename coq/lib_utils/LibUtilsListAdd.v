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

(** This module contains additional definitions and lemmas on
lists. *)

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
Require Import Program.Basics.

Section ListAdd.
  (** * Miscellaneous operations on lists *)
  
  Section Misc.
    Context {A:Type}.

    Lemma app_inv_self_l (l l2:list A) :
      l = l ++ l2 -> l2 = nil.
    Proof.
      intros eqq1.
      assert (eqq2:l ++ nil = l ++ l2) by (rewrite app_nil_r; trivial).
      apply app_inv_head in eqq2.
      congruence.
    Qed.

    Lemma app_inv_self_r (l l2:list A) :
      l = l2 ++ l -> l2 = nil.
    Proof.
      intros eqq1.
      assert (eqq2:nil ++ l = l2 ++ l) by (simpl; trivial).
      apply app_inv_tail in eqq2.
      congruence.
    Qed.

    Lemma length_app_other_tail {l1 l2 l1' l2' : list A} :
      length (l1 ++ l2) = length (l1' ++ l2') ->
      length l2 = length l2' ->
      length l1 = length l1'.
    Proof.
      repeat rewrite app_length.
      intros eqq1 eqq2.
      rewrite eqq2 in eqq1.
      assert (pm:Datatypes.length l1 + Datatypes.length l2' - Datatypes.length l2' =
                 Datatypes.length l1' + Datatypes.length l2' - Datatypes.length l2').
      { rewrite eqq1; trivial. }
      repeat rewrite Nat.add_sub in pm; trivial.
    Qed.

    Lemma length_app_other_head {l1 l2 l1' l2' : list A} :
      length (l1 ++ l2) = length (l1' ++ l2') ->
      length l1 = length l1' ->
      length l2 = length l2'.
    Proof.
      intros eqqs.
      apply length_app_other_tail.
      repeat rewrite app_length in *.
      rewrite plus_comm, eqqs, plus_comm; trivial.
    Qed.

    Lemma app_inv_head_length {l1 l2 l1' l2' : list A} :
      l1 ++ l2 = l1' ++ l2' ->
      length l1 = length l1' ->
      l1 = l1' /\ l2 = l2'.
    Proof.
      revert l1'.
      induction l1; destruct l1'; try discriminate; simpl; intros eqlen eqq.
      - subst; eauto.
      - invcs eqq.
        invcs eqlen.
        specialize (IHl1 _ H2 H0).
        destruct IHl1; subst.
        tauto.
    Qed.

    Lemma app_inv_tail_length {l1 l2 l1' l2' : list A} :
      l1 ++ l2 = l1' ++ l2' ->
      length l2 = length l2' ->
      l1 = l1' /\ l2 = l2'.
    Proof.
      intros eqq eql.
      apply app_inv_head_length; trivial.
      eapply length_app_other_tail; eauto.
      rewrite eqq; trivial.
    Qed.

    Definition singleton (x:A) : list A := x::nil.
    
    Lemma is_nil_dec (l:list A) : {l = nil} + {l <> nil}.
    Proof.
      destruct l.
      - eauto.
      - right; inversion 1.
    Qed.

    Fixpoint lflatten (l:list (list A)) : list A :=
      match l with
      | nil => nil
      | l1 :: l' =>
        l1 ++ (lflatten l')
      end.

    Lemma flat_map_app {B} (f:A->list B) l1 l2 :
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
    Proof.
      induction l1; simpl; trivial.
      rewrite app_ass. congruence.
    Qed.

    Lemma flat_map_singleton a : flat_map (fun d : A => d::nil) a = a.
    Proof.
      induction a; simpl; trivial.
      rewrite IHa; trivial.
    Qed.
    
    Lemma map_nil f l :
      map f l = (@nil A) <-> l = (@nil A).
    Proof.
      split; intros.
      - induction l; try reflexivity; simpl in *.
        congruence.
      - rewrite H; reflexivity.
    Qed.
    
    Lemma eq_means_same_length :
      forall (l1 l2:list A),
        l1 = l2 -> (length l1) = (length l2).
    Proof.
      intros; rewrite H; reflexivity.
    Qed.

    Lemma app_cons_middle (l1 l2:list A) (a:A) :
      l1 ++ (a::l2) = (l1 ++ (a::nil))++l2.
    Proof.
      induction l1.
      reflexivity.
      simpl.
      rewrite IHl1.
      reflexivity.
    Qed.

    Lemma map_app_break {B:Type} (f:A->B) {a b c} :
      map f a = b ++ c ->
      {b':list A & {c' : list A | a = b' ++ c' /\ b = map f b' /\ c = map f c'}}.
    Proof.
      revert a c.
      induction b; simpl; intros a' c eqq.
      - exists nil; exists a'; auto.
      - destruct a'; simpl in eqq; try discriminate.
        invcs eqq.
        destruct (IHb _ _ H1) as [b' [c' [? [??]]]]; subst.
        exists (a0::b'); exists c'; auto.
    Qed.

    Lemma map_inj_strong {B} (f g:A->B) (l1 l2:list A)
          (inj:forall (x y:A), In (f x) (map f l1) -> In (g y) (map g l2) -> f x = g y -> x = y) :
      map f l1 = map g l2 ->
      l1 = l2.
    Proof.
      revert l2 inj.
      induction l1; simpl; destruct l2; simpl; intros inj eqq; trivial; try discriminate.
      invcs eqq.
      f_equal; auto.
    Qed.
    
    Lemma map_inj {B} (f g:A->B) (l1 l2:list A)
          (inj:forall (x y:A), f x = g y -> x = y) :
      map f l1 = map g l2 ->
      l1 = l2.
    Proof.
      apply map_inj_strong; auto.
    Qed.

    Lemma app_cons_cons_expand (l:list A) a b :
      l ++ a::b::nil = (l ++ a ::nil)++b::nil.
    Proof.
      rewrite app_ass.
      simpl.
      trivial.
    Qed.

    Lemma in_split_first {dec:EqDec A eq} (x : A) (l : list A) :
      In x l -> exists l1 l2 : list A, l = l1 ++ x :: l2 /\ ~ In x l1.
    Proof.
      induction l; simpl; try contradiction.
      destruct (a == x); unfold equiv, complement in *.
      - subst; exists nil, l; simpl; tauto.
      - intros [eqq|inn].
        + congruence.
        + destruct (IHl inn) as [l1 [l2 [eqq nin]]]; subst.
          exists (a::l1), l2; split; trivial.
          simpl.
          tauto.
    Qed.

    Lemma concat_In y (l:list (list A)) : In y (concat l) <-> (exists x : list A, In x l /\ In y x).
    Proof.
      rewrite <- in_flat_map.
      rewrite flat_map_concat_map.
      rewrite map_id.
      reflexivity.
    Qed.

    Lemma in_in_split_or {dec:EqDec A eq} (l:list (list A)) a :
      (exists l1 la l2, l = l1++la::l2 /\ In a la /\ ~ In a (concat l1))
      \/ Forall (fun x => ~ In a x) l.
    Proof.
      induction l; simpl; [ right; trivial | ].
      destruct (in_dec dec a a0) as [inn1|nin1].
      - left.
        destruct (in_split_first _ _ inn1)
          as [? [? [??]]]; subst.
        exists (nil). 
        exists (x ++ a::x0).
        exists l.
        simpl; eauto.
      - destruct IHl as [[l1 [la [l2 [eqq [inn2 nin2]]]]]|nin2].
        + left; subst.
          exists (a0::l1), la, l2.
          repeat split; trivial.
          rewrite concat_In.
          simpl.
          intros [? [inn3 inn4]].
          destruct inn3.
          * subst; eauto.
          * apply nin2.
            apply concat_In; eauto.
        + right.
          constructor; trivial.
    Qed.

    Lemma Permutation_in_nin_inv {l1:list A} {l1' l2 l2'} :
      Permutation (l1::l1') (l2::l2') -> forall a,
        In a l1 -> ~ In a (concat l2') ->
        l1 = l2 /\ Permutation l1' l2'.
    Proof.
      intros perm a inn nin.
      assert (inn1:In l1 (l2::l2')).
      { rewrite <- perm; simpl; eauto. }
      simpl in inn1.
      destruct inn1 as [eqq|inn1].
      - subst; split; trivial.
        apply Permutation_cons_inv in perm; trivial.
      - elim nin.
        apply concat_In; eauto.
    Qed.
    
  End Misc.
  
  Lemma Permutation_cons_nin_map {A B} (f:A->B) x l₁ y l₂ :
    Permutation (x::l₁) (y::l₂) ->
    f x = f y ->
    ~ In (f x) (map f l₁) ->
    x = y /\ Permutation l₁ l₂.
  Proof.
    intros perm nin1 nin2.
    assert (inn1:In y (y :: l₂)) by (simpl; tauto).
    rewrite <- perm in inn1.
    simpl in inn1.
    invcs inn1.
    - apply Permutation_cons_inv in perm.
      tauto.
    - elim nin2.
      apply in_map_iff.
      exists y.
      rewrite nin1.
      tauto.
  Qed.
  
  (** * Properties of folds *)
  
  Section Fold.
    Context {A B C: Type}.
    
    Lemma fold_left_map
          (f:A -> C -> A) (g:B->C) (l:list B) (init:A) :
      fold_left f (map g l) init = fold_left (fun a b => f a (g b)) l init.
    Proof.
      revert init.
      induction l; simpl; trivial.
    Qed.

    Lemma fold_left_ext
          (f g:A -> B -> A) (l:list B) (init:A) :
      (forall x y, f x y = g x y) ->
      fold_left f l init = fold_left g l init.
    Proof.
      intros eqq.
      revert init.
      induction l; simpl; trivial; intros.
      rewrite eqq, IHl.
      trivial.
    Qed.

    Lemma fold_right_app_map_singleton l : 
      fold_right (fun a b : list A => a ++ b) nil
                 (map (fun x : A => (x::nil)) l) = l.
    Proof.
      induction l; simpl; congruence.
    Qed.

    Lemma fold_right_perm (f : A -> A -> A)
          (assoc:forall x y z : A, f x (f y z) = f (f x y) z) 
          (comm:forall x y : A, f x y = f y x) (l1 l2:list A) (unit:A) 
          (perm:Permutation l1 l2) :
      fold_right f unit l1 = fold_right f unit l2.
    Proof.
      revert l1 l2 perm.
      apply Permutation_ind_bis; simpl; intros.
      - trivial.
      - rewrite H0; trivial.
      - rewrite assoc, (comm y x), <- assoc, H0; trivial.
      - rewrite H0, H2; trivial.
    Qed.

  End Fold.

  (** * Properties of [Forall] *)
  
  Section Forall.
    Context {A:Type}.

    (* XXX Alternative to List.Forall but defined so it can be used for computation XXX *)
    Lemma Forall_dec_defined {P} :
      (forall x:A, {P x} + { ~ P x }) ->
      forall l:list A, {Forall P l} + {~ Forall P l}.
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - left. apply Forall_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_cons.
          * right. now inversion_clear 1.
        + right. now inversion_clear 1.
    Defined.

    Global Instance Forall_perm {P} : Proper ((@Permutation A) ==> iff) (@Forall A P).
    Proof.
      intros ? ? perm.
      repeat rewrite Forall_forall.
      split; intros H ? inn.
      - rewrite <- perm in inn; eauto.
      - rewrite perm in inn; eauto.
    Qed.
    
  End Forall.

  Lemma Forall_liftP_in {A} {f:A->Prop} {l} :
    Forall (liftP f) l ->
    forall x, In (Some x) l -> f x.
  Proof.
    rewrite Forall_forall; intros HH x inn.
    specialize (HH _ inn).
    simpl in HH; trivial.
  Qed.
  
  (** * Properties of [filter] *)
  
  Section Filter.
    Context {A:Type}.

    Lemma filter_length :
      forall (p:A -> bool), forall (l:list A),
          length l >= length (filter p l).
    Proof.
      intros.
      induction l; simpl.
      - auto.
      - elim (two_cases p a); intro; rewrite H; simpl; auto with arith.
    Qed.

    Lemma filter_smaller :
      forall (p:A -> bool), forall (l:list A), forall (x:A),
            filter p l <> x::l.
    Proof.
      intros.
      assert ((length (x::l)) > (length (filter p l))).
      simpl.
      assert ((length (filter p l) <= length l)).
      apply filter_length.
      auto with arith.
      assert ((length (x :: l)) <> (length (filter p l))).
      omega.
      unfold not in *; intro.
      apply H0.
      apply eq_means_same_length.
      rewrite H1.
      reflexivity.
    Qed.

    Lemma filter_filter :
      forall (p:A -> bool), forall (s:list A),
          filter p (filter p s) = filter p s.
    Proof.
      induction s.
      - reflexivity.
      - simpl. elim (two_cases p a); intro. rewrite H. simpl.
        rewrite H. rewrite IHs. reflexivity.
        rewrite H; rewrite IHs; reflexivity.
    Qed.

    Lemma filter_not_filter:
      forall (p:A -> bool), forall (s:list A),
          filter p (filter (fun x => negb (p x)) s) = nil.
    Proof.
      induction s.
      - simpl; reflexivity.
      - simpl; elim (two_cases p a); intro; rewrite H; simpl.
        rewrite IHs; reflexivity.
        rewrite H; assumption.
    Qed.

    Lemma filter_id_implies_pred :
      forall (p:A -> bool), forall (l:list A),
          filter p l = l -> forall (y:A), (In y l -> (p y = true)).
    Proof.
      intros.
      induction l; simpl in *; try contradiction.
      elim (two_cases p a); intro.
      rewrite H1 in H.
      elim H0; intro.
      rewrite <- H2; assumption.
      apply IHl.
      inversion H.
      rewrite filter_filter; reflexivity.
      assumption.
      rewrite H1 in H.
      clear H0 IHl H1.
      assert False.
      apply (filter_smaller p l a); assumption.
      contradiction.
    Qed.

    Lemma filter_nil_implies_not_pred :
      forall (p:A -> bool), forall (l:list A),
          filter p l = nil -> forall (y:A), (In y l -> (p y = false)).
    Proof.
      intros.
      induction l; simpl in *; try contradiction.
      elim (two_cases p a); intro; rewrite H1 in H.
      elim H0; intro; try discriminate.
      elim H0; intro.   
      rewrite <- H2; assumption.
      apply IHl; assumption.
    Qed.

    Lemma filter_comm:
      forall (x:list A) (p1 p2: A -> bool),
        (filter p1 (filter p2 x)) = (filter p2 (filter p1 x)).
    Proof.
      intros.
      induction x.
      simpl; reflexivity.
      simpl.
      generalize (four_cases p1 p2 a);intros.
      elim H; intro H1; elim H1; intro H2; elim H2; intros C1 C2; clear H H1 H2;
        rewrite C1; rewrite C2; simpl.
      - rewrite C1; rewrite C2; rewrite IHx; reflexivity. (* both predicates true *)
      - rewrite C2; rewrite IHx; reflexivity.             (* p1 true, p2 false *)
      - rewrite C1; rewrite IHx; reflexivity.             (* p2 true, p1 false *)
      - rewrite IHx; reflexivity.                         (* both predicates false *)
    Qed.

    Lemma filter_and:
      forall (x:list A) (p1 p2: A -> bool),
        (filter p1 (filter p2 x)) = (filter (fun a => andb (p1 a) (p2 a)) x).
    Proof.
      intros.
      induction x.
      simpl; reflexivity.
      simpl.
      generalize (four_cases p1 p2 a);intros.
      elim H; intro H1; elim H1; intro H2; elim H2; intros C1 C2; clear H H1 H2;
        rewrite C1; rewrite C2; simpl; try rewrite C1; rewrite IHx; reflexivity.
    Qed.

    Lemma filter_eq:
      forall (p1 p2:A -> bool),
        (forall x:A, p1 x = p2 x) -> (forall l:list A, filter p1 l = filter p2 l).
    Proof.
      intros.
      induction l.
      simpl; reflexivity.
      simpl; rewrite <- H.
      generalize (two_cases p1 a); intros; elim H0; intros; clear H0; rewrite H1.
      rewrite IHl; reflexivity.
      rewrite IHl; reflexivity.
    Qed.

    Lemma false_filter_nil {f} {l:list A} :
      (forall x, In x l -> f x = false) ->  filter f l = nil.
    Proof.
      induction l; simpl; trivial.
      intros.
      generalize (H a); intuition.
      rewrite H0.
      apply IHl; intuition.
    Qed.

    Lemma filter_app (f:A->bool) l1 l2 :
      filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
    Proof.
      induction l1; simpl; intuition.
      match_destr.
      rewrite IHl1; simpl; trivial.
    Qed.

    Lemma Forall_filter {P} {l:list A} f :
      Forall P l -> Forall P (filter f l).
    Proof.
      induction l; simpl; trivial.
      inversion 1; subst.
      destruct (f a); auto.
    Qed.    
    
    Lemma find_filter f (l:list A) :  find f l = hd_error (filter f l).
    Proof.
      induction l; simpl; trivial.
      destruct (f a); simpl; auto.
    Qed.

    Lemma filter_ext (f g : A -> bool) (l : list A) : 
      (forall x, In x l -> f x = g x) ->
      filter f l = filter g l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite IHl by intuition.
      rewrite (H a) by intuition.
      trivial.
    Qed.

    Lemma true_filter (f : A -> bool) (l : list A) :
      (forall x : A, In x l -> f x = true) -> filter f l = l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite H, IHl; intuition.
    Qed.

    Lemma filter_rev (f:A->bool) l :
      filter f (rev l) = rev (filter f l).
    Proof.
      induction l; simpl; trivial.
      rewrite filter_app, IHl.
      simpl.
      match_destr.
      rewrite app_nil_r.
      trivial.
    Qed.
    
  End Filter.

  (** * Permutation properties *)
  
  Section Perm_equiv.
    Context {A:Type}.
    Context {eqdec:EqDec A eq}.

    Definition ldeqA := (@Permutation A).

    Global Instance perm_equiv : Equivalence (@Permutation A).
    Proof.
      constructor.
      - unfold Reflexive; auto.
      - intros l1 l2.
        induction 1; eauto.
        apply perm_swap.
        apply perm_trans with (l' := l'); assumption.
      - unfold Transitive; apply perm_trans.
    Qed.

  End Perm_equiv.
  
  (** * Properties over two lists *)
  
  Section List2.
    (** ** Properties of [forallb2] *)
    
    Section forallb2.
      Fixpoint forallb2 {A B:Type} (f:A->B->bool) (l1:list A) (l2:list B): bool :=
        match l1,l2 with
        | nil, nil => true
        | a1::l1, a2::l2 => f a1 a2 && forallb2 f l1 l2
        | _, _ => false
        end.

      Lemma forallb2_forallb {A B:Type} (f:A->B->bool) :
        forall (l1:list A) (l2:list B), 
          (length l1 = length l2) ->
          forallb (fun xy => f (fst xy) (snd xy)) (combine l1 l2) = forallb2 f l1 l2.
      Proof.
        induction l1; destruct l2; simpl; intuition.
        f_equal; auto.
      Qed.

      Lemma forallb2_forallb_true {A B:Type} (f:A->B->bool) :
        forall (l1:list A) (l2:list B), 
          (length l1 = length l2 /\ forallb (fun xy => f (fst xy) (snd xy)) (combine l1 l2) = true)
          <->
          forallb2 f l1 l2 = true.
      Proof.
        induction l1; destruct l2; simpl; intuition;
          repeat rewrite andb_true_iff in *; firstorder.
      Qed.

      Lemma forallb2_Forallb {A B:Type} (f:A->B->bool) :
        forall l1 l2, forallb2 f l1 l2 = true <-> Forall2 (fun x y => f x y = true) l1 l2.
      Proof.
        Ltac inv := try match goal with 
                        | [H:Forall2 _ _ (_::_) |- _ ] => inversion H; clear H
                        | [H:Forall2 _ (_::_) _ |- _ ] => inversion H; clear H
                        end; firstorder.
        induction l1; destruct l2; simpl; intuition; inv;
          repeat rewrite andb_true_iff in *; firstorder.
      Qed.

      Lemma forallb2_eq {A B:Type} : forall (f1 f2:A->B->bool) l1 l2, 
          (forall x y, In x l1 -> In y l2 -> f1 x y = f2 x y) ->
          forallb2 f1 l1 l2 = forallb2 f2 l1 l2.
      Proof.
        induction l1; destruct l2; simpl; intuition.
        f_equal; auto.
      Qed.

      Lemma forallb2_sym {A B} : forall (f:A->B->bool) {l1 l2}, 
          forallb2 f l1 l2 = forallb2 (fun x y => f y x) l2 l1.
      Proof.
        induction l1; destruct l2; simpl; intuition.
        f_equal; trivial.
      Qed.
      
    End forallb2.

    (** ** Properties of [Forall2] *)
    
    Section Forall2.
      
      Lemma Forall2_incl {A B} : forall (f1 f2:A->B->Prop) l1 l2, 
        (forall x y, In x l1 -> In y l2 -> f1 x y-> f2 x y) ->
        Forall2 f1 l1 l2 -> Forall2 f2 l1 l2.
      Proof.
        intros.
        induction H0; firstorder.
      Qed.

      Lemma Forall2_map {A B C D} (f:C->D->Prop) (g:A->C) (h:B->D) a b:
        Forall2 (fun x y => f (g x) (h y)) a b <-> Forall2 f (map g a) (map h b).
      Proof.
        revert b.
        induction a; destruct b; simpl; split; inversion 1;
          eauto 2; subst; firstorder.
      Qed.

      Lemma Forall2_map_f {A B C D} (f:C->D->Prop) (g:A->C) (h:B->D) a b:
        Forall2 (fun x y => f (g x) (h y)) a b -> Forall2 f (map g a) (map h b).
      Proof.
        apply Forall2_map.
      Qed.

      Lemma Forall2_map_b {A B C D} (f:C->D->Prop) (g:A->C) (h:B->D) a b:
        Forall2 f (map g a) (map h b) -> Forall2 (fun x y => f (g x) (h y)) a b.
      Proof.
        apply Forall2_map.
      Qed.

      Lemma Forall2_length {A B} (f:A->B->Prop)  a b:
        Forall2 f a b -> length a = length b.
      Proof.
        revert b;
          induction a; inversion 1; subst; simpl; intuition.
      Qed.

      Global Instance Forall2_refl {A} R `{Reflexive A R} : Reflexive (Forall2 R).
      Proof.
        red.
        induction x; simpl; trivial.
        constructor; auto.
      Qed.

      Global Instance Forall2_sym {A} R `{Symmetric A R} : Symmetric (Forall2 R).
      Proof.
        red.
        induction x; simpl; inversion 1; subst; trivial.
        constructor; auto.
      Qed.

      Global Instance Forall2_trans {A} R `{Transitive A R} : Transitive (Forall2 R).
      Proof.
        red.
        induction x; simpl; inversion 1; subst; trivial.
        inversion 1; subst.
        constructor; eauto.
      Qed.

      Global Instance Forall2_pre {A} R `{PreOrder A R} : PreOrder (Forall2 R).
      Proof.
        destruct H.
        constructor; red.
        - apply Forall2_refl; trivial.
        - apply Forall2_trans; trivial.
      Qed.

      Global Instance Forall2_part_eq {A} R `{PartialOrder A eq R } :
        PartialOrder eq (Forall2 R).
      Proof.
        intros l1 l2.
        split; intros HH.
        - repeat red; subst; intuition.
        - repeat red in HH; intuition.
          revert l2 H0 H1.
          induction l1; destruct l2; trivial; intros F1 F2;
            invcs F1; invcs F2.
          + f_equal.
            * apply antisymmetry; trivial.
            * apply IHl1; trivial.
      Qed.

      Lemma Forall2_conj {A B} {f1 f2:A->B->Prop} {l1 l2} : 
        Forall2 f1 l1 l2 -> Forall2 f2 l1 l2 -> Forall2 (fun x y => f1 x y /\ f2 x y) l1 l2.
      Proof.
        intros.
        induction H0; trivial.
        invcs H; firstorder.
      Qed.

      Lemma Forall2_Forall_trans {A B} {P:A->Prop} {Q:B->Prop} l l' :
        Forall2 (fun x y => P x -> Q y) l l' ->
        Forall P l -> Forall Q l'.
      Proof.
        intros f2; induction f2; trivial.
        intros f1; invcs f1.
        eauto.
      Qed.
      
      Lemma Forall2_trans_relations_weak {A B C}
            (R1:A->B->Prop) (R2:B->C->Prop) (R3:A->C->Prop):
        (forall a b c, R1 a b -> R2 b c -> R3 a c) ->
        forall a b c, Forall2 R1 a b -> Forall2 R2 b c -> Forall2 R3 a c.
      Proof.
        intros pf.
        induction a; intros b c Fab Fbc
        ; invcs Fab; invcs Fbc; eauto.
      Qed.

      Lemma Forall2_eq {A} (l1 l2:list A): Forall2 eq l1 l2 <-> l1 = l2.
      Proof.
        split; intros; subst; [ | reflexivity ].
        revert l2 H; induction l1; inversion 1; subst; trivial.
        f_equal; eauto.
      Qed.

      Lemma Forall2_flip {A B} {P:A->B->Prop} {l1 l2} :
        Forall2 P l1 l2 -> Forall2 (fun x y => P y x) l2 l1.
      Proof.
        revert l2; induction l1; simpl; inversion 1; subst; auto.
      Qed.
      
      Lemma Forall2_In_l {A B} {P:A->B->Prop} {l1 l2 a} :
        Forall2 P l1 l2 ->
        In a l1 ->
        exists b,
          In b l2 /\
          P a b.
      Proof.
        revert l2 a. induction l1; simpl; [intuition |].
        inversion 1; subst; intros.
        intuition; subst; simpl; eauto.
        destruct (IHl1 _ _ H4 H1); intuition; eauto.
      Qed.

      Lemma Forall2_In_r {A B} {P:A->B->Prop} {l1 l2 b} :
        Forall2 P l1 l2 ->
        In b l2 ->
        exists a,
          In a l1 /\
          P a b.
      Proof.
        intros.
        apply Forall2_flip in H.
        apply (Forall2_In_l H H0).
      Qed.

      Lemma Forall2_app_tail_inv {A B} P l1 l2 a1 a2 :
        @Forall2 A B P (l1 ++ (a1::nil)) (l2 ++ (a2::nil)) ->
        Forall2 P l1 l2 /\ P a1 a2.
      Proof.
        intros.
        destruct (Forall2_app_inv_l _ _ H) as [?[?[f1 [f2 eqq]]]].
        inversion f2; subst.
        inversion H4; subst.
        apply app_inj_tail in eqq.
        destruct eqq; subst.
        auto.
      Qed.

      Lemma Forall2_app_inv {A B : Type} {R : A -> B -> Prop} {l1 l2 : list A} {l1' l2' : list B} :
        Forall2 R (l1 ++ l2) (l1' ++ l2') ->
        length l1 = length l1' ->
        Forall2 R l1 l1' /\ Forall2 R l2 l2'.
      Proof.
        intros F2 eql.
        apply Forall2_app_inv_l in F2.
        destruct F2 as [l1'' [l2'' [F21 [F22 eqq]]]].
        apply app_inv_head_length in eqq.
        - destruct eqq; subst; tauto.
        - rewrite <- eql.
          apply Forall2_length in F21; trivial.
      Qed.

      Lemma filter_Forall2_same {A B} P f g (l1:list A) (l2:list B) :
        Forall2 P l1 l2 ->
        map f l1 = map g l2 ->
        Forall2 P (filter f l1) (filter g l2).
      Proof.
        revert l2.
        induction l1; simpl; inversion 1; subst; simpl; trivial.
        inversion 1.
        rewrite H3.
        match_destr.
        + constructor; auto.
        + auto.
      Qed.
      
      Lemma Forall2_map_Forall {A B:Type} (P:A->B->Prop) (f:A->B) l :
        Forall2 P l (map f l) <-> Forall (fun x => P x (f x)) l.
      Proof.
        split
        ; induction l; simpl; trivial
        ; inversion 1; subst; auto.
      Qed.
      
    End Forall2.

  End List2.

  (** * Properties holding for all pairs in a list *)

  Section Forallb_ordpairs.

    Fixpoint forallb_ordpairs {A} f (l:list A)
      := match l with
         | nil => true
         | x::ls => forallb (f x) ls && forallb_ordpairs f ls
         end.

    Lemma forallb_ordpairs_ForallOrdPairs {A} f (l:list A) :
      forallb_ordpairs f l = true <-> (ForallOrdPairs (fun x y => f x y = true) l).
    Proof.
      induction l; simpl; intuition.
      - constructor.
      - rewrite andb_true_iff in H1.
        intuition.
        econstructor; trivial.
        rewrite Forall_forall.
        rewrite forallb_forall in H2.
        trivial.
      - rewrite andb_true_iff.
        rewrite forallb_forall.
        invcs H1.
        rewrite Forall_forall in H4.
        intuition.
    Qed.
    
    Lemma forallb_ordpairs_ext {A} f1 f2 (l:list A) :
      (forall x y, In x l -> In y l -> f1 x y = f2 x y) ->
      forallb_ordpairs f1 l = forallb_ordpairs f2 l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite IHl.
      - f_equal.
        apply forallb_ext.
        intuition.
      - intuition.
    Qed.

    Fixpoint forallb_ordpairs_refl {A} (f:A->A->bool) (l:list A)
      := match l with
         | nil => true
         | x::ls => forallb (f x) (x::ls) && forallb_ordpairs_refl f ls
         end.

    Lemma forallb_ordpairs_refl_conj A f (l:list A) :
      forallb_ordpairs_refl f l = forallb_ordpairs f l && forallb (fun x => f x x) l.
    Proof.
      induction l; simpl; trivial.
      rewrite IHl.
      repeat rewrite andb_assoc.
      f_equal.
      repeat rewrite <- andb_assoc.
      rewrite andb_comm.
      repeat rewrite andb_assoc.
      trivial.
    Qed.

    Lemma forallb_ordpairs_app_cons {A} f (l:list A) x :
      forallb_ordpairs f l = true ->
      forallb (fun y => f y x) l = true ->
      forallb_ordpairs f (l ++ x::nil) = true.
    Proof.
      induction l; simpl; trivial.
      repeat rewrite andb_true_iff in * .
      repeat rewrite forallb_forall in * .
      simpl in * .
      intuition.
      rewrite in_app_iff in H0.
      simpl in H0.
      intuition.
      congruence.
    Qed.
    
    Lemma forallb_ordpairs_refl_app_cons {A} f (l:list A) x :
      forallb_ordpairs_refl f l = true ->
      f x x = true ->
      forallb (fun y => f y x) l = true ->
      forallb_ordpairs_refl f (l ++ x::nil) = true.
    Proof.
      repeat rewrite forallb_ordpairs_refl_conj.
      repeat rewrite andb_true_iff.
      intuition.
      - apply forallb_ordpairs_app_cons; trivial.
      - rewrite forallb_app; simpl; intuition.
    Qed.

  End Forallb_ordpairs.

  (** * Removal from a list *)
  
  Section Remove.
    Context {A:Type}.
    Context {eqdec:EqDec A eq}.
    
    Lemma remove_in_neq
          (l : list A) (x y : A) : x <> y ->
                                   (In x l <-> In x (remove eqdec y l)).
    Proof.
      intros neq. induction l; simpl; intuition; subst.
      - destruct (eqdec y x); subst; intuition.
      - destruct (eqdec y a); subst; intuition.
      - destruct (eqdec y a); subst; intuition.
        simpl in *; intuition.
    Qed.

    Lemma list_in_remove_impl_diff x y l:
      In x (remove eqdec y l) -> x <> y.
    Proof.
      case (equiv_dec x y); try congruence.
      intros Heq; rewrite Heq in *; clear Heq.
      intros H.
      apply remove_In in H.
      contradiction.
    Qed.
    
    Lemma list_remove_append_distrib:
      forall (v:A) (l1 l2:list A),
        remove eqdec v l1 ++ remove eqdec v l2 = remove eqdec v (l1 ++ l2).
    Proof.
      intros.
      induction l1; try reflexivity.
      simpl.
      destruct (eqdec v a).
      - assumption.
      - simpl; rewrite IHl1; reflexivity.
    Qed.

    Lemma list_remove_idempotent:
      forall v l,
        remove eqdec v (remove eqdec v l) = remove eqdec v l.
    Proof.
      intros.
      induction l; try reflexivity.
      simpl.
      destruct (eqdec v a).
      - assumption.
      - simpl.
        destruct (eqdec v a); congruence.
    Qed.

    Lemma list_remove_commute:
      forall v1 v2 l,
        remove eqdec v1 (remove eqdec v2 l) = remove eqdec v2 (remove eqdec v1 l).
    Proof.
      induction l; try reflexivity.
      simpl.
      destruct (eqdec v2 a); destruct (eqdec v1 a); simpl.
      - assumption.
      - rewrite e in *.
        destruct (eqdec a a); congruence.
      - rewrite e in *.
        destruct (eqdec a a); congruence.
      - destruct (eqdec v1 a); destruct (eqdec v2 a); simpl.
        + assumption.
        + congruence.
        + congruence.
        + rewrite IHl; reflexivity.
    Qed.

    Remark list_remove_in v1 v2 l1 l2:
      (In v1 l1 -> In v1 l2) ->
      In v1 (remove eqdec v2 l1) -> In v1 (remove eqdec v2 l2).
    Proof.
      intros Hl1l2 Hl1rm.
      case (eqdec v1 v2).
      - intros Heq; rewrite Heq in *; clear Heq.
        assert (~ In v2 (remove eqdec v2 l1)); try contradiction.
        apply remove_In.
      - intros Heq.
        apply remove_in_neq; try congruence.
        apply remove_in_neq in Hl1rm; try congruence.
        apply Hl1l2.
        assumption.
    Qed.

    Lemma remove_inv v n l:
      In v (remove eqdec n l) -> In v l /\ v <> n.
    Proof.
      induction l; intros; simpl in *.
      - contradiction.
      - destruct (eqdec n a).
        elim (IHl H); intros; auto; simpl in *.
        elim H; clear H; intros; subst; auto.
        elim (IHl H); intros; auto.
    Qed.

    Lemma not_in_remove_impl_not_in:
      forall x v l,
        x <> v ->
        ~ In x (remove eqdec v l) ->
        ~ In x l.
    Proof.
      intros x v l.
      intros Hneq Hx.
      induction l.
      - simpl.
        trivial.
      - simpl.
        unfold not.
        intros H.
        destruct H.
        + rewrite H in *; clear H.
          simpl in Hx.
          case (eqdec v x) in Hx; try congruence.
          simpl in Hx.
          apply Decidable.not_or in Hx.
          destruct Hx.
          congruence.
        + simpl in Hx.
          case (eqdec v a) in Hx; try congruence.
          * simpl in Hx.
            apply IHl in Hx.
            contradiction.
          * simpl in Hx.
            apply Decidable.not_or in Hx.
            destruct Hx.
            apply IHl in H1.
            contradiction.
    Qed.

    Lemma remove_nin_inv {v1 v2 l} :
      ~ (In v1 (remove eqdec v2 l)) ->
      v1 = v2 \/ ~ In v1 l.
    Proof.
      destruct (v2 == v1); unfold equiv, complement in *; eauto 3.
      intros nin.
      apply not_in_remove_impl_not_in in nin; eauto.
    Qed.

    Lemma incl_remove x (l1 l2:list A) :
      incl (remove eqdec x l1) l2 <-> incl l1 (x::l2).
    Proof.
      unfold incl; simpl; intuition.
      - destruct (eqdec x a); subst; eauto 2.
        right; apply (H a).
        apply remove_in_neq; congruence.
      - apply remove_inv in H0.
        destruct H0 as [inn neq].
        destruct (H _ inn); congruence.
    Qed.

    Fixpoint remove_all (x : A) (l : list A) : list A :=
      match l with
      | nil => nil
      | y::tl => if (x == y) then (remove_all x tl) else y::(remove_all x tl)
      end.

    Global Instance remove_all_proper : Proper (eq ==> ldeqA ==> ldeqA) remove_all.
    Proof.
      unfold Proper, respectful.
      intros; rewrite H.
      elim H0; intros; simpl.
      - reflexivity.
      - destruct (equiv_dec y x1); rewrite H2; reflexivity.
      - destruct (equiv_dec y x1); destruct (equiv_dec y y1); try reflexivity.
        apply perm_swap.
      - rewrite H2; rewrite H4; reflexivity.
    Qed.

    Lemma remove_all_filter x l:
      remove_all x l = filter (nequiv_decb x) l.
    Proof.
      induction l; simpl; trivial.
      unfold nequiv_decb, negb, equiv_decb. rewrite IHl.
      match_destr.
    Qed.
    
    Lemma remove_all_app (v:A) l1 l2
      : remove_all v (l1 ++ l2) = remove_all v l1 ++ remove_all v l2.
    Proof.
      repeat rewrite remove_all_filter.
      rewrite filter_app.
      trivial.
    Qed.

    Lemma fold_left_remove_all_In {l init a} :
      In a (fold_left (fun (a : list A) (b : A) =>
                         filter (nequiv_decb b) a) l init)
      -> In a init /\ ~ In a l.
    Proof.
      revert init a.
      induction l; simpl.
      - intuition.
      - intros.
        destruct (IHl _ _ H).
        apply filter_In in H0.
        unfold nequiv_decb, equiv_decb, negb in H0.
        intuition; subst.
        destruct (equiv_dec a0 a0); intuition.
    Qed.

    Lemma nin_remove dec (l:list A) a :
      ~ In a l -> remove dec a l = l.
    Proof.
      induction l; simpl; trivial.
      match_destr; intuition; congruence.
    Qed.

  End Remove.

  (** * Replace in a list *)
  
  Section Replace.
    Context {A:Type}.
    Context `{eqdec:EqDec A eq}.

    Definition replace_all l v n
      := map (fun x => if eqdec x v then n else x) l.
    
    Lemma replace_all_nin l v n :
      ~ In v l -> 
      map (fun x => if eqdec x v then n else x) l = l.
    Proof.
      induction l; simpl; intuition.
      destruct (eqdec a v); congruence.
    Qed.

    Lemma in_replace_all {v v':A} {l} {x} : 
      In x (replace_all l v v') ->
      x = v' \/ (x <> v /\ In x l).
    Proof.
      unfold replace_all; intros.
      apply in_map_iff in H.
      destruct H as [? [eqq inn]].
      match_destr_in eqq; unfold equiv, complement in *; subst; eauto.
    Qed.
    
    Lemma replace_all_remove_neq l v0 v n:
      v <> v0 -> n <> v0 ->
      remove eqdec v0 
             (map (fun x  => if eqdec x v then n else x) 
                  l) =
      (map (fun x => if eqdec x v then n else x) 
           (remove eqdec v0 l)).
    Proof.
      induction l; simpl; intuition.
      rewrite H2.
      destruct (eqdec a v); subst; simpl.
      - destruct (eqdec v0 n); subst; simpl; intuition.
        destruct (eqdec v0 a); subst; simpl; [congruence|].
        rewrite e in *; clear e.
        destruct (eqdec v v); intuition.
      - destruct (eqdec v0 a); trivial; simpl.
        destruct (eqdec a v); subst; intuition.
    Qed.

    Lemma remove_replace_all_nin l v v' :
      ~ In v' l ->
      remove eqdec v' (replace_all l v v') =
      remove eqdec v l.
    Proof.
      induction l; simpl; intuition.
      rewrite H. destruct (eqdec a v); simpl; try (rewrite e in *; clear e).
      - destruct (eqdec v v); intuition; 
          destruct (eqdec v' v'); intuition.
      - destruct (eqdec v a); intuition;
          destruct (eqdec v' a); intuition.
    Qed.

    Lemma replace_all_app (l1 l2:list A) v v' :
      replace_all (l1 ++ l2) v v' = replace_all l1 v v' ++ replace_all l2 v v'.
    Proof.
      apply map_app.
    Qed.

    Lemma replace_all_nin_eq (l:list A) v v' :
      ~ In v l -> replace_all l v v' = l.
    Proof.
      induction l; simpl; trivial.
      match_destr; intuition; congruence.
    Qed.

    Lemma replace_all_remove_eq (l:list A) v v' :
      replace_all (remove equiv_dec v l) v v' = remove equiv_dec v l.
    Proof.
      apply replace_all_nin_eq.
      apply remove_In.
    Qed.

    Lemma remove_replace_all_comm (l:list A) v0 v v'  :
      v0 <> v ->
      v0 <> v' ->
      remove equiv_dec v0 (replace_all l v v') =
      replace_all (remove equiv_dec v0 l) v v'.
    Proof.
      intros.
      induction l; simpl; trivial.
      destruct (equiv_dec a v).
      - rewrite e in *; clear e a.
        destruct (eqdec v v); try congruence.
        repeat (match_destr; [congruence | ]).
        simpl; match_destr; congruence.
      - destruct (eqdec a v); try congruence.
        match_destr.
        simpl; match_destr; try congruence.
    Qed.
    
    Definition flat_replace_all l (v:A) n
      := flat_map (fun x => if eqdec x v then n else (x::nil)) l.

    Lemma flat_replace_all_nil l (v:A) :
      flat_replace_all l v nil = @remove_all A eqdec v l.
    Proof.
      induction l; simpl; trivial.
      match_destr; match_destr; simpl; try congruence.
    Qed.

    Lemma flat_replace_all_app l1 l2 (v:A) n
      : flat_replace_all (l1 ++ l2) v n
        = flat_replace_all l1 v n ++ flat_replace_all l2 v n.
    Proof.
      unfold flat_replace_all.
      apply flat_map_app.
    Qed.

    Lemma fold_left_remove_all_nil_in_inv {B} {x ps l}:
      In x (fold_left
              (fun (h : list nat) (xy : nat * B) =>
                 remove_all (fst xy) h)
              ps l) ->
      In x l.
    Proof.
      revert l.
      induction ps using rev_ind; simpl; intuition; subst.
      apply IHps.
      rewrite fold_left_app in H.
      simpl in H.
      rewrite remove_all_filter in H.
      apply filter_In in H. intuition.
    Qed.

    Lemma fold_left_remove_all_nil_in_inv' {x ps l}:
      In x (fold_left
              (fun (h : list nat) (xy : nat) =>
                 remove_all xy h)
              ps l) ->
      In x l.
    Proof.
      revert l.
      induction ps using rev_ind; simpl; intuition; subst.
      apply IHps.
      rewrite fold_left_app in H.
      simpl in H.
      rewrite remove_all_filter in H.
      apply filter_In in H. intuition.
    Qed.

    Lemma fold_left_remove_all_nil_in_not_inv'  {x ps l}:
      In x (fold_left
              (fun (h : list nat) (xy : nat ) =>
                 remove_all xy h)
              ps l) ->
      ~ In x ps.
    Proof.
      revert l.
      induction ps; simpl; intuition; subst.
      - simpl in *.
        apply fold_left_remove_all_nil_in_inv' in H.
        rewrite remove_all_filter in H.
        apply filter_In in H. unfold nequiv_decb, equiv_decb in *.
        intuition. match_destr_in H1.
        congruence.
      - eauto.
    Qed.
    
    Lemma replace_all_remove_eq' (l : list A) (v n : A) :
      map (fun x : A => if eqdec x v then n else x) (remove eqdec v l) = (remove eqdec v l).
    Proof.
      apply replace_all_nin.
      apply remove_In.
    Qed.

  End Replace.

  (** * List inclusion *)

  Section Inclusion.

    Definition cut_down_to {A B} {dec:EqDec A eq} (l:list (A*B)) (l2:list A) :=
      filter (fun a => existsb (fun z => (fst a) ==b z) l2) l.

    Lemma cut_down_to_in
          {A B} {dec:EqDec A eq}
          (l:list (A*B)) l2 a :
      In a (cut_down_to l l2) <-> In a l /\ In (fst a) l2 .
    Proof.
      unfold cut_down_to.
      red; intros.
      rewrite filter_In.
      rewrite existsb_exists.
      firstorder.
      - unfold equiv_decb in *; match_destr_in H1.
        congruence.
      - exists (fst a); split; trivial.
        unfold equiv_decb; match_destr.
        congruence.
    Qed.

    Lemma cut_down_to_app  {A B} {dec:EqDec A eq}
          (l l':list (A*B)) l2 :
      cut_down_to (l++l') l2 = cut_down_to l l2 ++ cut_down_to l' l2.
    Proof.
      unfold cut_down_to.
      apply filter_app.
    Qed.
    
    Lemma incl_dec {A} {dec:EqDec A eq} (l1 l2:list A) :
      {incl l1 l2} + {~ incl l1 l2}.
    Proof.
      unfold incl.
      induction l1.
      - left; inversion 1.
      - destruct IHl1.
        + destruct (in_dec dec a l2).
          * left; simpl; intros; intuition; congruence.
          * right; simpl;  intros inn; apply n; intuition.
        + right; simpl; intros inn; apply n; intuition.
    Defined.

    Global Instance incl_pre A : PreOrder (@incl A).
    Proof.
      unfold incl.
      constructor; red; intuition.
    Qed.

    Lemma incl_cons_iff {A : Type} (a : A) (l m : list A) :
      incl (a :: l) m <-> In a m /\ incl l m.
    Proof.
      unfold incl; simpl; intuition; subst; tauto.
    Qed.
    
    Lemma incl_app_iff {A:Type} (l m n : list A) :
      incl l n /\ incl m n <-> incl (l ++ m) n.
    Proof.
      unfold incl; intuition.
      rewrite in_app_iff in H.
      intuition.
    Qed.

    Lemma set_inter_contained {A} dec (l l':list A):
      (forall a, In a l -> In a l') ->
      set_inter dec l l' = l.
    Proof.
      induction l; simpl; intuition.
      case_eq (set_mem dec a l'); trivial.
      - rewrite IHl; auto.
      - intros ninn. apply set_mem_complete1 in ninn.
        elim ninn. apply H; intuition.
    Qed.

    Lemma set_inter_idempotent {A} dec (l:list A):
      set_inter dec l l = l.
    Proof.
      apply set_inter_contained; trivial.
    Qed.

    Lemma set_inter_comm_in {A} dec a b :
      (forall x, In x (@set_inter A dec a b)  -> In x (set_inter dec b a)) .
    Proof.
      intros ? inn.
      apply set_inter_elim in inn.
      apply set_inter_intro; intuition.
    Qed.
    
    Lemma nincl_exists {A} {dec:EqDec A eq} (l1 l2:list A) :
      ~ incl l1 l2 -> {x | In x l1 /\ ~ In x l2}.
    Proof.
      unfold incl.
      induction l1; simpl.
      - intuition.
      - intros.
        destruct (in_dec dec a l2).
        + destruct IHl1.
          * intros inn.
            apply H. intuition; subst; trivial.
          * exists x; intuition.
        + exists a; intuition.
    Qed.

  End Inclusion.

  (** * List equivalence *)
  
  Section Equivalence.
    Context {A:Type}.

    Definition equivlist (l l':list A) 
      := forall x, In x l <-> In x l'.

    Global Instance equivlist_equiv : Equivalence equivlist.
    Proof.
      constructor; red; unfold equivlist; firstorder.
    Qed.

    Global Instance Permutation_equivlist :
      subrelation (@Permutation A) equivlist.
    Proof.
      split; intros.
      - eapply Permutation_in; eauto.
      - eapply Permutation_in. symmetry; eauto. eauto.
    Qed.

    Lemma equivlist_in {l1 l2} : equivlist l1 l2 -> (forall x:A, In x l1 -> In x l2).
    Proof.
      intros e x inn. specialize (e x); intuition.
    Qed.
    
    Lemma equivlist_incls (l1 l2:list A) :
      equivlist l1 l2 <-> (incl l1 l2 /\ incl l2 l1).
    Proof.
      unfold equivlist, incl.
      firstorder.
    Qed.

    Global Instance equivlist_In_proper : Proper (eq ==> equivlist ==> iff) (@In A).
    Proof.
      unfold Proper, respectful, equivlist; intros; subst; firstorder.
    Qed.

    Global Instance equivlist_cons_proper :
      Proper (eq ==> equivlist ==> equivlist) (@cons A).
    Proof.
      unfold Proper, respectful, equivlist; simpl; intros ? a ? l1 l2 eqq x; subst.
      split; intros [?|inn]; subst; eauto 2
      ; right; apply eqq; trivial.
    Qed.
    
    Global Instance incl_cons_proper :
      Proper (eq ==> (@incl A) ==> (@incl A)) (@cons A).
    Proof.
      unfold Proper, respectful, incl; simpl; intros ? a ? l1 l2 eqq x; subst.
      intros [?|inn]; subst; eauto 2
      ; right; apply eqq; trivial.
    Qed.
    
    Lemma equivlist_dec {dec:EqDec A eq} (l1 l2:list A) :
      {equivlist l1 l2} + {~ equivlist l1 l2}.
    Proof.
      destruct (incl_dec l1 l2).
      - destruct (incl_dec l2 l1).
        + left; rewrite equivlist_incls; intuition.
        + right; rewrite equivlist_incls; intuition.
      - right; rewrite equivlist_incls; intuition.
    Defined.
    
    Lemma equivlist_nil {l:list A} : equivlist l nil -> l = nil.
    Proof.
      destruct l; trivial.
      intros inn.
      destruct (inn a); simpl in *.
      intuition.
    Qed.

    Lemma app_idempotent_equivlist (l:list A) :
      equivlist (l++l) l.
    Proof.
      apply equivlist_incls; split;
        intros ? ?; rewrite in_app_iff in *; intuition.
    Qed.
    
    Lemma app_commutative_equivlist (l1 l2:list A) :
      equivlist (l1++l2) (l2++l1).
    Proof.
      apply equivlist_incls; split;
        intros ? ?; rewrite in_app_iff in *; intuition.
    Qed.
    
    Lemma app_contained_equivlist  (a b:list A) :
      incl b a ->
      equivlist (a ++ b) a.
    Proof.
      intros.
      apply equivlist_incls; split; intros x xin.
      - rewrite in_app_iff in xin. destruct xin; eauto.
      - rewrite in_app_iff. eauto.
    Qed.

    Lemma set_inter_equivlist dec a b :
      equivlist (@set_inter A dec a b) (set_inter dec b a) .
    Proof.
      split; intros; apply set_inter_comm_in; trivial.
    Qed.

    Global Instance set_inter_equivlist_proper dec : Proper (equivlist ==> equivlist ==> equivlist) (@set_inter A dec).
    Proof.
      cut (Proper (equivlist ==> equivlist ==> (@incl A)) (@set_inter A dec)); unfold Proper, respectful; intros.
      { apply equivlist_incls; intuition. }
      intros z zin.
      apply set_inter_elim in zin.
      rewrite H,H0 in zin.
      apply set_inter_intro; intuition.
    Qed.

    Lemma set_inter_assoc dec a b c:
      @set_inter A dec (set_inter dec a b) c
      = set_inter dec a (set_inter dec b c).
    Proof.
      revert b c.
      induction a; simpl; trivial; intros.
      case_eq (set_mem dec a b); intros.
      - simpl.
        apply set_mem_correct1 in H.
        case_eq (set_mem dec a c); simpl; intros.
        + apply set_mem_correct1 in H0.
          rewrite IHa.
          case_eq (set_mem dec a (set_inter dec b c));
            simpl; intros; trivial.
          apply set_mem_complete1 in H1.
          elim H1. apply set_inter_intro; trivial.
        + case_eq (set_mem dec a (set_inter dec b c));
            simpl; intros; trivial.
          apply set_mem_complete1 in H0.
          apply set_mem_correct1 in H1.
          apply set_inter_elim in H1.
          intuition.
      -  apply set_mem_complete1 in H.
         case_eq (set_mem dec a (set_inter dec b c));
           simpl; intros; trivial.
         apply set_mem_correct1 in H0.
         apply set_inter_elim in H0.
         intuition.
    Qed.
    
    Lemma equivlist_cons l1 l2 (s:A) :
      equivlist l1 l2 ->
      equivlist (s::l1) (s::l2).
    Proof.
      unfold equivlist.
      firstorder.
    Qed.

    Global Instance equivlist_filter :
      Proper (eq ==> equivlist ==> equivlist) (@filter A).
    Proof.
      red; unfold equivlist; intros ? ? ? ? ? ? ?; subst.
      repeat rewrite filter_In.
      firstorder.
    Qed.
    
    Global Instance equivlist_remove_all {dec:EqDec A eq} :
      Proper (eq ==> equivlist ==> equivlist) (@remove_all A dec).
    Proof.
      red; intros ? ? ? ? ? ?; subst.
      repeat rewrite remove_all_filter.
      apply equivlist_filter; trivial.
    Qed.

    Lemma incl_list_dec (dec:forall x y:A, {x = y} + {x <> y}) (l1 l2:list A) : {(forall x, In x l1 -> In x l2)} + {~(forall x, In x l1 -> In x l2)}.
    Proof.
      case_eq (forallb (fun x => if in_dec dec x l2 then true else false) (l1)); intros fb.
      - left.
        rewrite forallb_forall in fb.
        intros a inna. specialize (fb _ inna).
        match_destr_in fb.
      - right. rewrite forallb_not_existb in fb. rewrite negb_false_iff in fb.
        rewrite existsb_exists in fb. destruct fb as [? [inn ne]].
        intro im. specialize (im _ inn).
        match_destr_in ne. congruence.
    Defined.

    Global Instance Forall_equiv_proper {P} : Proper (equivlist ==> iff) (@Forall A P).
    Proof.
      intros ? ? eqs.
      repeat rewrite Forall_forall.
      firstorder.
    Qed.
    
  End Equivalence.

  Global Instance map_equivlist {A B} : Proper (eq ==> equivlist ==> equivlist) (@map A B).
  Proof.
    repeat red; intros; subst.
    repeat rewrite in_map_iff.
    split; intros [? [??]]; subst.
    - rewrite H0 in H1; eauto.
    - rewrite <- H0 in H1; eauto.
  Qed.

  (** * Assymetric relations on a list *)
  
  Section Assym_over.
    
    Definition asymmetric_over {A} R (l:list A) :=
      forall x y, In x l-> In y l -> ~R x y -> ~R y x -> x = y.
    
    Lemma asymmetric_asymmetric_over {A} {R} :
      (forall x y:A, ~R x y -> ~R y x -> x = y) ->
      forall l, asymmetric_over R l .
    Proof.
      red; intuition.
    Qed.

    Lemma asymmetric_over_incl {A} {R} {l2:list A}
      : asymmetric_over R l2 ->
        forall l1,
          (forall x, In x l1 -> In x l2) ->
          asymmetric_over R l1.
    Proof.
      unfold asymmetric_over; intuition.
    Qed.

    Lemma asymmetric_over_equivlist {A} {R} {l1 l2:list A} :
      equivlist l1 l2 ->
      (asymmetric_over R l1 <->
       asymmetric_over R l2).
    Proof.
      intros; split; intros aH; eapply asymmetric_over_incl; try eapply aH;
        apply equivlist_in; trivial.
      symmetry; trivial.
    Qed.
    
    Lemma asymmetric_over_cons_inv {A} {R} {a:A} {l1} :
      asymmetric_over R (a::l1) ->
      asymmetric_over R l1.
    Proof.
      unfold asymmetric_over; simpl; intuition.
    Qed.

    Hint Resolve asymmetric_over_cons_inv : list.

    Lemma asymmetric_over_swap {A} R {a b:A} {l1} :
      asymmetric_over R (a::b::l1) ->
      asymmetric_over R (b::a::l1).
    Proof.
      unfold asymmetric_over; simpl; intuition.
    Qed.

  End Assym_over.

  (** * Lists without duplicates *)

  Section NoDup.
    
    Global Instance perm_in {A} : Proper (eq ==> (@Permutation A) ==> iff) (@In A).
    Proof.
      Hint Resolve Permutation_in Permutation_sym : list.
      unfold Proper, respectful; intros; subst; intuition; eauto with list.
    Qed.
    
    Lemma NoDup_perm' {A:Type} {a b:list A} : NoDup a -> Permutation a b -> NoDup b.
    Proof.
      intros nd p.
      revert nd.
      revert a b p.
      apply (Permutation_ind_bis (fun l l' => NoDup l -> NoDup l')); intuition.
      - inversion H1; subst. constructor; eauto with list.
      - inversion H1; subst. inversion H5; subst.
        rewrite H in H4,H6.
        constructor; [|constructor]; simpl in *; intuition; subst; eauto.
    Qed.
    
    Global Instance NoDup_perm {A:Type} :
      Proper (@Permutation A ==> iff) (@NoDup A).
    Proof.
      Hint Resolve NoDup_perm' Permutation_sym : list.
      unfold Proper, respectful; intros; subst; intuition; eauto with list.
    Qed.

    Lemma NoDup_Permutation' {A : Type} (l l' : list A) :
      NoDup l ->
      NoDup l' -> equivlist l l' -> Permutation l l'.
    Proof.
      intros.
      apply NoDup_Permutation; intuition.
    Qed.

    Lemma NoDup_rev {A:Type} (l:list A) : NoDup (rev l) <-> NoDup l.
    Proof.
      rewrite <- Permutation_rev.
      intuition.
    Qed.

    Lemma NoDup_app_inv {A:Type} {a b:list A} : NoDup (a++b) -> NoDup a.
    Proof.
      induction b; intuition.
      - rewrite app_nil_r in H; trivial.
      - rewrite <- Permutation_middle in H.
        inversion H; subst; auto.
    Qed.
    
    Hint Resolve NoDup_app_inv : list.

    Lemma NoDup_app_inv2 {A:Type} {a b:list A} : NoDup (a++b) -> NoDup b.
    Proof.
      rewrite Permutation_app_comm.
      eauto with list.
    Qed.

    Lemma NoDup_dec {A:Type} {dec:EqDec A eq} (l:list A): {NoDup l} + {~NoDup l}.
    Proof.
      induction l.
      - left; constructor.
      - destruct (in_dec equiv_dec a l).
        + right; inversion 1; congruence.
        + destruct IHl.
          * left; constructor; auto.
          * right; inversion 1; congruence.
    Defined.

    Lemma unmap_NoDup {A B} (f:A->B) l :
      NoDup (map f l) -> NoDup l.
    Proof.
      induction l; simpl.
      - constructor.
      - inversion 1; subst.
        econstructor; eauto.
        intros inn; apply H2.
        apply in_map_iff.
        eauto.
    Qed.
    
    Lemma map_inj_NoDup {A B} (f:A->B) 
          (inj:forall x y, f x = f y -> x = y) (l:list A) :
      NoDup l ->
      NoDup (map f l).
    Proof.
      induction l; simpl.
      - constructor.
      - inversion 1; subst.
        econstructor; eauto.
        intros inn; apply H2.
        apply in_map_iff in inn.
        destruct inn as [x [xeq xin]].
        rewrite <- (inj _ _ xeq).
        trivial.
    Qed.

    Lemma filter_NoDup {A} (f:A->bool) l :
      NoDup l -> NoDup (filter f l).
    Proof.
      induction l; simpl; trivial.
      match_destr; intros.
      - inversion H; constructor; subst; trivial.
        + rewrite filter_In.
          intuition.
        + auto.
      - inversion H; subst; auto.
    Qed.

  End NoDup.

  
  Section find.
    Context {A:Type}.
    
    Lemma find_ext f g (l:list A):
      (forall x, f x = g x) ->
      find f l = find g l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite H, IHl; trivial.
    Qed.

    Lemma find_app f (l1 l2:list A) :
      find f (l1 ++ l2) = match find f l1 with
                          | Some x => Some x
                          | None => find f l2
                          end.
    Proof.
      revert l2.
      induction l1; simpl; trivial; intros.
      destruct (f a); trivial.
    Qed.

    Lemma find_over_map {B} f (g:A->B) (l:list A) :
      find f (map g l) = lift g (find (fun x => f (g x)) l).
    Proof.
      induction l; simpl; trivial.
      match_destr.
    Qed.
    
  End find.
  (** * Disjoint lists *)
  
  Section Disjoint.
    Definition disjoint {A:Type} (l1 l2:list A)
      := forall x, In x l1 -> In x l2 -> False.

    Lemma NoDup_app_dis {A:Type} (a b:list A) :
      NoDup (a++b) -> disjoint a b.
    Proof.
      red; intros.
      destruct (in_split _ _ H0) as [a1[a2 aeq]].
      subst.
      rewrite <- app_assoc in H.
      apply NoDup_app_inv2 in H.
      simpl in H.
      inversion H; subst.
      simpl in *; intuition.
    Qed.

    Lemma disjoint_cons_inv1 {A:Type} {a:A} {l1 l2} : 
      disjoint (a :: l1) l2 -> disjoint l1 l2 /\ ~ In a l2.
    Proof.
      unfold disjoint; simpl; intuition.
      apply (H x); intuition.
      specialize (H a); intuition.
    Qed.

    Lemma disjoint_app_l {A} (l1 l2 l3:list A) :
      disjoint (l1 ++ l2) l3 <-> (disjoint l1 l3 /\ disjoint l2 l3).
    Proof.
      unfold disjoint; intuition.
      eapply H; try rewrite in_app_iff; eauto.
      eapply H; try rewrite in_app_iff; eauto.
      rewrite in_app_iff in H.
      intuition; eauto.
    Qed.

    Lemma disjoint_app_r {A} (l1 l2 l3:list A) :
      disjoint l1 (l2 ++ l3) <-> (disjoint l1 l2 /\ disjoint l1 l3).
    Proof.
      unfold disjoint; intuition.
      eapply H; try rewrite in_app_iff; eauto.
      eapply H; try rewrite in_app_iff; eauto.
      rewrite in_app_iff in H2.
      intuition; eauto.
    Qed.

    Lemma NoDup_app {A:Type} {a b:list A} :
      disjoint a b -> NoDup a -> NoDup b -> NoDup (a++b).
    Proof.
      revert b;
        induction a; intuition.
      simpl; inversion H0; subst.
      apply disjoint_cons_inv1 in H.
      constructor; intuition.
      apply in_app_or in H2. intuition.
    Qed.

    Global Instance disjoint_sym {A:Type} : Symmetric (@disjoint A).
    Proof.
      red; unfold disjoint; firstorder.
    Qed.

    Lemma disjoint_nil_l {A:Type} (l:list A) : disjoint nil l.
    Proof.
      red; inversion 1.
    Qed.

    Lemma disjoint_nil_r {A:Type} (l:list A) : disjoint l nil.
    Proof.
      red; inversion 2.
    Qed.

    Hint Immediate disjoint_nil_l disjoint_nil_r : list.

    Lemma disjoint_incl {A:Type} (l1 l2 l3:list A) :
      incl l3 l2 ->
      disjoint l1 l2 ->
      disjoint l1 l3.
    Proof.
      unfold disjoint, incl; eauto.
    Qed.

    Lemma disjoint_cons1 {A : Type} (a : A) (l1 l2 : list A) :
      disjoint l1 l2 -> ~ In a l2 ->
      disjoint (a :: l1) l2.
    Proof.
      unfold disjoint; simpl; intuition; subst; eauto.
    Qed.

    Lemma disjoint_cons2 {A : Type} (a : A) (l1 l2 : list A) :
      disjoint l1 l2 -> ~ In a l1 ->
      disjoint l1 (a::l2).
    Proof.
      intros.
      unfold disjoint; simpl; intuition; subst; eauto.
    Qed.

    Lemma disjoint_cons_inv2 {A : Type} (a : A) (l1 l2 : list A) :
      disjoint l1 (a::l2) -> (disjoint l1 l2 /\ ~ In a l1).
    Proof.
      unfold disjoint; simpl; intuition; subst; eauto.
    Qed.

    Lemma disjoint_with_exclusion {A:Type} (l l1 l2:list A) :
      disjoint l1 l2 ->
      (forall x,
          In x l -> In x (l1 ++ l2) -> In x l1) ->
      disjoint l l2.
    Proof.
      unfold disjoint; intros disj excl x inn1 inn2.
      specialize (excl x inn1).
      rewrite in_app_iff in excl.
      intuition; eauto.
    Qed.
    
    Lemma disjoint_rev_r {A} (l1 l2: list A) :
      disjoint l1 (rev l2) <-> disjoint l1 l2.
    Proof.
      intros.
      assert (eqq:equivlist (rev l2) l2).
      { rewrite <- Permutation_rev; reflexivity. }
      apply equivlist_incls in eqq.
      split; intros disj.
      - eapply disjoint_incl in disj; eauto; tauto.
      - eapply disjoint_incl; eauto; tauto.
    Qed.

    Lemma disjoint_rev_l {A} (l1 l2: list A) :
      disjoint (rev l1) l2 <-> disjoint l1 l2.
    Proof.
      split; intros disj; symmetry; symmetry in disj.
      - apply disjoint_rev_r; auto.
      - apply disjoint_rev_r in disj; auto.
    Qed.

    Lemma  disjoint_remove_swap {A} dec (v:A) l1 l2 :
      disjoint (remove dec v l1) l2 <-> disjoint l1 (remove dec v l2).
    Proof.
      unfold disjoint; split; intros H x inn1 inn2.
      - apply remove_inv in inn2.
        apply (H x); try tauto.
        apply remove_in_neq; tauto.
      - apply remove_inv in inn1.
        apply (H x); try tauto.
        apply remove_in_neq; tauto.
    Qed.

    Global Instance disjoint_equivs {A} : Proper (equivlist ==> equivlist ==> iff) (@disjoint A).
    Proof.
      cut (Proper (equivlist ==> equivlist==> Basics.impl) (@disjoint A)).
      {
        unfold Proper, respectful, equivlist; unfold Basics.impl; split; [eauto | ].
        symmetry in H0, H1; eauto.
      }
      unfold Proper, respectful, Basics.impl; intros l1 l1' eqq1 l2 l2' eqq2.
      unfold equivlist, disjoint in *.
      intros disj x inn1 inn2.
      rewrite <- eqq1 in inn1.
      rewrite <- eqq2 in inn2.
      eauto.
    Qed.

    Global Instance disjoint_incl_proper {A} : Proper ((@incl A) --> (@incl A) --> Basics.impl) (@disjoint A).
    Proof.
      unfold Proper, respectful, Basics.impl, Basics.flip; intros l1 l1' eqq1 l2 l2' eqq2.
      unfold incl, disjoint in *.
      intros disj x inn1 inn2.
      eauto.
    Qed.

    Lemma disjoint_replace_all {A:Type} {dec:EqDec A eq} (v v':A) l l' : 
      disjoint l l' ->
      ~ In v' l ->
      disjoint l (replace_all l' v v').
    Proof.
      unfold disjoint, replace_all; intros.
      apply in_map_iff in H2.
      destruct H2 as [? [eqq inn]].
      match_destr_in eqq; unfold equiv, complement in *; subst; eauto.
    Qed.

    Lemma disjoint_dec {A} (dec:forall x y:A, {x=y} + {x<>y}) (l₁ l₂:list A) :
      {disjoint l₁ l₂} + {~ disjoint l₁ l₂}.
    Proof.
      unfold disjoint.
      assert (F:{Forall (fun x => ~ In x l₁) l₂} + {~ Forall (fun x => ~ In x l₁) l₂}).
      {
        apply Forall_dec_defined.
        intros.
        destruct (in_dec dec x l₁); [right | left]; eauto.
      }
      destruct F.
      - left; rewrite Forall_forall in *.
        intros; eapply f; eauto.
      - right; rewrite Forall_forall in *.
        intros f; eapply n; eauto.
    Defined.

    Lemma disjoint_eqdec {A} `{dec:EqDec A eq} (l₁ l₂:list A) :
      {disjoint l₁ l₂} + {~ disjoint l₁ l₂}.
    Proof.
      apply disjoint_dec; trivial.
    Defined.

    
  End Disjoint.

  (** * Zip of two lists *)

  Section Zip.
    
    Fixpoint zip {A B} (l1:list A) (l2: list B) : option (list (A * B)) :=
      match l1 with
      | nil =>
        match l2 with
        | nil => Some nil
        | _ => None
        end
      | x1 :: l1' =>
        match l2 with
        | nil => None
        | x2 :: l2' =>
          match zip l1' l2' with
          | None => None
          | Some l3 =>
            Some ((x1, x2) :: l3)
          end
        end
      end.
  End Zip.

  Section Seq.
    Lemma seq_ge init bound :
      forall x, In x (seq init bound) -> x >= init.
    Proof.
      revert init.
      induction bound; simpl; intuition.
      specialize (IHbound (S init) x H0).
      omega.
    Qed.
    
    Lemma seq_NoDup init bound :
      NoDup (seq init bound).
    Proof.
      revert init.
      induction bound; simpl; intros.
      - constructor.
      - econstructor; eauto.
        intro inn.
        apply seq_ge in inn.
        omega.
    Qed.

    Lemma seq_plus a b c : seq a (b+c) = seq a b ++ seq (a+b) c.
    Proof.
      revert a c.
      induction b; simpl; intros.
      - auto.
      - rewrite IHb.
        rewrite plus_Sn_m, plus_n_Sm.
        trivial.
    Qed.

    Lemma find_seq_same_aux b a n1 n2 x y :
      n1 < n2 ->
      find b (seq a n1) = Some x ->
      find b (seq a n2) = Some y ->
      x = y.
    Proof.
      intros nlt eq1 eq2.
      assert (n2eq:n2 = n1 + (n2 - n1))
        by (rewrite le_plus_minus_r; auto with arith).
      rewrite n2eq in eq2.
      rewrite seq_plus, find_app, eq1 in eq2.
      congruence.
    Qed.

    Lemma find_seq_same b a n1 n2 x y : find b (seq a n1) = Some x ->
                                        find b (seq a n2) = Some y ->
                                        x = y.
    Proof.
      destruct (lt_eq_lt_dec n1 n2) as [[?|?]|?].
      - apply find_seq_same_aux; auto.
      - congruence.
      - intros; symmetry.
        eapply find_seq_same_aux; eauto.
    Qed.
    

  End Seq.

  Definition not_nil {A:Type} (l:list A)
    := match l with
       | nil => false
       | _ => true
       end.
  
  Definition filter_nil {A:Type} := filter (@not_nil A).
  
  Section concat.

    Global Instance Permutation_concat {A} :
      Proper ((@Permutation (list A)) ==> (@Permutation A)) (@concat A).
    Proof.
      repeat red.
      apply Permutation_ind_bis; simpl; intros.
      - trivial.
      - apply Permutation_app; trivial.
      - repeat rewrite <- app_ass.
        apply Permutation_app; trivial.
        apply Permutation_app_swap.
      - etransitivity; eauto.
    Qed.

    Lemma concat_filter {A : Type} (f : A -> bool) (l : list (list A)) :
      filter f (concat l) = concat (map (filter f) l).
    Proof.
      induction l; simpl; trivial.
      rewrite filter_app, IHl; trivial.
    Qed.

    Lemma concat_filter_nil {A:Type} (ls:list (list A)) :
      concat (filter_nil ls) = concat ls.
    Proof.
      induction ls; simpl; trivial.
      destruct a; simpl; trivial.
      rewrite IHls; trivial.
    Qed.

    Lemma concat_nil_r {A:Type} (ls:list (list A)) :
      concat ls = nil <-> Forall (eq nil) ls.
    Proof.
      split; intros eqq.
      - induction ls; simpl.
        + constructor.
        +  destruct a; try discriminate.
           intuition.
      - induction ls; simpl; trivial.
        invcs eqq; simpl.
        auto.
    Qed.

  End concat.

  Section alldisjoint.

    Definition all_disjoint {A} := ForallOrdPairs (@disjoint A).

    Lemma all_disjoint2_facts {A} (x y:list A) (l:list (list A)) :
      all_disjoint (x::y::l) ->
      disjoint x y.
    Proof.
      intros ad; red in ad.
      repeat match goal with
             | [ H : Forall _ (_::_) |- _ ] => invcs H
             | [ H : ForallOrdPairs _ (_::_) |- _ ] => invcs H
             end; tauto.
    Qed.      

    Lemma all_disjoint3_facts {A} (x y z:list A) (l:list (list A)) :
      all_disjoint (x::y::z::l) ->
      disjoint x y
      /\ disjoint x z
      /\ disjoint y z.
    Proof.
      intros ad; red in ad.
      repeat match goal with
             | [ H : Forall _ (_::_) |- _ ] => invcs H
             | [ H : ForallOrdPairs _ (_::_) |- _ ] => invcs H
             end; tauto.
    Qed.

    Lemma all_disjoint3_iff {A} (x y z:list A) :
      all_disjoint (x::y::z::nil) <->
      disjoint x y
      /\ disjoint x z
      /\ disjoint y z.
    Proof.
      split; unfold all_disjoint; intros ad.
      - repeat match goal with
               | [ H : Forall _ (_::_) |- _ ] => invcs H
               | [ H : ForallOrdPairs _ (_::_) |- _ ] => invcs H
               end; tauto.
      - repeat constructor; try tauto.
    Qed.

    Lemma all_disjoint_has_same_eq {A} {ls:list (list A)} :
      all_disjoint ls ->
      forall l1 l2,
        In l1 ls ->
        In l2 ls ->
        forall x,
          In x l1 -> In x l2 -> l1 = l2.
    Proof.
      induction ls; simpl; try contradiction.
      intros ad l1 l2 inn1 inn2 x innx1 innx2.
      invcs ad.
      specialize (IHls H2).
      rewrite Forall_forall in H1.
      destruct inn1 as [? | inn1]; destruct inn2 as [? | inn2]; subst.
      - trivial.
      - elim (H1 _ inn2 _ innx1 innx2).
      - elim (H1 _ inn1 _ innx2 innx1).
      - eauto.
    Qed.

    
    Global Instance all_disjoint_perm_proper {A} : Proper ((@Permutation (list A)) ==> iff) all_disjoint.
    Proof.
      cut (Proper ((@Permutation (list A)) ==> impl) all_disjoint)
      ; unfold Proper, respectful, impl.
      { split; [eauto | ]; symmetry in H0; eauto. }
      change (forall x y : list (list A), Permutation x y -> (fun x y => all_disjoint x -> all_disjoint y) x y).
      apply Permutation_ind_bis; unfold all_disjoint in *; intros.
      - trivial.
      - invcs H1.
        constructor.
        + rewrite <- H; trivial.
        + eauto.
      - invcs H1.
        invcs H4.
        invcs H5.
        constructor.
        + constructor.
          * symmetry; trivial.
          * rewrite <- H; trivial.
        + constructor.
          * rewrite <- H; trivial.
          * eauto.
      - eauto.
    Qed.

    Lemma all_disjoint_cons_inv {A} {a:A} {l1 l2} :
      all_disjoint ((a :: l1) :: l2) -> all_disjoint (l1::l2) /\ ~ In a (concat l2).
    Proof.
      intros disj; invcs disj.
      split.
      - constructor; trivial.
        revert H1; apply Forall_impl; intros ? disj.
        apply disjoint_cons_inv1 in disj; tauto.
      - rewrite Forall_forall in H1.
        rewrite concat_In.
        intros [x [inn1 inn2]].
        specialize (H1 _ inn1).
        apply (H1 a); simpl; eauto.
    Qed.

  End alldisjoint.

End ListAdd.

Hint Resolve disjoint_nil_l disjoint_nil_r : list.

Global Arguments remove_nin_inv {A eqdec v1 v2 l}.
