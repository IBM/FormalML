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

(** This module provides support for monadic iterators over bags. *)

Require Import Arith.
Require Import Min.
Require Import Max.
Require Import Lia.
Require Import Permutation.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import List.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import LibUtilsLift.
Require Import LibUtilsSublist.

Section LiftIterators.
  (** * Lift iterators *)

  (** ** Lifted map *)
  
  Section lift_map.
    Fixpoint lift_map {A B} (f : A -> option B) (l:list A) : option (list B) :=
      match l with
      | nil => Some nil
      | x :: t =>
        match f x with
        | None => None
        | Some x' =>
          lift (fun t' => x' :: t') (lift_map f t)
        end
      end.

    Lemma lift_map_Forall {A B} {f:A->option B} {P} {l x} :
      lift_map f l = Some x ->
      Forall P l ->
      forall (P2:B->Prop),
        (forall x z, f x = Some z -> P x -> P2 z) ->
        Forall P2 x.
    Proof.
      revert x. induction l; simpl.
      - inversion 1; subst; trivial.
      - match_case; intros.
        inversion H1; subst.
        destruct (lift_map f l); simpl in *; try discriminate.
        inversion H0; subst.
        eauto.
    Qed.

    Lemma lift_map_id {A} l:
      lift_map (fun d : A => Some d) l = Some l.
    Proof.
      induction l; try reflexivity.
      simpl.
      unfold lift.
      rewrite IHl; reflexivity.
    Qed.
    
    Lemma lift_map_map {A B} (f:A -> B) l:
      lift_map (fun d : A => Some (f d)) l = Some (map f l).
    Proof.
      induction l; try reflexivity.
      simpl.
      unfold lift.
      rewrite IHl; reflexivity.
    Qed.

    Lemma lift_map_lift {A B C} (f:B->C) (g:A->option B) l :
    lift_map (fun x => lift f (g x)) l =
    lift (map f) (lift_map g l).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl.
    destruct (g a); simpl; trivial.
    destruct (lift_map g l); simpl; trivial.
  Qed.
    
    Lemma lift_map_map_merge {A} {B} {C} (f1:A -> B) (f2:B -> option C) (l: list A):
      (lift_map (fun d => f2 (f1 d)) l) =
      lift_map f2 (map f1 l).
    Proof.
      induction l; intros; simpl; [reflexivity| ].
      destruct (f2 (f1 a)); [|reflexivity].
      rewrite IHl.
      reflexivity.
    Qed.

    Lemma lift_map_over_app {A B} (f:A -> option B) (l1:list A) (l2:list A) :
      lift_map f (l1 ++ l2) = olift2 (fun x y => Some (x++y)) (lift_map f l1) (lift_map f l2).
    Proof.
      revert l2.
      induction l1; intros.
      - simpl; destruct (lift_map f l2); reflexivity.
      - simpl.
        destruct (f a); try reflexivity.
        rewrite IHl1.
        generalize (lift_map f l1); generalize (lift_map f l2); intros.
        destruct o0; destruct o; reflexivity.
    Qed.

    (* sometimes useful when coq compiler chokes on Fixpoints with lift_map *)
    Fixpoint listo_to_olist {a: Type} (l: list (option a)) : option (list a) :=
      match l with
      | nil => Some nil
      | Some x :: xs => match listo_to_olist xs with
                        | None => None
                        | Some xs => Some (x::xs)
                        end
      | None :: xs => None
      end.

    Lemma listo_to_olist_simpl_lift_map {A B:Type} (f:A -> option B) (l:list A) :
      lift_map f l = (listo_to_olist (map f l)).
    Proof.
      induction l; intros.
      - reflexivity.
      - simpl.
        destruct (f a).
        * rewrite IHl; reflexivity.
        * reflexivity.
    Qed.

    Lemma listo_to_olist_some {A:Type} (l:list (option A)) (l':list A) :
      listo_to_olist l = Some l' ->
      l = (map Some l').
    Proof.
      revert l'.
      induction l; simpl; intros l' eqq.
      - invcs eqq; simpl; trivial.
      - destruct a; try discriminate.
        match_destr_in eqq.
        invcs eqq.
        simpl.
        rewrite <- IHl; trivial.
    Qed.
    
    Lemma lift_map_ext  {A B : Type} (f g : A -> option B) (l : list A) :
      (forall x, In x l -> f x = g x) ->
      lift_map f l = lift_map g l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite IHl by intuition.
      rewrite (H a) by intuition.
      trivial.
    Qed.

    Lemma lift_map_map_fusion {A B C}
          (f:B->option C) (g:A -> B) (l:list A) :
      lift_map f (map g l) = lift_map (fun x => f (g x)) l.
    Proof.
      induction l; simpl; trivial.
      match_destr. rewrite IHl; trivial.
    Qed.

    Lemma lift_map_Forall_exists {A B} (f:A->option B) l :
      Forall (fun x => exists y, f x = Some y) l ->
      exists l', lift_map f l = Some l'
                 /\ Forall2 (fun old new => f old = Some new) l l'.
    Proof.
      induction l; simpl; intros F.
      - eauto.
      - invcs F.
        destruct H1 as [? eqq1].
        destruct (IHl H2) as [? [eqq2 Feq]].
        rewrite eqq1, eqq2; simpl.
        eauto.
    Qed.

    Lemma lift_map_Forall_exists_strong {A B} (f:A->option B) l :
      Forallt (fun x => {y | f x = Some y}) l ->
      { l' | lift_map f l = Some l'
             & Forall2 (fun old new => f old = Some new) l l'}.
    Proof.
      induction l; simpl; intros F.
      - eauto.
      - invcs F.
        destruct X as [? eqq1].
        destruct (IHl X0) as [? eqq2 Feq].
        rewrite eqq1, eqq2; simpl.
        eauto.
    Qed.

    Lemma lift_map_Forall_exists_and {A B} {P:B->Prop} (f:A->option B) l :
      Forall (fun x => exists y, f x = Some y /\ P y) l ->
      exists l', lift_map f l = Some l'
                 /\ Forall P l'.
    Proof.
      induction l; simpl; intros F.
      - eauto.
      - invcs F.
        destruct H1 as [? [eqq1 Px]].
        destruct (IHl H2) as [? [eqq2 Feq]].
        rewrite eqq1, eqq2; simpl.
        eauto.
    Qed.

    Lemma lift_map_Forall_exists_and_strong {A B} {P:B->Prop} (f:A->option B) l :
      Forallt (fun x => {y | f x = Some y & P y}) l ->
      { l' | lift_map f l = Some l'
             & Forall P l'}.
    Proof.
      induction l; simpl; intros F.
      - eauto.
      - invcs F.
        destruct X as [? eqq1 Px].
        destruct (IHl X0) as [? eqq2 Feq].
        rewrite eqq1, eqq2; simpl.
        eauto.
    Qed.

    
  End lift_map.

  (** ** Lifted flat-map *)
  
  Section lift_flat_map.
    Fixpoint lift_flat_map {A B} (f : A -> option (list B)) (l:list A) : option (list B) :=
      match l with
      | nil => Some nil
      | x :: t =>
        match f x with
        | None => None
        | Some x' =>
          lift (fun t' => x' ++ t') (lift_flat_map f t)
        end
      end.

    Lemma lift_flat_map_Forall {A B} {f:A->option (list B)} {P} {l x} :
      lift_flat_map f l = Some x ->
      Forall P l ->
      forall P2,
        (forall x z, f x = Some z -> P x -> Forall P2 z) ->
        Forall P2 x.
    Proof.
      revert x. induction l; simpl.
      - inversion 1; subst; trivial.
      - match_case; intros.
        inversion H1; subst.
        destruct (lift_flat_map f l); simpl in *; try discriminate.
        inversion H0; subst.
        apply Forall_app; eauto.
    Qed.

    Lemma lift_flat_map_ext {A B} (f g:A->option (list B)) l :
      (forall x, In x l -> f x = g x) ->
      lift_flat_map f l = lift_flat_map g l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite IHl by intuition.
      rewrite (H a) by intuition.
      trivial.
    Qed.
  End lift_flat_map.

  (** ** Lifted filter *)
  
  Section lift_filter.
    Fixpoint lift_filter {A:Type} (f:A -> option bool) (l:list A) : option (list A) :=
      match l with
      | nil => Some nil
      | x::l' =>
        match (f x) with
        | None => None
        | Some b =>
          match lift_filter f l' with
          | None => None
          | Some l'' =>
            if b then Some (x::l'') else Some l''
          end
        end
      end.

    Lemma lift_filter_eq {A} (f g:A -> option bool) l :
      (forall a, In a l -> f a = g a) ->
      lift_filter f l = lift_filter g l.
    Proof.
      intros.
      induction l; try reflexivity.
      simpl in *.
      assert (forall a0, In a0 l -> f a0 = g a0).
      intros; apply H. right; assumption.
      specialize (IHl H0).
      assert (f a = g a).
      apply (H a); left; reflexivity.
      clear H.
      rewrite H1. rewrite IHl.
      reflexivity.
    Qed.

    Lemma lift_filter_Forall {A} {f:A->option bool} {P} {l x} :
      lift_filter f l = Some x ->
      Forall P l ->
      Forall P x.
    Proof.
      revert x; induction l; simpl.
      - inversion 1; subst; eauto.
      - match_case; intros.
        inversion H1; subst.
        destruct (lift_filter f l); simpl in *; try discriminate; intros.
        destruct b; inversion H0; subst; eauto.
    Qed.

    Lemma lift_filter_ext {A : Type} (f g : A -> option bool) (l : list A) : 
      (forall x, In x l -> f x = g x) ->
      lift_filter f l = lift_filter g l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite IHl by intuition.
      rewrite (H a) by intuition.
      trivial.
    Qed.

    Definition orfilter {A} (f:A -> option bool) (ol:option (list A)) : option (list A) :=
      olift (lift_filter f) ol.

    Lemma lift_filter_Forall_exists {A} (f:A->option bool) l :
      Forall (fun x => exists y, f x = Some y) l ->
      exists l', lift_filter f l = Some l'
                 /\ sublist l' l.
    Proof.
      induction l; simpl; intros F.
      - eauto with fml.
      - invcs F.
        destruct H1 as [? eqq1].
        destruct (IHl H2) as [? [eqq2 Feq]].
        rewrite eqq1, eqq2; simpl.
        destruct x; simpl
        ; eexists; split; try reflexivity.
        + constructor; trivial.
        + constructor; trivial.
    Qed.

    Lemma lift_filter_Forall_exists_strong {A} (f:A->option bool) l :
      Forallt (fun x => { y | f x = Some y}) l ->
      { l' : list A | lift_filter f l = Some l' & sublist l' l}.
    Proof.
      induction l; simpl; intros F.
      - eauto with fml.
      - invcs F.
        destruct H0 as [? eqq1].
        destruct (IHl X) as [? eqq2 Feq].
        rewrite eqq1, eqq2; simpl.
        destruct x; simpl
        ; eexists; constructor; try reflexivity; trivial.
    Qed.

  End lift_filter.

  (** ** Lifted append *)
  
  Section lift_app.

    Definition lift_app {A:Type} (l1 l2:option (list A)) : option (list A) :=
      match l1,l2 with
      | Some l1',Some l2' => Some (l1'++l2')
      | _,_ => None
      end.

    Lemma lift_app_filter {A:Type} (p:A -> option bool) (l1 l2:list A):
      lift_filter p (app l1 l2) = lift2 (@app A) (lift_filter p l1) (lift_filter p l2).
    Proof.
      induction l1; simpl.
      destruct (lift_filter p l2); reflexivity.
      destruct (p a); simpl; try reflexivity.
      rewrite IHl1; clear IHl1.
      destruct (lift_filter p l1); try reflexivity.
      destruct b; destruct (lift_filter p l2); reflexivity.
    Qed.
  End lift_app.

  (** ** Lifted flatten *)
  
  Section lift_flatten.
    Definition lift_flatten {A} : option (list (list A)) -> option (list A) :=
      lift lflatten.

    Lemma filter_eq_flatten_if {A} (e:A -> option bool) (ol:option (list A)) :
      orfilter e ol = lift_flatten (olift (lift_map (rif e)) ol).
    Proof.
      destruct ol; try reflexivity.
      induction l.
      reflexivity.
      simpl.
      unfold rif in *.
      destruct (e a); try reflexivity.
      destruct b; simpl in *; rewrite IHl; clear IHl;
        generalize ((lift_map
                       (fun a0 : A =>
                          match e a0 with
                          | Some true => Some (a0::nil)
                          | Some false => Some nil
                          | None => None
                          end) l)); intros;
          destruct o; reflexivity.
    Qed.
  End lift_flatten.

  Section lift_err.

    Definition lift_err {A E B} (f:A->B) (a:E+A) : E+B
      := match a with
         | inl e => inl e
         | inr a' => inr (f a')
         end.
    
    Fixpoint lift_err_map {A E B} (f:A->E+B) (l:list A) : E + list B
      := match l with
         | nil => inr nil
         | x::t =>
           match f x with
           | inl e => inl e
           | inr x' =>
             lift_err (fun t' => x' :: t') (lift_err_map f t)
           end
         end.
    
    Lemma lift_err_map_map {A B E C} (f:B->E+C) (g:A->B) (l:list A) :
      lift_err_map f (map g l) = lift_err_map (fun x => f (g x)) l.
    Proof.
      induction l; simpl; trivial.
      rewrite IHl; trivial.
    Qed.

    Lemma lift_err_map_inr {A E} (l:list A) :
      lift_err_map (@inr E A) l = inr l.
    Proof.
      induction l; simpl; trivial.
      rewrite IHl; trivial.
    Qed.

    Lemma lift_err_map_ext  {A E B} (f g:A->E+B) (l:list A) :
      (forall x, In x l -> f x = g x) ->
      lift_err_map f l = lift_err_map g l.
    Proof.
      intros eqq.
      induction l; simpl; trivial.
      rewrite eqq, IHl; simpl in *; eauto.
    Qed.

    Lemma lift_err_map_eta  {A E B} (f:A->E+B) (l:list A) :
      lift_err_map (fun x => f x) l = lift_err_map f l.
    Proof.
      apply lift_err_map_ext; trivial.
    Qed.

  End lift_err.

End LiftIterators.

