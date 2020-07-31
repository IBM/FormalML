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

(** Support for creating and reasoning about fresh names (represented
as strings). *)

Require Import String.
Require Import List.
Require Import Permutation.
Require Import Arith Min.
Require Import EquivDec.
Require Import Morphisms.
Require Import Lia.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import LibUtilsStringAdd.
Require Import LibUtilsDigits.
Require Import LibUtilsLift.
Require Import LibUtilsSublist.

Section Fresh.
  
  Section finder.
    Context {A:Type}.
    Context (incr:A->A).
    Context (f:A->bool).
    
    Fixpoint find_bounded (bound:nat) (init:A)
      := match bound with
         | O => None
         | S n =>
           if f init
           then Some init
           else find_bounded n (incr init)
         end.

    Lemma find_bounded_correct bound init y :
      find_bounded bound init = Some y ->
      f y = true.
    Proof.
      revert init.
      induction bound; simpl; intros.
      - discriminate.
      - match_case_in H; intros eqq; rewrite eqq in H.
        + inversion H; congruence.
        + eauto.
    Qed.
  End finder.

  Lemma find_bounded_S_ge f bound init y :
    find_bounded S f bound init = Some y ->
    y >= init.
  Proof.
    revert init y.
    induction bound; simpl; intros.
    - discriminate.
    - match_destr_in H.
      + inversion H; subst; lia.
      + specialize (IHbound (S init) _ H).
        lia.
  Qed.

  Lemma find_bounded_S_seq f bound init :
    find_bounded S f bound init = find f (seq init bound).
  Proof.
    revert init.
    induction bound; simpl; trivial; intros.
    match_destr; auto.
  Qed.

  Lemma find_bounded_S_nin_finds' {A:Type} f {dec:EqDec A eq} (dom:list A)
        (bound:nat) (pf:bound > length dom)
        (inj:forall x y, f x = f y -> x = y) :
    {y:A | lift f (find_bounded S
                                (fun x =>
                                   if in_dec equiv_dec (f x) dom
                                   then false else true)
                                bound 0) = Some y}.
  Proof.
    rewrite find_bounded_S_seq.
    rewrite <- (find_over_map (fun x  => if in_dec equiv_dec x dom then false else true) f).
    apply find_fresh_from.
    - rewrite map_length.
      rewrite seq_length.
      trivial.
    - apply map_inj_NoDup; trivial.
      apply seq_NoDup.
  Defined.

  (* This version has better computational properties *)
  Definition find_bounded_S_nin_finds {A:Type} f {dec:EqDec A eq} (dom:list A)
             (bound:nat) (pf:bound > length dom)
             (inj:forall x y, f x = f y -> x = y) :
    {y:A | lift f (find_bounded S
                                (fun x =>
                                   if in_dec equiv_dec (f x) dom
                                   then false else true)
                                bound 0) = Some y}.
  Proof.
    case_eq (find_bounded S
                          (fun x : nat => if in_dec equiv_dec (f x) dom then false else true)
                          bound 0).
    - intros; simpl.
      exists (f n); reflexivity.
    - destruct (find_bounded_S_nin_finds' f dom bound pf inj); intros.
      rewrite H in e.
      simpl in e. discriminate.
  Defined.
  
  Definition find_fresh_inj_f {A:Type} {dec:EqDec A eq} f (inj:forall x y, f x = f y -> x = y) (dom:list A) : A
    := proj1_sig (find_bounded_S_nin_finds f dom (S (length dom)) (gt_Sn_n _) inj).

  Lemma find_fresh_inj_f_fresh {A:Type} {dec:EqDec A eq} f (inj:forall x y, f x = f y -> x = y) (dom:list A) :
    ~ In (find_fresh_inj_f f inj dom) dom.
  Proof.
    unfold find_fresh_inj_f.
    match goal with
    | [|- context[ proj1_sig ?x ]] => destruct x
    end; simpl.
    apply some_lift in e.
    destruct e as [? e ?]; subst.
    apply find_bounded_correct in e.
    match_destr_in e.
  Qed.

  Definition find_fresh_string (dom:list string)
    := find_fresh_inj_f
         nat_to_string16
         nat_to_string16_inj
         dom.
  
  Lemma find_fresh_string_is_fresh (dom:list string) : 
    ~ In (find_fresh_string dom) dom.
  Proof.
    unfold find_fresh_string.
    apply find_fresh_inj_f_fresh.
  Qed.


  (* Java equivalent: NnrcOptimizer.fresh_var (serves same purpose, not an exact translation) *)
  Definition fresh_var (pre:string) (dom:list string) :=
    let problems:=filter (prefix pre) dom in
    let problemEnds:=
        map (fun x => substring (String.length pre) (String.length x - String.length pre) x) problems in
    append pre (find_fresh_string problemEnds).

  Lemma fresh_var_fresh pre (dom:list string) : 
    ~ In (fresh_var pre dom) dom.
  Proof.
    unfold fresh_var.
    intros inn.
    rewrite in_of_append in inn.
    apply find_fresh_string_is_fresh in inn.
    trivial.
  Qed.

  Lemma fresh_var_fresh1 x1 pre dom :
    x1 <> fresh_var pre (x1::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

  Lemma fresh_var_fresh2 x1 x2 pre dom :
    x2 <> fresh_var pre (x1::x2::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::x2::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

  Lemma fresh_var_fresh3 x1 x2 x3 pre dom :
    x3 <> fresh_var pre (x1::x2::x3::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::x2::x3::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

  Lemma fresh_var_fresh4 x1 x2 x3 x4 pre dom :
    x4 <> fresh_var pre (x1::x2::x3::x4::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::x2::x3::x4::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

  Definition fresh_var2 pre1 pre2 (dom:list string) :=
    let fresh_var1 := fresh_var pre1 dom in
    (fresh_var1, fresh_var pre2 (fresh_var1::dom)).
  
  Lemma fresh_var2_distinct pre1 pre2 dom :
    (fst (fresh_var2 pre1 pre2 dom)) <>
    (snd (fresh_var2 pre1 pre2 dom)).
  Proof.
    unfold fresh_var2; simpl.
    apply fresh_var_fresh1.
  Qed.

  Definition fresh_var3 pre1 pre2 pre3 (dom:list string) :=
    let fresh_var1 := fresh_var pre1 dom in
    let fresh_var2 := fresh_var pre2 (fresh_var1::dom) in
    let fresh_var3 := fresh_var pre3 (fresh_var2::fresh_var1::dom) in
    (fresh_var1, fresh_var2, fresh_var3).
  
  Lemma fresh_var3_distinct pre1 pre2 pre3 dom :
    (fst (fst (fresh_var3 pre1 pre2 pre3 dom))) <>
    (snd (fst (fresh_var3 pre1 pre2 pre3 dom))) /\
    (snd (fst (fresh_var3 pre1 pre2 pre3 dom))) <>
    (snd (fresh_var3 pre1 pre2 pre3 dom)) /\
    (fst (fst (fresh_var3 pre1 pre2 pre3 dom))) <>
    (snd (fresh_var3 pre1 pre2 pre3 dom)).
  Proof.
    unfold fresh_var3; simpl.
    split;[|split].
    - apply fresh_var_fresh1.
    - apply fresh_var_fresh1.
    - apply fresh_var_fresh2.
  Qed.

  (* given a variable, gets the "base": the part before the last seperator *)
  Definition get_var_base (sep:string) (var:string)
    := match index 0 (string_reverse sep) (string_reverse var) with
       | Some n => substring 0 (String.length var - (S n)) var
       | None => var
       end.

  Lemma get_var_base_pre sep var :
    prefix (get_var_base sep var) var = true.
  Proof.
    unfold get_var_base.
    match_destr; simpl.
    - apply substring_prefix.
    - apply prefix_refl.
  Qed.

  Definition fresh_var_from sep (oldvar:string) (dom:list string) : string
    := if in_dec string_dec oldvar dom
       then fresh_var (append (get_var_base sep oldvar) sep) dom
       else oldvar.

  Lemma fresh_var_from_fresh sep oldvar (dom:list string) : 
    ~ In (fresh_var_from sep oldvar dom) dom.
  Proof.
    unfold fresh_var_from.
    match_destr.
    apply fresh_var_fresh.
  Qed.

  Lemma find_fresh_inj_f_equivlist x y :
    equivlist x y ->
    find_fresh_inj_f nat_to_string16 nat_to_string16_inj x =
    find_fresh_inj_f nat_to_string16 nat_to_string16_inj y.
  Proof.
    intros.
    unfold find_fresh_inj_f; simpl.
    repeat (match goal with
            | [|- context[ proj1_sig ?x ]] => destruct x
            end; simpl).
    apply some_lift in e.
    destruct e as [? e ?]; subst.
    apply some_lift in e0.
    destruct e0 as [? e0 ?]; subst.
    f_equal.
    rewrite find_bounded_S_seq in e, e0.
    rewrite (find_ext
               (fun x0 : nat => if in_dec equiv_dec (nat_to_string16 x0) x then false else true)
               (fun x0 : nat => if in_dec equiv_dec (nat_to_string16 x0) y then false else true)) in e.
    - eapply find_seq_same; eauto.
    - intros.
      do 2 match_destr.
      + rewrite H in i; congruence.
      + rewrite <- H in i; congruence.
  Qed.
  
  Global Instance find_fresh_string_equivlist : Proper (equivlist ==> eq) find_fresh_string.
  Proof.
    intros ???.
    unfold find_fresh_string.
    apply find_fresh_inj_f_equivlist; trivial.      
  Qed.
  (*
Eval vm_compute in 
      fresh_var_from "$"%string "cat_var$5"%string ("cat_var$0"::"i"::"cat_var$5"::"tmp1"::"tmp2"::"cat_var1"::nil)%string.
   *)

  Global Instance fresh_var_equivlist : Proper (eq ==> equivlist ==> eq) fresh_var.
  Proof.
    intros ??????; subst.
    unfold fresh_var.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma fresh_var_from_id sep v l :
    ~ In v l ->
    fresh_var_from sep v l = v.
  Proof.
    unfold fresh_var_from.
    match_destr; tauto.
  Qed.

  Lemma fresh_var_from_nincl {sep v l l2} :
    In (fresh_var_from sep v l) l2 -> ~ incl l2 l.
  Proof.
    intros inn1 incl.
    apply (fresh_var_from_fresh sep v l).
    apply incl; trivial.
  Qed.

  Lemma fresh_var_from_incl_nin sep v l1 l2 :
    incl l2 l1 ->
    ~ In (fresh_var_from sep v l1) l2.
  Proof.
    intros incl1 inn.
    apply (fresh_var_from_nincl inn); trivial.
  Qed.

End Fresh.

Ltac prove_fresh_nin
  := match goal with
     | [ |- ~ In (fresh_var ?pre ?l) _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ |- In (fresh_var ?pre ?l) _ -> False] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ |- ~ (fresh_var ?pre ?l) = _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ |-  (fresh_var ?pre ?l) <> _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ H:In (fresh_var ?pre ?l) _ |- _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ H:(fresh_var ?pre ?l) = _ |- _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     end.

