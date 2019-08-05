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

(** This module contains definitions and properties of association
lists. *)

Require Import String.
Require Import List.
Require Import Sumbool.
Require Import Bool.
Require Import Permutation.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Equivalence.
Require Import Peano_dec.
Require Import Ascii.
Require Import LibUtilsCoqLibAdd.
Require Import LibUtilsListAdd.
Require Import LibUtilsStringAdd.
Require Import LibUtilsLift.

Section Assoc.

  (** * Association lists *)
  
  Section Defn.
    Context {A B:Type}.
    Context (dec:forall a a':A, {a=a'} + {a<>a'}).

    (* define lookup for assocation lists *)
    Fixpoint lookup l a : option B
      := match l with 
         | nil => None
         | (f',v')::os => if dec a f' then Some v' else lookup os a
         end.

    Fixpoint update_first l a n : list (A*B)
      := match l with 
         | nil => nil
         | (f',v')::os => if dec a f' then (a,n)::os else (f',v')::(update_first os a n)
         end.

    Definition domain (l:list (A*B)) := map (@fst A B) l.
    Definition codomain (l:list (A*B)) := map (@snd A B) l.

    Definition map_codomain {A B C} (f:B->C) (l:list (A*B)) : list (A*C)
      := map (fun b => (fst b, f (snd b))) l.
    
    Lemma domain_eq (l:list (A*B)) : domain l = map fst l.
    Proof.
      reflexivity.
    Qed.
    
    Lemma domain_nil (l:list (A*B)) :
      domain l = nil <-> l = nil.
    Proof.
      destruct l; simpl in *; intuition discriminate.
    Qed.

    Lemma codomain_nil (l:list (A*B)) :
      codomain l = nil <-> l = nil.
    Proof.
      destruct l; simpl in *; intuition discriminate.
    Qed.

    Lemma domain_rev (l:list (A*B)) : domain (rev l) = rev (domain l).
    Proof.
      unfold domain. apply map_rev.
    Qed.

    Lemma codomain_rev (l:list (A*B)) : codomain (rev l) = rev (codomain l).
    Proof.
      unfold codomain. apply map_rev.
    Qed.

    Lemma domain_update_first l a v: domain (update_first l a v) = domain l.
    Proof.
      induction l; simpl; trivial.
      destruct a0; simpl.
      destruct (dec a a0); subst; auto.
      simpl. congruence.
    Qed.

    Lemma map_eta_fst_domain l :
      (map (fun x : A * B => fst x) l) = domain l.
    Proof.
      unfold domain.
      apply map_eq.
      apply Forall_forall; auto.
    Qed.

    Lemma in_dom : forall {l} {a b}, In (a,b) l -> In a (domain l).
    Proof.
      unfold domain; induction l; simpl; trivial.
      intros. destruct a; simpl in *; intuition.
      inversion H0; intuition.
      eauto.
    Qed.

    Lemma in_codom {l : list (A * B)} {a : A} {b : B} :
      In (a, b) l -> In b (codomain l).
    Proof.
      intros.
      apply in_map_iff.
      exists (a,b); tauto.
    Qed.

    Lemma in_domain_in : forall {l} {a}, In a (domain l) -> exists b, In (a,b) l.
    Proof.
      induction l; simpl. intuition.
      intuition.
      simpl in *. subst; econstructor. intuition.
      destruct (IHl _ H0); eauto.
    Qed.

    Lemma lookup_none_nin :  forall {l} {a:A}, lookup l a = None -> ~ In a (domain l).
    Proof.
      induction l; simpl; intros; auto.
      destruct a. destruct (dec a0 a); subst; try discriminate.
      intuition.
      eauto.
    Qed.

    Lemma lookup_nin_none {l x} : ~ In x (domain l) -> lookup l x = None.
    Proof.
      induction l; simpl; intros; auto. 
      destruct a; simpl in *. intuition.
      destruct (dec x a); subst; intuition.
    Qed.

    Lemma NoDup_domain_NoDup {l} : NoDup (domain l) -> NoDup l.
    Proof.
      induction l; simpl; intros; [ constructor | ].
      inversion H; subst.
      constructor; auto.
      intro ina; apply H2.
      destruct a.
      eapply in_dom; eauto.
    Qed.

    Lemma lookup_in : forall l {a:A} {b:B}, lookup l a = Some b -> In (a,b) l.
    Proof.
      induction l; simpl; intuition.
      - discriminate.
      - destruct (dec a a0).
        + inversion H; intuition congruence.
        + intuition.
    Qed.

    Lemma lookup_in_domain : forall l {a:A} {b:B}, lookup l a = Some b -> In a (domain l).
    Proof.
      induction l; simpl; intuition.
      - discriminate.
      - destruct (dec a a0); simpl.
        + inversion H; intuition congruence.
        + right; apply (IHl a b0); assumption.
    Qed.

    Lemma lookup_to_front {l a x} : lookup l a = Some x -> exists l', Permutation l ((a,x)::l').
    Proof.
      intros.
      apply lookup_in in H.
      apply in_split in H.
      destruct H as [l1 [l2 leq]].
      exists (l1++l2).
      rewrite leq.
      symmetry.
      apply Permutation_middle.
    Qed.

    Lemma  lookup_split {l:list (A*B)} {a b} :
      lookup l a = Some b ->
      exists l1 l2 : list (A*B), l = l1 ++ (a,b) :: l2 /\ ~ In a (domain l1). 
    Proof.
      induction l; simpl; try discriminate; intros lo.
      destruct a0.
      match_destr_in lo; unfold equiv, complement in *.
      - invcs lo.
        exists nil, l; simpl; tauto.
      - destruct (IHl lo) as [l1 [l2 [? nin]]]; subst.
        exists ((a0,b0)::l1), l2; simpl.
        intuition.
    Qed.

    Global Instance dom_perm : Proper (@Permutation (A*B) ==> @Permutation A) domain.
    Proof.
      repeat red; intros.
      apply Permutation_map; auto.
    Qed.

    Global Instance perm_nodup :Proper (@Permutation (A) ==> iff) (@NoDup A).
    Proof.
      cut (forall l1 l2, @Permutation A l1 l2 -> (NoDup l1 -> NoDup l2)).
      - repeat red; intros; intuition eauto. symmetry in H0; eauto.
      - apply (@Permutation_ind_bis _ (fun x y => NoDup x -> NoDup y)); intuition.
        + inversion H1; subst. constructor; auto. intro; apply H4.
          symmetry in H; apply (Permutation_in _ H); trivial.
        + inversion H1; subst. inversion H5; subst. constructor; auto.
          * simpl in *. intro; apply H6. symmetry in H; apply (Permutation_in _ H); trivial.
            intuition congruence.
          * constructor; auto.
            simpl in *. intuition. apply H8. symmetry in H. apply (Permutation_in _ H).
            trivial.
    Qed.

    Lemma nodup_in_eq : forall {l} {a b c}, NoDup (domain l) -> In (a,b) l -> In (a,c) l -> b = c.
    Proof.
      induction l; simpl; intros; inversion H.
      intuition.
      intuition; subst.
      try inversion H0; try inversion H2; subst; trivial.
      - elim H4. eapply in_dom; eauto.
      - elim H4. eapply in_dom; eauto.
      - eauto.
    Qed.

    (* TODO: this should just replace in_dom_lookup *)      

    Lemma in_dom_lookup_strong :  forall {l} {a:A}, In a (domain l) -> {v | lookup l a = Some v}.
    Proof.
      induction l; simpl; [tauto|]; intros.
      destruct a; simpl in *.
      destruct (dec a0 a); [eauto|].
      apply IHl.
      intuition.
    Qed.

    Lemma in_dom_lookup :  forall {l} {a:A}, In a (domain l) -> exists v, lookup l a = Some v.
    Proof.
      intros ? ? ind.
      destruct (in_dom_lookup_strong ind).
      eauto.
    Qed.

    (* TODO: this should just replace in_lookup *)      
    Lemma in_lookup_strong :  forall {l} {a:A} {b0:B}, In (a,b0) l -> {v | lookup l a = Some v}.
    Proof.
      Hint Resolve in_dom_lookup_strong in_dom : list.
      intros. eauto with list.
    Qed.

    Lemma in_lookup :  forall {l} {a:A} {b0:B}, In (a,b0) l -> exists v, lookup l a = Some v.
    Proof.
      Hint Resolve in_dom_lookup in_dom : list.
      intros. eauto with list.
    Qed.

    Lemma in_lookup_nodup : forall {l} {a:A} {b:B}, NoDup (domain l) -> In (a,b) l -> lookup l a = Some b.
    Proof.
      intros.
      destruct (in_lookup H0).
      generalize (lookup_in _ H1); intros.
      generalize (nodup_in_eq H H0 H2); congruence.
    Qed.

    Lemma nin_update {l a} : lookup l a = None -> forall v, update_first l a v = l.
    Proof.
      induction l; simpl; trivial.
      destruct a0. destruct (dec a a0); intuition congruence.
    Qed.

    Lemma in_update_break {l a v} :
      lookup l a = Some v -> forall vv,
        exists l1 l2, l = l1++(a,v)::l2 /\
                      update_first l a vv = l1++(a,vv)::l2.
    Proof.
      induction l; simpl; intuition (try discriminate).
      destruct a0. destruct (dec a a0); intuition; subst.
      - inversion H; subst.
        exists nil; exists l; simpl; intuition.
      - destruct (H0 vv) as [l1 [l2 [leq1 leq2]]].
        subst. exists ((a0,b)::l1); exists l2; simpl; intuition.
        congruence.
    Qed.

    Lemma in_in_split_domain_or (l:list (list (A*B))) a :
      (exists l1 la l2, l = l1++la::l2 /\ In a (domain la) /\ ~ In a (domain (concat l1)))
      \/ Forall (fun x => ~ In a (domain x)) l.
    Proof.
      destruct (in_in_split_or (map domain l) a (dec:=dec)).
      - left.
        destruct H as [l1 [la [l2 [eqq [inn nin]]]]].
        destruct (map_app_break _ eqq)
          as [m1 [m2 [eqq1 [eqq2 eqq3]]]]; subst.
        destruct m2; simpl in *; try discriminate.
        unfold domain in *.
        rewrite <- concat_map in nin.
        invcs eqq3.
        exists m1, l, m2; eauto.
      - right.
        rewrite Forall_map in H; trivial.
    Qed.

    Lemma in_in_split_domain_first {l:list (list (A*B))} {a} :
      In a (domain (concat l)) ->
      exists l1 la l2, l = l1++la::l2 /\ In a (domain la) /\ ~ In a (domain (concat l1)).
    Proof.
      intros inn.
      destruct (in_in_split_domain_or l a)
        as [[l1 [la [l3 [eqq1 [inn1 nin1]]]]]|nin].
      - exists l1, la, l3; eauto.
      - unfold domain in inn.
        rewrite concat_map in inn.
        apply concat_In in inn.
        destruct inn as [ll [inn1 inn2]].
        rewrite Forall_forall in nin.
        apply in_map_iff in inn1.
        destruct inn1 as [ll'  [eqq1 inn3]]; subst.
        elim (nin ll'); eauto.
    Qed.

    Lemma update_app_in  (l1 l2:list (A*B)) v d :
      In v (domain l1) -> 
      update_first (l1++l2) v d = update_first l1 v d ++ l2.
    Proof.
      revert l2;
        induction l1; simpl; intros l2.
      - tauto.
      - destruct a; simpl.
        intros [eqq | inn].
        + subst.
          match_destr; try congruence.
        + rewrite (IHl1 _ inn).
          match_destr.
    Qed.

    Lemma update_app_nin (l1 l2:list (A*B)) v d :
      ~ In v (domain l1) -> 
      update_first (l1++l2) v d = l1 ++ update_first l2 v d.
    Proof.
      revert l2;
        induction l1; simpl; intros l2.
      - tauto.
      - destruct a; simpl.
        intros H; apply Decidable.not_or in H.
        destruct H as [neq nin].
        destruct (dec v a); [congruence | ].
        rewrite (IHl1 _ nin); trivial.
    Qed.

    Lemma update_app_nin2  (l1 l2:list (A*B)) v d :
      ~ In v (domain l2) -> 
      update_first (l1++l2) v d = update_first l1 v d ++ l2.
    Proof.
      intros nin2.
      destruct (in_dec dec v (domain l1)).
      - rewrite update_app_in; trivial.
      - rewrite update_app_nin; trivial.
        repeat rewrite nin_update; trivial
        ; apply lookup_nin_none; trivial.
    Qed.

    Lemma update_first_concat_disjoint_push (ls:list (list (A*B))) v d:
      all_disjoint (map domain ls) ->
      (update_first (concat ls) v d) =
      (concat (map (fun x => update_first x v d) ls)).
    Proof.
      induction ls; simpl; trivial.
      intros disj.
      invcs disj.
      rewrite <- (IHls H2).
      destruct (in_dec dec v (domain a)) as [inn|nin].
      - rewrite update_app_in by trivial.
        f_equal.
        rewrite nin_update; trivial.
        apply lookup_nin_none.
        unfold domain; rewrite concat_map.
        intros inn2.
        apply concat_In in inn2.
        destruct inn2 as [? [inn2 inn3]].
        rewrite Forall_forall in H1.
        specialize (H1 _ inn2).
        eapply H1; eauto.
      - rewrite update_app_nin by trivial.
        f_equal.
        rewrite nin_update; trivial.
        apply lookup_nin_none; trivial.
    Qed.

    Lemma Forall_update_first P (l:list (A*B)) x v : 
      Forall P l ->
      P (x,v) ->
      Forall P (update_first l x v).
    Proof.
      induction l; simpl; trivial; intros.
      invcs H.
      destruct a.
      match_destr; subst; eauto.
    Qed.

    Lemma update_first_in_or {l : list (A * B)} {z} {x} {v} :
      In z (update_first l x v) ->
      In z l \/ z = (x,v).
    Proof.
      induction l; simpl; intuition.
      destruct a.
      match_destr_in H; subst; simpl in *; intuition.
    Qed.

    Lemma update_first_update_first_eq (l:list (A*B)) v d1 d2 :
      update_first (update_first l v d1) v d2 = update_first l v d2.
    Proof.
      induction l; simpl; trivial.
      destruct a.
      match_destr; simpl; subst; trivial
      ; match_destr; congruence.
    Qed.
    
    Lemma update_first_update_first_neq_swap (l:list (A*B)) v1 d1 v2 d2 :
      v1 <> v2 ->
      update_first (update_first l v1 d1) v2 d2 =
      update_first (update_first l v2 d2) v1 d1.
    Proof.
      intros neq.
      induction l; simpl; trivial.
      destruct a.
      repeat (match_destr; simpl; subst; try congruence).
    Qed.

    Lemma lookup_some_nodup_perm {l l'} a v:
      NoDup (domain l) -> 
      Permutation l l' ->
      lookup l a = Some v ->
      lookup l' a = Some v.
    Proof.
      intros. apply lookup_in in H1.
      apply (Permutation_in _ H0) in H1.
      apply in_lookup_nodup; auto.
      rewrite H0 in H; trivial.
    Qed.

    Lemma lookup_none_perm {l l'} a :
      Permutation l l' ->
      lookup l a = None ->
      lookup l' a = None.
    Proof.
      intros.
      case_eq (lookup l' a); trivial.
      intros b bleq.
      apply lookup_in in bleq.
      symmetry in H.
      apply (Permutation_in _ H) in bleq.
      apply lookup_none_nin in H0.
      elim H0. eapply in_dom; eauto.
    Qed.

    Lemma update_first_NoDup_perm_proper {l l'} a v :
      NoDup (domain l) -> 
      Permutation l l' ->
      Permutation (update_first l a v) (update_first l' a v).
    Proof.
      intros.
      case_eq (lookup l a); [intros vv eqv|intros neq].
      - generalize (lookup_some_nodup_perm _ _ H H0 eqv); intro eqv'.
        destruct (in_update_break eqv v) as [l1 [l2 [leq1 leq2]]].
        destruct (in_update_break eqv' v) as [l1' [l2' [leq1' leq2']]].
        subst; rewrite leq2, leq2'.
        rewrite (Permutation_app_comm l1), (Permutation_app_comm l1').
        simpl. apply perm_skip.
        rewrite (Permutation_app_comm l1), (Permutation_app_comm l1') in H0.
        simpl in H0. 
        apply Permutation_cons_inv in H0.
        trivial.
      - repeat rewrite nin_update; auto. eapply lookup_none_perm; eauto.
    Qed.

    Lemma lookup_update_eq_in {l:list (A*B)} {a} {n:B} :
      In a (domain l) ->
      lookup (update_first l a n) a = Some n.
    Proof.
      revert a n.
      induction l; simpl; intuition; simpl in *; subst.
      - destruct (dec a a); simpl; intuition.
        destruct (dec a a); simpl; intuition.
      - case_eq (dec a a0); simpl; intros; try rewrite e in *; subst; rewrite H; auto.
    Qed.
    
    Lemma lookup_update_neq {l a a'} {n:B} : a<>a' -> lookup (update_first l a n) a' = lookup l a'.
    Proof.
      revert a a' n. induction l; simpl; intuition.
      destruct (dec a a0); subst; simpl.
      - destruct (dec a' a0); try congruence.
      - destruct (dec a' a0); simpl; auto.
    Qed.

    Lemma in_update_break_first  {l:list (A*B)} {a v} :
      lookup l a = Some v -> forall vv,
        exists l1 l2,
          l = l1++(a,v)::l2 /\
          update_first l a vv = l1++(a,vv)::l2
          /\ ~ In a (domain l1).
    Proof.
      induction l; simpl; intuition (try discriminate).
      destruct a0. destruct (dec a a0); intuition; subst.
      - inversion H; subst.
        exists nil; exists l; simpl; intuition.
      - destruct (H0 vv) as [l1 [l2 [leq1 leq2]]].
        subst. exists ((a0,b)::l1); exists l2; simpl; intuition.
        congruence.
    Qed.

    Lemma in_domain_split_or (l:list (A*B)) a :
      (exists l1 b l2, l = l1++(a,b)::l2 /\ ~ In a (domain l1))
      \/ ~ In a (domain l).
    Proof.
      induction l; simpl; [ right; tauto | ].
      destruct a0.
      destruct (dec a a0) as [inn1|neq1]; unfold equiv, complement in *.
      - left; subst.
        exists nil, b, l; simpl; tauto.
      - destruct IHl as [[l1 [b' [l2 [eqq inn2]]]]|nin2]; simpl.
        + left; subst.
          exists ((a0,b)::l1), b', l2.
          repeat split; trivial.
          simpl; intuition.
        + right.
          intuition.
    Qed.

    Lemma lookup_app {l1 l2} x:
      lookup (l1++l2) x = 
      match lookup l1 x with
      | Some y => Some y
      | None => lookup l2 x
      end.
    Proof.
      revert l2 x. induction l1; simpl; intros.
      - trivial.
      - destruct a; simpl. rewrite IHl1.
        destruct (dec x a); reflexivity.
    Qed.

    Lemma lookup_app_in {l1 l2} a b :
      lookup (l1++l2) a = Some b -> In (a,b) l1 \/ In (a,b) l2.
    Proof.
      intros.
      rewrite lookup_app in H.
      case_eq (lookup l1 a); intros.
      - rewrite H0 in H; inversion H.
        rewrite H2 in *; clear H2 H b0.
        left; apply lookup_in; assumption.
      - rewrite H0 in H; clear H0.
        right; apply lookup_in; assumption.
    Qed.
    
    Lemma domain_cons a (l:list (A*B)) :
      domain (a::l) = (fst a)::domain l.
    Proof.
      reflexivity.
    Qed.
    
  End Defn.

  Lemma map_codomain_update_first {A B C} (f:B->C) dec (l:list (A*B)) v d :
    map_codomain f (update_first dec l v d) =
    update_first dec (map_codomain f l) v (f d).
  Proof.
    induction l; simpl; trivial.
    destruct a; simpl.
    destruct (dec v a); simpl; trivial.
    rewrite IHl; trivial.
  Qed.


  Lemma Forall2_lookup_none {K A B} {P:A->B->Prop}
        {l : list (K * A)} {l' : list (K * B)} :
    (Forall2
       (fun (d : K * A) (r : K * B) =>
          fst d = fst r /\ P (snd d) (snd r)) l l') ->
    forall {dec s},
      lookup dec l' s = None -> 
      lookup dec l s = None.
  Proof.
    intros.
    induction H; simpl in *.
    reflexivity.
    destruct x; destruct y; simpl in *.
    elim H; intros; clear H.
    rewrite H2 in *; clear H2 H3.
    revert H0 IHForall2.
    elim (dec s k0); intros; try congruence.
    auto.
  Qed.    

  Lemma Forall2_lookup_some {K A B} {P:A->B->Prop}
        {l : list (K * A)} {l' : list (K * B)} :
    (Forall2
       (fun (d : K * A) (r : K * B) =>
          fst d = fst r /\ P (snd d) (snd r)) l l') ->
    forall {dec} {s:K} {d':B},
      lookup dec l' s = Some d' -> 
      (exists d'', lookup dec l s = Some d'' /\ P d'' d').
  Proof.
    intros H.
    induction H; intros; simpl in *.
    - discriminate.
    - destruct x; destruct y; simpl in *.
      destruct H; subst.
      destruct (dec s k0).
      + invcs H1; eauto.
      + destruct (IHForall2 _ _ _ H1) as [?[??]].
        eauto.
  Qed.

  Lemma Forall2_lookup_some_with_key {K A B} {P:K->A->B->Prop}
        {l : list (K * A)} {l' : list (K * B)} :
    (Forall2
       (fun (d : K * A) (r : K * B) =>
          fst d = fst r /\ P (fst d) (snd d) (snd r)) l l') ->
    forall {dec} {s:K} {d':B},
      lookup dec l' s = Some d' -> 
      (exists d'', lookup dec l s = Some d'' /\ P s d'' d').
  Proof.
    intros H.
    induction H; intros; simpl in *.
    - discriminate.
    - destruct x; destruct y; simpl in *.
      destruct H; subst.
      destruct (dec s k0).
      + invcs H1; eauto.
      + destruct (IHForall2 _ _ _ H1) as [?[??]].
        eauto.
  Qed.
  Lemma lookup_map_same_domain {A B C:Type} dec
        (f:(A*B)->(A*C)) l v :
    domain l = domain (map f l) ->
    lookup dec (map f l) v = lift (fun x => snd (f (v,x))) (lookup dec l v).
  Proof.
    induction l; simpl; trivial.
    destruct a; intros eqq; invcs eqq.
    rewrite <- H0.
    rewrite IHl; trivial.
    case_eq (f (a,b)); intros.
    rewrite H in H0; simpl in H0; subst.
    destruct (dec v a0); simpl; trivial.
    - subst. rewrite H; simpl; trivial.
  Qed.

  Lemma lookup_map_codomain {A B C:Type} dec (f:B->C) (l:list (A*B)) v :
    lookup dec (map_codomain f l) v = lift f (lookup dec l v).
  Proof.
    apply lookup_map_same_domain; simpl.
    unfold domain; rewrite map_map.
    simpl.
    apply map_ext; trivial.
  Qed.

  Lemma domain_map_codomain {A B C} (f:B->C) (l:list (A*B)) :
    domain (map_codomain f l) = domain l.
  Proof.
    unfold domain, map_codomain.
    rewrite map_map; simpl.
    rewrite map_eta_fst_domain; trivial.
  Qed.

  
  Lemma cut_down_to_incl_to
        {A B} {dec:EqDec A eq}
        (l:list (A*B)) l2 :
    incl (domain (cut_down_to l l2)) l2.
  Proof.
    red; intros.
    apply in_domain_in in H.
    destruct H as [? inn].
    apply cut_down_to_in in inn.
    simpl in inn; intuition.
  Qed.

  Lemma incl_domain_cut_down_incl
        {A B} {dec:EqDec A eq}
        (l:list (A*B)) l2 :
    incl l2 (domain l) ->
    incl l2 (domain (cut_down_to l l2)).
  Proof.
    unfold incl; intros.
    specialize (H _ H0).
    apply in_domain_in in H. destruct H as [? inn].
    eapply in_dom.
    apply cut_down_to_in; simpl.
    eauto.
  Qed.

  Lemma cut_down_to_lookup_some
        {A B} {dec:EqDec A eq}
        (l:list (A*B)) l2 a y :
    lookup dec (cut_down_to l l2) a = Some y -> 
    lookup dec l a = Some y /\ In a l2 .
  Proof.
    unfold cut_down_to.
    induction l; simpl; try discriminate.
    destruct a0; intros.
    case_eq (existsb (fun z : A => fst (a0, b) ==b z) l2); intros eqq1
    ; rewrite eqq1 in H.
    - apply existsb_exists in eqq1.
      destruct eqq1 as [? [??]].
      simpl in *.
      unfold equiv_decb in H1.
      match_destr_in H1.
      red in e; subst.
      match_destr.
      + invcs H.
        red in e; subst; tauto.
      + auto.
    - destruct (IHl H).
      rewrite H0.
      match_destr; try tauto.
      rewrite existsb_not_forallb, negb_false_iff, forallb_forall in eqq1.
      red in e; subst.
      specialize (eqq1 _ H1).
      simpl in eqq1.
      unfold equiv_decb in eqq1.
      match_destr_in eqq1.
      red in c; congruence.
  Qed.

  Lemma cut_down_to_lookup_in
        {A B} {dec:EqDec A eq}
        (l:list (A*B)) l2 a  :
    In a l2 ->
    lookup dec (cut_down_to l l2) a = lookup dec l a.
  Proof.
    intros inn.
    induction l; simpl; trivial.
    destruct a0; simpl.
    case_eq (existsb (fun z : A =>a0 ==b z) l2); intros eqq1; simpl; rewrite IHl; trivial.
    rewrite existsb_not_forallb, negb_false_iff, forallb_forall in eqq1.
    specialize (eqq1 _ inn).
    unfold equiv_decb in eqq1.
    match_destr_in eqq1.
    destruct (dec a a0); congruence.
  Qed.

  Global Instance domain_incl_proper A B : Proper (@incl (A*B) ==> @incl A) (@domain A B).
  Proof.
    unfold Proper, respectful, incl; intros.
    apply in_domain_in in H0.
    destruct H0.
    specialize (H _ H0).
    eapply in_dom; eauto.
  Qed.

  Lemma cut_down_to_incl
        {A B} {dec:EqDec A eq}
        (l:list (A*B)) (l2:list A) :
    incl (cut_down_to l l2) l.
  Proof.
    unfold incl; intros ? inn.
    apply cut_down_to_in in inn; tauto.
  Qed.
  
  (* note: right-rec so that new fields hide old fields *)
  Fixpoint assoc_lookupr {A B:Type} {P Q:A->A->Prop} (eqd:forall a a':A, {P a a'} + {Q a a'}) (l:list (A*B)) (a:A) : option B
    := match l with
       | nil => None
       | cons (a',d) r2 =>
         match assoc_lookupr eqd r2 a with
         | Some d' => Some d'
         | None =>
           if eqd a a'
           then Some d
           else None
         end
       end.
  
  (* note: right-rec so that new fields hide old fields *)
  Fixpoint projectr {A B:Type} {P Q:A->A->Prop} (eqd:forall a a':A, {P a a'} + {Q a a'}) (l:list (A*B)) (ats:list A) : list (option (A*B)) :=
    match ats with
    | nil => nil
    | cons a ats' =>
      match assoc_lookupr eqd l a with
      | Some d => (Some (a,d)) :: (projectr eqd l ats')
      | None => None :: (projectr eqd l ats')
      end
    end.

  Lemma assoc_lookupr_app {A B:Type} (l1 l2:list (A*B)) x (dec:forall x y, {x=y} + {x <> y}) :
    assoc_lookupr dec (l1++l2) x = 
    match assoc_lookupr dec l2 x with
    | Some y => Some y
    | None => assoc_lookupr dec l1 x
    end.
  Proof.
    revert l2 x. induction l1; simpl; intros.
    - destruct (assoc_lookupr dec l2 x); trivial.
    - destruct a. rewrite IHl1.
      destruct (assoc_lookupr dec l2 x); trivial.
  Qed.

  Lemma assoc_lookupr_lookup
        {A B} dec x (ls:list (A*B)):
    assoc_lookupr dec ls x = lookup dec (rev ls) x.
  Proof.
    induction ls; simpl; trivial.
    destruct a.
    rewrite IHls.
    rewrite lookup_app; simpl.
    trivial.
  Qed.
  
  Lemma lookup_assoc_lookupr
        {A B} dec x (ls:list (A*B)):
    lookup dec ls x = assoc_lookupr dec (rev ls) x.
  Proof.
    rewrite assoc_lookupr_lookup.
    rewrite rev_involutive.
    trivial.
  Qed.

  (* TODO: this should just replace in_dom_lookupr *)      
  Lemma in_dom_lookupr_strong {A B:Type} (l:list (A*B)) a (dec:forall x y, {x=y} + {x <> y}) :
    In a (domain l) -> {v|assoc_lookupr dec l a = Some v}.
  Proof.
    intros. induction l; simpl in *; [tauto|].
    destruct a0.
    simpl in *.
    case_eq (assoc_lookupr dec l a); simpl; [eauto|].
    destruct (dec a a0); simpl; [eauto|].
    intros ln; elim n.
    intuition.
    destruct X; congruence.
  Qed.

  Lemma in_dom_lookupr {A B:Type} (l:list (A*B)) a (dec:forall x y, {x=y} + {x <> y}) :
    In a (domain l) -> exists v, assoc_lookupr dec l a = Some v.
  Proof.
    intros ind.
    destruct (in_dom_lookupr_strong _ _ dec ind); eauto.
  Qed.

  Lemma assoc_lookupr_in  {A B:Type} (l :list (A*B)) a b (dec:forall x y, {x=y} + {x <> y}) :
    assoc_lookupr dec l a = Some b -> In (a,b) l.
  Proof.
    induction l; simpl; intros; try discriminate.
    destruct a0. destruct (assoc_lookupr dec l a); auto.
    destruct (dec a a0); auto.
    inversion H; subst. auto.
  Qed.

  Lemma  assoc_lookupr_none_nin {A B} 
         (dec : forall x0 y : A, {x0 = y} + {x0 <> y}) {l x} :
    assoc_lookupr dec l x = (@None B) ->  ~ In x (domain l).
  Proof.
    intros.
    intros ind.
    destruct (in_dom_lookupr _ _ dec ind).
    congruence.
  Qed.

  Lemma assoc_lookupr_nodup_perm {A B:Type} (l l':list (A*B)) x (dec:forall x y, {x=y} + {x <> y}) :
    NoDup (domain l) -> Permutation l l' -> assoc_lookupr dec l x = assoc_lookupr dec l' x.
  Proof.
    revert l' x.
    induction l; simpl; intros.
    - apply Permutation_nil in H0; subst; simpl; trivial.
    - destruct a; simpl. 
      assert (inl:In (a,b) l')
        by (apply (Permutation_in _ H0); simpl; intuition).
      destruct (in_split _ _ inl) as [l1 [l2 ?]]; subst.
      rewrite <- Permutation_middle in H0.
      apply Permutation_cons_inv in H0.
      inversion H; subst.
      rewrite (IHl _ _ H4 H0).
      repeat rewrite assoc_lookupr_app. simpl.
      destruct (assoc_lookupr dec l2 x); trivial.
      case_eq (assoc_lookupr dec l1 x);
        destruct (dec x a); trivial.
      subst.
      intros. elim H3.
      apply assoc_lookupr_in in H1.
      apply in_dom in H1.
      eapply Permutation_in; [symmetry; apply Permutation_map; eassumption|].
      rewrite map_app.
      eapply in_or_app. auto.
  Qed.

  Lemma in_split_strong {A:Type} `{EqDec A eq} {x} {l:list A} : In x l -> {l1:list A & {l2:list A | l = l1 ++ x::l2}}.
  Proof.
    induction l; simpl; intuition.
    destruct (equiv_dec a x); unfold equiv, complement in *.
    - rewrite e. exists nil; exists l; reflexivity.
    - destruct (In_dec equiv_dec x l).
      + destruct (IHl i) as [l1 [l2 eql]].
        exists (a::l1); exists l2. rewrite eql.
        reflexivity.
      + assert False; intuition.
  Defined.

  Lemma assoc_lookupr_nin_none {A B:Type} (l:list (A*B)) x (dec:forall x y, {x=y} + {x <> y}) : ~ In x (domain l) -> assoc_lookupr dec l x = None.
  Proof.
    induction l; simpl; intros; auto. 
    destruct a; simpl in *. intuition.
    destruct (assoc_lookupr dec l x); try congruence.
    destruct (dec x a); subst; intuition.
  Qed.

  Lemma in_assoc_lookupr_nodup {A B:Type} (l:list (A*B)) a b (dec:forall x y, {x=y} + {x <> y}):
    NoDup (domain l) -> In (a,b) l -> assoc_lookupr dec l a = Some b.
  Proof.
    intros.
    induction l.
    contradiction.
    simpl in *.
    inversion H; subst.
    specialize (IHl H4).
    destruct a0; simpl in *.
    elim H0; clear H0; intros.
    inversion H0; subst.
    clear H0 H.
    assert (assoc_lookupr dec l a = None).
    apply assoc_lookupr_nin_none; assumption.
    rewrite H.
    destruct (dec a a); congruence.
    rewrite (IHl H0).
    reflexivity.
  Qed.

  Lemma Forall2_lookupr_none {K A B} {P:A->B->Prop} {l : list (K * A)} {l' : list (K * B)} :
    (Forall2
       (fun (d : K * A) (r : K * B) =>
          fst d = fst r /\ P (snd d) (snd r)) l l') ->
    forall {Q1 Q2} {dec s},
      @assoc_lookupr K B Q1 Q2 dec l' s = None -> 
      assoc_lookupr dec l s = None.
  Proof.
    intros.
    induction H; simpl in *.
    reflexivity.
    destruct x; destruct y; simpl in *.
    elim H; intros; clear H.
    rewrite H2 in *; clear H2 H3.
    revert H0 IHForall2.
    elim (assoc_lookupr dec l' s); try congruence.
    elim (dec s k0); intros; try congruence.
    specialize (IHForall2 H0); rewrite IHForall2.
    reflexivity.
  Qed.    

  Lemma Forall2_lookupr_some  {K A B} {P:A->B->Prop} {l : list (K * A)} {l' : list (K * B)} :
    (Forall2
       (fun (d : K * A) (r : K * B) =>
          fst d = fst r /\ P (snd d) (snd r)) l l') ->
    forall {Q1 Q2} {dec} {s:K} {d':B},
      @assoc_lookupr K B Q1 Q2 dec l' s = Some d' -> 
      (exists d'', assoc_lookupr dec l s = Some d'' /\ P d'' d').
  Proof.
    intros.
    induction H; simpl in *.
    - elim H0; intros; congruence.
    - destruct x; destruct y; simpl in *.
      assert ((exists d, assoc_lookupr dec l' s = Some d) \/
              assoc_lookupr dec l' s = None)
        by (destruct (assoc_lookupr dec l' s);
            [left; exists b0; reflexivity|right; reflexivity]).
      elim H2; intros; clear H2.
      elim H3; intros; clear H3.
      revert H0 IHForall2.
      rewrite H2; intros.
      elim (IHForall2 H0); intros; clear IHForall2.
      elim H3; intros; clear H3.
      rewrite H4. exists x0. split;[reflexivity|assumption].
      clear IHForall2; assert (assoc_lookupr dec l s = None)
        by apply (Forall2_lookupr_none H1 H3).
      rewrite H3 in *; rewrite H2 in *; clear H2 H3.
      elim H; intros; clear H.
      rewrite H2 in *; clear H2.
      revert H0; elim (dec s k0); intros.
      + exists a; split; try reflexivity.
        inversion H0; rewrite H2 in *; assumption.
      + congruence.
  Qed.

  Definition permutation_dec {A:Type} `{EqDec A eq} (l l':list A) 
    : {Permutation l l'} + {~Permutation l l'}.
  Proof.
    revert l'. induction l.
    - destruct l'.
      + left; trivial.
      + right. apply Permutation_nil_cons.
    - intros. destruct (In_dec equiv_dec a l').
      + destruct (in_split_strong i) as [l1 [l2 eql]].
        destruct (IHl (l1++l2)).
        * left. subst. apply Permutation_cons_app; trivial.
        * right. intro P. elim n. subst. rewrite <- Permutation_middle in P.
          apply (Permutation_cons_inv P).
      + right. intro P. apply n. eapply (Permutation_in _ P). simpl; intuition.
  Defined.

  Lemma permutation_prover {A:Set} {dec:EqDec A eq}
        (l1 l2:list A)
        (pf:holds (permutation_dec l1 l2)) :
    Permutation l1 l2.
  Proof.
    generalize (permutation_dec l1 l2).
    unfold holds, is_true in *.
    match_destr_in pf.
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

  Lemma domain_length  {A B:Type} (l:list (A*B)) :
    List.length (domain l) = List.length l.
  Proof.
    apply map_length.
  Qed.
  
  Lemma domain_app {A B:Type} (l₁ l₂:list (A*B)) :
    domain (l₁ ++ l₂) = domain l₁ ++ domain l₂.
  Proof.
    unfold domain. rewrite map_app; trivial.
  Qed.

  Lemma codomain_length  {A B:Type} (l:list (A*B)) :
    List.length (codomain l) = List.length l.
  Proof.
    apply map_length.
  Qed.
  
  Lemma codomain_app {A B:Type} (l₁ l₂:list (A*B)) :
    codomain (l₁ ++ l₂) = codomain l₁ ++ codomain l₂.
  Proof.
    unfold codomain. rewrite map_app; trivial.
  Qed.

  Lemma app_inv_head_domain {A B:Type} {l1 l2 l1' l2' : list (A*B)} :
    l1 ++ l2 = l1' ++ l2' ->
    domain l1' = domain l1 ->
    l1 = l1' /\ l2 = l2'.
  Proof.
    intros eqq domeq.
    apply app_inv_head_length in eqq; trivial.
    rewrite <- domain_length.
    unfold domain in *.
    rewrite <- domeq.
    rewrite map_length; trivial.
  Qed.
  
  Section distinctdom.
    (* CLEANUP: could generalize bdistinct to work over an equivalence
   relation and then use the fst projection of an equivalence relation *)
    Fixpoint bdistinct_domain {A B} {R} `{dec:EqDec A R} (l:list (A*B))  :=
      match l with
      | nil => nil
      | x :: l' =>
        let dl' := bdistinct_domain l' in
        if (existsb (fun z => (fst x) ==b (fst z)) dl') then
          dl' else x::dl'
      end.

    Lemma bdistinct_domain_NoDup {A B} {dec:EqDec A eq} (l:list (A*B)) :
      NoDup (domain (bdistinct_domain l)).
    Proof.
      induction l; simpl.
      - constructor.
      - case_eq (existsb (fun z : A * B => fst a ==b fst z) (bdistinct_domain l)).
        + trivial.
        + intros; constructor; trivial.
          rewrite existsb_not_forallb, negb_false_iff, forallb_forall in H.
          intros inn.
          destruct (in_domain_in inn).
          specialize (H _ H0).
          simpl in H.
          unfold equiv_decb in *.
          match_destr_in H. intuition.
    Qed.

    Lemma bdistinct_domain_domain_equiv {A B} {dec:EqDec A eq} (l:list (A*B))  :
      equivlist (domain (bdistinct_domain l)) (domain l).
    Proof.
      induction l; simpl.
      - reflexivity.
      - match_case; intros.
        + rewrite IHl.
          rewrite existsb_exists in H.
          destruct H as [? [??]].
          split; simpl; intuition; subst.
          unfold equiv_decb in H0.
          match_destr_in H0. rewrite e.
          eapply equivlist_in; eauto.
          destruct x.
          eapply in_dom; eauto.
        + rewrite existsb_not_forallb, negb_false_iff, forallb_forall in H.
          rewrite domain_cons. split; simpl; intuition; subst.
          * right; apply (equivlist_in IHl _ H1).
          * generalize (equivlist_in (symmetry IHl) _ H1); eauto.
    Qed.

    Lemma bdistinct_rev_domain_equivlist {A B} {dec:EqDec A eq} (l:list (A*B)) :
      equivlist ((domain l)) (domain (bdistinct_domain (rev l))).
    Proof.
      rewrite bdistinct_domain_domain_equiv.
      rewrite domain_rev.
      rewrite <- (Permutation_rev (domain l)).
      reflexivity.
    Qed.

    Lemma bdistinct_domain_assoc_lookupr {A B} {dec:EqDec A eq} (l:list (A*B)) :
      forall x,
        assoc_lookupr dec (bdistinct_domain l) x
        = assoc_lookupr dec l x.
    Proof.
      induction l; simpl; trivial.
      destruct a; simpl; intros.
      match_case; match_case; simpl; intros; rewrite IHl, H; trivial.
      rewrite existsb_exists in H0.
      destruct H0 as [[??] [?inn eqq]].
      unfold equiv_decb in *; simpl in * .
      match_destr_in eqq.
      match_destr.
      unfold equiv in *.
      subst.
      rewrite <- IHl in H.
      apply assoc_lookupr_none_nin in H.
      apply in_dom in inn.
      intuition.
    Qed.

  End distinctdom.
  
  Section lookup_eq.
    Context {A B:Type}.
    Context {dec:EqDec A eq}.

    Definition lookup_incl (l1 l2:list (A*B)) : Prop
      := forall (x:A) (y:B), lookup dec l1 x = Some y ->
                             lookup dec l2 x = Some y.

    Global Instance lookup_incl_pre : PreOrder lookup_incl.
    Proof.
      unfold lookup_incl.
      constructor; red; intros; intuition.
    Qed.
    
    Definition lookup_equiv (l1 l2:list (A*B)) : Prop
      := forall (x:A), lookup dec l1 x = lookup dec l2 x.

    Global Instance lookup_equiv_equiv : Equivalence lookup_equiv.
    Proof.
      unfold lookup_equiv.
      constructor; red; simpl.
      - reflexivity.
      - eauto.
      - intros.
        etransitivity; eauto.
    Qed.

    Global Instance lookup_incl_equiv : subrelation lookup_equiv lookup_incl.
    Proof.
      repeat red; intros.
      congruence.
    Qed.

    Global Instance lookup_incl_part : PartialOrder lookup_equiv lookup_incl.
    Proof.
      unfold lookup_equiv, lookup_incl.
      intros l1 l2.
      unfold relation_conjunction, predicate_intersection,
      pointwise_extension, Basics.flip.
      split; [split|].
      - congruence.
      - congruence.
      - intros [eqq1 eqq2] x.
        specialize (eqq1 x).
        specialize (eqq2 x).
        destruct (lookup dec l1 x).
        + rewrite (eqq1 _ eq_refl); trivial.
        + destruct (lookup dec l2 x); trivial.
          rewrite (eqq2 _ eq_refl); trivial.
    Qed.

    Lemma lookup_incl_dec_nodup {decb:EqDec B eq} :
      forall x y, NoDup (domain x) -> {lookup_incl x y} + {~ lookup_incl x y}.
    Proof.
      intros x y nd.
      revert nd.
      unfold lookup_incl.
      induction x; simpl; intros.
      - left. intros; try discriminate.
      - destruct a; simpl in *.
        case_eq (lookup dec y a); intros.
        + destruct (decb b b0); unfold equiv in * .
          * { destruct IHx.
              - inversion nd; trivial.
              - left.
                intros ? ? eqq; subst.
                match_destr_in eqq; unfold equiv in * .
                + inversion eqq; clear eqq; subst.
                  auto.
                + auto.
              - right.
                intro inn; apply n.
                intros.
                subst.
                apply (inn x0 y0).
                match_destr.
                red in e; subst.
                apply lookup_in in H0.
                apply in_dom in H0.
                inversion nd; subst.
                intuition.
            }
          * right; intros inn.
            { rewrite (inn a b) in H.
              - inversion H; congruence.
              - match_destr; congruence.
            }
        + right. intro inn.
          rewrite (inn a b) in H.
          * discriminate.
          * match_destr.
            congruence.
    Defined.

    Lemma lookup_incl_dec {decb:EqDec B eq} :
      forall x y, {lookup_incl x y} + {~ lookup_incl x y}.
    Proof.
      intros.
      destruct (lookup_incl_dec_nodup (rev (bdistinct_domain (rev x))) y).
      - rewrite domain_rev.
        rewrite NoDup_rev.
        apply bdistinct_domain_NoDup.
      - left.
        unfold lookup_incl in *; intros.
        apply l.
        rewrite <- assoc_lookupr_lookup.
        rewrite (bdistinct_domain_assoc_lookupr (rev x) x0).
        rewrite lookup_assoc_lookupr in H.
        trivial.
      - right.
        unfold lookup_incl in *.
        intros inn; apply n; clear n; intros.
        apply inn.
        rewrite <- assoc_lookupr_lookup in H.
        rewrite (bdistinct_domain_assoc_lookupr (rev x) x0) in H.
        rewrite lookup_assoc_lookupr.
        trivial.
    Defined.

    Instance lookup_equiv_eqdec {decb:EqDec B eq} :
      EqDec (list (A*B)) lookup_equiv.
    Proof.
      red.
      unfold equiv, complement.
      intros x y.
      destruct (lookup_incl_dec x y).
      - destruct (lookup_incl_dec y x).
        + left.
          apply lookup_incl_part; split; trivial.
        + right.
          intros eqq.
          apply lookup_incl_part in eqq.
          destruct eqq; intuition.
      - right.
        intros eqq.
        apply lookup_incl_part in eqq.
        destruct eqq; intuition.
    Defined.

    Global Instance lookup_equiv_lookup 
      : Proper (lookup_equiv ==> eq ==> eq) (@lookup A B dec).
    Proof.
      intros ??????; subst.
      apply H.
    Qed.

    Lemma lookup_equiv_cons_same  {l1 l2:list (A*B)} :
      lookup_equiv l1 l2 ->
      forall a,
        lookup_equiv (a::l1) (a::l2).
    Proof.
      unfold lookup_equiv; simpl; destruct a; intros.
      match_destr.
    Qed.

    Lemma lookup_equiv_app {l1 l2 l1' l2':list (A*B)} :
      lookup_equiv l1 l1' ->
      lookup_equiv l2 l2' ->
      lookup_equiv (l1++l2) (l1'++l2').
    Proof.
      unfold lookup_equiv; simpl; intros.
      repeat rewrite lookup_app.
      rewrite H, H0; trivial.
    Qed.

    Lemma lookup_equiv_appl_same {l1 l2:list (A*B)} :
      lookup_equiv l1 l2 ->
      forall l,
        lookup_equiv (l++l1) (l++l2).
    Proof.
      intros.
      eapply lookup_equiv_app; trivial.
      reflexivity.
    Qed.

    Lemma lookup_equiv_appr_same {l1 l2:list (A*B)} :
      lookup_equiv l1 l2 ->
      forall l,
        lookup_equiv (l1++l) (l2++l).
    Proof.
      intros.
      eapply lookup_equiv_app; trivial.
      reflexivity.
    Qed.

    Lemma lookup_incl_cons_l_nin (l1 l2:list (A*B)) x y :
      lookup_incl l1 l2 ->
      ~ In x (domain l1) ->
      lookup_incl l1 ((x,y)::l2).
    Proof.
      unfold lookup_incl; simpl; intros.
      match_destr; unfold equiv in *; subst.
      - apply lookup_in in H1.
        apply in_dom in H1.
        intuition.
      - auto.
    Qed.

    Lemma cut_down_to_lookup_incl
          (l:list (A*B)) (l2:list A) :
      lookup_incl (cut_down_to l l2) l.
    Proof.
      unfold cut_down_to, lookup_incl.
      induction l; simpl; trivial; intros x y inn.
      destruct a; simpl in *.
      match_case_in inn
      ; intros eqq1; rewrite eqq1 in inn.
      - simpl in inn.
        match_destr.
        eauto.
      - rewrite (IHl _ _ inn).
        match_destr; unfold Equivalence.equiv, complement in *.
        subst.
        apply lookup_in in inn.
        apply filter_In in inn.
        simpl in inn.
        intuition congruence.
    Qed.

    Lemma lookup_remove_duplicate l v x l' x' l'' :
      lookup_equiv
        (l ++ (v,x)::l' ++ (v,x')::l'')
        (l ++ (v,x)::l' ++ l'').
    Proof.
      red; intros.
      repeat rewrite lookup_app.
      match_destr.
      simpl.
      match_destr.
      repeat rewrite lookup_app.
      match_destr.
      simpl.
      match_destr.
      congruence.
    Qed.

    Lemma lookup_remove_nin l v0 (x:B) l' v :
      v <> v0 ->
      lookup dec (l ++ (v0,x) :: l') v = lookup dec (l ++ l') v.
    Proof.
      intros.
      repeat rewrite lookup_app.
      match_destr.
      simpl.
      match_destr.
      congruence.
    Qed.

    Lemma lookup_swap_neq l1 v1 x1 v2 x2 l2 :
      v1 <> v2 ->
      lookup_equiv
        (l1++(v1,x1)::(v2,x2)::l2) 
        (l1++(v2,x2)::(v1,x1)::l2).
    Proof.
      red; intros.
      repeat rewrite lookup_app.
      match_destr.
      simpl.
      match_destr.
      match_destr.
      congruence.
    Qed.

    Lemma lookup_equiv_perm_nodup {l1 l2} :
      NoDup (domain l1) ->
      Permutation l1 l2 ->
      lookup_equiv l1 l2.
    Proof.
      unfold lookup_equiv; intros.
      case_eq (lookup dec l1 x); intros.
      - apply lookup_in in H1.
        rewrite H0 in H1.
        symmetry.
        apply in_lookup_nodup; trivial.
        rewrite <- H0.
        trivial.
      - symmetry.
        eapply lookup_none_perm in H1; eauto.
    Qed.

    Lemma update_first_NoDup_perm_invs (f g:B->B) {l1 l2} {a:A} {v1 v2:B} :
      NoDup (domain l1) -> 
      Permutation (update_first dec l1 a (f v1)) (update_first dec l2 a (g v2)) ->
      lookup dec l1 a = Some v1 ->
      lookup dec l2 a = Some v2 ->
      (forall x y, f x = g y -> x = y) ->
      Permutation l1 l2 /\ v1 = v2 /\ f v1 = g v2.
    Proof.
      intros nodup perm lo1 lo2 inj.
      assert (perm2: Permutation (domain l1) (domain l2)).
      { erewrite <- (domain_update_first dec l1)
        ; erewrite <- (domain_update_first dec l2).
        apply Permutation_map; eauto.
      }
      destruct (in_update_break dec lo1 (f v1))
        as [m1 [m2 [meqq mueqq]]].
      rewrite mueqq in perm.
      destruct (in_update_break dec lo2 (g v2))
        as [n1 [n2 [neqq nueqq]]].
      rewrite nueqq in perm.
      repeat rewrite <- Permutation_middle in perm.
      rewrite meqq in nodup.
      rewrite <- Permutation_middle in nodup.
      assert (lequiv:lookup_equiv ((a, f v1) :: m1 ++ m2) ((a, g v2) :: n1 ++ n2)).
      { apply lookup_equiv_perm_nodup; trivial. }
      assert (lo:lookup dec ((a, f v1) :: m1 ++ m2) a = Some (f v1)).
      { simpl; match_destr; congruence. }
      rewrite lequiv in lo.
      simpl in lo.
      match_destr_in lo; [| congruence].
      invcs lo.
      symmetry in H0.
      specialize (inj _ _ H0).
      subst.
      split; [ | tauto].
      rewrite H0 in perm.
      apply Permutation_cons_inv in perm.
      repeat rewrite <- Permutation_middle.
      eauto.
    Qed.

    Lemma assoc_lookupr_lookup_nodup x (ls:list (A*B)):
      NoDup (domain ls) ->
      assoc_lookupr dec ls x = lookup dec ls x.
    Proof.
      intros nd.
      rewrite @assoc_lookupr_lookup.
      apply lookup_equiv_perm_nodup; trivial.
      - rewrite domain_rev.
        rewrite <- Permutation_rev; trivial.
      - rewrite <- Permutation_rev. reflexivity.
    Qed.

    Lemma NoDup_lookup_equiv_equivlist (l1 l2:list (A*B)) :
      NoDup (domain l1) ->
      NoDup (domain l2) ->
      lookup_equiv l1 l2 ->
      equivlist l1 l2.
    Proof.
      unfold equivlist, lookup_equiv.
      intros nd1 nd2 loeq.
      intros [a b]; split; intros inn
      ; apply lookup_in with (dec0:=dec)
      ; apply (in_lookup_nodup) with (dec0:=dec) in inn; trivial
      ; congruence.
    Qed.

    Lemma NoDup_lookup_equiv_Permutation (l1 l2:list (A*B)) :
      NoDup (domain l1) ->
      NoDup (domain l2) ->
      lookup_equiv l1 l2 ->
      Permutation l1 l2.
    Proof.
      intros nd1 nd2 le.
      apply NoDup_Permutation';
        try (apply NoDup_domain_NoDup; trivial).
      apply NoDup_lookup_equiv_equivlist; trivial.
    Qed.
    
    Definition assoc_lookupr_equiv 
               (l1 l2:list (A*B))
      := forall x : A, assoc_lookupr dec l1 x = assoc_lookupr dec l2 x.

    Global Instance assoc_lookupr_equiv_equiv : Equivalence (assoc_lookupr_equiv).
    Proof.
      constructor; red; unfold assoc_lookupr_equiv; congruence.
    Qed.

    Global Instance assoc_lookupr_equiv_app:
      Proper (assoc_lookupr_equiv ==> assoc_lookupr_equiv ==> assoc_lookupr_equiv) (@app (A*B)).
    Proof.
      unfold Proper, respectful, assoc_lookupr_equiv; intros.
      rewrite (assoc_lookupr_app x x0).
      rewrite (assoc_lookupr_app y y0).
      rewrite H, H0.
      trivial.
    Qed.

    Lemma assoc_lookupr_equiv_cons_in (s:A) (d:B) l :
      In s (domain l) -> 
      assoc_lookupr_equiv l ((s, d) :: l).
    Proof.
      unfold assoc_lookupr_equiv; intros.
      simpl.
      match_case; intros.
      match_case; intros.
      unfold equiv in *; subst.
      apply assoc_lookupr_none_nin in H0.
      congruence.
    Qed.

  End lookup_eq.

  Lemma remove_domain_filter {A B} `{dec:EqDec A eq} s l:
    remove equiv_dec s (domain l) = 
    domain (filter (fun x : A * B => s <>b fst x) l).
  Proof.
    induction l; simpl; trivial.
    unfold nequiv_decb, equiv_decb.
    rewrite IHl.
    destruct (equiv_dec s (fst a)); simpl; trivial.
  Qed.
  
  Lemma fold_left_remove_all_nil_in_not_inv {B} {x ps l}:
    In x (fold_left
            (fun (h : list nat) (xy : nat * B) =>
               remove_all (fst xy) h)
            ps l) ->
    ~ In x (domain ps).
  Proof.
    revert l.
    induction ps; simpl; intuition; subst.
    - simpl in *.
      apply fold_left_remove_all_nil_in_inv in H.
      rewrite remove_all_filter in H.
      apply filter_In in H. unfold nequiv_decb, equiv_decb in *.
      intuition. match_destr_in H1.
      congruence.
    - eauto.
  Qed.

  Lemma fold_left_remove_all_nil_in {B} {x ps l}:
    In x l ->
    ~ In x (domain ps) ->
    In x (fold_left
            (fun (h : list nat) (xy : nat * B) =>
               remove_all (fst xy) h)
            ps l).
  Proof.
    revert l.
    induction ps using rev_ind; simpl; intuition; subst.
    rewrite fold_left_app; simpl.
    rewrite remove_all_filter.
    rewrite domain_app, in_app_iff in H0.
    simpl in H0.
    apply filter_In. split.
    - apply IHps; intuition.
    - unfold nequiv_decb, equiv_decb.
      match_destr.
      red in e; subst. intuition.
  Qed.

  Definition swap {A B} (xy:A*B) := (snd xy, fst xy).

  Section Swap.
    Lemma swap_idempotent {A B} (a:A*B) : swap (swap a) = a.
    Proof.
      destruct a; unfold swap; simpl; trivial.
    Qed.
    
    Lemma in_swap {A B} x (l:list (A*B)):
      In x (map swap l) <-> In (swap x) l.
    Proof.
      rewrite in_map_iff. split.
      - destruct 1 as [? [??]]; subst.
        rewrite swap_idempotent; trivial.
      - intros. econstructor; split; try eassumption.
        rewrite swap_idempotent; trivial.
    Qed.

    Lemma in_swap_in {A B} x (l:list (A*B)):
      In (swap x) (map swap l) <-> In x l.
    Proof.
      rewrite in_swap, swap_idempotent; intuition.
    Qed.
    
  End Swap.

  Section Lookup_diff.

    (* should really be replaced by a filter *)
    Fixpoint lookup_diff {A B C:Type} (dec:forall a a':A, {a=a'} + {a<>a'}) (l₁:list (A*B)) (l₂:list (A*C)) :=
      match l₁ with
      | nil => nil
      | x::xs => match lookup dec l₂ (fst x) with
                 | None => x::lookup_diff dec xs l₂
                 | Some _ => lookup_diff dec xs l₂
                 end
      end.

    Lemma lookup_diff_none1  {A B C:Type} (dec:forall a a':A, {a=a'} + {a<>a'}) {l₁:list(A*B)} (l₂:list (A*C)) {x} :
      lookup dec l₁ x = None ->
      lookup dec (lookup_diff dec l₁ l₂) x = None.
    Proof.
      revert x.
      induction l₁; simpl; trivial.
      destruct a; simpl; intros.
      case_eq (dec x a); intuition; subst; rewrite H0 in H; try discriminate.
      case_eq (lookup dec l₂ a); simpl; intuition.
      rewrite H0. auto.
    Qed.

    Lemma lookup_diff_none2  {A B C:Type} (dec:forall a a':A, {a=a'} + {a<>a'}) (l₁:list (A*B)) {l₂:list (A*C)} {x} :
      lookup dec l₂ x = None ->
      lookup dec (lookup_diff dec l₁ l₂) x = lookup dec l₁ x.
    Proof.
      revert x.
      induction l₁; simpl; trivial.
      destruct a; simpl; intuition.
      destruct (dec x a); subst.
      - rewrite H; simpl.
        destruct (dec a a); intuition.
      - generalize (IHl₁ a). destruct (lookup dec l₂ a); intuition.
        simpl. destruct (dec x a); intuition.
    Qed.

    Lemma lookup_diff_some2  {A B C:Type} (dec:forall a a':A, {a=a'} + {a<>a'}) (l₁:list(A*B)) {l₂:list (A*C)} {x t} :
      lookup dec l₂ x = Some t ->
      lookup dec (lookup_diff dec l₁ l₂) x = None.
    Proof.
      induction l₁; simpl; intuition.
      simpl.
      case_eq (lookup dec l₂ a0); intuition.
      simpl.
      destruct (dec x a0); subst; intuition.
      rewrite H in H1. discriminate.
    Qed.

    Lemma lookup_diff_inv {A B C} (dec:forall a a':A, {a=a'} + {a<>a'})
          x (l1:list (A*B)) (l2:list (A*C)):
      In x (lookup_diff dec l1 l2) ->
      In x l1 /\ ~ In (fst x) (domain l2).
    Proof.
      revert l2.
      induction l1; simpl; intros.
      - intuition.
      - match_case_in H; intros; rewrite H0 in H.
        + specialize (IHl1 _ H). intuition.
        + simpl in H. destruct H; subst.
          * intuition.
            apply lookup_none_nin in H0.
            destruct x.
            simpl in *. intuition.
          * specialize (IHl1 _ H). intuition.
    Qed.

    Lemma lookup_diff_nilr {A B C:Type}
          (dec:forall a a':A, {a=a'} + {a<>a'})
          (l₁:list (A*B)) :
      (lookup_diff dec l₁ (@nil (A*C))) = l₁.
    Proof.
      induction l₁; simpl; congruence.
    Qed.

    Lemma NoDup_lookup_diff {A B:Type} (dec:forall a a':A, {a=a'} + {a<>a'}) 
          {r₁ r₂:list (A*B)} :
      NoDup (domain r₁) -> NoDup (domain (lookup_diff dec r₁ r₂)).
    Proof.
      induction r₁; simpl; trivial.
      inversion 1; subst.
      destruct a; simpl in *.
      apply (lookup_nin_none dec) in H2.
      destruct (lookup dec r₂ a); intuition.
      simpl; constructor; auto.
      generalize (lookup_diff_none1 dec r₂ H2); intros nin.
      apply lookup_none_nin in nin; auto.
    Qed.

    Lemma lookup_diff_domain_bounded {A B C} dec l₁ l₂ :
      incl (domain l₁) (domain l₂) ->
      @lookup_diff A B C dec l₁ l₂ = nil.
    Proof.
      unfold incl.
      intros.
      induction l₁; simpl; trivial.
      match_case.
      - rewrite IHl₁; trivial.
        simpl in *; intuition.
      -  intros lo.
         apply lookup_none_nin in lo.
         specialize (H (fst a)); simpl in H.
         cut_to H; [ | intuition ].
         intuition.
    Qed.

    Lemma lookup_diff_bounded {A B} dec l₁ l₂ :
      incl l₁ l₂ ->
      @lookup_diff A B B dec l₁ l₂ = nil.
    Proof.
      intros.
      apply lookup_diff_domain_bounded.
      apply domain_incl_proper; trivial.
    Qed.

    Lemma lookup_diff_same_domain2 {A B C D} dec (l1:list (A*B)) (l2:list (A*C))  (l3:list (A*D)) :
      equivlist (domain l2) (domain l3) ->
      lookup_diff dec l1 l2 = lookup_diff dec l1 l3.
    Proof.
      intros eqq.
      induction l1; simpl; trivial.
      rewrite IHl1.
      specialize (eqq (fst a)).
      match_case; intros.
      - apply lookup_in in H.
        apply in_dom in H.
        destruct eqq as [eqq _].
        specialize (eqq H).
        apply (in_dom_lookup dec) in eqq.
        destruct eqq as [? eqq1].
        rewrite eqq1.
        trivial.
      - apply lookup_none_nin in H.
        match_case; intros.
        apply lookup_in in H0.
        apply in_dom in H0.
        destruct eqq as [_ eqq].
        specialize (eqq H0).
        intuition.
    Qed.

    Lemma map_lookup_diff {A B C} dec (f:A*B->A*C) (l1:list (A*B)) (l2:list (A*C)):
      (forall a, fst a = fst (f a)) ->
      map f (lookup_diff dec l1 l2) = lookup_diff dec (map f l1) l2.
    Proof.
      intros preserves.
      induction l1; simpl; trivial.
      rewrite <- preserves.
      match_destr.
      simpl; rewrite IHl1; trivial.
    Qed.

    Lemma lookup_diff_disjoint
          {A B:Type}
          (dec:forall a a':A, {a=a'} + {a<>a'})
          (l₁ l₂:list (A*B)) : 
      disjoint (domain (lookup_diff dec l₁ l₂)) (domain l₂).
    Proof.
      red; intros.
      apply (in_dom_lookup dec) in H; destruct H.
      apply (in_dom_lookup dec) in H0; destruct H0.
      rewrite (lookup_diff_some2 dec l₁ H0) in H.
      congruence.
    Qed.
    
  End Lookup_diff.

  Section Lookup_equiv_on.

    Definition lookup_equiv_on {A B} {dec:EqDec A eq}
               (dom:list A) (l1 l2:list (A*B))
      := forall x, In x dom -> lookup dec l1 x = lookup dec l2 x.
    
    Lemma cut_down_to_lookup_equiv_on {A B} {dec:EqDec A eq}
          (l:list (A*B)) l2 :
      lookup_equiv_on l2 (cut_down_to l l2) l.
    Proof.
      red.
      apply cut_down_to_lookup_in.
    Qed.
    
    Lemma lookup_equiv_on_is_cut_down_equiv  {A B} {dec:EqDec A eq}
          (dom:list A) (l1 l2:list (A*B))
      : lookup_equiv_on dom l1 l2
        <->
        lookup_equiv (cut_down_to l1 dom) (cut_down_to l2 dom).
    Proof.
      unfold lookup_equiv, lookup_equiv_on; split; intros.
      -  case_eq (lookup dec (cut_down_to l2 dom) x).
         + intros ? xlo.
           apply cut_down_to_lookup_some in xlo.
           destruct xlo as [xloeq inx].
           rewrite <- H in xloeq by trivial.
           rewrite cut_down_to_lookup_in; trivial.
         + case_eq (lookup dec (cut_down_to l1 dom) x); trivial.
           intros ? xlo1 xlo2.
           apply cut_down_to_lookup_some in xlo1.
           destruct xlo1 as [xloeq inx].
           rewrite H in xloeq by trivial.
           rewrite cut_down_to_lookup_in in xlo2 by trivial.
           congruence.
      - specialize (H x).
        repeat rewrite cut_down_to_lookup_in in H by trivial.
        trivial.
    Qed.

    Global Instance lookup_equiv_on_equiv {A B} {dec:EqDec A eq} l
      : Equivalence (@lookup_equiv_on A B dec l).
    Proof.
      apply (Equivalence_by_iff _ _ (lookup_equiv_on_is_cut_down_equiv l)).
      apply Equivalence_pullback.
      apply lookup_equiv_equiv.
    Qed.

    Lemma lookup_equiv_on_lookup_equiv {A B : Type} (dec : EqDec A eq)
          (l1 l2 : list (A * B)) :
      lookup_equiv l1 l2 <-> (forall dom, lookup_equiv_on dom l1 l2).
    Proof.
      unfold lookup_equiv, lookup_equiv_on.
      split; intros.
      - intuition.
      - apply (H (x::nil)); simpl; eauto.
    Qed.

    Lemma lookup_equiv_on_dom_incl  {A B} {dec:EqDec A eq}
          (dom1 dom2:list A) (l1 l2:list (A*B))
      : incl dom2 dom1 ->
        lookup_equiv_on dom1 l1 l2 ->
        lookup_equiv_on dom2 l1 l2.
    Proof.
      unfold lookup_equiv_on; intuition.
    Qed.

    Lemma lookup_equiv_on_dom_app_f  {A B} {dec:EqDec A eq}
          {dom1 dom2:list A} {l1 l2:list (A*B)}
      : lookup_equiv_on dom1 l1 l2 ->
        lookup_equiv_on dom2 l1 l2 -> 
        lookup_equiv_on (dom1++dom2) l1 l2.
    Proof.
      unfold lookup_equiv_on; intros.
      rewrite in_app_iff in *; intuition.
    Qed.
    
    Lemma lookup_equiv_on_dom_app  {A B} {dec:EqDec A eq}
          (dom1 dom2:list A) (l1 l2:list (A*B))
      : lookup_equiv_on (dom1++dom2) l1 l2 ->
        lookup_equiv_on dom1 l1 l2 
        /\ lookup_equiv_on dom2 l1 l2.
    Proof.
      unfold lookup_equiv_on; intuition.
    Qed.

    Lemma lookup_equiv_on_cons_same {A B} {dec:EqDec A eq} {l} {l1 l2:list (A*B)} :
      lookup_equiv_on l l1 l2 ->
      forall a,
        lookup_equiv_on l (a::l1) (a::l2).
    Proof.
      unfold lookup_equiv_on; simpl; destruct a; intros.
      match_destr; eauto.
    Qed.

    Global Instance lookup_equiv_on_incl_prop {A B} {dec:EqDec A eq} :
      Proper ((@incl A) --> eq ==> eq ==> Basics.impl) (@lookup_equiv_on A B dec).
    Proof.
      intros ??????????; subst.
      eapply lookup_equiv_on_dom_incl; eauto.
    Qed.

    Lemma lookup_equiv_on_update_first {A B} {dec:EqDec A eq} fvs (l₁ l₂:list (A*B)) v d :
      lookup_equiv_on fvs l₁ l₂ ->
      lookup_equiv_on fvs (update_first equiv_dec l₁ v d)
                      (update_first equiv_dec l₂ v d).
    Proof.
      unfold lookup_equiv_on; intros.
      specialize (H _ H0).
      destruct (x == v); unfold equiv, complement in *.
      - subst.
        case_eq ( lookup dec l₁ v); intros.
        + repeat rewrite lookup_update_eq_in; trivial.
          * rewrite H in H1; eapply lookup_in_domain; eauto.
          * eapply lookup_in_domain; eauto.
        + unfold equiv_dec in *
          ; repeat rewrite nin_update; congruence.
      - repeat rewrite lookup_update_neq by congruence.
        trivial.
    Qed.

  End Lookup_equiv_on.

  Section alldisjoint.
    
    Lemma all_disjoint_domain_has_same_eq {A B} {ls:list (list (A*B))} :
      all_disjoint (map domain ls) ->
      forall l1 l2,
        In l1 ls ->
        In l2 ls ->
        forall x,
          In x (domain l1) -> In x (domain l2) -> l1 = l2.
    Proof.
      induction ls; simpl; try contradiction.
      intros ad l1 l2 inn1 inn2 x innx1 innx2.
      invcs ad.
      specialize (IHls H2).
      rewrite Forall_forall in H1.
      destruct inn1 as [? | inn1]; destruct inn2 as [? | inn2]; subst.
      - trivial.
      - eelim (H1 (domain l2)); try eassumption.
        apply in_map; trivial.
      - eelim (H1 (domain l1)); try eassumption.
        apply in_map; trivial.
      - eauto.
    Qed.

  End alldisjoint.

  Section concat.

    Lemma concat_lookup_some_break {A B:Type} {dec:EqDec A eq} {ls:list (list (A*B))} {x:A} {v:B} :
      lookup dec (List.concat ls) x = Some v ->
      exists ll1 ll ll2, ls = ll1++ll::ll2
                         /\ lookup dec ll x = Some v
                         /\ ~ In x (domain (concat ll1)).
    Proof.
      intros lo.
      induction ls; simpl in *; try discriminate.
      rewrite lookup_app in lo.
      match_option_in lo.
      - invcs lo.
        exists nil, a, ls; simpl; eauto.
      - destruct (IHls lo) as [ll1[ll [ll2 [? [inn nin]]]]]; subst.
        exists (a::ll1), ll, ll2; simpl.
        repeat split; trivial.
        rewrite domain_app, in_app_iff.
        intros [inn2|inn2].
        + apply lookup_none_nin in eqq.
          contradiction.
        + contradiction.
    Qed.

  End concat.

  Section Substlist.
    
    (* Java equivalent: MROptimizer.substlist_subst *)
    Definition substlist_subst {A} {dec:EqDec A eq}
               (substlist:list (A*A)) (inp:A)
      := match lookup equiv_dec substlist inp with
         | Some x => x
         | None => inp
         end.
    
  End Substlist.

  Section Conv.
    Import ListNotations.
    
    Definition ascii_mk_lower_substtable
      := [("A", "a");("B", "b");("C", "c");("D", "d");("E", "e")
          ;("F", "f");("G", "g");("H", "h");("I", "i");("J", "j")
          ;("K", "k");("L", "l");("M", "m");("N", "n");("O", "o")
          ;("P", "p");("Q", "q");("R", "r");("S", "s");("T", "t")
          ;("U", "u");("V", "v");("W", "w");("X", "x");("Y", "y")
          ;("Z", "z")]%char.

    Definition ascii_mk_lower (c:ascii) : ascii
      := substlist_subst ascii_mk_lower_substtable c.

    Definition mk_lower (s:string) : string
      := map_string ascii_mk_lower s.

  End Conv.
  
End Assoc.

