Require Import Classical.
Require Import ClassicalChoice.
Require Import FinFun.

Require Import List Permutation.
Require Import Morphisms EquivDec Program.

Require Import Utils DVector.
Require Export Event.
Require Import Lia.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

Local Open Scope prob.

Lemma pre_event_complement_swap_classic {T} (A B:pre_event T) : pre_event_complement A === B <-> A === pre_event_complement B.
Proof.
  intros.
  apply pre_event_complement_swap
  ; red; intros; apply classic.
Qed.

Lemma event_complement_swap_classic {T} (σ:SigmaAlgebra T) (A B:event σ) : ¬ A === B <-> A === ¬ B.
Proof.
  intros.
  apply event_complement_swap; auto using sa_dec.
Qed.

Program Instance trivial_sa (T:Type) : SigmaAlgebra T
  := {
      sa_sigma (f:pre_event T) := (f === pre_event_none \/ f === pre_Ω)
    }.
Next Obligation.
  (* sigh. more classical reasoning needed *)
  destruct (classic (exists n, collection n === pre_Ω))
  ; [right|left]; firstorder.
Qed.
Next Obligation.
  firstorder.
Qed.
Next Obligation.
  firstorder.
Qed.

Lemma trivial_sa_sub {T} (sa:SigmaAlgebra T) : 
  sa_sub (trivial_sa T) sa.
Proof.
  intros ?[?|?].
  - rewrite H.
    apply sa_none.
  - rewrite H.
    apply sa_all.
Qed.

Program Instance discrete_sa (T:Type) : SigmaAlgebra T
  := {
      sa_sigma := fun _ => True 
    }.
                 
Program Instance subset_sa (T:Type) (A:pre_event T) : SigmaAlgebra T
  := {
      sa_sigma f := (f === pre_event_none \/ f === A \/ f === ¬ A \/ f === pre_Ω)
    }.
Next Obligation.
  (* sigh. more classical reasoning needed *)
  destruct (classic (exists n, collection n === pre_Ω))
  ; [repeat right; firstorder | ].
  destruct (classic (exists n, collection n === A))
  ; destruct (classic (exists n, collection n === pre_event_complement A)).
  + right; right; right.
    unfold union_of_collection, equiv, event_equiv; intros x.
    split; [firstorder | ].
    destruct (classic (A x)).
    * destruct H1 as [n1 H1].
      exists n1.
      apply H1; trivial.
    * destruct H2 as [n2 H2].
      exists n2.
      apply H2; trivial.
  + right; left.
    unfold union_of_collection, equiv, event_equiv; intros x.
    split.
    * intros [n cn].
      specialize (H n).
      destruct H as [eqq|[eqq|[eqq|eqq]]]
      ; apply eqq in cn
      ; firstorder.
    * intros ax.
      destruct H1 as [n1 H1].
      exists n1.
      apply H1; trivial.
  + right; right. left.
    unfold union_of_collection, equiv, event_equiv; intros x.
    split.
    * intros [n cn].
      specialize (H n).
      destruct H as [eqq|[eqq|[eqq|eqq]]]
      ; apply eqq in cn
      ; firstorder.
    * intros ax.
      destruct H2 as [n2 H2].
      exists n2.
      apply H2; trivial.
  + left.
    split; [| firstorder].
    intros [n cn].
    destruct (H n) as [eqq|[eqq|[eqq|eqq]]]
    ; apply eqq in cn
    ; firstorder.
Qed.
Next Obligation.
  replace pre_event_equiv with (@equiv (pre_event T) _ pre_event_equiv_equiv) in * |- * by reflexivity.
  repeat rewrite pre_event_complement_swap_classic.
  rewrite pre_event_not_not by auto using sa_pre_dec.
  rewrite pre_event_not_none, pre_event_not_all.
  tauto.
Qed.
Next Obligation.
  repeat right.
  reflexivity.
Qed.

Definition is_pre_partition {T}(part:nat->pre_event T)
  := pre_collection_is_pairwise_disjoint part 
     /\ pre_union_of_collection part === pre_Ω.

Definition pre_sub_partition {T} (part1 part2 : nat -> pre_event T)
  := forall n, part1 n === part2 n \/ part1 n === pre_event_none.

Instance pre_sub_partition_pre {T} : PreOrder (@pre_sub_partition T).
Proof.
  constructor; red; unfold pre_sub_partition; intuition eauto.
  - left; reflexivity.
  - specialize (H n).
    specialize (H0 n).
    intuition.
    + rewrite H1.
      tauto.
    + rewrite H1.
      tauto.
Qed.

Definition pre_in_partition_union {T} (part:nat->pre_event T) (f:pre_event T) : Prop
  := exists subpart, pre_sub_partition subpart part /\ (pre_union_of_collection subpart) === f.

Instance pre_in_partition_union_proper {T} (part:nat->pre_event T) :
  Proper (pre_event_equiv ==> iff) (pre_in_partition_union part).
Proof.
  cut (Proper (pre_event_equiv ==> Basics.impl) (pre_in_partition_union part))
  ; unfold pre_in_partition_union, Basics.impl.
  { intros HH x y xyeq.
    intuition eauto.
    symmetry in xyeq.
    intuition eauto.
  }
  intros x y xyeq [sub [sp uc]].
  rewrite xyeq in uc.
  eauto.
Qed.

Lemma pre_sub_partition_diff {T} (sub part:nat->pre_event T) :
  pre_sub_partition sub part ->
  pre_sub_partition (fun x : nat => pre_event_diff (part x) (sub x)) part.
Proof.
  intros is_sub n.
  specialize (is_sub n).
  destruct is_sub as [eqq|eqq]
  ; rewrite eqq.
  - rewrite pre_event_diff_self; intuition.
  - rewrite pre_event_diff_false_r; intuition.
Qed.

Program Instance countable_partition_sa {T} (part:nat->pre_event T) (is_part:is_pre_partition part) : SigmaAlgebra T
  := {
      sa_sigma := pre_in_partition_union part
    }.
Next Obligation.
    unfold pre_in_partition_union in *.
    unfold is_pre_partition in *.
    apply choice in H.
    destruct H as [partish pH].
    exists (fun n => pre_union_of_collection (fun x => partish x n)).
    split.
    + intros n.
      unfold pre_union_of_collection.

      unfold pre_union_of_collection in *.
      unfold is_partition in is_part.
      destruct (classic ((fun t : T => exists n0 : nat, partish n0 n t) === pre_event_none)); [eauto | ].
      left.
      apply not_all_ex_not in H.
      destruct H as [nn Hnn].
      unfold event_none in Hnn.
      assert (HH':~ ~ (exists n0 : nat, partish n0 n nn)) by intuition.
      apply NNPP in HH'.
      destruct HH' as [nn2 pnn2].
      destruct (pH nn2) as [HH1 HH2].
      red in HH1.
      intros x.
      split.
      * intros [nn3 pnn3].
        destruct (pH nn3) as [HH31 HH32].
        red in HH31.
        destruct (HH31 n); apply H in pnn3; trivial.
        vm_compute in pnn3; intuition.
      * intros pnnn.
        specialize (HH1 n).
        destruct HH1 as [eqq|eqq]; [ | apply eqq in pnn2; vm_compute in pnn2; intuition ].
        apply eqq in pnnn.
        eauto.
    + intros x; unfold pre_union_of_collection in *.
      split.
      * intros [n1 [n2 pnn]].
        exists n2.
        apply pH.
        eauto.
      * intros [n cn].
        apply pH in cn.
        destruct cn.
        eauto.
Qed.
Next Obligation.
  destruct is_part as [disj tot].
  destruct H as [sub [is_sub uc2]].
  rewrite <- uc2.
  exists (fun x => pre_event_diff (part x) (sub x)).
  split.
  + apply pre_sub_partition_diff; trivial.
  + intros x.
    unfold pre_union_of_collection, pre_event_complement, pre_event_diff.
    { split.
      -
        intros [n [part1 sub1]].
        intros [nn sub2].
        destruct (n == nn); unfold equiv, complement in *.
        + subst; tauto.
        + specialize (disj _ _ c x part1).
          destruct (is_sub nn); [ | firstorder].
          apply H in sub2.
          tauto.
      - intros.
        unfold pre_union_of_collection in tot.
        assert (xin:pre_Ω x) by firstorder.
        apply tot in xin.
        destruct xin as [n partn].
        exists n.
        split; trivial.
        intros subx.
        eauto.
    }
Qed.
Next Obligation.
  exists part.
  destruct is_part as [disj tot].
  rewrite tot.
  split; reflexivity.
Qed.

Program Instance sigma_algebra_intersection {T} (coll:SigmaAlgebra T->Prop): SigmaAlgebra T
  := { sa_sigma := fun e => forall sa, coll sa -> sa_sigma sa e
     }.
Next Obligation.
  apply sa_countable_union.
  auto.
Defined.
Next Obligation.
  eauto with prob.
Defined.
Next Obligation.
  eauto with prob.
Qed.

Lemma sigma_algebra_intersection_sub {T} (coll:SigmaAlgebra T->Prop)
  : forall s, coll s -> sa_sub (sigma_algebra_intersection coll) s.
Proof.
  unfold sa_sub, event_sub.
  simpl; intros.
  red; simpl
  ; eauto.
Qed.

Definition all_included {T} (F:pre_event T -> Prop) : SigmaAlgebra T -> Prop
  := fun sa => forall (e:pre_event T), F e -> sa_sigma sa e.

Global Instance all_included_proper {T} : Proper (equiv ==> equiv) (@all_included T).
Proof.
  repeat red; unfold equiv, event_equiv, all_included; intros.
  split; intros HH; intros; apply HH; firstorder.
Qed.

Instance generated_sa {T} (F:pre_event T -> Prop) : SigmaAlgebra T
  := sigma_algebra_intersection (all_included F).

Lemma generated_sa_sub {T} (F:pre_event T -> Prop) :
  forall x, F x -> sa_sigma (generated_sa F) x.
Proof.
  unfold sa_sigma, generated_sa, sigma_algebra_intersection, all_included.
  eauto.
Qed.

Lemma generated_sa_sub' {T} (F:pre_event T -> Prop) :
  pre_event_sub F (sa_sigma (generated_sa F)).
Proof.
  firstorder.
Qed.

Lemma generated_sa_minimal {T} (F:pre_event T -> Prop) (sa':SigmaAlgebra T) :
  (forall x, F x -> sa_sigma sa' x) ->
  (forall x, sa_sigma (generated_sa F) x -> sa_sigma sa' x).
Proof.
  intros ff x sax.
  unfold sa_sigma, generated_sa, sigma_algebra_intersection, all_included in sax.
  eauto.
Qed.

Inductive prob_space_closure {T} : (pre_event T->Prop) -> pre_event T -> Prop
  :=
  | psc_all p : prob_space_closure p pre_Ω
  | psc_refl (p:pre_event T->Prop) q : p q -> prob_space_closure p q
  | psc_countable p (collection: nat -> pre_event T) :
      (forall n, prob_space_closure p (collection n)) ->
      prob_space_closure p (pre_union_of_collection collection)
  | psc_complement p q : prob_space_closure p q -> prob_space_closure p (pre_event_complement q)
.

Program Instance closure_sigma_algebra {T} (F:pre_event T -> Prop) : SigmaAlgebra T
  := { sa_sigma := prob_space_closure F }.
Next Obligation.
  now apply psc_countable.
Qed.
Next Obligation.
  now apply psc_complement.
Qed.
Next Obligation.
  now apply psc_all.
Qed.

Theorem generated_sa_closure {T} (F:pre_event T -> Prop) : generated_sa F === closure_sigma_algebra F.
Proof.
  unfold equiv, sa_equiv; simpl.
  split; intros.
  - apply (generated_sa_minimal F (closure_sigma_algebra F)); trivial.
    simpl; intros.
    now apply psc_refl.
  - induction H.
    + apply sa_all.
    + eauto.
    + apply sa_countable_union; eauto.
    + apply sa_complement; eauto.
Qed.

Global Instance closure_sigma_algebra_proper {T} :
  Proper (Equivalence.equiv ==> Equivalence.equiv) (@closure_sigma_algebra T).
Proof.
  unfold Equivalence.equiv, pre_event_equiv, sa_equiv.
  intros ?? eqq ?.
  simpl; split; intros HH
  ; apply generated_sa_closure in HH
  ; apply generated_sa_closure
  ; simpl in *
  ; intros sa allsa
  ; apply HH
  ; eapply all_included_proper; eauto.
  symmetry; eauto.
Qed.

Global Instance prob_space_closure_proper {T} :
  Proper (Equivalence.equiv ==> Equivalence.equiv ==> iff) (@prob_space_closure T).
Proof.
  unfold Equivalence.equiv, pre_event_equiv, sa_equiv.
  intros ?? eqq1 ?? eqq2.
  simpl; split; intros HH
  ; apply generated_sa_closure in HH
  ; apply generated_sa_closure
  ; simpl in *
  ; intros sa allsa
  ; eapply sa_proper
  ; try apply HH
  ; try red; firstorder.
Qed.

Lemma generated_sa_sub_sub {X:Type} (E1 E2:pre_event X -> Prop) :
  sa_sub (generated_sa E1) (generated_sa E2) <->
  (pre_event_sub E1 (sa_sigma (generated_sa E2))).
Proof.
  firstorder.
Qed.
    
Lemma generated_sa_equiv_subs {X:Type} (E1 E2:pre_event X -> Prop) :
  generated_sa E1 === generated_sa E2 <->
  (pre_event_sub E1 (sa_sigma (generated_sa E2)) /\
   pre_event_sub E2 (sa_sigma (generated_sa E1))).
Proof.
  firstorder.
Qed.

Global Instance generated_sa_sub_proper {X:Type}  :
  Proper (pre_event_sub ==> sa_sub) (@generated_sa X).
Proof.
  firstorder.
Qed.

Global Instance generated_sa_proper {X:Type}  :
  Proper (pre_event_equiv ==> sa_equiv) (@generated_sa X).
Proof.
  firstorder.
Qed.

Definition pre_event_set_product {T₁ T₂} (s₁ : pre_event T₁ -> Prop) (s₂ : pre_event T₂ -> Prop) : pre_event (T₁ * T₂) -> Prop
  := fun (e:pre_event (T₁ * T₂)) =>
       exists e₁ e₂,
         s₁ e₁ /\ s₂ e₂ /\
         e === (fun '(x₁, x₂) => e₁ x₁ /\ e₂ x₂).

   
Instance pre_event_set_product_proper {T1 T2} : Proper (equiv ==> equiv ==> equiv ==> iff) (@pre_event_set_product T1 T2).
Proof.
  repeat red.
  unfold equiv, pre_event_equiv, pre_event_set_product; simpl; intros.
  split; intros [x2 [x3 [? [? HH]]]]
  ; unfold equiv in *
  ; exists x2, x3
  ; firstorder.
Qed.

Instance product_sa {T₁ T₂} (sa₁:SigmaAlgebra T₁) (sa₂:SigmaAlgebra T₂) : SigmaAlgebra (T₁ * T₂)
  := generated_sa (pre_event_set_product (sa_sigma sa₁) (sa_sigma sa₂)).

Global Instance product_sa_proper {T1 T2} : Proper (equiv ==> equiv ==> equiv) (@product_sa T1 T2).
Proof.
  repeat red; unfold equiv, sa_equiv; simpl.
  intros.
  split; intros HH.
  - intros.
    apply HH.
    revert H1.
    apply all_included_proper.
    split; intros HH2.
    + now rewrite <- H, <- H0.
    + now rewrite H, H0.
  - intros.
    apply HH.
    revert H1.
    apply all_included_proper.
    split; intros HH2.
    + now rewrite H, H0.
    + now rewrite <- H, <- H0.
Qed.

Theorem product_sa_sa {T₁ T₂} {sa1:SigmaAlgebra T₁} {sa2:SigmaAlgebra T₂} (a:event sa1) (b:event sa2) :
  sa_sigma (product_sa sa1 sa2) (fun '(x,y) => a x /\ b y).
Proof.
  apply generated_sa_sub.
  red.
  destruct a; destruct b; simpl.
  exists x; exists x0.
  firstorder.
Qed.

Definition product_sa_event {T₁ T₂} {sa1:SigmaAlgebra T₁} {sa2:SigmaAlgebra T₂} (a:event sa1) (b:event sa2)
  := exist _ _ (product_sa_sa a b).

  

(* dependent product *)
Definition pre_event_set_dep_product {T₁:Type} {T₂:T₁->Type} (s₁ : pre_event T₁ -> Prop) (s₂ : forall x, pre_event (T₂ x) -> Prop) : pre_event (sigT T₂) -> Prop
  := fun (e:pre_event (sigT T₂)) =>
       exists (e₁:pre_event T₁) (e₂:forall x, pre_event (T₂ x)),
         s₁ e₁ /\ (forall x, e₁ x -> s₂ x (e₂ x)) /\
         e === (fun x12 => e₁ (projT1 x12) /\ e₂ _ (projT2 x12)).


Lemma pre_event_set_dep_product_proper {T1:Type} {T2:T1->Type}
      (s1x s1y : pre_event T1 -> Prop)
      (s1equiv : equiv s1x s1y)
      (s2x s2y : forall x, pre_event (T2 x) -> Prop)
      (s2equiv : (forall x y, s2x x y <-> s2y x y)) :
    pre_event_equiv (pre_event_set_dep_product s1x s2x)
                    (pre_event_set_dep_product s1y s2y).
Proof.
  repeat red.
  unfold equiv, pre_event_equiv, pre_event_set_dep_product; simpl; intros.
  split; intros [x2 [x3 [? [? HH]]]]
  ; unfold equiv in *
  ; exists x2, x3
  ; firstorder.
Qed.

Instance dep_product_sa {T₁:Type} {T₂:T₁->Type}
         (sa₁:SigmaAlgebra T₁) (sa₂:forall x, SigmaAlgebra (T₂ x)) : SigmaAlgebra (sigT T₂)
  := generated_sa (pre_event_set_dep_product (sa_sigma sa₁) (fun x => sa_sigma (sa₂ x))).

Lemma dep_product_sa_proper {T1 T2}
      (s1x s1y : SigmaAlgebra T1)
      (s1equiv : equiv s1x s1y)
      (s2x s2y : forall x, SigmaAlgebra (T2 x))
      (s2equiv : (forall x, equiv (s2x x) (s2y x))) :
  sa_equiv (dep_product_sa s1x s2x) (dep_product_sa s1y s2y).
Proof.
  repeat red; unfold equiv, sa_equiv in *; simpl.
  intros.
  split; intros HH.
  - intros.
    apply HH.
    revert H.
    apply all_included_proper.
    now apply pre_event_set_dep_product_proper.
  - intros.
    apply HH.
    revert H.
    apply all_included_proper.
    apply pre_event_set_dep_product_proper; symmetry; trivial.
    apply s2equiv.
Qed.

Lemma dep_product_sa_sa {T₁:Type} {T₂:T₁->Type} {sa₁:SigmaAlgebra T₁} {sa₂:forall x, SigmaAlgebra (T₂ x)}
       (a:event sa₁) (b:forall a, event (sa₂ a)) :
  sa_sigma (dep_product_sa sa₁ sa₂) (fun '(existT x y) => a x /\ b x y).
Proof.
  apply generated_sa_sub.
  red.
  exists a.
  exists b.
  split; [| split].
  - apply sa_sigma_event_pre.
  - intros.
    apply sa_sigma_event_pre.
  - intros [??]; simpl; reflexivity.
Qed.

Definition dep_product_sa_event {T₁:Type} {T₂:T₁->Type} {sa₁:SigmaAlgebra T₁} {sa₂:forall x, SigmaAlgebra (T₂ x)}
  (a:event sa₁) (b:forall a, event (sa₂ a)) :
  event (dep_product_sa sa₁ sa₂)
  := exist _ _ (dep_product_sa_sa a b).


Definition pre_event_push_forward {X Y:Type} (f:X->Y) (ex:pre_event X) : pre_event Y
  := fun y => exists x, f x = y /\ ex x.

Instance pre_event_push_forward_proper {X Y:Type} (f:X->Y) : Proper (equiv ==> equiv) (pre_event_push_forward f).
Proof.
  firstorder congruence.
Qed.

Definition pullback_sa_sigma {X Y:Type} (sa:SigmaAlgebra Y) (f:X->Y) : pre_event X -> Prop
  := fun (xe:pre_event X) =>
       exists ye:pre_event Y,
         sa_sigma sa ye /\
         forall a, xe a <-> ye (f a).

Program Instance pullback_sa {X Y:Type} (sa:SigmaAlgebra Y) (f:X->Y) : SigmaAlgebra X
  := {|
  sa_sigma := pullback_sa_sigma sa f |}.
Next Obligation.
  unfold pullback_sa_sigma in *.
  apply choice in H.
  destruct H as [ce Hce].
  exists (pre_union_of_collection ce).
  split.
  - apply sa_countable_union; intros n.
    apply Hce.
  - intros a.
    unfold pre_union_of_collection.
    split; intros [n ?]
    ; exists n
    ; now apply Hce.
Qed.
Next Obligation.
  unfold pullback_sa_sigma in *.
  destruct H as [y [??]].
  exists (pre_event_complement y).
  split.
  - now apply sa_complement.
  - unfold pre_event_complement.
    intros a.
    split; intros HH1 HH2; now apply H0 in HH2.
Qed.
Next Obligation.
  unfold pullback_sa_sigma in *.
  exists pre_Ω.
  split.
  - apply sa_all.
  - unfold pre_Ω.
    tauto.
Qed.
  
Program Instance pair_fst_sa {T1 T2:Type} (sa:SigmaAlgebra (T1 * T2))
        : SigmaAlgebra T1
  := {|
  sa_sigma := fun (ye:pre_event T1) =>
                sa_sigma sa (fun v => ye (fst v))
    |}.
Next Obligation.
  now apply sa_countable_union.
Qed.
Next Obligation.
  now apply sa_complement.
Qed.
Next Obligation.
  apply sa_all.
Qed.

Program Instance pair_snd_sa {T1 T2:Type} (sa:SigmaAlgebra (T1 * T2))
        : SigmaAlgebra T2
  := {|
  sa_sigma := fun (ye:pre_event T2) =>
                sa_sigma sa (fun v => ye (snd v))
    |}.
Next Obligation.
  now apply sa_countable_union.
Qed.
Next Obligation.
  now apply sa_complement.
Qed.
Next Obligation.
  apply sa_all.
Qed.

Lemma pair_fst_pullback {X Y:Type} (sa1 : SigmaAlgebra X) (inh : inhabited Y) :
  sa_equiv (pair_fst_sa (T2 := Y) (pullback_sa sa1 fst))
         sa1.
Proof.
  intros ?.
  split; intros.
  - simpl in H.
    unfold pullback_sa_sigma in H.
    destruct H as [? [? ?]].
    assert (pre_event_equiv x x0).
    {
      intros ?.
      destruct inh.
      specialize (H0 (x1, X0)).
      now simpl in H0.
    }
    now rewrite H1.
  - simpl.
    unfold pullback_sa_sigma.
    exists x.
    split; trivial.
    now intros.
  Qed.

Lemma pair_snd_pullback {X Y:Type} (sa2 : SigmaAlgebra Y) (inh : inhabited X) :
  sa_equiv (pair_snd_sa (T1 := X) (pullback_sa sa2 snd))
         sa2.
Proof.
  intros ?.
  split; intros.
  - simpl in H.
    unfold pullback_sa_sigma in H.
    destruct H as [? [? ?]].
    assert (pre_event_equiv x x0).
    {
      intros ?.
      destruct inh.
      specialize (H0 (X0, x1)).
      now simpl in H0.
    }
    now rewrite H1.
  - simpl.
    unfold pullback_sa_sigma.
    exists x.
    split; trivial.
    now intros.
  Qed.

Lemma pair_snd_pullback_fst {X Y:Type} (sa1 : SigmaAlgebra X) (inh1 : inhabited X) :
  sa_equiv (pair_snd_sa (pullback_sa sa1 fst)) (trivial_sa Y).
Proof.
  apply sa_equiv_subs.
  split; intros.
  - destruct (classic (sa_sub (pair_snd_sa (pullback_sa sa1 fst)) (trivial_sa Y))); try easy.
    assert (exists (e : pre_event Y),
             exists (y1 : Y), exists (y2 : Y),
               sa_sigma (pair_snd_sa (pullback_sa sa1 fst)) e /\
                 (e y1) /\ ~(e y2)).
    {
      apply not_all_ex_not in H.
      destruct H as [e HH].
      exists e.
      apply imply_to_and in HH.
      destruct HH as [HH1 HH2].
      apply not_or_and in HH2.
      destruct HH2 as [HH2 HH3].
      assert (exists y1, e y1).
      {
        apply NNPP; intros HH.
        elim HH2.
        intros y.
        generalize (not_ex_all_not _ _ HH y); firstorder.
      }
      assert (exists y2, ~ e y2).
      {
        apply NNPP; intros HH.
        elim HH3.
        intros y.
        generalize (not_ex_all_not _ _ HH y); intros HH'.
        apply NNPP in HH'.
        firstorder.
      }
      destruct H as [y1 ?].
      destruct H0 as [y2 ?].
      eauto.
    } 
    destruct H0 as [? [? [? [[? [? ?]] [? ?]]]]].
    destruct inh1.
    generalize (H1 (X0, x0)); intros.
    generalize (H1 (X0, x1)); intros.
    rewrite <- H5 in H4.
    tauto.
  - apply trivial_sa_sub.
Qed.

Instance pullback_sa_sigma_proper {X Y:Type} :
  Proper (equiv ==> (pointwise_relation X equiv) ==> equiv)
         (@pullback_sa_sigma X Y).
Proof.
  unfold pointwise_relation, equiv, pullback_sa_sigma.
  repeat red; intros; simpl.
  split; intros [ye [??]].
  - exists ye.
    split.
    + now apply H.
    + now intros; rewrite H2, H0.
  - exists ye.
    split.
    + now apply H.
    + now intros; rewrite H2, H0.
Qed.
  
Instance pullback_sa_proper {X Y:Type} :
  Proper (equiv ==> (pointwise_relation X equiv) ==> equiv)
         (@pullback_sa X Y).
Proof.
  unfold pointwise_relation, equiv.
  apply pullback_sa_sigma_proper.
Qed.

Lemma pullback_sa_pullback {X Y:Type} (sa:SigmaAlgebra Y) (f:X->Y) (y:pre_event Y) :
  sa_sigma _ y -> sa_sigma (pullback_sa sa f) (pre_event_preimage f y).
Proof.
  simpl.
  unfold pre_event_preimage, pullback_sa_sigma.
  intros say.
  exists y.
  split; trivial.
  reflexivity.
Qed.

Lemma nested_pullback_sa_equiv {X Y Z : Type} (sa : SigmaAlgebra Z) (f : X -> Y) (g : Y -> Z) :
  sa_equiv (pullback_sa sa (fun x => g (f x))) (pullback_sa (pullback_sa sa g) f).
Proof.
  apply sa_equiv_subs.
  split.
  - intros ??.
    simpl in *.
    red.
    red in H.
    destruct H as [? [? ?]].
    exists (fun x => x0 (g x)).
    split; trivial.
    now apply pullback_sa_pullback.
  - intros ??.
    simpl in *.
    destruct H as [?[[?[??]]?]]; simpl in *.
    red.
    exists x1.
    split; trivial.
    firstorder.
Qed.

Lemma pullback_sa_compose_equiv {X Y Z : Type} (sa : SigmaAlgebra Z) (f : X -> Y) (g : Y -> Z) :
  sa_equiv (pullback_sa sa (compose g f)) (pullback_sa (pullback_sa sa g) f).
Proof.
  rewrite <- nested_pullback_sa_equiv.
  apply pullback_sa_proper; try reflexivity.
Qed.

Program Instance prod_section_fst_sa {T₁ T₂} {sa1:SigmaAlgebra T₁} {sa2:SigmaAlgebra T₂} (x : T₁) : SigmaAlgebra (T₁ * T₂) :=
  {| sa_sigma := fun (e : pre_event (T₁ * T₂)) => sa_sigma sa2 (fun y => e (x, y)) |}.
Next Obligation.
  now apply sa_countable_union.
Qed.
Next Obligation.
  now apply sa_complement.
Qed.
Next Obligation.
  apply sa_all.  
Qed.

Program Instance prod_section_snd_sa {T₁ T₂} {sa1:SigmaAlgebra T₁} {sa2:SigmaAlgebra T₂} (y :  T₂) : SigmaAlgebra (T₁ * T₂) :=
  {| sa_sigma := fun (e : pre_event (T₁ * T₂)) => sa_sigma sa1 (fun x => e (x, y)) |}.
Next Obligation.
  now apply sa_countable_union.
Qed.
Next Obligation.
  now apply sa_complement.
Qed.
Next Obligation.
  apply sa_all.  
Qed.

Lemma product_section_fst {T₁ T₂} {sa1:SigmaAlgebra T₁} {sa2:SigmaAlgebra T₂}
      (E:event (product_sa sa1 sa2)) :
  forall x, sa_sigma sa2 (fun y => E (x, y)).
Proof.
  intros.
  pose (C := prod_section_fst_sa x).
  assert (forall (e : pre_event (T₁ * T₂)), 
             (pre_event_set_product (sa_sigma sa1) (sa_sigma sa2) e) -> sa_sigma C e). 
  {
    unfold pre_event_set_product.
    intros.
    destruct H as [? [? [? [? ?]]]].
    destruct (classic (x0 x)).
    - simpl.
      revert H0.
      apply sa_proper.
      intro z.
      specialize (H1 (x, z)).
      simpl in H1.
      tauto.
    - simpl.
      generalize (sa_none (s := sa2)).
      apply sa_proper.
      intro z.
      unfold pre_event_none.
      specialize (H1 (x, z)).
      simpl in H1.
      tauto.
   }
  assert (forall (e : pre_event (T₁ * T₂)), sa_sigma (product_sa sa1 sa2) e -> sa_sigma C e).
  {
    intros.
    generalize (generated_sa_minimal (pre_event_set_product (sa_sigma sa1) (sa_sigma sa2)) C H e); intros.
    now apply H1.
  }
  specialize (H0 E).
  apply H0.
  destruct E.
  apply s.
 Qed.

Lemma product_section_snd {T₁ T₂} {sa1:SigmaAlgebra T₁} {sa2:SigmaAlgebra T₂} (E:event (product_sa sa1 sa2)) :
  forall y, sa_sigma sa1 (fun x => E (x, y)).
Proof.
  intros.
  pose (C := prod_section_snd_sa (T₁ := T₁) y).
  assert (forall (e : pre_event (T₁ * T₂)), 
             (pre_event_set_product (sa_sigma sa1) (sa_sigma sa2) e) -> sa_sigma C e). 
  {
    unfold pre_event_set_product.
    intros.
    destruct H as [? [? [? [? ?]]]].
    destruct (classic (x0 y)).
    - simpl.
      revert H.
      apply sa_proper.
      intro z.
      specialize (H1 (z, y)).
      simpl in H1.
      tauto.
    - simpl.
      generalize (sa_none (s := sa1)).
      apply sa_proper.
      intro z.
      unfold pre_event_none.
      specialize (H1 (z, y)).
      simpl in H1.
      tauto.
   }
  assert (forall (e : pre_event (T₁ * T₂)), sa_sigma (product_sa sa1 sa2) e -> sa_sigma C e).
  {
    intros.
    generalize (generated_sa_minimal (pre_event_set_product (sa_sigma sa1) (sa_sigma sa2)) C H e); intros.
    now apply H1.
  }
  specialize (H0 E).
  apply H0.
  destruct E.
  apply s.
 Qed.

Section isos.
  Context {Ts:Type} {Td:Type} {cod: SigmaAlgebra Td}.

  Lemma pullback_sa_iso_l_sub (rv1 : Ts -> Td) (f g : Td -> Td)
    (inv:forall x, g (f x) = x)
    (g_sigma:forall s, sa_sigma _ s -> sa_sigma _ (fun x => s (g x))) :
    sa_sub (pullback_sa _ rv1) (pullback_sa _ (fun x => f (rv1 x))).
  Proof.
    intros ? [? [??]]; simpl in *.
    red.
    exists (fun x => x0 (g x)).
    split.
    - auto.
    - intros.
      split; intros ?.
      + now rewrite inv, <- H0.
      + now rewrite inv, <- H0 in H1.
  Qed.

  Lemma pullback_sa_f_sub (rv1 : Ts -> Td) (f : Td -> Td)
    (f_sigma:forall s, sa_sigma _ s -> sa_sigma _ (fun x => s (f x))) :
    sa_sub (pullback_sa _ (fun x => f (rv1 x))) (pullback_sa _ rv1).
  Proof.
    intros ? [? [??]]; simpl in *.
    red.
    exists (fun x => x0 (f x)).
    split; auto.
  Qed.

  Lemma pullback_sa_isos (rv1 : Ts -> Td) (f g : Td -> Td)
    (inv:forall x, g (f x) = x)
    (f_sigma:forall s, sa_sigma _ s -> sa_sigma _ (fun x => s (g x)))
    (g_sigma:forall s, sa_sigma _ s -> sa_sigma _ (fun x => s (f x))) :
    sa_equiv (pullback_sa _ rv1) (pullback_sa _ (fun x => f (rv1 x))).
  Proof.
    apply sa_equiv_subs.
    split.
    - eapply pullback_sa_iso_l_sub; eauto.
    - now apply pullback_sa_f_sub.
  Qed.

End isos.

Instance iso_sa {A B}
         {iso:Isomorphism A B}
         (sa:SigmaAlgebra A) : SigmaAlgebra B
  := pullback_sa sa iso_b.

Definition iso_event {A B: Type}
           {σ:SigmaAlgebra A}
           {iso:Isomorphism A B}
           (e:event σ) : event (iso_sa σ)
  := exist _ (pre_event_preimage (iso_b (Isomorphism:=iso)) e) (pullback_sa_pullback σ (iso_b (Isomorphism:=iso)) (event_pre e) (sa_sigma_event_pre e) ).

Program Definition iso_event_b {A B: Type}
        {σ:SigmaAlgebra A}
        {iso:Isomorphism A B}
        (e:event (iso_sa σ)) : event σ
  := exist _ (pre_event_preimage (iso_f (Isomorphism:=iso)) e) _.
Next Obligation.
  simpl in *.
  destruct e as [?[?[??]]].
  simpl in *.
  unfold pre_event_preimage.
  revert s.
  apply sa_proper; intros ?.
  split; intros HH.
  + apply i in HH.
    now rewrite iso_b_f in HH.
  + apply i.
    now rewrite iso_b_f.
Qed.

Global Instance iso_event_b_proper {A B: Type}
       {σ:SigmaAlgebra A}
       {iso:Isomorphism A B} :
  Proper (equiv ==> equiv)
         (@iso_event_b A B σ iso).
Proof.
  intros ????; simpl.
  apply pre_event_preimage_proper; try reflexivity.
  apply H.
Qed.

Lemma iso_event_b_union
      {A B: Type}
      {σ:SigmaAlgebra A}
      {iso:Isomorphism A B}
      (collection : nat -> event (iso_sa σ)):
  iso_event_b (union_of_collection collection) ===
              union_of_collection (fun n => iso_event_b (collection n)).
Proof.
  intros ?; simpl.
  unfold pre_event_preimage.
  split; intros [n HH]; exists n; apply HH.
Qed.

Lemma iso_event_b_disjoint
      {A B: Type}
      {σ:SigmaAlgebra A}
      {iso:Isomorphism A B}
      (collection : nat -> event (iso_sa σ)) :
  collection_is_pairwise_disjoint collection ->
  collection_is_pairwise_disjoint (fun n : nat => iso_event_b (collection n)).
Proof.
  unfold collection_is_pairwise_disjoint; intros ?????.
  now apply H.
Qed.

Definition union_sa {T : Type} (sa1 sa2:SigmaAlgebra T) :=
  generated_sa (pre_event_union (sa_sigma sa1) 
                                (sa_sigma sa2)).

Global Instance union_sa_proper {T:Type}  :
  Proper (sa_equiv ==> sa_equiv ==> sa_equiv) (@union_sa T).
Proof.
  intros ??????.
  unfold union_sa, pre_event_union.
  apply generated_sa_equiv_subs.
  split.
  - intros ??; firstorder.
  - intros ?; firstorder.
Qed.

Global Instance union_sa_sub_proper {T:Type}  :
  Proper (sa_sub ==> sa_sub ==> sa_sub) (@union_sa T).
Proof.
  intros ??????.
  unfold union_sa, pre_event_union.
  intros ??; firstorder.
Qed.

Lemma union_sa_sub_l {T : Type} (sa1 sa2:SigmaAlgebra T) :
  sa_sub sa1 (union_sa sa1 sa2).
Proof.
  intros ????; simpl.
  apply H0.
  now left.
Qed.

Lemma union_sa_sub_r {T : Type} (sa1 sa2:SigmaAlgebra T) :
  sa_sub sa2 (union_sa sa1 sa2).
Proof.
  intros ????; simpl.
  apply H0.
  now right.
Qed.

Lemma union_sa_comm {T : Type} (sa1 sa2:SigmaAlgebra T) :
  sa_equiv (union_sa sa1 sa2) (union_sa sa2 sa1).
Proof.
  apply generated_sa_proper.
  apply pre_event_union_comm.
Qed.

Lemma union_sa_generated_l_simpl {T : Type} (a b:pre_event T -> Prop) :
  generated_sa
    (pre_event_union (sa_sigma (generated_sa a)) b)
    ===
    generated_sa
    (pre_event_union a b).
Proof.
  split; intros HH; simpl in *; intros.
  - apply HH.
    intros ? [?|?].
    + apply H0; intros ??.
      apply H; red; tauto.
    + apply H; red; tauto.
  - apply HH.
    intros ? [?|?].
    + apply H.
      red.
      left; intros.
      now apply H1.
    + apply H.
      red; tauto.
Qed.

Lemma union_sa_generated_r_simpl {T : Type} (a b:pre_event T -> Prop) :
  generated_sa
    (pre_event_union a (sa_sigma (generated_sa b)))
    ===
    generated_sa
    (pre_event_union a b).
Proof.
  rewrite pre_event_union_comm.
  rewrite union_sa_generated_l_simpl.
  now rewrite pre_event_union_comm.
Qed.

Lemma union_sa_assoc {T : Type} (sa1 sa2 sa3:SigmaAlgebra T) :
  sa_equiv (union_sa sa1 (union_sa sa2 sa3)) (union_sa (union_sa sa1 sa2) sa3).
Proof.
  unfold union_sa.
  rewrite union_sa_generated_l_simpl, union_sa_generated_r_simpl.
  apply generated_sa_proper.
  apply pre_event_union_assoc.
Qed.

Lemma union_sa_sub_both {T : Type} {sa1 sa2 dom:SigmaAlgebra T} :
  sa_sub sa1 dom ->
  sa_sub sa2 dom ->
  sa_sub (union_sa sa1 sa2) dom.
Proof.
  unfold union_sa; intros.
  intros ? HH.
  apply HH.
  intros ? [?|?]; auto.
Qed.  

Lemma product_union_pullback {X Y:Type} (sa1 : SigmaAlgebra X) (sa2 : SigmaAlgebra Y) :
  sa_equiv (product_sa sa1 sa2) (union_sa (pullback_sa sa1 fst) (pullback_sa sa2 snd)).
Proof.
  apply sa_equiv_subs.
  split.
  - apply generated_sa_sub_sub.
    intros ??.
    destruct H as [? [? [? [? ?]]]].
    rewrite H1.
    assert (pre_event_equiv
              (fun '(x₁, x₂) => x0 x₁ /\ x1 x₂)
              (pre_event_inter (fun '(x₁, x₂) => x0 x₁)
                               (fun '(x₁, x₂) => x1 x₂))).
    {
      intros ?.
      destruct x2.
      now unfold pre_event_inter.
    }
    rewrite H2.
    apply sa_inter.
    + apply union_sa_sub_l.
      exists x0.
      split; trivial.
      intros.
      now destruct a.
    + apply union_sa_sub_r.
      exists x1.
      split; trivial.
      intros.
      now destruct a.
  - apply union_sa_sub_both.
    + intros ??.
      destruct H as [? [? ?]].
      generalize (product_sa_sa (exist _ _ H) Ω).
      apply sa_proper.
      intros ?.
      destruct x1.
      now rewrite H0.
    + intros ??.
      destruct H as [? [? ?]].
      generalize (product_sa_sa (sa1 := sa1) Ω (exist _ _ H)).
      apply sa_proper.
      intros ?.
      destruct x1.
      now rewrite H0.
Qed.

Lemma union_pullback_sub {A B : Type} (sa1 sa2 : SigmaAlgebra B) (f : A -> B) : 
  sa_sub (union_sa (pullback_sa sa1 f) (pullback_sa sa2 f))
         (pullback_sa (union_sa sa1 sa2) f).
Proof.
  apply union_sa_sub_both.
  - intros ??.
    destruct H as [? [? ?]].
    exists x0.
    split; trivial.
    now apply union_sa_sub_l.
  - intros ??.
    destruct H as [? [? ?]].
    exists x0.
    split; trivial.
    now apply union_sa_sub_r.
 Qed.    

 Lemma pullback_sa_sub {A B : Type} (sa1 sa2 : SigmaAlgebra B) (f : A -> B) :
   sa_sub sa1 sa2 ->
   sa_sub (pullback_sa sa1 f) (pullback_sa sa2 f).
 Proof.
   unfold pullback_sa, pullback_sa_sigma.
   intros ???.
   simpl in *.
   destruct H0 as [? [? ?]].
   exists x0.
   split; trivial.
   now apply H.
 Qed.

 Local Instance pullback_sa_sub_proper {A B : Type} : Proper (sa_sub ==> pointwise_relation _ eq ==> sa_sub) (@pullback_sa A B).
 Proof.
   intros ???????[?[??]].
   unfold pullback_sa, pullback_sa_sigma in *; simpl in *.
   exists x2.
   split.
   - now apply H.
   - intros a.
     now rewrite <- H0.
 Qed.

 Lemma pullback_sa_id {T : Type} (sa : SigmaAlgebra T) :
   sa_equiv (pullback_sa sa id) sa.
 Proof.
   intros ?.
   unfold pullback_sa, pullback_sa_sigma.
   simpl.
   split; intros.
   - destruct H as [? [? ?]].
     unfold id in H0.
     assert (pre_event_equiv x x0).
     {
       intros ?.
       apply H0.
     }
     now rewrite H1.
   - eexists.
     split; [apply H|].
     intros.
     now unfold id.
  Qed.

 Lemma iso_sa_symm_id {A B} (σ : SigmaAlgebra A) (iso:Isomorphism A B) :
  sa_equiv (iso_sa (iso:=Isomorphism_symm iso) (iso_sa (iso:=iso) σ)) σ.
Proof.
  unfold iso_sa.
  rewrite <- pullback_sa_compose_equiv.
  simpl.
  unfold compose.
  symmetry.
  rewrite <- pullback_sa_id at 1.
  apply (pullback_sa_proper); try reflexivity.
  intros ?.
  rewrite iso_b_f.
  reflexivity.
Qed.  

Lemma iso_sa_symm_id' {A B} (σ : SigmaAlgebra A) (iso:Isomorphism B A) :
  sa_equiv (iso_sa (iso:=iso) (iso_sa (iso:=Isomorphism_symm iso) σ)) σ.
Proof.
  unfold iso_sa.
  rewrite <- pullback_sa_compose_equiv.
  simpl.
  unfold compose.
  symmetry.
  rewrite <- pullback_sa_id at 1.
  apply (pullback_sa_proper); try reflexivity.
  intros ?.
  rewrite iso_f_b.
  reflexivity.
Qed.  

Lemma union_pullback_sub_conv {A B : Type} (sa1 sa2 : SigmaAlgebra B) 
      (f : A -> B) :
  (exists (g : B -> A),
      (pointwise_relation _ eq (compose f g) id) /\
      (pointwise_relation _ eq (compose g f) id)) ->
  sa_sub (pullback_sa (union_sa sa1 sa2) f)
         (union_sa (pullback_sa sa1 f) (pullback_sa sa2 f)).
Proof.
  intros [g [? ?]].
  generalize (union_pullback_sub (pullback_sa sa1 f) (pullback_sa sa2 f) g); intros.
  do 2 rewrite <- pullback_sa_compose_equiv in H1.
  rewrite H in H1.
  do 2 rewrite pullback_sa_id in H1.
  generalize (pullback_sa_sub _ _ f H1); intros.
  rewrite <- pullback_sa_compose_equiv in H2.
  rewrite H0 in H2.
  now rewrite pullback_sa_id in H2.
Qed.

Lemma union_pullback_comm {A B : Type} (sa1 sa2 : SigmaAlgebra B)
      (f : A -> B) :
  (exists (g : B -> A),
      (pointwise_relation _ eq (compose f g) id) /\
      (pointwise_relation _ eq (compose g f) id)) ->
  sa_equiv (union_sa (pullback_sa sa1 f) (pullback_sa sa2 f))
           (pullback_sa (union_sa sa1 sa2) f).
Proof.
  intros.
  apply sa_equiv_subs.
  split; intros.
  - apply union_pullback_sub.
  - now apply union_pullback_sub_conv.
Qed.

Lemma product_flip {A B:Type} (sa1 : SigmaAlgebra A) (sa2 : SigmaAlgebra B) :
  sa_equiv (product_sa sa1 sa2)
           (pullback_sa (product_sa sa2 sa1) (fun '(a,b) => (b,a))).
Proof.
  do 2 rewrite product_union_pullback.
  rewrite <- union_pullback_comm.
  - rewrite union_sa_comm.
    apply union_sa_proper;
      rewrite <- pullback_sa_compose_equiv;
      apply pullback_sa_proper; try easy;
      now intros [??].
  - exists (fun '(b,a) => (a,b)).
    split.
    + now intros [??].
    + now intros [??].
  Qed.

Lemma union_trivial {X} (sa : SigmaAlgebra X) :
  sa_equiv sa (union_sa (trivial_sa X) sa).
Proof.
  apply sa_equiv_subs.
  split.
  - apply union_sa_sub_r.
  - apply union_sa_sub_both.
    + apply trivial_sa_sub.
    + easy.
  Qed.

Definition countable_union_sa {T : Type} (sas:nat->SigmaAlgebra T) :=
  generated_sa (pre_union_of_collection (fun n => (sa_sigma (sas n)))).

Global Instance countable_union_sa_sub_proper {T:Type}  :
  Proper (pointwise_relation _ sa_sub ==> sa_sub) (@countable_union_sa T).
Proof.
  intros ???.
  unfold countable_union_sa, pre_union_of_collection.
  apply generated_sa_sub_proper.
  intros ? [n ?].
  specialize (H n).
  eauto.
Qed.

Lemma countable_union_sa_proper {T:Type}  :
  Proper (pointwise_relation _ sa_equiv ==> sa_equiv) (@countable_union_sa T).
Proof.
  intros ???.
  unfold countable_union_sa, pre_union_of_collection.
  apply generated_sa_proper; intros ?.
  split; intros [n ?]
  ; exists n; now apply H.
Qed.

Lemma countable_union_sa_sub {T : Type} (sas:nat -> SigmaAlgebra T) :
  forall n, sa_sub (sas n) (countable_union_sa sas).
Proof.
  intros ?????; simpl.
  apply H0.
  now exists n.
Qed.

Lemma countable_union_sa_sub_all {T : Type} {sas:nat -> SigmaAlgebra T} {dom: SigmaAlgebra T} :
  (forall n, sa_sub (sas n) dom) ->
  sa_sub (countable_union_sa sas) dom.
Proof.
  intros ???; simpl.
  apply H0.
  intros ?[??].
  eapply H; eauto.
Qed.

Definition is_countable {T} (e:pre_event T)
  := exists (coll:nat -> T -> Prop),
    (forall n t1 t2, coll n t1 -> coll n t2 -> t1 = t2) /\
    e === (fun a => exists n, coll n a).

Lemma is_countable_empty {T} : @is_countable T pre_event_none.
Proof.
  exists (fun n t => False).
  firstorder.
Qed.

Instance is_countable_proper_sub {T} : Proper (pre_event_sub --> Basics.impl) (@is_countable T).
Proof.
  unfold Proper, respectful, Basics.impl, Basics.flip, is_countable.
  intros x y sub [c cx].
  red in sub.
  exists (fun n t =>
            c n t /\ y t).
  firstorder.
Qed.

Global Instance is_countable_proper {T} : Proper (equiv ==> iff) (@is_countable T).
Proof.
  unfold Proper, respectful.
  intros x y eqq.
  split; intros.
  - apply (is_countable_proper_sub x y); trivial.
    apply pre_event_equiv_sub; trivial.
    symmetry; trivial.
  - apply (is_countable_proper_sub y x); trivial.
    apply pre_event_equiv_sub; trivial.
Qed.

Lemma is_countable_singleton {A:Type} {σ:SigmaAlgebra A} x pf :
  is_countable (event_singleton x pf).
Proof.
  red.
  exists (fun n => match n with
           | 0 => fun x' => x = x'
           | _ => pre_event_none
           end
    ).
  split.
  - intros ??? s1 s2.
    match_destr_in s1; [congruence|].
    red in s1; tauto.
  - intros ?.
    simpl.
    unfold pre_event_singleton.
    split.
    + intros; subst.
      exists 0%nat; trivial.
    + intros [? s1].
      match_destr_in s1.
      * eauto.
      * red in s1; tauto.
Qed.

Definition Finj_event {T} (coll:nat->pre_event T) (n:nat) : ({x:T | coll n x} -> nat) -> Prop
  := fun f => Injective f.

Lemma union_of_collection_is_countable {T} (coll:nat->pre_event T) :
  (forall n : nat, is_countable (coll n)) -> is_countable (pre_union_of_collection coll).
Proof.
  intros isc.
  apply choice in isc.
  destruct isc as [f fprop].
  exists (fun n => let '(n1,n2) := iso_b n in f n1 n2).
  split.
  - intros.
    case_eq (@iso_b _ _ nat_pair_encoder n); intros n1 n2 eqq.
    rewrite eqq in *.
    destruct (fprop n1)
      as [HH1 HH2].
    eapply HH1; eauto.
  - intros x.
    split.
    + intros [n1 ncoll].
      destruct (fprop n1) as [HH1 HH2].
      specialize (HH2 x).
      apply HH2 in ncoll.
      destruct ncoll as [n2 fx].
      exists (iso_f (n1,n2)).
      rewrite iso_b_f; trivial.
    + intros [n fx].
      case_eq (@iso_b _ _ nat_pair_encoder n).
      intros n1 n2 eqq.
      rewrite eqq in *.
      destruct (fprop n1) as [HH1 HH2].
      specialize (HH2 x).
      exists n1.
      apply HH2.
      eauto.
Qed.

(* The set of countable and c-countable sets forms a sigma algebra *)
Local Program Instance countable_sa (T:Type) : SigmaAlgebra T
  := {
      sa_sigma (f:pre_event T) := is_countable f \/ is_countable (¬ f)
    }.
Next Obligation.
  destruct (classic (forall n, is_countable (collection n))).
  + (* they are all countable *)
    left.
    apply union_of_collection_is_countable; trivial.
  + apply not_all_ex_not in H0.
    destruct H0 as [n ncn].
    assert (iscnn:is_countable (pre_event_complement (collection n))).
    { destruct (H n); intuition. }
    generalize (pre_union_of_collection_sup collection n); intros subs.
    apply pre_event_complement_sub_proper in subs.
    rewrite <- subs in iscnn.
    eauto.
Qed.
Next Obligation.
  rewrite pre_event_not_not by auto using sa_pre_dec.
  tauto.
Qed.
Next Obligation.
  right.
  rewrite pre_event_not_all.
  apply is_countable_empty.
Qed.

(* vector product *)
Definition pre_event_set_vector_product {T} {n} (v:vector ((pre_event T)->Prop) n) : pre_event (vector T n) -> Prop
  := fun (e:pre_event (vector T n)) =>
       exists (sub_e:vector (pre_event T) n),
         (forall i pf, (vector_nth i pf v) (vector_nth i pf sub_e))
         /\
         e === (fun (x:vector T n) => forall i pf, (vector_nth i pf sub_e) (vector_nth i pf x)).

Instance pre_event_set_vector_product_proper {n} {T} : Proper (equiv ==> equiv) (@pre_event_set_vector_product T n).
Proof.
  repeat red.
  unfold equiv, pre_event_equiv, pre_event_set_vector_product; simpl; intros.
  split; intros [v [HH1 HH2]].
  - unfold equiv in *.
    exists v.
    split; intros.
    + apply H; eauto.
    + rewrite HH2.
      reflexivity.
  - unfold equiv in *.
    exists v.
    split; intros.
    + apply H; eauto.
    + rewrite HH2.
      reflexivity.
Qed.

Instance vector_sa {n} {T} (sav:vector (SigmaAlgebra T) n) : SigmaAlgebra (vector T n)
  := generated_sa (pre_event_set_vector_product (vector_map sa_sigma sav)).

Global Instance vector_sa_proper {T} {n} : Proper (equiv ==> equiv) (@vector_sa T n).
Proof.
  repeat red; unfold equiv, sa_equiv; simpl.
  intros.
  split; intros HH.
  - intros.
    apply HH.
    revert H0.
    apply all_included_proper.
    apply pre_event_set_vector_product_proper.
    intros ??.
    repeat rewrite vector_nth_map.
    specialize (H i pf).
    apply H.
  - intros.
    apply HH.
    revert H0.
    apply all_included_proper.
    apply pre_event_set_vector_product_proper.
    intros ??.
    repeat rewrite vector_nth_map.
    specialize (H i pf).
    symmetry.
    apply H.
Qed.

(* vector product, inductively *)

Section ivector.

  Fixpoint ivector_sa {n} {T} : ivector (SigmaAlgebra T) n -> SigmaAlgebra (ivector T n)
    := match n with
       | 0%nat => fun _ => trivial_sa unit
       | S m => fun '(hd,tl) => product_sa hd (ivector_sa tl)
       end.

  Global Existing Instance ivector_sa.
  
  Global Instance ivector_sa_proper {n} {T} :
    Proper (ivector_Forall2 equiv ==> equiv) (@ivector_sa n T).
  Proof.
    unfold Proper, respectful; simpl.
    induction n; simpl.
    - reflexivity.
    - intros [??][??] [??] ?.
      split.
      + apply product_sa_proper; trivial.
        * now symmetry.
        * apply IHn.
          now symmetry.
      + apply product_sa_proper; trivial.
        now apply IHn.
  Qed.

  Lemma ivector_sa_sa {n} {T} {σ:SigmaAlgebra T} (a:ivector (event σ) n) :
    sa_sigma (ivector_sa (ivector_const n σ))
             (fun v => ivector_Forall2 (fun a x => event_pre a x) a v).
  Proof.
    revert a.
    induction n; [firstorder |].
    intros [hd tl].
    apply generated_sa_sub.
    red.
    exists (event_pre hd).
    exists  (fun v : ivector T n => ivector_Forall2 (fun (a0 : event σ) (x : T) => a0 x) tl v).
    split; [| split].
    - now destruct hd.
    - apply IHn.
    - reflexivity.
  Qed.

  Definition ivector_sa_event {n} {T} {σ:SigmaAlgebra T} (a:ivector (event σ) n)
    : event (ivector_sa (ivector_const n σ))
  := exist _ _ (ivector_sa_sa a).

  Lemma ivector_sa_event_as_prod {n} {T} {σ:SigmaAlgebra T} (hd:event σ) (tl:ivector (event σ) n) :
    ivector_sa_event (n:=S n) (hd, tl) === product_sa_event hd (ivector_sa_event tl).
  Proof.
    unfold equiv, event_equiv; simpl.
    reflexivity.
  Qed.

Program Instance ivector_hd_sa {T:Type} {n:nat} (sa:SigmaAlgebra (ivector T (S n)))
        : SigmaAlgebra T
  := {|
  sa_sigma := fun (ye:pre_event T) =>
                sa_sigma sa 
                         (fun (v : (ivector T (S n))) => ye (ivector_hd v))
    |}.
Next Obligation.
  now apply sa_countable_union.
Qed.
Next Obligation.
  now apply sa_complement.
Qed.
Next Obligation.
  apply sa_all.
Qed.

Program Instance ivector_tl_sa {T:Type} {n:nat} (sa:SigmaAlgebra (ivector T (S n)))
        : SigmaAlgebra (ivector T n)
  := {|
  sa_sigma := fun (ye:pre_event (ivector T n)) =>
                sa_sigma sa 
                         (fun (v : (ivector T (S n))) => ye (ivector_tl v))
    |}.
Next Obligation.
  now apply sa_countable_union.
Qed.
Next Obligation.
  now apply sa_complement.
Qed.
Next Obligation.
  apply sa_all.
Qed.


  Definition pre_event_set_ivector_product {T} {n} (v:ivector ((pre_event T)->Prop) n) : pre_event (ivector T n) -> Prop
    := fun (e:pre_event (ivector T n)) =>
         exists (sub_e:ivector (pre_event T) n),
           (forall i pf, (ivector_nth i pf v) (ivector_nth i pf sub_e))
           /\
           e === (fun (x:ivector T n) => forall i pf, (ivector_nth i pf sub_e) (ivector_nth i pf x)).

  Instance pre_event_set_ivector_product_proper {n} {T} : Proper (equiv ==> equiv) (@pre_event_set_ivector_product T n).
  Proof.
    repeat red.
    unfold equiv, pre_event_equiv, pre_event_set_ivector_product; simpl; intros.
    split; intros [v [HH1 HH2]].
    - unfold equiv in *.
      exists v.
      split; intros.
      + rewrite <- ivector_Forall2_nth_iff in H.
        apply H; eauto.
      + rewrite HH2.
        reflexivity.
    - unfold equiv in *.
      exists v.
      split; intros.
      + rewrite <- ivector_Forall2_nth_iff in H.
         apply H; eauto.
      + rewrite HH2.
        reflexivity.
  Qed.

  Lemma lt_S_n_S i1 n pf :
    (Lt.lt_S_n i1 n (Lt.lt_n_S i1 n pf)) = pf.
  Proof.
    apply digit_pf_irrel.
  Qed.
  
  
  Lemma generated_rectangle_proj {T} {n} (s : SigmaAlgebra T) (i : ivector (SigmaAlgebra T) n) (e : pre_event (ivector T n)) :
    sa_sigma (generated_sa (pre_event_set_ivector_product (ivector_map sa_sigma i))) e ->
    sa_sigma (generated_sa (pre_event_set_ivector_product (ivector_map sa_sigma (n:=S n) (s, i)))) (fun '(_, x₂) => e x₂).
  Proof.
    simpl; intros HH sa saInc.
    - specialize (HH (ivector_tl_sa sa)).
      eapply sa_proper; try eapply HH.
      + now intros [??]; simpl.
      + clear HH.
        intros ? [?[??]].
        apply saInc.
        red.
        exists (pre_Ω, x).
        split.
        * intros.
          destruct i0; simpl.
          -- apply sa_all.
          --  apply H.
        * split; intros HH.
          -- rewrite (H0 (ivector_tl x0)) in HH.
             intros [|?]?; simpl.
             ++ now red.
             ++ destruct x0.
                apply HH.
          -- apply H0; intros.
             destruct x0.
             specialize (HH (S i0) (Lt.lt_n_S _ _ pf)); simpl in *.
             now rewrite lt_S_n_S in HH.
  Qed.

  Lemma ivector_rectangles_generate_sa {n} {T} 
        (sav:ivector (SigmaAlgebra T) n) : 
    sa_equiv 
      (ivector_sa sav)
      (generated_sa (pre_event_set_ivector_product (ivector_map sa_sigma sav))).
  Proof.
    revert sav.
    induction n; intros.
    - intros ?.
      simpl.
      split; intros.      
      + destruct H; rewrite  H.
        * apply sa_none.
        * apply sa_all.
      + apply (H (trivial_sa unit)).
        intros ??.
        destruct H0 as [? [? ?]].
        rewrite H1.
        simpl; right.
        easy.
    - intros ?.
      destruct sav.
      split; intros.
      + unfold ivector_sa, product_sa in H.
        destruct
          (generated_sa_sub_sub 
             (pre_event_set_product 
                (sa_sigma s)
                (sa_sigma
                   ((fix ivector_sa (n : nat) (T : Type) {struct n} : ivector (SigmaAlgebra T) n -> SigmaAlgebra (ivector T n) :=
                       match n as n0 return (ivector (SigmaAlgebra T) n0 -> SigmaAlgebra (ivector T n0)) with
                       | 0 => fun _ : ivector (SigmaAlgebra T) 0 => trivial_sa ()
                       | S m => fun '(hd, tl) => generated_sa (pre_event_set_product (sa_sigma hd) (sa_sigma (ivector_sa m T tl)))
                       end) n T i)))
             (pre_event_set_ivector_product (ivector_map sa_sigma (ivector_cons s i)))).
        clear H0.
        apply H1; [|apply H].
        clear H1.
        unfold pre_event_sub.
        intros.
        destruct H0 as [? [? [? [? ?]]]].
        rewrite H2.
        assert (pre_event_equiv
                  (fun '(x₁, x₂) => x1 x₁ /\ x2 x₂)
                  (pre_event_inter
                     (fun '(x₁, x₂) => x1 x₁)
                     (fun '(x₁, x₂) => x2 x₂))).
        {
          intros ?.
          destruct x3.
          easy.
        }
        rewrite H3.
        specialize (IHn i).
        apply sa_inter.
        * apply generated_sa_sub.
          unfold pre_event_set_ivector_product.
          exists (ivector_cons x1 (ivector_const n pre_Ω)).
          split.
          -- intros.
             destruct i0.
             ++ now simpl.
             ++ simpl.
                rewrite ivector_nth_const, ivector_nth_map.
                apply sa_all.  
          -- intros ?.
             destruct x3.
             split; intros.
             ++ destruct i1.
                ** now simpl.
                ** simpl.
                   now rewrite ivector_nth_const.
             ++ assert (0 < S n) by lia.
                specialize (H4 0 H5).
                now simpl in H4.
        * clear H2 H3 x0 x1 H0 x H.
          simpl in H1.
          apply (generated_rectangle_proj s i x2).
          apply IHn.
          apply H1.
      + simpl; intros.
        apply H.
        intros ??.
        apply H0.
        destruct H1 as [? [? ?]].
        unfold pre_event_set_product.
        destruct x0.
        exists p.
        exists (fun v => ivector_Forall2 (fun a0 (x : T) => a0 x) i0 v).
        generalize (H1 0 (NPeano.Nat.lt_0_succ n)); intros.
        simpl in H3.
        split; trivial.
        split.
        * apply IHn.
          apply generated_sa_sub.
          unfold pre_event_set_ivector_product.
          exists i0; split.
          -- intros.
             specialize (H1 (S i1) (Lt.lt_n_S i1 n pf)).
             simpl in H1.
             now rewrite lt_S_n_S in H1.
          -- intros ?.
             now rewrite <- ivector_Forall2_nth_iff.
        * rewrite H2.
          intros ?.
          destruct x0.
          split; intros.
          generalize (H4 0 (NPeano.Nat.lt_0_succ n)); intros.
          simpl in H5.
          split; trivial.
          -- rewrite <- ivector_Forall2_nth_iff.
             intros.
             specialize (H4 (S i2) (Lt.lt_n_S i2 n pf)).
             simpl in H4.
             now rewrite lt_S_n_S in H4.             
          -- destruct H4.
             rewrite <- ivector_Forall2_nth_iff in H5.
             destruct i2.
             ++ now simpl.
             ++ apply H5.
   Qed.
  
  Lemma ivector_rectangles_union_nth {n} {T} 
        (sav:ivector (SigmaAlgebra T) n) : 
    sa_equiv 
      (generated_sa (pre_event_set_ivector_product (ivector_map sa_sigma sav)))
      (countable_union_sa
         (fun (i : nat) =>
            match Compare_dec.lt_dec i n with
            | left pf => 
              pullback_sa (ivector_nth i pf sav)
                          (fun (v : ivector T n) => ivector_nth i pf v)
            | right _ => (trivial_sa (ivector T n))
            end )).
   Proof.
     apply sa_equiv_subs.
     split.
     - apply generated_sa_sub_sub.
       intros ??.
       destruct H as [? [? ?]].
       rewrite H0.
       apply sa_pre_bounded_inter.
       intros.
       simpl.
       intros.
       apply H1.
       exists n0.
       match_destr; try lia.
       simpl.
       unfold pullback_sa_sigma.
       exists (ivector_nth _ pf x0).
       specialize (H n0 pf).
       rewrite ivector_nth_map in H.
       split.
       + now rewrite (digit_pf_irrel _ _ l pf).
       + intros.
         now rewrite (digit_pf_irrel _ _ l pf).
     - apply countable_union_sa_sub_all.
       intros.
       intros ??.
       match_destr_in H.
       + simpl in H.
         destruct H as [? [??]].
         apply generated_sa_sub.
         exists (ivector_create n (fun i pf => if i == n0 then x0 else pre_Ω)).
         split.
         * intros.
           rewrite ivector_nth_create, ivector_nth_map.
           match_destr.
           -- destruct e.
              now rewrite (digit_pf_irrel _ _ pf l).           
           -- apply sa_all.
        * intros ?.
          split; intros.
          -- rewrite ivector_nth_create.
             rewrite H0 in H1.
             match_destr.
             ++ destruct e.
                now rewrite (digit_pf_irrel _ _ pf l).                           
             ++ now unfold pre_Ω.
          -- rewrite (H0 x1).
             specialize (H1 n0 l).
             rewrite ivector_nth_create in H1.
             match_destr_in H1.
             now destruct c.
       + now apply trivial_sa_sub.
   Qed.

   Lemma ivector_sa_countable_union_nth  {n} {T} 
         (sav:ivector (SigmaAlgebra T) n) :
      sa_equiv 
        (ivector_sa sav)
        (countable_union_sa
           (fun (i : nat) =>
              match Compare_dec.lt_dec i n with
              | left pf => 
                pullback_sa (ivector_nth i pf sav)
                            (fun (v : ivector T n) => ivector_nth i pf v)
              | right _ => (trivial_sa (ivector T n))
              end )).
  Proof.
    rewrite ivector_rectangles_generate_sa.
    apply ivector_rectangles_union_nth.
  Qed.

  Lemma countable_union_pullback_sub {A B} 
        (sas: nat -> SigmaAlgebra B) (f : A -> B) :
    sa_sub 
        (countable_union_sa (fun (i : nat) => pullback_sa (sas i) f))
        (pullback_sa (countable_union_sa sas) f).
   Proof.
     apply countable_union_sa_sub_all.
     intros ???.
     destruct H as [? [? ?]].
     exists x0.
     split; trivial.
     now apply (countable_union_sa_sub sas n).
   Qed.

   Lemma countable_union_pullback_sub_conv {A B : Type} 
         (sas : nat -> SigmaAlgebra B) 
         (f : A -> B) :
  (exists (g : B -> A),
      (pointwise_relation _ eq (compose f g) id) /\
      (pointwise_relation _ eq (compose g f) id)) ->
  sa_sub (pullback_sa (countable_union_sa sas) f)
         (countable_union_sa (fun (i : nat) => pullback_sa (sas i) f)).
   Proof.
     intros [g [? ?]].
     generalize (countable_union_pullback_sub
                   (fun n => pullback_sa (sas n) f) g); intros.
     assert (sa_equiv
               (countable_union_sa (fun i : nat => pullback_sa (pullback_sa (sas i) f) g))
               (countable_union_sa sas)).
     {
       intros ?.
       apply countable_union_sa_proper.
       intros ?.
       rewrite <- pullback_sa_compose_equiv.
       rewrite H.
       now rewrite pullback_sa_id.
     }
     rewrite H2 in H1.
     generalize (pullback_sa_sub _ _ f H1); intros.
     rewrite <- pullback_sa_compose_equiv in H3.
     rewrite H0 in H3.
     now rewrite pullback_sa_id in H3.
   Qed.

   Lemma countable_union_pullback_comm {A B : Type}
         (sas : nat -> SigmaAlgebra B) 
         (f : A -> B) :
  (exists (g : B -> A),
      (pointwise_relation _ eq (compose f g) id) /\
      (pointwise_relation _ eq (compose g f) id)) ->
    sa_equiv
        (countable_union_sa (fun (i : nat) => pullback_sa (sas i) f))
        (pullback_sa (countable_union_sa sas) f).
Proof.
  intros.
  apply sa_equiv_subs.
  split; intros.
  - apply countable_union_pullback_sub.
  - now apply countable_union_pullback_sub_conv.
Qed.

Lemma countable_union_permute_ind {T : Type}
      (sas : nat -> SigmaAlgebra T)
      (f : nat -> nat) :
  (exists (g : nat -> nat),
      (pointwise_relation _ eq (compose f g) id) /\
      (pointwise_relation _ eq (compose g f) id)) ->
  sa_equiv
    (countable_union_sa sas)
    (countable_union_sa (fun n => sas (f n))).
Proof.
  intros ??.
  simpl.
  destruct H as [g [? ?]].
  split; intros.
  - apply H1.
    intros ??.
    apply H2.
    destruct H3.
    exists (g x0).
    specialize (H x0).
    unfold compose, id in H.
    now rewrite H.
  - apply H1.
    intros ??.
    apply H2.
    destruct H3.
    now exists (f x0).
Qed.


Lemma pullback_ivector_sa_rev {T} {n : nat} (sav: ivector (SigmaAlgebra T) n) :
  sa_equiv (ivector_sa sav)
           (pullback_sa (ivector_sa (ivector_rev sav)) ivector_rev).
Proof.
    do 2 rewrite ivector_sa_countable_union_nth.
    rewrite <- countable_union_pullback_comm.
    - pose (f := fun (i : nat) =>
                   match Compare_dec.lt_dec i n with
                   | left _ => n - S i
                   | in_right => i
                   end).
      rewrite (countable_union_permute_ind
                     (fun i : nat =>
                        match Compare_dec.lt_dec i n with
                        | left pf => pullback_sa (ivector_nth i pf sav) (fun v : ivector T n => ivector_nth i pf v)
                        | in_right => trivial_sa (ivector T n)
                        end)
                     f).
      + apply countable_union_sa_proper.
        intros ??.
        split; intros.
        unfold f in H.
        * match_destr.
          -- rewrite <- (nested_pullback_sa_equiv (ivector_nth a l (ivector_rev sav)) (@ivector_rev n T)  (fun v : ivector T n => ivector_nth a l v) x).
             match_destr_in H; try lia.
             rewrite ivector_nth_rev.
             destruct H as [? [? ?]].
             simpl; red.
             exists x0.
             split.
             ++ now rewrite (digit_pf_irrel _ _  (ivector_rev_ind l) l0).       
             ++ intros.
                rewrite (H0 a0).
                rewrite ivector_nth_rev.
                now rewrite (digit_pf_irrel _ _  (ivector_rev_ind l) l0).
          -- match_destr_in H; try lia.
             destruct H.
             ++ simpl; red.
                exists pre_event_none; split.
                ** apply sa_none.
                ** intros.
                   now rewrite (H a0).
             ++ simpl; red.
                exists pre_Ω; split.
                ** apply sa_all.
                ** intros.
                   now rewrite (H a0).
        * unfold f.
          match_destr_in H.
          -- match_destr; try lia.
             rewrite <- (nested_pullback_sa_equiv (ivector_nth a l (ivector_rev sav)) (@ivector_rev n T)  (fun v : ivector T n => ivector_nth a l v) x) in H.
             rewrite ivector_nth_rev in H.
             destruct H as [? [? ?]].
             simpl; red.
             exists x0.
             split.
             ++ now rewrite (digit_pf_irrel _ _  (ivector_rev_ind l) l0) in H.
             ++ intros.
                rewrite (H0 a0).
                rewrite ivector_nth_rev.
                now rewrite (digit_pf_irrel _ _  (ivector_rev_ind l) l0).
          -- destruct H as [? [? ?]].
             match_destr; try lia.
             destruct H.
             ++ left.
                intros ?.
                now rewrite H0, (H (ivector_rev x1)).
             ++ right.
                intros ?.
                now rewrite H0, (H (ivector_rev x1)).
      + exists f.
        split;
          intros ?;
          unfold f, compose, id;
          match_destr; match_destr; try lia.
    - exists ivector_rev.
      unfold compose, id.
      split; intros ?;
        now rewrite ivector_rev_involutive.
  Qed.

   Lemma pullback_ivector_sa_rev_alt {T} {n : nat} (sav: ivector (SigmaAlgebra T) n):
     sa_equiv (pullback_sa (ivector_sa sav) ivector_rev)
              (ivector_sa (ivector_rev sav)).
   Proof.
     generalize (pullback_ivector_sa_rev (ivector_rev sav)); intros.
     symmetry in H.
     now rewrite ivector_rev_involutive in H.
   Qed.

End ivector.

Section infalg.
  Context {Idx:Type}.

  Definition pre_event_set_infinite_product
             {types:Idx->Type}
             (v:forall (i:Idx), ((pre_event (types i))->Prop)) : pre_event (forall (i:Idx), types i) -> Prop
    := fun (e:pre_event (forall (i:Idx), types i)) =>
         exists (l:list Idx),
           NoDup l ->
           exists (sub_e:(forall (i:Idx), pre_event (types i))),
             Forall (fun i => (v i) (sub_e i)) l /\
               e === fun x => Forall (fun i => (sub_e i) (x i)) l.

Instance infinite_product_sa {spaces:Idx->sigT SigmaAlgebra} : SigmaAlgebra (forall (i:Idx), projT1 (spaces i))
  := generated_sa (pre_event_set_infinite_product (fun i => sa_sigma (projT2 (spaces i)))).

End infalg.


Definition is_pre_partition_list {T} (l:list (pre_event T)) :=
  ForallOrdPairs pre_event_disjoint l /\ pre_list_union l === pre_Ω.

Lemma pre_is_partition_list_partition {T} {l:list (pre_event T)} :
  is_pre_partition_list l ->
  is_pre_partition (pre_list_collection l pre_event_none).
Proof.
  intros [??].
  split.
  - now apply pre_list_collection_disjoint.
  - rewrite pre_list_union_union, H0.
    reflexivity.
Qed.

Instance list_partition_sa {T} (l:list (pre_event T)) (is_part:is_pre_partition_list l) :
  SigmaAlgebra T := countable_partition_sa
                      (pre_list_collection l pre_event_none)
                      (pre_is_partition_list_partition is_part).

Definition is_partition_list {T} {σ:SigmaAlgebra T} (l:list (event σ)) :=
  ForallOrdPairs event_disjoint l /\ list_union l === Ω.

Lemma is_partition_list_pre {T} {σ:SigmaAlgebra T}
      (l : list (event σ))
      (isp:is_pre_partition_list (map event_pre l)) :
  is_partition_list l <->
  is_pre_partition_list (map event_pre l).
Proof.
  unfold is_partition_list, is_pre_partition_list.
  rewrite list_union_as_pre.
  unfold equiv.
  unfold event_equiv; simpl.
  unfold event_pre; simpl.
  split; intros [??]; split; trivial.
  - apply ForallOrdPairs_map.
    revert H.
    apply ForallOrdPairs_sub; try reflexivity.
  - rewrite ForallOrdPairs_map in H.
    revert H.
    apply ForallOrdPairs_sub; try reflexivity.
Qed.

Global Instance is_partition_list_perm {T} {σ:SigmaAlgebra T}  :
  Proper (@Permutation _ ==> iff) (@is_partition_list T σ).
Proof.
  cut (Proper (@Permutation _ ==> impl) is_partition_list).
  {
    unfold Proper, respectful, impl; intros HH x y perm.
    split; intros.
    - eauto.
    - symmetry in perm.
      eauto.
  }
  unfold is_partition_list.
  unfold Proper, respectful, impl; intros x y perm [HH HHunion].
  split.
  - eapply ForallOrdPairs_perm; try eapply HH.
    + apply event_disjoint_sym.
    + now symmetry.
  - now rewrite <- perm.
Qed.

Global Instance is_partition_list_event_equiv {T} {σ:SigmaAlgebra T}:
  Proper (Forall2 event_equiv ==> iff) (@is_partition_list T σ).
Proof.
  cut (Proper (Forall2 event_equiv ==> impl) is_partition_list).
  {
    unfold Proper, respectful, impl; intros HH x y perm.
    split; intros.
    - eauto.
    - symmetry in perm.
      eauto.
  }
  unfold is_partition_list.
  unfold Proper, respectful, impl; intros x y perm [HH HHunion].
  split.
  - eapply ForallOrdPairs_Forall2_prop; eauto.
    apply event_disjoint_proper'.
  - rewrite <- HHunion.
    now apply list_union_Forall2_prop.
Qed.

Lemma is_partition_list_trivial {T} {σ:SigmaAlgebra T} :
  is_partition_list (Ω :: nil) (σ:=σ).
Proof.
  split.
  - repeat constructor.
  - apply list_union_singleton.
Qed.

Section dec.

  Context {Ts:Type} {dom:SigmaAlgebra Ts}.

  Lemma is_partition_refine (l1 l2 : list dec_sa_event) :
    is_partition_list (map dsa_event l1) ->
    is_partition_list (map dsa_event l2) ->    
    is_partition_list (map dsa_event (refine_dec_sa_partitions l1 l2)).
  Proof.
    unfold is_partition_list, refine_dec_sa_partitions.
    intros [??] [??].
    split.
    - now apply events_disjoint_refine.
    - now rewrite event_equiv_list_union_refine_all.
  Qed.

End dec.

Section filtration.
  Context {Ts:Type}.

  Class IsSubAlgebras {Idx} (dom:SigmaAlgebra Ts) (sas:Idx->SigmaAlgebra Ts)
    := is_sub_algebras : forall n, sa_sub (sas n) dom.
    
  Class IsFiltration (sas:nat->SigmaAlgebra Ts)
    := is_filtration : forall n, sa_sub (sas n) (sas (S n)).

  Lemma is_filtration_le (sas:nat->SigmaAlgebra Ts) {isf:IsFiltration sas}
    : forall k n, k <= n -> sa_sub (sas k) (sas n).
  Proof.
    induction 1.
    - reflexivity.
    - rewrite IHle.
      apply is_filtration.
  Qed.

  Global Instance is_filtration_const (c:SigmaAlgebra Ts) : IsFiltration (fun _ : nat => c).
    Proof.
      intros ?.
      reflexivity.
    Qed.

  Global Instance IsSubAlgebras_proper {Idx} :
    Proper (sa_sub ==> pointwise_relation _ sa_sub --> impl) (@IsSubAlgebras Idx).
  Proof.
    unfold IsSubAlgebras.
    intros ????????.
    now rewrite <- H0, H1.
  Qed.

  Global Instance IsSubAlgebras_eq_proper' {Idx} :
    Proper (sa_equiv ==> pointwise_relation _ sa_equiv ==> impl) (@IsSubAlgebras Idx).
  Proof.
    intros ??????.
    apply IsSubAlgebras_proper.
    - rewrite H; reflexivity.
    - symmetry in H0.
      rewrite H0.
      reflexivity.
  Qed.

  Global Instance IsSubAlgebras_eq_proper {Idx} :
    Proper (sa_equiv ==> pointwise_relation _ sa_equiv ==> iff) (@IsSubAlgebras Idx).
  Proof.
    intros ??????.
    split; apply IsSubAlgebras_eq_proper'; trivial
    ; now symmetry.
  Qed.


  Global Instance IsFiltration_proper' :
    Proper (pointwise_relation _ sa_equiv ==> impl) IsFiltration.
  Proof.
    intros ?????.
    rewrite <- (H n), <- (H (S n)).
    apply H0.
  Qed.
  
  Global Instance IsFiltration_proper :
    Proper (pointwise_relation _ sa_equiv ==> iff) IsFiltration.
  Proof.
      intros ???.
      split; apply IsFiltration_proper'; trivial.
      now symmetry.
  Qed.

  Section fs.
    Context (sas:nat->SigmaAlgebra Ts).
    Fixpoint filtrate_sa (n : nat) : SigmaAlgebra Ts
      := match n with
         | 0%nat => sas 0%nat
         | S k => union_sa (sas (S k)) (filtrate_sa k)
         end.
  End fs.

  Global Instance filtrate_sa_is_filtration (sas:nat->SigmaAlgebra Ts) :
    IsFiltration (filtrate_sa sas).
  Proof.
    intros n; simpl.
    apply union_sa_sub_r.
  Qed.

  Lemma filtrate_sa_sub (sas:nat->SigmaAlgebra Ts) (n : nat) : sa_sub (sas n) (filtrate_sa sas n).
  Proof.
    unfold filtrate_sa.
    destruct n; simpl.
    - reflexivity.
    - apply union_sa_sub_l.
  Qed.

  Lemma filtrate_sa_sub_all (sas:nat->SigmaAlgebra Ts) (dom : SigmaAlgebra Ts) (n : nat) :
    (forall k, k <= n -> sa_sub (sas k) dom) -> sa_sub (filtrate_sa sas n) dom.
  Proof.
    simpl.
    induction n; simpl; intros.
    - apply H; trivial.
    - apply union_sa_sub_both; eauto.
  Qed.

  Global Instance filtrate_sa_is_sub_algebra
         (sas:nat->SigmaAlgebra Ts) (dom : SigmaAlgebra Ts) {subs : IsSubAlgebras dom sas} :
    IsSubAlgebras dom (filtrate_sa sas).
  Proof.
    intros ?.
    apply filtrate_sa_sub_all; intros.
    apply subs.
  Qed.
  
  (* In the limit, its all the same *)
  Lemma filtrate_sa_countable_union (sas:nat->SigmaAlgebra Ts) :
    sa_equiv (countable_union_sa (filtrate_sa sas)) (countable_union_sa sas).
  Proof.
    unfold countable_union_sa.
    apply generated_sa_equiv_subs.
    split.
    - intros ? [n ?].
      revert x H.
      induction n; simpl in *; intros.
      + apply H0.
        red.
        eauto.
      + apply H.
        intros ? [?|?].
        * apply H0.
          red; eauto.
        * apply IHn; trivial.
    - intros ? [n ?].
      intros ??.
      apply H0.
      exists n.
      now apply filtrate_sa_sub.
  Qed.

  Lemma filtrate_sa_countable_union_sub  (sas:nat->SigmaAlgebra Ts) n :
    sa_sub (filtrate_sa sas n) (countable_union_sa sas).
  Proof.
    rewrite <- filtrate_sa_countable_union.
    apply countable_union_sa_sub.
  Qed.

  Global Instance filtrate_sa_sub_proper : Proper (pointwise_relation _ sa_sub ==> pointwise_relation _ sa_sub) filtrate_sa.
  Proof.
    intros ??? n.
    induction n; simpl.
    - apply H.
    - now apply union_sa_sub_proper. 
  Qed.

  Global Instance filtrate_sa_proper : Proper (pointwise_relation _ sa_equiv ==> pointwise_relation _ sa_equiv) filtrate_sa.
  Proof.
    intros ????.
    apply antisymmetry; apply filtrate_sa_sub_proper; intros n
    ; specialize (H n); apply sa_equiv_subs in H
    ; tauto.
  Qed.

End filtration.


  
