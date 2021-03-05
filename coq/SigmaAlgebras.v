Require Import Classical.
Require Import ClassicalChoice.
Require Import FinFun.

Require Import List.
Require Import Morphisms EquivDec.

Require Import Utils DVector.
Require Import ProbSpace.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

Local Open Scope prob.

Lemma classic_event_lem {T} : forall a:event T, event_lem a.
Proof.
  intros ??; apply classic.
Qed.

Lemma event_complement_swap_classic {T} (A B:event T) : ¬ A === B <-> A === ¬ B.
Proof.
  intros.
  apply event_complement_swap; auto using classic_event_lem.
Qed.

Program Instance trivial_sa (T:Type) : SigmaAlgebra T
  := {
      sa_sigma (f:event T) := (f === ∅ \/ f === Ω)
    }.
Next Obligation.
  (* sigh. more classical reasoning needed *)
  destruct (classic (exists n, collection n === Ω))
  ; [right|left]; firstorder.
Qed.
Next Obligation.
  firstorder.
Qed.
Next Obligation.
  firstorder.
Qed.

Program Instance discrete_sa (T:Type) : SigmaAlgebra T
  := {
      sa_sigma := fun _ => True 
    }.
                 
Program Instance subset_sa (T:Type) (A:event T) : SigmaAlgebra T
  := {
      sa_sigma f := (f === ∅ \/ f === A \/ f === ¬ A \/ f === Ω)
    }.
Next Obligation.
  (* sigh. more classical reasoning needed *)
  destruct (classic (exists n, collection n === Ω))
  ; [repeat right; firstorder | ].
  destruct (classic (exists n, collection n === A))
  ; destruct (classic (exists n, collection n === ¬ A)).
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
  replace event_equiv with (@equiv (event T) _ event_equiv_equiv) in * by reflexivity.
  repeat rewrite event_complement_swap_classic.
  rewrite event_not_not by auto using classic_event_lem.
  autorewrite with prob.
  tauto.
Qed.
Next Obligation.
  repeat right.
  reflexivity.
Qed.

Definition is_partition {T} (part:nat->event T)
  := collection_is_pairwise_disjoint part 
     /\ union_of_collection part === Ω.

Definition sub_partition {T} (part1 part2 : nat -> event T)
  := forall n, part1 n === part2 n \/ part1 n === ∅.

Instance sub_partition_pre {T} : PreOrder (@sub_partition T).
Proof.
  constructor; red; unfold sub_partition; intuition eauto.
  - left; reflexivity.
  - specialize (H n).
    specialize (H0 n).
    intuition.
    + rewrite H1.
      tauto.
    + rewrite H1.
      tauto.
Qed.

Definition in_partition_union {T} (part:nat->event T) (f:event T) : Prop
  := exists subpart, sub_partition subpart part /\ (union_of_collection subpart) === f.

Instance in_partition_union_proper {T} (part:nat->event T) :
  Proper (event_equiv ==> iff) (in_partition_union part).
Proof.
  cut (Proper (event_equiv ==> Basics.impl) (in_partition_union part))
  ; unfold in_partition_union, Basics.impl.
  { intros HH x y xyeq.
    intuition eauto.
    symmetry in xyeq.
    intuition eauto.
  }
  intros x y xyeq [sub [sp uc]].
  rewrite xyeq in uc.
  eauto.
Qed.

Lemma sub_partition_diff {T} (sub part:nat->event T) :
  sub_partition sub part ->
  sub_partition (fun x : nat => part x \ sub x) part.
Proof.
  intros is_sub n.
  specialize (is_sub n).
  destruct is_sub as [eqq|eqq]
  ; rewrite eqq
  ; autorewrite with prob
  ; intuition.
Qed.

Program Instance countable_partition_sa {T} (part:nat->event T) (is_part:is_partition part) : SigmaAlgebra T
  := {
      sa_sigma := in_partition_union part
    }.
Next Obligation.
    unfold in_partition_union in *.
    unfold is_partition in *.
    apply choice in H.
    destruct H as [partish pH].
    exists (fun n => union_of_collection (fun x => partish x n)).
    split.
    + intros n.
      unfold union_of_collection.

      unfold union_of_collection in *.
      unfold is_partition in is_part.
      destruct (classic ((fun t : T => exists n0 : nat, partish n0 n t) === ∅)); [eauto | ].
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
    + intros x; unfold union_of_collection in *.
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
  exists (fun x => part x \ sub x).
  split.
  + apply sub_partition_diff; trivial.
  + intros x.
    unfold union_of_collection, event_complement, event_diff.
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
        unfold union_of_collection in tot.
        assert (xin:Ω x) by firstorder.
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
  := { sa_sigma := fun e => forall sa, coll sa -> @sa_sigma _ sa e
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
  eauto.
Qed.

Definition all_included {T} (F:event T -> Prop) : SigmaAlgebra T -> Prop
  := fun sa => forall (e:event T), F e -> @sa_sigma _ sa e.

Global Instance all_included_proper {T} : Proper (equiv ==> equiv) (@all_included T).
Proof.
  repeat red; unfold equiv, event_equiv, all_included; intros.
  split; intros HH; intros; apply HH; firstorder.
Qed.

Instance generated_sa {T} (F:event T -> Prop) : SigmaAlgebra T
  := sigma_algebra_intersection (all_included F).

Lemma generated_sa_sub {T} (F:event T -> Prop) :
  forall x, F x -> @sa_sigma _ (generated_sa F) x.
Proof.
  unfold sa_sigma, generated_sa, sigma_algebra_intersection, all_included.
  eauto.
Qed.

Lemma generated_sa_minimal {T} (F:event T -> Prop) (sa':SigmaAlgebra T) :
  (forall x, F x -> @sa_sigma _ sa' x) ->
  (forall x, @sa_sigma _ (generated_sa F) x -> @sa_sigma _ sa' x).
Proof.
  intros ff x sax.
  unfold sa_sigma, generated_sa, sigma_algebra_intersection, all_included in sax.
  eauto.
Qed.

Inductive prob_space_closure {T} : (event T->Prop) -> event T -> Prop
  :=
  | psc_all p : prob_space_closure p Ω
  | psc_refl (p:event T->Prop) q : p q -> prob_space_closure p q
  | psc_countable p (collection: nat -> event T) :
      (forall n, prob_space_closure p (collection n)) ->
      prob_space_closure p (union_of_collection collection)
  | psc_complement p q : prob_space_closure p q -> prob_space_closure p (¬ q)
.

Program Instance closure_sigma_algebra {T} (F:event T -> Prop) : SigmaAlgebra T
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

Theorem generated_sa_closure {T} (F:event T -> Prop) : generated_sa F === closure_sigma_algebra F.
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

Definition event_set_product {T₁ T₂} (s₁ : event T₁ -> Prop) (s₂ : event T₂ -> Prop) : event (T₁ * T₂) -> Prop
  := fun (e:event (T₁ * T₂)) =>
       exists e₁ e₂,
         s₁ e₁ /\ s₂ e₂ ->
         e === (fun '(x₁, x₂) => e₁ x₁ /\ e₂ x₂).

Instance event_set_product_proper {T1 T2} : Proper (equiv ==> equiv ==> equiv) (@event_set_product T1 T2).
Proof.
  repeat red.
  unfold equiv, event_equiv, event_set_product; simpl; intros.
  split; intros [x2 [x3 HH]].
  - unfold equiv in *.
    exists x2, x3.
    intros [??]; apply HH.
    firstorder.
  - unfold equiv in *.
    exists x2, x3.
    intros [??]; apply HH.
    firstorder.
Qed.

Instance product_sa {T₁ T₂} (sa₁:SigmaAlgebra T₁) (sa₂:SigmaAlgebra T₂) : SigmaAlgebra (T₁ * T₂)
  := generated_sa (event_set_product (@sa_sigma _ sa₁) (@sa_sigma _ sa₂)).

Global Instance product_sa_proper {T1 T2} : Proper (equiv ==> equiv ==> equiv) (@product_sa T1 T2).
Proof.
  repeat red; unfold equiv, sa_equiv; simpl.
  intros.
  split; intros HH.
  - intros.
    apply HH.
    revert H1.
    apply all_included_proper.
    rewrite H, H0.
    reflexivity.
  - intros.
    apply HH.
    revert H1.
    apply all_included_proper.
    rewrite H, H0.
    reflexivity.
Qed.

Definition event_pullback {X Y:Type} (f:X->Y) (ex:event X) : event Y
  := fun y => exists x, f x = y.

Instance event_pullback_proper {X Y:Type} (f:X->Y) : Proper (event_equiv ==> event_equiv) (event_pullback f).
Proof.
  repeat red; intuition.
Qed.

Instance pullback_sa {X Y:Type} (sa:SigmaAlgebra Y) (f:X->Y) : SigmaAlgebra X
  := generated_sa (fun e => sa_sigma (event_pullback f e)).

Instance pullback_sa_proper {X Y:Type} : Proper (equiv ==> (pointwise_relation X equiv) ==> equiv) (@pullback_sa X Y).
Proof.
  unfold pointwise_relation, equiv.
  repeat red; intros; simpl.
  split; intros HH; intros.
  - apply HH.
    revert H1.
    apply all_included_proper; intros e.
    unfold event_pullback.
    unfold sa_equiv in H.
    
    split; intros HH2.
    + apply H.
      revert HH2.
      apply sa_proper.
      red; intros.
      split; intros [??]; subst; eauto.
    + apply H.
      revert HH2.
      apply sa_proper.
      red; intros.
      split; intros [??]; subst; eauto.
  - apply HH.
    revert H1.
    apply all_included_proper; intros e.
    unfold event_pullback.
    unfold sa_equiv in H.
    
    split; intros HH2.
    + apply H.
      revert HH2.
      apply sa_proper.
      red; intros.
      split; intros [??]; subst; eauto.
    + apply H.
      revert HH2.
      apply sa_proper.
      red; intros.
      split; intros [??]; subst; eauto.
Qed.

Definition is_countable {T} (e:event T)
  := exists (coll:nat -> T -> Prop),
    (forall n t1 t2, coll n t1 -> coll n t2 -> t1 = t2) /\
    e === (fun a => exists n, coll n a).

Lemma is_countable_empty {T} : @is_countable T ∅.
Proof.
  exists (fun n t => False).
  firstorder.
Qed.

Instance is_countable_proper_sub {T} : Proper (event_sub --> Basics.impl) (@is_countable T).
Proof.
  unfold Proper, respectful, Basics.impl, Basics.flip, is_countable.
  intros x y sub [c cx].
  red in sub.
  exists (fun n t =>
            c n t /\ y t).
  firstorder.
Qed.

Instance is_countable_proper {T} : Proper (event_equiv ==> iff) (@is_countable T).
Proof.
  unfold Proper, respectful.
  intros x y eqq.
  split; intros.
  - apply (is_countable_proper_sub x y); trivial.
    apply event_equiv_sub; trivial.
    symmetry; trivial.
  - apply (is_countable_proper_sub y x); trivial.
    apply event_equiv_sub; trivial.
Qed.

Lemma union_of_collection_sup {T} (coll:nat->event T) n : (coll n) ≤ (union_of_collection coll).
Proof.
  unfold event_sub, union_of_collection.
  eauto.
Qed.


Definition F {T} (coll:nat->event T) (n:nat) : ({x:T | coll n x} -> nat) -> Prop
  := fun f => Injective f.


Lemma union_of_collection_is_countable {T} (coll:nat->event T) :
  (forall n : nat, is_countable (coll n)) -> is_countable (union_of_collection coll).
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
Program Instance countable_sa (T:Type) : SigmaAlgebra T
  := {
      sa_sigma (f:event T) := is_countable f \/ is_countable (¬ f)
    }.
Next Obligation.
  destruct (classic (forall n, is_countable (collection n))).
  + (* they are all countable *)
    left.
    apply union_of_collection_is_countable; trivial.
  + apply not_all_ex_not in H0.
    destruct H0 as [n ncn].
    assert (iscnn:is_countable (¬ collection n)).
    { destruct (H n); intuition. }
    generalize (union_of_collection_sup collection n); intros subs.
    apply event_complement_sub_proper in subs.
    rewrite <- subs in iscnn.
    eauto.
Qed.
Next Obligation.
  rewrite event_not_not by auto using classic_event_lem.
  tauto.
Qed.
Next Obligation.
  right.
  rewrite event_not_all.
  apply is_countable_empty.
Qed.

(* vector product *)
Definition event_set_vector_product {T} {n} (v:vector ((event T)->Prop) n) : event (vector T n) -> Prop
  := fun (e:event (vector T n)) =>
       exists (sub_e:vector (event T) n),
         (forall i pf, (vector_nth i pf v) (vector_nth i pf sub_e))
         /\
         e === (fun (x:vector T n) => forall i pf, (vector_nth i pf sub_e) (vector_nth i pf x)).

Instance event_set_vector_product_proper {n} {T} : Proper (equiv ==> equiv) (@event_set_vector_product T n).
Proof.
  repeat red.
  unfold equiv, event_equiv, event_set_vector_product; simpl; intros.
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
  := generated_sa (event_set_vector_product (vector_map (@sa_sigma _) sav)).

Global Instance vector_sa_proper {T} {n} : Proper (equiv ==> equiv) (@vector_sa T n).
Proof.
  repeat red; unfold equiv, sa_equiv; simpl.
  intros.
  split; intros HH.
  - intros.
    apply HH.
    revert H0.
    apply all_included_proper.
    apply event_set_vector_product_proper.
    intros ??.
    repeat rewrite vector_nth_map.
    specialize (H i pf).
    apply H.
  - intros.
    apply HH.
    revert H0.
    apply all_included_proper.
    apply event_set_vector_product_proper.
    intros ??.
    repeat rewrite vector_nth_map.
    specialize (H i pf).
    symmetry.
    apply H.
Qed.

Definition is_partition_list {T} (l:list (event T)) :=
  ForallOrdPairs event_disjoint l /\ event_equiv (list_union l) Ω.

Lemma is_partition_list_partition {T} {l:list (event T)} :
  is_partition_list l ->
  SigmaAlgebras.is_partition (list_collection l event_none).
Proof.
  intros [??].
  split.
  - now apply list_collection_disjoint.
  - rewrite list_union_union, H0.
    reflexivity.
Qed.

Instance list_partition_sa {T} (l:list (event T)) (is_part:is_partition_list l) :
  SigmaAlgebra T := countable_partition_sa
                      (list_collection l event_none)
                      (is_partition_list_partition is_part).

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
