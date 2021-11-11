Require Import Classical.
Require Import ClassicalChoice.
Require Import FinFun.

Require Import List Permutation.
Require Import Morphisms EquivDec Program.

Require Import Utils DVector.
Require Export Event.

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
  red; simpl
  ; eauto.
Qed.

Definition all_included {T} (F:pre_event T -> Prop) : SigmaAlgebra T -> Prop
  := fun sa => forall (e:pre_event T), F e -> @sa_sigma _ sa e.

Global Instance all_included_proper {T} : Proper (equiv ==> equiv) (@all_included T).
Proof.
  repeat red; unfold equiv, event_equiv, all_included; intros.
  split; intros HH; intros; apply HH; firstorder.
Qed.

Instance generated_sa {T} (F:pre_event T -> Prop) : SigmaAlgebra T
  := sigma_algebra_intersection (all_included F).

Lemma generated_sa_sub {T} (F:pre_event T -> Prop) :
  forall x, F x -> @sa_sigma _ (generated_sa F) x.
Proof.
  unfold sa_sigma, generated_sa, sigma_algebra_intersection, all_included.
  eauto.
Qed.

Lemma generated_sa_sub' {T} (F:pre_event T -> Prop) :
  pre_event_sub F (@sa_sigma _ (generated_sa F)).
Proof.
  firstorder.
Qed.

Lemma generated_sa_minimal {T} (F:pre_event T -> Prop) (sa':SigmaAlgebra T) :
  (forall x, F x -> @sa_sigma _ sa' x) ->
  (forall x, @sa_sigma _ (generated_sa F) x -> @sa_sigma _ sa' x).
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
  (pre_event_sub E1 (sa_sigma (SigmaAlgebra:=(generated_sa E2)))).
Proof.
  firstorder.
Qed.
    
Lemma generated_sa_equiv_subs {X:Type} (E1 E2:pre_event X -> Prop) :
  generated_sa E1 === generated_sa E2 <->
  (pre_event_sub E1 (sa_sigma (SigmaAlgebra:=(generated_sa E2))) /\
   pre_event_sub E2 (sa_sigma (SigmaAlgebra:=(generated_sa E1)))).
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
         s₁ e₁ /\ s₂ e₂ ->
         e === (fun '(x₁, x₂) => e₁ x₁ /\ e₂ x₂).

Instance event_set_product_proper {T1 T2} : Proper (equiv ==> equiv ==> equiv) (@pre_event_set_product T1 T2).
Proof.
  repeat red.
  unfold equiv, pre_event_equiv, pre_event_set_product; simpl; intros.
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
  := generated_sa (pre_event_set_product (@sa_sigma _ sa₁) (@sa_sigma _ sa₂)).

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

Definition pre_event_push_forward {X Y:Type} (f:X->Y) (ex:pre_event X) : pre_event Y
  := fun y => exists x, f x = y /\ ex x.

Instance pre_event_push_forward_proper {X Y:Type} (f:X->Y) : Proper (equiv ==> equiv) (pre_event_push_forward f).
Proof.
  firstorder congruence.
Qed.

Definition pullback_sa_sigma {X Y:Type} (sa:SigmaAlgebra Y) (f:X->Y) : pre_event X -> Prop
  := fun (xe:pre_event X) =>
       exists ye:pre_event Y,
         sa_sigma (SigmaAlgebra:=sa) ye /\
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
    split; intros HH1 HH2
    ; now apply H0 in HH2.
Qed.
Next Obligation.
  unfold pullback_sa_sigma in *.
  exists pre_Ω.
  split.
  - apply sa_all.
  - unfold pre_Ω.
    tauto.
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
  sa_sigma y -> sa_sigma (SigmaAlgebra:=pullback_sa sa f) (pre_event_preimage f y).
Proof.
  simpl.
  unfold pre_event_preimage, pullback_sa_sigma.
  intros say.
  exists y.
  split; trivial.
  reflexivity.
Qed.

Definition union_sa {T : Type} (sa1 sa2:SigmaAlgebra T) :=
  generated_sa (pre_event_union (@sa_sigma _ sa1) 
                                (@sa_sigma _ sa2)).

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

Definition countable_union_sa {T : Type} (sas:nat->SigmaAlgebra T) :=
  generated_sa (pre_union_of_collection (fun n => (@sa_sigma _ (sas n)))).

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
Program Instance countable_sa (T:Type) : SigmaAlgebra T
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
  := generated_sa (pre_event_set_vector_product (vector_map (@sa_sigma _) sav)).

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

  Section fs.
    Context (sas:nat->SigmaAlgebra Ts).
    Fixpoint filtrate_sa (n : nat) : SigmaAlgebra Ts
      := match n with
         | 0%nat => trivial_sa Ts
         | S k => union_sa (sas k) (filtrate_sa k)
         end.
  End fs.

  Global Instance filtrate_sa_is_filtration (sas:nat->SigmaAlgebra Ts) :
    IsFiltration (filtrate_sa sas).
  Proof.
    intros n; simpl.
    apply union_sa_sub_r.
  Qed.

  Lemma filtrate_sa_sub (sas:nat->SigmaAlgebra Ts) (n : nat) : sa_sub (sas n) (filtrate_sa sas (S n)).
  Proof.
    apply union_sa_sub_l.
  Qed.

  Lemma filtrate_sa_sub_all (sas:nat->SigmaAlgebra Ts) (dom : SigmaAlgebra Ts) (n : nat) :
    (forall k, k < n -> sa_sub (sas k) dom) -> sa_sub (filtrate_sa sas n) dom.
  Proof.
    simpl.
    induction n; simpl; intros.
    - apply trivial_sa_sub.
    - apply union_sa_sub_both; eauto.
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
      + apply trivial_sa_sub; eauto.
      + apply H.
        intros ? [?|?].
        * apply H0.
          red; eauto.
        * apply IHn; trivial.
    - intros ? [n ?].
      intros ??.
      apply H0.
      exists (S n).
      now apply filtrate_sa_sub.
  Qed.

  Lemma filtrate_sa_countable_union_sub  (sas:nat->SigmaAlgebra Ts) n :
    sa_sub (filtrate_sa sas n) (countable_union_sa sas).
  Proof.
    rewrite <- filtrate_sa_countable_union.
    apply countable_union_sa_sub.
  Qed.

End filtration.
