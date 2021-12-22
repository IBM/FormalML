Require Import Program.Basics.
Require Import Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec.
Require Import Equivalence.
Require Import Classical ClassicalFacts ClassicalChoice.

Require Import Utils.
Import ListNotations.
Require Export Event SigmaAlgebras ProbSpace.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.
Section dynkin.

  Context {T:Type}.
  
  Class Pi_system (c:pre_event T -> Prop)
    := pi_inter : forall a, c a ->
            forall b, c b ->
                 c (pre_event_inter a b).

  Class Lambda_system (c:pre_event T -> Prop)
    := mk_lambda_system {
        lambda_Ω : c pre_Ω
      ; lambda_proper :> Proper (pre_event_equiv ==> iff) c
      ; lambda_complement {a} : c a -> c (pre_event_complement a)
      ; lambda_disjoint_countable_union (an : nat -> pre_event T) :
        (forall x, c (an x)) ->
        pre_collection_is_pairwise_disjoint an ->
        c (pre_union_of_collection an)
      }.

  Lemma lambda_none (c:pre_event T -> Prop) {c_lambda:Lambda_system c}: c pre_event_none.
  Proof.
    rewrite <- pre_event_not_all.
    apply lambda_complement.
    apply lambda_Ω.
  Qed.

  Lemma lambda_disjoint_list_union (c:pre_event T -> Prop) {c_lambda:Lambda_system c} l :
    (forall x, In x l -> c x) ->
    ForallOrdPairs pre_event_disjoint l ->
    c (pre_list_union l).
  Proof.
    intros.
    rewrite <- pre_list_union_union.
    apply lambda_disjoint_countable_union.
    - intros.
      unfold pre_list_collection.      
      destruct (nth_in_or_default x l pre_event_none); trivial.
      + now apply H.
      + rewrite e.
        now apply lambda_none.
    - now apply pre_list_collection_disjoint.
  Qed.

  Lemma lambda_disjoint_union (c:pre_event T -> Prop) {c_lambda:Lambda_system c} a b :
    c a -> c b -> pre_event_disjoint a b ->
    c (pre_event_union a b).
  Proof.
    intros.
    rewrite <- pre_list_union2.
    apply lambda_disjoint_list_union; trivial.
    - simpl; intuition congruence.
    - now repeat constructor.
  Qed.

  Lemma lambda_complement_alt (c:pre_event T -> Prop) {c_lambda:Lambda_system c} a b :
    c a -> c b ->
    pre_event_sub a b ->
    c (pre_event_diff b a).
  Proof.
    intros.
    rewrite pre_event_diff_derived.
    apply (lambda_proper (pre_event_complement (pre_event_union (pre_event_complement b) a))).
    - rewrite pre_event_complement_union.
      rewrite pre_event_not_not; try reflexivity.
      intros ?; apply classic.
    - apply lambda_complement.
      apply lambda_disjoint_union; trivial.
      + now apply lambda_complement.
      + firstorder.
  Qed.

  Lemma lambda_complement_alt_suffices (c:pre_event T -> Prop)
        (lambda_Ω : c pre_Ω)
        (lambda_proper : Proper (pre_event_equiv ==> iff) c)
        (lambda_complement : forall a b, c a -> c b ->
                                 pre_event_sub a b ->
                                 c (pre_event_diff b a))
        (lambda_disjoint_countable_union : forall (an : nat -> pre_event T),
            (forall x, c (an x)) ->
            pre_collection_is_pairwise_disjoint an ->
            c (pre_union_of_collection an)) : Lambda_system c.
  Proof.
    constructor; trivial.
    intros.
    specialize (lambda_complement a pre_Ω).
    rewrite pre_event_diff_true_l in lambda_complement.
    apply lambda_complement; trivial.
    apply pre_event_sub_true.
  Qed.

  Program Instance Pi_Lambda_sa (c:pre_event T -> Prop) (c_pi:Pi_system c) {c_lambda:Lambda_system c}
    : SigmaAlgebra T
    := {|
      sa_sigma := c
    |}.
  Next Obligation.
    rewrite make_pre_collection_disjoint_union.
    apply lambda_disjoint_countable_union.
    - intros.
      unfold make_pre_collection_disjoint.
      rewrite pre_event_diff_derived.
      apply pi_inter; trivial.
      rewrite pre_event_complement_union_of_collection.
      induction x.
      + unfold pre_event_complement, pre_inter_of_collection, pre_event_none.

        simpl; unfold pre_event_none.
        apply (lambda_proper pre_Ω).
        * firstorder.
        * apply lambda_Ω.
      + apply (lambda_proper (
                   pre_event_inter (pre_event_complement (collection x))
                                   (pre_inter_of_collection
                                      (fun n : nat => pre_event_complement (if Compare_dec.lt_dec n x then collection n else ∅))))).
        * intros ?.
          unfold pre_event_complement, pre_event_inter, pre_inter_of_collection, pre_event_none; simpl.
          unfold pre_event_none.
          split.
          -- intros [HH1 ?] ? HH2.
             match_destr_in HH2.
             destruct (PeanoNat.Nat.eq_dec n x).
             ++ congruence. 
             ++ apply (H0 n).
                match_destr; try lia.
          -- intros HH.
             split.
             ++ specialize (HH x).
                match_destr_in HH.
                lia.
             ++ intros.
                match_destr; [| tauto].
                specialize (HH n).
                match_destr_in HH.
                lia.
        * apply pi_inter; trivial.
          now apply lambda_complement.
    - apply make_pre_collection_disjoint_disjoint.
  Qed.
  Next Obligation.
    now apply lambda_complement.
  Qed.
  Next Obligation.
    apply lambda_Ω.
  Qed.

  Definition lambda_system_inter (coll:(pre_event T->Prop)->Prop) : pre_event T -> Prop
    := fun e => forall a, coll a -> a e.
  
  Instance lambda_system_inter_lambda (coll:(pre_event T->Prop)->Prop)
           {lcoll: forall (c:pre_event T -> Prop), coll c -> Lambda_system c} :
    Lambda_system (lambda_system_inter coll).
  Proof.
    unfold lambda_system_inter.
    constructor.
    - intros.
      specialize (lcoll _ H).
      apply lambda_Ω.
    - intros ???.
      split; intros ???
      ; specialize (lcoll _ H1).
      + rewrite <- H.
        apply (H0 _ H1).
      + rewrite H.
        apply (H0 _ H1).
    - intros.
      specialize (lcoll _ H0).
      apply lambda_complement.
      apply (H _ H0).
    - intros.
      specialize (lcoll _ H1).
      apply lambda_disjoint_countable_union; trivial.
      exact (fun x => H x _ H1).
  Qed.

  Lemma lambda_system_intersection_sub (coll:(pre_event T->Prop)->Prop)
    : forall s, coll s -> forall x, (lambda_system_inter coll) x ->  s x.
  Proof.
    firstorder.
  Qed.

  Definition lambda_all_included (F:pre_event T -> Prop) : (pre_event T->Prop)->Prop
    := fun l => Lambda_system l /\ forall (e:pre_event T), F e -> l e.

  Global Instance lambda_all_included_proper : Proper (equiv ==> equiv) lambda_all_included.
  Proof.
    firstorder.
  Qed.

  Instance lambda_all_included_lambda (F:pre_event T -> Prop) : forall c, lambda_all_included F c -> Lambda_system c.
  Proof.
    firstorder.
  Qed.

  Definition generated_lambda (F:pre_event T -> Prop) : pre_event T -> Prop
    := lambda_system_inter (lambda_all_included F).

  Global Instance generated_lambda_lambda (F:pre_event T -> Prop) : Lambda_system (generated_lambda F).
  Proof.
    apply lambda_system_inter_lambda.
    apply lambda_all_included_lambda.
  Qed.
  
  Lemma generated_lambda_sub (F:pre_event T -> Prop) :
    forall x, F x -> generated_lambda F x.
  Proof.
    firstorder.
  Qed.

  Lemma generated_lambda_minimal (F:pre_event T -> Prop) (c:(pre_event T->Prop)) {c_lambda:Lambda_system c} :
    pre_event_sub F c ->
    pre_event_sub (generated_lambda F) c.
  Proof.
    firstorder.
  Qed.

  Lemma pre_collection_is_pairwise_disjoint_inter (an:nat->pre_event T) (a:pre_event T) :
    pre_collection_is_pairwise_disjoint an ->
    pre_collection_is_pairwise_disjoint (fun n : nat => pre_event_inter a (an n)).
  Proof.
    firstorder.
  Qed.

  Instance pi_generated_lambda_pi (C:pre_event T -> Prop) {cpi:Pi_system C} : Pi_system (generated_lambda C).
  Proof.
    pose (Da := fun a => fun x => (generated_lambda C) (pre_event_inter a x)).
    assert (lambda_Da : forall a, (generated_lambda C) a -> Lambda_system (Da a)).
    {
      intros a D'a.
      unfold Da.
      apply lambda_complement_alt_suffices.
      - now rewrite pre_event_inter_true_r.
      - intros ???.
        now rewrite H.
      - intros.
        rewrite pre_event_inter_diff'.
        apply lambda_complement_alt; trivial.
        + apply generated_lambda_lambda.
        + now rewrite H1.
      - intros.
        rewrite pre_event_inter_countable_union_distr.
        apply lambda_disjoint_countable_union; trivial.
        now apply pre_collection_is_pairwise_disjoint_inter.
    }
    assert (Pi_almost:
               forall (a b : pre_event T),
                 C a -> generated_lambda C b ->
                 generated_lambda C (pre_event_inter a b)).
    {
      intros.
      assert (subc:pre_event_sub C (Da a)).
      {
        intros x ?? [??].
        apply H3.
        now apply cpi.
      }
      assert (subDa:pre_event_sub (generated_lambda C) (Da a)).
      {
        apply generated_lambda_minimal; trivial.
        apply lambda_Da.
        now apply generated_lambda_sub.
      }
      now apply subDa.
    }
    intros ????.
    assert (subc:pre_event_sub C (Da b)).
    {
      intros ??.
      unfold Da.
      rewrite pre_event_inter_comm.
      apply Pi_almost; trivial.
    }
    apply generated_lambda_minimal in subc; [| auto].
    rewrite pre_event_inter_comm.
    now apply subc.
  Qed.    

  Instance pi_generated_lambda_sa (C:pre_event T -> Prop) {cpi:Pi_system C} : SigmaAlgebra T
    := Pi_Lambda_sa (generated_lambda C) (pi_generated_lambda_pi C).

  Instance SigmaAlgebra_Lambda (sa:SigmaAlgebra T) : Lambda_system (fun x => sa_sigma x).
  Proof.
    constructor; simpl.
    - apply sa_all.
    - intros ???.
      now apply sa_proper.
    - intros.
      now apply sa_complement.
    - intros.
      now apply sa_countable_union.
  Qed.

  Instance SigmaAlgebra_Pi (sa:SigmaAlgebra T) : Pi_system (fun x => sa_sigma x).
  Proof.
    intros ????.
    now apply sa_inter.
  Qed.

  Lemma pi_generated_lambda_generated_sa (C:pre_event T -> Prop) {cpi:Pi_system C} :
    sa_equiv (pi_generated_lambda_sa C)
             (generated_sa C).
  Proof.
    split; simpl; intros HH.
    - intros ??; simpl.
      apply HH.
      red.
      split.
      + apply SigmaAlgebra_Lambda.
      + auto.
    - apply (HH (pi_generated_lambda_sa C)).
      red; simpl.
      apply generated_lambda_sub.
  Qed.
  
  Theorem Dynkin (C:pre_event T -> Prop) (D:pre_event T -> Prop) {cpi:Pi_system C} {dlambda:Lambda_system D} :
    pre_event_sub C D -> pre_event_sub (@sa_sigma _ (generated_sa C)) D.
  Proof.
    intros csub.
    generalize (pi_generated_lambda_generated_sa C).
    unfold sa_equiv; simpl; intros HH.
    rewrite <- HH.
    now apply generated_lambda_minimal.
  Qed.

End dynkin.

Section extension_uniqueness.

  Definition generated_sa_base_event {T} {C:pre_event T -> Prop} {a} (Ca:C a) :
    event (generated_sa C)
    := exist _ a (generated_sa_sub _ _ Ca).
  
  Lemma pi_prob_extension_unique {T} (C:pre_event T -> Prop) {cpi:Pi_system C}
        (P1 P2:ProbSpace (generated_sa C)) :
    (forall a (Ca:C a), ps_P (ProbSpace:=P1) (generated_sa_base_event Ca) = ps_P (ProbSpace:=P2) (generated_sa_base_event Ca)) ->
    (forall a, ps_P (ProbSpace:=P1) a = ps_P (ProbSpace:=P2) a).
  Proof.
    intros HH.
    pose (A := fun e => exists pf, ps_P (ProbSpace:=P1) (exist _ e pf) = ps_P (ProbSpace:=P2) (exist _ e pf)).
    assert (csub : pre_event_sub C A).
    {
      intros ??; red; eauto.
    } 
    assert (asub : pre_event_sub A (@sa_sigma _ (generated_sa C))).
    {
      now intros ? [??].
    }     

    assert (lambda_A : Lambda_system A).
    {
      subst A.
      constructor.
      - exists sa_all.
        rewrite (ps_proper _ Ω) by reflexivity.
        rewrite ps_one.
        rewrite (ps_proper _ Ω) by reflexivity.
        now rewrite ps_one.
      - intros ???.
        split; intros [??].
        + assert (say:sa_sigma (SigmaAlgebra:=(@generated_sa T C)) y).
          {
            now rewrite <- H.
          }
          exists say.
          etransitivity; [etransitivity |]; [| apply H0 | ].
          * now apply ps_proper; red; simpl; symmetry.
          * now apply ps_proper; red; simpl.
        + assert (sax:sa_sigma (SigmaAlgebra:=(@generated_sa T C)) x).
          {
            now rewrite H.
          }
          exists sax.
          etransitivity; [etransitivity |]; [| apply H0 | ].
          * now apply ps_proper; red; simpl; symmetry.
          * now apply ps_proper; red; simpl.
      - intros ? [??].
        exists (sa_complement _ x).
        replace (exist (fun e : pre_event T => sa_sigma e) (pre_event_complement a) (sa_complement a x))
          with (event_complement (σ:=generated_sa C) (exist _ a x))
          by reflexivity.
        repeat rewrite ps_complement.
        apply Rcomplements.Rminus_eq_compat_l.
        etransitivity; [etransitivity |]; [| apply H | ].
          * now apply ps_proper; red; simpl; symmetry.
          * now apply ps_proper; red; simpl.
      - intros.
        assert (sa_an:forall x, sa_sigma (SigmaAlgebra:=(@generated_sa T C)) (an x)) by eauto.
        exists (sa_countable_union _ sa_an).
        assert (eqq1:event_equiv
                  (exist (fun e : pre_event T => sa_sigma e) (pre_union_of_collection an) (sa_countable_union an sa_an)) 
                  (union_of_collection (σ:=generated_sa C) (fun n => exist _ (an n) (sa_an n)))).
        {
          rewrite union_of_collection_as_pre; intros ?; simpl.
          unfold collection_pre; simpl.
          reflexivity.
        } 
        rewrite eqq1.
        assert (disj:collection_is_pairwise_disjoint (σ:=generated_sa C) (fun n : nat => exist sa_sigma (an n) (sa_an n))).
        {
          now apply collection_is_pairwise_disjoint_pre.
        }
        generalize (ps_countable_disjoint_union _ disj (ProbSpace:=P1))
        ; intros HH1.
        generalize (ps_countable_disjoint_union _ disj (ProbSpace:=P2))
        ; intros HH2.
        red in HH1, HH2.
        eapply infinite_sum'_unique; try eapply HH1.
        eapply infinite_sum'_ext; try apply HH2.
        intros; simpl.
        destruct (H x).
        etransitivity; [etransitivity |]; [| apply H1 | ].
          * now apply ps_proper; red; simpl; symmetry.
          * now apply ps_proper; red; simpl.
    }
    apply Dynkin in csub; trivial.
    assert (pre_event_equiv A (@sa_sigma _ (generated_sa C)))
      by now apply antisymmetry.
    intros.
    destruct a.
    assert (Ax :A x) by now apply H.
    destruct Ax.
    etransitivity; [etransitivity |]; [| apply H0 | ].
    * now apply ps_proper; red; simpl; symmetry.
    * now apply ps_proper; red; simpl.
      Unshelve.
      trivial.
  Qed.

End extension_uniqueness.
