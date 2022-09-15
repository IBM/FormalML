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
        (lambda_diff : forall a b, c a -> c b ->
                                   pre_event_sub a b ->
                                   c (pre_event_diff b a))
        (lambda_disjoint_countable_union : forall (an : nat -> pre_event T),
            (forall x, c (an x)) ->
            pre_collection_is_pairwise_disjoint an ->
            c (pre_union_of_collection an)) : Lambda_system c.
  Proof.
    constructor; trivial.
    intros.
    specialize (lambda_diff a pre_Ω).
    rewrite pre_event_diff_true_l in lambda_diff.
    apply lambda_diff; trivial.
    apply pre_event_sub_true.
  Qed.

  Lemma pre_collection_increasing_trans (an : nat -> pre_event T) (x : nat) :
    (forall x, pre_event_sub (an x) (an (S x))) ->
    forall x0,
      x0 < S x -> pre_event_sub (an x0) (an x).
  Proof.
    intros.
    pose (h := x - x0).
    replace x with (x0 + h) by lia.
    induction h.
    - now replace (x0 + 0) with x0 by lia.
    - unfold pre_event_sub in *.
      intros.
      specialize (IHh x1 H1).
      specialize (H (x0 + h) x1 IHh).
      now replace (x0 + S h) with (S (x0 + h)) by lia.
  Qed.

  Lemma lambda_union_alt  (c:pre_event T -> Prop) {c_lambda:Lambda_system c}  :
    forall (an : nat -> pre_event T),
      (forall x, c (an x)) ->
      (forall x, pre_event_sub (an x) (an (S x))) ->
      c (pre_union_of_collection an).
  Proof.
    intros.
    pose (bn := make_pre_collection_disjoint an).
    generalize (lambda_complement_alt c); intros.
    destruct c_lambda.
    specialize (lambda_disjoint_countable_union0 bn).
    cut_to lambda_disjoint_countable_union0.
    - revert lambda_disjoint_countable_union0.
      apply lambda_proper0.
      apply make_pre_collection_disjoint_union.
    - induction x.
      + specialize (H 0).
        revert H.
        apply lambda_proper0.
        apply make_pre_collection_disjoint0.
      + unfold bn.
        unfold make_pre_collection_disjoint.
        specialize (H1 (an x) (an (S x))).
        cut_to H1; try easy.
        revert H1.
        apply lambda_proper0.
        intro z.
        assert (pre_event_equiv  (pre_union_of_collection
                                    (fun y : nat =>
                                       if Compare_dec.lt_dec y (S x) then an y else pre_event_none))
                                 (an x)).
        {
          intro w.
          unfold pre_union_of_collection.
          split; intros.
          - destruct H1.
            match_destr_in H1; try easy.
            revert H1.
            now apply pre_collection_increasing_trans.
          - exists x.
            match_destr.
            lia.
        }
        specialize (H1 z).
        unfold pre_event_diff.
        now rewrite H1.
    - apply make_pre_collection_disjoint_disjoint.
  Qed.

  Lemma pre_list_union_take_Sn (an : nat -> pre_event T) (x : nat):
    pre_event_equiv
      (pre_list_union (collection_take an (S x)))
      (pre_event_union (pre_list_union (collection_take an x)) (an x)).
  Proof.
    rewrite collection_take_Sn.
    rewrite pre_list_union_app.
    now rewrite pre_list_union_singleton.
  Qed.

  Lemma lambda_union_alt_suffices (c:pre_event T -> Prop) 
        (lambda_Ω : c pre_Ω)
        (lambda_proper : Proper (pre_event_equiv ==> iff) c)
        (lambda_diff : forall a b, c a -> c b ->
                                   pre_event_sub a b ->
                                   c (pre_event_diff b a))
        (lambda_union_increasing : forall (an : nat -> pre_event T),
            (forall x, c (an x)) ->
            (forall x, pre_event_sub (an x) (an (S x))) ->            
            c (pre_union_of_collection an)) : Lambda_system c.
  Proof.
    assert (forall a : pre_event T, c a -> c (pre_event_complement a)).
    {
      intros.
      specialize (lambda_diff a pre_Ω).
      rewrite pre_event_diff_true_l in lambda_diff.
      apply lambda_diff; trivial.
      apply pre_event_sub_true.
    }
    constructor; trivial.
    intros.
    pose (bn := fun n => pre_list_union (collection_take an (S n))).
    specialize (lambda_union_increasing bn).
    cut_to lambda_union_increasing.
    - revert lambda_union_increasing.
      apply lambda_proper.
      intro z.
      unfold pre_union_of_collection.
      split; intros; destruct H2.
      + exists x.
        unfold bn.
        unfold pre_list_union, collection_take.
        exists (an x).
        split; trivial.
        apply in_map_iff.
        exists x.
        split; trivial.
        apply in_seq.
        lia.
      + unfold bn in H2.
        unfold pre_list_union, collection_take in H2.
        destruct H2 as [? [? ?]].
        apply in_map_iff in H2.
        destruct H2 as [? [? ?]].
        exists x1.
        now rewrite <- H2 in H3.
    - induction x.
      + unfold bn.
        unfold pre_list_union, collection_take.
        specialize (H0 0%nat).
        revert H0.
        apply lambda_proper.
        intro z.
        split; intros.
        * destruct H0 as [? [? ?]].
          apply in_map_iff in H0.
          destruct H0 as [? [? ?]].
          apply in_seq in H3.
          assert (x0 = 0%nat) by lia.
          rewrite H4 in H0.
          now rewrite <- H0 in H2.
        * exists (an 0); split; trivial.
          apply in_map_iff.
          exists 0; split; trivial.
          apply in_seq.
          lia.
      + assert (pre_event_equiv
                  (bn (S x))
                  (pre_event_union (an (S x)) (bn x))).
        {
          unfold bn.
          rewrite (pre_list_union_take_Sn an (S x)).
          now rewrite pre_event_union_comm.
        }
        assert (pre_event_equiv
                  (bn (S x))
                  (pre_event_complement
                     (pre_event_diff (pre_event_complement (an (S x)))
                                     (bn x)))).
        {
          rewrite H2.
          intro z.
          unfold pre_event_union, pre_event_diff, pre_event_complement; simpl.
          tauto.          
        }
        rewrite H3.
        apply H.
        apply lambda_diff; trivial.
        * now apply H.
        * unfold pre_event_sub, pre_event_complement.
          intros.
          unfold bn, pre_list_union, collection_take in H4.
          destruct H4 as [? [? ?]].
          apply in_map_iff in H4.
          destruct H4 as [? [? ?]].
          rewrite <- H4 in H5.
          apply in_seq in H6.
          specialize (H1 x2 (S x)).
          cut_to H1; try lia.
          specialize (H1 x0).
          tauto.
    - unfold pre_event_sub, bn.
      unfold pre_list_union, collection_take.
      intros.
      destruct H2 as [? [? ?]].
      apply in_map_iff in H2.
      destruct H2 as [? [? ?]].
      exists x1.
      split; trivial.
      rewrite <- H2.
      apply in_map_iff.
      exists x2; split; trivial.
      apply in_seq.
      apply in_seq in H4.
      lia.
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

  Instance SigmaAlgebra_Lambda (sa:SigmaAlgebra T) : Lambda_system (fun x => sa_sigma _ x).
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

  Instance SigmaAlgebra_Pi (sa:SigmaAlgebra T) : Pi_system (fun x => sa_sigma _ x).
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
    pre_event_sub C D -> pre_event_sub (sa_sigma (generated_sa C)) D.
  Proof.
    intros csub.
    generalize (pi_generated_lambda_generated_sa C).
    unfold sa_equiv; simpl; intros HH.
    rewrite <- HH.
    now apply generated_lambda_minimal.
  Qed.

  Lemma Pi_system_inter (C1 C2 : pre_event T -> Prop) {cp1 : Pi_system C1} {cp2 : Pi_system C2} :
    Pi_system (fun x => exists e1 e2, C1 e1 /\ C2 e2 /\ pre_event_equiv x (pre_event_inter e1 e2)).
    Proof.
      unfold Pi_system in *.
      intros.
      destruct H as [? [? [? [? ?]]]].
      destruct H0 as [? [? [? [? ?]]]].      
      exists (pre_event_inter x x1).
      exists (pre_event_inter x0 x2).
      split.
      - now apply cp1.
      - split.
        + now apply cp2.
        + rewrite H2, H4.
          firstorder.
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
    assert (asub : pre_event_sub A (sa_sigma (generated_sa C))).
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
        + assert (say:sa_sigma (@generated_sa T C) y).
          {
            now rewrite <- H.
          }
          exists say.
          etransitivity; [etransitivity |]; [| apply H0 | ].
          * now apply ps_proper; red; simpl; symmetry.
          * now apply ps_proper; red; simpl.
        + assert (sax:sa_sigma (@generated_sa T C) x).
          {
            now rewrite H.
          }
          exists sax.
          etransitivity; [etransitivity |]; [| apply H0 | ].
          * now apply ps_proper; red; simpl; symmetry.
          * now apply ps_proper; red; simpl.
      - intros ? [??].
        exists (sa_complement _ x).
        replace (exist (fun e : pre_event T => sa_sigma _ e) (pre_event_complement a) (sa_complement a x))
          with (event_complement (σ:=generated_sa C) (exist _ a x))
          by reflexivity.
        repeat rewrite ps_complement.
        apply Rcomplements.Rminus_eq_compat_l.
        etransitivity; [etransitivity |]; [| apply H | ].
          * now apply ps_proper; red; simpl; symmetry.
          * now apply ps_proper; red; simpl.
      - intros.
        assert (sa_an:forall x, sa_sigma (@generated_sa T C) (an x)) by eauto.
        exists (sa_countable_union _ sa_an).
        assert (eqq1:event_equiv
                  (exist (fun e : pre_event T => sa_sigma _ e) (pre_union_of_collection an) (sa_countable_union an sa_an)) 
                  (union_of_collection (σ:=generated_sa C) (fun n => exist _ (an n) (sa_an n)))).
        {
          rewrite union_of_collection_as_pre; intros ?; simpl.
          unfold collection_pre; simpl.
          reflexivity.
        } 
        rewrite eqq1.
        assert (disj:collection_is_pairwise_disjoint (σ:=generated_sa C) (fun n : nat => exist (sa_sigma _) (an n) (sa_an n))).
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
    assert (pre_event_equiv A (sa_sigma (generated_sa C)))
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
