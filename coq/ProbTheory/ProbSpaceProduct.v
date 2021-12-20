Require Import Program.Basics.
Require Import Coquelicot.Coquelicot.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.
Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec.
Require Import Equivalence.
Require Import Classical ClassicalFacts ClassicalChoice.
Require Ensembles.

Require Import Utils DVector.
Import ListNotations.
Require Export Event SigmaAlgebras ProbSpace.
Require Export RandomVariable VectorRandomVariable.
Require Import ClassicalDescription.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

Section pre_make_disjoint.
  Context {T:Type}.
  
  Definition make_pre_collection_disjoint (coll:nat->pre_event T) : nat -> pre_event T
    := fun x => pre_event_diff (coll x) ((pre_union_of_collection (fun y =>
                                                                  if lt_dec y x
                                                                  then coll y
                                                                  else ∅))).

  Lemma make_pre_collection_disjoint_sub (En:nat -> pre_event T) n : pre_event_sub (make_pre_collection_disjoint En n) (En n).
Proof.
  now intros x [??].
Qed.

Lemma make_pre_collection_disjoint0 (En:nat -> pre_event T) :
  pre_event_equiv (make_pre_collection_disjoint En 0) (En 0%nat).
Proof.
  unfold make_pre_collection_disjoint.
  red; intros.
  split; intros.
  - destruct H; trivial.
  - split; trivial.
    unfold pre_union_of_collection.
    intros [? HH].
    match_destr_in HH.
    lia.
Qed.

Hint Rewrite @make_pre_collection_disjoint0 : prob.

Lemma make_pre_collection_disjoint_in (coll:nat->pre_event T) (x:nat) (e:T) :
  make_pre_collection_disjoint coll x e <->
  (coll x) e /\ forall y, (y < x)%nat -> ~ (coll y) e.
Proof.
  split.
  - unfold make_pre_collection_disjoint; intros HH.
    destruct HH as [H1 H2].
    split; trivial.
    intros y ylt cy.
    apply H2.
    exists y.
    destruct (lt_dec y x); intuition.
  - intros [ce fce].
    unfold make_pre_collection_disjoint.
    split; trivial.
    unfold pre_union_of_collection.
    intros [n Hn].
    destruct (lt_dec n x); trivial.
    eapply fce; eauto.
Qed.
  
Lemma make_pre_collection_disjoint_disjoint (coll:nat->pre_event T) :
  pre_collection_is_pairwise_disjoint (make_pre_collection_disjoint coll).
Proof.
  intros x y xyneq e e1 e2.
  apply make_pre_collection_disjoint_in in e1.
  apply make_pre_collection_disjoint_in in e2.
  destruct e1 as [H11 H12].
  destruct e2 as [H21 H22].
  destruct (not_eq _ _ xyneq) as [xlt|ylt].
  - eapply H22; eauto.
  - eapply H12; eauto.
Qed.

   
  Lemma make_pre_collection_disjoint_union (coll:nat->pre_event T) :
    pre_event_equiv (pre_union_of_collection coll)
                    (pre_union_of_collection (make_pre_collection_disjoint coll)).
  Proof.
    unfold pre_union_of_collection.
    intros t.
    split; intros [n Hn].
    - simpl.
      generalize (excluded_middle_entails_unrestricted_minimization classic (fun n => coll n t))
      ; intros HH.
      specialize (HH _ Hn).
      destruct HH as [m mmin].
      exists m.
      destruct mmin.
      unfold make_pre_collection_disjoint.
      split; trivial.
      unfold pre_union_of_collection.
      intros [nn Hnn].
      destruct (lt_dec nn m); [ | tauto].
      specialize (H0 _ Hnn).
      lia.
    - apply make_pre_collection_disjoint_in in Hn.
      exists n; tauto.
  Qed.

End pre_make_disjoint.

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
                                      (fun n : nat => pre_event_complement (if lt_dec n x then collection n else ∅))))).
        * intros ?.
          unfold pre_event_complement, pre_event_inter, pre_inter_of_collection, pre_event_none; simpl.
          unfold pre_event_none.
          split.
          -- intros [HH1 ?] ? HH2.
             match_destr_in HH2.
             destruct (Nat.eq_dec n x).
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
        apply Rminus_eq_compat_l.
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

Section util.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Definition list_Rbar_sum (l : list Rbar) : Rbar
    := fold_right Rbar_plus (Finite 0) l.
               
  Lemma list_Rbar_sum_const_mulR {A : Type} f (l : list A) :
    forall (r:R), list_Rbar_sum (map (fun x => Rbar_mult r (f x)) l)  =
              Rbar_mult r (list_Rbar_sum (map (fun x => f x) l)).
  Proof.
    intro r.
    induction l; simpl.
    - f_equal; lra.
    - rewrite  IHl.
      now rewrite Rbar_mult_r_plus_distr.
  Qed.

  Definition sum_Rbar_n (f:nat->Rbar) (n:nat) : Rbar
    := list_Rbar_sum (map f (seq 0 n)).

  Instance fold_right_plus_le_proper :
    Proper (Rbar_le ==> Forall2 Rbar_le ==> Rbar_le) (fold_right Rbar_plus).
  Proof.
    intros a b eqq1 x y eqq2.
    revert a b eqq1.
    induction eqq2; simpl; trivial; intros.
    apply Rbar_plus_le_compat; trivial.
    now apply IHeqq2.
  Qed.

  Lemma Rbar_plus_nneg_compat (a b : Rbar) :
    Rbar_le 0 a ->
    Rbar_le 0 b ->
    Rbar_le 0 (Rbar_plus a b).
  Proof.
    generalize (Rbar_plus_le_compat  0 a 0 b); intros HH.
    rewrite Rbar_plus_0_r in HH.
    auto.
  Qed.

  Lemma sum_Rbar_n_pos_incr (f : nat -> Rbar) :
    (forall i : nat, Rbar_le 0 (f i)) ->
    forall n : nat, Rbar_le (sum_Rbar_n f n) (sum_Rbar_n f (S n)).
  Proof.
    unfold sum_Rbar_n, list_Rbar_sum; intros.
    rewrite seq_Sn, map_app, fold_right_app.
    apply fold_right_plus_le_proper; try reflexivity.
    simpl.
    apply Rbar_plus_nneg_compat; trivial.
    reflexivity.
  Qed.

  Lemma list_Rbar_sum_nneg_nneg (l:list Rbar) :
    (forall x, In x l -> Rbar_le 0 x) ->
    Rbar_le 0 (list_Rbar_sum l).
  Proof.
    intros.
    induction l; [reflexivity |].
    simpl list_Rbar_sum.
    apply Rbar_plus_nneg_compat.
    - apply H; simpl; tauto.
    - apply IHl; intros.
      apply H; simpl; tauto.
  Qed.

  Lemma sum_Rbar_n_nneg_nneg (f : nat -> Rbar) n :
    (forall i : nat, (i <= n)%nat -> Rbar_le 0 (f i)) ->
    Rbar_le 0 (sum_Rbar_n f n).
  Proof.
    intros.
    apply list_Rbar_sum_nneg_nneg; intros.
    apply in_map_iff in H0.
    destruct H0 as [? [??]]; subst.
    apply in_seq in H1.
    apply H; lia.
  Qed.

  Lemma nneg_fold_right_Rbar_plus_nneg l :
        Forall (Rbar_le 0) l ->
        Rbar_le 0 (fold_right Rbar_plus 0 l).
  Proof.
    induction l.
    - simpl; reflexivity.
    -  simpl map; simpl fold_right.
       intros HH; invcs HH.
       apply Rbar_plus_nneg_compat; auto.
  Qed.

  Lemma list_Rbar_sum_nneg_perm (l1 l2:list Rbar) :
    Forall (Rbar_le 0) l1 ->
    Forall (Rbar_le 0) l2 ->
    Permutation l1 l2 ->
    list_Rbar_sum l1 = list_Rbar_sum l2.
  Proof.
    intros.
    unfold list_Rbar_sum.
    induction H1; simpl; trivial.
    - invcs H; invcs H0; now rewrite IHPermutation.
    - invcs H; invcs H0; invcs H4; invcs H5.
      repeat rewrite <- Rbar_plus_assoc
      ; try apply ex_Rbar_plus_pos; trivial
      ; try apply nneg_fold_right_Rbar_plus_nneg
      ; trivial.
      f_equal.
      now rewrite Rbar_plus_comm.
    - assert (Forall (Rbar_le 0) l')
        by now rewrite <- H1_.
      now rewrite IHPermutation1, IHPermutation2.
  Qed.

  Lemma nneg_fold_right_Rbar_plus_acc l acc :
    Rbar_le 0 acc ->
    Forall (Rbar_le 0) l ->    
    fold_right Rbar_plus acc l = Rbar_plus acc (fold_right Rbar_plus (Finite 0) l).
  Proof.
    intros pos1 pos2; revert pos1.
    induction pos2; intros.
    - now rewrite Rbar_plus_0_r.
    - simpl.
      rewrite IHpos2; trivial.
      repeat rewrite <- Rbar_plus_assoc_nneg; trivial
      ; try now apply nneg_fold_right_Rbar_plus_nneg.
      f_equal.
      apply Rbar_plus_comm.
  Qed.

  Lemma list_Rbar_sum_nneg_plus (l1 l2 : list Rbar) :
    Forall (Rbar_le 0) l1 ->
    Forall (Rbar_le 0) l2 ->
    list_Rbar_sum (l1 ++ l2) =
      Rbar_plus (list_Rbar_sum l1) (list_Rbar_sum l2).
  Proof.
    intros.
    unfold list_Rbar_sum.
    rewrite fold_right_app.
    rewrite nneg_fold_right_Rbar_plus_acc; trivial
    ; try now apply nneg_fold_right_Rbar_plus_nneg.
    now rewrite Rbar_plus_comm.
  Qed.    

  Lemma sum_Rbar_n_nneg_plus (f g:nat->Rbar) (n:nat) :
    (forall x, (x < n)%nat -> Rbar_le 0 (f x)) ->
    (forall x, (x < n)%nat -> Rbar_le 0 (g x)) ->
      sum_Rbar_n (fun x => Rbar_plus (f x) (g x)) n =
        Rbar_plus (sum_Rbar_n f n) (sum_Rbar_n g n).
  Proof.
    unfold sum_Rbar_n; intros.
    induction n; [simpl; f_equal; lra | ].
    rewrite seq_Sn.
    rewrite plus_0_l.

    repeat rewrite map_app.
    repeat rewrite list_Rbar_sum_nneg_plus; simpl
    ; try solve [apply Forall_forall; intros ? HH
                 ; apply in_map_iff in HH
                 ; destruct HH as [? [? HH]]; subst
                 ; apply in_seq in HH
                 ; try apply Rbar_plus_nneg_compat
                 ; try (apply H || apply H0); lia
                |
                  repeat constructor
                  ; try apply Rbar_plus_nneg_compat
                  ; try (apply H || apply H0); lia].
    rewrite IHn
    ; intros; try solve [(apply H || apply H0); lia].
    repeat rewrite Rbar_plus_0_r.
    repeat rewrite <- Rbar_plus_assoc_nneg
    ; trivial
    ; try apply Rbar_plus_nneg_compat
    ; (try solve [
            try (apply list_Rbar_sum_nneg_nneg
                 ; intros ? HH
                 ; apply in_map_iff in HH
                 ; destruct HH as [? [? HH]]; subst
                 ; apply in_seq in HH)
            ; try (apply H || apply H0); lia]).
    f_equal.
    repeat rewrite Rbar_plus_assoc_nneg
    ; trivial
    ; (try solve [
            try (apply list_Rbar_sum_nneg_nneg
                 ; intros ? HH
                 ; apply in_map_iff in HH
                 ; destruct HH as [? [? HH]]; subst
                 ; apply in_seq in HH)
            ; try (apply H || apply H0); lia]).
    f_equal.
    apply Rbar_plus_comm.
  Qed.      
    

  
  Lemma map_const_repeat {A B} (c:A) (l:list B) : map (fun _ => c) l = repeat c (length l).
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma fold_right_Rbar_plus_const {A} c (l:list A) :
    fold_right Rbar_plus 0 (map (fun _ => c) l) = (Rbar_mult (INR (length l)) c).
  Proof.
    induction l; intros.
    - simpl.
      now rewrite Rbar_mult_0_l.
    - simpl length.
      rewrite S_INR; simpl.
      rewrite IHl.
      generalize (pos_INR (length l)); intros HH.
      destruct c; simpl; rbar_prover.
  Qed.

  Lemma seq_sum_list_sum {T}
        (f:T -> Rbar) (B:list T) d :
    f d = 0 ->
    ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => f (nth n B d)) i) = list_Rbar_sum (map f B).
  Proof.
    intros.
    rewrite (ELim_seq_ext_loc _ (fun _ => sum_Rbar_n (fun n : nat => f (nth n B d)) (length B))).
    - rewrite ELim_seq_const.
      unfold sum_Rbar_n.
      f_equal.
      unfold pre_list_collection.
      now rewrite <- map_map, <- list_as_nthseq.
    - exists (length B); intros.
      unfold sum_Rbar_n.
      replace n with (length B + (n - length B))%nat by lia.
      rewrite seq_plus.
      unfold list_Rbar_sum.
      rewrite map_app, fold_right_app.
      f_equal.
      rewrite (seq_shiftn_map (length B)).
      rewrite map_map.
      rewrite (map_ext
                 (fun x : nat => f (nth (length B + x) B d ))
                 (fun x : nat => 0)).
      + rewrite fold_right_Rbar_plus_const.
        now rewrite Rbar_mult_0_r.
      + intros ?.
        rewrite nth_overflow; trivial.
        lia.
  Qed.

    Global Instance list_Rbar_sum_monotone : Proper (Forall2 Rbar_le ==> Rbar_le) list_Rbar_sum.
  Proof.
    intros ???.
    induction H; simpl.
    - reflexivity.
    - now apply Rbar_plus_le_compat.
  Qed.
    
  Global Instance sum_Rbar_n_monotone : Proper (pointwise_relation _ Rbar_le ==> eq ==> Rbar_le) sum_Rbar_n.
  Proof.
    intros ??????; subst.
    apply list_Rbar_sum_monotone.
    apply Forall2_map_f.
    apply Forall2_refl_in.
    apply Forall_forall; intros.
    apply H.
  Qed.
  
  Lemma pre_list_union_map_none {A B} (l:list A) :
    pre_event_equiv (pre_list_union (map (fun _  => pre_event_none) l)) (@pre_event_none B).
  Proof.
    induction l; simpl.
    - now rewrite pre_list_union_nil.
    - now rewrite pre_list_union_cons, IHl, pre_event_union_false_l.
  Qed.

  Global Instance pre_list_union_sub_proper {A} :
    Proper (Forall2 pre_event_sub ==> pre_event_sub) (@pre_list_union A).
  Proof.
    intros ????[?[??]].
    red.
    destruct (Forall2_In_l H H0) as [? [??]].
    eauto.
  Qed.

  Global Instance pre_list_inter_sub_proper {A} :
    Proper (Forall2 pre_event_sub ==> pre_event_sub) (@pre_list_inter A).
  Proof.
    intros ???????.
    destruct (Forall2_In_r H H1) as [? [??]].
    red in H0.
    apply H3.
    apply H0; simpl; eauto.
  Qed.

  Global Instance pre_list_union_proper {A} :
    Proper (Forall2 pre_event_equiv ==> pre_event_equiv) (@pre_list_union A).
  Proof.
    intros ????.
    split.
    - apply pre_list_union_sub_proper; trivial.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
    - apply pre_list_union_sub_proper; trivial.
      symmetry in H.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
  Qed.

  Global Instance pre_list_inter_proper {A} :
    Proper (Forall2 pre_event_equiv ==> pre_event_equiv) (@pre_list_inter A).
  Proof.
    intros ????.
    split.
    - apply pre_list_inter_sub_proper; trivial.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
    - apply pre_list_inter_sub_proper; trivial.
      symmetry in H.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
  Qed.

  Lemma pre_collection_take_nth_in {A} a (En:nat -> pre_event A) n x:
    nth a (collection_take En n) pre_event_none x <->
      (a < n /\ (En a) x)%nat.
  Proof.
    unfold collection_take.
    split.
    - intros na.
      destruct (lt_dec a n).
      + split; trivial.
        destruct (map_nth_in_exists En (seq 0 n) pre_event_none a).
        * now rewrite seq_length.
        * rewrite H in na.
          rewrite seq_nth in na by trivial.
          now simpl in na.
      + rewrite nth_overflow in na.
        * red in na; tauto.
        * rewrite map_length, seq_length.
          lia.
    - intros [alt Ea].
      destruct (map_nth_in_exists En (seq 0 n) pre_event_none a).
      + now rewrite seq_length.
      + rewrite H.
        rewrite seq_nth by trivial.
        now simpl.
  Qed.

  Lemma pre_collection_take_sub {A} (En:nat -> pre_event A) n :
    pointwise_relation _ pre_event_sub (pre_list_collection (collection_take En n) pre_event_none) En.
  Proof.
    repeat red; intros.
    apply pre_collection_take_nth_in in H.
    tauto.
  Qed.

  Lemma pre_collection_take_preserves_disjoint {A} (En:nat -> pre_event A) n:
    pre_collection_is_pairwise_disjoint En ->
    ForallOrdPairs pre_event_disjoint (collection_take En n).
  Proof.
    intros disj.
    apply pre_list_collection_disjoint.
    eapply pre_collection_is_pairwise_disjoint_pre_event_sub_proper; eauto.
    apply pre_collection_take_sub.
  Qed.

  Lemma pre_list_union_take_collection_sub {A} (E:nat->pre_event A) n :
    pre_event_sub (pre_list_union (collection_take E n)) (pre_union_of_collection E).
  Proof.
    rewrite <- pre_list_union_union.

    apply pre_union_of_collection_sub_proper.
    apply pre_collection_take_sub.
  Qed.

  Lemma pre_event_diff_diff_l {A} (a b c : pre_event A) :
    pre_event_equiv (pre_event_diff (pre_event_diff a b) c) (pre_event_diff a (pre_event_union b c)).
  Proof.
    firstorder.
  Qed.

  Lemma pre_union_of_collection_lt_S {A} (E:nat->pre_event A) n :
    pre_event_equiv (pre_union_of_collection (fun y : nat => if lt_dec y (S n) then E y else ∅))
                    (pre_event_union (E n) (pre_union_of_collection (fun y : nat => if lt_dec y n then E y else ∅))).
  Proof.
    intros ?; split.
    - intros [? HH].
      match_destr_in HH; try contradiction.
      destruct (Nat.eq_dec x0 n).
      * subst.
        now left.
      * right.
        exists x0.
        match_destr.
        lia.
    - intros [|[??]].
      + exists n.
        match_destr; try lia.
      + match_destr_in H; try contradiction.
        exists x0.
        match_destr.
        lia.
  Qed.


End util.

Section measure.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Context {T:Type}.
  Context {σ:SigmaAlgebra T}.

  Class is_measure (μ:event σ -> Rbar)
    := mk_measure {
        measure_proper :> Proper (event_equiv ==> eq) μ
      ; measure_none : μ event_none = 0%R
      ; measure_nneg a : Rbar_le 0 (μ a)
      ; measure_countable_disjoint_union (B:nat->event σ) :
        collection_is_pairwise_disjoint B ->
        μ (union_of_collection B) = (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i))
      }.
  
  Lemma measure_list_disjoint_union (μ:event σ -> Rbar) {μ_meas:is_measure μ} (l: list (event σ)) :
    (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
    ForallOrdPairs event_disjoint l ->
    μ (list_union l) = list_Rbar_sum (map μ l).
  Proof.
    intros Hd.
    generalize (measure_countable_disjoint_union (list_collection l ∅)); intros HH.
    cut_to HH.
    - unfold sum_of_probs_equals in HH.
      erewrite measure_proper in HH; [| eapply list_union_union ].
      rewrite HH.
      unfold list_collection.
      apply (seq_sum_list_sum _ _ ∅).
      apply measure_none.
    - apply list_collection_disjoint; trivial.
  Qed.

  Lemma measure_disjoint_union (μ:event σ -> Rbar) {μ_meas:is_measure μ} (a b: event σ) :
    (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
    event_disjoint a b ->
    μ (a ∪ b) = Rbar_plus (μ a) (μ b).
  Proof.
    intros Hd.
    generalize (measure_list_disjoint_union μ [a; b]); intros HH.
    rewrite list_union_cons, list_union_singleton in HH.
    simpl in HH.
    rewrite Rbar_plus_0_r in HH.
    apply HH.
    now repeat constructor.
  Qed.    
  
  Global Instance measure_monotone (μ:event σ -> Rbar) {μ_meas:is_measure μ} :
    Proper (event_sub ==> Rbar_le) μ.
  Proof.
    intros ???.
    rewrite (sub_diff_union _ _ H).
    rewrite measure_disjoint_union; trivial.
    - rewrite <- (Rbar_plus_0_l (μ x)) at 1.
      apply Rbar_plus_le_compat; try reflexivity.
      apply measure_nneg.
    - firstorder.
  Qed.

  Lemma measure_countable_sub_union (μ:event σ -> Rbar) {μ_meas:is_measure μ} (B:nat->event σ) :
    Rbar_le (μ (union_of_collection B)) (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i)).
  Proof.
    rewrite make_collection_disjoint_union.
    rewrite measure_countable_disjoint_union.
    - intros.
      apply ELim_seq_le; intros.
      apply sum_Rbar_n_monotone; trivial; intros ?.
      apply measure_monotone; trivial.
      apply make_collection_disjoint_sub.
    - apply make_collection_disjoint_disjoint.
  Qed.
  
  Lemma measure_all_one_ps_le1 (μ:event σ -> Rbar) {μ_meas:is_measure μ}
        (measure_all:μ Ω = R1) A : Rbar_le (μ A) R1.
  Proof.
    rewrite <- measure_all.
    apply measure_monotone; firstorder.
  Qed.

  Lemma measure_all_one_ps_fin (μ:event σ -> Rbar) {μ_meas:is_measure μ}
        (measure_all:μ Ω = R1) A : is_finite (μ A).
  Proof.
    eapply bounded_is_finite.
    - apply measure_nneg.
    - apply measure_all_one_ps_le1; trivial.
  Qed.

  Lemma is_measure_ex_Elim_seq
        (μ:event σ -> Rbar) {μ_meas:is_measure μ} (E:nat->event σ) :
    ex_Elim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (E n)) i).
  Proof.
    apply ex_Elim_seq_incr; intros.
    apply sum_Rbar_n_pos_incr; intros.
    apply measure_nneg.
  Qed.

  Program Instance measure_all_one_ps (μ:event σ -> Rbar) {μ_meas:is_measure μ}
           (measure_all:μ Ω = R1) :
    ProbSpace σ
    := {|
      ps_P x := real (μ x)
    |}.
  Next Obligation.
    intros ???.
    now rewrite H.
  Qed.
  Next Obligation.
    unfold sum_of_probs_equals.
    apply infinite_sum_infinite_sum'.
    apply infinite_sum_is_lim_seq.
    rewrite measure_countable_disjoint_union; trivial.
    apply is_Elim_seq_fin.

    assert (isfin:is_finite (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (collection n)) i))).
    {
      cut (ex_finite_Elim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (collection n)) i))
      ; [ now intros [??] |].
      eapply ex_finite_Elim_seq_incr with (M:=Finite 1) (m:=0%nat).
      - intros.
        apply sum_Rbar_n_pos_incr.
        intros; apply measure_nneg.
      - intros.
        unfold sum_Rbar_n.
        rewrite <- map_map.
        rewrite <- measure_list_disjoint_union; trivial.
        + replace 1 with R1 by lra; simpl.
          rewrite <- measure_all.
          apply measure_monotone; trivial.
          firstorder.
        + now apply collection_take_preserves_disjoint.
      - now unfold sum_Rbar_n; simpl.
    }         
    rewrite isfin.
    rewrite <- ELim_seq_incr_1.
    erewrite ELim_seq_ext; try eapply ELim_seq_correct.
    - apply ex_Elim_seq_incr; intros.
      apply sum_f_R0_pos_incr.
      intros.
      generalize (measure_nneg (collection i)); simpl.
      match_destr; simpl; try tauto; try lra.
    - intros; simpl.
      rewrite sum_f_R0_sum_f_R0'.
      rewrite sum_f_R0'_as_fold_right.
      unfold sum_Rbar_n, list_Rbar_sum.
      rewrite fold_right_map.
      induction (seq 0 (S n)); simpl; trivial.
      rewrite IHl.
      rewrite <- measure_all_one_ps_fin; trivial.
  Qed.
  Next Obligation.
    now rewrite measure_all.
  Qed.
  Next Obligation.
    generalize (measure_nneg A); simpl.
    match_destr; simpl; try tauto; try lra.
  Qed.

  Lemma ps_measure (ps:ProbSpace σ) : is_measure ps_P.
  Proof.
    constructor.
    - intros ???.
      f_equal.
      now apply ps_proper.
    - f_equal.
      apply ps_none.
    - intros; simpl.
      apply ps_pos.
    - intros.
      generalize (ps_countable_disjoint_union B H); intros HH.
      unfold sum_of_probs_equals in HH.
      apply infinite_sum_infinite_sum' in HH.
      apply infinite_sum_is_lim_seq in HH.
      apply is_Elim_seq_fin in HH.
      apply is_Elim_seq_unique in HH.
      rewrite <- ELim_seq_incr_1.
      rewrite <- HH.
      apply ELim_seq_ext; intros.
      rewrite sum_f_R0_sum_f_R0'.
      rewrite sum_f_R0'_as_fold_right.
      unfold sum_Rbar_n, list_Rbar_sum.
      rewrite fold_right_map.
      induction (seq 0 (S n)); simpl; trivial.
      now rewrite <- IHl; simpl.
  Qed.

  Class is_complete_measure (μ:event σ -> Rbar) {μ_meas:is_measure μ}
    := measure_is_complete : forall a b, pre_event_sub a (event_pre b) -> μ b = 0 -> sa_sigma a.

End measure.


Section outer_measure.
  Context {T:Type}.

  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.
                                                              
  Class is_outer_measure (μ:pre_event T -> Rbar)
    := mk_outer_measure {
        outer_measure_proper :> Proper (pre_event_equiv ==> eq) μ
      ; outer_measure_none : μ pre_event_none = 0%R
      ; outer_measure_nneg a : Rbar_le 0 (μ a)
      ; outer_measure_countable_subadditive (A:pre_event T) (B:nat->pre_event T) :
        pre_event_sub A (pre_union_of_collection B) ->
        Rbar_le (μ A) (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i))
      }.

    Class is_outer_measure_alt (μ:pre_event T -> Rbar)
    := mk_outer_measure_alt {
        outer_measure_alt_none : μ pre_event_none = 0%R
      ; outer_measure_alt_nneg a : Rbar_le 0 (μ a)
      ; outer_measure_alt_monotone :> Proper (pre_event_sub ==> Rbar_le) μ
      ; outer_measure_alt_countable_union (B:nat->pre_event T) :
        Rbar_le (μ (pre_union_of_collection B)) (ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (B n)) i))
      }.

  Hint Resolve outer_measure_nneg : prob.
  Hint Resolve Rbar_plus_nneg_compat : prob.

  Global Instance outer_measure_alt_proper (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure_alt μ}: Proper (pre_event_equiv ==> eq) μ.
  Proof.
    intros ???.
    apply antisymmetry
    ; apply outer_measure_alt_monotone; firstorder.
  Qed.

    (* The infinite sum is always defined, since the values are all nonnegative *)
  Lemma is_outer_measure_ex_Elim_seq
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat->pre_event T) :
    ex_Elim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (E n)) i).
  Proof.
    apply ex_Elim_seq_incr; intros.
    apply sum_Rbar_n_pos_incr; auto with prob.
  Qed.

  Lemma outer_measure_list_subadditive
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ}
        (A:pre_event T) (B:list (pre_event T)) :
        pre_event_sub A (pre_list_union B) ->
        Rbar_le (μ A) (list_Rbar_sum (map μ B)).
  Proof.
    intros.
    rewrite <- (seq_sum_list_sum _ _ pre_event_none).
    - apply outer_measure_countable_subadditive.
      generalize (pre_list_union_union B).
      unfold pre_list_collection; intros HH.
      now rewrite HH.
    - apply outer_measure_none.
  Qed.

  Global Instance is_outer_measure_is_alt
         (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    is_outer_measure_alt μ.
  Proof.
    - constructor; try solve [destruct μ_outer; trivial].
      + intros A B sub.
        generalize (outer_measure_list_subadditive μ A (B::nil)).
        simpl.
        rewrite Rbar_plus_0_r.
        intros HH2; apply HH2.
        now rewrite pre_list_union_singleton.
      + intros.
        now apply (outer_measure_countable_subadditive _ B).
  Qed.
  
  Lemma is_outer_measure_alt_iff (μ:pre_event T -> Rbar) :
    is_outer_measure μ <-> is_outer_measure_alt μ.
  Proof.
    split; intros HH.
    - now apply is_outer_measure_is_alt.
    - constructor; try solve [destruct HH; trivial].
      + now apply outer_measure_alt_proper.
      + intros.
        rewrite H.
        now apply outer_measure_alt_countable_union.
  Qed.

  Definition μ_measurable (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T)
    := forall (A:pre_event T), μ A = Rbar_plus (μ (pre_event_inter A E)) (μ (pre_event_diff A E)).

  Global Instance μ_measurable_proper (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    Proper (pre_event_equiv ==> iff) (μ_measurable μ).
  Proof.
    unfold μ_measurable.
    intros ???.
    split; intros ??.
    - now rewrite <- H.
    - now rewrite H.
  Qed.

  Lemma μ_measurable_simpl (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T)
    : (forall (A:pre_event T),
          Rbar_le (Rbar_plus (μ (pre_event_inter A E))
                             (μ (pre_event_diff A E)))
                  (μ A)) -> μ_measurable μ E.
  Proof.
    intros ??.
    apply antisymmetry; trivial.
    generalize (outer_measure_list_subadditive μ A [(pre_event_inter A E); (pre_event_diff A E)])
    ; simpl; intros HH.
    rewrite Rbar_plus_0_r in HH.
    apply HH.
    intros ??.
    red.
    simpl.
    destruct (classic (E x)).
    - exists (pre_event_inter A E); split; eauto.
      firstorder.
    - exists (pre_event_diff A E); split; eauto.
      firstorder.
  Qed.

  Lemma μ_measurable_complement (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T) :
    μ_measurable μ E -> μ_measurable μ (pre_event_complement E).
  Proof.
    unfold μ_measurable; intros.
    rewrite pre_event_diff_derived.
    rewrite pre_event_not_not; [| intros ?; apply classic].
    rewrite <- pre_event_diff_derived.
    rewrite Rbar_plus_comm.
    apply H.
  Qed.

  Lemma μ_measurable_complement_b (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T) :
   μ_measurable μ (pre_event_complement E) -> μ_measurable μ E.
  Proof.
    intros.
    rewrite <- (pre_event_not_not E); try (intros ?; apply classic).
    now apply μ_measurable_complement.
  Qed.

  Hint Resolve ex_Rbar_plus_pos : prob.

  Lemma measure_ex_Rbar_plus (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} x y :
    ex_Rbar_plus (μ x) (μ y).
  Proof.
    auto with prob.
  Qed.

  Hint Resolve measure_ex_Rbar_plus : prob.
  
  Lemma measure_fold_right_Rbar_plus_nneg
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} l :
    Rbar_le 0 (fold_right Rbar_plus 0 (map μ l)).
  Proof.
    apply nneg_fold_right_Rbar_plus_nneg.
    apply Forall_map.
    apply Forall_forall; intros.
    auto with prob.
  Qed.
  
  Lemma list_Rbar_sum_measure_perm (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} {l1 l2} :
    Permutation l1 l2 ->
    list_Rbar_sum (map μ l1) = list_Rbar_sum (map μ l2).
  Proof.
    intros.
    apply list_Rbar_sum_nneg_perm
    ; try solve [ apply Forall_map; apply Forall_forall; intros; auto with prob].
    now apply Permutation_map.
  Qed.

  (* Note that A does not need to be measurable *)
  Lemma μ_measurable_list_inter_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (A:pre_event T) (l : list (pre_event T)) :
    Forall (μ_measurable μ) l ->
    ForallOrdPairs pre_event_disjoint l ->
    μ (pre_list_union (map (pre_event_inter A) l)) = list_Rbar_sum (map μ (map (pre_event_inter A) l)).
  Proof.
    intros meas disj.
    induction l; simpl.
    - rewrite pre_list_union_nil.
      apply outer_measure_none.
    - invcs meas.
      invcs disj.
      specialize (IHl H2 H4).
      rewrite H1.
      rewrite pre_event_inter_comm.
      rewrite pre_event_inter_pre_list_union_distr.
      rewrite pre_event_union_diff_distr; simpl.
      repeat rewrite pre_list_union_cons.
      rewrite pre_event_inter_comm, <- pre_event_inter_assoc, pre_event_inter_self.
      rewrite <- pre_event_inter_diff, pre_event_diff_self.
      rewrite pre_event_inter_false_r.
      rewrite pre_event_union_false_l.
      assert (eqq1: Forall2 pre_event_equiv (map (pre_event_inter a) (map (pre_event_inter A) l))
                            (map (fun _ => pre_event_none) l)).
      {
        rewrite map_map.
        apply Forall2_map_f.
        apply Forall2_refl_in.
        apply Forall_forall; intros.
        rewrite Forall_forall in H3.
        specialize (H3 _ H).
        firstorder.
      } 
      rewrite eqq1.
      rewrite pre_list_union_map_none.
      rewrite pre_event_union_false_r.
      assert (eqq2:Forall2 pre_event_equiv
                           (map (fun x => pre_event_diff x a) (map (pre_event_inter A) l))
                           (map (pre_event_inter A) l)).
      {
        rewrite <- (map_id (map (pre_event_inter A) l)) at 2.
        apply Forall2_map_f.
        apply Forall2_refl_in.
        apply Forall_forall; intros.
        rewrite Forall_forall in H3.
        apply in_map_iff in H.
        destruct H as [? [??]]; subst.
        specialize (H3 _ H0).
        firstorder.
      } 
      rewrite eqq2.
      now rewrite IHl; simpl.
  Qed.

  Lemma μ_measurable_list_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (l : list (pre_event T)) :
    Forall (μ_measurable μ) l ->
    ForallOrdPairs pre_event_disjoint l ->
    μ (pre_list_union l) = list_Rbar_sum (map μ l).
  Proof.
    intros meas disj.
    assert (eqq1: Forall2 pre_event_equiv (map (pre_event_inter pre_Ω) l) l).
    {
      symmetry.
      apply Forall2_map_Forall.
      apply Forall_forall; intros.
      now rewrite pre_event_inter_true_l.
    }
    etransitivity; [etransitivity |]
    ; [| apply (μ_measurable_list_inter_disjoint_additivity μ pre_Ω l meas disj) | ].
    - now rewrite eqq1.
    - f_equal.
      rewrite map_map.
      apply map_ext; intros.
      now rewrite pre_event_inter_true_l.
  Qed.      

  Lemma μ_measurable_list_inter_take_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (A:pre_event T) (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    forall n, μ (pre_list_union (map (pre_event_inter A) (collection_take E n))) = 
           sum_Rbar_n (fun i : nat => μ (pre_event_inter A (E i))) n.
  Proof.
    intros.
    rewrite (μ_measurable_list_inter_disjoint_additivity μ A).
    - unfold sum_Rbar_n.
      unfold collection_take.
      now repeat rewrite map_map.
    - apply Forall_forall; intros.
      apply In_collection_take in H1.
      destruct H1 as [? [??]]; subst.
      auto.
    - now apply pre_collection_take_preserves_disjoint.
  Qed.

  Lemma μ_measurable_list_take_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    forall n, μ (pre_list_union (collection_take E n)) = 
           sum_Rbar_n (fun i : nat => μ (E i)) n.
  Proof.
    intros.
    rewrite (μ_measurable_list_disjoint_additivity μ).
    - unfold sum_Rbar_n.
      unfold collection_take.
      now rewrite map_map.
    - apply Forall_forall; intros.
      apply In_collection_take in H1.
      destruct H1 as [? [??]]; subst.
      auto.
    - now apply pre_collection_take_preserves_disjoint.
  Qed.

  Theorem μ_measurable_countable_inter_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (A:pre_event T) (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    μ (pre_union_of_collection (fun n => pre_event_inter A (E n))) = ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (pre_event_inter A (E n))) i).
  Proof.
    intros meas disj.
    apply antisymmetry.
    - apply outer_measure_alt_countable_union.
    - assert (eqqn:forall n, μ (pre_list_union  (map (pre_event_inter A) (collection_take E n))) = 
                          sum_Rbar_n (fun i : nat => μ (pre_event_inter A (E i))) n)
        by (intros; eapply μ_measurable_list_inter_take_disjoint_additivity; eauto).

      assert (le1:forall n, Rbar_le (μ (pre_list_union  (map (pre_event_inter A) (collection_take E n)))) (μ (pre_union_of_collection  (fun n => pre_event_inter A (E n))))).
      {
        intros.
        apply outer_measure_alt_monotone.
        rewrite <- pre_list_union_take_collection_sub.
        unfold collection_take.
        now rewrite map_map.
      } 
      rewrite <- (ELim_seq_const  (μ (pre_union_of_collection (fun n : nat => pre_event_inter A (E n))))).
      apply ELim_seq_le; intros.
      now rewrite <- eqqn.
  Qed.

  Theorem μ_measurable_countable_disjoint_additivity
        (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    (μ (pre_union_of_collection E)) = ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (E n)) i).
  Proof.
    intros meas disj.
    apply antisymmetry.
    - apply outer_measure_alt_countable_union.
    - assert (eqqn:forall n, μ (pre_list_union (collection_take E n)) = 
                          sum_Rbar_n (fun i : nat => μ (E i)) n)
        by (intros; eapply μ_measurable_list_take_disjoint_additivity; eauto).

      assert (le1:forall n, Rbar_le (μ (pre_list_union (collection_take E n))) (μ (pre_union_of_collection E))).
      {
        intros.
        apply outer_measure_alt_monotone.
        apply pre_list_union_take_collection_sub.
      } 
      rewrite <- (ELim_seq_const  (μ (pre_union_of_collection E))).
      apply ELim_seq_le; intros.
      now rewrite <- eqqn.
  Qed.

  Theorem μ_measurable_0 (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:pre_event T) :
    μ E = 0 -> μ_measurable μ E.
  Proof.
    intros.
    apply μ_measurable_simpl; intros.
    replace (μ (pre_event_inter A E)) with (Finite 0).
    - rewrite Rbar_plus_0_l.
      apply outer_measure_alt_monotone.
      apply pre_event_diff_sub.
    - apply antisymmetry.
      + apply outer_measure_alt_nneg.
      + rewrite <- H.
        apply outer_measure_alt_monotone.
        apply pre_event_inter_sub_r.
  Qed.

  Lemma μ_measurable_none (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    μ_measurable μ pre_event_none.
  Proof.
    apply μ_measurable_0.
    apply outer_measure_none.
  Qed.

  Hint Resolve μ_measurable_none : prob.

  Lemma μ_measurable_Ω (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    μ_measurable μ pre_Ω.
  Proof.
    rewrite <- pre_event_not_none.
    apply μ_measurable_complement.
    apply μ_measurable_none.
  Qed.

  Hint Resolve μ_measurable_Ω : prob.

  Lemma μ_measurable_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (a b : pre_event T) :
    μ_measurable μ a ->
    μ_measurable μ b ->
    μ_measurable μ (pre_event_union a b).
  Proof.
    intros.
    apply μ_measurable_simpl; intros.
    rewrite (H A).
    rewrite (H0 (pre_event_inter A a)).
    rewrite (H0 (pre_event_diff A a)).
    rewrite pre_event_diff_diff_l.
    rewrite <- Rbar_plus_assoc by auto with prob.
    apply Rbar_plus_le_compat; try reflexivity.
    generalize (outer_measure_list_subadditive μ
                                               (pre_event_inter A (pre_event_union a b))
                                               [(pre_event_inter (pre_event_inter A a) b)
                                                ; (pre_event_diff (pre_event_inter A a) b)
                                                ;  (pre_event_inter (pre_event_diff A a) b)])
    ; intros HH.
    simpl in HH.
    rewrite Rbar_plus_0_r in HH.
    rewrite Rbar_plus_assoc by auto with prob.
    apply HH.
    intros ?[??].
    unfold pre_list_union; simpl.
    destruct H2.
    - destruct (classic (b x)).
      + exists (pre_event_inter (pre_event_inter A a) b); firstorder.
      + exists (pre_event_diff (pre_event_inter A a) b); firstorder.
    - destruct (classic (a x)).
      + exists (pre_event_inter (pre_event_inter A a) b); firstorder.
      + exists (pre_event_inter (pre_event_diff A a) b); firstorder.
  Qed.

  Hint Resolve μ_measurable_union μ_measurable_complement : prob.
  
  Corollary μ_measurable_inter (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (a b : pre_event T) :
    μ_measurable μ a ->
    μ_measurable μ b ->
    μ_measurable μ (pre_event_inter a b).
  Proof.
    intros.
    apply μ_measurable_complement_b.
    rewrite pre_event_complement_inter.
    auto with prob.
  Qed.

  Hint Resolve μ_measurable_inter : prob.

  Corollary μ_measurable_diff (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (a b : pre_event T) :
    μ_measurable μ a ->
    μ_measurable μ b ->
    μ_measurable μ (pre_event_diff a b).
  Proof.
    intros.
    rewrite pre_event_diff_derived.
    auto with prob.
  Qed.

  Hint Resolve μ_measurable_inter : prob.  

  Lemma μ_measurable_list_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (l:list (pre_event T)) :
    Forall (μ_measurable μ) l ->
    μ_measurable μ (pre_list_union l).
  Proof.
    intros meas.
    induction meas; simpl.
    - rewrite pre_list_union_nil.
      apply μ_measurable_none.
    - rewrite pre_list_union_cons.
      now apply μ_measurable_union.
  Qed.    

  Lemma μ_measurable_disjoint_countable_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    pre_collection_is_pairwise_disjoint E ->
    μ_measurable μ (pre_union_of_collection E).
  Proof.
    intros meas disj.
    apply μ_measurable_simpl; intros.

    rewrite pre_event_inter_countable_union_distr.
    rewrite (μ_measurable_countable_inter_disjoint_additivity μ); trivial.

    rewrite <- (ELim_seq_const (μ (pre_event_diff A (pre_union_of_collection E)))).
    rewrite <- ELim_seq_plus.
    - rewrite <- (ELim_seq_const (μ A)).
      apply ELim_seq_le; intros.
      etransitivity.
      + eapply Rbar_plus_le_compat.
        * reflexivity.
        * apply (outer_measure_alt_monotone
                   (pre_event_diff A (pre_union_of_collection E))
                   (pre_event_diff A (pre_list_union (collection_take E n)))).
          now rewrite pre_list_union_take_collection_sub.
      + assert (measu:μ_measurable μ (pre_list_union (collection_take E n))).
        {
          apply μ_measurable_list_union.
          apply Forall_forall; intros ? inn.
          apply In_collection_take in inn.
          destruct inn as [?[??]]; subst.
          auto.
        }
        rewrite (measu A).
        apply Rbar_plus_le_compat; try reflexivity.
        rewrite pre_event_inter_pre_list_union_distr.
        rewrite <- (μ_measurable_list_inter_take_disjoint_additivity μ); trivial.
        reflexivity.
    - now apply is_outer_measure_ex_Elim_seq. 
    - apply ex_Elim_seq_const.
    - apply ex_Rbar_plus_pos.
      + rewrite <- (ELim_seq_const 0).
        apply ELim_seq_le; intros.
        unfold sum_Rbar_n.
        unfold list_Rbar_sum.
        rewrite <- map_map.
        now apply measure_fold_right_Rbar_plus_nneg.
      + rewrite ELim_seq_const.
        auto with prob.
  Qed.

  Lemma μ_measurable_make_disjoint (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) ->
    forall n, μ_measurable μ (make_pre_collection_disjoint E n).
  Proof.
    unfold make_pre_collection_disjoint; intros.
    apply μ_measurable_diff; trivial.
    induction n.
    - simpl.
      rewrite pre_union_of_collection_const.
      auto with prob.
    - rewrite pre_union_of_collection_lt_S.
      auto with prob.
  Qed.
    
  Theorem μ_measurable_countable_union (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} (E:nat -> pre_event T) :
    (forall n, μ_measurable μ (E n)) -> μ_measurable μ (pre_union_of_collection E).
  Proof.
    intros.
    rewrite (make_pre_collection_disjoint_union E).
    apply μ_measurable_disjoint_countable_union.
    - intros.
      now apply μ_measurable_make_disjoint.
    - apply make_pre_collection_disjoint_disjoint.
  Qed.

  (* These results are also called Caratheodory’s Theorem *)
  Instance μ_measurable_sa (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    SigmaAlgebra T
    := {|
      sa_sigma E := μ_measurable μ E
    ; sa_countable_union := μ_measurable_countable_union μ
    ; sa_complement := μ_measurable_complement μ
    ; sa_all := μ_measurable_Ω μ
    |}.

  Global Instance μ_measurable_sa_measure (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    is_measure (σ:=μ_measurable_sa μ) μ.
  Proof.
    constructor.
    - intros ???.
      red in H.
      now rewrite H.
    - apply outer_measure_none.
    - intros.
      apply outer_measure_nneg.
    - intros.
      apply (μ_measurable_countable_disjoint_additivity μ); trivial.
      intros.
      now destruct (B n); simpl.
  Qed.

  Global Instance μ_measurable_sa_complete_measure (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} :
    is_complete_measure (σ:=μ_measurable_sa μ) μ.
  Proof.
    intros ????.
    apply μ_measurable_0. 
    rewrite <- H0.
    apply antisymmetry.
    - now rewrite H.
    - rewrite H0.
      apply outer_measure_nneg.
  Qed.
  
End outer_measure.


Section omf.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.


  Context {T:Type}.
  Context {σ:SigmaAlgebra T}.
  Context (μ:event σ -> Rbar).
  Context {μ_meas:is_measure μ}.

  Definition outer_μ_of_covers (an:nat->event σ) : Rbar :=
    ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => μ (an n)) i).
  
  Definition outer_μ (A:pre_event T) : Rbar
    := Rbar_glb (fun (x : Rbar) =>
                   exists (an:nat->event σ),
                     pre_event_sub A (union_of_collection an) /\
                       x = outer_μ_of_covers an).

  Lemma ELim_seq_pos (f : nat -> Rbar) :
    (forall n, Rbar_le 0 (f n)) ->
    Rbar_le 0 (ELim_seq f).
  Proof.
    intros.
    generalize (ELim_seq_le (fun _ => 0) f); intros.
    rewrite ELim_seq_const in H0.
    now apply H0.
  Qed.

  Lemma outer_μ_nneg (A:pre_event T) 
    : Rbar_le 0 (outer_μ A).
  Proof.
    unfold outer_μ.
    unfold Rbar_glb, proj1_sig; match_destr; destruct r as [lb glb].
    apply glb; intros ?[?[??]]; subst.
    apply ELim_seq_pos; intros.
    apply sum_Rbar_n_nneg_nneg; intros.
    apply measure_nneg.
  Qed.

  Lemma outer_μ_of_covers_nneg (an:nat->event σ) :
    Rbar_le 0 (outer_μ_of_covers an).
  Proof.
    apply ELim_seq_pos; intros.
    apply sum_Rbar_n_nneg_nneg; intros.
    apply measure_nneg.
  Qed.
  
  Global Instance outer_μ_of_covers_monotone : Proper (pointwise_relation _ event_sub ==> Rbar_le) outer_μ_of_covers.
  Proof.
    intros ???.
    apply ELim_seq_le; intros.
    apply sum_Rbar_n_monotone; trivial.
    intros ?.
    now apply measure_monotone.
  Qed.

  Lemma is_finite_dec (a:Rbar) : {is_finite a} + {~ is_finite a}.
  Proof.
    unfold is_finite; destruct a; simpl; intuition congruence.
  Qed.

  (** * Extended Emptiness is decidable *)

  Definition Rbar_Empty (E : Rbar -> Prop) :=
    Rbar_glb (fun x => x = 0 \/ E x) = Rbar_lub (fun x => x = 0 \/ E x)
    /\ Rbar_glb (fun x => x = 1 \/ E x) = Rbar_lub (fun x => x = 1 \/ E x).

  Lemma Rbar_Empty_correct_1 (E : Rbar -> Prop) :
    Rbar_Empty E -> forall x, ~ E x.
  Proof.
    intros.
    unfold Rbar_Empty, Rbar_glb, Rbar_lub, proj1_sig in *.
    repeat match_destr_in H.
    destruct H; subst.
    unfold Rbar_is_glb, Rbar_is_lub in *.
    intuition.
    assert (x1 = 0)
      by (apply Rbar_le_antisym; eauto).
    assert (x3 = 1)
      by (apply Rbar_le_antisym; eauto).
    subst.
    specialize (H2 x).
    cut_to H2; [| tauto].
    specialize (H4 x).
    cut_to H4; [| tauto].
    generalize (Rbar_le_trans _ _ _ H4 H2); simpl; lra.
  Qed.

  Lemma Rbar_Empty_correct_2 (E : Rbar -> Prop) :
    (forall x, ~ E x) -> Rbar_Empty E.
  Proof.
    intros H.
    unfold Rbar_Empty, Rbar_glb, Rbar_lub, proj1_sig in *.
    repeat match_destr.
    unfold Rbar_is_glb, Rbar_is_lub in *.
    destruct r; destruct r0; destruct r1; destruct r2.
    assert (x = Finite 0).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H1; intros ?[]; subst; [reflexivity | eelim H; eauto].
    }
    assert (x0 = Finite 0).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H3; intros ?[]; subst; [reflexivity | eelim H; eauto].
    } 
    assert (x1 = Finite 1).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H5; intros ?[]; subst; [reflexivity | eelim H; eauto].
    } 
    assert (x2 = Finite 1).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H7; intros ?[]; subst; [reflexivity | eelim H; eauto].
    }
    split; congruence.
  Qed.

  Lemma Rbar_Empty_dec (E : Rbar -> Prop) :
    {~Rbar_Empty E}+{Rbar_Empty E}.
  Proof.
    unfold Rbar_Empty.
    destruct (Rbar_eq_dec (Rbar_glb (fun x => x = 0 \/ E x)) (Rbar_lub (fun x => x = 0 \/ E x))).
    - destruct (Rbar_eq_dec (Rbar_glb (fun x => x = 1 \/ E x)) (Rbar_lub (fun x => x = 1 \/ E x))).
      + right; tauto.
      + left; tauto.
    - left; tauto.
  Defined.

  Lemma not_Rbar_Empty_dec (E : Rbar -> Prop) : (Decidable.decidable (exists x, E x)) ->
                                        {(exists x, E x)} + {(forall x, ~ E x)}.
  Proof.
    intros.
    destruct (Rbar_Empty_dec E).
    - left.
      destruct H; trivial.
      contradict n.
      apply Rbar_Empty_correct_2; intros ??.
      apply H; eauto.
    - right; intros.
      now apply Rbar_Empty_correct_1.
  Qed.      

  Lemma Rbar_uniqueness_dec P : (exists ! x : Rbar, P x) -> {x : Rbar | P x}.
  Proof.
    intros HH.
    exists (Rbar_lub P).
    destruct HH as [? [??]].
    replace (Rbar_lub P) with x; trivial.
    apply sym_eq, Rbar_is_lub_unique.
    split.
    - intros ??.
      rewrite (H0 _ H1); apply Rbar_le_refl.
    - firstorder.
  Qed.

  Lemma Rbar_is_glb_fin_close_classic {E a} (eps:posreal):
    Rbar_is_glb E (Finite a) -> exists x, E x /\ Rbar_le x (a + eps).
  Proof.
    intros HH1.
    apply NNPP; intros HH2.
    generalize (not_ex_all_not _ _ HH2); intros HH3.
    assert (Rbar_is_glb E (Finite (a + eps))).
    {
      destruct HH1.
      split.
      - intros ??.
        specialize (H _ H1).
        specialize (HH3 x).
        intuition.
        apply Rbar_not_le_lt in H3.
        now apply Rbar_lt_le.
      - intros.
        eapply Rbar_le_trans; try now eapply H0.
        simpl.
        destruct eps; simpl; lra.
    }
    apply Rbar_is_glb_unique in HH1.
    apply Rbar_is_glb_unique in H.
    rewrite H in HH1.
    invcs HH1.
    destruct eps; simpl in *; lra.
  Qed.

  Lemma Rle_forall_le: forall a b : R, (forall eps : posreal, a <= b + eps) -> a <= b.
  Proof.
    intros.
    apply Rlt_forall_le; intros.
    specialize (H (pos_div_2 eps)).
    simpl in H.
    eapply Rle_lt_trans; try eapply H.
    destruct eps; simpl.
    lra.
  Qed.

  Lemma Rbar_le_forall_Rbar_le: forall a b : Rbar, (forall eps : posreal, Rbar_le a (Rbar_plus b eps)) -> Rbar_le a b.
  Proof.
    intros [] []; simpl; intros HH; trivial
    ; try (apply HH; exact posreal1).
    now apply Rle_forall_le.
  Qed.

  Lemma Elim_seq_sum_pos_fin_n_fin f r :
    (forall n, Rbar_le 0 (f n)) ->
    ELim_seq
        (fun i : nat => sum_Rbar_n f i) = Finite r ->
    forall n, is_finite (f n).
  Proof.
    intros.
    generalize (ELim_seq_pos _ H); intros nneglim.
    case_eq (f n); intros; simpl; [reflexivity |..].
    - assert (HH:Rbar_le (ELim_seq (fun _ => sum_Rbar_n f (S n))) (ELim_seq (fun i : nat => sum_Rbar_n f i))).
      {
        apply ELim_seq_le_loc.
        exists (S n); intros.
        apply (le_ind (S n) (fun x => Rbar_le (sum_Rbar_n f (S n)) (sum_Rbar_n f x))); trivial.
        - reflexivity.
        - intros.
          eapply Rbar_le_trans; try eapply H4.
          apply sum_Rbar_n_pos_incr; trivial.
      }
      rewrite ELim_seq_const in HH.
      rewrite H0 in HH.
      
      unfold sum_Rbar_n in HH.
      rewrite seq_Sn, map_app in HH; simpl in HH.
      rewrite H1 in HH.
      erewrite list_Rbar_sum_nneg_perm in HH
      ; try eapply Permutation_app_comm.
      + simpl in HH.
        unfold Rbar_plus in HH; simpl in HH.
        assert (Rbar_le 0 (list_Rbar_sum (map f (seq 0 n)))).
        {
          apply list_Rbar_sum_nneg_nneg; intros.
          apply in_map_iff in H2.
          now destruct H2 as [?[??]]; subst.
        }
        destruct (list_Rbar_sum (map f (seq 0 n))); simpl in HH
        ; try contradiction.
      + apply Forall_app.
        * apply Forall_map; apply Forall_forall; intros; trivial.
        * repeat constructor.
      + apply Forall_app.
        * repeat constructor.
        * apply Forall_map; apply Forall_forall; intros; trivial.
    - specialize (H n).
      rewrite H1 in H.
      simpl in H.
      contradiction.
  Qed.

  Lemma Rbar_glb_ge (E:Rbar->Prop) c :
    (forall x, E x -> Rbar_le c x) ->
    Rbar_le c (Rbar_glb E).
  Proof.
    unfold Rbar_glb, proj1_sig; match_destr; intros.
    apply r; intros ??.
    now apply H.
  Qed.

  Lemma list_Rbar_sum_map_finite (l:list R) : list_Rbar_sum (map Finite l) = list_sum l.
  Proof.
    unfold list_Rbar_sum.
    induction l; simpl; trivial.
    now rewrite IHl; simpl.
  Qed.

  Lemma Lim_seq_sum_2n2 : Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ x) (seq 0 n))) = 2.
  Proof.
    generalize (is_series_geom (1/2))
    ; intros HH.
    cut_to HH; [| rewrite Rabs_pos_eq; lra].
    apply is_series_Reals in HH.
    apply infinite_sum_is_lim_seq in HH.
    replace (/ (1 - 1 / 2)) with 2 in HH by lra.
    apply is_lim_seq_unique in HH.
    erewrite Lim_seq_ext in HH
    ; [| intros; rewrite <- sum_f_R0_sum_f_R0'; reflexivity].
    erewrite Lim_seq_ext in HH
    ; [| intros; rewrite <- sum_f_R0'_list_sum; reflexivity].
    rewrite <- Lim_seq_incr_1.
    rewrite <- HH.
    apply Lim_seq_ext; intros.
    f_equal.
    apply map_ext; intros.
    replace (1/2) with (/2) by lra.
    rewrite Rinv_pow; try lra.
  Qed.

  Lemma Lim_seq_sum_2n : Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ (S x)) (seq 0 n))) = 1.
  Proof.
    transitivity (Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ x) (seq 1 n)))).
    - apply Lim_seq_ext; intros.
      now rewrite <- seq_shift, map_map.
    - generalize (Lim_seq_sum_2n2); intros HH.
      rewrite <- Lim_seq_incr_1 in HH.
      erewrite Lim_seq_ext in HH
      ; [| intros; rewrite <- cons_seq; simpl; reflexivity].
      rewrite Lim_seq_plus in HH.
      + rewrite Lim_seq_const in HH.
        rewrite Rinv_1 in HH.
        destruct (Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ x) (seq 1 n)))); simpl in *
        ; invcs HH; try lra.
        f_equal; lra.
      + apply ex_lim_seq_const.
      + apply ex_lim_seq_incr; intros.
        rewrite seq_Sn, map_app, list_sum_cat.
        simpl.
        assert (0 < (/ (2 * 2 ^ n))).
        {
          intros.
          apply Rinv_pos.
          generalize (pow_lt 2 n); lra.
        }
        lra.
      + apply ex_Rbar_plus_pos.
        * rewrite Lim_seq_const; simpl; lra.
        * apply Lim_seq_pos; intros.
          apply list_sum_pos_pos'.
          apply Forall_map.
          apply Forall_forall; intros.
          left.
          apply Rinv_pos.
          apply pow_lt; lra.
  Qed.

  Lemma ELim_seq_sum_2n : ELim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ (S x)) (seq 0 n))) = 1.
  Proof.
    rewrite Elim_seq_fin.
    apply Lim_seq_sum_2n.
  Qed.


  Lemma ELim_seq_Rbar_sum_2n :
    ELim_seq (sum_Rbar_n (fun x : nat => Finite (/ 2 ^ (S x)))) = 1.
  Proof.
    unfold sum_Rbar_n.
    erewrite ELim_seq_ext
    ; [| intros ?; rewrite <- map_map; rewrite list_Rbar_sum_map_finite; reflexivity].
    apply ELim_seq_sum_2n.
  Qed.
    
  Lemma ELim_seq_sum_eps2n f eps :
    (0 <= eps) ->
    (forall x, Rbar_le 0 (f x)) ->
    ELim_seq (fun i => sum_Rbar_n (fun a => Rbar_plus (f a) (eps / 2 ^ (S a))) i) =
      Rbar_plus (ELim_seq (fun i => sum_Rbar_n f i)) eps.
  Proof.
    intros.
    assert (epsdivpos:forall i, 0 <= (eps / (2 * 2 ^ i))).
    {
      intros.
      apply Rdiv_le_0_compat; trivial.
      apply Rmult_lt_0_compat; try lra.
      apply pow_lt; lra.
    } 

    erewrite ELim_seq_ext
    ; [| intros; rewrite sum_Rbar_n_nneg_plus; [reflexivity |..]]
    ; trivial.
    - rewrite ELim_seq_plus.
      + f_equal.
        rewrite (ELim_seq_ext _ (sum_Rbar_n (fun x : nat => Rbar_mult eps (/ 2 ^ (S x))))) by reflexivity.
        unfold sum_Rbar_n.
        erewrite ELim_seq_ext
        ; [| intros; apply list_Rbar_sum_const_mulR].
        generalize ELim_seq_Rbar_sum_2n.
        unfold sum_Rbar_n; intros HH.
        rewrite ELim_seq_scal_l.
        * rewrite HH.
          now rewrite Rbar_mult_1_r.
        * now rewrite HH.
      + apply ex_Elim_seq_incr; intros.
        now apply sum_Rbar_n_pos_incr.
      + apply ex_Elim_seq_incr; intros.
        apply sum_Rbar_n_pos_incr; intros; simpl; trivial.
      + apply ex_Rbar_plus_pos
        ; apply ELim_seq_pos
        ; intros
        ; apply sum_Rbar_n_nneg_nneg
        ; intros
        ; trivial
        ; simpl
        ; trivial.
    - intros; simpl; trivial.
  Qed.

  Global Instance outer_μ_outer_measure : is_outer_measure outer_μ.
  Proof.
    unfold outer_μ.
    apply is_outer_measure_alt_iff.
    constructor.
    - apply antisymmetry; try apply outer_μ_nneg.
      unfold Rbar_glb, proj1_sig; match_destr; destruct r as [lb glb].
      apply lb.
      exists (fun _ => event_none).
      split.
      + firstorder.
      + rewrite <- (ELim_seq_const 0).
        apply ELim_seq_ext; intros.
        unfold sum_Rbar_n.
        induction (seq 0 n); simpl; trivial.
        rewrite IHl, measure_none; simpl.
        now rewrite Rbar_plus_0_l.
    - intros.
      apply outer_μ_nneg.
    - intros ???.
      apply Rbar_glb_subset
      ; intros ? [? [??]].
      exists x1.
      split; trivial.
      now rewrite H.
    - intros B.
      assert (lim_seq_nneg:
               Rbar_le 0
                       (ELim_seq
                          (fun i : nat =>
                             sum_Rbar_n
                               (fun n : nat =>
                                  Rbar_glb
                                    (fun x : Rbar =>
                                       exists an : nat -> event σ,
                                         pre_event_sub (B n) (union_of_collection an) /\ x = outer_μ_of_covers an)) i))).
      {
        apply ELim_seq_pos; intros.
        apply sum_Rbar_n_nneg_nneg; intros k klt.
        apply Rbar_glb_ge; intros ? [?[??]]; subst.
        apply outer_μ_of_covers_nneg.
      } 
      case_eq (ELim_seq
       (fun i : nat =>
        sum_Rbar_n
          (fun n : nat =>
           Rbar_glb
             (fun x : Rbar =>
              exists an : nat -> event σ,
                pre_event_sub (B n) (union_of_collection an) /\ x = outer_μ_of_covers an)) i)).
      + (* finite *)
        intros ??.

        assert (isnneg : forall n,
                   Rbar_le 0
                           (Rbar_glb
                              (fun x : Rbar =>
                                 exists an : nat -> event σ,
                                   pre_event_sub (B n) (union_of_collection an) /\
                                     x = outer_μ_of_covers an))).
        {
          intros.
          apply Rbar_glb_ge; intros ? [?[??]]; subst.
          apply outer_μ_of_covers_nneg.
        } 

        assert (isfin : forall n,
                   is_finite (Rbar_glb
                                (fun x : Rbar =>
                                   exists an : nat -> event σ,
                                     pre_event_sub (B n) (union_of_collection an) /\
                                       x = outer_μ_of_covers an))).
        {
          apply (Elim_seq_sum_pos_fin_n_fin _ _ isnneg H).
        }

        apply Rbar_le_forall_Rbar_le; intros eps.

        
        
        assert (p:forall n,
                 exists (e:event σ),
                   pre_event_sub (B n) e /\
                     Rbar_le (μ e)
                             (Rbar_plus (
                                  outer_μ (B n))
                                        (eps/(pow 2 (S n))))).
        {
          intros n.
          specialize (isfin n).
          unfold outer_μ, Rbar_glb, proj1_sig in *; match_destr.
          rewrite <- isfin in r0.
          assert (posdiv: 0 < (eps / 2 ^ (S n))).
          {
            apply Rdiv_lt_0_compat.
            - apply cond_pos.
            - apply pow_lt; lra.
          } 
          destruct (Rbar_is_glb_fin_close_classic (mkposreal _ posdiv) r0) as [? [[?[??]] ?]]; subst.
          exists (union_of_collection x1).
          split; trivial.
          simpl in H2.
          rewrite <- isfin; simpl.
          eapply Rbar_le_trans; try eapply H2.
          now apply measure_countable_sub_union.
        }
 
        apply choice in p; trivial.
        
        destruct p as [an HH].

        rewrite <- H.

        assert (le1:
                 Rbar_le
                   (ELim_seq
                      (fun i : nat =>
                         sum_Rbar_n
                           (fun x : nat => μ (an x)) i))
                   (ELim_seq
                      (fun i : nat =>
                         sum_Rbar_n
                           (fun x : nat => (Rbar_plus (outer_μ (B x)) (eps / 2 ^ S x))) i))).
        {
          apply ELim_seq_le; intros.
          apply sum_Rbar_n_monotone; trivial; intros ?.
          apply HH.
        }
        rewrite ELim_seq_sum_eps2n in le1; trivial
        ; try solve [destruct eps; simpl; lra].
        etransitivity
        ; [etransitivity |]
        ; [ | apply le1 | ].
        * unfold Rbar_glb, proj1_sig; match_destr.
          apply r0.
          exists an.
          split; trivial.
          intros ??.
          destruct H0.
          exists x1.
          now apply (HH x1).
        * reflexivity.
      + intros H.
        unfold Rbar_le; match_destr.
      + intros H. rewrite H in lim_seq_nneg.
        now simpl in lim_seq_nneg.
  Qed.
  
  Lemma outer_μ_is_measurable (A:event σ) : μ_measurable outer_μ A.
  Proof.
    apply μ_measurable_simpl; intros B.
    unfold outer_μ.
    unfold Rbar_glb, proj1_sig.
    repeat match_destr.
    destruct r as [lb1 glb1].    
    destruct r0 as [lb2 glb2].
    destruct r1 as [lb0 glb0].
    apply glb0; intros ? [?[??]].
    rewrite H0; clear x2 H0.
    unfold is_lb_Rbar in *.
    assert (nneg:Rbar_le 0 (outer_μ_of_covers x3)).
    {
      apply outer_μ_of_covers_nneg.
    } 
    case_eq (outer_μ_of_covers x3); simpl.
    - (* finite *)
      intros ? eqq1.
      specialize (lb1 (outer_μ_of_covers (fun n => event_inter (x3 n) A))).
      cut_to lb1.
      + specialize (lb2 (outer_μ_of_covers (fun n => event_diff (x3 n) A))).
        cut_to lb2.
        * {
          etransitivity.
          - eapply Rbar_plus_le_compat; try eassumption.
          - unfold outer_μ_of_covers.
            rewrite <- ELim_seq_plus.
            + rewrite <- eqq1.
              unfold outer_μ_of_covers.
              apply ELim_seq_le; intros.
              rewrite <- sum_Rbar_n_nneg_plus by (intros; apply measure_nneg).
              apply sum_Rbar_n_monotone; trivial; intros ?.
              rewrite <- measure_disjoint_union; trivial.
              * apply measure_monotone; trivial.
                firstorder.
              * firstorder.
            + now apply is_measure_ex_Elim_seq.
            + now apply is_measure_ex_Elim_seq.
            + apply ex_Rbar_plus_pos
              ; apply outer_μ_of_covers_nneg.
        } 
        * 
          eexists; split; try reflexivity.
          rewrite H.
          repeat rewrite pre_of_union_of_collection.
          now rewrite pre_event_countable_union_diff_distr.
      + 
        eexists; split; try reflexivity.
        rewrite H.
        repeat rewrite pre_of_union_of_collection.
        rewrite pre_event_inter_comm.
        rewrite pre_event_inter_countable_union_distr.
        apply pre_union_of_collection_sub_proper; intros ?.
        rewrite pre_event_inter_comm.
        reflexivity.
    - intros; simpl.
      unfold Rbar_le; match_destr.
    - intros HH; rewrite HH in nneg; simpl in nneg; contradiction.
  Qed.

  Lemma outer_μ_μ (A:event σ) : outer_μ A = μ A.
  Proof.
    unfold outer_μ.
    unfold Rbar_glb, proj1_sig; match_destr.
    destruct r as [lb glb].
    unfold is_lb_Rbar in *.
    apply antisymmetry.
    - case_eq (μ A); simpl.
      + intros.
        apply lb.
        exists (list_collection [A] ∅).
        split.
        * intros ??.
          now (exists 0%nat; simpl).
        * unfold outer_μ_of_covers.
          unfold list_collection.
          rewrite seq_sum_list_sum.
          -- simpl.
             now rewrite Rbar_plus_0_r.
          -- apply measure_none.
      + intros; now destruct x.
      + intros.
        generalize (measure_nneg A); rewrite H.
        now destruct x.
    - apply glb; intros ? [? [??]].
      rewrite H0.
      unfold outer_μ_of_covers.
      transitivity (μ (union_of_collection x1)).
      + now apply measure_monotone.
      + now apply measure_countable_sub_union.
  Qed.

End omf.
