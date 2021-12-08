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
Require Import Classical ClassicalFacts.
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

Section demorgan.
    Context {T:Type}.

    Lemma pre_event_complement_union (E1 E2:pre_event T) :
      pre_event_equiv (pre_event_complement (pre_event_union E1 E2))
                      (pre_event_inter (pre_event_complement E1) (pre_event_complement E2)).
    Proof.
    red; intros.
    split; intros.
    - now apply not_or_and.
    - now apply and_not_or.
  Qed.

    Lemma pre_event_complement_inter (E1 E2:pre_event T) :
      pre_event_equiv (pre_event_complement (pre_event_inter E1 E2))
                      (pre_event_union (pre_event_complement E1) (pre_event_complement E2)).
    Proof.
    red; intros.
    split; intros.
    - now apply not_and_or.
    - now apply or_not_and.
  Qed.

  Lemma pre_event_complement_union_of_collection (E : nat -> pre_event T) :
    pre_event_equiv (pre_event_complement (pre_union_of_collection E))
                    (pre_inter_of_collection (fun n => pre_event_complement (E n))).
  Proof.
    intros ?.
    unfold pre_event_complement, pre_inter_of_collection, pre_union_of_collection.
    firstorder.
  Qed.

    Lemma pre_event_inter_diff' (a b c:pre_event T) :
      pre_event_equiv (pre_event_inter a (pre_event_diff b c))
                      (pre_event_diff (pre_event_inter a b) (pre_event_inter a c)).
    Proof.
      firstorder.
    Qed.

    Lemma pre_event_inter_diff (a b c:pre_event T) :
      pre_event_equiv (pre_event_inter a (pre_event_diff b c))
                      (pre_event_diff (pre_event_inter a b) c).
    Proof.
      repeat rewrite pre_event_diff_derived.
      now rewrite <- pre_event_inter_assoc.
    Qed.

End demorgan.

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
        (f:pre_event T -> Rbar) (B:list (pre_event T)) d :
    f d = 0 ->
    ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => f (pre_list_collection B d n)) i) = list_Rbar_sum (map f B).
  Proof.
    intros.
    rewrite (ELim_seq_ext_loc _ (fun _ => sum_Rbar_n (fun n : nat => f (pre_list_collection B d n)) (length B))).
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
                 (fun x : nat => f (pre_list_collection B d (length B + x)))
                 (fun x : nat => 0)).
      + rewrite fold_right_Rbar_plus_const.
        now rewrite Rbar_mult_0_r.
      + intros ?.
        unfold pre_list_collection.
        rewrite nth_overflow; trivial.
        lia.
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
  Context {T:Type}.
  Context {σ:SigmaAlgebra T}.
  Context {ps:ProbSpace σ}.

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
      now rewrite pre_list_union_union.
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
    induction l.
    - simpl; reflexivity.
    -  simpl map; simpl fold_right.
      auto with prob.
  Qed.
  
  Lemma list_Rbar_sum_measure_perm (μ:pre_event T -> Rbar) {μ_outer:is_outer_measure μ} {l1 l2} :
    Permutation l1 l2 ->
    list_Rbar_sum (map μ l1) = list_Rbar_sum (map μ l2).
  Proof.
    intros.
    unfold list_Rbar_sum.
    induction H; simpl; trivial.
    - now rewrite IHPermutation.
    - repeat rewrite <- Rbar_plus_assoc
      ; try apply ex_Rbar_plus_pos
      ; try apply outer_measure_nneg
      ; try apply measure_fold_right_Rbar_plus_nneg
      ; trivial.
      f_equal.
      now rewrite Rbar_plus_comm.
    - now rewrite IHPermutation1.
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

  Instance μ_measurable_sa (μ:pre_event T -> R) {μ_outer:is_outer_measure μ} :
    SigmaAlgebra T
    := {|
      sa_sigma E := μ_measurable μ E
    ; sa_countable_union := μ_measurable_countable_union μ
    ; sa_complement := μ_measurable_complement μ
    ; sa_all := μ_measurable_Ω μ
    |}.

End measure.

(*
  Definition outer_measure_of (A:pre_event T) 
    := Glb_Rbar (fun (x : R) =>
                   exists (an:nat->event S),
                     pre_event_sub A (union_of_collection an)
                     /\ sum_of_probs_equals ps_P an x).

 *)
  
  

  

  
