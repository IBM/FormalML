Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Export RandomVariableLpR RandomVariableL2.
Require Import quotient_space.
Require Import RbarExpectation.

Require Import Event.
Require Import Almost.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section sa_sub_props.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).
  
  Definition event_sa_sub 
             (x:event dom2) : event dom
    := exist _ (event_pre x) (sub _ (proj2_sig x)).

  Global Instance event_sa_sub_equiv_proper :
    Proper (event_equiv ==> event_equiv) event_sa_sub.
  Proof.
    repeat red; intros.
    simpl.
    specialize (H x0).
    destruct x; destruct y; simpl in *.
    intuition.
  Qed.

  Lemma collection_is_pairwise_disjoint_sa_sub collection :
    collection_is_pairwise_disjoint collection ->
    collection_is_pairwise_disjoint (fun n : nat => event_sa_sub (collection n)).
  Proof.
    unfold collection_is_pairwise_disjoint; intros.
    unfold event_disjoint; simpl.
    now apply H.
  Qed.

  Lemma union_of_collection_sa_sub collection :
    event_equiv
      (event_sa_sub (union_of_collection collection))
      (union_of_collection (fun n : nat => event_sa_sub (collection n))).
  Proof.
    intros x; simpl.
    reflexivity.
  Qed.

  Instance RandomVariable_sa_sub {Td} {cod : SigmaAlgebra Td}
           x
           {rv_x:RandomVariable dom2 cod x}
    : RandomVariable dom cod x.
  Proof.
    intros e.
    specialize (rv_x e).
    now apply sub.
  Qed.

End sa_sub_props.

Section sa_sub_prob.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Instance prob_space_sa_sub : ProbSpace dom2.
  Proof.
    exists (fun x => ps_P (event_sa_sub sub x)).
    - repeat red; intros.
      now rewrite H.
    - intros.
      generalize (ps_countable_disjoint_union (fun n => event_sa_sub sub (collection n)))
      ; intros HH.
      cut_to HH.
      + rewrite union_of_collection_sa_sub.
        unfold sum_of_probs_equals in *.
        apply HH.
      + now apply collection_is_pairwise_disjoint_sa_sub.
    - erewrite ps_proper; try eapply ps_one.
      unfold Ω, pre_Ω.
      repeat red; intros; simpl; tauto.
    - intros.
      apply ps_pos.
  Defined.

  Lemma almostR2_prob_space_sa_sub_lift
        RR
        (f1 f2:Ts -> R):
    almostR2 prob_space_sa_sub RR f1 f2 ->
    almostR2 prts RR f1 f2.
  Proof.
    intros [p [pone peqq]].
    red.
    simpl in *.
    exists (event_sa_sub sub p).
    split; trivial.
  Qed.
  
  Lemma almostR2_prob_space_sa_sub_lift_Rbar
        RR
        (f1 f2:Ts -> Rbar):
    almostR2 prob_space_sa_sub RR f1 f2 ->
    almostR2 prts RR f1 f2.
  Proof.
    intros [p [pone peqq]].
    red.
    simpl in *.
    exists (event_sa_sub sub p).
    split; trivial.
  Qed.

  Lemma almost_prob_space_sa_sub_lift
        (prop : Ts -> Prop) :
    almost prob_space_sa_sub prop ->
    almost prts prop.
  Proof.
    intros [p [pone peqq]].
    red.
    simpl in *.
    exists (event_sa_sub sub p).
    split; trivial.
  Qed.

  Lemma SimpleExpectation_prob_space_sa_sub
        (x:Ts->R)
        {rv:RandomVariable dom borel_sa x} 
        {rv2:RandomVariable dom2 borel_sa x} 
        {frf:FiniteRangeFunction x} :
    @SimpleExpectation Ts dom2 prob_space_sa_sub x rv2 frf =
    @SimpleExpectation Ts dom prts x rv frf.
  Proof.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext; intros.
    f_equal.
    simpl.
    apply ps_proper.
    intros ?.
    unfold preimage_singleton; simpl.
    tauto.
  Qed.

  Lemma NonnegExpectation_prob_space_sa_sub
        (x:Ts -> R)
        {pofrf:NonnegativeFunction x}
        {rv:RandomVariable dom2 borel_sa x}
        
    :
      @NonnegExpectation Ts dom2 prob_space_sa_sub  x pofrf =
      @NonnegExpectation Ts dom prts x pofrf.
  Proof.
    generalize ((RandomVariable_sa_sub sub x (rv_x:=rv)))
    ; intros rv1.
    

    assert (forall n, RandomVariable dom borel_sa (simple_approx (fun x0 : Ts => x x0) n)).
    {
      apply simple_approx_rv.
      * now apply positive_Rbar_positive.
      * typeclasses eauto.
    } 

    assert (forall n, RandomVariable dom2 borel_sa (simple_approx (fun x0 : Ts => x x0) n)).
    {
      apply simple_approx_rv.
      * now apply positive_Rbar_positive.
      * typeclasses eauto.
    } 

    rewrite <- (monotone_convergence x (simple_approx x)
                                    rv1 pofrf
                                    (fun n => simple_approx_rv _ _)
                                    (fun n => simple_approx_pofrf _ _)).
    rewrite <- (monotone_convergence x (simple_approx x)
                                    rv pofrf
                                    (fun n => simple_approx_rv _ _)
                                    (fun n => simple_approx_pofrf _ _)).
    - apply Lim_seq_ext; intros n.
      repeat erewrite <- simple_NonnegExpectation.
      apply SimpleExpectation_prob_space_sa_sub.
    - intros n a.
      apply (simple_approx_le x pofrf n a).
    - intros n a.
      apply (simple_approx_increasing x pofrf n a).
    - intros n.
      apply simple_expectation_real; trivial.
      apply simple_approx_frf.
    - intros.
      apply (simple_approx_lim_seq x).
      now apply positive_Rbar_positive.
    - intros n a.
      apply (simple_approx_le x pofrf n a).
    - intros n a.
      apply (simple_approx_increasing x pofrf n a).
    - intros n.
      apply simple_expectation_real; trivial.
      apply simple_approx_frf.
    - intros.
      apply (simple_approx_lim_seq x).
      now apply positive_Rbar_positive.

      Unshelve.
      apply simple_approx_frf.
  Qed.

  Lemma Expectation_prob_space_sa_sub
        (x:Ts->R)
        {rv:RandomVariable dom2 borel_sa x} :
    @Expectation Ts dom2 prob_space_sa_sub  x =
    @Expectation Ts dom prts x.
  Proof.
    generalize ((RandomVariable_sa_sub sub x (rv_x:=rv)))
    ; intros rv1.

    unfold Expectation.
    repeat rewrite NonnegExpectation_prob_space_sa_sub by typeclasses eauto.
    reflexivity.
  Qed.

  Lemma Rbar_NonnegExpectation_prob_space_sa_sub
        (x:Ts->Rbar)
        {pofrf:Rbar_NonnegativeFunction x}
        {rv:RandomVariable dom2 Rbar_borel_sa x}
        
    :
      @Rbar_NonnegExpectation Ts dom2 prob_space_sa_sub x pofrf =
      @Rbar_NonnegExpectation Ts dom prts x pofrf.
  Proof.
    generalize ((RandomVariable_sa_sub sub x (rv_x:=rv)))
    ; intros rv1.
    

    assert (forall n, RandomVariable dom borel_sa (simple_approx (fun x0 : Ts => x x0) n)).
    {
      intros.
      apply simple_approx_rv; trivial.
    } 

    assert (forall n, RandomVariable dom2 borel_sa (simple_approx (fun x0 : Ts => x x0) n)).
    {
      intros.
      apply simple_approx_rv; trivial.
    } 

    rewrite <- (Rbar_monotone_convergence x (simple_approx x)
                                         rv1 pofrf
                                         (fun n => simple_approx_rv _ _)
                                         (fun n => simple_approx_pofrf _ _)).
    rewrite <- (Rbar_monotone_convergence x (simple_approx x)
                                         rv pofrf
                                         (fun n => simple_approx_rv _ _)
                                         (fun n => simple_approx_pofrf _ _)).
    - apply Lim_seq_ext; intros n.
      repeat erewrite <- simple_NonnegExpectation.
      apply SimpleExpectation_prob_space_sa_sub.
    - intros n a.
      apply (simple_approx_le x pofrf n a).
    - intros n a.
      apply (simple_approx_increasing x pofrf n a).
    - intros n.
      apply simple_expectation_real; trivial.
      apply simple_approx_frf.
    - intros.
      apply (simple_approx_lim_seq x); trivial.
    - intros n a.
      apply (simple_approx_le x pofrf n a).
    - intros n a.
      apply (simple_approx_increasing x pofrf n a).
    - intros n.
      apply simple_expectation_real; trivial.
      apply simple_approx_frf.
    - intros.
      apply (simple_approx_lim_seq x); trivial.
      Unshelve.
      apply simple_approx_frf.
  Qed.

  Lemma Rbar_Expectation_prob_space_sa_sub
        (x:Ts->Rbar)
        {rv:RandomVariable dom2 Rbar_borel_sa x} :
    @Rbar_Expectation Ts dom2 prob_space_sa_sub  x =
    @Rbar_Expectation Ts dom prts x.
  Proof.
    generalize ((RandomVariable_sa_sub sub x (rv_x:=rv)))
    ; intros rv1.

    unfold Rbar_Expectation.
    repeat rewrite Rbar_NonnegExpectation_prob_space_sa_sub by typeclasses eauto.
    reflexivity.
  Qed.

  Lemma IsLp_prob_space_sa_sub
        p (x:Ts->R)
        {rv:RandomVariable dom2 borel_sa x} :
    IsLp prts p x <->
    IsLp prob_space_sa_sub p x.
  Proof.
    unfold IsLp, IsFiniteExpectation; intros.
    now rewrite Expectation_prob_space_sa_sub by typeclasses eauto.
  Qed.

  Lemma IsFiniteExpectation_prob_space_sa_sub
        (x:Ts->R)
        {rv:RandomVariable dom2 borel_sa x}
        {isfe:IsFiniteExpectation prob_space_sa_sub x} :
    IsFiniteExpectation prts x.
  Proof.
    unfold IsFiniteExpectation in *.
    now rewrite Expectation_prob_space_sa_sub in isfe by trivial.
  Qed.

  Lemma IsFiniteExpectation_prob_space_sa_sub_f
        (x:Ts->R)
        {rv:RandomVariable dom2 borel_sa x}
        {isfe:IsFiniteExpectation prts x} :
    IsFiniteExpectation prob_space_sa_sub x.
  Proof.
    unfold IsFiniteExpectation in *.
    now erewrite Expectation_prob_space_sa_sub.
  Qed.

  Lemma FiniteExpectation_prob_space_sa_sub
        (x:Ts->R)
        {rv:RandomVariable dom2 borel_sa x}
        {isfe1:IsFiniteExpectation prob_space_sa_sub x}
        {isfe2:IsFiniteExpectation prts x} :
    FiniteExpectation prob_space_sa_sub x =
    FiniteExpectation prts x.
  Proof.
    unfold FiniteExpectation, proj1_sig.
    repeat match_destr.
    rewrite Expectation_prob_space_sa_sub in e by trivial.
    congruence.
  Qed.

  Lemma Rbar_IsFiniteExpectation_prob_space_sa_sub
        (x:Ts->Rbar)
        {rv:RandomVariable dom2 Rbar_borel_sa x}
        {isfe:Rbar_IsFiniteExpectation prob_space_sa_sub x} :
    Rbar_IsFiniteExpectation prts x.
  Proof.
    unfold Rbar_IsFiniteExpectation in *.
    now rewrite Rbar_Expectation_prob_space_sa_sub in isfe by trivial.
  Qed.

  Lemma Rbar_IsFiniteExpectation_prob_space_sa_sub_f
        (x:Ts->Rbar)
        {rv:RandomVariable dom2 Rbar_borel_sa x}
        {isfe:Rbar_IsFiniteExpectation prts x} :
    Rbar_IsFiniteExpectation prob_space_sa_sub x.
  Proof.
    unfold Rbar_IsFiniteExpectation in *.
    now erewrite Rbar_Expectation_prob_space_sa_sub.
  Qed.

End sa_sub_prob.

Section ortho_project.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  (* the conditional expectation of x over the sub-algebra dom2 *)

  Definition ortho_phi (dom2 : SigmaAlgebra Ts)
    : LpRRVq prts 2 -> Prop
    := (fun y:LpRRVq prts 2 =>
          exists z, Quot _ z = y /\
               RandomVariable dom2 borel_sa (LpRRV_rv_X prts z)).

  Definition LpRRV_filter_from_seq {dom2:SigmaAlgebra Ts} {prts2 : ProbSpace dom2}
             (f : nat -> LpRRV prts2 2) : ((LpRRV_UniformSpace prts2 big2 -> Prop) -> Prop) :=
    fun (P : (LpRRV_UniformSpace prts2 big2 -> Prop)) => exists (N:nat), forall (n:nat), (n >= N)%nat -> P (f n).

  Lemma cauchy_filterlim_almost_unique_eps (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
    (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
    forall (eps:posreal), LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) < eps.
  Proof.
    intros.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/2) by lra.
    specialize (H (mkposreal _ H2)).
    specialize (H0 (mkposreal _ H2)).     
    generalize (Hierarchy.filter_and _ _ H H0); intros.
    apply filter_ex in H3.
    unfold LpRRVball in H3.
    destruct H3 as [? [? ?]].
    generalize (LpRRV_dist_triang prts big2 x x0 y); intros.
    unfold LpRRV_dist in H5.
    eapply Rle_lt_trans.
    apply H5.
    rewrite LpRRVnorm_minus_sym in H4.
    simpl in H3; simpl in H4; simpl.
    lra.
  Qed.     

  Lemma cauchy_filterlim_almost_unique_eps_alt (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
    (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
    forall (eps:posreal), LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) < eps.
  Proof.
    intros.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/4) by lra.
    destruct (H (mkposreal _ H2)) as [x0 [? ?]].
    destruct (H0 (mkposreal _ H2)) as [y0 [? ?]].
    generalize (Hierarchy.filter_and _ _ H3 H5); intros.
    apply filter_ex in H7.
    unfold LpRRVball in H7.
    destruct H7 as [? [? ?]].
    generalize (LpRRV_dist_triang prts big2 x x0 x1); intros.
    generalize (LpRRV_dist_triang prts big2 x1 y0 y); intros.
    unfold LpRRV_dist in H9.
    unfold LpRRV_dist in H10.
    generalize (LpRRV_dist_triang prts big2 x x1 y); intros.
    unfold LpRRV_dist in H11.
    apply LpRRV_ball_sym in H4; unfold LpRRVball in H4; simpl in H4.
    simpl in H7.
    rewrite LpRRVnorm_minus_sym in H8; simpl in H8.
    unfold LpRRVball in H6; simpl in H6.
    eapply Rle_lt_trans.
    apply H11.
    assert (LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x x1) < eps/2).
    {
      eapply Rle_lt_trans.
      apply H9.
      simpl; lra.
    }
    assert (LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x1 y) < eps/2).
    {
      eapply Rle_lt_trans.
      apply H10.
      simpl; lra.
    }
    lra.
  Qed.     

  Lemma cauchy_filterlim_almost_unique_0 (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
    (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
    LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) = 0.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_eps _ _ _ _ H H0); intros.
    apply nneg_lt_eps_zero; trivial.
    apply power_nonneg.
  Qed.

  Lemma cauchy_filterlim_almost_unique_alt_0 (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
    (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
    LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) = 0.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_eps_alt _ _ _ _ H H0); intros.
    apply nneg_lt_eps_zero; trivial.
    apply power_nonneg.
  Qed.

  Lemma cauchy_filterlim_almost_unique (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
    (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
    almostR2 prts eq x y.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_0 _ _ _ _ H H0); intros.
    apply LpRRV_norm0 in H1.
    now apply LpRRValmost_sub_zero_eq in H1.
  Qed.

  Lemma cauchy_filterlim_almost_unique_alt (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
    (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
    almostR2 prts eq x y.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_alt_0 _ _ _ _ H H0); intros.
    apply LpRRV_norm0 in H1.
    now apply LpRRValmost_sub_zero_eq in H1.
  Qed.
  
  Definition subset_to_sa_sub
             {dom2 : SigmaAlgebra Ts}
             (sub : sa_sub dom2 dom)
             (set:LpRRV_UniformSpace (prob_space_sa_sub prts sub) big2 -> Prop) :
    {x : LpRRV_UniformSpace prts big2 | RandomVariable dom2 borel_sa x} -> Prop.
  Proof.
    intros [x pfx].
    apply set.
    simpl.
    destruct x; simpl in *.
    exists LpRRV_rv_X; trivial.
    apply IsLp_prob_space_sa_sub; trivial.
  Defined.

  Definition subset_filter_to_sa_sub_filter
             {dom2 : SigmaAlgebra Ts}
             (sub : sa_sub dom2 dom)
             (F:({x : LpRRV_UniformSpace prts big2 | RandomVariable dom2 borel_sa x} -> Prop) -> Prop) :
    (LpRRV_UniformSpace (prob_space_sa_sub prts sub) big2 -> Prop) -> Prop.
  Proof.
    intros sa.
    apply F.
    eapply subset_to_sa_sub; eauto.
  Defined.

  Lemma subset_filter_to_sa_sub_filter_Filter {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) F :
    Filter F ->
    Filter (subset_filter_to_sa_sub_filter sub F).
  Proof.
    intros [FF1 FF2 FF3].
    unfold subset_filter_to_sa_sub_filter, subset_to_sa_sub.
    split.
    - eapply FF3; try eapply FF1; intros.
      destruct x; trivial.
    - intros.
      eapply FF3; try eapply FF2; [| eapply H | eapply H0].
      intros [??]; simpl; intros.
      tauto.
    - intros.
      eapply FF3; [| eapply H0].
      intros [??].
      eapply H.
  Qed.

  Lemma subset_filter_to_sa_sub_filter_proper {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) F :
    ProperFilter F ->
    ProperFilter (subset_filter_to_sa_sub_filter sub F).
  Proof.
    intros pf.
    unfold subset_filter_to_sa_sub_filter; simpl.
    constructor.
    - intros.
      destruct pf.
      destruct (filter_ex _ H).
      destruct x; simpl in *.
      eexists; eapply H0.
    - destruct pf.
      now apply subset_filter_to_sa_sub_filter_Filter.
  Qed.

  Definition prob_space_sa_sub_set_lift
             {dom2} (sub:sa_sub dom2 dom)
             (s:LpRRV (prob_space_sa_sub prts sub) 2 -> Prop)
             (x:LpRRV prts 2) : Prop.
  Proof.
    destruct x.
    destruct (ClassicalDescription.excluded_middle_informative (RandomVariable dom2 borel_sa LpRRV_rv_X)).
    - apply s.
      exists LpRRV_rv_X; trivial.
      now apply IsLp_prob_space_sa_sub.
    - exact False.
  Defined.

  Definition prob_space_sa_sub_LpRRV_lift
             {dom2} (sub:sa_sub dom2 dom)
             (s:LpRRV (prob_space_sa_sub prts sub) 2)
    : LpRRV prts 2.
  Proof.
    destruct s.
    exists LpRRV_rv_X.
    - eapply RandomVariable_sa_sub; eauto.
    - eapply IsLp_prob_space_sa_sub; eauto.
  Defined.

  Instance prob_space_sa_sub_LpRRV_lift_rv {dom2} (sub:sa_sub dom2 dom) (X:LpRRV (prob_space_sa_sub prts sub) 2)
           {rvx:RandomVariable dom2 borel_sa X} :
    RandomVariable dom2 borel_sa (prob_space_sa_sub_LpRRV_lift sub X).
  Proof.
    now destruct X; simpl in *.
  Qed.

  Lemma ortho_phi_closed 
        {dom2 : SigmaAlgebra Ts} 
        (sub : sa_sub dom2 dom) :
    @closed (LpRRVq_UniformSpace prts 2 big2) (ortho_phi dom2).
  Proof.
    unfold closed, ortho_phi, locally.
    intros.
    destruct (Quot_inv x); subst.
    generalize (not_ex_all_not _ _ H)
    ; intros HH1; clear H.
    generalize (fun n => not_all_ex_not _ _ (HH1 n))
    ; intros HH2; clear HH1.

    assert (HH3: forall n : posreal,
               exists n0 : LpRRVq_UniformSpace prts 2 big2,
                 @Hierarchy.ball  (LpRRVq_UniformSpace prts 2 big2) (Quot (LpRRV_eq prts) x0) n n0 /\
                 (exists z : LpRRV prts 2,
                     Quot (LpRRV_eq prts) z = n0 /\ RandomVariable dom2 borel_sa z)).
    {
      intros n.
      destruct (HH2 n).
      exists x.
      apply not_all_not_ex in H.
      destruct H.
      tauto.
    }
    clear HH2.
    
    assert (HH4: forall eps : posreal,
               exists z : LpRRV prts 2,
                 (@Hierarchy.ball (LpRRVq_UniformSpace prts 2 big2)
                                  (Quot (LpRRV_eq prts) x0) eps
                                  (Quot (LpRRV_eq prts) z)) /\
                 (RandomVariable dom2 borel_sa z)).
    {
      intros eps.
      destruct (HH3 eps) as [x [xH1 [z [xH2 xH3]]]]; subst.
      eauto.
    }
    clear HH3.
    assert (HH5: forall eps : posreal,
               exists z : LpRRV prts 2,
                 (@Hierarchy.ball (LpRRV_UniformSpace prts big2)
                                  x0 eps z) /\
                 (RandomVariable dom2 borel_sa z)).
    {
      intros eps.
      destruct (HH4 eps) as [x [? ?]].
      red in H; simpl in H.
      rewrite LpRRVq_ballE in H.
      eauto.
    }
    assert (forall (n : nat), 0 < (/ (INR (S n)))).
    {
      intros.
      apply Rinv_0_lt_compat.
      apply lt_0_INR.
      lia.
    }
    assert (forall (n:nat),
               {z:LpRRV prts 2 |
                 (LpRRVball prts big2 x0 (mkposreal _ (H n)) z) /\
                 (RandomVariable dom2 borel_sa z)}).
    {
      intros.
      destruct (constructive_indefinite_description _ (HH5 (mkposreal _ (H n))))
        as [x Fx].
      now exists x.
    }
    pose (f := fun (n : nat) => proj1_sig (X n)).
    assert (is_lim_seq (fun n => LpRRV_dist prts (p:=bignneg _ big2) (f n) x0) 0).
    {
      apply is_lim_seq_spec.
      unfold is_lim_seq'.
      intros.
      assert (0 < eps) by apply cond_pos.
      generalize (archimed_cor1 eps H0); intros.
      destruct H1 as [? [? ?]].
      exists x.
      intros.
      rewrite Rminus_0_r, Rabs_pos_eq.
      - unfold f.
        destruct (X n) as [? [? ?]].
        simpl.
        apply LpRRV_ball_sym in l.
        unfold LpRRVball in l.
        eapply Rlt_trans.
        apply l.
        apply Rlt_trans with (r2 := / INR x); trivial.
        apply Rinv_lt_contravar.
        apply Rmult_lt_0_compat.
        + now apply lt_0_INR.
        + apply lt_0_INR; lia.
        + apply lt_INR; lia.
      - unfold LpRRVnorm.
        apply power_nonneg.
    }
    pose (prts2 := prob_space_sa_sub prts sub).

    pose (F :=  LpRRV_filter_from_seq f).
    pose (dom2pred := fun v => RandomVariable dom2 borel_sa v).
    pose (F2 := subset_filter F dom2pred ).
    pose (F3:=subset_filter_to_sa_sub_filter sub F2).

    generalize (L2RRV_lim_complete prts2 big2 F3); intros HH1.

    
    assert (ProperFilter F).
    {
      subst F f.
      unfold LpRRV_filter_from_seq; simpl.
      split.
      - intros P [N HP].
        exists (proj1_sig (X N)).
        apply HP.
        lia.
      - split.
        + exists 0%nat; trivial.
        + intros P Q [NP HP] [NQ HQ].
          exists (max NP NQ); intros n nN.
          split.
          * apply HP.
            generalize (Max.le_max_l NP NQ); lia.
          * apply HQ.
            generalize (Max.le_max_r NP NQ); lia.
        + intros P Q Himp [N HP].
          exists N; intros n nN.
          auto.
    }

    assert (pfsub:ProperFilter (subset_filter F (fun v : LpRRV prts 2 => dom2pred v))).
    {
      apply subset_filter_proper; intros.
      subst F.
      subst f.
      unfold LpRRV_filter_from_seq in H2.
      destruct H2 as [? HH2].
      unfold dom2pred.
      exists (proj1_sig (X x)).
      split.
      - destruct (X x); simpl.
        tauto.
      - apply HH2; lia.
    } 
    
    assert (F3proper:ProperFilter F3).
    {
      unfold F3, F2.
      now apply subset_filter_to_sa_sub_filter_proper.
    }

    assert (F3cauchy:cauchy F3).
    {
      unfold F3, F2.
      unfold subset_filter_to_sa_sub_filter.
      intros eps; simpl.
      unfold F, f.
      unfold LpRRV_filter_from_seq; simpl.
      unfold dom2pred.
      assert (eps2pos:0 < eps / 2).
      {
        destruct eps; simpl.
        lra.
      } 

      destruct (archimed_cor1 (eps/2) eps2pos) as [N [Nlt Npos]].

      destruct (X N)
        as [x [XH XR]].
      assert (xlp:IsLp (prob_space_sa_sub prts sub) 2 x).
      {
        apply IsLp_prob_space_sa_sub; typeclasses eauto.
      } 
      exists (pack_LpRRV (prob_space_sa_sub prts sub) x).
      red.
      exists N.
      simpl.
      intros n nN ?.
      destruct (X n) as [Xn [XnH XnRv]]; simpl in *.
      unfold pack_LpRRV; simpl.
      generalize (LpRRV_dist_triang prts big2 x x0 Xn)
      ; intros triag.
      unfold LpRRV_dist in triag.
      unfold Hierarchy.ball; simpl.
      unfold LpRRVball; simpl.
      simpl in *.

      destruct Xn as [Xn ??]; simpl in *.
      apply LpRRV_ball_sym in XH.
      LpRRV_simpl.
      simpl in *.
      unfold LpRRVball in XnH, XH, triag.
      simpl in XnH, XH, triag.
      unfold LpRRVminus in XnH, XH, triag; simpl in XnH, XH, triag.
      
      unfold LpRRVnorm in *.
      erewrite FiniteExpectation_prob_space_sa_sub; try typeclasses eauto.
      unfold pack_LpRRV, prob_space_sa_sub in XnH, XH, triag |- *; simpl in *.
      eapply Rle_lt_trans; try eapply triag.
      replace (pos eps) with ((eps/2) + (eps/2)) by lra.
      assert (sNeps2:/ INR (S N) < eps /2).
      {
        apply Rle_lt_trans with (r2 := / INR N); trivial.
        apply Rinv_le_contravar.
        - apply lt_0_INR; lia.
        - apply le_INR; lia.
      }
      assert (sneps2:/ INR (S n) < eps /2).
      {
        apply Rle_lt_trans with (r2 := / INR (S N)); trivial.
        apply Rinv_le_contravar.
        - apply lt_0_INR; lia.
        - apply le_INR; lia.
      }
      apply Rplus_lt_compat.
      - rewrite <- sNeps2; trivial.
      - rewrite <- sneps2; trivial.
    } 
    cut_to HH1; trivial.
    exists (prob_space_sa_sub_LpRRV_lift sub (LpRRV_lim prts2 big2 F3)).
    split; [|typeclasses eauto].
    LpRRVq_simpl.
    unfold LpRRV_eq.
    apply (LpRRValmost_sub_zero_eq prts (p := bignneg 2 big2)).
    apply LpRRV_norm0.
    apply nneg_lt_eps_zero; [apply power_nonneg |].
    assert (forall (eps:posreal),
               exists (N:nat),
                 forall (n:nat), (n>=N)%nat ->
                          LpRRV_dist prts (p:=bignneg _ big2) (f n) x0 < eps).
    {
      intros.
      apply is_lim_seq_spec in H0.
      destruct (H0 eps).
      exists x; intros.
      specialize (H2 n H3).
      rewrite Rminus_0_r in H2.
      now rewrite Rabs_pos_eq in H2 by apply power_nonneg.
    }

    assert (F3limball:forall (eps:posreal),
               (LpRRV_dist prts  (p:=bignneg _ big2) (prob_space_sa_sub_LpRRV_lift sub (LpRRV_lim prts2 big2 F3)) x0) < eps).
    {
      intros.
      assert (0 < eps) by apply cond_pos.
      assert (0 < eps/2) by lra.
      destruct (HH1 (mkposreal _ H4)).
      destruct (H2 (mkposreal _ H4)).
      specialize (H6 (max x x1)).
      specialize (H5 (max x x1)).
      cut_to H5; try lia.
      cut_to H6; try lia.
      unfold F3, F2, F in H5.
      unfold LpRRV_filter_from_seq in H5.
      generalize (LpRRV_dist_triang prts big2 (prob_space_sa_sub_LpRRV_lift sub (LpRRV_lim prts2 big2 F3)) (f (max x x1)) x0); intros.
      rewrite Rplus_comm in H7.
      eapply Rle_lt_trans.
      apply H7.
      replace (pos eps) with ((eps/2) + (eps/2)) by lra.
      apply Rplus_lt_compat.
      apply H6.
      unfold dom2pred in H5.
      assert (frv:RandomVariable dom2 borel_sa (f (Init.Nat.max x x1))).
      {
        unfold f.
        unfold proj1_sig.
        match_destr; tauto.
      } 
      specialize (H5 frv).
      unfold subset_to_sa_sub, Hierarchy.ball in H5.
      simpl in H5.
      unfold LpRRVball, LpRRVnorm in H5.
      simpl in H5.
      unfold prts2 in H5.
      assert (isfe2:IsFiniteExpectation prts
                                        (rvpower
                                           (rvabs
                                              (rvminus
                                                 (LpRRV_lim (prob_space_sa_sub prts sub) big2
                                                            (subset_filter_to_sa_sub_filter sub
                                                                                            (subset_filter
                                                                                               (fun P : LpRRV prts 2 -> Prop =>
                                                                                                  exists N : nat, forall n : nat, (n >= N)%nat -> P (f n))
                                                                                               (fun v : LpRRV prts 2 => RandomVariable dom2 borel_sa v))))
                                                 (match
                                                     f (Init.Nat.max x x1) as l
                                                     return (RandomVariable dom2 borel_sa l -> LpRRV (prob_space_sa_sub prts sub) 2)
                                                   with
                                                   | {| LpRRV_rv_X := LpRRV_rv_X; LpRRV_lp := LpRRV_lp |} =>
                                                     fun pfx : RandomVariable dom2 borel_sa LpRRV_rv_X =>
                                                       {|
                                                         LpRRV_rv_X := LpRRV_rv_X;
                                                         LpRRV_rv := pfx;
                                                         LpRRV_lp := match IsLp_prob_space_sa_sub prts sub 2 LpRRV_rv_X with
                                                                     | conj x _ => x
                                                                     end LpRRV_lp |}
                                                   end frv))) (const 2))).
      {
        eapply (IsFiniteExpectation_prob_space_sa_sub prts sub); try typeclasses eauto.
        unfold FiniteExpectation, proj1_sig in H5.
        match_destr_in H5.
        red.
        now rewrite e.
      }       
      rewrite (FiniteExpectation_prob_space_sa_sub _ _ _ (isfe2:=isfe2)) in H5.
      unfold LpRRV_dist, LpRRVnorm.
      simpl.
      unfold f in *.
      eapply Rle_lt_trans; try eapply H5.
      right.
      f_equal.
      apply FiniteExpectation_ext; intros ?.
      rv_unfold.
      f_equal.
      f_equal.
      f_equal.
      - unfold prob_space_sa_sub_LpRRV_lift; simpl.
        unfold F3, F2, F.
        unfold LpRRV_filter_from_seq.
        simpl.
        unfold prts2, dom2pred.
        match_destr.
      - f_equal.
        clear H6.

        destruct (X (Init.Nat.max x x1)); simpl.
        match_destr.
    } 
    apply F3limball.
  Qed.

  Lemma ortho_phi_complete
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) :
    @complete_subset (@PreHilbert_NormedModule (@L2RRVq_PreHilbert Ts dom prts)) (ortho_phi dom2).
  Proof.
    unfold complete_subset.
    exists (LpRRVq_lim prts big2).
    intros F PF cF HH.
    assert (HHclassic: forall P : PreHilbert_NormedModule -> Prop,
               F P -> (exists x : PreHilbert_NormedModule, P x /\ ortho_phi dom2 x)).
    {
      intros P FP.
      specialize (HH P FP).
      now apply NNPP in HH.
    }
    clear HH.
    match goal with
      [|- _ /\ ?x ] => cut x; [split; trivial |]
    end.
    - apply ortho_phi_closed; trivial.
      simpl.
      unfold locally.
      intros [eps HH].
      specialize (H eps).
      destruct (HHclassic _ H) as [? [? ?]].
      specialize (HH x).
      elim HH; trivial.
      now rewrite <- hball_pre_uniform_eq.
    - intros.
      assert (cF':@cauchy (@LpRRVq_UniformSpace Ts dom prts (IZR (Zpos (xO xH))) big2) F).
      {
        now apply cauchy_pre_uniform.
      } 
      generalize (LpRRVq_lim_complete prts big2 F PF); intros.
      eapply filter_imp; try eapply (H cF' eps).
      + intros.
        unfold Hierarchy.ball; simpl.
        now apply L2RRVq_ball_ball.
  Qed.

  Program Definition ortho_projection_hilbert (E:PreHilbert) 
          (phi: E -> Prop) (phi_mod: compatible_m phi) (phi_compl: complete_subset phi)
          (u : E) : {v:E |
                      unique (fun v => phi v /\ norm (minus u v) = Glb_Rbar (fun r : R => exists w : E, phi w /\ r = norm (minus u w))) v}.
  generalize (ortho_projection_subspace phi phi_mod phi_compl u);intros.
  cut_to H.
  - destruct (constructive_definite_description _ H) as [x xH].
    exists x.
    split; trivial.
    destruct H as [y [yH1 yH2]].
    intros.
    transitivity y; [| eauto].
    symmetry; eauto.
  - intro; apply classic.
  Qed.

  Lemma ortho_phi_compatible_m
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
    : compatible_m (E:=(L2RRVq_PreHilbert prts)) (ortho_phi dom2).
  Proof.
    split; [split | ]; intros.
    - destruct H as [a [eqqa rv_a]]; subst.
      destruct H0 as [b [eqqb rv_b]]; subst.
      unfold plus, opp; simpl.
      rewrite LpRRVq_oppE, LpRRVq_plusE.
      eexists.
      split.
      + reflexivity.
      + typeclasses eauto.
    - exists (LpRRVq_zero prts).
      exists (LpRRVzero prts).
      simpl.
      split.
      + reflexivity.
      + typeclasses eauto.
    - destruct H as [a [eqqa Ha]]; subst.
      exists (LpRRVscale prts l a).
      simpl.
      split.
      + unfold scal; simpl.
        rewrite LpRRVq_scaleE.
        reflexivity.
      + typeclasses eauto.
  Qed.

End ortho_project.

Section is_cond_exp.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  (* The universal property that conditional expectations satisfy.
     This section shows its properties (including uniqueness).
     We later show existence (under reasonable conditions)
   *)
  
  Definition is_conditional_expectation
             (dom2 : SigmaAlgebra Ts)
             (f : Ts -> R)
             (ce : Ts -> Rbar)           
             {rvf : RandomVariable dom borel_sa f}
             {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    := forall P (dec:dec_pre_event P),
      sa_sigma (SigmaAlgebra := dom2) P ->
      Expectation (rvmult f (EventIndicator dec)) =
      Rbar_Expectation (Rbar_rvmult ce (EventIndicator dec)).
  
  Context {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Theorem is_conditional_expectation_Expectation
        (f : Ts -> R)
        (ce : Ts -> Rbar)           
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce} :
    is_conditional_expectation dom2 f ce ->
    Expectation f = Rbar_Expectation ce.
  Proof.
    intros HH.
    specialize (HH pre_Ω (dsa_dec dsa_Ω) sa_all).
    etransitivity.
    - etransitivity; [| apply HH].
      apply Expectation_ext.
      intros ?.
      rv_unfold.
      simpl; lra.
    - apply Rbar_Expectation_ext.
      intros ?.
      rv_unfold.
      unfold Rbar_rvmult.
      simpl.
      now rewrite Rbar_mult_1_r.
  Qed.

  Lemma is_conditional_expectation_FiniteExpectation
        (f : Ts -> R)
        (ce : Ts -> Rbar)           
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce} :
    is_conditional_expectation dom2 f ce ->
    IsFiniteExpectation prts f <-> Rbar_IsFiniteExpectation prts ce.
  Proof.
    unfold IsFiniteExpectation, Rbar_IsFiniteExpectation.
    intros HH.
    now erewrite (is_conditional_expectation_Expectation) by eauto.
  Qed.

  (* is_conditional_expectation is proper up to almost *)
  Theorem is_conditional_expectation_proper
        (f1 f2 : Ts -> R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf1 : RandomVariable dom borel_sa f1}
        {rvf2 : RandomVariable dom borel_sa f2}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
    : almostR2 prts eq f1 f2 ->
      almostR2 prts eq ce1 ce2 ->
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2.
  Proof.
    unfold is_conditional_expectation
    ; intros eqq1 eqq2 is1 P dec saP.
    specialize (is1 P dec saP).
    etransitivity.
    - etransitivity; [| apply is1].
      apply Expectation_almostR2_proper.
      + apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        now apply sub.
      + apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv.
        now apply sub.
      + apply almostR2_eq_mult_proper; trivial.
        * now symmetry.
        * reflexivity.
    - apply Rbar_Expectation_almostR2_proper.
      + apply Rbar_rvmult_rv; trivial.
        * eapply RandomVariable_sa_sub; eauto.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + apply Rbar_rvmult_rv; trivial.
        * eapply RandomVariable_sa_sub; eauto.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + apply almostR2_eq_Rbar_mult_proper; trivial.
        reflexivity.
  Qed.

  (* is_conditional_expectation is also almost unique, as long as the 
     input function is finite expectation, or is nonnegative.
     Failing that, if both candidates are almost finite, then the result still holds.
   *)
  
  Lemma is_conditional_expectation_nneg_le
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        {nnf : NonnegativeFunction f}
        {nnf1 : Rbar_NonnegativeFunction ce1}
        {nnf2 : Rbar_NonnegativeFunction ce2}
    : is_conditional_expectation dom2 f ce1 ->
      is_conditional_expectation dom2 f ce2 ->
      almostR2 (prob_space_sa_sub prts sub) Rbar_le ce1 ce2.
  Proof.
    unfold is_conditional_expectation; intros isce1 isce2.

    pose (G := fun x:R => pre_event_inter (fun omega => Rbar_gt (ce1 omega) (ce2 omega)) (fun omega => Rbar_gt x (ce2 omega))).
    assert (sa_G : forall x:R, sa_sigma (G x)).
    {
      intros x.
      unfold G.
      unfold pre_event_inter.
      apply (sa_proper _ 
                       (fun x0 : Ts => (Rbar_gt ((Rbar_rvminus ce1 (Rbar_finite_part ce2)) x0) 0) /\ Rbar_lt (ce2 x0) x )).
      - intro z.
        unfold Rbar_rvminus, Rbar_rvopp, Rbar_finite_part.
        split; intros.
        + destruct H.
          split; try easy.
          unfold Rbar_rvplus in H.
          assert (is_finite (ce2 z)).
          * eapply bounded_is_finite.
            apply nnf2.
            apply Rbar_lt_le.
            apply H0.
          * rewrite <- H1 in H |- *.
            unfold Rbar_opp in H.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (ce2 z)) in H.
            rewrite Rbar_plus_0_l in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
        + destruct H.
          unfold Rbar_gt in H0.
          assert (is_finite (ce2 z)).
          * eapply bounded_is_finite.
            apply nnf2.
            apply Rbar_lt_le.
            apply H0.
          * split; try easy.
            unfold Rbar_rvplus.
            rewrite <- H1 in H |- *.
            unfold Rbar_opp.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (- ce2 z)) in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
      - apply sa_inter.
        + apply Rbar_sa_le_gt; intros.
          apply Rbar_plus_measurable.
          * typeclasses eauto.
          * apply rv_Rbar_measurable.
            apply Rbar_rvopp_rv.
            apply Real_Rbar_rv.
            apply measurable_rv.
            now apply Rbar_finite_part_meas.
        + apply Rbar_sa_le_lt.
          intros.
          now apply rv_Rbar_measurable.
    }

    pose (IG := fun x:R => EventIndicator (classic_dec (G x))).

    assert (nneg12I:forall x:R, Rbar_NonnegativeFunction (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun omega : Ts => IG x omega))).
    {
      intros x omega.
      unfold IG, classic_dec; simpl.
      unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp; simpl.
      rv_unfold.
      destruct (excluded_middle_informative (G x omega)).
      - rewrite Rbar_mult_1_r.
        destruct g.
        destruct (ce1 omega); destruct (ce2 omega); simpl in *; try tauto.
        lra.
      - rewrite Rbar_mult_0_r.
        lra.
    } 
    
    assert (eqq1:forall x, Rbar_NonnegExpectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (IG x)) =
                           Rbar_minus (Rbar_NonnegExpectation (Rbar_rvmult ce1 (IG x)))
                                      (Rbar_NonnegExpectation (Rbar_rvmult ce2 (IG x)))).
    {
      intros x.

      generalize (@Rbar_NonnegExpectation_minus_bounded2 _ _ prts (Rbar_rvmult ce1 (IG x)) (Rbar_rvmult ce2 (IG x))); intros HH.
      cut_to HH.
      - unfold IG in HH.
        specialize (HH _ (Rabs x) (Rabs_pos _)).
        cut_to HH.
        + specialize (HH _).
          assert ( nnf12 : Rbar_NonnegativeFunction
                             (Rbar_rvminus (Rbar_rvmult ce1 (IG x))
                                           (Rbar_rvmult ce2 (IG x)))).
          {
            intros a.
            unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, IG, EventIndicator; simpl.
            destruct (classic_dec (G x) a); simpl.
            - repeat rewrite Rbar_mult_1_r.
              destruct g as [??].
              destruct (ce1 a); destruct (ce2 a); simpl in *; lra.
            - repeat rewrite Rbar_mult_0_r; simpl.
              lra.
          }
          specialize (HH nnf12).
          unfold IG.
          rewrite <- HH.
          eapply Rbar_NonnegExpectation_ext.
          intros a.
          unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, EventIndicator; simpl.
          match_destr.
          * now repeat rewrite Rbar_mult_1_r.
          * repeat rewrite Rbar_mult_0_r.
            simpl; f_equal; lra.
        + intros ?.
          unfold G.
          unfold Rbar_rvmult, EventIndicator, const; simpl.
          match_destr.
          * destruct p.
            destruct (ce2 a); simpl in *; try tauto.
            -- field_simplify.
               eapply Rle_trans; [| apply RRle_abs].
               now left.
            -- destruct (Rle_dec 0 1); try lra.
               destruct (Rle_lt_or_eq_dec 0 1 r); try lra.
               now simpl.
          * rewrite Rbar_mult_0_r.
            simpl.
            apply Rabs_pos.
      - apply Rbar_rvmult_rv; trivial.
        + eapply RandomVariable_sa_sub; eauto.
        + apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      - apply Rbar_rvmult_rv; trivial.
        + eapply RandomVariable_sa_sub; eauto.
        + apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
    }
    
    assert (eqq2: forall x, Rbar_NonnegExpectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (IG x)) = 0).
    {
      intros.
      rewrite eqq1.
      generalize (isce1 (G x) (classic_dec (G x)) (sa_G x))
      ; intros HH1.
      generalize (isce2 (G x) (classic_dec (G x)) (sa_G x))
      ; intros HH2.
      rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)) in HH1.
      rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)) in HH2.
      rewrite (Expectation_pos_pofrf _ (nnf:=_)) in HH1.
      rewrite (Expectation_pos_pofrf _ (nnf:=_)) in HH2.
      invcs HH1.
      invcs HH2.
      unfold IG.
      rewrite <- H0, <- H1.
      apply Rbar_minus_eq_0.
    }

    assert (psG0:forall x, ps_P (ProbSpace:=((prob_space_sa_sub prts sub))) (exist _ (G x) (sa_G x)) = 0).
    {
      intros x.
      specialize (eqq2 x).
      assert (Rbar_NonnegExpectation_zero_pos':almostR2 prts eq (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => IG x x0)) (const 0)).
      {
        apply Rbar_Expectation_nonneg_zero_almost_zero; trivial.
        - apply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _) (Rbar_rvminus (Rbar_rvmult ce1 (IG x))
                                                                                             (Rbar_rvmult ce2 (IG x)))).
          + intros ?.
            unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, Rbar_rvmult; simpl.
            unfold IG, EventIndicator; simpl.
            match_destr.
            * now repeat rewrite Rbar_mult_1_r.
            * repeat rewrite Rbar_mult_0_r.
              simpl.
              f_equal; lra.
          + apply Rbar_rvplus_rv.
            * apply Rbar_rvmult_rv.
              -- eapply RandomVariable_sa_sub; eauto.
              -- apply borel_Rbar_borel.
                 apply EventIndicator_pre_rv.
                 now apply sub.
            * apply Rbar_rvopp_rv.
              apply Rbar_rvmult_rv.
              -- eapply RandomVariable_sa_sub; eauto.
              -- apply borel_Rbar_borel.
                 apply EventIndicator_pre_rv.
                 now apply sub.
        - now rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)), eqq2.
      }

      destruct Rbar_NonnegExpectation_zero_pos' as [P [pone pH]].
      unfold const in pH.
      unfold Rbar_rvmult, IG, EventIndicator in pH.
      apply NNPP.
      intros neq.
      assert (HH1:ps_P  (ProbSpace:=prts) (event_inter P (event_sa_sub sub (exist sa_sigma (G x) (sa_G x)))) <> 0).
      {
        rewrite ps_inter_l1; trivial.
      } 
      destruct (zero_prob_or_witness _ HH1) as [a [Pa Ga]]; simpl in *.
      specialize (pH _ Pa).
      match_destr_in pH; try tauto.
      rewrite Rbar_mult_1_r in pH.
      destruct Ga as [??].
      unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp in pH.
      destruct (ce1 a); destruct (ce2 a); simpl in *; try (invcs pH; lra).
    }

    generalize (is_lim_ascending (prob_space_sa_sub prts sub) (fun n => exist _ _ (sa_G (INR n))))
    ; intros HH.
    cut_to HH.
    - apply (is_lim_seq_ext _ (fun _ => 0)) in HH.
      + apply is_lim_seq_unique in HH.
        rewrite Lim_seq_const in HH.
        assert (eqq3:pre_event_equiv (union_of_collection (fun n : nat => exist sa_sigma (G (INR n)) (sa_G (INR n))))
                                     (fun omega : Ts => Rbar_gt (ce1 omega) (ce2 omega))).
        {
          intros a.
          split; simpl.
          - now intros [?[??]].
          - unfold G.
            intros.
            exists (Z.to_nat (up (ce2 a))).
            split; trivial.
            assert (isf:is_finite (ce2 a)).
            {
              generalize (nnf2 a); intros ?.
              destruct (ce2 a).
              - reflexivity.
              - destruct (ce1 a); simpl in *; tauto.
              - simpl in H0; tauto.
            }
            rewrite <- isf.
            simpl.
            rewrite INR_up_pos.
            * apply archimed.
            * generalize (nnf2 a); intros HH2.
              rewrite <- isf in HH2; simpl in HH2.
              lra.
        } 
        destruct (sa_proper dom2 _ _ eqq3) as [sa1 _].
        cut_to sa1.
        * rewrite (ps_proper _ (exist _ _ sa1)) in HH by (now red).

          generalize (ps_complement (prob_space_sa_sub prts sub)
                                    (exist _ _ sa1))
          ; intros eqq4.
          invcs HH.
          simpl in *.
          rewrite <- H0 in eqq4.
          field_simplify in eqq4.
          eexists.
          split; [apply eqq4|].
          intros a; simpl.
          unfold pre_event_complement.
          unfold Rbar_gt.
          intros.
          now apply Rbar_not_lt_le.
        * apply sa_sigma_event_pre.
      + trivial.
    - intros ??.
      unfold G.
      intros [??].
      split; trivial.
      unfold Rbar_gt in *.
      eapply Rbar_lt_le_trans; try eapply H0.
      apply le_INR; lia.
  Qed.

  Local Existing Instance Rbar_le_part.
  
  Theorem is_conditional_expectation_nneg_unique
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        {nnf : NonnegativeFunction f}
        {nnf1 : Rbar_NonnegativeFunction ce1}
        {nnf2 : Rbar_NonnegativeFunction ce2}
    : is_conditional_expectation dom2 f ce1 ->
      is_conditional_expectation dom2 f ce2 ->
      almostR2 (prob_space_sa_sub prts sub) eq ce1 ce2.
  Proof.
    intros.
    apply antisymmetry
    ; eapply is_conditional_expectation_nneg_le; eauto.
  Qed.

  Lemma is_conditional_expectation_almostfinite_le
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        (isf2:almost (prob_space_sa_sub prts sub) (fun a => is_finite (ce2 a))) :
    is_conditional_expectation dom2 f ce1 ->
    is_conditional_expectation dom2 f ce2 ->
    almostR2 (prob_space_sa_sub prts sub) Rbar_le ce1 ce2.
  Proof.
    unfold is_conditional_expectation; intros isce1 isce2.

    pose (G := fun x:R => pre_event_inter (fun omega => Rbar_gt (ce1 omega) (ce2 omega))
                                          (fun omega => Rbar_ge x ((Rbar_rvabs ce2) omega))).
    assert (sa_G : forall x:R, sa_sigma (G x)).
    {
      intros x.
      unfold G.
      unfold pre_event_inter.
      apply (sa_proper _ 
                       (fun x0 : Ts => (Rbar_gt ((Rbar_rvminus ce1 (Rbar_finite_part ce2)) x0) 0) /\ Rbar_le (Rbar_abs (ce2 x0)) x )).
      - intro z.
        unfold Rbar_rvminus, Rbar_rvopp, Rbar_finite_part.
        split; intros.
        + destruct H.
          split; try easy.
          unfold Rbar_rvplus in H.
          assert (is_finite (ce2 z)).
          * destruct (ce2 z).
            -- now unfold is_finite.
            -- now simpl in H0.
            -- now simpl in H0.
          * rewrite <- H1 in H |- *.
            unfold Rbar_opp in H.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (ce2 z)) in H.
            rewrite Rbar_plus_0_l in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
        + destruct H.
          unfold Rbar_gt in H0.
          assert (is_finite (ce2 z)).
          * unfold Rbar_rvabs in H0.
            destruct (ce2 z).
            -- now unfold is_finite.
            -- now simpl in H0.
            -- now simpl in H0.
          * split; try easy.
            unfold Rbar_rvplus.
            rewrite <- H1 in H |- *.
            unfold Rbar_opp.
            unfold Rbar_gt in *.
            apply (Rbar_plus_lt_compat_r _ _ (- ce2 z)) in H.
            destruct ((ce1 z)); simpl in *; trivial.
            f_equal; lra.
      - apply sa_inter.
        + apply Rbar_sa_le_gt; intros.
          apply Rbar_plus_measurable.
          * typeclasses eauto.
          * apply rv_Rbar_measurable.
            apply Rbar_rvopp_rv.
            apply Real_Rbar_rv.
            apply measurable_rv.
            now apply Rbar_finite_part_meas.
        + apply Rbar_Rabs_measurable.
          now apply rv_Rbar_measurable.
    }

    assert (nnf12: forall x,
               Rbar_NonnegativeFunction (Rbar_rvmult (Rbar_rvminus ce1 ce2) (EventIndicator (classic_dec (G x))))).
    {
      intros x a.
      unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, EventIndicator; simpl.
      destruct (classic_dec (G x) a); simpl.
      - rewrite Rbar_mult_1_r.
        unfold G, Rbar_rvabs in g.
        destruct g as [??].
        destruct (ce1 a); destruct (ce2 a); simpl in *; try tauto.
        lra.
      - now rewrite Rbar_mult_0_r.
    } 

    assert (isfe2abs : forall x,
               match Rbar_Expectation (Rbar_rvabs (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x))))) with
               | Some (Finite _) => True
               | _ => False
               end).
    {
      intros x.
      rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=_)).
      generalize (Rbar_NonnegExpectation_le (nnf2:=(@nnfconst Ts (Rabs x) (Rabs_pos x))) (Rbar_rvabs (Rbar_rvmult ce2 (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0))) (const (Rabs x)))
      ; intros HH1.
      cut_to HH1.
      - simpl in *.
        rewrite Rbar_NonnegExpectation_const in HH1.
        generalize (Rbar_NonnegExpectation_pos
                      (Rbar_rvabs (Rbar_rvmult ce2 (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0))))
        ; intros HH2.
        simpl in *.
        match_destr.
      - intros a.
        unfold Rbar_rvabs, Rbar_rvmult, const, EventIndicator.
        match_destr.
        + rewrite Rbar_mult_1_r.
          destruct g as [??].
          unfold Rbar_rvabs in *.
          destruct (Rbar_abs (ce2 a)); simpl in *; try tauto.
          etransitivity; try eapply H0.
          apply RRle_abs.
        + rewrite Rbar_mult_0_r; simpl.
          rewrite Rabs_R0.
          apply Rabs_pos.
    } 

    assert (isfe2 : forall x,
               match Rbar_Expectation (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x)))) with
               | Some (Finite _) => True
               | _ => False
               end).
    {
      intros.
      apply Rbar_Expectation_abs_then_finite.
      apply isfe2abs.
    } 

    assert (isfe1 : forall x,
               match Rbar_Expectation (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x)))) with
               | Some (Finite _) => True
               | _ => False
               end).
    {
      intros a.
      specialize (isfe2 a).
      specialize (isce1 _ (classic_dec _) (sa_G a)).
      specialize (isce2 _ (classic_dec _) (sa_G a)).
      rewrite <- isce1.
      now rewrite <- isce2 in isfe2.
    } 

    assert (eqq0:forall x, rv_eq (Rbar_rvmult (Rbar_rvminus ce1 ce2) (EventIndicator (classic_dec (G x))))
                                 ((Rbar_rvminus (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x))))
                                                (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x))))))).
    {
      intros x a.
      unfold Rbar_rvminus, Rbar_rvmult, Rbar_rvplus, Rbar_rvopp.
      rewrite Rbar_mult_plus_distr_fin_r.
      now rewrite Rbar_mult_opp_l.
    } 
    
    assert (eqqlin:forall x, Rbar_Expectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (EventIndicator (classic_dec (G x)))) =

                        match Rbar_Expectation (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x)))),
                              Rbar_Expectation (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x)))) with
                        | Some exp1, Some exp2 => Some (Rbar_minus exp1 exp2)
                        | _, _ => None
                        end).
    {
      intros x.

      transitivity (Rbar_Expectation (Rbar_rvminus (Rbar_rvmult ce1 (EventIndicator (classic_dec (G x))))
                                                   (Rbar_rvmult ce2 (EventIndicator (classic_dec (G x)))))).
      {
        now apply Rbar_Expectation_ext.
      }
      specialize (isfe1 x); specialize (isfe2 x).
      match_case_in isfe1; intros; rewrite H in isfe1; try tauto.
      match_destr_in isfe1; try tauto.
      match_case_in isfe2; intros; rewrite H0 in isfe2; try tauto.
      match_destr_in isfe2; try tauto.
      apply Rbar_Expectation_minus_finite; trivial.
      - apply Rbar_rvmult_rv.
        + now apply RandomVariable_sa_sub.
        + apply Real_Rbar_rv.
          apply EventIndicator_pre_rv.
          now apply sub.
      - apply Rbar_rvmult_rv.
        + now apply RandomVariable_sa_sub.
        + apply Real_Rbar_rv.
          apply EventIndicator_pre_rv.
          now apply sub.
    }

    assert (eqq2: forall x,  Rbar_Expectation (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0)) = Some (Finite 0)).
    {
      intros x.
      rewrite eqqlin.
      specialize (isce1 _ (classic_dec _) (sa_G x)).
      specialize (isce2 _ (classic_dec _) (sa_G x)).
      specialize (isfe2 x).
      rewrite <- isce1, <- isce2.
      rewrite <- isce2 in isfe2.
      match_destr_in isfe2; try tauto.
      now rewrite Rbar_minus_eq_0.
    }

    assert (rv12 : forall x,
               RandomVariable dom2 Rbar_borel_sa
                              (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0))).
    {
      intros x.
      eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)); try eapply eqq0.
      apply Rbar_rvplus_rv.
      - apply Rbar_rvmult_rv; trivial.
        apply Real_Rbar_rv.
        now apply EventIndicator_pre_rv.
      - apply Rbar_rvopp_rv.
        apply Rbar_rvmult_rv; trivial.
        apply Real_Rbar_rv.
        now apply EventIndicator_pre_rv.
    } 

    assert (psG0:forall x, ps_P (ProbSpace:=((prob_space_sa_sub prts sub))) (exist _ (G x) (sa_G x)) = 0).
    {
      intros x.
      specialize (eqq2 x).
      generalize (@Rbar_Expectation_nonneg_zero_almost_zero _ _ ((prob_space_sa_sub prts sub))
                                                            (Rbar_rvmult (Rbar_rvminus ce1 ce2) (fun x0 : Ts => EventIndicator (classic_dec (G x)) x0)))
      ; intros HH2.
      cut_to HH2; trivial.
      - destruct HH2 as [P [pone pH]].
        unfold const in pH.
        unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvopp, EventIndicator in pH.
        apply NNPP.
        intros neq.
        simpl in *.
        assert (HH1:ps_P (ProbSpace:=((prob_space_sa_sub prts sub))) (event_inter P (exist sa_sigma (G x) (sa_G x))) <> 0).
        {
          rewrite ps_inter_l1; trivial.
        } 
        destruct (zero_prob_or_witness _ HH1) as [a [Pa Ga]]; simpl in *.
        specialize (pH _ Pa).
        match_destr_in pH; try tauto.
        rewrite Rbar_mult_1_r in pH.
        destruct Ga as [??].
        unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp in pH.
        destruct (ce1 a); destruct (ce2 a); simpl in *; try (invcs pH; lra).
      - rewrite Rbar_Expectation_prob_space_sa_sub; trivial.
    }

    destruct isf2 as [P [Pone ?]].
    assert (psG0' : forall x, ps_P
                           (event_inter
                              (event_sa_sub sub (exist _ (G x) (sa_G x)))
                              (event_sa_sub sub P))
                         = 0).
    {
      intros a; simpl in *.
      now rewrite ps_inter_r1.
    }

    generalize (is_lim_ascending prts (fun x => (event_inter
                                                (event_sa_sub sub (exist _ (G (INR x)) (sa_G (INR x))))
                                                (exist _ _ (sa_finite_Rbar ce2 (RandomVariable_sa_sub sub _))))))
    ; intros HH.
    cut_to HH.
    - apply (is_lim_seq_ext _ (fun _ => 0)) in HH.
      + apply is_lim_seq_unique in HH.
        rewrite Lim_seq_const in HH.
        assert (eqq3:pre_event_equiv
                       (union_of_collection
                          (fun x : nat => event_inter (event_sa_sub sub (exist sa_sigma (G (INR x)) (sa_G (INR x)))) (exist _ _ (sa_finite_Rbar ce2 (RandomVariable_sa_sub sub _)))))
                       (pre_event_inter 
                          (fun omega : Ts => Rbar_gt (ce1 omega) (ce2 omega))
                          (fun a => is_finite (ce2 a)))).
        { 
          intros a.
          split; simpl.
          - intros [?[[??]?]].
            split; trivial.
          - unfold G.
            intros [??].
            exists (Z.to_nat (up (Rabs (ce2 a)))).
            split; trivial.
            split; trivial.
            unfold Rbar_ge, Rbar_rvabs.
            rewrite <- H1; simpl.
            rewrite INR_up_pos.
            * apply Rge_le.
              left. apply archimed.
            * apply Rle_ge.
              apply Rabs_pos.
        } 
        destruct (sa_proper dom2 _ _ eqq3) as [sa1 _].
        cut_to sa1.
        * rewrite (ps_proper _ (event_sa_sub sub ((exist _ _ sa1)))) in HH by (now red).
          generalize (ps_complement (prob_space_sa_sub prts sub)
                                    ((exist _ _ sa1)))
          ; intros eqq4.
          invcs HH.
          simpl in *.
          rewrite <- H1 in eqq4.
          field_simplify in eqq4.
          eexists.
          split.
          -- rewrite ps_inter_r1.
             ++ apply eqq4.
             ++ apply Pone.
          -- intros a; simpl.
             unfold pre_event_complement.
             unfold Rbar_gt.
             intros [??].
             apply not_and_or in H0.
             specialize (H _ H2).
             destruct H0; try tauto.
             now apply Rbar_not_lt_le.
        * apply  sa_countable_union
          ; intros n.
          simpl.
          apply sa_inter; trivial.
          now apply sa_finite_Rbar.
      + intros n.
        simpl in *.
        rewrite ps_inter_r1; trivial.
        erewrite <- ps_inter_r1; try eapply Pone.
        rewrite ps_proper; try eapply Pone.
        intros ?; simpl.
        split.
        * intros [??]; trivial.
        * intros; split; auto.
    - intros ??.
      unfold G.
      intros [[??]?].
      split; trivial.
      split; trivial.
      unfold Rbar_gt, Rbar_ge in *.
      eapply Rbar_le_trans; try eapply H1.
      apply le_INR; lia.
  Qed.

  Theorem is_conditional_expectation_almostfinite_unique
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        (isf1:almost (prob_space_sa_sub prts sub) (fun a => is_finite (ce1 a)))
        (isf2:almost (prob_space_sa_sub prts sub) (fun a => is_finite (ce2 a))) :
    is_conditional_expectation dom2 f ce1 ->
    is_conditional_expectation dom2 f ce2 ->
    almostR2 (prob_space_sa_sub prts sub) eq ce1 ce2.
  Proof.
    intros.
    apply antisymmetry
    ; eapply is_conditional_expectation_almostfinite_le; eauto.
  Qed.

  Theorem is_conditional_expectation_unique
        (f : Ts->R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
        {isfe:IsFiniteExpectation prts f} :
    is_conditional_expectation dom2 f ce1 ->
    is_conditional_expectation dom2 f ce2 ->
    almostR2 (prob_space_sa_sub prts sub) eq ce1 ce2.
  Proof.
    intros.
    
    eapply is_conditional_expectation_almostfinite_unique; eauto.
    - generalize (finite_Rbar_Expectation_almostR2_finite _ ce1)
      ; intros HH1.
      eexists.
      split.
      + apply (finite_Rbar_Expectation_almostR2_finite _ ce1).
        apply Rbar_IsFiniteExpectation_prob_space_sa_sub_f; trivial.
        eapply is_conditional_expectation_FiniteExpectation; eauto.
      + now simpl.
    - generalize (finite_Rbar_Expectation_almostR2_finite _ ce2)
      ; intros HH1.
      eexists.
      split.
      + apply (finite_Rbar_Expectation_almostR2_finite _ ce2).
        apply Rbar_IsFiniteExpectation_prob_space_sa_sub_f; trivial.
        eapply is_conditional_expectation_FiniteExpectation; eauto.
      + now simpl.
  Qed.

  Existing Instance Rbar_rvmult_rv.

  Lemma Rbar_rvmult_assoc (a:Ts->Rbar) (b:Ts->Rbar) (c:Ts->Rbar) :
    rv_eq (Rbar_rvmult a (Rbar_rvmult b c)) (Rbar_rvmult (Rbar_rvmult a b) c).
  Proof.
    intros ?.
    apply Rbar_mult_assoc.
  Qed.

  Lemma rvmult_rvscale c (a b:Ts->R) : 
    rv_eq (rvmult (rvscale c a) b) (rvscale c (rvmult a b)).
  Proof.
    intros ?.
    rv_unfold; lra.
  Qed.

  Theorem is_conditional_expectation_const (c:R)
    :
      is_conditional_expectation dom2 (const c) (const c).
  Proof.
    intros P Pdec saP.
    unfold Rbar_rvmult, rvmult, const; simpl.
    now rewrite gen_Expectation_Rbar_Expectation.
  Qed.
  
  Lemma is_conditional_expectation_scale_nzero (c:R)
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rv : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      c <> 0 ->
      is_conditional_expectation dom2 f ce ->
      is_conditional_expectation dom2 (rvscale c f) (Rbar_rvmult (const c) ce)
                                 (rvce:=Rbar_rvmult_rv _ _)
  .
  Proof.
    intros cnzero isce P Pdec saP.
    
    generalize (Expectation_scale c (rvmult f (EventIndicator Pdec)) cnzero)
    ; intros HH1.
    generalize (Rbar_Expectation_scale c (Rbar_rvmult ce (fun x : Ts => EventIndicator Pdec x)) cnzero)
    ; intros HH2.
    specialize (isce P Pdec saP).
    simpl in *.
    
    rewrite <- (Rbar_Expectation_ext (Rbar_rvmult_assoc _ _ _)).
    rewrite (Expectation_ext (rvmult_rvscale _ _ _)).
    match_destr_in HH1
    ; match_destr_in HH2
    ; rewrite HH1, HH2
    ; trivial.
    now invcs isce.
  Qed.

  Corollary is_conditional_expectation_propere
            {f1 f2 : Ts -> R}
            (eq1:almostR2 prts eq f1 f2) 
            {ce1 ce2 : Ts -> Rbar}
            (eq2:almostR2 prts eq ce1 ce2)
            (rvf1 : RandomVariable dom borel_sa f1)
            (rvf2 : RandomVariable dom borel_sa f2)
            (rvce1 : RandomVariable dom2 Rbar_borel_sa ce1)
            (rvce2 : RandomVariable dom2 Rbar_borel_sa ce2)
            :
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2.
    Proof.
      now apply is_conditional_expectation_proper.
    Qed.
    
  Theorem is_conditional_expectation_scale (c:R)
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rv : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      is_conditional_expectation dom2 f ce ->
      is_conditional_expectation dom2 (rvscale c f) (Rbar_rvmult (const c) ce)
                                 (rvce:=Rbar_rvmult_rv _ _).
  Proof.
    destruct (Req_EM_T c 0).
    - subst.
      intros.
      unfold rvscale, Rbar_rvmult, const.
      apply (is_conditional_expectation_proper (const 0) _ (const 0) _).
      + apply all_almost; intros; unfold const; lra.
      + apply all_almost; intros; unfold const.
        now rewrite Rbar_mult_0_l.
      + apply is_conditional_expectation_const.        
    - now apply is_conditional_expectation_scale_nzero.
  Qed.
  
  Corollary is_conditional_expectation_scale_inv (c:R)
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rv : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      c <> 0 ->
      is_conditional_expectation dom2 (rvscale c f) (Rbar_rvmult (const c) ce)
                                 (rvce:=Rbar_rvmult_rv _ _) ->
      is_conditional_expectation dom2 f ce.
  Proof.
    intros cnzero isce.
    generalize (is_conditional_expectation_scale (/ c) _ _ isce).
    apply is_conditional_expectation_proper
    ; apply all_almost
    ; intros ?
    ; unfold rvscale, Rbar_rvmult, const.
    - now field_simplify.
    - rewrite Rbar_mult_div_fin_cancel_l; trivial.
  Qed.

  Theorem is_conditional_expectation_plus
        (f1 f2 : Ts -> R)
        (ce1 ce2 : Ts -> Rbar)
        {rvf1 : RandomVariable dom borel_sa f1}
        {rvf2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}
        {rvce1 : RandomVariable dom2 Rbar_borel_sa ce1}
        {rvce2 : RandomVariable dom2 Rbar_borel_sa ce2}
    :
      is_conditional_expectation dom2 f1 ce1 ->
      is_conditional_expectation dom2 f2 ce2 ->
      is_conditional_expectation dom2 (rvplus f1 f2) (Rbar_rvplus ce1 ce2)
                                      (rvce:= Rbar_rvplus_rv _ _).
  Proof.
    intros isce1 isce2 ???.
    generalize (rvmult_rvadd_distr (EventIndicator dec) f1 f2); intros eqq1.
    rewrite rvmult_comm in eqq1.
    rewrite (Expectation_ext eqq1).
    generalize (IsFiniteExpectation_indicator prts f1 dec (sub _ H) isfe1)
    ; intros isfe1'.
    generalize (IsFiniteExpectation_indicator prts f2 dec (sub _ H) isfe2)
    ; intros isfe2'.
    
    red in isfe1', isfe2'.
    match_option_in isfe1'; try tauto.
    match_option_in isfe2'; try tauto.
    destruct r; try tauto.
    destruct r0; try tauto.
    rewrite Expectation_sum_finite with (e1:=r) (e2:=r0); trivial.
    - rewrite isce1 in eqq; trivial.
      rewrite isce2 in eqq0; trivial.
      assert (rv_eq (Rbar_rvmult (Rbar_rvplus ce1 ce2) (EventIndicator dec))
                    (Rbar_rvplus (Rbar_rvmult (EventIndicator dec) ce1) (Rbar_rvmult (EventIndicator dec) ce2))).
      {
        intros ?.
        unfold Rbar_rvminus, Rbar_rvmult, Rbar_rvplus, Rbar_rvopp.
        simpl.
        rewrite (Rbar_mult_comm _ (EventIndicator dec a)).
        now rewrite Rbar_mult_r_plus_distr.
      }
      
      rewrite (Rbar_Expectation_ext H0).
      rewrite Rbar_Expectation_sum_finite with (e1:=r) (e2:=r0); trivial.
      + apply Rbar_rvmult_rv; trivial.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
        * eapply RandomVariable_sa_sub; eauto.
      + apply Rbar_rvmult_rv; trivial.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
        * eapply RandomVariable_sa_sub; eauto.
      + rewrite <- eqq.
        apply Rbar_Expectation_ext.
        intros ?.
        unfold Rbar_rvmult.
        apply Rbar_mult_comm.
      + rewrite <- eqq0.
        apply Rbar_Expectation_ext.
        intros ?.
        unfold Rbar_rvmult.
        apply Rbar_mult_comm.
    - apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sub.
    - apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sub.
    - rewrite <- eqq.
      apply Expectation_ext.
      apply rvmult_comm.
    - rewrite <- eqq0.
      apply Expectation_ext.
      apply rvmult_comm.
  Qed.

  Lemma Rbar_rvlim_almost_proper (f1 f2:nat->Ts->R) :
    (forall n, almostR2 prts eq (f1 n) (f2 n)) ->
    almostR2 prts eq (Rbar_rvlim f1) (Rbar_rvlim f2).
  Proof.
    intros eqq.
    unfold Rbar_rvlim.
    destruct (choice _ eqq) as [coll collp].
    exists (inter_of_collection coll).
    split.
    - apply ps_one_countable_inter.
      intros n.
      now destruct (collp n).
    - intros x px.
      apply Lim_seq_ext; intros n.
      destruct (collp n) as [? eqq2].
      rewrite eqq2; trivial.
      apply px.
  Qed.

  Global Instance rvmin_almost_proper : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvmin.
  Proof.
    intros ?? [p1[? eqq1]] ?? [p2[? eqq2]].
    exists (event_inter p1 p2).
    split.
    - rewrite ps_inter_l1; trivial.
    - intros ? [??].
      unfold rvmin.
      rewrite eqq1, eqq2; trivial.
  Qed.

  Global Instance Rbar_rvplus_almost_proper {DOM:SigmaAlgebra Ts} (PRTS: ProbSpace DOM)  : Proper (almostR2 PRTS eq ==> almostR2 PRTS eq ==> almostR2 PRTS eq) Rbar_rvplus.
  Proof.
    intros ?? [p1[? eqq1]] ?? [p2[? eqq2]].
    exists (event_inter p1 p2).
    split.
    - rewrite ps_inter_l1; trivial.
    - intros ? [??].
      unfold Rbar_rvplus.
      rewrite eqq1, eqq2; trivial.
  Qed.

  Global Instance Rbar_rvopp_almost_proper {DOM:SigmaAlgebra Ts} (PRTS: ProbSpace DOM) : Proper (almostR2 PRTS eq ==> almostR2 PRTS eq) Rbar_rvopp.
  Proof.
    intros ?? [p1[? eqq1]].
    exists p1.
    split; trivial.
    - intros ??.
      unfold Rbar_rvopp.
      rewrite eqq1; trivial.
  Qed.

  Definition event_Rbar_ge {domm}
             (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : event domm
    := @exist (pre_event Ts) _ _ (sa_le_Rbar_ge_rv rv_X x).

  Theorem is_conditional_expectation_isfe
        f ce
        {rvf:RandomVariable dom borel_sa f} 
        {rvce:RandomVariable dom2 Rbar_borel_sa ce} :
    is_conditional_expectation dom2 f ce ->
    IsFiniteExpectation prts f ->
    Rbar_IsFiniteExpectation prts ce.
  Proof.
    unfold is_conditional_expectation, IsFiniteExpectation, Rbar_IsFiniteExpectation; intros isce isf.
    specialize (isce _ (dsa_dec dsa_Ω)).

    assert (eqq1:forall f, Expectation (rvmult f (EventIndicator (dsa_dec dsa_Ω))) = Expectation f).
    {
      intros.
      apply Expectation_proper.
      rv_unfold; intros ?; simpl.
      lra.
    }
    assert (eqq2:forall f, Rbar_Expectation (Rbar_rvmult f (EventIndicator (dsa_dec dsa_Ω))) = Rbar_Expectation f).
    {
      intros.
      apply Rbar_Expectation_proper.
      rv_unfold; intros ?; simpl.
      unfold Rbar_rvmult.
      now rewrite Rbar_mult_1_r.
    }

    rewrite eqq1, eqq2 in isce.
    rewrite isce in isf.
    - apply isf.
    - simpl.
      apply sa_all.
  Qed.

  Theorem is_conditional_expectation_nneg
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
        {nnf:NonnegativeFunction f}
    :
      is_conditional_expectation dom2 f ce ->
      almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) ce.
  Proof.
    unfold is_conditional_expectation.
    intros isce.

    specialize (isce (fun x => Rbar_lt (ce x) 0) (classic_dec _)).
    cut_to isce.
    - rewrite (Expectation_pos_pofrf _ (nnf:= indicator_prod_pos _ _ _)) in isce.
      generalize (NonnegExpectation_pos (rvmult f (EventIndicator (classic_dec (fun x : Ts => Rbar_lt (ce x) 0)))))
      ; intros le1.

      case_eq (Rbar_Expectation
           (Rbar_rvmult ce
              (fun x : Ts =>
                 EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))
      ; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in isce
      ; try discriminate.
      assert (nnf1:Rbar_NonnegativeFunction
                     (Rbar_rvopp
                        (Rbar_rvmult ce
                                     (fun x : Ts =>
                                        EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))).
      {
        intros ?.
        unfold Rbar_rvopp, Rbar_rvmult, EventIndicator.
        match_destr.
        - rewrite Rbar_mult_1_r.
          apply Rbar_opp_le.
          rewrite Rbar_opp_involutive.
          simpl.
          rewrite Ropp_0.
          now apply Rbar_lt_le.
        - rewrite Rbar_mult_0_r.
          simpl; lra.
      }

      assert (r = 0).
      {
        apply antisymmetry; [| congruence].
        generalize (Rbar_Expectation_opp
                      (Rbar_rvmult ce
                                   (fun x : Ts =>
                                      EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))
        ; intros HH1.
        simpl in HH1.
        rewrite eqq1 in HH1.
        rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=nnf1)) in HH1.
        generalize (Rbar_NonnegExpectation_pos
                      (Rbar_rvopp
                         (Rbar_rvmult ce
                                      (fun x : Ts =>
                                         EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x))))
        ; intros HH2.
        invcs HH1.
        rewrite H0 in HH2.
        apply Rbar_opp_le.
        unfold Rbar_opp.
        rewrite Ropp_0.
        apply HH2.
      }
      subst.
      generalize (Rbar_Expectation_opp
                    (Rbar_rvmult ce
                                 (fun x : Ts =>
                                    EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))
      ; intros HH1; simpl in HH1.
      rewrite eqq1 in HH1; simpl in HH1.
      rewrite Ropp_0 in HH1.
      assert (rv1:RandomVariable dom2 Rbar_borel_sa
                                 (Rbar_rvopp
                                    (Rbar_rvmult ce
                                                 (fun x : Ts =>
                                                    EventIndicator (classic_dec (fun x0 : Ts => Rbar_lt (ce x0) 0)) x)))).
      {
        apply Rbar_rvopp_rv.
        {
          apply Rbar_rvmult_rv; trivial.
          apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          apply Rbar_sa_le_lt; intros.
          now apply rv_Rbar_measurable.
        }
      }
      rewrite <- (Rbar_Expectation_prob_space_sa_sub prts sub) in HH1; trivial.
      apply (Rbar_Expectation_nonneg_zero_almost_zero _) in HH1; trivial.
      eapply almost_impl; try eapply HH1.
      apply all_almost.
      unfold const.
      intros ? eqq0.
      unfold Rbar_rvopp, Rbar_rvmult, EventIndicator in eqq0.
      match_destr_in eqq0.
      + rewrite Rbar_mult_1_r in eqq0.
        apply (f_equal Rbar_opp) in eqq0.
        rewrite Rbar_opp_involutive in eqq0.
        rewrite eqq0.
        simpl; lra.
      + now apply Rbar_not_lt_le.
    - apply Rbar_sa_le_lt; intros.
      now apply rv_Rbar_measurable.
  Qed.

  Lemma is_conditional_expectation_anneg
        (f : Ts -> R)
        (ce : Ts -> Rbar)
        {rvf : RandomVariable dom borel_sa f}
        {rvce : RandomVariable dom2 Rbar_borel_sa ce}
    :
      almostR2 prts Rle (const 0) f ->
      is_conditional_expectation dom2 f ce ->
      almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) ce.
  Proof.
    intros anneg isce.
    unfold almostR2, const in anneg.
    destruct (almost_map_R_split _ anneg)
      as [f2 [eqq1 [nneg f2_rv]]].
    specialize (f2_rv rvf).
    apply (is_conditional_expectation_proper _ f2 _ ce) in isce
    ; trivial; try reflexivity.
    eapply is_conditional_expectation_nneg; eauto.
  Qed.

  Lemma is_conditional_expectation_factor_out_frf
        f g ce
        {frfg : FiniteRangeFunction g}
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvce : RandomVariable dom2 borel_sa ce}
        {rvgf: RandomVariable dom borel_sa (rvmult f g)} :
    IsFiniteExpectation prts f ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
    unfold is_conditional_expectation.
    intros isfe isce P decP saP.
    assert (eqq1:rv_eq
              (rvmult (rvmult f g) (EventIndicator decP))
              (rvmult (rvmult f (frf_indicator g)) (EventIndicator decP))).
    {
      apply rvmult_proper; try reflexivity.
      apply rvmult_proper; try reflexivity.
      apply (frf_indicator_sum g).
    }
    rewrite (Expectation_ext eqq1).
    unfold frf_indicator.
    
    assert (eqq2:
              rv_eq
                (rvmult (rvmult f (frf_indicator g)) (EventIndicator decP))
                (fun omega : Ts =>
                   RealAdd.list_sum
                     (map (fun c : R => (f omega) * scale_val_indicator g c omega * EventIndicator decP omega)
                          (nodup Req_EM_T frf_vals)))).
    {
      intros ?.
      admit.
    } 
    rewrite eqq2.

    assert (isfe1:forall c, IsFiniteExpectation prts
                                      (fun omega : Ts =>
                                         f omega * val_indicator g c omega * EventIndicator decP omega)).
    {
      admit.
    }

    assert (eqq3:Expectation
              (fun omega : Ts =>
                 RealAdd.list_sum
                   (map
                      (fun c : R =>
                         f omega * scale_val_indicator g c omega * EventIndicator decP omega)
                      (nodup Req_EM_T frf_vals))) =
            Some (Finite (RealAdd.list_sum
              (map
          (fun c : R =>
             c * FiniteExpectation prts
               (fun omega => f omega * val_indicator g c omega * EventIndicator decP omega))
          (nodup Req_EM_T frf_vals))))).
    {
      admit.
    }

    rewrite eqq3.
    unfold val_indicator.
  Admitted.

  Theorem is_conditional_expectation_factor_nneg
          f g ce
          {nnegg : NonnegativeFunction g}
          {rvf : RandomVariable dom borel_sa f}
          {rvg : RandomVariable dom2 borel_sa g}
          {rvce : RandomVariable dom2 borel_sa ce}
          {rvgf: RandomVariable dom borel_sa (rvmult f g)} :
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g) ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
  Admitted.

  Theorem is_conditional_expectation_factor_out
        f g ce
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvce : RandomVariable dom2 borel_sa ce}
        {rvgf: RandomVariable dom borel_sa (rvmult f g)} :
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g) ->
    is_conditional_expectation dom2 f ce ->
    is_conditional_expectation dom2 (rvmult f g) (Rbar_rvmult g ce).
  Proof.
  Admitted.

End is_cond_exp.

Section cond_exp_l2.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  (* For functions in the quotiented L2 space, we define conditional expectation
     via the orthonormal projection 
   *)
  Definition conditional_expectation_L2q
             (x:LpRRVq prts 2)
    : {v : L2RRVq_PreHilbert prts
        | unique
            (fun v : L2RRVq_PreHilbert prts =>
               ortho_phi prts dom2 v /\
               norm (minus (G:=(PreHilbert.AbelianGroup (L2RRVq_PreHilbert prts))) x v) =
               Glb_Rbar (fun r : R => exists w : L2RRVq_PreHilbert prts,
                             ortho_phi prts dom2 w /\
                             r = norm (minus (G:=(PreHilbert.AbelianGroup (L2RRVq_PreHilbert  prts)))x w)))
            v}.
  Proof.
    apply (ortho_projection_hilbert (L2RRVq_PreHilbert prts)
                                    (ortho_phi prts dom2)
                                    (ortho_phi_compatible_m prts sub)
                                    (ortho_phi_complete prts sub)
                                    x).
  Qed.

  Let nneg2 : nonnegreal := bignneg 2 big2.
  Canonical nneg2.

  (* Note that we lose uniqueness, since it only holds over the quotiented space. *)
  Definition conditional_expectation_L2 (f :LpRRV prts 2) :
    {v : LpRRV prts 2 
      | RandomVariable dom2 borel_sa v /\
        LpRRVnorm prts (LpRRVminus prts f v) =
        Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                      RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                      r = LpRRVnorm prts (LpRRVminus prts f w)) /\
        (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts f v) (LpRRVminus prts w v) <= 0) /\
        (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts v w = L2RRVinner prts (pack_LpRRV prts f) w) /\

        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (LpRRVnorm prts (LpRRVminus prts f z) =
                             Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                                           RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                                           r = LpRRVnorm prts (LpRRVminus prts f w))) -> LpRRV_eq prts z v) /\
        
        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts f z) (LpRRVminus prts w z) <= 0) -> LpRRV_eq prts z v) /\
        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts z w = L2RRVinner prts (pack_LpRRV prts f) w)  -> LpRRV_eq prts z v)

    }.
  Proof.
    destruct ((conditional_expectation_L2q (Quot _ f))).
    destruct u as [[HH1 HH2] HH3].
    destruct (charac_ortho_projection_subspace1 _ (ortho_phi_compatible_m _ sub) (Quot (LpRRV_eq prts) f) _ HH1)
      as [cops1_f _].
    destruct (charac_ortho_projection_subspace2 _ (ortho_phi_compatible_m _ sub) (Quot (LpRRV_eq prts) f) _ HH1)
      as [cops2_f _].
    specialize (cops1_f HH2).
    specialize (cops2_f HH2).
    red in HH1.
    apply constructive_indefinite_description in HH1.
    destruct HH1 as [y [eqqy rvy]].
    exists y.
    split; trivial.
    subst.
    unfold norm, minus, plus, opp in *; simpl in *.
    rewrite L2RRVq_norm_norm in HH2.
    autorewrite with quot in HH2.
    rewrite LpRRVq_normE in HH2.
    rewrite LpRRVminus_plus.
    unfold nonneg in HH2 |- *; simpl in *.
    rewrite HH2.
    assert (glb_eq:
              Glb_Rbar
                (fun r : R =>
                   exists w : LpRRVq prts 2,
                     ortho_phi prts dom2 w /\ r = Hnorm (LpRRVq_plus prts (Quot (LpRRV_eq prts) f) (LpRRVq_opp prts w)))
              =
              Glb_Rbar
                (fun r : R =>
                   exists w : LpRRV prts 2, RandomVariable dom2 borel_sa w /\ r = LpRRVnorm prts (LpRRVminus prts f w))).

    { 
      apply Glb_Rbar_eqset; intros.
      split; intros [w [wrv wnorm]].
      + rewrite L2RRVq_norm_norm in wnorm.
        destruct wrv as [w' [? rvw']]; subst.
        exists w'.
        split; trivial.
        autorewrite with quot.
        rewrite LpRRVq_normE.
        now rewrite LpRRVminus_plus.
      + subst.
        exists (Quot _ w).
        split.
        * exists w.
          split; trivial.
        * rewrite L2RRVq_norm_norm.
          autorewrite with quot.
          rewrite LpRRVq_normE.
          now rewrite LpRRVminus_plus.
    } 
    repeat split.
    - now f_equal.
    - intros.
      specialize (cops1_f (Quot _ w)).
      cut_to cops1_f.
      + unfold inner in cops1_f; simpl in cops1_f.
        LpRRVq_simpl.
        rewrite L2RRVq_innerE in cops1_f.
        etransitivity; try eapply cops1_f.
        right.
        apply L2RRV_inner_proper.
        * apply LpRRV_seq_eq; intros ?; simpl.
          rv_unfold; lra.
        * apply LpRRV_seq_eq; intros ?; simpl.
          rv_unfold; lra.
      + red; eauto.
    - intros.
      specialize (cops2_f (Quot _ w)).
      cut_to cops2_f.
      + unfold inner in cops2_f; simpl in cops2_f.
        repeat rewrite L2RRVq_innerE in cops2_f.
        apply cops2_f.
      + red; eauto.
    - intros x xrv xeqq.
      specialize (HH3 (Quot _ x)).
      cut_to HH3.
      + apply Quot_inj in HH3; try typeclasses eauto.
        now symmetry.
      + split.
        * unfold ortho_phi.
          eauto.
        * rewrite L2RRVq_norm_norm.
          autorewrite with quot.
          rewrite LpRRVq_normE.
          rewrite <- LpRRVminus_plus.
          unfold nonneg in *; simpl in *.
          rewrite xeqq.
          symmetry.
          now f_equal.
    - intros x xrv xeqq.
      specialize (HH3 (Quot _ x)).
      cut_to HH3.
      + apply Quot_inj in HH3; try typeclasses eauto.
        now symmetry.
      + split.
        * unfold ortho_phi.
          eauto.
        * destruct (charac_ortho_projection_subspace1 _
                                                      (ortho_phi_compatible_m _ sub)
                                                      (Quot (LpRRV_eq prts) f)
                                                      (Quot _ x))
            as [_ cops1_b].
          -- red; eauto.
          -- apply cops1_b; intros.
             destruct H as [z [? rvz]]; subst.
             specialize (xeqq _ rvz).
             etransitivity; try eapply xeqq.
             right.
             unfold inner, minus, plus, opp; simpl.
             LpRRVq_simpl.
             rewrite L2RRVq_innerE.
             apply L2RRV_inner_proper.
             ++ now rewrite <- LpRRVminus_plus.
             ++ now rewrite <- LpRRVminus_plus.
    - intros x xrv xeqq.
      specialize (HH3 (Quot _ x)).
      cut_to HH3.
      + apply Quot_inj in HH3; try typeclasses eauto.
        now symmetry.
      + split.
        * unfold ortho_phi.
          eauto.
        * destruct (charac_ortho_projection_subspace2 _
                                                      (ortho_phi_compatible_m _ sub)
                                                      (Quot (LpRRV_eq prts) f)
                                                      (Quot _ x))
            as [_ cops2_b].
          -- red; eauto.
          -- apply cops2_b; intros.
             destruct H as [z [? rvz]]; subst.
             specialize (xeqq _ rvz).
             unfold inner, minus, plus, opp; simpl.
             repeat rewrite L2RRVq_innerE.
             rewrite xeqq.
             apply L2RRV_inner_proper; try reflexivity.
             now apply LpRRV_seq_eq; intros ?; simpl.
  Qed.

  Definition conditional_expectation_L2fun (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {isl : IsLp prts 2 f} :
    LpRRV prts 2
    := proj1_sig (conditional_expectation_L2 (pack_LpRRV prts f)).

  Instance conditional_expectation_L2fun_rv
           (f : Ts -> R) 
           {rv : RandomVariable dom borel_sa f}
           {isl : IsLp prts 2 f} :
    RandomVariable dom2 borel_sa (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Lemma conditional_expectation_L2fun_eq
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) (conditional_expectation_L2fun f)) =
    Glb_Rbar
      (fun r : R =>
         exists w : LpRRV prts 2,
           RandomVariable dom2 borel_sa w /\ r = LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) w)).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Lemma conditional_expectation_L2fun_eq1
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts (pack_LpRRV prts f) (conditional_expectation_L2fun f)) (LpRRVminus prts w (conditional_expectation_L2fun f)) <= 0).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Lemma conditional_expectation_L2fun_eq2
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (conditional_expectation_L2fun f) w = L2RRVinner prts (pack_LpRRV prts f) w).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr; tauto.
  Qed.

  Lemma conditional_expectation_L2fun_eq3
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    is_conditional_expectation prts dom2 f (fun x => (conditional_expectation_L2fun f) x).
  Proof.
    unfold is_conditional_expectation.
    intros.
    assert (RandomVariable dom2 borel_sa (EventIndicator dec)) by now apply EventIndicator_pre_rv.
    assert (RandomVariable dom borel_sa (EventIndicator dec)) by now apply RandomVariable_sa_sub.
    generalize (conditional_expectation_L2fun_eq2 f (pack_LpRRV prts (EventIndicator dec))); intros.
    cut_to H2.
    - unfold L2RRVinner in H2.
      simpl in H2.
      symmetry in H2.
      unfold FiniteExpectation, proj1_sig in H2.
      do 2 match_destr_in H2.
      subst.
      erewrite Expectation_ext; [rewrite e | reflexivity].
      unfold Rbar_rvmult; simpl.
      rewrite <- gen_Expectation_Rbar_Expectation.
      erewrite Expectation_ext; [rewrite e0 | reflexivity].
      trivial.
    - now apply EventIndicator_pre_rv.
  Qed.

  Lemma conditional_expectation_L2fun_unique
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        (z: LpRRV prts 2)
        {z_rv:RandomVariable dom2 borel_sa z} :
    (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) z) =
     Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                   RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                   r = LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) w))) ->
    LpRRV_eq prts z (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    intuition.
  Qed.

  Lemma conditional_expectation_L2fun_unique1
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        (z: LpRRV prts 2)
        {z_rv:RandomVariable dom2 borel_sa z} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts (pack_LpRRV prts f) z) (LpRRVminus prts w z) <= 0) -> LpRRV_eq prts z (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    intuition.
  Qed.

  Lemma conditional_expectation_L2fun_unique2
        (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        (z: LpRRV prts 2)
        {z_rv:RandomVariable dom2 borel_sa z} :
    (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts z w = L2RRVinner prts (pack_LpRRV prts f) w)  -> LpRRV_eq prts z (conditional_expectation_L2fun f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    intuition.
  Qed.

  Lemma conditional_expectation_L2fun_const
        (c : R) :
    LpRRV_eq prts
             (LpRRVconst prts c)
             (conditional_expectation_L2fun (const c)).
  Proof.
    apply conditional_expectation_L2fun_unique2.
    - typeclasses eauto.
    - intros.
      now unfold LpRRVconst.
  Qed.

  Instance IsLp_min_const_nat (f : Ts -> R) (n : nat) 
           {nneg : NonnegativeFunction f} :
    IsLp prts 2 (rvmin f (const (INR n))).
  Proof.
    intros.
    apply IsLp_bounded with (rv_X2 := const (power (INR n) 2)).
    - intro x.
      unfold rvpower, rvabs, rvmin, const.
      apply Rle_power_l; try lra.
      split.
      + apply Rabs_pos.
      + rewrite Rabs_right.
        apply Rmin_r.
        specialize (nneg x).
        apply Rmin_case; try lra.
        apply Rle_ge, pos_INR.
    - apply IsFiniteExpectation_const.
  Qed.

  Lemma conditional_expectation_L2fun_proper (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    almostR2 prts eq f1 f2 ->
    LpRRV_eq prts
             (conditional_expectation_L2fun f1)
             (conditional_expectation_L2fun f2).
  Proof.
    intros eqq.
    unfold conditional_expectation_L2fun, proj1_sig.
    repeat match_destr.
    destruct a as [xrv [xeq [? [? [xuniq ?]]]]].
    rename x0 into y.
    destruct a0 as [yrv [yeq [? [? [yuniq ?]]]]].
    apply yuniq; trivial.
    rewrite (LpRRV_norm_proper prts _ (LpRRVminus prts (pack_LpRRV prts f2) x)) in xeq.
    - unfold nneg2, bignneg, nonneg in *.
      rewrite xeq.
      f_equal.
      apply Glb_Rbar_eqset.
      split; intros [w [wrv wnorm]].
      + subst.
        exists w.
        split; trivial.
        apply LpRRV_norm_proper.
        apply LpRRV_minus_proper; trivial.
        reflexivity.
      + subst.
        exists w.
        split; trivial.
        apply LpRRV_norm_proper.
        apply LpRRV_minus_proper; trivial.
        * now symmetry.
        * reflexivity.
    - apply LpRRV_minus_proper; trivial.
      reflexivity.
  Qed.

  Lemma conditional_expectation_L2fun_nonneg (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        {nneg: NonnegativeFunction f} :
    almostR2 (prob_space_sa_sub prts sub) Rle (const 0) (conditional_expectation_L2fun f).
  Proof.
    generalize (conditional_expectation_L2fun_eq3 f); intros.
    unfold is_conditional_expectation in H.
    apply Expectation_mult_indicator_almost_nonneg; [typeclasses eauto|].
    intros.
    destruct P.
    specialize (H x dec s).
    rewrite Expectation_prob_space_sa_sub.
    - simpl.
      unfold Rbar_rvmult, rvmult in *; simpl in *.
      rewrite <- gen_Expectation_Rbar_Expectation in H.
      rewrite <- H.
      erewrite Expectation_pos_pofrf.
      generalize (NonnegExpectation_pos (rvmult f (EventIndicator dec))); intros.
      rv_unfold; simpl.
      match_case; intros.
      + simpl in H0.
        now rewrite H1 in H0.
      + simpl in H0.
        now rewrite H1 in H0.
    - apply rvmult_rv.
      + apply conditional_expectation_L2fun_rv.
      + now apply EventIndicator_pre_rv.
  Qed.
  
  Lemma conditional_expectation_L2fun_nonneg_prts (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        {nneg: NonnegativeFunction f} :
    almostR2 prts Rle (const 0) (conditional_expectation_L2fun f).
  Proof.
    apply almostR2_prob_space_sa_sub_lift with (sub0 := sub).
    now apply conditional_expectation_L2fun_nonneg.
  Qed.

  Local Existing Instance Rbar_le_pre.

  Lemma conditional_expectation_L2fun_plus f1 f2
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    LpRRV_eq prts
             (conditional_expectation_L2fun (rvplus f1 f2))
             (LpRRVplus prts (conditional_expectation_L2fun f1) (conditional_expectation_L2fun f2)).
  Proof.
    symmetry.
    apply (conditional_expectation_L2fun_unique2)
    ; try typeclasses eauto.
    intros.
    replace (pack_LpRRV prts (rvplus f1 f2)) with
        (LpRRVplus prts (pack_LpRRV prts f1) (pack_LpRRV prts f2)) by reflexivity.
    repeat rewrite L2RRV_inner_plus.
    f_equal
    ; now apply conditional_expectation_L2fun_eq2.
  Qed.
  
End cond_exp_l2.

Section cond_exp2.      

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Lemma conditional_expectation_L2fun_le (f1 f2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    rv_le f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) Rle (conditional_expectation_L2fun prts sub f1) 
             (conditional_expectation_L2fun prts sub f2).
  Proof.
    intros.
    generalize (conditional_expectation_L2fun_eq3 prts sub f1); intro eqq1.
    generalize (conditional_expectation_L2fun_eq3 prts sub f2); intros eqq2.
    assert (isfe1:IsFiniteExpectation prts f1) by (apply (IsLp_Finite prts 2); trivial; lra).
    assert (isfe2:IsFiniteExpectation prts f2) by (apply (IsLp_Finite prts 2); trivial; lra).
    generalize (is_conditional_expectation_isfe prts f2 (fun x => (conditional_expectation_L2fun prts sub f2) x) eqq2 isfe2); intros isce2.  
    apply Expectation_mult_indicator_almost_le;
      [apply conditional_expectation_L2fun_rv |   
       apply conditional_expectation_L2fun_rv | | ].
    apply IsFiniteExpectation_prob_space_sa_sub_f; trivial.
    apply conditional_expectation_L2fun_rv.
    apply Rbar_finexp_finexp in isce2; trivial.
    apply Real_Rbar_rv.
    apply RandomVariable_sa_sub; trivial.
    apply conditional_expectation_L2fun_rv.
    intros.
    destruct P.
    specialize (eqq1 x dec s).
    specialize (eqq2 x dec s).
    assert (RandomVariable 
              dom2 borel_sa
              (rvmult (conditional_expectation_L2fun prts sub f1) (EventIndicator dec))).
    {
      apply rvmult_rv.
      - apply conditional_expectation_L2fun_rv.
      - apply EventIndicator_pre_rv.
        simpl.
        apply s.
    }
    assert (RandomVariable dom2 borel_sa
                           (rvmult (conditional_expectation_L2fun prts sub f2) (EventIndicator dec))).
    {
      apply rvmult_rv.
      - apply conditional_expectation_L2fun_rv.
      - apply EventIndicator_pre_rv.
        simpl.
        apply s.
    }
    rewrite Expectation_prob_space_sa_sub; trivial.
    unfold Rbar_rvmult in *; simpl in *.
    rewrite <- gen_Expectation_Rbar_Expectation in eqq1, eqq2.
    unfold rvmult; simpl.
    simpl; rewrite <- eqq1.
    match_case; intros.
    - rewrite Expectation_prob_space_sa_sub; trivial.
      simpl; rewrite <- eqq2.
      match_case; intros.
      + apply Expectation_le with (rv_X1 := (rvmult f1 (EventIndicator dec)))
                                  (rv_X2 := (rvmult f2 (EventIndicator dec))); trivial.
        {
          intro z.
          rv_unfold.
          match_destr.
          - now do 2 rewrite Rmult_1_r.
          - lra.
        }
      + generalize (IsFiniteExpectation_indicator prts f2 dec)
        ; intros HH.
        cut_to HH; trivial.
        * red in HH.
          simpl in HH.
          now rewrite H3 in HH.
        * simpl.
          now apply sub.
    - + generalize (IsFiniteExpectation_indicator prts f1 dec)
        ; intros HH.
        cut_to HH; trivial.
        * red in HH.
          simpl in HH.
          now rewrite H2 in HH.
        * simpl.
          now apply sub.
  Qed.

  Lemma conditional_expectation_L2fun_le_prts (f1 f2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
    rv_le f1 f2 ->
    almostR2 prts Rle (conditional_expectation_L2fun prts sub f1) 
             (conditional_expectation_L2fun prts sub f2).
  Proof.
    intros.
    apply almostR2_prob_space_sa_sub_lift with (sub0 := sub).
    now apply conditional_expectation_L2fun_le.
  Qed.

  Local Existing Instance Rbar_le_pre.
  Local Existing Instance IsLp_min_const_nat.
  Local Existing Instance conditional_expectation_L2fun_rv.

  Definition NonNegConditionalExpectation (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {nnf : NonnegativeFunction f} : Ts -> Rbar :=
    Rbar_rvlim (fun n => conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))).

  (* if f has finite exp, we can discard the infinite points *)
  Definition FiniteNonNegConditionalExpectation (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {isfe : IsFiniteExpectation prts f}
             {nnf : NonnegativeFunction f} : Ts -> R :=
    rvlim (fun n => conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))).

  Lemma NonNegCondexp_almost_increasing (f : Ts -> R) 
          {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almost (prob_space_sa_sub prts sub)
           (fun x => 
              forall n,
                conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x
                <= conditional_expectation_L2fun prts sub (rvmin f (const (INR (S n)))) x).
  Proof.
    apply almost_forall.
    intros.
    apply conditional_expectation_L2fun_le.
    intro x.
    rv_unfold.
    apply Rle_min_compat_l.
    apply le_INR.
    lia.
  Qed.

  Lemma NonNegCondexp_almost_increasing_prts (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almost prts
           (fun x => 
              forall n,
                conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x
                <= conditional_expectation_L2fun prts sub (rvmin f (const (INR (S n)))) x).
  Proof.
    apply almost_prob_space_sa_sub_lift with (sub0 := sub).
    apply NonNegCondexp_almost_increasing.
  Qed.

  Lemma almost_Rbar_rvlim_condexp_incr_indicator_rv (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} 
        (E : event dom2) :
    ps_P (ProbSpace:=(prob_space_sa_sub prts sub)) E = 1 ->
    (forall x0 : Ts,
        E x0 ->
        forall n : nat,
          conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x0 <=
          conditional_expectation_L2fun prts sub (rvmin f (const (INR (S n)))) x0) ->
    (RandomVariable 
       dom2 Rbar_borel_sa
       (Rbar_rvlim
          (fun n0 : nat =>
             rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n0))))
                    (EventIndicator (classic_dec E))))).
  Proof.
    intros.
    apply Rbar_rvlim_rv.
    - typeclasses eauto.
    - intros.
      apply ex_lim_seq_incr.
      intros.
      rv_unfold.
      match_destr.
      + setoid_rewrite Rmult_1_r.
        apply H0.
        apply e.
      + setoid_rewrite Rmult_0_r.
        lra.
  Qed.

  Lemma NonNegCondexp_almost_nonneg (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) (NonNegConditionalExpectation f).
  Proof.
    unfold NonNegConditionalExpectation.
    assert (almost (prob_space_sa_sub prts sub)
                   (fun x => forall n,
                        0 <= (conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))) x)).
    {
      apply almost_forall.
      intros.
      apply conditional_expectation_L2fun_nonneg.
      intro x.
      unfold rvmin, const.
      apply Rmin_glb; trivial.
      apply pos_INR.
    }
    destruct H as [? [? ?]].
    exists x.
    split; trivial.
    intros.
    specialize (H0 x0 H1).
    unfold const, Rbar_rvlim.
    replace (Finite 0) with (Lim_seq (fun _ => 0)) by apply Lim_seq_const.
    apply Lim_seq_le_loc.
    exists 0%nat.
    intros.
    apply H0.
  Qed.

  Lemma NonNegCondexp_almost_nonneg_prts (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    almostR2 prts Rbar_le (const 0) (NonNegConditionalExpectation f).
  Proof.
    apply almost_prob_space_sa_sub_lift with (sub0 := sub).
    apply NonNegCondexp_almost_nonneg.
  Qed.

  Lemma rvlim_rvmin_indicator (f : Ts -> R) (P:pre_event Ts) (dec:dec_pre_event P) :
    rv_eq (fun  x=> Finite (rvmult f (EventIndicator dec) x))
          (Rbar_rvlim (fun n : nat => rvmult (rvmin f (const (INR n))) (EventIndicator dec))).
  Proof.
    intros a.
    unfold rvmult.
    unfold Rbar_rvlim.
    rewrite Lim_seq_scal_r.
    generalize (rvlim_rvmin f); intros HH.
    unfold Rbar_rvlim in HH.
    rewrite HH.
    now simpl.
  Qed.
    
  Lemma NonNegCondexp_is_Rbar_condexp_almost0  (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    exists (g : nat -> Ts -> R),
      (forall n, (NonnegativeFunction (g n)))
      /\ (forall n, (rv_le (g n) (g (S n))))
      /\ RandomVariable dom2 Rbar_borel_sa (Rbar_rvlim g)
      /\ exists (g_rv:forall n, RandomVariable dom2 borel_sa (g n)),
          (forall n, is_conditional_expectation prts dom2 (rvmin f (const (INR n))) (g n)).
  Proof.
    assert (HHsuc:forall n, rv_le (rvmin f (const (INR n))) (rvmin f (const (INR (S n))))).
    {
      intros n ?.
      rv_unfold.
      apply Rle_min_compat_l.
      apply le_INR; lia.
    }
    
    destruct (almost_forall _ (fun n => conditional_expectation_L2fun_le (rvmin f (const (INR n))) (rvmin f (const (INR (S n)))) (HHsuc n))) as [? [??]].
    destruct (almost_forall _ (fun n => conditional_expectation_L2fun_nonneg prts sub (rvmin f (const (INR n)))))
      as [? [??]].
    pose (E := event_inter x x0).    
    assert (ps_P (ProbSpace := (prob_space_sa_sub prts sub)) E = 1).
    {
      unfold E.
      now rewrite ps_inter_l1.
    }
    exists (fun n => rvmult 
               (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
               (EventIndicator (classic_dec E))).
    assert (g_rv :  forall n, RandomVariable dom2 borel_sa
                                        (rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                                                (EventIndicator (classic_dec E)))).
    {
      typeclasses eauto.
    }
    repeat split.
    - intros n a.
      unfold EventIndicator, rvmult; simpl.
      match_destr; try lra.
      field_simplify.
      destruct p as [px px0].
      apply (H2 _ px0).
    - intros n a.
      unfold EventIndicator, rvmult; simpl.
      match_destr; try lra.
      field_simplify.
      destruct p as [px px0].
      apply (H0 _ px).
    -  apply almost_Rbar_rvlim_condexp_incr_indicator_rv; trivial.
       intros.
       apply H0.
       apply H4.
    - exists g_rv.
      intros n.
      + assert (eqq1: (almostR2 (prob_space_sa_sub prts sub) eq ((rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                                                                         (EventIndicator (classic_dec E))))
                                (conditional_expectation_L2fun prts sub (rvmin f (const (INR n)))))).
        {
          exists E.
          split; trivial.
          intros.
          rv_unfold.
          match_destr; [| tauto].
          lra.
        }
        assert (rv2:RandomVariable dom borel_sa
           (rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                   (EventIndicator (classic_dec E)))).
        {
          apply rvmult_rv.
          - apply RandomVariable_sa_sub; trivial.
            apply conditional_expectation_L2fun_rv.
          - apply EventIndicator_pre_rv.
            apply sub.
            apply sa_sigma_event_pre.
        }
        
        generalize (is_conditional_expectation_proper prts sub)
        ; intros HH.
        generalize (HH (rvmin f (const (INR n))) (rvmin f (const (INR n)))
                       (fun x => conditional_expectation_L2fun prts sub (rvmin f (const (INR n))) x)
                       (rvmult (conditional_expectation_L2fun prts sub (rvmin f (const (INR n))))
                               (EventIndicator (classic_dec E))))
                   
        ; intros HH2.
        apply (HH2 _ _ _ _ (reflexivity _)); clear HH HH2.
        * apply almost_f_equal.
          apply (almost_prob_space_sa_sub_lift _ sub).
          symmetry in eqq1.
          apply eqq1.
        * apply conditional_expectation_L2fun_eq3.
  Qed.

  Lemma NonNegCondexp_is_Rbar_condexp_g  (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    exists (g : nat -> Ts -> R),
      Rbar_NonnegativeFunction (Rbar_rvlim g)
      /\ exists (g_rv : RandomVariable dom2 Rbar_borel_sa (Rbar_rvlim g)),
        is_conditional_expectation prts dom2 f (Rbar_rvlim g).      
  Proof.
    destruct (NonNegCondexp_is_Rbar_condexp_almost0 f) as [g [gnnf [gincr [glimrv [grv giscond]]]]].
    generalize 3; intros.
    exists g.
    split.
    - now apply Rbar_rvlim_nnf.
    - exists glimrv.
      unfold is_conditional_expectation.
      intros.
      assert (nnexpg: forall n : nat,
                 IsFiniteExpectation prts (g n)).
      {
        intros.
        generalize  (is_conditional_expectation_isfe prts
                                                     (rvmin f (const (INR n))) 
                                                     (g n)); intros.
        cut_to H1; trivial.
        - apply Rbar_finexp_finexp in H1; trivial.
          apply Real_Rbar_rv.
          apply RandomVariable_sa_sub; trivial.
        - typeclasses eauto.
      } 
      assert (forall n : nat,
                 RandomVariable dom2 borel_sa
                                (rvmult (g n) (EventIndicator dec))).
      {
        intros.
        apply rvmult_rv.
        - typeclasses eauto.
        - now apply EventIndicator_pre_rv.
      }
      assert (forall n, 
                 RandomVariable dom borel_sa
                                (rvmult (g n) (EventIndicator dec))).
      {
        intros.
        apply RandomVariable_sa_sub; trivial.
      }
      assert  (forall n : nat,
                  NonnegativeFunction
                    (rvmult (g n)
                            (EventIndicator dec)
              )) by (intros; now apply indicator_prod_pos).
      generalize (monotone_convergence_Rbar
                    (fun n => rvmult (g n) (EventIndicator dec)) H2 H3); intros.
      cut_to H4.
      + assert 
          (rv_eq
             (Rbar_rvlim
                (fun n : nat =>
                   rvmult (g n) (EventIndicator dec)))
             (Rbar_rvmult
                (Rbar_rvlim g)
                (fun x : Ts => EventIndicator dec x))).
        {
          intro x.
          rv_unfold.
          unfold Rbar_rvlim, Rbar_rvmult.
          destruct (dec x).
          - rewrite Lim_seq_mult.
            + now rewrite Lim_seq_const.
            + apply ex_lim_seq_incr.
              intros.
              apply gincr.
            + apply ex_lim_seq_const.
            + rewrite Lim_seq_const.
              unfold ex_Rbar_mult.
              match_destr.
          - setoid_rewrite Rmult_0_r.
            rewrite Lim_seq_const.
            now rewrite Rbar_mult_0_r.
        }
        rewrite <- (Rbar_Expectation_ext H5); clear H5.
        erewrite Rbar_Expectation_pos_pofrf.
        rewrite <- H4.
        erewrite Expectation_pos_pofrf.
        f_equal.
        eassert (forall n,
                    NonnegExpectation (rvmult (rvmin f (const (INR n))) (EventIndicator dec)) =
                    NonnegExpectation (rvmult (g n) (EventIndicator dec))).
        {
          intros.
          unfold is_conditional_expectation in giscond.
          specialize (giscond n P dec H0).
          unfold Rbar_rvmult in giscond; simpl in *.
          rewrite <- gen_Expectation_Rbar_Expectation in giscond.
          rewrite (Expectation_pos_pofrf _ (nnf:=_)) in giscond.
          rewrite (Expectation_pos_pofrf _ (nnf:=_))in giscond.
          now inversion giscond.
        }
        erewrite Lim_seq_ext.
        2: {
          intros.
          rewrite <- H5.
          reflexivity.
        }
        rewrite (monotone_convergence_Rbar
                   (fun n =>  (rvmult (rvmin f (const (INR n))) (EventIndicator dec)))).
        * rewrite Expectation_Rbar_Expectation.
          apply Rbar_NonnegExpectation_ext; intros a.
          now rewrite rvlim_rvmin_indicator.
        * intros.
          apply rvmult_rv.
          -- typeclasses eauto.
          -- apply EventIndicator_pre_rv.
             now apply sub.
        * intros n x.
          rv_unfold.
          match_destr.
          -- do 2 rewrite Rmult_1_r.
             apply Rle_min_compat_l.
             apply le_INR.
             lia.
          -- lra.
        * intros.
          apply IsFiniteNonnegExpectation.
          apply IsFiniteExpectation_indicator; try typeclasses eauto.
          now apply sub.
      + intros n x.
        rv_unfold.
        match_destr.
        * do 2 rewrite Rmult_1_r.
          apply gincr.
        * lra.
      + intros.
        apply IsFiniteNonnegExpectation.
        apply IsFiniteExpectation_indicator; try typeclasses eauto.
        * now apply RandomVariable_sa_sub.
        * now apply sub.
  Qed.

  Lemma NonNegCondexp'  (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    { g : Ts -> Rbar |
      Rbar_NonnegativeFunction g
      /\ exists (g_rv : RandomVariable dom2 Rbar_borel_sa g),
          is_conditional_expectation prts dom2 f g }.
  Proof.
    apply constructive_indefinite_description.
    destruct (NonNegCondexp_is_Rbar_condexp_g f) as [g [?[??]]].
    exists (Rbar_rvlim g); eauto.
  Qed.

  Definition NonNegCondexp  (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f}
             {nnf : NonnegativeFunction f} : Ts -> Rbar
    := proj1_sig (NonNegCondexp' f).

  Global Instance NonNegCondexp_nneg (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f}
         {nnf : NonnegativeFunction f} :
    Rbar_NonnegativeFunction (NonNegCondexp f).
  Proof.
    unfold NonNegCondexp, proj1_sig; match_destr.
    destruct a as [?[??]]; eauto.
  Qed.

  Global Instance NonNegCondexp_rv (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f}
         {nnf : NonnegativeFunction f} :
    RandomVariable dom2 Rbar_borel_sa (NonNegCondexp f).
  Proof.
    unfold NonNegCondexp, proj1_sig; match_destr.
    destruct a as [?[??]]; eauto.
  Qed.

  Lemma conditional_expectation_L2fun_cond_exp 
        (f : Ts -> R)
        {rv : RandomVariable dom borel_sa f} {isl : IsLp prts 2 f} :
    is_conditional_expectation prts dom2 f (LpRRV_rv_X _ (conditional_expectation_L2fun prts sub f)).
  Proof.
    intros ???.
    unfold Rbar_rvmult; simpl.
    now apply conditional_expectation_L2fun_eq3.
  Qed.    
  
  Lemma NonNegCondexp_cond_exp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f} :
    is_conditional_expectation prts dom2 f (NonNegCondexp f).
  Proof.
    unfold NonNegCondexp.
    unfold is_conditional_expectation; intros.
    unfold proj1_sig.
    match_destr.
    destruct a as [?[??]]; eauto.
  Qed.
    
  Lemma NonNegCond_almost_finite (f : Ts -> R)
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f}
        {rvce : RandomVariable dom2 Rbar_borel_sa (NonNegCondexp f)} :
    IsFiniteExpectation prts f ->
    almost prts (fun x => is_finite ((NonNegCondexp f) x)).
  Proof.
    intros isfe.
    apply IsFiniteExpectation_nneg_is_almost_finite; trivial.
    - apply (RandomVariable_sa_sub sub); trivial.
    - apply NonNegCondexp_nneg.
    - eapply (is_conditional_expectation_FiniteExpectation); eauto.
      apply NonNegCondexp_cond_exp.
  Qed.

  Definition ConditionalExpectation (f : Ts -> R) 
             {rv : RandomVariable dom borel_sa f} : Ts -> Rbar :=
    Rbar_rvminus (NonNegCondexp (pos_fun_part f))
                 (NonNegCondexp (neg_fun_part f)).

  Global Instance Condexp_rv (f : Ts -> R) 
         {rv : RandomVariable dom borel_sa f} :
    RandomVariable dom2 Rbar_borel_sa (ConditionalExpectation f).
  Proof.
    unfold ConditionalExpectation, Rbar_rvminus.
    apply Rbar_rvplus_rv.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

  Lemma Condexp_cond_exp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
    :
      is_conditional_expectation prts dom2 f (ConditionalExpectation f).
  Proof.
    intros P dec sa_P.
    assert (isfe1:IsFiniteExpectation prts (rvmult f (EventIndicator dec))).
    {
      apply IsFiniteExpectation_indicator; trivial.
      now apply sub.
    }

    destruct (IsFiniteExpectation_parts prts (rvmult f (EventIndicator dec)))
      as [isfep isfen]; trivial.

    unfold Expectation.
    unfold ConditionalExpectation.
    transitivity (Rbar_Expectation
                    (Rbar_rvminus (Rbar_rvmult
                                     (NonNegCondexp (fun x : Ts => pos_fun_part f x))
                                     (fun x : Ts => EventIndicator dec x))
                                  (Rbar_rvmult
                                     (NonNegCondexp (fun x : Ts => neg_fun_part f x))
                                     (fun x : Ts => EventIndicator dec x)))).
    - unfold IsFiniteExpectation in isfep, isfen.
      match_option_in isfep; try tauto.
      match_option_in isfen; try tauto.
      destruct r; try tauto.
      destruct r0; try tauto.
      rewrite Rbar_Expectation_minus_finite with (e1:=r) (e2:=r0).
      + rewrite Expectation_pos_pofrf with (nnf:= (positive_part_nnf _)) in eqq.
        rewrite Expectation_pos_pofrf with (nnf:= (negative_part_nnf _)) in eqq0.
        invcs eqq.
        invcs eqq0.
        simpl.
        rewrite H0, H1.
        simpl.
        reflexivity.
      + apply Rbar_rvmult_rv.
        * apply (RandomVariable_sa_sub sub).
          apply NonNegCondexp_rv.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + apply Rbar_rvmult_rv.
        * apply (RandomVariable_sa_sub sub).
          apply NonNegCondexp_rv.
        * apply borel_Rbar_borel.
          apply EventIndicator_pre_rv.
          now apply sub.
      + rewrite <- NonNegCondexp_cond_exp; trivial.
        erewrite Expectation_proper; try eapply eqq.
        intros ?.
        rv_unfold; simpl.
        match_destr
        ; repeat rewrite Rmult_1_r
        ; repeat rewrite Rmult_0_r
        ; trivial.
        unfold Rmax; match_destr.
      + rewrite <- NonNegCondexp_cond_exp; trivial.
        erewrite Expectation_proper; try eapply eqq0.
        intros ?.
        rv_unfold; simpl.
        match_destr
        ; repeat rewrite Rmult_1_r
        ; repeat rewrite Rmult_0_r
        ; trivial.
        rewrite Ropp_0.
        unfold Rmax; match_destr.
    - apply Rbar_Expectation_proper.
      intros ?.
      unfold Rbar_rvminus, Rbar_rvmult, Rbar_rvplus, Rbar_rvopp.
      simpl.
      repeat rewrite (Rbar_mult_comm _ (EventIndicator dec a)).
      rewrite Rbar_mult_r_plus_distr.
      now rewrite <- Rbar_mult_opp_r.
  Qed.

  Lemma Rbar_Expec_Condexp (f : Ts -> R) 
        {rv : RandomVariable dom borel_sa f}
        {isfe:IsFiniteExpectation prts f}
    :
      Expectation f = 
      Rbar_Expectation (ConditionalExpectation f).
    Proof.
      generalize (Condexp_cond_exp f pre_Ω (classic_dec pre_Ω) (sa_all)); intros.
      assert (indall: rv_eq
                (fun (x:Ts) => (EventIndicator (classic_dec pre_Ω)) x)
                (fun (x:Ts) =>  (const 1) x)).
      {
        intro x.
        unfold EventIndicator, pre_Ω, const.
        now match_destr.
      }
      assert (rv_eq
                (rvmult f (EventIndicator (classic_dec pre_Ω)))
                f).
        {
          intro x.
          unfold rvmult.
          rewrite indall.
          unfold const.
          now rewrite Rmult_1_r.
        }
        rewrite (Expectation_ext H0) in H.
        assert (rv_eq
                  (Rbar_rvmult
                     (ConditionalExpectation f)
                     (fun x : Ts => EventIndicator (classic_dec pre_Ω) x))
                  (ConditionalExpectation f)).
        {
          intro x.
          unfold Rbar_rvmult.
          rewrite indall.
          unfold const.
          now rewrite Rbar_mult_1_r.
       }
        now rewrite (Rbar_Expectation_ext H1) in H.
   Qed.

  (*  Lemma event_Rbar_Rgt_sa (σ:SigmaAlgebra Ts) (x1 x2:Ts->Rbar)
      {rv1:RandomVariable σ Rbar_borel_sa x1}
      {rv2:RandomVariable σ Rbar_borel_sa x2}
      (forall x, ex_Rbar_plus (x1 x) (Rbar_opp (x2 x)))
  : sa_sigma (fun x => Rbar_gt (x1 x) (x2 x)).
Proof.
  apply (sa_proper _ (fun x => (Rbar_rvminus x1 x2) x > 0)).
  - unfold Rbar_rvminus.
    intros ?.
    unfold Rbar_rvminus, Rbar_gt, Rbar_rvopp, Rbar_rvplus.
    destruct x1; destruct x2; simpl; try (intuition lra).

    
    + split; trivial; intros.

    intuition lra.
  - apply sa_le_gt; intros.
    apply rv_measurable.
    typeclasses eauto.
Qed.

  Definition event_Rbar_Rgt (σ:SigmaAlgebra Ts) x1 x2
      {rv1:RandomVariable σ borel_sa x1}
      {rv2:RandomVariable σ borel_sa x2} : event σ
  := exist _ _ (event_Rgt_sa σ x1 x2).

Lemma event_Rbar_Rgt_dec (σ:SigmaAlgebra Ts) x1 x2
      {rv1:RandomVariable σ borel_sa x1}
      {rv2:RandomVariable σ borel_sa x2} :
  dec_event (event_Rgt σ x1 x2).
Proof.
  unfold event_Rgt.
  intros x; simpl.
  apply Rgt_dec.
Qed.
   *)


  
  Lemma NonNegConditionalExpectation_proper (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {nnf1 : NonnegativeFunction f1} 
        {nnf2 : NonnegativeFunction f2} :
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (NonNegCondexp f1)
             (NonNegCondexp f2).
  Proof.
    intros eqq.
    generalize (NonNegCondexp_cond_exp f1); intros HH1.
    generalize (NonNegCondexp_cond_exp f2); intros HH2.
    apply (is_conditional_expectation_nneg_unique prts sub f1 (NonNegCondexp f1) (NonNegCondexp f2) HH1).
    apply (is_conditional_expectation_proper prts sub f2 f1 (NonNegCondexp f2) (NonNegCondexp f2)); trivial.
    - now symmetry.
    - reflexivity.
  Qed.

  Lemma ConditionalExpectation_proper (f1 f2 : Ts -> R) 
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2} :
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation f1)
             (ConditionalExpectation f2).
  Proof.
    intros eqq.
    unfold ConditionalExpectation.
    apply Rbar_rvplus_almost_proper.
    - apply NonNegConditionalExpectation_proper.
      now apply pos_fun_part_proper_almostR2.
    - apply Rbar_rvopp_almost_proper.
      apply NonNegConditionalExpectation_proper.
      now apply neg_fun_part_proper_almostR2.
  Qed.

End cond_exp2.

Section cond_exp_props.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Existing Instance RandomVariable_sa_sub.
  Existing Instance conditional_expectation_L2fun_rv.

  (* prove ext theorems for the conditional expectations stuff) *)

  Let nneg2 : nonnegreal := bignneg 2 big2.
  Canonical nneg2.

  Lemma LpRRVnorm_const {p} c : p <> 0 -> LpRRVnorm (p:=p) prts (LpRRVconst prts c) = Rabs c.
  Proof.
    intros.
    unfold LpRRVnorm; simpl.
    rv_unfold.
    generalize (FiniteExpectation_const prts (power (Rabs c) p))
    ; intros HH.
    unfold const in HH.
    erewrite FiniteExpectation_pf_irrel.
    rewrite HH.
    apply inv_power_cancel; trivial.
    apply Rabs_pos.
  Qed.
  
  Lemma LpRRVnorm0 {p} : p <> 0 -> LpRRVnorm (p:=p) prts (LpRRVzero prts) = 0.
  Proof.
    intros.
    unfold LpRRVzero.
    rewrite LpRRVnorm_const; trivial.
    now rewrite Rabs_R0.
  Qed.
  
  Lemma conditional_expectation_L2fun_rv_eq
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {rv2 : RandomVariable dom2 borel_sa f}
        {isl : IsLp prts 2 f} :
    LpRRV_eq prts
             (conditional_expectation_L2fun prts sub f)
             (pack_LpRRV prts f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    destruct a as [xrv [xeq xuniq]].
    match type of xeq with
    |  _ = (real ?x) => replace x with (Finite 0) in xeq
    end.
    - apply LpRRV_norm0 in xeq.
      apply LpRRValmost_sub_zero_eq in xeq.
      symmetry.
      apply xeq.
    - symmetry.
      unfold Glb_Rbar, proj1_sig.
      match_destr.
      destruct i as [lb glb].
      unfold is_lb_Rbar in *.
      apply Rbar_le_antisym.
      + apply lb.
        exists (pack_LpRRV prts f (rv:=RandomVariable_sa_sub sub f)).
        split; trivial.
        LpRRV_simpl.
        rewrite (LpRRV_norm_proper prts _ (LpRRVzero prts)).
        * rewrite LpRRVnorm0; trivial.
        * apply LpRRV_seq_eq.
          unfold LpRRV_seq; simpl.
          rewrite rvminus_self.
          reflexivity.
      + apply glb; intros y [w [rvw eqw]].
        subst.
        unfold LpRRVnorm; simpl.
        apply power_nonneg.
  Qed.



  Lemma NonNegConditionalExpectation_rv_eq f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {rv2 : RandomVariable dom2 borel_sa f}
        {nnf : NonnegativeFunction f} :
    almostR2  (prob_space_sa_sub prts sub) eq
              (NonNegCondexp prts sub f)
              f.
  Proof.
    eapply is_conditional_expectation_nneg_unique; trivial.
    - typeclasses eauto.
    - apply NonNegCondexp_cond_exp.
    - unfold is_conditional_expectation.
      intros.
      assert (rv_eq (Rbar_rvmult (fun x : Ts => f x) (fun x : Ts => EventIndicator dec x))
                    (rvmult f (EventIndicator dec))).
      {
        intro x.
        unfold Rbar_rvmult, rvmult.
        now simpl.
      }
      rewrite (Rbar_Expectation_ext H0).
      apply gen_Expectation_Rbar_Expectation.
  Qed.

  Corollary NonNegConditionalExpectation_const c pf
            {dom2 : SigmaAlgebra Ts}
            (sub : sa_sub dom2 dom) :
    almostR2 (prob_space_sa_sub prts sub) eq
             (NonNegCondexp prts sub (const c) (nnf:=pf))
             (const c).
  Proof.
    apply NonNegConditionalExpectation_rv_eq.
    apply rvconst.
  Qed.

  (* If f is dom2-measurable, then its conditional expectation with
     respect to dom2 is almost itself *)
  Theorem ConditionalExpectation_rv_eq
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          f
          {rv : RandomVariable dom borel_sa f}
          {rv2 : RandomVariable dom2 borel_sa f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub f)
             f.
  Proof.
    unfold ConditionalExpectation, Rbar_rvminus.
    rewrite (NonNegConditionalExpectation_rv_eq (fun x : Ts => pos_fun_part f x))
      by typeclasses eauto.
    rewrite (NonNegConditionalExpectation_rv_eq (fun x : Ts => neg_fun_part f x))
      by typeclasses eauto.
    apply almostR2_eq_subr.
    unfold Rbar_rvplus.
    intros a.
    generalize (rv_pos_neg_id f a).
    unfold rvplus, rvopp, rvscale; simpl.
    intros eqq.
    f_equal.
    etransitivity; try (symmetry; eapply eqq).
    lra.
  Qed.

  Corollary ConditionalExpectation_const
            {dom2 : SigmaAlgebra Ts}
            (sub : sa_sub dom2 dom) c :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub (const c))
             (const c).
  Proof.
    apply ConditionalExpectation_rv_eq.
    apply rvconst.
  Qed.

  Lemma conditional_expectation_L2fun_scale
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        c :
    LpRRV_eq prts
             (conditional_expectation_L2fun prts sub (rvscale c f))
             (LpRRVscale prts c (conditional_expectation_L2fun prts sub f)).
  Proof.
    symmetry.
    apply (conditional_expectation_L2fun_unique2)
    ; try typeclasses eauto.
    intros.
    transitivity (L2RRVinner prts (LpRRVscale prts c (pack_LpRRV prts f)) w); try reflexivity.
    repeat rewrite L2RRV_inner_scal.
    f_equal.
    now apply conditional_expectation_L2fun_eq2.
  Qed.

  Lemma conditional_expectation_L2fun_opp
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    LpRRV_eq prts
             (conditional_expectation_L2fun prts sub (rvopp f))
             (LpRRVopp prts (conditional_expectation_L2fun prts sub f)).
  Proof.
    etransitivity.
    - etransitivity; [| apply (conditional_expectation_L2fun_scale sub f (-1))].
      now apply conditional_expectation_L2fun_proper.
    - apply almostR2_eq_subr; intros ?; simpl.
      reflexivity.
  Qed.

  Lemma conditional_expectation_L2fun_Expectation
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    Expectation (conditional_expectation_L2fun prts sub f) = Expectation f.
  Proof.
    generalize (conditional_expectation_L2fun_eq2 prts sub f (LpRRVconst prts 1)); intros HH.
    cut_to HH; try typeclasses eauto.
    unfold L2RRVinner in HH.
    unfold LpRRVconst in HH; simpl in HH.
    rewrite (FiniteExpectation_ext prts
                                   (rvmult (conditional_expectation_L2fun prts sub f) (const 1))
                                   (conditional_expectation_L2fun prts sub f)
            ) in HH by (intros ?; rv_unfold; lra).
    rewrite (FiniteExpectation_ext prts
                                   (rvmult f (const 1))
                                   f
            ) in HH by (intros ?; rv_unfold; lra).
    unfold FiniteExpectation, proj1_sig in HH.
    repeat match_destr_in HH; congruence.
  Qed.

  Lemma Lim_seq_min_n_scale (fx c : R) :
    Lim_seq (fun n : nat => Rmin (c * fx) (INR n)) = 
    Lim_seq (fun n : nat => c * Rmin (fx) (INR n)).
  Proof.
    rewrite Lim_seq_min.
    rewrite Lim_seq_scal_l.
    rewrite Lim_seq_min.
    now simpl.
  Qed.

  Lemma rvmin_INR_le (f : Ts -> R) :
    forall (n:nat),
      rv_le (rvmin f (const (INR n))) (rvmin f (const (INR (S n)))).
  Proof.
    intros n x.
    unfold rvmin, const.
    apply Rle_min_compat_l.
    apply le_INR.
    lia.
  Qed.

  Instance NonNeg_rvmin (f g : Ts -> R)
           {nnf: NonnegativeFunction f}
           {nng: NonnegativeFunction g} :
    NonnegativeFunction (rvmin f g).
  Proof.
    unfold NonnegativeFunction in *.
    unfold rvmin.
    intros.
    now apply Rmin_glb.
  Qed.

  Instance NonNeg_INR (n : nat) :
    @NonnegativeFunction Ts (const (INR n)).
  Proof.
    unfold NonnegativeFunction.
    intro.
    apply pos_INR.
  Qed.

  Lemma Rbar_NonnegExpectation_scale (c: posreal) 
        (rv_X : Ts -> Rbar)
        {pofrf:Rbar_NonnegativeFunction rv_X} 
        {pofcrf:Rbar_NonnegativeFunction (fun omega => Rbar_mult c (rv_X omega))} :
    Rbar_NonnegExpectation (fun omega => Rbar_mult c (rv_X omega)) =
    Rbar_mult c (Rbar_NonnegExpectation rv_X).
  Proof.
    unfold Rbar_NonnegExpectation.
    unfold SimpleExpectationSup.
    rewrite <- lub_rbar_scale.
    apply Lub_Rbar_eqset; intros.
    split; intros [? [? [? [[??]?]]]].
    - exists (rvscale (/ c) x0).
      exists (rvscale_rv _ _ _ _).
      exists (frfscale _ _).
      split; [split |].
      + assert (0 < / c).
        { destruct c; simpl.
          now apply Rinv_0_lt_compat.
        } 
        apply (positive_scale_nnf (mkposreal _ H2) x0). 
      + unfold rv_le, rvscale in *.
        intros y.
        specialize (H0 y).
        simpl in H0.
        destruct (rv_X y).
        * simpl in H0.
          apply (Rmult_le_compat_l (/ c)) in H0.
          -- rewrite <- Rmult_assoc in H0.
             rewrite Rinv_l in H0.
             ++ simpl; lra.
             ++ destruct c; simpl; lra.
          -- destruct c; simpl.
             left.
             now apply Rinv_0_lt_compat.
        * now simpl.
        * generalize (cond_pos c); intros.
          rewrite Rbar_mult_comm in H0.
          rewrite <- Rbar_mult_mult_pos in H0.
          now simpl in H0.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1.
        field; trivial.
        destruct c; simpl.
        lra.
    - exists (rvscale c x0).
      exists (rvscale_rv _ _ _ _).
      exists (frfscale c x0).
      split; [split |].
      + typeclasses eauto.
      + intro z.
        specialize (H0 z).
        unfold rvscale.
        rewrite Rbar_mult_comm.
        rewrite <- Rbar_mult_mult_pos.
        replace (Finite (c * x0 z)) with (Rbar_mult_pos (x0 z) c).
        apply Rbar_mult_pos_le; trivial.
        simpl.
        now rewrite Rmult_comm.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1.
        field; trivial.
        destruct c; simpl.
        lra.
  Qed.

  Lemma Rbar_mult_pos_div_pos (x : Rbar) (c : posreal) :
    x = Rbar_mult_pos (Rbar_div_pos x c) c.
  Proof.
    destruct x.
    - simpl.
      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite Rinv_l.
      + now rewrite Rmult_1_r.
      + apply Rgt_not_eq.
        apply cond_pos.
    - now simpl.
    - now simpl.
  Qed.

  Lemma  Rbar_le_mult_pos_div_pos (x r : Rbar) (c : posreal) :
    Rbar_le (Rbar_mult_pos x c) r <-> Rbar_le x (Rbar_div_pos r c).
  Proof.
    generalize (cond_pos c); intros.
    assert (pos c <> 0) by now apply Rgt_not_eq.
    split; intros.
    - rewrite Rbar_mult_pos_le with (z := c).
      now rewrite <- Rbar_mult_pos_div_pos.
    - rewrite Rbar_mult_pos_le with (z := c) in H1.
      now rewrite <- Rbar_mult_pos_div_pos in H1.
  Qed.

  Instance Rbar_mult_pos_measurable (domm :SigmaAlgebra Ts) (f : Ts -> Rbar) (c:posreal) :
    RbarMeasurable (dom := domm) f ->
    RbarMeasurable (dom := domm) (fun omega => Rbar_mult_pos (f omega) c).
  Proof.
    intros ? r.
    assert (pre_event_equiv (fun omega : Ts => Rbar_le (Rbar_mult_pos (f omega) c) r)
                            (fun omega : Ts => Rbar_le (f omega) (Rbar_div_pos r c))).
    - red; intros.
      apply Rbar_le_mult_pos_div_pos.
    - rewrite H0.
      apply H.
  Qed.

  Lemma NonNegConditionalExpectation_scale
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f}
        (c:posreal) :
    almostR2 (prob_space_sa_sub prts sub) eq
             (NonNegCondexp prts sub (rvscale c f))
             (fun omega => Rbar_mult c (NonNegCondexp prts sub f omega)).
  Proof.
    generalize (is_conditional_expectation_nneg_unique 
                  prts sub (rvscale c f) 
                  (NonNegCondexp prts sub (rvscale c f))); intros.
    specialize (H (fun omega => Rbar_mult c (NonNegCondexp prts sub f omega))).
    specialize (H _ _).
    assert (rvce2 : RandomVariable dom2 Rbar_borel_sa (fun omega : Ts => Rbar_mult c (NonNegCondexp prts sub f omega))).
    {
      apply Rbar_measurable_rv.
      apply RbarMeasurable_proper with (x := fun omega => Rbar_mult_pos (NonNegCondexp prts sub f omega) c).
      - intro x.
        rewrite Rbar_mult_mult_pos.
        apply Rbar_mult_comm.
      - apply (Rbar_mult_pos_measurable dom2).
        apply rv_Rbar_measurable.
        apply NonNegCondexp_rv.
    }
    specialize (H rvce2 _ _).
    apply H.
    - intro x.
      rewrite Rbar_mult_comm.
      rewrite <- Rbar_mult_mult_pos.
      replace (Finite 0) with (Rbar_mult_pos (Finite 0) c).
      + apply Rbar_mult_pos_le.
        apply NonNegCondexp_nneg.
      + unfold Rbar_mult_pos.
        now rewrite Rmult_0_l.
    - apply NonNegCondexp_cond_exp.
    - unfold is_conditional_expectation; intros.
      generalize (NonNegCondexp_cond_exp prts sub f P dec H0); intros.
      assert (rv_eq (rvmult (rvscale c f) (EventIndicator dec)) (rvscale c (rvmult f (EventIndicator dec)))).
      {
        intro x.
        rv_unfold.
        lra.
      }
      rewrite (Expectation_ext H2).
      erewrite Expectation_pos_pofrf.
      erewrite Expectation_pos_pofrf in H1.
      assert (Rbar_NonnegativeFunction 
                (Rbar_rvmult (NonNegCondexp prts sub f) (fun x : Ts => EventIndicator dec x))).
      {
        intro x.
        unfold EventIndicator, Rbar_rvmult.
        match_destr.
        - rewrite Rbar_mult_1_r.
          apply NonNegCondexp_nneg.
        - rewrite Rbar_mult_0_r.
          now simpl.
      }
      assert (Rbar_NonnegativeFunction
                (Rbar_rvmult (fun omega : Ts => Rbar_mult c (NonNegCondexp prts sub f omega)) 
                             (fun x : Ts => EventIndicator dec x))).
      {
        intro x.
        unfold EventIndicator, Rbar_rvmult.
        match_destr.
        - rewrite Rbar_mult_1_r.
          rewrite Rbar_mult_comm.
          rewrite <- Rbar_mult_mult_pos.
          replace (Finite 0) with (Rbar_mult_pos 0 c).
          + apply Rbar_mult_pos_le.
            apply NonNegCondexp_nneg.
          + simpl.          
            now rewrite Rmult_0_l.
        - rewrite Rbar_mult_0_r.
          now simpl.
      }
      rewrite Rbar_Expectation_pos_pofrf with (nnf0 := H4).
      rewrite Rbar_Expectation_pos_pofrf with (nnf0 := H3) in H1.
      f_equal.
      inversion H1.
      rewrite NonnegExpectation_scale.
      rewrite H6.
      erewrite <- Rbar_NonnegExpectation_scale.
      apply Rbar_NonnegExpectation_ext.
      intro x.
      unfold Rbar_rvmult.
      destruct (NonNegCondexp prts sub f x).
      + simpl; now rewrite Rmult_assoc.
      + unfold EventIndicator.
        replace (Rbar_mult c p_infty) with (p_infty).
        match_destr.
        * rewrite Rbar_mult_1_r.
          rewrite Rbar_mult_comm.
          rewrite <- Rbar_mult_mult_pos.
          now simpl.
        * rewrite Rbar_mult_0_r.
          now rewrite Rbar_mult_0_r.
        * rewrite Rbar_mult_comm.
          rewrite <- Rbar_mult_mult_pos.
          now simpl.
      + unfold EventIndicator.
        replace (Rbar_mult c m_infty) with (m_infty).
        match_destr.
        * rewrite Rbar_mult_1_r.
          rewrite Rbar_mult_comm.
          rewrite <- Rbar_mult_mult_pos.
          now simpl.
        * rewrite Rbar_mult_0_r.
          now rewrite Rbar_mult_0_r.
        * rewrite Rbar_mult_comm.
          rewrite <- Rbar_mult_mult_pos.
          now simpl.
          Unshelve.
          intro z.
          rewrite Rbar_mult_comm.
          rewrite <- Rbar_mult_mult_pos.
          replace (Finite 0) with (Rbar_mult_pos 0 c).
          apply Rbar_mult_pos_le.
          apply H3.
          simpl.
          now rewrite Rmult_0_l.
  Qed.

  Lemma pos_fun_part_scale_pos_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (pos_fun_part (rvscale c f) x)) (rvscale c (fun x : Ts => pos_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    now rewrite (scale_Rmax0 (mkposreal c H)); simpl.
  Qed.

  Lemma neg_fun_part_scale_pos_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (neg_fun_part (rvscale c f) x)) (rvscale c (fun x : Ts => neg_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    rewrite Ropp_mult_distr_r.
    now rewrite (scale_Rmax0 (mkposreal c H)); simpl.
  Qed.

  Lemma pos_fun_part_scale_neg_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (pos_fun_part (rvscale (- c) f) x)) (rvscale c (fun x : Ts => neg_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    rewrite <- (scale_Rmax0 (mkposreal c H)); simpl.
    f_equal; lra.
  Qed.

  Lemma neg_fun_part_scale_neg_eq c f : 
    0 < c ->
    rv_eq (fun x => nonneg (neg_fun_part (rvscale (- c) f) x)) (rvscale c (fun x : Ts => pos_fun_part f x)).
  Proof.
    intros ??.
    unfold rvscale; simpl.
    rewrite Ropp_mult_distr_r.
    rewrite <- (scale_Rmax0 (mkposreal c H)); simpl.
    f_equal; lra.
  Qed.


  Theorem ConditionalExpectation_scale
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          f
          {rv : RandomVariable dom borel_sa f}
          c :
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub (rvscale c f))
             (fun omega => Rbar_mult c (ConditionalExpectation prts sub f omega)).
  Proof.
    destruct (Rtotal_order c 0) as [?|[?|?]].
    - unfold ConditionalExpectation, Rbar_rvminus.
      assert (cpos:0 < - c) by lra.
      pose (cc:=mkposreal _ cpos).
      rewrite (NonNegConditionalExpectation_proper prts sub (fun x : Ts => pos_fun_part (rvscale c f) x) (rvscale cc (neg_fun_part f)))
      , (NonNegConditionalExpectation_proper prts sub (fun x : Ts => neg_fun_part (rvscale c f) x) (rvscale cc (pos_fun_part f))).
      + repeat rewrite NonNegConditionalExpectation_scale.
        simpl.
        apply almostR2_eq_subr; intros ?.
        unfold Rbar_rvplus, Rbar_rvopp.
        replace (Finite (- c)) with (Rbar_opp (Finite c)) by reflexivity.
        
        rewrite <- Rbar_mult_opp_l.
        rewrite Rbar_opp_involutive.
        rewrite Rbar_mult_opp_l.
        rewrite <- Rbar_mult_opp_r.
        rewrite <- Rbar_mult_r_plus_distr.
        now rewrite Rbar_plus_comm.
      + apply almostR2_eq_subr.
        rewrite <- neg_fun_part_scale_neg_eq.
        * simpl.
          now rewrite Ropp_involutive.
        * unfold cc; simpl; lra.
      + apply almostR2_eq_subr.
        rewrite <- pos_fun_part_scale_neg_eq.
        * simpl.
          now rewrite Ropp_involutive.
        * unfold cc; simpl; lra.
    - subst.
      unfold rvscale.
      rewrite (ConditionalExpectation_proper prts sub _ (const 0))
      ; [| apply almostR2_eq_subr; intros ?; unfold const; lra].
      rewrite ConditionalExpectation_const.
      apply almostR2_eq_subr; intros ?.
      rewrite Rbar_mult_0_l.
      reflexivity.
    - unfold ConditionalExpectation, Rbar_rvminus.
      pose (cc:=mkposreal c H).
      rewrite (NonNegConditionalExpectation_proper prts sub (fun x : Ts => pos_fun_part (rvscale c f) x) (rvscale cc (pos_fun_part f)))
      , (NonNegConditionalExpectation_proper prts sub (fun x : Ts => neg_fun_part (rvscale c f) x) (rvscale cc (neg_fun_part f))).
      + repeat rewrite NonNegConditionalExpectation_scale.
        simpl.
        apply almostR2_eq_subr; intros ?.
        unfold Rbar_rvplus, Rbar_rvopp.
        rewrite <- Rbar_mult_opp_r.
        now rewrite Rbar_mult_r_plus_distr.
      + apply almostR2_eq_subr.
        apply neg_fun_part_scale_pos_eq.
        unfold cc; simpl; lra.
      + apply almostR2_eq_subr.
        apply pos_fun_part_scale_pos_eq.
        unfold cc; simpl; lra.
  Qed.

  Lemma Rbar_rvlim_plus_min (f1 f2 : Ts -> R) :
    rv_eq
      (Rbar_rvlim
         (fun n : nat =>
            rvplus (rvmin f1 (const (INR n))) 
                   (rvmin f2 (const (INR n)))))
      (Rbar_rvlim
         (fun n : nat =>
            rvmin (rvplus f1 f2) (const (INR n)))). 
  Proof.
    intro x.
    unfold Rbar_rvlim, rvmin, rvplus, const.
    rewrite Lim_seq_plus.
    - do 3 rewrite Lim_seq_min.
      now simpl.
    - apply ex_lim_seq_incr.
      intros.
      apply Rle_min_compat_l.
      apply le_INR.
      lia.
    - apply ex_lim_seq_incr.
      intros.
      apply Rle_min_compat_l.
      apply le_INR.
      lia.
    - do 2 rewrite Lim_seq_min.
      now simpl.
  Qed.
  
  Lemma ConditionalExpectation_nonneg
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f}
    :
      almostR2 (prob_space_sa_sub prts sub) eq (ConditionalExpectation prts sub f)
               (NonNegCondexp prts sub f).
  Proof.
    unfold ConditionalExpectation.
    transitivity ((Rbar_rvplus (NonNegCondexp prts sub (fun x : Ts => pos_fun_part f x))
                               (Rbar_rvopp (const 0)))).
    - apply Rbar_rvplus_almost_proper; try reflexivity.
      apply Rbar_rvopp_almost_proper.
      transitivity (NonNegCondexp prts sub (const 0) (nnf:=fun _ => z_le_z)).
      + apply NonNegConditionalExpectation_proper.
        apply almostR2_eq_subr.
        rewrite <- neg_fun_part_pos; trivial.
        reflexivity.
      + apply NonNegConditionalExpectation_const.
    - transitivity (NonNegCondexp prts sub (fun x : Ts => pos_fun_part f x)).
      + apply almostR2_eq_subr; intros ?.
        unfold Rbar_rvplus, Rbar_rvopp, const; simpl.
        rewrite Ropp_0.
        apply Rbar_plus_0_r.
      + apply NonNegConditionalExpectation_proper.
        apply almostR2_eq_subr; intros ?.
        rewrite <- pos_fun_part_pos; trivial.
  Qed.
  
  Lemma NonNegConditionalExpectation_L2
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f}
        {isl : IsLp prts 2 f}
    :
      almostR2  (prob_space_sa_sub prts sub) eq (NonNegCondexp prts sub f)
                (LpRRV_rv_X prts (conditional_expectation_L2fun prts sub f)).
  Proof.
    generalize (is_conditional_expectation_nneg_unique 
                  prts sub f
                  (NonNegCondexp prts sub f) ); intros uniq.
    generalize (conditional_expectation_L2fun_rv prts sub f); intros cond_rv.
    generalize (conditional_expectation_L2fun_nonneg prts sub f); intros anneg.
    unfold almostR2, const in anneg.
    destruct (almost_map_R_split _ anneg)
      as [ce [eqq1 [nneg ce_rv]]].
    cut_to ce_rv; trivial.
    rewrite (almost_f_equal _ _ _ _ eqq1).
    
    specialize (uniq (fun x => ce x) rv _).
    rewrite borel_Rbar_borel in ce_rv, cond_rv.
    specialize (uniq ce_rv nnf _).
    apply uniq; trivial.
    - apply NonNegCondexp_cond_exp.
    - apply
        is_conditional_expectation_proper
        with (f1:=f)
             (ce1:=(LpRRV_rv_X _ (conditional_expectation_L2fun prts sub f)))
             (rvf1:=rv)
             (rvce1:=cond_rv); trivial.
      + reflexivity.
      + apply almost_f_equal.
        eapply almostR2_prob_space_sa_sub_lift; eauto.
      + apply conditional_expectation_L2fun_cond_exp.
  Qed.

  Global Instance pos_fun_part_islp (p:nonnegreal) f :
    IsLp prts p f ->
    IsLp prts p (pos_fun_part f).
  Proof.
    intros islp.
    eapply IsLp_bounded; try eapply islp.
    intros ?.
    rv_unfold; simpl.
    apply Rle_power_l.
    - apply cond_nonneg.
    - split.
      + apply Rabs_pos.
      + unfold Rmax.
        match_destr.
        * rewrite Rabs_R0.
          apply Rabs_pos.
        * reflexivity.
  Qed.

  Global Instance neg_fun_part_islp (p:nonnegreal) f :
    IsLp prts p f ->
    IsLp prts p (neg_fun_part f).
  Proof.
    intros islp.
    assert (islp2:IsLp prts p (rvopp f)) by now apply IsLp_opp.
    generalize (pos_fun_part_islp p (rvopp f) islp2).
    apply IsLp_proper; trivial.
    unfold rvopp; intros a.
    generalize (pos_fun_part_scale_neg_eq 1 f).
    replace (- (1)) with (-1) by lra.
    intros HH.
    rewrite HH by lra.
    unfold rvscale.
    lra.
  Qed.

  Lemma almostR2_Finite {DOM : SigmaAlgebra Ts} (PRTS : ProbSpace DOM)  (x y:Ts->R) :
    almostR2 PRTS eq (fun a => (Finite (x a))) (fun a => (Finite (y a))) <->
    almostR2 PRTS eq x y.
  Proof.
    split
    ; intros [p[pone peqq]]
    ; exists p; split; trivial
    ; intros a pa
    ; specialize (peqq a pa).
    - now invcs peqq.
    - now rewrite peqq.
  Qed.

  (*
    Lemma ConditionalExpectation_L2 f
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv : RandomVariable dom borel_sa f}
          {isl : IsLp prts 2 f}
      :
        almostR2  (prob_space_sa_sub prts sub) eq (ConditionalExpectation prts f sub)
                 (LpRRV_rv_X prts (conditional_expectation_L2fun prts f sub)).
    Proof.
      unfold ConditionalExpectation.
      unfold Rbar_rvminus.
      repeat rewrite NonNegConditionalExpectation_L2.
      assert (islp2:IsLp prts 2 (rvplus (fun x : Ts => pos_fun_part f x) (rvopp (fun x : Ts => neg_fun_part f x)))).
      {
        eapply IsLp_proper; try (symmetry; eapply rv_pos_neg_id); eauto.
      }
      generalize (conditional_expectation_L2fun_plus prts (fun x : Ts => pos_fun_part f x) (rvopp (fun x : Ts => neg_fun_part f x)) sub)
      ; intros HH.
      simpl in HH.
      apply (almostR2_Finite (prob_space_sa_sub prts sub)).
      transitivity ( (fun x : Ts => conditional_expectation_L2fun prts
                                                               (rvplus (fun x : Ts => pos_fun_part f x) (rvopp (fun x : Ts => neg_fun_part f x))) sub x)).
      - red in HH.
        simpl in *.
        symmetry.
        etransitivity.
        + etransitivity; [| eapply HH].
          now apply conditional_expectation_L2fun_proper.
        + apply almostR2_eq_plus_proper; try reflexivity.
          etransitivity; [apply conditional_expectation_L2fun_opp |].
          simpl.
          apply almostR2_eq_subr; intros ?.
          unfold rvopp, rvscale.
          field_simplify.
          reflexivity.
      - apply conditional_expectation_L2fun_proper.
        apply almostR2_eq_subr.
        now rewrite <- rv_pos_neg_id.
    Qed.
   *)

  Lemma ConditionalExpectation_finexp_plus
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (f1 f2 : Ts -> R)
        {rvf1 : RandomVariable dom borel_sa f1}
        {rvf2 : RandomVariable dom borel_sa f2}
        {isfe1:IsFiniteExpectation prts f1}
        {isfe2:IsFiniteExpectation prts f2}
    :
      almostR2 (prob_space_sa_sub prts sub) eq
               (ConditionalExpectation prts sub (rvplus f1 f2))
               (Rbar_rvplus (ConditionalExpectation prts sub f1)
                            (ConditionalExpectation prts sub f2)).
  Proof.
    generalize (is_conditional_expectation_plus prts sub f1 f2
                                                            (ConditionalExpectation prts sub f1)
                                                            (ConditionalExpectation prts sub f2))
    ; intros HH.

    cut_to HH
    ; try now apply Condexp_cond_exp.
    generalize (Condexp_cond_exp prts sub (rvplus f1 f2))
    ; intros HH2.

    generalize (is_conditional_expectation_unique prts sub (rvplus f1 f2))
    ; intros HH3.
    specialize (HH3 
                  (ConditionalExpectation prts sub (rvplus f1 f2))
                  (Rbar_rvplus (ConditionalExpectation prts sub f1)(ConditionalExpectation prts sub f2))
                  _ ).
    assert (rvce1 : RandomVariable dom2 Rbar_borel_sa
                                   (ConditionalExpectation prts sub (rvplus f1 f2))).
    {
      apply Condexp_rv.
    }
    assert (rvce2 : RandomVariable dom2 Rbar_borel_sa
                                   (Rbar_rvplus (ConditionalExpectation prts sub f1)
                                                (ConditionalExpectation prts sub f2))).
    {
      apply Rbar_rvplus_rv
      ; apply Condexp_rv.
    } 
    apply (HH3 _ _); trivial.
    typeclasses eauto.
  Qed.  


  Lemma NonNegConditionalExpectation_le
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f1 f2
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {nnf1 : NonnegativeFunction f1}
        {nnf2 : NonnegativeFunction f2} :
    almostR2 prts Rle f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) Rbar_le (NonNegCondexp prts sub f1) (NonNegCondexp prts sub f2).
  Proof.
  Admitted.
  
  Theorem ConditionalExpectation_le
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          f1 f2
          {rv1 : RandomVariable dom borel_sa f1}
          {rv2 : RandomVariable dom borel_sa f2} :
    almostR2 prts Rle f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) Rbar_le (ConditionalExpectation prts sub f1) (ConditionalExpectation prts sub f2).
  Proof.
  Admitted.

  Local Existing Instance Rbar_le_pre.
  Lemma NonNegConditionalExpectation_nonneg
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f}
    : almostR2 (prob_space_sa_sub prts sub) Rbar_le (const 0) (NonNegCondexp prts sub f).
  Proof.
    generalize (NonNegConditionalExpectation_le sub (const 0) f (nnf1:=fun _ => z_le_z))
    ; intros HH.
    cut_to HH.
    - rewrite <- HH.
      generalize (NonNegConditionalExpectation_const 0 (fun _ => z_le_z) sub)
      ; intros HH2.
      apply (almostR2_subrelation (prob_space_sa_sub prts sub) (R_subr:=eq_subrelation _)).
      now symmetry.
    - apply almostR2_le_subr.
      apply nnf.
  Qed.

  Instance rvmin_le_proper : Proper (rv_le ==> rv_le ==> rv_le) (@rvmin Ts).
  Proof.
    unfold rv_le, rvmin, pointwise_relation.
    intros ???????.
    unfold Rmin.
    repeat match_destr.
    - etransitivity; eauto.
    - etransitivity; try eapply H.
      lra.
  Qed.

  Instance const_le_proper : Proper (Rle ==> rv_le) (const (B:=Ts)).
  Proof.
    intros ????.
    now unfold const.
  Qed.

  Global Instance rvplus_le_proper : Proper (rv_le ==> rv_le ==> rv_le) (rvplus (Ts:=Ts)).
  Proof.
    unfold rv_le, rvplus, pointwise_relation.
    intros ???????.
    apply Rplus_le_compat; auto.
  Qed.

  Lemma Rbar_rvmult_comm (f1 f2 : Ts -> Rbar) :
    rv_eq (Rbar_rvmult f1 f2) (Rbar_rvmult f2 f1).
  Proof.
    intro x.
    unfold Rbar_rvmult.
    now rewrite Rbar_mult_comm.
  Qed.

  Instance nncondexp_mult_ind_rv 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           f {P} (dec : dec_pre_event P) 
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} :
    sa_sigma P ->
    RandomVariable dom Rbar_borel_sa
                   (Rbar_rvmult (NonNegCondexp prts sub f)
                                (fun x : Ts => EventIndicator dec x)).
  Proof.
    intros.
    apply RandomVariable_sa_sub; trivial.
    apply Rbar_rvmult_rv.
    - apply NonNegCondexp_rv.
    - apply Real_Rbar_rv.
      apply EventIndicator_pre_rv; trivial.
  Qed.

  Lemma NonNegConditionalExpectation_plus
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f1 f2
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {nnf1 : NonnegativeFunction f1}
        {nnf2 : NonnegativeFunction f2} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (NonNegCondexp prts sub (rvplus f1 f2))
             (Rbar_rvplus (NonNegCondexp prts sub f1) (NonNegCondexp prts sub f2)).
  Proof.
    generalize (is_conditional_expectation_nneg_unique 
                  prts sub (rvplus f1 f2)
                  (NonNegCondexp prts sub (rvplus f1 f2))); intros.
    specialize (H (Rbar_rvplus (NonNegCondexp prts sub f1) (NonNegCondexp prts sub f2)) _ _).
    assert (rvce2 : RandomVariable dom2 Rbar_borel_sa (Rbar_rvplus (NonNegCondexp prts sub f1) (NonNegCondexp prts sub f2))).
    {
      apply Rbar_rvplus_rv.
      - typeclasses eauto.
      - typeclasses eauto.
    }
    specialize (H rvce2 _ _ _).
    apply H.
    - apply NonNegCondexp_cond_exp.
    - unfold is_conditional_expectation; intros.
      generalize (NonNegCondexp_cond_exp prts sub f1 P dec H0); intros.
      generalize (NonNegCondexp_cond_exp prts sub f2 P dec H0); intros.        
      erewrite Expectation_pos_pofrf.
      erewrite Expectation_pos_pofrf in H1.
      erewrite Expectation_pos_pofrf in H2.        
      assert (Rbar_NonnegativeFunction 
                (Rbar_rvmult (Rbar_rvplus (NonNegCondexp prts sub f1) (NonNegCondexp prts sub f2)) 
                             (fun x : Ts => EventIndicator dec x))).
      {
        intro x.
        unfold EventIndicator, Rbar_rvmult.
        match_destr.
        - rewrite Rbar_mult_1_r.
          apply pos_Rbar_plus; apply NonNegCondexp_nneg.
        - rewrite Rbar_mult_0_r.
          now simpl.
      }
      rewrite Rbar_Expectation_pos_pofrf with (nnf := H3).
      f_equal.
      assert
        (rv_eq 
           (Rbar_rvmult (Rbar_rvplus (NonNegCondexp prts sub f1) (NonNegCondexp prts sub f2)) 
                        (fun x : Ts => EventIndicator dec x))
           (Rbar_rvplus (Rbar_rvmult (NonNegCondexp prts sub f1) (fun x : Ts => EventIndicator dec x))
                        (Rbar_rvmult (NonNegCondexp prts sub f2) (fun x : Ts => EventIndicator dec x)))).
      {
        intro x.
        unfold Rbar_rvmult, Rbar_rvplus.
        rewrite Rbar_mult_comm.
        rewrite Rbar_mult_r_plus_distr.
        now do 2 rewrite Rbar_mult_comm with (x := EventIndicator dec x).
      }
      assert
      (rv_eq
         (rvmult (rvplus f1 f2) (EventIndicator dec))
         (rvplus (rvmult f1 (EventIndicator dec)) (rvmult f2 (EventIndicator dec)))).
      {
        intro x.
        rv_unfold.
        lra.
      }
      rewrite (Rbar_NonnegExpectation_ext _ _ H4).
      rewrite (NonnegExpectation_ext _ _ H5).
      generalize (NonnegExpectation_sum (rvmult f1 (EventIndicator dec))); intros.
      specialize (H6 (rvmult f2 (EventIndicator dec))).
      generalize (Rbar_NonnegExpectation_plus (Rbar_rvmult (NonNegCondexp prts sub f1) (fun x : Ts => EventIndicator dec x))); intros.
      specialize (H7 (Rbar_rvmult (NonNegCondexp prts sub f2) (fun x : Ts => EventIndicator dec x)) ).
      specialize (H7
                    (nncondexp_mult_ind_rv sub f1 dec H0)
                    (nncondexp_mult_ind_rv sub f2 dec H0) _ _).
      rewrite H7.
      cut_to H6.
      + specialize (H6 _ _).
        rewrite H6.
        generalize (NonNegCondexp_cond_exp prts sub f1 P dec H0); intros.
        generalize (NonNegCondexp_cond_exp prts sub f2 P dec H0); intros.
        erewrite Expectation_pos_pofrf in H8.
        erewrite Expectation_pos_pofrf in H9.
        erewrite Rbar_Expectation_pos_pofrf in H8.
        erewrite Rbar_Expectation_pos_pofrf in H9.
        inversion H8.
        inversion H9.
        now f_equal.
      + apply rvmult_rv; trivial.
        apply RandomVariable_sa_sub; trivial.
        apply EventIndicator_pre_rv; trivial.
      + apply rvmult_rv; trivial.
        apply RandomVariable_sa_sub; trivial.
        apply EventIndicator_pre_rv; trivial.
        Unshelve.
        * typeclasses eauto.
        * typeclasses eauto.
        * typeclasses eauto.
        * typeclasses eauto.                                    
        * typeclasses eauto.
        * typeclasses eauto.
  Qed.

  Instance mult_ind_dom2 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (f : Ts -> R)
        (P : event dom2)
        {rvf : RandomVariable dom borel_sa f} :
    RandomVariable dom borel_sa (rvmult (EventIndicator (classic_dec P)) f).
  Proof.
    apply rvmult_rv; trivial.
    apply RandomVariable_sa_sub; trivial.
    typeclasses eauto.
  Qed.

  Lemma Condexp_factor_out_indicator
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (f : Ts -> R)
        (P : event dom2)
        {rvf : RandomVariable dom borel_sa f} 
        {rve: RandomVariable dom borel_sa (rvmult (EventIndicator (classic_dec P)) f)}:
    IsFiniteExpectation prts f ->
    Rbar_Expectation (ConditionalExpectation prts sub (rvmult (EventIndicator (classic_dec P))  f)) =
    Rbar_Expectation (Rbar_rvmult (EventIndicator (classic_dec P)) (ConditionalExpectation prts sub f)).
  Proof.
    intros.
    generalize (Condexp_cond_exp prts sub f P (classic_dec P)); intros.
    assert (rv_eq 
              (Rbar_rvmult (ConditionalExpectation prts sub f)
                           (EventIndicator (classic_dec P)))
              (Rbar_rvmult (EventIndicator (classic_dec P))
                           (ConditionalExpectation prts sub f))) by apply Rbar_rvmult_comm.
    specialize (H0 (proj2_sig P)).
    rewrite (Rbar_Expectation_ext H1) in H0.
    rewrite <- H0.
    assert (rv_eq
               (rvmult f (EventIndicator (classic_dec P)))
               (rvmult (EventIndicator (classic_dec P)) f)) by apply rvmult_comm.
    rewrite (Expectation_ext H2).
    symmetry.
    apply Rbar_Expec_Condexp.
    symmetry in H2.
    apply (IsFiniteExpectation_proper prts _ _ H2).
    apply IsFiniteExpectation_indicator; trivial.
    apply sub.
    apply (proj2_sig P).
 Qed.

  Lemma Condexp_factor_out_scale_indicator
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (f : Ts -> R)
        (c : R)
        (P : event dom2)
        {rvf : RandomVariable dom borel_sa f} 
        {rve: RandomVariable dom borel_sa (rvmult (rvscale c (EventIndicator (classic_dec P))) f)}:
    IsFiniteExpectation prts f ->
    Rbar_Expectation (ConditionalExpectation prts sub (rvmult (rvscale c (EventIndicator (classic_dec P)))  f)) =
    Rbar_Expectation (Rbar_rvmult (rvscale c (EventIndicator (classic_dec P))) (ConditionalExpectation prts sub f)).
  Proof.
    intros.
    generalize (Condexp_cond_exp prts sub (rvscale c f) P (classic_dec P) (proj2_sig P)); intros.
    generalize (ConditionalExpectation_scale sub f c); intros.
    apply almostR2_prob_space_sa_sub_lift_Rbar in H1.
    assert (almostR2 prts eq
                     (Rbar_rvmult (ConditionalExpectation prts sub (rvscale c f)) (EventIndicator (classic_dec P)))
                     (Rbar_rvmult (rvscale c (EventIndicator (classic_dec P))) (ConditionalExpectation prts sub f))).
    {
      destruct H1 as [? [? ?]].
      exists x.
      split; trivial.
      intros.
      specialize (H2 _ H3).
      unfold Rbar_rvmult.
      rewrite H2.
      unfold rvscale.
      rewrite Rbar_mult_comm with (x := c).
      rewrite <- Rbar_mult_assoc.
      now rewrite Rbar_mult_comm.
    }
    assert
    (RandomVariable dom Rbar_borel_sa
                    (Rbar_rvmult (ConditionalExpectation prts sub (rvscale c f)) (fun x : Ts => EventIndicator (classic_dec P) x))).
    {
      apply Rbar_rvmult_rv.
      + apply RandomVariable_sa_sub; trivial.
        apply Condexp_rv.
      + apply Real_Rbar_rv.
        apply RandomVariable_sa_sub; trivial.         
        typeclasses eauto.
     }
    assert
      (RandomVariable dom Rbar_borel_sa
                      (Rbar_rvmult (fun omega : Ts => rvscale c (EventIndicator (classic_dec P)) omega) (ConditionalExpectation prts sub f))).
     {
       apply Rbar_rvmult_rv.
       + apply Real_Rbar_rv.
         apply rvscale_rv.
         apply RandomVariable_sa_sub; trivial.         
         typeclasses eauto.
       + apply RandomVariable_sa_sub; trivial.
         apply Condexp_rv.
     }
    rewrite (Rbar_Expectation_almostR2_proper prts (dom := dom) _ _ H2) in H0.
    rewrite <- H0.
    assert (rv_eq
               (rvmult (rvscale c f) (EventIndicator (classic_dec P)))
               (rvmult (rvscale c (EventIndicator (classic_dec P))) f)).
    {
      intro x.
      rv_unfold.
      lra.
    }
    rewrite (Expectation_ext H5).
    symmetry.
    apply Rbar_Expec_Condexp.
    symmetry in H2.
    assert
      (rv_eq 
         (rvmult (rvscale c (EventIndicator (classic_dec P))) f)
         (rvscale c (rvmult f (EventIndicator (classic_dec P))))).
    {
      intro x.
      rv_unfold.
      lra.
    }
    apply (IsFiniteExpectation_proper prts _ _ H6).
    apply IsFiniteExpectation_scale.
    apply IsFiniteExpectation_indicator; trivial.
    apply sub.
    apply (proj2_sig P).
  Qed.
  
  Lemma Rbar_mult_plus_R (a b : R) (z : Rbar) :
    Rbar_mult z (a + b) = Rbar_plus (Rbar_mult z a) (Rbar_mult z b).
  Proof.
    destruct  z.
    - simpl; apply Rbar_finite_eq; lra.
  Admitted.

  Lemma Condexp_factor_out_plus
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        (f g1 g2 : Ts -> R)
        {rvf : RandomVariable dom borel_sa f}
        {rvg1 : RandomVariable dom2 borel_sa g1}
        {rvg2 : RandomVariable dom2 borel_sa g2}        
        {rvg1f : RandomVariable dom borel_sa (rvmult g1 f)}                 
        {rvg2f : RandomVariable dom borel_sa (rvmult g2 f)}                 
        {rve: RandomVariable dom borel_sa (rvmult (rvplus g1 g2) f)} :
    IsFiniteExpectation prts (rvmult g1 f) ->
    IsFiniteExpectation prts (rvmult g2 f) ->    
    
    Rbar_Expectation (ConditionalExpectation prts sub (rvmult g1 f)) = 
    Rbar_Expectation (Rbar_rvmult g1 (ConditionalExpectation prts sub f)) ->
    
    Rbar_Expectation (ConditionalExpectation prts sub (rvmult g2 f)) = 
    Rbar_Expectation (Rbar_rvmult g2 (ConditionalExpectation prts sub f)) ->

    Rbar_Expectation (ConditionalExpectation prts sub (rvmult (rvplus g1 g2) f)) = 
    Rbar_Expectation (Rbar_rvmult (rvplus g1 g2) (ConditionalExpectation prts sub f)).

  Proof.
    intros.
    generalize (ConditionalExpectation_finexp_plus sub (rvmult g1 f) (rvmult g2 f)); intros.
    apply almostR2_prob_space_sa_sub_lift_Rbar in H3.
    assert (rv_eq (rvmult (rvplus g1 g2) f) (rvplus (rvmult g1 f) (rvmult g2 f))).
    {
      intro.
      rv_unfold.
      lra.
    }
    apply (almostR2_eq_subr prts) in H4.
    apply ConditionalExpectation_proper with (sub0 := sub) (rv1 := rve)
      (rv2 := (@rvplus_rv Ts dom (@rvmult Ts g1 f) (@rvmult Ts g2 f) rvg1f rvg2f)) in H4.
    apply almostR2_prob_space_sa_sub_lift_Rbar in H4.
    generalize (almostR2_trans prts _ _ _ _ H4 H3); intros.
    assert (RandomVariable dom Rbar_borel_sa (ConditionalExpectation prts sub (rvmult (rvplus g1 g2) f))).
    {
      apply RandomVariable_sa_sub; trivial.
      typeclasses eauto.
    }
    assert (RandomVariable dom Rbar_borel_sa  (Rbar_rvplus (ConditionalExpectation prts sub (rvmult g1 f))
            (ConditionalExpectation prts sub (rvmult g2 f)))).
    {
      apply Rbar_rvplus_rv.
      + apply RandomVariable_sa_sub; trivial.
        typeclasses eauto.
      + apply RandomVariable_sa_sub; trivial.
        typeclasses eauto.
    }
    rewrite (Rbar_Expectation_almostR2_proper prts _ _ H5).
    assert (rv_eq  (Rbar_rvmult (fun omega : Ts => rvplus g1 g2 omega)
                                (ConditionalExpectation prts sub f))
                   (Rbar_rvplus 
                      (Rbar_rvmult g1 (ConditionalExpectation prts sub f))
                      (Rbar_rvmult g2 (ConditionalExpectation prts sub f)))).
    {
      intro x.
      unfold Rbar_rvmult.
      unfold rvplus, Rbar_rvplus.
      rewrite Rbar_mult_comm.
      rewrite Rbar_mult_comm with (x := g1 x).
      rewrite Rbar_mult_comm with (x := g2 x).      
      apply Rbar_mult_plus_R.
    }
    rewrite (Rbar_Expectation_ext H8).
    generalize (IsFiniteExpectation_Finite prts (rvmult g1 f)); intros.
    generalize (IsFiniteExpectation_Finite prts (rvmult g2 f)); intros.    
    destruct H9 as [r1 ?].
    destruct H10 as [r2 ?].
    rewrite Rbar_Expectation_sum_finite with (e1 := r1) (e2 := r2); trivial.
    rewrite Rbar_Expectation_sum_finite with (e1 := r1) (e2 := r2); trivial.
    - apply Rbar_rvmult_rv.
      + apply Real_Rbar_rv.
        apply RandomVariable_sa_sub; trivial.
      + apply RandomVariable_sa_sub; trivial.
        apply Condexp_rv.
    - apply Rbar_rvmult_rv.
      + apply Real_Rbar_rv.
        apply RandomVariable_sa_sub; trivial.
      + apply RandomVariable_sa_sub; trivial.
        apply Condexp_rv.
    - rewrite <- H1.
      now rewrite <- Rbar_Expec_Condexp.
    - rewrite <- H2.
      now rewrite <- Rbar_Expec_Condexp.
    - apply RandomVariable_sa_sub; trivial.
      apply Condexp_rv.
    - apply RandomVariable_sa_sub; trivial.
      apply Condexp_rv.
    - now rewrite <- Rbar_Expec_Condexp.
    - now rewrite <- Rbar_Expec_Condexp.
   Qed.
  
  Instance almostR2_eq_Rbar_plus_proper
          : Proper (almostR2 prts eq ==> almostR2 prts eq  ==> almostR2 prts eq) Rbar_rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (event_inter Px Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold Rbar_rvplus.
      now rewrite eq_onx, eq_ony.
  Qed.

  Instance almostR2_eq_Rbar_mult_proper
          : Proper (almostR2 prts eq ==> almostR2 prts eq  ==> almostR2 prts eq) Rbar_rvmult.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (event_inter Px Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold Rbar_rvmult.
      now rewrite eq_onx, eq_ony.
  Qed.

  Lemma Condexp_factor_out_frf
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f g
        {frfg : FiniteRangeFunction g}
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvgf: RandomVariable dom borel_sa (rvmult g f)} :
    IsFiniteExpectation prts f ->
    Rbar_Expectation (ConditionalExpectation prts sub (rvmult g f)) =
    Rbar_Expectation (Rbar_rvmult g (ConditionalExpectation prts sub f)).
  Proof.
    intros.
    generalize (frf_indicator_sum g); intros.
    unfold frf_indicator in H0.
    assert (rv_eq (rvmult g f)
                  (rvmult  
                     (fun omega : Ts =>
                        RealAdd.list_sum
                          (map (fun c : R => scale_val_indicator g c omega)
                               (nodup Req_EM_T frf_vals))) f)) by now rewrite H0.
    apply (all_almost prts) in H1.
    assert (RandomVariable dom borel_sa
          (rvmult
             (fun omega : Ts =>
              RealAdd.list_sum
                (map (fun c : R => scale_val_indicator g c omega)
                     (nodup Req_EM_T frf_vals))) f)) by admit.
    apply Rbar_Expectation_almostR2_proper.
    - apply RandomVariable_sa_sub; trivial.
      apply Condexp_rv.
    - apply Rbar_rvmult_rv.
      + apply RandomVariable_sa_sub; trivial.
        now apply Real_Rbar_rv.
      + apply RandomVariable_sa_sub; trivial.
        apply Condexp_rv.
    - generalize (ConditionalExpectation_proper prts sub _ _ H1); intros.
      apply almostR2_prob_space_sa_sub_lift_Rbar in H3.
      rewrite H3.
      assert (RandomVariable dom borel_sa g) by now apply RandomVariable_sa_sub.
      assert (RandomVariable dom borel_sa
          (fun omega : Ts =>
           RealAdd.list_sum
             (map (fun c : R => scale_val_indicator g c omega)
                  (nodup Req_EM_T frf_vals)))) by admit.
      assert (rv_eq (fun (omega:Ts) => Finite (g omega))
                    (fun omega : Ts => Finite (RealAdd.list_sum (map (fun c : R => scale_val_indicator g c omega) (nodup Req_EM_T frf_vals))))).
      {
        intro x.
        simpl.
        now rewrite H0.
      }
      assert (rv_eq (ConditionalExpectation prts sub f) (ConditionalExpectation prts sub f)).
      {
        intro.
        reflexivity.
      }
      apply (almostR2_eq_subr prts) in H6.
      apply (almostR2_eq_subr prts) in H7.      
      rewrite (almostR2_eq_Rbar_mult_proper _ _ H6 _ _ H7).
      
    Admitted.


  Lemma Condexp_factor_out0 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f g
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvgf: RandomVariable dom borel_sa (rvmult g f)} :
    IsFiniteExpectation prts (rvmult g f) ->
    Rbar_Expectation (ConditionalExpectation prts sub (rvmult g f)) =
    Rbar_Expectation (Rbar_rvmult g (ConditionalExpectation prts sub f)).
  Proof.
  Admitted.
  
  Lemma Condexp_factor_out 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        f g 
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g}
        {rvgf: RandomVariable dom borel_sa (rvmult g f)} :
    IsFiniteExpectation prts (rvmult g f) ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (ConditionalExpectation prts sub (rvmult g f))
             (Rbar_rvmult g (ConditionalExpectation prts sub f)).
  Proof.
    intros isfin.
    generalize (is_conditional_expectation_unique 
                  prts sub (rvmult g f)
                  (ConditionalExpectation prts sub (rvmult g f))); intros.
    specialize (H (Rbar_rvmult g (ConditionalExpectation prts sub f)) _ _).
    assert (RandomVariable dom2 Rbar_borel_sa
                           (Rbar_rvmult (fun x : Ts => g x) 
                                        (ConditionalExpectation prts sub f))).
    {
      apply Rbar_rvmult_rv.
      - now apply Real_Rbar_rv.
      - typeclasses eauto.
    }
    specialize (H H0 _).
    apply H.
    - now apply Condexp_cond_exp.
    - unfold is_conditional_expectation; intros.
      assert (rv_eq (rvmult (rvmult g f) (EventIndicator dec))
                    (rvmult (rvmult g (EventIndicator dec)) f)).
      {
        intro x.
        rv_unfold.
        lra.
      }
      rewrite (Expectation_ext H2).
      assert (rv_eq  
                (Rbar_rvmult (Rbar_rvmult g (ConditionalExpectation prts sub f))
                             (EventIndicator dec))
                (Rbar_rvmult (fun x => real ((rvmult g (EventIndicator dec)) x))
                             (ConditionalExpectation prts sub f))).
      {
        intro x.
        unfold Rbar_rvmult; rv_unfold.
        match_destr.
        - rewrite Rmult_1_r.
          now rewrite Rbar_mult_1_r.
        - rewrite Rmult_0_r.
          rewrite Rbar_mult_0_l.
          now rewrite Rbar_mult_0_r.
      }
      rewrite (Rbar_Expectation_ext H3).
      assert (RandomVariable dom2 borel_sa (rvmult g (EventIndicator dec))).
      {
        apply rvmult_rv; trivial.
        apply EventIndicator_pre_rv; trivial.
      }
      assert (RandomVariable dom borel_sa (rvmult (rvmult g (EventIndicator dec)) f)).
      {
        apply rvmult_rv; trivial.
        apply RandomVariable_sa_sub; trivial.
      }
      generalize (Condexp_factor_out0 sub f (rvmult g (EventIndicator dec))); intros.
      assert (IsFiniteExpectation prts (rvmult (rvmult g (EventIndicator dec)) f)).
      {
        symmetry in H2.
        apply (IsFiniteExpectation_proper prts _ _ H2).
        apply IsFiniteExpectation_indicator; trivial.
        apply sub.
        apply H1.
      }
      simpl.
      rewrite <- (H6 H7).
      now apply Rbar_Expec_Condexp.
   Qed.
  
End cond_exp_props.
