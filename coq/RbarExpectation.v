Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Coquelicot.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Export SimpleExpectation Expectation.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

  Section RbarBorel.
    
  Instance Rbar_borel_sa : SigmaAlgebra Rbar
    := generated_sa (fun (s:Rbar->Prop) => exists r, forall m, Rbar_le m r <-> s m).

  Context {Ts:Type}
    {dom: SigmaAlgebra Ts}.

    (* For the Rbar_borel_sa, this is an equivalent definition *)
  Class RbarMeasurable (f: Ts -> Rbar)
      := rbarmeasurable : forall (r:Rbar), 
          sa_sigma (fun omega : Ts => Rbar_le (f omega) r).

  Lemma Rbar_borel_sa_preimage
      (rvx: Ts -> Rbar)
      (pf_pre: forall r:Rbar, sa_sigma (fun omega:Ts => Rbar_le (rvx omega) r)%R) :
  (forall B: event Rbar_borel_sa, sa_sigma (event_preimage rvx B)).
  Proof.
    intros.
    unfold event_preimage.
    destruct B; simpl.
    apply generated_sa_closure in s.
    simpl in *.  
    dependent induction s.
    - apply sa_all.
    - destruct H as [??].
      generalize (pf_pre x).
      apply sa_proper; intros xx.
      specialize (H (rvx xx)).
      tauto.
    - apply sa_countable_union. 
      eauto.
    - apply sa_complement; eauto.
  Qed.

  Lemma Rbar_borel_sa_preimage2 
      (rvx: Ts -> Rbar):
  (forall r:Rbar, sa_sigma (fun omega:Ts => Rbar_le (rvx omega) r)) <-> 
  (forall B: event Rbar_borel_sa, (sa_sigma (event_preimage rvx B))).
Proof.
  split; intros.
  - now apply Rbar_borel_sa_preimage.
  - unfold event_preimage in *.
    refine (H (exist _  (fun x => Rbar_le x r) _)).
    apply generated_sa_sub.
    exists r; intuition.
Qed.

    Global Instance Rbar_measurable_rv (rv_X:Ts->Rbar)
             {rm:RbarMeasurable rv_X}
      : RandomVariable dom Rbar_borel_sa rv_X.
    Proof.
      intros ?.
      apply Rbar_borel_sa_preimage2; trivial; intros.
    Qed.

    Definition Rbar_ge (x y : Rbar) := Rbar_le y x.

  Lemma Rbar_equiv_le_lt (f : Ts -> Rbar) (r:R) :
    pre_event_equiv (fun omega : Ts => Rbar_lt (f omega) r)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => 
                                      Rbar_le (f omega) 
                                              (Rbar_minus r  (/ (1 + INR n)))))).
  Proof.
    unfold pre_event_equiv, pre_union_of_collection.
    intros.
    split ; intros.
    - case_eq (f x); intros.
      + rewrite H0 in H; simpl in H.
        generalize (archimed_cor1 (r - r0)) ; intros.
        assert (r - r0 > 0) by lra.
        specialize (H1 H2).
        clear H2.
        destruct H1 as [N [HNf HN]].
        exists N. left.
        replace (1 + INR N) with (INR (S N)) by (apply S_O_plus_INR).
        assert (r0 < r - / INR N) by lra.
        eapply Rlt_trans ; eauto.
        unfold Rminus.
        apply Rplus_lt_compat_l, Ropp_lt_contravar.
        apply Rinv_lt_contravar.
        rewrite <-mult_INR. apply lt_0_INR ; lia.
        apply lt_INR ; lia.
      + rewrite H0 in H; now simpl in H.
      + exists (0%nat); now simpl.
   - destruct H.
     assert (0 < / INR (S x0)).
     { 
       apply Rinv_0_lt_compat.
       apply  lt_0_INR; lia.
     }
     replace (1 + INR x0) with (INR (S x0)) in H by (apply S_O_plus_INR).
     eapply Rbar_le_lt_trans.
     apply H.
     simpl; simpl in H0; lra.
   Qed.

  Lemma Rbar_sa_le_ge (f : Ts -> Rbar) :
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_le (f omega) r)) ->
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_ge (f omega) r)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => Rbar_ge (f omega) r)
                        (pre_event_complement (fun omega : Ts => Rbar_lt (f omega) r))).
    {
      intro x.
      unfold pre_event_complement.
      split; intros.
      - now apply Rbar_le_not_lt.
      - now apply Rbar_not_lt_le in H0.
    }
    destruct r.
    - rewrite H0.
      apply sa_complement.
      rewrite Rbar_equiv_le_lt.
      apply sa_countable_union.
      intros.
      apply H.
    - rewrite H0.
      apply sa_complement.
      assert (pre_event_equiv 
                (fun omega : Ts => Rbar_lt (f omega) p_infty)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => 
                                      Rbar_le (f omega) (INR n))))).
      { 
        intro x.
        unfold pre_union_of_collection.
        destruct (f x).
        - split; intros.
          + destruct (Rle_dec 0 r).
            * exists (Z.to_nat (up r)).
              rewrite INR_up_pos; try lra.
              simpl.
              left.
              apply archimed.
            * exists (0%nat).
              simpl; lra.
          + now simpl.
        - split; intros.
          + now simpl in H1.
          + destruct H1; now simpl in H1.
        - split; intros.
          + exists (0%nat); now simpl.
          + now simpl.
      }
      rewrite H1.
      apply sa_countable_union.
      intros.
      apply H.
    - assert (pre_event_equiv (fun omega : Ts => Rbar_ge (f omega) m_infty)
                              (fun omega => True)).
      {
        intro x.
        now simpl.
      }
      rewrite H1.
      apply sa_all.
   Qed.

  Lemma Rbar_sa_le_pt (f : Ts -> Rbar) :
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_le (f omega) r)) ->
    (forall (pt:Rbar), sa_sigma (fun omega : Ts => f omega = pt)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega = pt)
                        (pre_event_inter (fun omega : Ts => Rbar_le (f omega) pt)
                                     (fun omega : Ts => Rbar_ge (f omega) pt))).
    - unfold pre_event_equiv, pre_event_inter; intros.
      unfold Rbar_ge.
      split; intros.
      + rewrite H0; simpl.
        split; apply Rbar_le_refl.
      + destruct H0.
        now apply Rbar_le_antisym.
    - rewrite H0.
      apply sa_inter; trivial.
      now apply Rbar_sa_le_ge.
   Qed.

  End RbarBorel.

  Lemma Rbar_borel_singleton (c:Rbar) :
    sa_sigma (SigmaAlgebra:=Rbar_borel_sa) (pre_event_singleton c).
  Proof.
    apply Rbar_sa_le_pt.
    apply Rbar_borel_sa_preimage2; intros.
    destruct B.
    unfold event_preimage.
    simpl.
    apply s.
  Qed.

  Global Instance Rbar_borel_has_preimages : HasPreimageSingleton Rbar_borel_sa.
  Proof.
    red; intros.
    apply Rbar_sa_le_pt; intros.
    apply Rbar_borel_sa_preimage2; intros.
    now apply rv_preimage_sa.
  Qed.

Section RbarExpectation.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Local Open Scope prob.


  Class Rbar_PositiveRandomVariable
          (rv_X:Ts->Rbar) : Prop :=
    prv : forall (x:Ts), (Rbar_le 0 (rv_X x)).

  Definition Rbar_rv_le := pointwise_relation Ts Rbar_le.

  Definition Rbar_rvabs  (rv_X : Ts -> Rbar) := fun omega => Rbar_abs (rv_X omega).

  Global Instance Rbar_rvabs_prv
             (rv_X : Ts -> Rbar) :
      Rbar_PositiveRandomVariable (Rbar_rvabs rv_X).
    Proof.
      unfold Rbar_PositiveRandomVariable, Rbar_rvabs.
      intros.
      unfold Rbar_abs.
      match_destr.
      - simpl; apply Rabs_pos.
      - now simpl.
      - now simpl.
    Qed.

    Instance Rbar_Rabs_measurable (f : Ts -> Rbar) :
      RbarMeasurable f ->
      RbarMeasurable (Rbar_rvabs f).
    Proof.
      unfold RbarMeasurable, Rbar_rvabs.
      intros.
      assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_abs (f omega)) r)
                (pre_event_union
                   (pre_event_inter
                      (fun omega : Ts => Rbar_ge (f omega) 0 )
                      (fun omega : Ts => Rbar_le (f omega) r))
                   (pre_event_inter
                      (fun omega : Ts => Rbar_le (f omega) 0)
                      (fun omega : Ts => Rbar_ge (f omega) (Rbar_opp r))))).
      intro x.
      unfold pre_event_union, pre_event_inter, Rbar_abs.
      match_destr.
      - simpl; match_destr.
        + simpl.
          unfold Rabs.
          match_destr; lra.
        + simpl; lra.
        + simpl; lra.
      - simpl; match_destr; simpl; tauto.
      - simpl; match_destr; simpl; tauto.
      - rewrite H0.
        apply sa_union.
        + apply sa_inter; trivial.
          now apply Rbar_sa_le_ge.
        + apply sa_inter; trivial.
          now apply Rbar_sa_le_ge.
    Qed.

    Global Instance Rbar_rvabs_rv
           (rv_X : Ts -> Rbar)
           {rv : RandomVariable dom Rbar_borel_sa rv_X} :
      RandomVariable dom Rbar_borel_sa (Rbar_rvabs rv_X).
    Proof.
      unfold RandomVariable.
      apply Rbar_borel_sa_preimage2.
      apply Rbar_Rabs_measurable.
      unfold RbarMeasurable.
      generalize (Rbar_borel_sa_preimage2 rv_X); intros.
      destruct H.
      apply H0.
      apply rv.
    Qed.

  Global Instance Rbar_rv_le_pre : PreOrder Rbar_rv_le.
  Proof.
    unfold Rbar_rv_le.
    constructor; intros.
    - intros ??; apply Rbar_le_refl.
    - intros ??????.
      eapply Rbar_le_trans; eauto.
  Qed.

  Global Instance Rbar_rv_le_part : PartialOrder rv_eq Rbar_rv_le.
  Proof.
    intros ??.
    split; intros eqq.
    - repeat red.
      repeat red in eqq.
      split; intros ?; rewrite eqq; apply Rbar_le_refl.
    - destruct eqq as [le1 le2].
      intros y.
      specialize (le1 y).
      specialize (le2 y).
      now apply Rbar_le_antisym.
  Qed.

  Definition Rbar_Expectation_posRV
             (rv_X : Ts -> Rbar)
             {posrv:Rbar_PositiveRandomVariable rv_X} :  Rbar   :=
    (SimpleExpectationSup
       (fun
           (rvx2: Ts -> R)
           (rv2 : RandomVariable dom borel_sa rvx2)
           (srv2: SimpleRandomVariable rvx2) =>
           PositiveRandomVariable rvx2 /\ 
           (Rbar_rv_le rvx2 rv_X))).

  Lemma Rbar_Expectation_posRV_ext 
        {rv_X1 rv_X2 : Ts -> Rbar}
        (prv1:Rbar_PositiveRandomVariable rv_X1) 
        (prv2:Rbar_PositiveRandomVariable rv_X2):
    rv_eq rv_X1 rv_X2 ->
    Rbar_Expectation_posRV rv_X1 = Rbar_Expectation_posRV rv_X2.
  Proof.
    intros eqq.
    unfold Rbar_Expectation_posRV, SimpleExpectationSup.
    apply Lub_Rbar_eqset; intros x.
    split; intros [y [ yrv [ysrv [??]]]].
    - exists y; exists yrv; exists ysrv.
      rewrite <- eqq.
      auto.
    - exists y; exists yrv; exists ysrv.
      rewrite eqq.
      auto.
  Qed.

  Lemma Rbar_Expectation_posRV_pf_irrel 
        {rv_X: Ts -> R}
        (prv1 prv2:Rbar_PositiveRandomVariable rv_X) :
    Rbar_Expectation_posRV rv_X (posrv:=prv1) = Rbar_Expectation_posRV rv_X (posrv:=prv2).
  Proof.
    apply Rbar_Expectation_posRV_ext.
    reflexivity.
  Qed.

  Definition Rbar_max (x y : Rbar) : Rbar :=
    if Rbar_le_dec x y then y else x.

  Definition Rbar_pos_fun_part (f : Ts -> Rbar) : (Ts -> Rbar) :=
    fun x => Rbar_max (f x) 0.
    
  Definition Rbar_neg_fun_part (f : Ts -> Rbar) : (Ts -> Rbar) :=
    fun x => Rbar_max (Rbar_opp (f x)) 0.

  Global Instance Rbar_pos_fun_pos  (f : Ts -> Rbar)  :
    Rbar_PositiveRandomVariable (Rbar_pos_fun_part f).
  Proof.
    unfold Rbar_PositiveRandomVariable, Rbar_pos_fun_part, Rbar_max.
    intros.
    match_destr.
    - simpl; lra.
    - destruct (f x).
      + simpl in *; lra.
      + now simpl.
      + now simpl in n.
  Qed.

  Global Instance Rbar_neg_fun_pos  (f : Ts -> Rbar)  :
    Rbar_PositiveRandomVariable (Rbar_neg_fun_part f).
  Proof.
    unfold Rbar_PositiveRandomVariable, Rbar_neg_fun_part, Rbar_max.
    intros.
    match_destr.
    - simpl; lra.
    - destruct (f x).
      + simpl in *; lra.
      + now simpl in n.
      + now simpl.
  Qed.

  Definition Rbar_Expectation (rv_X : Ts -> Rbar) : option Rbar :=
    Rbar_minus' (Rbar_Expectation_posRV (Rbar_pos_fun_part rv_X))
                (Rbar_Expectation_posRV (Rbar_neg_fun_part rv_X)).

  Lemma Rbar_Expectation_ext {rv_X1 rv_X2 : Ts -> Rbar} :
    rv_eq rv_X1 rv_X2 ->
    Rbar_Expectation rv_X1 = Rbar_Expectation rv_X2.
  Proof.
    intros eqq.
    unfold Rbar_Expectation.
    f_equal.
    - apply Rbar_Expectation_posRV_ext.
      intros x; simpl.
      unfold Rbar_pos_fun_part.
      now rewrite eqq.
    - f_equal.
      apply Rbar_Expectation_posRV_ext.
      intros x; simpl.
      unfold Rbar_neg_fun_part.
      now rewrite eqq.
  Qed.

  Global Instance Rbar_Expectation_proper : Proper (rv_eq ==> eq) Rbar_Expectation.
  Proof.
    intros ???.
    now apply Rbar_Expectation_ext.
  Qed.

  Lemma Rbar_Expectation_posRV_le 
        (rv_X1 rv_X2 : Ts -> Rbar)
        {prv1 : Rbar_PositiveRandomVariable rv_X1}
        {prv2 : Rbar_PositiveRandomVariable rv_X2} :
    Rbar_rv_le rv_X1 rv_X2 ->
    Rbar_le (Rbar_Expectation_posRV rv_X1) (Rbar_Expectation_posRV rv_X2).
  Proof.
    intros.
    unfold Rbar_Expectation_posRV, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    refine (is_lub_Rbar_subset _ _ _ _ _ i0 i); intros.
    destruct H0 as [rvx [? [? [? ?]]]].
    exists rvx; exists x2; exists x3.
    split; trivial.
    destruct H0.
    split; trivial.
    intros ?.
    specialize (H a); specialize (H2 a).
    now apply Rbar_le_trans with (y := rv_X1 a).
  Qed.

  Lemma Rbar_Expectation_posRV_const (c : R) (nnc : 0 <= c) :
    (@Rbar_Expectation_posRV (const c) (prvconst _ nnc)) = c.
  Proof.
    unfold Rbar_Expectation_posRV, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    simpl in *.
    unfold is_lub_Rbar in i.
    unfold is_ub_Rbar in i.
    destruct i.
    specialize (H c).
    specialize (H0 c).
    cut_to H.
    cut_to H0.
    - apply Rbar_le_antisym; trivial.    
    - intros.
      destruct H1 as [? [? [? [? ?]]]].
      destruct H1.
      generalize (SimpleExpectation_le x1 (const c) H3); intros.
      rewrite H2 in H4.
      rewrite SimpleExpectation_const in H4.
      now simpl.
    - exists (const c).
      exists (rvconst _ _ c).
      exists (srvconst c).
      split; trivial; [| apply SimpleExpectation_const].
      split; [ apply (prvconst c nnc) |].
      unfold rv_le, const; intros ?.
      simpl.
      lra.
  Qed.

  Lemma Rbar_Expectation_posRV_const0 :
    (@Rbar_Expectation_posRV (const 0) (prvconst _ z_le_z)) = 0.
  Proof.
    apply Rbar_Expectation_posRV_const.
  Qed.

  Lemma Rbar_Expectation_posRV_pos
        (rv_X : Ts -> Rbar)
        {prv : Rbar_PositiveRandomVariable rv_X} :
    Rbar_le 0 (Rbar_Expectation_posRV rv_X).
  Proof.
    rewrite <- Rbar_Expectation_posRV_const0.
    apply Rbar_Expectation_posRV_le; trivial.
  Qed.

  Lemma is_finite_Rbar_Expectation_posRV_le
        (rv_X1 rv_X2 : Ts -> Rbar)
        {prv1 : Rbar_PositiveRandomVariable rv_X1}
        {prv2 : Rbar_PositiveRandomVariable rv_X2} :
    Rbar_rv_le rv_X1 rv_X2 ->
    is_finite (Rbar_Expectation_posRV rv_X2) ->
    is_finite (Rbar_Expectation_posRV rv_X1).
  Proof.
    intros.
    eapply bounded_is_finite with (b := (Rbar_Expectation_posRV rv_X2)).
    apply Rbar_Expectation_posRV_pos.
    rewrite H0.
    now apply Rbar_Expectation_posRV_le.
 Qed.

  Definition Rbar_rvlim (f : nat -> Ts -> R) : (Ts -> Rbar) :=
    (fun omega => Lim_seq (fun n => f n omega)).

(*
  Global Instance Rbar_rvlim_rv (f: nat -> Ts -> R)
         {rv : forall n, RandomVariable dom borel_sa (f n)} :
    RandomVariable dom Rbar_borel_sa (Rbar_rvlim f).
  Proof.
  Admitted.
 *)
  
  Global Instance Rbar_rvlim_prv
         (Xn : nat -> Ts -> R) 
         (posrv : forall n, PositiveRandomVariable (Xn n)) :
      Rbar_PositiveRandomVariable (Rbar_rvlim Xn).
    Proof.
      unfold Rbar_PositiveRandomVariable, Rbar_rvlim.
      unfold PositiveRandomVariable in posrv.
      intros.
      generalize (Lim_seq_le_loc (fun _ => 0) (fun n => Xn n x)); intros.
      rewrite Lim_seq_const in H.
      apply H.
      now exists 0%nat.
    Qed.

    Lemma Rbar_rvlim_pos_ge
        (Xn : nat -> Ts -> R)          
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      forall n, Rbar_rv_le (Xn n) (Rbar_rvlim Xn).
    Proof.
      intros.
      intro x.
      unfold Rbar_rvlim.
      generalize (Lim_seq_correct (fun n => Xn n x)) ; intros.
      cut_to H0.
      - destruct (Lim_seq (fun n => Xn n x)).
        + generalize (is_lim_seq_incr_compare _ _ H0); intros.
          apply H1.
          intros.
          apply H.
        + now simpl.
        + generalize (is_lim_seq_const 0); intros.
          unfold PositiveRandomVariable in Xn_pos.
          assert (forall n, 0 <= Xn n x); intros.
          apply Xn_pos.
          generalize (is_lim_seq_le _ _ _ _ H2 H1 H0); intros.
          now simpl in H3.
      - apply ex_lim_seq_incr.
        intros.
        apply H.
    Qed.
      
    Instance positive_Rbar_positive
             (rv_X : Ts -> R)
             (xpos : PositiveRandomVariable rv_X) :
      Rbar_PositiveRandomVariable rv_X.
    Proof.
      easy.
    Qed.

(*
    Instance rv_Rbar_rv
             (rv_X : Ts -> R)
             (rv : RandomVariable dom borel_sa rv_X) :
      RandomVariable dom Rbar_borel_sa rv_X.
    Proof.
      Admitted.

    Instance Rbar_rv_rv
             (rv_X : Ts -> R)
             (rv : RandomVariable dom Rbar_borel_sa rv_X) :
      RandomVariable dom borel_sa rv_X.
    Proof.
      Admitted.
*)

    Lemma Expectation_Rbar_Expectation
        (rv_X : Ts -> R)
        (xpos : PositiveRandomVariable rv_X) :
      Expectation_posRV rv_X = Rbar_Expectation_posRV rv_X.
    Proof.
      unfold Expectation_posRV, Rbar_Expectation_posRV.
      unfold SimpleExpectationSup, Lub_Rbar.
      repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
             end.
      destruct i; destruct i0.
      apply Rbar_le_antisym.
      - apply H0, H1.
      - apply H2, H.
    Qed.

    Lemma Expectation_rvlim_ge
        (Xn : nat -> Ts -> R)          
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      forall n, Rbar_le (Expectation_posRV (Xn n)) (Rbar_Expectation_posRV (Rbar_rvlim Xn)).
  Proof.
    intros.
    rewrite Expectation_Rbar_Expectation.
    unfold Rbar_Expectation_posRV, Expectation_posRV.
    unfold SimpleExpectationSup, Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    refine (is_lub_Rbar_subset _ _ _ _ _ i0 i); intros.
    destruct H0 as [rvx [? [? [? ?]]]].
    exists rvx; exists x2; exists x3.
    split; trivial.
    destruct H0.
    split; trivial.
    intros ?.
    specialize (H2 a).
    simpl in H2.
    apply Rbar_le_trans with (y := (Xn n a)); trivial.
    apply Rbar_rvlim_pos_ge; trivial.
  Qed.

  Lemma monotone_convergence_Ec2_Rbar_rvlim
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: PositiveRandomVariable cphi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) ((Rbar_rvlim Xn) omega)) ->
      (forall (n:nat), sa_sigma (fun (omega:Ts) => (Xn n omega) >= cphi omega)) /\
      pre_event_equiv (pre_union_of_collection (fun n => fun (omega:Ts) => (Xn n omega) >= cphi omega)) 
                  pre_Ω.
  Proof.
    intros.
    split.
    - intros x.
      now apply sigma_f_ge_g. 
    - assert (pre_event_equiv (pre_event_union (fun (omega : Ts) => Rbar_lt (cphi omega) ((Rbar_rvlim Xn) omega))
                                       (fun (omega : Ts) => cphi omega = 0))
                          pre_Ω).
      + intros x.
        unfold pre_Ω, pre_event_union.
        specialize (H0 x).
        tauto.
      + rewrite <- H1.
        intros x.
        specialize (H1 x).
        unfold pre_Ω in H1.
        split; [tauto | ].
        intros.
        unfold pre_union_of_collection; intros.
        unfold rvlim in H2.
        specialize (H0 x).
        destruct H0.
        * rewrite H0.
          exists (0%nat).
          apply Rle_ge, Xn_pos.
        * unfold Rbar_rvlim in H0.
          generalize (ex_lim_seq_incr (fun n => Xn n x)); intros.
          apply Lim_seq_correct in H3; [| intros; apply H].
          generalize (H3); intros.
          rewrite <- is_lim_seq_spec in H3.
          unfold is_lim_seq' in H3.
          match_case_in H3; intros.
          -- rewrite H5 in H3.
             specialize (posphi x).
             rewrite H5 in H0; simpl in H0.
             assert (0 < r - cphi x) by lra.
             specialize (H3 (mkposreal _ H6)).
             destruct H3.
             exists x0.
             specialize (H3 x0).
             simpl in H3.
             cut_to H3; [|lia].
             rewrite Rabs_left1 in H3; [lra | ].
             rewrite H5 in H4.
             generalize (is_lim_seq_incr_compare _ _ H4); intros.
             cut_to H7.
             specialize (H7 x0); lra.
             intros; apply H.
          -- rewrite H5 in H3.
             specialize (H3 (cphi x)).
             destruct H3.
             exists x0.
             specialize (H3 x0).
             left; apply H3; lia.
         -- rewrite H5 in H0.
            simpl in H0.
            specialize (posphi x).
            lra.
     Qed.

  Lemma monotone_convergence_E_phi_lim2_Rbar_rvlim
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: PositiveRandomVariable cphi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) ((Rbar_rvlim Xn) omega)) ->
      is_lim_seq (fun n => Expectation_posRV 
                          (rvmult cphi 
                                  (EventIndicator
                                     (fun omega => Rge_dec (Xn n omega) (cphi omega))))) 
                 (Expectation_posRV cphi).
  Proof.
    intros.
    rewrite <- (simple_Expectation_posRV cphi).
    assert (sa1:forall n,  sa_sigma (fun omega : Ts => Xn n omega >= cphi omega)).
    intros.
    now apply sigma_f_ge_g.
    assert (rv1:forall n, RandomVariable dom borel_sa (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
    {
      intros.
      apply rvmult_rv; trivial.
      now apply EventIndicator_pre_rv.
    } 
    
    apply (is_lim_seq_ext 
             (fun n => SimpleExpectation 
                      (rv:=rv1 n) (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega)))))).
    - intros.
      rewrite <- simple_Expectation_posRV with (rv:=rv1 n) (srv := (srvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))); trivial.
    - apply (is_lim_seq_ext 
               (fun (n:nat) =>
                  (list_sum (map (fun v => v * (ps_P (event_inter
                                                     (preimage_singleton cphi v)
                                                     (exist _ (fun omega => Xn n omega >= cphi omega) (sa1 n)))))
                                 (nodup Req_EM_T srv_vals))))).
      + intros.
        symmetry.
        erewrite <- simpleFunEventIndicator.
        eapply SimpleExpectation_pf_irrel.
      + unfold SimpleExpectation.
        generalize (is_lim_seq_list_sum
                      (map
                         (fun v : R => fun n => 
                                      v *
                                      ps_P
                                        (event_inter (preimage_singleton cphi v)
                                                   (exist _ (fun omega : Ts => Xn n omega >= cphi omega) (sa1 n))))
                       (nodup Req_EM_T srv_vals))
                    (map (fun v : R => v * ps_P (preimage_singleton cphi v))
                         (nodup Req_EM_T srv_vals)))
      ; intros HH.
      cut_to HH.
      * eapply is_lim_seq_ext; try eapply HH.
        intros; simpl.
        now rewrite map_map.
      * clear HH.
        rewrite map_map.
        rewrite <- Forall2_map.
        apply Forall2_refl_in.
        rewrite Forall_forall; intros.
        replace (Finite (x * ps_P (preimage_singleton cphi x))) with
            (Rbar_mult x (ps_P (preimage_singleton cphi x)))
          by reflexivity.
        apply is_lim_seq_scal_l.
        apply lim_prob.
        -- intros.
          apply event_inter_sub_proper; [reflexivity | ].
          intros xx.
          unfold rv_le in H.
          specialize (H n xx).
          simpl.
          lra.
        -- rewrite <- event_inter_countable_union_distr.
          assert (event_equiv (union_of_collection (fun (n : nat) => exist _ (fun (omega : Ts) => Xn n omega >= cphi omega) (sa1 n))) Ω).
          apply monotone_convergence_Ec2_Rbar_rvlim; trivial.
          ++ rewrite H2.
             apply event_inter_true_r.
  Qed.

  Lemma monotone_convergence0_cphi2_Rbar_rvlim
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: PositiveRandomVariable cphi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) ((Rbar_rvlim Xn) omega)) ->
      (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
      Rbar_le (Expectation_posRV cphi)
              (Lim_seq (fun n => real (Expectation_posRV (Xn n)))).
  Proof.
    intros.
    generalize (monotone_convergence_E_phi_lim2_Rbar_rvlim Xn cphi Xn_rv sphi phi_rv posphi Xn_pos H H0); intros.
    apply is_lim_seq_unique in H2.
    rewrite <- H2.
    apply Lim_seq_le_loc.
    unfold Hierarchy.eventually.
    exists (0%nat); intros.
    assert (PositiveRandomVariable
              (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
    now apply indicator_prod_pos.
    assert (RandomVariable _ borel_sa  (rvmult cphi
                                                  (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
    -  apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sigma_f_ge_g.
    - generalize (Expectation_posRV_le
                    (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))
                    (Xn n)); intros.
      cut_to H6.
      + rewrite <- H1 in H6.
        assert (is_finite (Expectation_posRV
                             (rvmult cphi
                                     (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega)))))).
        * assert (srv1:SimpleRandomVariable  (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
          {
            apply srvmult; trivial.
            apply EventIndicator_pre_srv.
          }
          rewrite <- simple_Expectation_posRV with (rv := H5) (srv := srv1).
          now unfold is_finite.
        * rewrite <- H7 in H6.
          now simpl in H6.
      + unfold rv_le; intros x.
        unfold rvmult, EventIndicator.
        destruct (Rge_dec (Xn n x) (cphi x)); [lra | ].
        unfold PositiveRandomVariable in Xn_pos.
        generalize (Xn_pos n x); lra.
  Qed.

  Lemma monotone_convergence0_Rbar_rvlim (c:R)
        (Xn : nat -> Ts -> R)
        (phi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posphi: PositiveRandomVariable phi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
      Rbar_rv_le phi (Rbar_rvlim Xn) ->
      0 < c < 1 ->
      Rbar_le (Rbar_mult c (Expectation_posRV phi))
              (Lim_seq (fun n => real (Expectation_posRV (Xn n)))).
  Proof.
    intros.
    pose (cphi := rvscale c phi).
    assert (PositiveRandomVariable cphi).
    - unfold PositiveRandomVariable, cphi, rvscale.
      unfold PositiveRandomVariable in posphi.
      intros.
      destruct H2.
      apply Rmult_le_pos; trivial.
      lra.
    - generalize (monotone_convergence0_cphi2_Rbar_rvlim Xn cphi Xn_rv 
                                             (srvscale c phi) (rvscale_rv _ c phi phi_rv) H3 Xn_pos).
      intros.
      cut_to H4; trivial.
      + destruct H2.
        rewrite <- (Expectation_posRV_scale (mkposreal c H2)); apply H4.
      + intros.
        unfold cphi, rvscale.
        destruct H2.
        unfold rv_le in H1.
        specialize (H1 omega).
        unfold PositiveRandomVariable in posphi.
        specialize (posphi omega).
        unfold Rle in posphi.
        destruct posphi.
        * right.
          assert (c * phi omega < phi omega).
          -- apply Rplus_lt_reg_l with (x := - (c * phi omega)).
             ring_simplify.
             replace (- c * phi omega + phi omega) with ((1-c)*phi omega) by lra.
             apply Rmult_lt_0_compat; [lra | trivial].
          -- now apply Rbar_lt_le_trans with (y := phi omega).
        * left.
          rewrite <- H6.
          lra.
  Qed.

  Lemma monotone_convergence00_Rbar_rvlim
        (Xn : nat -> Ts -> R)
        (phi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posphi: PositiveRandomVariable phi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :

    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
    Rbar_rv_le phi (Rbar_rvlim Xn) ->
    Rbar_le 
      (Expectation_posRV phi)
      (Lim_seq (fun n =>  real (Expectation_posRV (Xn n)))).
  Proof.
    assert (is_lim_seq (fun n => (1-/(2+INR n)) * (real (Expectation_posRV phi)))
                       (real (Expectation_posRV phi))).
    - replace (real (Expectation_posRV phi)) with 
          (1 * (real (Expectation_posRV phi))) at 1.
      + apply is_lim_seq_scal_r with (lu := Finite 1) (a := (Expectation_posRV phi)).
        replace (Finite 1) with (Rbar_minus (Finite 1) (Finite 0)) by 
            (simpl; rewrite Rbar_finite_eq; lra).
        apply is_lim_seq_minus'.
        * apply is_lim_seq_const.
        * replace (Finite 0) with (Rbar_inv p_infty).
          -- apply is_lim_seq_inv.
             ++ apply is_lim_seq_plus with (l1 := 2) (l2 := p_infty).
                apply is_lim_seq_const.
                apply is_lim_seq_INR.
                unfold is_Rbar_plus.
                now simpl.
             ++ discriminate.
          -- now simpl.
      + now simpl; rewrite Rmult_1_l.
    - intros.
      case_eq (Lim_seq (fun n : nat => Expectation_posRV (Xn n))); intros.
      + apply is_lim_seq_le with 
            (u:= (fun n => (1-/(2+INR n)) * (real (Expectation_posRV phi))))
            (v:= (fun _ : nat => r)).
        * intros.
          assert (0< 1 - /(2+INR n)).
          -- apply Rplus_lt_reg_l with (x := /(2+INR n)).
             ring_simplify.
             apply Rmult_lt_reg_l with (r := (2 + INR n)).
             ++ generalize (pos_INR n); lra.
             ++ rewrite <- Rinv_r_sym.
                ** generalize (pos_INR n); lra.
                ** apply Rgt_not_eq.
                   generalize (pos_INR n); lra.
          -- generalize (monotone_convergence0_Rbar_rvlim (mkposreal _ H4) Xn phi Xn_rv sphi phi_rv posphi Xn_pos); intros.
             cut_to H5; trivial.
             rewrite H3 in H5.
             assert (is_finite (Expectation_posRV phi)) by (now apply simple_expectation_real).
             ++ rewrite <- H6 in H5; now simpl in H5.
             ++ split; [trivial | simpl].
                apply Rplus_lt_reg_l with (x := -1).
                ring_simplify.
                apply Ropp_lt_gt_0_contravar.
                apply  Rinv_0_lt_compat.
                generalize (pos_INR n); lra.
        * assert (is_finite (Expectation_posRV phi))  by (now apply simple_expectation_real).
          rewrite <- H4.
          apply H.
        * apply is_lim_seq_const.
      + now destruct (Expectation_posRV phi).
      + now apply Lim_seq_Expectation_m_infty in H3.
  Qed.

    Lemma monotone_convergence_Rbar
        (Xn : nat -> Ts -> R)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
    Lim_seq (fun n => Expectation_posRV (Xn n)) = Rbar_Expectation_posRV (Rbar_rvlim Xn).
  Proof.
    intros.
    generalize (Rbar_rvlim_pos_ge Xn Xn_pos H); intros.
    generalize (Expectation_rvlim_ge Xn Xn_pos H); intros.
    generalize Expectation_posRV_le; intros.
    assert (forall (n:nat), (Rbar_le (Expectation_posRV (Xn n)) (Expectation_posRV (Xn (S n))))).
    + intros.
      apply H3; trivial.
    + pose (a := (Lim_seq (fun n : nat => Expectation_posRV (Xn n)))).
      
      generalize (Lim_seq_le_loc (fun n => Expectation_posRV (Xn n)) 
                                 (fun _ => Rbar_Expectation_posRV (Rbar_rvlim Xn))); intros.
        rewrite Lim_seq_const in H5.
        assert (Rbar_le (Rbar_Expectation_posRV (Rbar_rvlim Xn)) (Lim_seq (fun n : nat => Expectation_posRV (Xn n)))).
        * unfold Rbar_Expectation_posRV.
          unfold SimpleExpectationSup.
          {
            unfold Lub_Rbar.
            match goal with
              [|- context [proj1_sig ?x]] => destruct x
            end; simpl.
            destruct i as [i0 i1].
            apply i1.
            red; intros y [? [?[?[??]]]].
            subst.
            destruct H6.
            rewrite simple_Expectation_posRV with (prv := H6); trivial.

            
            apply monotone_convergence00_Rbar_rvlim; trivial.
          }
        * apply Rbar_le_antisym; trivial.
          generalize (Expectation_rvlim_ge Xn Xn_pos H); intros.
          case_eq (Rbar_Expectation_posRV (Rbar_rvlim Xn)); intros.
          ++ rewrite H8 in H5; simpl in H5.
             apply H5.
             exists (0%nat).
             intros.
             specialize (H7 n).
             rewrite H8 in H7.
             rewrite <- H0 in H7.
             apply H7.
          ++ now destruct (Lim_seq (fun n : nat => Expectation_posRV (Xn n))).
          ++ generalize (Rbar_Expectation_posRV_pos (Rbar_rvlim Xn)); intros.
             now rewrite H8 in H9.
  Qed.

End RbarExpectation.

  


