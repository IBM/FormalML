Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Coquelicot.
Require Import Classical_Prop.
Require Import Classical.
Require Import RealRandomVariable.

Require Import Utils.
Require Export SimpleExpectation Expectation.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R.

Require Import RandomVariableFinite.

Section RbarExpectation.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  Local Open Scope prob.

  Global Instance Rbar_rvabs_nnf
             (rv_X : Ts -> Rbar) :
      Rbar_NonnegativeFunction (Rbar_rvabs rv_X).
    Proof.
      unfold Rbar_NonnegativeFunction, Rbar_rvabs.
      intros.
      unfold Rbar_abs.
      match_destr.
      - simpl; apply Rabs_pos.
      - now simpl.
      - now simpl.
    Qed.

    Global Instance Rbar_rvabs_rv
           (rv_X : Ts -> Rbar)
           {rv : RandomVariable dom Rbar_borel_sa rv_X} :
      RandomVariable dom Rbar_borel_sa (Rbar_rvabs rv_X).
    Proof.
      apply Rbar_measurable_rv.
      apply Rbar_Rabs_measurable.
      now apply rv_Rbar_measurable.
    Qed.

    Global Instance Rbar_rvpower_rv (rv_X1 : Ts -> Rbar) (n:Rbar)
           {rvx1 : RandomVariable dom Rbar_borel_sa rv_X1} :
      RandomVariable dom Rbar_borel_sa (Rbar_rvpower rv_X1 n).
    Proof.
      apply Rbar_measurable_rv.
      apply Rbar_power_measurable.
      now apply rv_Rbar_measurable.
    Qed.

    Global Instance Rbar_rvplus_rv  (rv_X1 rv_X2 : Ts -> Rbar)
           {rvx1 : RandomVariable dom Rbar_borel_sa rv_X1} 
           {rvx2 : RandomVariable dom Rbar_borel_sa rv_X2} :      
    (forall x, ex_Rbar_plus (rv_X1 x) (rv_X2 x)) ->
      RandomVariable dom Rbar_borel_sa (Rbar_rvplus rv_X1 rv_X2).
   Proof.
     intros.
     apply Rbar_measurable_rv.
     apply rv_Rbar_measurable in rvx1.
     apply rv_Rbar_measurable in rvx2.     
     now apply Rbar_plus_measurable.
  Qed.

    Global Instance Rbar_rvplus_pos_rv  (rv_X1 rv_X2 : Ts -> Rbar)
           {rvx1 : RandomVariable dom Rbar_borel_sa rv_X1} 
           {rvx2 : RandomVariable dom Rbar_borel_sa rv_X2} 
           {nnfx1 : Rbar_NonnegativeFunction rv_X1}
           {nnfx2 : Rbar_NonnegativeFunction rv_X2} :
      RandomVariable dom Rbar_borel_sa (Rbar_rvplus rv_X1 rv_X2).
    Proof.
      apply Rbar_rvplus_rv; trivial.
      intros.
      specialize (nnfx1 x); specialize (nnfx2 x).
      now apply ex_Rbar_plus_pos.
    Qed.

  Definition Rbar_NonnegExpectation
             (rv_X : Ts -> Rbar)
             {pofrf:Rbar_NonnegativeFunction rv_X} :  Rbar   :=
    (SimpleExpectationSup
       (fun
           (rvx2: Ts -> R)
           (rv2 : RandomVariable dom borel_sa rvx2)
           (frf2: FiniteRangeFunction rvx2) =>
           NonnegativeFunction rvx2 /\ 
           (Rbar_rv_le rvx2 rv_X))).

  Lemma Rbar_NonnegExpectation_ext 
        {rv_X1 rv_X2 : Ts -> Rbar}
        (nnf1:Rbar_NonnegativeFunction rv_X1) 
        (nnf2:Rbar_NonnegativeFunction rv_X2):
    rv_eq rv_X1 rv_X2 ->
    Rbar_NonnegExpectation rv_X1 = Rbar_NonnegExpectation rv_X2.
  Proof.
    intros eqq.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup.
    apply Lub_Rbar_eqset; intros x.
    split; intros [y [ yrv [yfrf [??]]]].
    - exists y; exists yrv; exists yfrf.
      rewrite <- eqq.
      auto.
    - exists y; exists yrv; exists yfrf.
      rewrite eqq.
      auto.
  Qed.

  Lemma Rbar_NonnegExpectation_pf_irrel 
        {rv_X: Ts -> R}
        (nnf1 nnf2:Rbar_NonnegativeFunction rv_X) :
    Rbar_NonnegExpectation rv_X (pofrf:=nnf1) = Rbar_NonnegExpectation rv_X (pofrf:=nnf2).
  Proof.
    apply Rbar_NonnegExpectation_ext.
    reflexivity.
  Qed.

  Definition Rbar_max (x y : Rbar) : Rbar :=
    if Rbar_le_dec x y then y else x.

  Definition Rbar_pos_fun_part (f : Ts -> Rbar) : (Ts -> Rbar) :=
    fun x => Rbar_max (f x) 0.
    
  Definition Rbar_neg_fun_part (f : Ts -> Rbar) : (Ts -> Rbar) :=
    fun x => Rbar_max (Rbar_opp (f x)) 0.

  Program Definition Rbar_neg_fun_part_alt (f : Ts -> Rbar) : (Ts -> Rbar) :=
    Rbar_pos_fun_part (fun x => Rbar_opp (f x)).

  Lemma Rbar_neg_fun_part_alt_rveq (f : Ts -> Rbar) :
    rv_eq (Rbar_neg_fun_part f) (Rbar_neg_fun_part_alt f).
  Proof.
    easy.
  Qed.

  Instance Rbar_opp_measurable (f : Ts -> Rbar) :
    RbarMeasurable f ->
    RbarMeasurable (fun x => Rbar_opp (f x)).
  Proof.
    unfold RbarMeasurable; intros.
    assert (pre_event_equiv
              (fun omega : Ts => Rbar_le (Rbar_opp (f omega)) r)
              (fun omega : Ts => Rbar_ge (f omega) (Rbar_opp r))).
    {
      intro x.
      unfold Rbar_ge.
      rewrite <- Rbar_opp_le.
      now rewrite Rbar_opp_involutive.
    }
    rewrite H0.
    now apply Rbar_sa_le_ge.
  Qed.

  Global Instance Rbar_pos_fun_part_measurable (f : Ts -> Rbar) :
    RbarMeasurable f ->
    RbarMeasurable (Rbar_pos_fun_part f).
  Proof.
    unfold RbarMeasurable, Rbar_pos_fun_part; intros.
    assert (pre_event_equiv
              (fun omega : Ts => Rbar_le (Rbar_max (f omega) 0) r)
              (pre_event_union
                 (pre_event_inter
                    (fun omega : Ts => Rbar_ge (f omega) 0 )
                    (fun omega : Ts => Rbar_le (f omega) r))
                 (pre_event_inter
                    (fun omega : Ts => Rbar_le (f omega) 0)
                    (fun omega : Ts => Rbar_le 0 r)))).
    {    
      intro x.
      unfold pre_event_union, pre_event_inter.
      unfold Rbar_max.
      match_destr.
      - split; intros.
        + tauto.
        + destruct H0.
          * destruct H0.
            unfold Rbar_ge in H0.
            generalize (Rbar_le_antisym _ _ r0 H0); intros.
            now rewrite H2 in H1.
          * tauto.
      - split; intros.
        + apply Rbar_not_le_lt in n.
          left.
          assert (Rbar_ge (f x) 0) by now apply Rbar_lt_le.
          tauto.
        + destruct H0.
          * tauto.
          * destruct H0.
            eapply Rbar_le_trans.
            apply H0.
            apply H1.
    }
    rewrite H0.
    apply sa_union.
    - apply sa_inter; trivial.
      now apply Rbar_sa_le_ge.
    - apply sa_inter; trivial.
      destruct (Rbar_le_dec 0 r).
      + assert (pre_event_equiv
                  (fun _ : Ts => Rbar_le 0 r)
                  (fun _ => True)) by easy.
        rewrite H1.
        apply sa_all.
      + assert (pre_event_equiv
                  (fun _ : Ts => Rbar_le 0 r)
                  (fun _ => False)) by easy.
        rewrite H1.
        apply sa_none.
   Qed.

  Instance Rbar_neg_fun_part_measurable (f : Ts -> Rbar) :
      RbarMeasurable f ->
      RbarMeasurable (Rbar_neg_fun_part f).
    Proof.
      unfold RbarMeasurable; intros.
      assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_neg_fun_part f omega) r)
                (fun omega : Ts => Rbar_le (Rbar_pos_fun_part 
                                              (fun x => Rbar_opp (f x)) omega) r)).
      {
        intro x.
        now rewrite Rbar_neg_fun_part_alt_rveq.
      }
      rewrite H0.
      apply Rbar_pos_fun_part_measurable.
      now apply Rbar_opp_measurable.
    Qed.

  Global Instance Rbar_pos_fun_part_rv (f : Ts -> Rbar) 
         (rv : RandomVariable dom Rbar_borel_sa f) :
    RandomVariable dom Rbar_borel_sa (Rbar_pos_fun_part f).
  Proof.
    apply Rbar_measurable_rv.
    apply rv_Rbar_measurable in rv.
    typeclasses eauto.
  Qed.

  Global Instance Rbar_neg_fun_part_rv (f : Ts -> Rbar) 
         (rv : RandomVariable dom Rbar_borel_sa f) :
    RandomVariable dom Rbar_borel_sa (Rbar_neg_fun_part f).
  Proof.
    apply Rbar_measurable_rv.
    apply rv_Rbar_measurable in rv.
    typeclasses eauto.
  Qed.

  Global Instance Rbar_pos_fun_pos  (f : Ts -> Rbar)  :
    Rbar_NonnegativeFunction (Rbar_pos_fun_part f).
  Proof.
    unfold Rbar_NonnegativeFunction, Rbar_pos_fun_part, Rbar_max.
    intros.
    match_destr.
    - simpl; lra.
    - destruct (f x).
      + simpl in *; lra.
      + now simpl.
      + now simpl in n.
  Qed.

  Global Instance Rbar_neg_fun_pos  (f : Ts -> Rbar)  :
    Rbar_NonnegativeFunction (Rbar_neg_fun_part f).
  Proof.
    unfold Rbar_NonnegativeFunction, Rbar_neg_fun_part, Rbar_max.
    intros.
    match_destr.
    - simpl; lra.
    - destruct (f x).
      + simpl in *; lra.
      + now simpl in n.
      + now simpl.
  Qed.

  Definition Rbar_Expectation (rv_X : Ts -> Rbar) : option Rbar :=
    Rbar_minus' (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X))
                (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X)).

  Lemma Rbar_Expectation_ext {rv_X1 rv_X2 : Ts -> Rbar} :
    rv_eq rv_X1 rv_X2 ->
    Rbar_Expectation rv_X1 = Rbar_Expectation rv_X2.
  Proof.
    intros eqq.
    unfold Rbar_Expectation.
    f_equal.
    - apply Rbar_NonnegExpectation_ext.
      intros x; simpl.
      unfold Rbar_pos_fun_part.
      now rewrite eqq.
    - f_equal.
      apply Rbar_NonnegExpectation_ext.
      intros x; simpl.
      unfold Rbar_neg_fun_part.
      now rewrite eqq.
  Qed.

  Global Instance Rbar_Expectation_proper : Proper (rv_eq ==> eq) Rbar_Expectation.
  Proof.
    intros ???.
    now apply Rbar_Expectation_ext.
  Qed.

  Lemma Rbar_NonnegExpectation_le 
        (rv_X1 rv_X2 : Ts -> Rbar)
        {nnf1 : Rbar_NonnegativeFunction rv_X1}
        {nnf2 : Rbar_NonnegativeFunction rv_X2} :
    Rbar_rv_le rv_X1 rv_X2 ->
    Rbar_le (Rbar_NonnegExpectation rv_X1) (Rbar_NonnegExpectation rv_X2).
  Proof.
    intros.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup.
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

  Lemma Rbar_NonnegExpectation_const (c : R) (nnc : 0 <= c) :
    (@Rbar_NonnegExpectation (const c) (nnfconst _ nnc)) = c.
  Proof.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup.
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
      exists (frfconst c).
      split; trivial; [| apply SimpleExpectation_const].
      split; [ apply (nnfconst c nnc) |].
      unfold rv_le, const; intros ?.
      simpl.
      lra.
  Qed.

  Lemma Rbar_NonnegExpectation_const0 :
    (@Rbar_NonnegExpectation (const 0) (nnfconst _ z_le_z)) = 0.
  Proof.
    apply Rbar_NonnegExpectation_const.
  Qed.

  Lemma Rbar_NonnegExpectation_pos
        (rv_X : Ts -> Rbar)
        {nnf : Rbar_NonnegativeFunction rv_X} :
    Rbar_le 0 (Rbar_NonnegExpectation rv_X).
  Proof.
    rewrite <- Rbar_NonnegExpectation_const0.
    apply Rbar_NonnegExpectation_le; trivial.
  Qed.

  Lemma is_finite_Rbar_NonnegExpectation_le
        (rv_X1 rv_X2 : Ts -> Rbar)
        {nnf1 : Rbar_NonnegativeFunction rv_X1}
        {nnf2 : Rbar_NonnegativeFunction rv_X2} :
    Rbar_rv_le rv_X1 rv_X2 ->
    is_finite (Rbar_NonnegExpectation rv_X2) ->
    is_finite (Rbar_NonnegExpectation rv_X1).
  Proof.
    intros.
    eapply bounded_is_finite with (b := (Rbar_NonnegExpectation rv_X2)).
    apply Rbar_NonnegExpectation_pos.
    rewrite H0.
    now apply Rbar_NonnegExpectation_le.
 Qed.

      
    Lemma Expectation_Rbar_Expectation
        (rv_X : Ts -> R)
        (xpos : NonnegativeFunction rv_X) :
      NonnegExpectation rv_X = Rbar_NonnegExpectation rv_X.
    Proof.
      unfold NonnegExpectation, Rbar_NonnegExpectation.
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
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      forall n, Rbar_le (NonnegExpectation (Xn n)) (Rbar_NonnegExpectation (Rbar_rvlim Xn)).
  Proof.
    intros.
    rewrite Expectation_Rbar_Expectation.
    unfold Rbar_NonnegExpectation, NonnegExpectation.
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
        (sphi : FiniteRangeFunction cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: NonnegativeFunction cphi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
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
        (sphi : FiniteRangeFunction cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: NonnegativeFunction cphi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) ((Rbar_rvlim Xn) omega)) ->
      is_lim_seq (fun n => NonnegExpectation 
                          (rvmult cphi 
                                  (EventIndicator
                                     (fun omega => Rge_dec (Xn n omega) (cphi omega))))) 
                 (NonnegExpectation cphi).
  Proof.
    intros.
    rewrite <- (simple_NonnegExpectation cphi).
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
      rewrite <- simple_NonnegExpectation with (rv:=rv1 n) (frf := (frfmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))); trivial.
    - apply (is_lim_seq_ext 
               (fun (n:nat) =>
                  (list_sum (map (fun v => v * (ps_P (event_inter
                                                     (preimage_singleton cphi v)
                                                     (exist _ (fun omega => Xn n omega >= cphi omega) (sa1 n)))))
                                 (nodup Req_EM_T frf_vals))))).
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
                       (nodup Req_EM_T frf_vals))
                    (map (fun v : R => v * ps_P (preimage_singleton cphi v))
                         (nodup Req_EM_T frf_vals)))
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
        (sphi : FiniteRangeFunction cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: NonnegativeFunction cphi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) ((Rbar_rvlim Xn) omega)) ->
      (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
      Rbar_le (NonnegExpectation cphi)
              (Lim_seq (fun n => real (NonnegExpectation (Xn n)))).
  Proof.
    intros.
    generalize (monotone_convergence_E_phi_lim2_Rbar_rvlim Xn cphi Xn_rv sphi phi_rv posphi Xn_pos H H0); intros.
    apply is_lim_seq_unique in H2.
    rewrite <- H2.
    apply Lim_seq_le_loc.
    unfold Hierarchy.eventually.
    exists (0%nat); intros.
    assert (NonnegativeFunction
              (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
    now apply indicator_prod_pos.
    assert (RandomVariable _ borel_sa  (rvmult cphi
                                                  (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
    -  apply rvmult_rv; trivial.
      apply EventIndicator_pre_rv.
      now apply sigma_f_ge_g.
    - generalize (NonnegExpectation_le
                    (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))
                    (Xn n)); intros.
      cut_to H6.
      + rewrite <- H1 in H6.
        assert (is_finite (NonnegExpectation
                             (rvmult cphi
                                     (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega)))))).
        * assert (frf1:FiniteRangeFunction  (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
          {
            apply frfmult; trivial.
            apply EventIndicator_pre_frf.
          }
          rewrite <- simple_NonnegExpectation with (rv := H5) (frf := frf1).
          now unfold is_finite.
        * rewrite <- H7 in H6.
          now simpl in H6.
      + unfold rv_le; intros x.
        unfold rvmult, EventIndicator.
        destruct (Rge_dec (Xn n x) (cphi x)); [lra | ].
        unfold NonnegativeFunction in Xn_pos.
        generalize (Xn_pos n x); lra.
  Qed.

  Lemma monotone_convergence0_Rbar_rvlim (c:R)
        (Xn : nat -> Ts -> R)
        (phi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : FiniteRangeFunction phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posphi: NonnegativeFunction phi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
      Rbar_rv_le phi (Rbar_rvlim Xn) ->
      0 < c < 1 ->
      Rbar_le (Rbar_mult c (NonnegExpectation phi))
              (Lim_seq (fun n => real (NonnegExpectation (Xn n)))).
  Proof.
    intros.
    pose (cphi := rvscale c phi).
    assert (NonnegativeFunction cphi).
    - unfold NonnegativeFunction, cphi, rvscale.
      unfold NonnegativeFunction in posphi.
      intros.
      destruct H2.
      apply Rmult_le_pos; trivial.
      lra.
    - generalize (monotone_convergence0_cphi2_Rbar_rvlim Xn cphi Xn_rv 
                                             (frfscale c phi) (rvscale_rv _ c phi phi_rv) H3 Xn_pos).
      intros.
      cut_to H4; trivial.
      + destruct H2.
        rewrite <- (NonnegExpectation_scale (mkposreal c H2)); apply H4.
      + intros.
        unfold cphi, rvscale.
        destruct H2.
        unfold rv_le in H1.
        specialize (H1 omega).
        unfold NonnegativeFunction in posphi.
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
        (sphi : FiniteRangeFunction phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posphi: NonnegativeFunction phi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :

    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    Rbar_rv_le phi (Rbar_rvlim Xn) ->
    Rbar_le 
      (NonnegExpectation phi)
      (Lim_seq (fun n =>  real (NonnegExpectation (Xn n)))).
  Proof.
    assert (is_lim_seq (fun n => (1-/(2+INR n)) * (real (NonnegExpectation phi)))
                       (real (NonnegExpectation phi))).
    - replace (real (NonnegExpectation phi)) with 
          (1 * (real (NonnegExpectation phi))) at 1.
      + apply is_lim_seq_scal_r with (lu := Finite 1) (a := (NonnegExpectation phi)).
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
      case_eq (Lim_seq (fun n : nat => NonnegExpectation (Xn n))); intros.
      + apply is_lim_seq_le with 
            (u:= (fun n => (1-/(2+INR n)) * (real (NonnegExpectation phi))))
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
             assert (is_finite (NonnegExpectation phi)) by (now apply simple_expectation_real).
             ++ rewrite <- H6 in H5; now simpl in H5.
             ++ split; [trivial | simpl].
                apply Rplus_lt_reg_l with (x := -1).
                ring_simplify.
                apply Ropp_lt_gt_0_contravar.
                apply  Rinv_0_lt_compat.
                generalize (pos_INR n); lra.
        * assert (is_finite (NonnegExpectation phi))  by (now apply simple_expectation_real).
          rewrite <- H4.
          apply H.
        * apply is_lim_seq_const.
      + now destruct (NonnegExpectation phi).
      + now apply Lim_seq_Expectation_m_infty in H3.
  Qed.

    Lemma monotone_convergence_Rbar
        (Xn : nat -> Ts -> R)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    Lim_seq (fun n => NonnegExpectation (Xn n)) = Rbar_NonnegExpectation (Rbar_rvlim Xn).
  Proof.
    intros.
    generalize (Rbar_rvlim_pos_ge Xn Xn_pos H); intros.
    generalize (Expectation_rvlim_ge Xn Xn_pos H); intros.
    generalize NonnegExpectation_le; intros.
    assert (forall (n:nat), (Rbar_le (NonnegExpectation (Xn n)) (NonnegExpectation (Xn (S n))))).
    + intros.
      apply H3; trivial.
    + pose (a := (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
      
      generalize (Lim_seq_le_loc (fun n => NonnegExpectation (Xn n)) 
                                 (fun _ => Rbar_NonnegExpectation (Rbar_rvlim Xn))); intros.
        rewrite Lim_seq_const in H5.
        assert (Rbar_le (Rbar_NonnegExpectation (Rbar_rvlim Xn)) (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
        * unfold Rbar_NonnegExpectation.
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
            rewrite simple_NonnegExpectation with (nnf := H6); trivial.

            
            apply monotone_convergence00_Rbar_rvlim; trivial.
          }
        * apply Rbar_le_antisym; trivial.
          generalize (Expectation_rvlim_ge Xn Xn_pos H); intros.
          case_eq (Rbar_NonnegExpectation (Rbar_rvlim Xn)); intros.
          ++ rewrite H8 in H5; simpl in H5.
             apply H5.
             exists (0%nat).
             intros.
             specialize (H7 n).
             rewrite H8 in H7.
             rewrite <- H0 in H7.
             apply H7.
          ++ now destruct (Lim_seq (fun n : nat => NonnegExpectation (Xn n))).
          ++ generalize (Rbar_NonnegExpectation_pos (Rbar_rvlim Xn)); intros.
             now rewrite H8 in H9.
  Qed.

  Lemma Rbar_monotone_convergence
        (X : Ts -> Rbar )
        (Xn : nat -> Ts -> R)
        (rvx : RandomVariable dom Rbar_borel_sa X)
        (posX: Rbar_NonnegativeFunction X) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    (forall (n:nat), Rbar_rv_le (Xn n) X) ->
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
    Lim_seq (fun n => NonnegExpectation (Xn n)) =  (Rbar_NonnegExpectation X).
  Proof.
    generalize Rbar_NonnegExpectation_le; intros.
    assert (forall (n:nat), (Rbar_le (Rbar_NonnegExpectation (Xn n)) (Rbar_NonnegExpectation X))).
    - intros.
      apply H; trivial.
    - assert (forall (n:nat), (Rbar_le (NonnegExpectation (Xn n)) (NonnegExpectation (Xn (S n))))).
      {
        generalize NonnegExpectation_le; intros.    
        apply H5; trivial.
      }
      + pose (a := (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
        generalize (Lim_seq_le_loc (fun n => NonnegExpectation (Xn n)) 
                                   (fun _ => Rbar_NonnegExpectation X)); intros.
        rewrite Lim_seq_const in H6.
        assert (Rbar_le (Rbar_NonnegExpectation X) (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
        * unfold Rbar_NonnegExpectation.
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
            unfold BoundedNonnegativeFunction in H7.
            destruct H7.
            rewrite simple_NonnegExpectation with (nnf := H7); trivial.
            apply monotone_convergence00 with (X0 := X); trivial.
          }
        * apply Rbar_le_antisym; trivial.
          case_eq (Rbar_NonnegExpectation X); intros.
          ++ rewrite H8 in H6; simpl in H6.
             apply H6.
             unfold Hierarchy.eventually.   
             exists (0%nat).
             intros.
             specialize (H (Xn n) X (Xn_pos n) posX (H0 n)).
             rewrite <- (H2 n) in H.
             rewrite H8 in H.
             now simpl in H.
          ++ now destruct (Lim_seq (fun n : nat => NonnegExpectation (Xn n))).
          ++ generalize (Rbar_NonnegExpectation_pos X); intros.
             now rewrite H8 in H9.
  Qed.

  Lemma Rbar_NonnegExpectation_plus
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2}
        {nnf1:Rbar_NonnegativeFunction rv_X1}
        {nnf2:Rbar_NonnegativeFunction rv_X2} :     
    Rbar_NonnegExpectation (Rbar_rvplus rv_X1 rv_X2) =
    Rbar_plus (Rbar_NonnegExpectation rv_X1) (Rbar_NonnegExpectation rv_X2).
  Proof.
    generalize (simple_approx_lim_seq rv_X1 nnf1); intros.
    generalize (simple_approx_lim_seq rv_X2 nnf2); intros.
    generalize (simple_approx_rv rv_X1); intro apx_rv1.
    generalize (simple_approx_rv rv_X2); intro apx_rv2.
    generalize (simple_approx_pofrf rv_X1); intro apx_nnf1.
    generalize (simple_approx_pofrf rv_X2); intro apx_nnf2.     
    generalize (simple_approx_frf rv_X1); intro apx_frf1.
    generalize (simple_approx_frf rv_X2); intro apx_frf2.
    generalize (simple_approx_le rv_X1 nnf1); intro apx_le1.
    generalize (simple_approx_le rv_X2 nnf2); intro apx_le2. 
    generalize (simple_approx_increasing rv_X1 nnf1); intro apx_inc1.
    generalize (simple_approx_increasing rv_X2 nnf2); intro apx_inc2.
    
    generalize (Rbar_monotone_convergence rv_X1 (simple_approx rv_X1) rv1 nnf1 apx_rv1 apx_nnf1 apx_le1 apx_inc1 (fun n => simple_expectation_real (simple_approx rv_X1 n))); intros.
    generalize (Rbar_monotone_convergence rv_X2 (simple_approx rv_X2) rv2 nnf2 apx_rv2 apx_nnf2 apx_le2 apx_inc2 (fun n => simple_expectation_real (simple_approx rv_X2 n))); intros.
    cut_to H1; trivial.
    cut_to H2; trivial.
    generalize (fun n => rvplus_rv _ (simple_approx rv_X1 n) (simple_approx rv_X2 n)); intros.
    generalize (fun n => rvplus_nnf (simple_approx rv_X1 n) (simple_approx rv_X2 n)); intros.     
    generalize (fun n => simple_expectation_real (simple_approx rv_X1 n)); intros apx_fin1.
    generalize (fun n => simple_expectation_real (simple_approx rv_X2 n)); intros apx_fin2.     
    generalize (Rbar_monotone_convergence (Rbar_rvplus rv_X1 rv_X2) 
                                     (fun n => rvplus (simple_approx rv_X1 n)
                                                   (simple_approx rv_X2 n))
                                         (Rbar_rvplus_pos_rv rv_X1 rv_X2)
                                         (pos_Rbar_plus rv_X1 rv_X2) H3 H4); intros.
    cut_to H5; trivial.
    - rewrite Lim_seq_ext with (v := fun n => (NonnegExpectation (simple_approx rv_X1 n)) +
                                           (NonnegExpectation (simple_approx rv_X2 n)))
        in H5.
      + rewrite Lim_seq_plus in H5.
        * rewrite H1 in H5.
          rewrite H2 in H5.
          now symmetry.
        * apply ex_lim_seq_incr.
          intros.
          generalize (NonnegExpectation_le (simple_approx rv_X1 n) (simple_approx rv_X1 (S n)) (apx_inc1 n)); intros.
          rewrite <- apx_fin1 in H6; simpl in H6.
          now rewrite <- apx_fin1 in H6; simpl in H6.           
        * apply ex_lim_seq_incr.
          intros.
          generalize (NonnegExpectation_le (simple_approx rv_X2 n) (simple_approx rv_X2 (S n)) (apx_inc2 n)); intros.
          rewrite <- apx_fin2 in H6; simpl in H6.
          now rewrite <- apx_fin2 in H6; simpl in H6.           
        * unfold ex_Rbar_plus, Rbar_plus'.
          match_case; intros.
          match_case_in H6; intros.
          -- rewrite H7 in H6.
             match_case_in H6; intros.
             ++ rewrite H8 in H6; congruence.
             ++ rewrite H8 in H6; congruence.
             ++ now apply Lim_seq_Expectation_m_infty in H8.
          -- rewrite H7 in H6.
             match_case_in H6; intros.
             ++ rewrite H8 in H6; congruence.
             ++ rewrite H8 in H6; congruence.                 
             ++ now apply Lim_seq_Expectation_m_infty in H8.
          -- rewrite H7 in H6.
             now apply Lim_seq_Expectation_m_infty in H7.
      + intros.
        rewrite <- simple_NonnegExpectation with (rv:=rvplus_rv _ _ _) (frf := frfplus (simple_approx rv_X1 n) (simple_approx rv_X2 n)); trivial.
        rewrite <- sumSimpleExpectation; trivial.
        rewrite <- simple_NonnegExpectation with (rv:=apx_rv1 n) (frf := apx_frf1 n); trivial.
        rewrite <- simple_NonnegExpectation with (rv:=apx_rv2 n) (frf := apx_frf2 n); trivial.
    - unfold rv_le, rvplus.
      intros n x.
      specialize (apx_le1 n x).
      specialize (apx_le2 n x).
      replace (Finite (simple_approx rv_X1 n x + simple_approx rv_X2 n x)) with
          (Rbar_plus (simple_approx rv_X1 n x) (simple_approx rv_X2 n x)) by now simpl.
      now apply Rbar_plus_le_compat.
    - unfold rv_le, rvplus.
      intros n x.
      specialize (apx_inc1 n x).
      specialize (apx_inc2 n x).       
      lra.
    - intros.
      apply simple_expectation_real; trivial.
      apply frfplus; trivial.
    - intros.
      unfold Rbar_rvplus.
      apply is_lim_seq_plus with (l1 := rv_X1 omega) (l2 := rv_X2 omega); trivial.
      apply Rbar_plus_correct.
      generalize (nnf1 omega); intros.
      generalize (nnf2 omega); intros.
      now apply ex_Rbar_plus_pos.
  Qed.

  Lemma Rbar_pos_fun_part_pos (rv_X : Ts -> Rbar) 
        {nnf : Rbar_NonnegativeFunction rv_X} :
    rv_eq rv_X (Rbar_pos_fun_part rv_X).
  Proof.
    unfold Rbar_pos_fun_part.
    intro x.
    simpl.
    specialize (nnf x).
    unfold Rbar_max.
    match_destr.
    now apply Rbar_le_antisym.
  Qed.

  Lemma Rbar_neg_fun_part_pos (rv_X : Ts -> Rbar) 
        {nnf : Rbar_NonnegativeFunction rv_X} :
    rv_eq (const (Finite 0)) (Rbar_neg_fun_part rv_X).
  Proof.
    unfold Rbar_neg_fun_part, const.
    intro x.
    simpl.
    specialize (nnf x).
    unfold Rbar_max, Rbar_opp.
    match_destr.
    match_destr.
    - simpl in *; lra.
    - tauto.
    - tauto.
  Qed.

  Lemma Rbar_Expectation_pos_pofrf (rv_X : Ts -> Rbar) 
        {nnf : Rbar_NonnegativeFunction rv_X} :
    Rbar_Expectation rv_X = Some (Rbar_NonnegExpectation rv_X).
  Proof.
    unfold Rbar_Expectation.
    replace (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X)) with (Rbar_NonnegExpectation rv_X).
    - replace (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X)) with (Finite 0).
      + unfold Rbar_minus', Rbar_plus', Rbar_opp.
        match_destr.
        f_equal; apply Rbar_finite_eq; lra.
      + generalize (Rbar_neg_fun_part_pos rv_X); intros.
        assert (Rbar_NonnegativeFunction (fun (x : Ts) => 0)).
        {
          intro x.
          now simpl.
        }
        rewrite Rbar_NonnegExpectation_ext with (nnf2 := H0).
        symmetry.
        * assert (0 <= 0) by lra.
          apply (Rbar_NonnegExpectation_const _ H1).
        * now symmetry.
    - apply Rbar_NonnegExpectation_ext; trivial.
      now apply Rbar_pos_fun_part_pos.
  Qed.

  Lemma Rbar_Expectation_zero_pos 
        (X : Ts -> Rbar)
        {rv : RandomVariable dom Rbar_borel_sa X}
        {pofrf : Rbar_NonnegativeFunction X} :
    Rbar_Expectation X = Some (Finite 0) ->
    ps_P (preimage_singleton (has_pre := Rbar_borel_has_preimages) X (Finite 0)) = 1.
  Proof.
    rewrite Rbar_Expectation_pos_pofrf with (nnf := pofrf); intros.
    inversion H.

    generalize (simple_approx_lim_seq X pofrf); intros.
    generalize (simple_approx_rv X); intro apx_rv1.
    generalize (simple_approx_pofrf X); intro apx_nnf1.
    generalize (simple_approx_frf X); intro apx_frf1.
    generalize (simple_approx_le X pofrf); intro apx_le1.
    generalize (simple_approx_increasing X pofrf); intro apx_inc1.
    generalize (Rbar_monotone_convergence X (simple_approx X) rv pofrf apx_rv1 apx_nnf1 apx_le1 apx_inc1 (fun n => simple_expectation_real (simple_approx X n)) H0); intros.

    assert (forall n:nat, NonnegExpectation (simple_approx X n) = 0).
    intros.
    generalize (Rbar_NonnegExpectation_le (simple_approx X n) X (apx_le1 n)); intros.
    rewrite H1 in H3.
    generalize (NonnegExpectation_pos (simple_approx X n)); intros.
    apply Rbar_le_antisym; trivial.
  

    assert (forall n:nat, ps_P (preimage_singleton (simple_approx X n) 0) = 1).
    intros.
    apply SimplePosExpectation_zero_pos with (frf := apx_frf1 n); trivial.
    generalize (frf_NonnegExpectation (simple_approx X n)); intros.
    rewrite H3 in H4; symmetry in H4.
    now apply Rbar_finite_eq in H4.

    assert (forall n:nat, ps_P (event_complement (preimage_singleton (has_pre := borel_has_preimages) (simple_approx X n) 0)) = 0).
    {
      intros.
      rewrite ps_complement.
      rewrite H4; lra.
    } 
    generalize (lim_prob (fun n => (event_complement (preimage_singleton (has_pre := borel_has_preimages) (simple_approx X n) 0)))
                         (event_complement (preimage_singleton (has_pre := Rbar_borel_has_preimages) X 0))
               ); trivial; intros HH.
    cut_to HH; trivial.
    - apply is_lim_seq_ext with (v := (fun n => 0)) in HH.
      + apply is_lim_seq_unique in HH.    
        rewrite Lim_seq_const in HH.
        rewrite ps_complement in HH.
        apply Rbar_finite_eq in HH.
        rewrite H1; lra.
      + trivial.
    -
      unfold event_sub, pre_event_sub, event_complement, pre_event_complement; simpl; intros.
      unfold NonnegativeFunction in apx_nnf1.
      apply Rgt_not_eq.
      apply Rdichotomy in H6.
      destruct H6.
      + generalize (apx_nnf1 n); intros.
        specialize (H7 x); lra.
      + specialize (apx_inc1 n x).
        lra.
    - unfold event_complement, pre_event_complement.
      intro x; simpl.
      split; intros.
      + destruct H6.
        unfold pre_event_preimage, pre_event_singleton.
        apply Rdichotomy in H6.
        destruct H6.
        generalize (apx_nnf1 x0 x); intros; lra.        
        specialize (apx_le1 x0 x); simpl in apx_le1.
        destruct (X x).
        * apply Rbar_finite_neq.
          apply Rgt_not_eq; lra.
        * discriminate.
        * discriminate.
      + specialize (H0 x).
        clear H H1 H2 H3 H4 H5 HH.
        unfold pre_event_preimage, pre_event_singleton in *.
        assert (Rbar_gt (X x) 0).
        {
          specialize (pofrf x).
          destruct (X x).
          - apply Rbar_finite_neq in H6.
            apply Rdichotomy in H6.
            destruct H6.
            + simpl in pofrf; lra.
            + now simpl.
          - now simpl.
          - tauto.
        }
        apply is_lim_seq_spec in H0.
        unfold is_lim_seq' in H0.
        case_eq (X x)
        ; [intros ? eqq1 | intros eqq1..]
        ; rewrite eqq1 in *.
        * specialize (H0 (mkposreal _ H)).
          destruct H0.
          specialize (H0 x0).
          exists x0.
          apply Rgt_not_eq.
          cut_to H0; [|lia].
          simpl in H0.
          specialize (apx_le1 x0 x).
          rewrite <- Rabs_Ropp in H0.
          replace (Rabs (-(simple_approx X x0 x - r))) with (r - simple_approx X x0 x) in H0
          ; try lra.
          simpl in apx_le1.
          rewrite Rabs_pos_eq; try lra.
          rewrite eqq1 in apx_le1.
          lra.
         * exists (1%nat).
           unfold simple_approx.
           match_destr.
           -- apply not_0_INR.
              lia.
           -- rewrite eqq1 in n.
              tauto.
         * tauto.
  Qed.


End RbarExpectation.

Section EventRestricted.
    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

    
  Lemma event_restricted_Rbar_NonnegExpectation P (pf1 : ps_P P = 1) pf (f : Ts -> Rbar) 
        (nnf : Rbar_NonnegativeFunction f) :
    @Rbar_NonnegExpectation Ts dom prts f nnf = 
    @Rbar_NonnegExpectation _ _ (event_restricted_prob_space prts P pf) 
                       (event_restricted_function P f) _.
  Proof.
    unfold Rbar_NonnegExpectation.
    unfold SimpleExpectationSup.
    unfold Lub_Rbar.
    destruct
      (ex_lub_Rbar
       (fun x : R =>
        exists
          (rvx : Ts -> R) (rv : RandomVariable dom borel_sa rvx) 
        (frf : FiniteRangeFunction rvx),
          (NonnegativeFunction rvx /\ Rbar_rv_le (fun x0 : Ts => rvx x0) f) /\
          SimpleExpectation rvx = x)).
    destruct
      (ex_lub_Rbar
       (fun x0 : R =>
        exists
          (rvx : event_restricted_domain P -> R) (rv : 
                                                  RandomVariable
                                                    (event_restricted_sigma P)
                                                    borel_sa rvx) 
        (frf : FiniteRangeFunction rvx),
          (NonnegativeFunction rvx /\
           Rbar_rv_le (fun x1 : event_restricted_domain P => rvx x1)
             (event_restricted_function P f)) /\ SimpleExpectation rvx = x0)).
    simpl.
    unfold is_lub_Rbar in *.
    destruct i; destruct i0.
    apply Rbar_le_antisym.
    - apply H0.
      unfold is_ub_Rbar.
      intros.
      destruct H3 as [? [? [? [? ?]]]].
      destruct H3.
      unfold is_ub_Rbar in H1.
      unfold is_ub_Rbar in H.
      apply H1.
      exists (event_restricted_function P x2).
      exists (Restricted_RandomVariable P x2 x3).
      exists (Restricted_FiniteRangeFunction P x2 x4).
      split.
      + split.
        * now apply Restricted_NonnegativeFunction.
        * etransitivity; [| apply event_restricted_Rbar_rv_le; eapply H5].
          intros ?; simpl.
          now right.
      + now rewrite <- event_restricted_SimpleExpectation.
    - apply H2.
      unfold is_ub_Rbar.
      intros.
      destruct H3 as [? [? [? [? ?]]]].
      destruct H3.
      unfold is_ub_Rbar in H1.
      unfold is_ub_Rbar in H.
      apply H.
      exists (lift_event_restricted_domain_fun 0 x2).
      do 2 eexists.
      split; [split |].
      + typeclasses eauto.
      + intro z.
        unfold lift_event_restricted_domain_fun.
        match_destr.
        apply H5.
      + subst.
        erewrite event_restricted_SimpleExpectation; eauto.
        apply SimpleExpectation_ext.
        apply restrict_lift.
  Qed.

  Lemma event_restricted_Rbar_Expectation P (pf1 : ps_P P = 1) pf (f : Ts -> Rbar) :
    @Rbar_Expectation Ts dom prts f = 
    @Rbar_Expectation _ _ (event_restricted_prob_space prts P pf) 
                       (event_restricted_function P f).
  Proof.
    unfold Rbar_Expectation.
    generalize (event_restricted_Rbar_NonnegExpectation 
                  P pf1 pf (Rbar_pos_fun_part f) _); intros.
    rewrite H.
    generalize (event_restricted_Rbar_NonnegExpectation 
                  P pf1 pf (Rbar_neg_fun_part f) _); intros.
    now rewrite H0.
  Qed.

End EventRestricted.

Require Import AlmostEqual.

Section almost.

    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}.

  Definition classic_dec {T : Type} (P : pre_event T)
    := (fun a => ClassicalDescription.excluded_middle_informative (P a)).

  Context (prts: ProbSpace dom).

  Instance Rbar_pos_fun_part_proper_almostR2 : Proper (almostR2 prts eq ==> almostR2 prts eq) 
                                            (fun x x0 => Rbar_pos_fun_part x x0).
  Proof.
    intros x1 x2 eqq1.
    apply (almostR2_sub prts eq (fun x x0 => Rbar_pos_fun_part x x0)); trivial.
    intros.
    unfold Rbar_pos_fun_part; simpl.
    now rewrite H.
  Qed.

  Instance Rbar_neg_fun_part_proper_almostR2 : Proper (almostR2 prts eq ==> almostR2 prts eq) 
                                            (fun x x0 => Rbar_neg_fun_part x x0).
  Proof.
    intros x1 x2 eqq1.
    apply (almostR2_sub prts eq (fun x x0 => Rbar_neg_fun_part x x0)); trivial.
    intros.
    unfold Rbar_neg_fun_part; simpl.
    now rewrite H.
  Qed.

  Lemma Rbar_NonnegExpectation_almostR2_0 x 
        {nnf:Rbar_NonnegativeFunction x} :
    almostR2 prts eq x (const 0) ->
    Rbar_NonnegExpectation x = 0.
  Proof.
    intros.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    destruct i as [xub xlub].
    unfold is_ub_Rbar in xub.
    specialize (xub 0).
    specialize (xlub 0).
    unfold is_ub_Rbar in xlub.
    cut_to xub.
    - cut_to xlub.
      + now apply Rbar_le_antisym.
      + intros.
        unfold BoundedNonnegativeFunction in H0.
        destruct H0 as [? [? [? [[? ?] ?]]]].
        simpl.
        assert (almostR2 prts eq x2 (const 0)).
        * destruct H as [P [Pall eq_on]].
          exists P.
          split; trivial.
          intros a ?.
          specialize (H1 a).
          rewrite eq_on in H1; trivial.
          unfold const in *.
          specialize (H0 a).
          simpl in H1.
          lra.
        * generalize (SimplePosExpectation_pos_zero prts x2 H3); intros.
          rewrite H4 in H2.
          rewrite <- H2.
          simpl; lra.
    - exists (const 0); exists (rvconst _ _ 0); exists (frfconst 0).
      split.
      + unfold BoundedNonnegativeFunction.
        split.
        * apply nnfconst; lra.
        * apply nnf.
      + apply SimpleExpectation_const.
  Qed.
  
  Lemma Rbar_NonnegExpectation_EventIndicator_as x {P} (dec:dec_event P)
        {xrv:RandomVariable dom Rbar_borel_sa x}                 
        {xnnf:Rbar_NonnegativeFunction x}
    :
      ps_P P = 1 ->
    Rbar_NonnegExpectation x = Rbar_NonnegExpectation (Rbar_rvmult x (EventIndicator dec)).
  Proof.
    intros pone.
    assert (eqq1:rv_eq x
                  (Rbar_rvplus (Rbar_rvmult x (EventIndicator dec))
                          (Rbar_rvmult x (EventIndicator (classic_dec (pre_event_complement P)))))).
    {
      intros ?.
      unfold EventIndicator, Rbar_rvmult, Rbar_rvplus, pre_event_complement.
      repeat match_destr; try tauto.
      - now rewrite Rbar_mult_1_r, Rbar_mult_0_r, Rbar_plus_0_r.
      - now rewrite Rbar_mult_1_r, Rbar_mult_0_r, Rbar_plus_0_l.
    }

    rewrite (Rbar_NonnegExpectation_ext _ _ eqq1).
    rewrite Rbar_NonnegExpectation_plus.
    - assert (eqq2:almostR2 prts eq (Rbar_rvmult x (EventIndicator (classic_dec (pre_event_complement P)))) (const 0)).
      {
        exists P.
        split; trivial.
        intros.
        unfold EventIndicator, pre_event_complement, Rbar_rvmult.
        match_destr; try tauto.
        now rewrite Rbar_mult_0_r.
      }
      rewrite (Rbar_NonnegExpectation_almostR2_0 _ eqq2).
      now rewrite Rbar_plus_0_r. 
    - apply Rbar_rvmult_rv; trivial.
      apply Real_Rbar_rv.
      typeclasses eauto.
    - apply Rbar_rvmult_rv; trivial.
      apply Real_Rbar_rv.
      apply EventIndicator_pre_rv.
      apply sa_complement.
      destruct P; trivial.
Qed.

  
  Lemma Rbar_NonnegExpectation_almostR2_proper x y
        {xrv:RandomVariable dom Rbar_borel_sa x}
        {yrv:RandomVariable dom Rbar_borel_sa y}
        {xnnf:Rbar_NonnegativeFunction x}
        {ynnf:Rbar_NonnegativeFunction y} :
    almostR2 prts eq x y ->
    Rbar_NonnegExpectation x = Rbar_NonnegExpectation y.
  Proof.
    intros [P [Pone Peqq]].
    rewrite (Rbar_NonnegExpectation_EventIndicator_as x (classic_dec P) Pone).
    rewrite (Rbar_NonnegExpectation_EventIndicator_as y (classic_dec P) Pone).
    apply Rbar_NonnegExpectation_ext.
    intros ?.
    unfold Rbar_rvmult, EventIndicator.
    match_destr.
    - repeat rewrite Rbar_mult_1_r.
      now rewrite Peqq.
    - now repeat rewrite Rbar_mult_0_r.
  Qed.

  Lemma Rbar_Expectation_almostR2_proper x y
        {xrv:RandomVariable dom Rbar_borel_sa x}
        {yrv:RandomVariable dom Rbar_borel_sa y} :
    almostR2 prts eq x y ->
    Rbar_Expectation x = Rbar_Expectation y.
  Proof.
    intros eqq.
    unfold Rbar_Expectation.
    rewrite (Rbar_NonnegExpectation_almostR2_proper (fun x0 : Ts => Rbar_pos_fun_part x x0) (fun x0 : Ts => Rbar_pos_fun_part y x0))
      by now apply Rbar_pos_fun_part_proper_almostR2.
    rewrite (Rbar_NonnegExpectation_almostR2_proper (fun x0 : Ts => Rbar_neg_fun_part x x0) (fun x0 : Ts => Rbar_neg_fun_part y x0))
      by now apply Rbar_neg_fun_part_proper_almostR2.
    reflexivity.
  Qed.

End almost.
