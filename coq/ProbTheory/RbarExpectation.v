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
Require Import Almost.
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
      RandomVariable dom Rbar_borel_sa (Rbar_rvplus rv_X1 rv_X2).
   Proof.
     intros.
     apply Rbar_measurable_rv.
     apply rv_Rbar_measurable in rvx1.
     apply rv_Rbar_measurable in rvx2.     
     now apply Rbar_plus_measurable.
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

      
  Lemma NNExpectation_Rbar_NNExpectation
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

  Lemma Rbar_pos_fun_pos_fun (rv_X : Ts -> R) :
    rv_eq (Rbar_pos_fun_part rv_X) (pos_fun_part rv_X).
  Proof.
    intro x.
    unfold Rbar_pos_fun_part, pos_fun_part.
    unfold Rbar_max; simpl.
    unfold Rmax.
    repeat match_destr; simpl in *; lra.
  Qed.
  
  Lemma Rbar_neg_fun_neg_fun (rv_X : Ts -> R) :
    rv_eq (Rbar_neg_fun_part rv_X) (neg_fun_part rv_X).
  Proof.
    intro x.
    unfold Rbar_neg_fun_part, neg_fun_part.
    unfold Rbar_max; simpl.
    unfold Rmax.
    repeat match_destr; simpl in *; lra.
  Qed.

  Lemma Expectation_Rbar_Expectation
        (rv_X : Ts -> R) :
    Expectation rv_X = Rbar_Expectation rv_X.
  Proof.
    unfold Expectation, Rbar_Expectation.
    f_equal.
    - rewrite NNExpectation_Rbar_NNExpectation.
      apply Rbar_NonnegExpectation_ext.
      intro x.
      now rewrite Rbar_pos_fun_pos_fun.
    - rewrite NNExpectation_Rbar_NNExpectation.
      apply Rbar_NonnegExpectation_ext.
      intro x.
      now rewrite Rbar_neg_fun_neg_fun.
  Qed.

    Lemma Expectation_rvlim_ge
        (Xn : nat -> Ts -> R)          
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      forall n, Rbar_le (NonnegExpectation (Xn n)) (Rbar_NonnegExpectation (Rbar_rvlim Xn)).
  Proof.
    intros.
    rewrite NNExpectation_Rbar_NNExpectation.
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

  Global Instance Rbar_NonnegativeFunction_const_posreal (c: posreal) :
    Rbar_NonnegativeFunction (const (B:=Ts) c).
  Proof.
    destruct c.
    apply nnfconst.
    lra.
  Qed.
  
  Lemma Rbar_NonnegExpectation_scale (c: posreal) 
        (rv_X : Ts -> Rbar)
        {pofrf:Rbar_NonnegativeFunction rv_X} :
    Rbar_NonnegExpectation (Rbar_rvmult (const c) rv_X) =
    Rbar_mult c (Rbar_NonnegExpectation rv_X).
  Proof.
    destruct c as [c cpos].
    unfold Rbar_rvmult, const.
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
        { 
          now apply Rinv_0_lt_compat.
        } 
        apply (positive_scale_nnf (mkposreal _ H2) x0). 
      + unfold rv_le, rvscale in *.
        intros y.
        specialize (H0 y).
        simpl in H0.
        destruct (rv_X y); simpl in *; try tauto
        ; [|
           destruct (Rle_dec 0 c); try lra
           ; destruct (Rle_lt_or_eq_dec 0 c r); try lra
          ].
        apply (Rmult_le_compat_l (/ c)) in H0.
        * rewrite <- Rmult_assoc in H0.
          rewrite Rinv_l in H0; lra.
        * left.
          now apply Rinv_0_lt_compat.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1; simpl.
        lra.
    - exists (rvscale c x0).
      exists (rvscale_rv _ _ _ _).
      exists (frfscale c x0).
      split; [split |].
      + now apply (rvscale_nnf (mkposreal c cpos)). 
      + intros a.
        specialize (H0 a).
        simpl in *.
        destruct (rv_X a); simpl in *; try tauto.
        * unfold rvscale.
          apply Rmult_le_compat_l; lra.
        * destruct (Rle_dec 0 c); try lra
          ; destruct (Rle_lt_or_eq_dec 0 c r); try lra.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1; simpl.
        field; trivial.
        lra.
  Qed.

  Lemma Rbar_Expectation_scale_pos (c:posreal) (rv_X : Ts -> Rbar) :
    Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvmult (const c) rv_X)) =
    Rbar_mult c (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X)).
  Proof.
    rewrite <- Rbar_NonnegExpectation_scale.
    apply Rbar_NonnegExpectation_ext.
    intros x.
    unfold Rbar_pos_fun_part, Rbar_rvmult, const.
    now rewrite scale_Rbar_max0.
  Qed.
  
  Lemma Rbar_Expectation_scale_neg (c:posreal) (rv_X : Ts -> Rbar) :
    Rbar_NonnegExpectation (fun x : Ts => Rbar_neg_fun_part (Rbar_rvmult (const c) rv_X) x) =
    Rbar_mult c (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X)).
  Proof.
    rewrite <- Rbar_NonnegExpectation_scale.
    apply Rbar_NonnegExpectation_ext.
    intros x.
    unfold Rbar_neg_fun_part, Rbar_rvmult, const.
    rewrite <- Rbar_mult_opp_r.
    now rewrite scale_Rbar_max0.
  Qed.

  Lemma Rbar_Expectation_scale_posreal (c: posreal) 
        (rv_X : Ts -> Rbar) :
    let Ex_rv := Rbar_Expectation rv_X in
    let Ex_c_rv := Rbar_Expectation (Rbar_rvmult (const c) rv_X) in
    Ex_c_rv = 
    match Ex_rv with
    | Some x => Some (Rbar_mult c x)
    | None => None
    end.
  Proof. 
    unfold Rbar_Expectation.
    rewrite Rbar_Expectation_scale_pos; trivial.
    rewrite Rbar_Expectation_scale_neg; trivial.
    apply scale_Rbar_diff.
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
                                         (Rbar_rvplus_rv rv_X1 rv_X2)
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
    unfold Rbar_pos_fun_part, Rbar_max.
    intro x.
    match_case; intros.
    now apply Rbar_le_antisym.
  Qed.

  Lemma Rbar_neg_fun_part_pos (rv_X : Ts -> Rbar) 
        {nnf : Rbar_NonnegativeFunction rv_X} :
    rv_eq (Rbar_neg_fun_part rv_X) (fun x => (const 0) x).
  Proof.
    unfold Rbar_neg_fun_part, const, Rbar_max.
    intro x.
    specialize (nnf x).
    rewrite <- Rbar_opp_le in nnf.
    replace (Rbar_opp 0) with (Finite 0) in nnf by (simpl; apply Rbar_finite_eq; lra).
    match_case; intros.
    now apply Rbar_le_antisym.
  Qed.

  Instance nnf_0 :
    (@Rbar_NonnegativeFunction Ts (fun x => const 0 x)).
  Proof.
    unfold Rbar_NonnegativeFunction.
    intros.
    simpl.
    unfold const.
    lra.
  Qed.

  Lemma Rbar_Expectation_pos_pofrf (rv_X : Ts -> Rbar) 
        {nnf : Rbar_NonnegativeFunction rv_X} :
    Rbar_Expectation rv_X = Some (Rbar_NonnegExpectation rv_X).
  Proof.
    unfold Rbar_Expectation.
    rewrite <- (Rbar_NonnegExpectation_ext _ _ (Rbar_pos_fun_part_pos rv_X)).
    rewrite (Rbar_NonnegExpectation_ext _ _ (Rbar_neg_fun_part_pos rv_X)).
    replace (Rbar_NonnegExpectation (const 0)) with (Finite 0).
    - unfold Rbar_minus'.
      simpl.
      rewrite Ropp_0.
      unfold Rbar_plus'.
      match_case; intros.
      + f_equal.
        apply Rbar_finite_eq.
        lra.
    - generalize (Rbar_NonnegExpectation_const (Finite 0)); intros.
      symmetry.
      assert (0 <= 0) by lra.
      apply (H H0).
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

  Lemma Rbar_Expectation_nonneg_zero_almost_zero
        (X : Ts -> Rbar)
        {rv : RandomVariable dom Rbar_borel_sa X}
        {pofrf :Rbar_NonnegativeFunction X} :
    Rbar_Expectation X = Some (Finite 0) ->
    almostR2 Prts eq X (const (Finite 0)).
  Proof.
    exists (preimage_singleton (has_pre := Rbar_borel_has_preimages) X 0).
    split.
    - now apply Rbar_Expectation_zero_pos.
    - intros.
      apply H0.
  Qed.

    Global Instance Rbar_nnfabs
           (rv_X : Ts -> Rbar) :
      Rbar_NonnegativeFunction (Rbar_rvabs rv_X).
    Proof.
      unfold Rbar_NonnegativeFunction, Rbar_rvabs.
      intros; apply Rbar_abs_nneg.
    Qed.

    Lemma Rbar_pos_fun_part_le rv_X : 
      Rbar_rv_le (Rbar_pos_fun_part rv_X) (Rbar_rvabs rv_X).
    Proof.
      intros ?.
      unfold Rbar_rvabs, Rbar_pos_fun_part, Rbar_abs, Rbar_max; simpl.
      repeat match_destr; try simpl; try easy.
      - apply Rabs_pos.
      - apply Rle_abs.
    Qed.

    Lemma Rbar_neg_fun_part_le rv_X :
      Rbar_rv_le (Rbar_neg_fun_part rv_X) (Rbar_rvabs rv_X).
    Proof.
      intros ?.
      unfold Rbar_rvabs, Rbar_rvopp, Rbar_neg_fun_part, Rbar_abs, Rbar_max; simpl.
      repeat match_destr; try simpl; try easy.
      - apply Rabs_pos.
      - apply Rabs_maj2.
    Qed.

  Lemma Rbar_Expectation_abs_then_finite (rv_X:Ts->Rbar)  
    :  match Rbar_Expectation (Rbar_rvabs rv_X) with
       | Some (Finite _) => True
       | _ => False
       end ->
       match Rbar_Expectation rv_X with
       | Some (Finite _) => True
       | _ => False
       end.
  Proof.
    rewrite Rbar_Expectation_pos_pofrf with (nnf := Rbar_nnfabs _).
    unfold Rbar_Expectation.
    intros HH.
    match_case_in HH
    ; [intros r eqq | intros eqq | intros eqq]
    ; rewrite eqq in HH
    ; try contradiction.

    unfold Rbar_minus', Rbar_plus'.
    assert (fin:is_finite (Rbar_NonnegExpectation (Rbar_rvabs rv_X)))
      by (rewrite eqq; reflexivity).
    generalize (Rbar_pos_fun_part_le rv_X); intros le1.
    generalize (is_finite_Rbar_NonnegExpectation_le _ _ le1 fin)
    ; intros fin1.
    generalize (Rbar_neg_fun_part_le rv_X); intros le2.
    generalize (is_finite_Rbar_NonnegExpectation_le _ _ le2 fin)
    ; intros fin2.
    rewrite <- fin1.
    rewrite <- fin2.
    simpl; trivial.
  Qed.

    Lemma Rbar_rv_pos_neg_id (rv_X:Ts->Rbar) : 
      rv_eq (rv_X) (Rbar_rvplus (Rbar_pos_fun_part rv_X) (Rbar_rvopp (Rbar_neg_fun_part rv_X))).
    Proof.
      intros x.
      unfold Rbar_rvplus, Rbar_rvopp, Rbar_pos_fun_part, Rbar_neg_fun_part; simpl.
      assert (Rbar_opp 0 = 0).
      {
        unfold Rbar_opp.
        rewrite Rbar_finite_eq.
        lra.
      }
      unfold Rbar_max; repeat match_destr.
      - rewrite H.
        rewrite <- H in r0.
        rewrite Rbar_opp_le in r0.
        rewrite Rbar_plus_0_r.
        apply Rbar_le_antisym; eauto.
      - rewrite Rbar_opp_involutive.
        now rewrite Rbar_plus_0_l.
      - rewrite H.
        now rewrite Rbar_plus_0_r.
      - rewrite Rbar_opp_involutive.
        rewrite <- H in n0.
        rewrite Rbar_opp_le in n0.
        apply Rbar_not_le_lt in n0.
        apply Rbar_not_le_lt in n.
        generalize (Rbar_lt_trans _ _ _ n n0); intros.
        simpl in H0; lra.
    Qed.

  Lemma Rbar_Expectation_opp
        (rv_X : Ts -> Rbar) :
    let Ex_rv := Rbar_Expectation rv_X in
    let Ex_o_rv := Rbar_Expectation (Rbar_rvopp rv_X) in
    Ex_o_rv = 
    match Ex_rv with
    | Some x => Some (Rbar_opp x)
    | None => None
    end.
  Proof.
    unfold Rbar_Expectation.
    rewrite Rbar_NonnegExpectation_ext with (nnf2 := Rbar_neg_fun_pos rv_X).
    - replace (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvopp rv_X) )) with
          (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X)).
      + unfold Rbar_minus'.
        case_eq  (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X)); intros.
        * case_eq  (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X)); intros; simpl; f_equal.
          rewrite Rbar_finite_eq; lra.
        * case_eq  (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X)); intros; simpl; f_equal.
        * case_eq  (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X)); intros; simpl; f_equal.
      + symmetry.
        rewrite Rbar_NonnegExpectation_ext with (nnf2 := Rbar_pos_fun_pos rv_X).
        * reflexivity.
        * intro x.
          unfold Rbar_neg_fun_part, Rbar_rvopp, Rbar_pos_fun_part; simpl.
          now rewrite Rbar_opp_involutive.
    - intro x.
      now unfold Rbar_neg_fun_part, Rbar_rvopp, Rbar_pos_fun_part; simpl.
  Qed.

  Lemma Rbar_Expectation_scale (c: R) 
        (rv_X : Ts -> Rbar) :
    c <> 0 ->
    let Ex_rv := Rbar_Expectation rv_X in
    let Ex_c_rv := Rbar_Expectation (Rbar_rvmult (const c) rv_X) in
    Ex_c_rv = 
    match Ex_rv with
    | Some x => Some (Rbar_mult c x)
    | None => None
    end.
  Proof. 
    intros.
    destruct (Rlt_dec 0 c).
    apply (Rbar_Expectation_scale_posreal (mkposreal c r)).
    destruct (Rlt_dec 0 (- c)).
    - unfold Ex_c_rv.
      rewrite (@Rbar_Expectation_ext _ (Rbar_rvopp (Rbar_rvmult (const (- c)) rv_X))).
      + rewrite Rbar_Expectation_opp.
        rewrite (Rbar_Expectation_scale_posreal (mkposreal (-c) r)).
        unfold Ex_rv.
        case_eq (Rbar_Expectation rv_X); intros; trivial.
        f_equal; simpl.
        rewrite <- Rbar_mult_opp_l.
        simpl.
        now replace (- - c) with (c) by lra.
      + intro x.
        unfold Rbar_rvmult, Rbar_rvopp, const.
        simpl.
        rewrite <- Rbar_mult_opp_l; simpl.
        now replace (- - c) with (c) by lra.
    - unfold Ex_c_rv, Ex_rv.
      lra.
  Qed.

  Global Instance Rbar_LimInf_seq_pos
         (Xn : nat -> Ts -> R)
         (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    Rbar_NonnegativeFunction 
      (fun omega : Ts => (LimInf_seq (fun n : nat => Xn n omega))).
  Proof.
    intro x.
    generalize (LimInf_le (fun n : nat => 0) (fun n : nat => Xn n x)); intros.
    cut_to H.
    - now rewrite LimInf_seq_const in H.
    - exists (0%nat).
      intros.
      apply Xn_pos.
  Qed.

  Lemma Rbar_NN_Fatou
        (Xn : nat -> Ts -> R)
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (fin_exp : forall n, is_finite (NonnegExpectation (Xn n)))
        (lim_rv : RandomVariable dom Rbar_borel_sa 
                                 (fun omega => LimInf_seq (fun n => Xn n omega))) :
    Rbar_le (Rbar_NonnegExpectation (fun omega => LimInf_seq (fun n => Xn n omega)))
            (LimInf_seq (fun n => NonnegExpectation (Xn n))).
  Proof.
    generalize (is_finite_Fatou_Y Xn Xn_pos); intros.
    generalize (Fatou_Y_pos Xn Xn_pos); intros.
    assert (forall n, rv_le (fun omega : Ts => Fatou_Y Xn n omega) (Xn n)).
    - intros; intro x.
      unfold Fatou_Y.
      generalize (Inf_seq_correct (fun k : nat => Xn (k + n)%nat x)); intros.
      apply is_inf_seq_glb in H1.
      unfold Rbar_is_glb in H1.
      destruct H1.
      unfold Rbar_is_lower_bound in H1.
      specialize (H1 (Xn n x)).
      assert  (exists n0 : nat, (Finite (Xn n x)) = (Finite (Xn (n0 + n)%nat x))) by
       (exists (0%nat); f_equal).
      specialize (H1 H3).
      unfold Fatou_Y in H.
      now rewrite <- H in H1.
    - assert (Lim_seq (fun n => NonnegExpectation (Fatou_Y Xn n)) =  
              (Rbar_NonnegExpectation (fun omega => LimInf_seq (fun n => Xn n omega)))).
      + apply Rbar_monotone_convergence with (X:= (fun omega : Ts => LimInf_seq (fun n : nat => Xn n omega))); trivial.
        * assert (forall (n:nat), Rbar_le (NonnegExpectation (Fatou_Y Xn n))
                                          (NonnegExpectation (Xn n))); intros.
          -- now apply NonnegExpectation_le.
          -- now apply Fatou_Y_rv.
        * intros; intro x.
          generalize (inf_limInf (fun k => Xn k x) n); intros HH.
          rewrite <- (H n x) in HH.
          apply HH.
        * intros; intro x.
          unfold Fatou_Y.
          do 2 rewrite Inf_eq_glb.
          generalize (Rbar_glb_subset (fun x0 : Rbar => exists n0 : nat, x0 = Xn (n0 + n)%nat x)
                                      (fun x0 : Rbar => exists n0 : nat, x0 = Xn (n0 + S n)%nat x)); intros.
          unfold Fatou_Y in H.
          generalize (H n x).
          generalize (H (S n) x).
          do 2 rewrite Inf_eq_glb; intros.
          rewrite <- H3 in H2.
          rewrite <- H4 in H2.    
          apply H2.
          intros.
          destruct H5.
          exists (S x1).
          now replace (S x1 + n)%nat with (x1 + S n)%nat by lia.          
        * intros; now apply Finite_NonnegExpectation_le with (rv_X2 := Xn n) (nnf2 := Xn_pos n).
        * intros.
         (* rewrite isf. *)
          apply (lim_seq_Inf_seq (fun k => Xn k omega)); trivial.
          -- unfold Fatou_Y in H.
             intros.
             apply H.
          -- intros.
             now apply Fatou_Y_incr.
      + rewrite <- H2.
        replace  (Lim_seq
       (fun n : nat => NonnegExpectation (fun omega : Ts => Fatou_Y Xn n omega))) with
        (LimInf_seq
       (fun n : nat => NonnegExpectation (fun omega : Ts => Fatou_Y Xn n omega))).
        * apply LimInf_le.
          exists (0%nat); intros.
          generalize (NonnegExpectation_le (fun omega : Ts => Fatou_Y Xn n omega) (Xn n) (H1 n)); intros.
          generalize (Finite_NonnegExpectation_le (Fatou_Y Xn n) (Xn n) _ (Xn_pos n) (H1 n) (fin_exp n)); intros.
          rewrite <- H5 in H4.
          rewrite <- (fin_exp n) in H4.
          apply H4.
        * rewrite limInf_increasing; trivial.
          intros.
          generalize (NonnegExpectation_le 
                        (fun omega : Ts => Fatou_Y Xn n omega)
                        (fun omega : Ts => Fatou_Y Xn (S n) omega)); intros.
          generalize (Finite_NonnegExpectation_le (Fatou_Y Xn n) (Xn n) _ (Xn_pos n) (H1 n) (fin_exp n)); intros.
          generalize (Finite_NonnegExpectation_le (Fatou_Y Xn (S n)) (Xn (S n)) _ (Xn_pos (S n)) (H1 (S n)) (fin_exp (S n))); intros.                    
          rewrite <- H4 in H3.
          rewrite <- H5 in H3.          
          apply H3.
          intro x.
          unfold Fatou_Y.
          do 2 rewrite Inf_eq_glb.
          generalize (Rbar_glb_subset (fun x0 : Rbar => exists n0 : nat, x0 = Xn (n0 + n)%nat x)
                                      (fun x0 : Rbar => exists n0 : nat, x0 = Xn (n0 + S n)%nat x)); intros.
          unfold Fatou_Y in H.
          generalize (H n x).
          generalize (H (S n) x).
          do 2 rewrite Inf_eq_glb; intros.
          rewrite <- H7 in H6.
          rewrite <- H8 in H6.    
          apply H6.
          intros.
          destruct H9.
          exists (S x1).
          now replace (S x1 + n)%nat with (x1 + S n)%nat by lia.          
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

Section almost.

    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}.

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
        * generalize (SimplePosExpectation_pos_zero x2 H3); intros.
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

(*
    Lemma Rbar_NonnegExpectation_almostR2_eq f1 f2
          {nnf1:Rbar_NonnegativeFunction f1} 
          {nnf2:Rbar_NonnegativeFunction f2} :      
    almostR2 prts eq f1 f2 ->
    Rbar_NonnegExpectation f1 = Rbar_NonnegExpectation f2.
  Proof.
    intros.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    destruct i as [xub xlub].
    destruct i0 as [xub0 xlub0].    
    unfold is_ub_Rbar in xub.
    unfold is_ub_Rbar in xub0.    
    apply Rbar_le_antisym.
    - apply xlub.
      unfold is_ub_Rbar; intros.
      destruct H0 as [? [? [? [[? ?] ?]]]].
      assert (almostR2 prts Rbar_le x2 f2).
      + destruct H as [P [Pall eq_on]].
        exists P.
        split;trivial.
        intros a ?.
        specialize (H1 a).
        rewrite eq_on in H1; trivial.
      + apply xub0.
        exists x2; exists x3; exists x4.
        split; trivial.
        split; trivial.
        Locate SimplePosExpectation_pos_zero.
      

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
*)
  
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

  
  Lemma Rbar_pos_neg_id (x:Rbar) : 
    x = Rbar_plus (Rbar_max x 0) (Rbar_opp (Rbar_max (Rbar_opp x) 0)).
  Proof.
    assert (Rbar_opp 0 = 0).
    {
      unfold Rbar_opp.
      rewrite Rbar_finite_eq.
      lra.
    }
    unfold Rbar_max; repeat match_destr.
    - rewrite H.
      rewrite <- H in r0.
      rewrite Rbar_opp_le in r0.
      rewrite Rbar_plus_0_r.
      apply Rbar_le_antisym; eauto.
    - rewrite Rbar_opp_involutive.
      now rewrite Rbar_plus_0_l.
    - rewrite H.
      now rewrite Rbar_plus_0_r.
    - rewrite Rbar_opp_involutive.
      rewrite <- H in n0.
      rewrite Rbar_opp_le in n0.
      apply Rbar_not_le_lt in n0.
      apply Rbar_not_le_lt in n.
      generalize (Rbar_lt_trans _ _ _ n n0); intros.
      simpl in H0; lra.
  Qed.

  Lemma Rbar_max_minus_nneg (x y : Rbar) :
    Rbar_le 0 x ->
    Rbar_le 0 y ->
    (x = 0 \/ y = 0) ->
    Rbar_max (Rbar_minus x y) 0 = x.
  Proof.
    intros.
    unfold Rbar_max, Rbar_minus.
    destruct x; destruct y; try tauto.
    simpl in H; simpl in H0.
    - match_destr.
      + simpl in r1.
        destruct H1; apply Rbar_finite_eq in H1; apply Rbar_finite_eq; lra.
      + apply Rbar_not_le_lt in n.
        simpl; simpl in n.
        destruct H1; apply Rbar_finite_eq in H1; apply Rbar_finite_eq; lra.
    - match_destr; destruct H1; try congruence.
      rewrite H1 in n.
      now simpl in n.
    - destruct H1; try congruence.
      rewrite H1; simpl.
      match_destr; try congruence.
      now simpl in r0.
    - destruct H1; congruence.
  Qed.

    Program Definition pinf_Indicator 
          (f : Ts -> Rbar) :=
    EventIndicator (P := (fun x => (f x) = p_infty)) _.
  Next Obligation.
    apply ClassicalDescription.excluded_middle_informative.
  Qed.

  Instance Rbar_positive_indicator_prod (f : Ts -> Rbar) (c : posreal) :
    Rbar_NonnegativeFunction (rvscale c (pinf_Indicator f)).
  Proof.
    unfold pinf_Indicator.
    apply rvscale_nnf.
    typeclasses eauto.
  Qed.

  Lemma finite_Rbar_NonnegExpectation_le_inf
        (f : Ts -> Rbar)
        (fpos : Rbar_NonnegativeFunction f) 
        (c : posreal)   :
    is_finite (Rbar_NonnegExpectation f) ->
    Rbar_le (NonnegExpectation (rvscale c (pinf_Indicator f)))
            (Rbar_NonnegExpectation f).
  Proof.
    generalize (Rbar_NonnegExpectation_le (rvscale c (pinf_Indicator f)) f); intros.
    apply H.
    intro x.
    unfold rvscale, pinf_Indicator.
    unfold EventIndicator.
    match_destr.
    - rewrite Rmult_1_r.
      rewrite e.
      now simpl.
    - rewrite Rmult_0_r.
      apply fpos.
  Qed.
  
  Lemma finite_Rbar_NonnegExpectation_le_inf2
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) 
        (fpos : Rbar_NonnegativeFunction f) :
    is_finite (Rbar_NonnegExpectation f) ->
    forall (c:posreal), Rbar_le (c * (ps_P (exist _ _ (sa_pinf_Rbar f rv))))
            (Rbar_NonnegExpectation f).
  Proof.
    intros.
    generalize (finite_Rbar_NonnegExpectation_le_inf f fpos c H); intros.
    rewrite NonnegExpectation_scale in H0.
    unfold pinf_Indicator in H0.
    assert (FiniteRangeFunction (EventIndicator (fun x : Ts => pinf_Indicator_obligation_1 f x))) by typeclasses eauto.
    assert (RandomVariable dom borel_sa (EventIndicator (fun x : Ts => pinf_Indicator_obligation_1 f x))).
    apply EventIndicator_pre_rv.
    now apply sa_pinf_Rbar.
    generalize (frf_NonnegExpectation (EventIndicator (fun x : Ts => pinf_Indicator_obligation_1 f x))); intros.
    rewrite H2 in H0.
    generalize (SimpleExpectation_pre_EventIndicator 
                  (P := (fun x => f x = p_infty)) (sa_pinf_Rbar f rv)
                  (fun x : Ts => pinf_Indicator_obligation_1 f x)); intros.
    replace (@SimpleExpectation Ts dom prts
                  (@EventIndicator Ts (fun x : Ts => @eq Rbar (f x) p_infty)
                                   (fun x : Ts => pinf_Indicator_obligation_1 f x)) H1 X)
      with
        (ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv))) in H0.
    apply H0.
    rewrite SimpleExpectation_pf_irrel with (frf2 := X) in H3.
    symmetry.
    apply H3.
   Qed.

   Lemma finite_Rbar_NonnegExpectation_never_inf
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) 
        (fpos : Rbar_NonnegativeFunction f) :
    is_finite (Rbar_NonnegExpectation f) ->
    ps_P (exist sa_sigma _ (sa_pinf_Rbar f rv)) = 0.
     Proof.
       intros.
       generalize (finite_Rbar_NonnegExpectation_le_inf2 f rv fpos H); intros.
       rewrite <- H in H0.
       simpl in H0.
       destruct (Rlt_dec 
                   0
                   (ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv)))).
       - assert (0 <
                 ((real (Rbar_NonnegExpectation f))+1)
                   /
                   (ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv)))).
         + unfold Rdiv.
           apply Rmult_lt_0_compat.
           generalize (Rbar_NonnegExpectation_pos f); intros.
           rewrite <- H in H1; simpl in H1.
           lra.
           now apply Rinv_0_lt_compat.
         + specialize (H0 (mkposreal _ H1)).
           simpl in H0.
           unfold Rdiv in H0.
           rewrite Rmult_assoc in H0.
           rewrite Rinv_l in H0.
           lra.
           now apply Rgt_not_eq.
       - generalize (ps_pos (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv))); intros.
         assert (0 >= ps_P (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv))) by lra.
         intuition.
   Qed.

  Lemma finite_Rbar_NonnegExpectation_almostR2_finite
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) 
        (fpos : Rbar_NonnegativeFunction f) :
    is_finite (Rbar_NonnegExpectation f) ->
    ps_P (exist sa_sigma _ (sa_finite_Rbar f rv)) = 1.
  Proof.
    intros.
    generalize (finite_Rbar_NonnegExpectation_never_inf f rv fpos H); intros.
    assert (event_equiv
              (exist sa_sigma (fun x : Ts => is_finite (f x)) (sa_finite_Rbar f rv))
              (event_complement
                 (exist sa_sigma (fun x : Ts => f x = p_infty) (sa_pinf_Rbar f rv)))).
    - intro x.
      simpl.
      unfold pre_event_complement.
      generalize (fpos x); intros.
      destruct (f x); unfold is_finite.
      + simpl in H1.
        split; intros.
        * discriminate.
        * reflexivity.
      + simpl.
        split; intros.
        * discriminate.
        * tauto.
      + now simpl in H1.
    - rewrite H1.
      rewrite ps_complement.
      rewrite H0.
      lra.
   Qed.

  Lemma finite_Rbar_NonnegExpectation_almost_finite
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) 
        (fpos : Rbar_NonnegativeFunction f) :
    is_finite (Rbar_NonnegExpectation f) ->
    almost prts (fun x => is_finite (f x)).
  Proof.
    intros.
    generalize (finite_Rbar_NonnegExpectation_almostR2_finite f rv fpos H); intros.
    exists  (exist sa_sigma (fun x : Ts => is_finite (f x)) (sa_finite_Rbar f rv)).
    split; trivial.
  Qed.

  Class Rbar_IsFiniteExpectation (rv_X:Ts->Rbar) 
    := Rbar_is_finite_expectation :
         match Rbar_Expectation rv_X with
         | Some (Finite _) => True
         | _ => False
         end.

  Lemma Rbar_rvabs_plus_posfun_negfun
        (f : Ts -> Rbar ) :
    rv_eq (Rbar_rvabs f)
          (Rbar_rvplus (Rbar_pos_fun_part f) (Rbar_neg_fun_part f)).
  Proof.
    intro x.
    unfold Rbar_rvabs, Rbar_rvplus, Rbar_pos_fun_part, Rbar_neg_fun_part.
    destruct (f x).
    - simpl.
      unfold Rbar_max, Rabs, Rbar_plus, Rbar_plus'.
      match_destr; simpl.
      + destruct (Rbar_le_dec r 0); destruct (Rbar_le_dec (-r) 0); unfold Rbar_le in *
        ; try lra.
        now rewrite Rplus_0_l.
      + destruct (Rbar_le_dec r 0); destruct (Rbar_le_dec (-r) 0); unfold Rbar_le in *
        ; try lra.
        * assert (r = 0) by lra; subst.
          now rewrite Rplus_0_r.
        * now rewrite Rplus_0_r.
    - simpl.
      unfold Rbar_max, Rabs, Rbar_plus, Rbar_plus'.
      destruct (Rbar_le_dec p_infty 0); destruct (Rbar_le_dec m_infty 0); unfold Rbar_le in *; tauto.
    - simpl.
      unfold Rbar_max, Rabs, Rbar_plus, Rbar_plus'.
      destruct (Rbar_le_dec p_infty 0); destruct (Rbar_le_dec m_infty 0); unfold Rbar_le in *; tauto.
  Qed.

  Lemma finiteExp_Rbar_rvabs 
        (f : Ts -> Rbar) 
        {rv : RandomVariable dom Rbar_borel_sa f}:
    Rbar_IsFiniteExpectation f <->
    is_finite (Rbar_NonnegExpectation (Rbar_rvabs f)).
  Proof.
    unfold Rbar_IsFiniteExpectation, Rbar_Expectation.
    generalize (Rbar_rvabs_plus_posfun_negfun f); intros.
    rewrite (Rbar_NonnegExpectation_ext _ _ H).
    unfold Rbar_minus'.
    unfold Rbar_plus', Rbar_opp.
    rewrite Rbar_NonnegExpectation_plus.
    generalize (Rbar_NonnegExpectation_pos (Rbar_pos_fun_part f)); intros.
    generalize (Rbar_NonnegExpectation_pos (Rbar_neg_fun_part f)); intros.  
    destruct (Rbar_NonnegExpectation (Rbar_pos_fun_part f)); unfold is_finite.
    - destruct (Rbar_NonnegExpectation (Rbar_neg_fun_part f)); simpl; intuition discriminate.
    - destruct (Rbar_NonnegExpectation (Rbar_neg_fun_part f)); simpl; intuition discriminate.
    - now simpl in H0.
    - now apply Rbar_pos_fun_part_rv.
    - now apply Rbar_neg_fun_part_rv.      
  Qed.

  Lemma finite_Rbar_Expectation_almostR2_finite
        (f : Ts -> Rbar)
        (rv : RandomVariable dom Rbar_borel_sa f) :
    Rbar_IsFiniteExpectation f ->
    ps_P (exist sa_sigma _ (sa_finite_Rbar f rv)) = 1.
  Proof.
    intros.
    generalize (finite_Rbar_NonnegExpectation_almostR2_finite (Rbar_rvabs f) (Rbar_rvabs_rv f) (Rbar_rvabs_nnf f)); intros.
    assert (pre_event_equiv
              (fun x : Ts => is_finite (Rbar_rvabs f x))
              (fun x : Ts => is_finite (f x))).
    {
      intro x.
      now unfold Rbar_rvabs, is_finite; destruct (f x); simpl.
    }
    assert (event_equiv
              (exist sa_sigma (fun x : Ts => is_finite (Rbar_rvabs f x))
                     (sa_finite_Rbar (Rbar_rvabs f) (Rbar_rvabs_rv f)))
              (exist sa_sigma (fun x : Ts => is_finite (f x)) (sa_finite_Rbar f rv))).
    easy.
    erewrite <- ps_proper; try eapply H2.
    apply H0.
    now apply finiteExp_Rbar_rvabs.
  Qed.    

  Lemma IsFiniteExpectation_nneg_is_almost_finite (f : Ts -> Rbar)
        {rv : RandomVariable dom Rbar_borel_sa f}
        {nnf : Rbar_NonnegativeFunction f} :
    Rbar_IsFiniteExpectation f ->
    almost prts (fun x => is_finite (f x)).
  Proof.
    intros isfe.
    generalize (finite_Rbar_Expectation_almostR2_finite f rv isfe)
    ; intros HH.
    eexists.
    split; try eapply HH.
    now simpl.
  Qed.

    Lemma Rbar_rv_le_pos_fun_part (rv_X1 rv_X2 : Ts -> Rbar) :
      Rbar_rv_le rv_X1 rv_X2 ->
      Rbar_rv_le (fun x : Ts => Rbar_pos_fun_part rv_X1 x) 
                 (fun x : Ts => Rbar_pos_fun_part rv_X2 x).
    Proof.
      intros le12 a.
      unfold Rbar_pos_fun_part, Rbar_max.
      match_destr; match_destr; trivial.
      - simpl; lra.
      - unfold Rbar_le in *.
        match_destr.
        + lra.
        + easy.
      - specialize (le12 a).
        unfold Rbar_le in *.
        match_destr; match_destr_in le12; lra.
    Qed.

    Lemma Rbar_rv_le_neg_fun_part (rv_X1 rv_X2 : Ts -> Rbar) :
      Rbar_rv_le rv_X1 rv_X2 ->
      Rbar_rv_le (fun x : Ts => Rbar_neg_fun_part rv_X2 x) 
                 (fun x : Ts => Rbar_neg_fun_part rv_X1 x).
    Proof.
      intros le12 a.
      unfold Rbar_neg_fun_part, Rbar_max; simpl.
      specialize (le12 a).
      rewrite <- Rbar_opp_le in le12.
      match_destr; match_destr; trivial.
      - simpl; lra.
      - unfold Rbar_le in *.
        match_destr.
        + lra.
        + easy.
      - unfold Rbar_le in *.
        match_destr; match_destr_in le12; lra.
    Qed.

  Lemma Rbar_IsFiniteExpectation_bounded (rv_X1 rv_X2 rv_X3 : Ts -> Rbar)
        {isfe1:Rbar_IsFiniteExpectation rv_X1}
        {isfe2:Rbar_IsFiniteExpectation rv_X3}
    :
      Rbar_rv_le rv_X1 rv_X2 ->
      Rbar_rv_le rv_X2 rv_X3 ->
      Rbar_IsFiniteExpectation rv_X2.
  Proof.
    intros.
    unfold Rbar_IsFiniteExpectation in *.
    unfold Rbar_Expectation in *.
    unfold Rbar_minus' in *.
    match_case_in isfe1
    ; [ intros ? eqq1 | intros eqq1]
    ; rewrite eqq1 in isfe1
    ; try contradiction.
    match_case_in isfe2
    ; [ intros ? eqq2 | intros eqq2]
    ; rewrite eqq2 in isfe2
    ; try contradiction.
    match_destr_in isfe1; try contradiction.
    match_destr_in isfe2; try contradiction.
    apply Finite_Rbar_plus' in eqq1.
    apply Finite_Rbar_plus' in eqq2.
    destruct eqq1 as [eqq1pos eqq1neg].
    destruct eqq2 as [eqq2pos eqq2neg].
    generalize (Rbar_rv_le_pos_fun_part _ _ H0).
    generalize (Rbar_rv_le_neg_fun_part _ _ H).
    intros.
    rewrite Finite_Rbar_opp in eqq1neg.
    rewrite <- (is_finite_Rbar_NonnegExpectation_le _ _ H1); trivial.
    rewrite <- (is_finite_Rbar_NonnegExpectation_le _ _ H2); simpl; trivial.
  Qed.

  
  Lemma Rbar_IsFiniteExpectation_parts f :
    Rbar_IsFiniteExpectation f ->
    Rbar_IsFiniteExpectation (Rbar_pos_fun_part f) /\
    Rbar_IsFiniteExpectation (Rbar_neg_fun_part f).
  Proof.
    unfold Rbar_IsFiniteExpectation; intros.
    unfold Rbar_Expectation, Rbar_minus' in H.
    do 2 erewrite Rbar_Expectation_pos_pofrf.
    destruct (Rbar_NonnegExpectation (Rbar_pos_fun_part f));
      destruct (Rbar_NonnegExpectation (Rbar_neg_fun_part f)); try now simpl in H.
  Qed.

  Lemma finexp_almost_finite rv_X
        {rv : RandomVariable dom Rbar_borel_sa rv_X} :
    Rbar_IsFiniteExpectation rv_X ->
    almost prts (fun x => is_finite (rv_X x)).
  Proof.
    intros.
    destruct (Rbar_IsFiniteExpectation_parts rv_X H).
    generalize (IsFiniteExpectation_nneg_is_almost_finite (Rbar_pos_fun_part rv_X) H0); intros.
    generalize (IsFiniteExpectation_nneg_is_almost_finite (Rbar_neg_fun_part rv_X) H1); intros.
    generalize (Rbar_rv_pos_neg_id rv_X); intros.
    destruct H2 as [? [? ?]].
    destruct H3 as [? [? ?]].
    exists (event_inter x x0).
    split.
    - rewrite <- H3.
      now apply ps_inter_l1.
    - intros ? [??].
      rewrite H4.
      unfold Rbar_rvplus, Rbar_rvopp.
      specialize (H5 x1).
      specialize (H6 x1).
      cut_to H5; trivial; try now apply (event_inter_sub_l x x0 x1).
      cut_to H6; try now apply (event_inter_sub_r x x0 x1).
      rewrite <- H5, <- H6.
      now simpl.
  Qed.

  Lemma finexp_almost_finite_part rv_X
        {rv : RandomVariable dom Rbar_borel_sa rv_X} :
    Rbar_IsFiniteExpectation rv_X ->
    almostR2 prts eq rv_X (Rbar_finite_part rv_X).
  Proof.
    intros.
    destruct (finexp_almost_finite rv_X H) as [? [? ?]].
    exists x.
    split; trivial.
    intros.
    unfold Rbar_finite_part.
    now rewrite <- H1.
  Qed.


  Global Instance finite_part_rv rv_X
         {rv : RandomVariable dom Rbar_borel_sa rv_X} :
    RandomVariable dom borel_sa (Rbar_finite_part rv_X).
  Proof.
    apply measurable_rv.
    now apply Rbar_finite_part_meas.
  Qed.

  Lemma finexp_Rbar_exp_finpart rv_X
        {rv : RandomVariable dom Rbar_borel_sa rv_X} :
    Rbar_IsFiniteExpectation rv_X ->
    Rbar_Expectation rv_X = Expectation (Rbar_finite_part rv_X).
  Proof.
    intros.
    rewrite Expectation_Rbar_Expectation.
    apply Rbar_Expectation_almostR2_proper; trivial.
    - typeclasses eauto.
    - now apply finexp_almost_finite_part.
  Qed.
  
  Lemma Rbar_finexp_finexp rv_X
        {rv : RandomVariable dom Rbar_borel_sa rv_X} :
    Rbar_IsFiniteExpectation rv_X ->
    IsFiniteExpectation prts (Rbar_finite_part rv_X).
  Proof.
    unfold Rbar_IsFiniteExpectation, IsFiniteExpectation; intros.
    now rewrite <- finexp_Rbar_exp_finpart.
  Qed.

  Lemma Rbar_finexp_almost_plus rv_X1 rv_X2
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1} 
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} :    
    Rbar_IsFiniteExpectation rv_X1 ->
    Rbar_IsFiniteExpectation rv_X2 ->
    almostR2 prts eq (Rbar_rvplus rv_X1 rv_X2) (rvplus (Rbar_finite_part rv_X1) (Rbar_finite_part rv_X2)).
  Proof.
    intros.
    destruct (finexp_almost_finite_part rv_X1 H) as [? [? ?]].
    destruct (finexp_almost_finite_part rv_X2 H0) as [? [? ?]].
    exists (event_inter x x0).
    split.
    - rewrite <- H3.
      now apply ps_inter_l1.
    - intros ? [??].
      specialize (H2 x1).
      specialize (H4 x1).
      cut_to H2; trivial; try now apply (event_inter_sub_l x x0 x1).
      cut_to H4; try now apply (event_inter_sub_r x x0 x1).
      unfold Rbar_rvplus.
      rewrite H2, H4.
      now unfold rvplus.
  Qed.

  Global Instance Rbar_is_finite_expectation_isfe_plus 
         (rv_X1 rv_X2 : Ts -> Rbar)
         {rv1 : RandomVariable dom Rbar_borel_sa rv_X1} 
         {rv2 : RandomVariable dom Rbar_borel_sa rv_X2}
         {isfe1: Rbar_IsFiniteExpectation rv_X1}
         {isfe2: Rbar_IsFiniteExpectation rv_X2} :
    Rbar_IsFiniteExpectation (Rbar_rvplus rv_X1 rv_X2).
  Proof.
    intros.
    generalize (Rbar_finexp_finexp rv_X1 isfe1); intros.
    generalize (Rbar_finexp_finexp rv_X2 isfe2); intros.    
    generalize (Rbar_finexp_almost_plus rv_X1 rv_X2 isfe1 isfe2); intros.
    assert (RandomVariable dom borel_sa (Rbar_finite_part rv_X1)) by typeclasses eauto.
    assert (RandomVariable dom borel_sa (Rbar_finite_part rv_X2)) by typeclasses eauto.
    generalize (IsFiniteExpectation_plus prts (Rbar_finite_part rv_X1) (Rbar_finite_part rv_X2) ); intros.
    unfold Rbar_IsFiniteExpectation.
    assert (RandomVariable dom Rbar_borel_sa (rvplus (Rbar_finite_part rv_X1) (Rbar_finite_part rv_X2))) by (apply Real_Rbar_rv; typeclasses eauto).
    generalize (Rbar_Expectation_almostR2_proper  (Rbar_rvplus rv_X1 rv_X2)); intros.
    specialize (H6 (rvplus (Rbar_finite_part rv_X1) (Rbar_finite_part rv_X2))).
    cut_to H6; trivial.
    - rewrite H6.
      rewrite <- Expectation_Rbar_Expectation.
      apply H4.    
    - apply Rbar_rvplus_rv; trivial.
  Qed.

  Lemma Rbar_IsFiniteExpectation_Finite (rv_X:Ts->Rbar)
        {isfe:Rbar_IsFiniteExpectation rv_X} :
    { x : R | Rbar_Expectation rv_X = Some (Finite x)}.
  Proof.
    red in isfe.
    match_destr_in isfe; try contradiction.
    destruct r; try contradiction.
    eauto.
  Qed.

  Definition Rbar_FiniteExpectation (rv_X:Ts->Rbar)
             {isfe:Rbar_IsFiniteExpectation rv_X} : R
    := proj1_sig (Rbar_IsFiniteExpectation_Finite rv_X).


  Ltac Rbar_simpl_finite
    := repeat match goal with
              | [|- context [proj1_sig ?x]] => destruct x; simpl
              | [H: context [proj1_sig ?x] |- _] => destruct x; simpl in H
              end.

  Lemma Rbar_Expectation_sum_finite 
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} :
    forall (e1 e2:R), 
      Rbar_Expectation rv_X1 = Some (Finite e1) ->
      Rbar_Expectation rv_X2 = Some (Finite e2) ->
      Rbar_Expectation (Rbar_rvplus rv_X1 rv_X2) = Some (Finite (e1 + e2)).
  Proof.
    intros.
    assert (isfe1: Rbar_IsFiniteExpectation rv_X1).
    {
      unfold Rbar_IsFiniteExpectation.
      now rewrite H.
    }
    assert (isfe2: Rbar_IsFiniteExpectation rv_X2).
    {
      unfold Rbar_IsFiniteExpectation.
      now rewrite H0.
    }
    generalize (Rbar_finexp_finexp rv_X1 isfe1); intros.
    generalize (Rbar_finexp_finexp rv_X2 isfe2); intros.    
    assert (RandomVariable dom borel_sa (Rbar_finite_part rv_X1)) by typeclasses eauto.
    assert (RandomVariable dom borel_sa (Rbar_finite_part rv_X2)) by typeclasses eauto.
    generalize (Expectation_sum_finite (Rbar_finite_part rv_X1)(Rbar_finite_part rv_X2) e1 e2); intros.
    generalize (Rbar_Expectation_almostR2_proper  (Rbar_rvplus rv_X1 rv_X2)); intros.
    specialize (H6 (rvplus (Rbar_finite_part rv_X1) (Rbar_finite_part rv_X2))).
    rewrite H6.
    - rewrite <- Expectation_Rbar_Expectation.
      apply H5.
      + rewrite Expectation_Rbar_Expectation.
        generalize (Rbar_Expectation_almostR2_proper rv_X1 (Rbar_finite_part rv_X1)); intros.
        rewrite <- H7.
        apply H.
        now apply finexp_almost_finite_part.
      + rewrite Expectation_Rbar_Expectation.
        generalize (Rbar_Expectation_almostR2_proper rv_X2 (Rbar_finite_part rv_X2)); intros.
        rewrite <- H7.
        apply H0.
        now apply finexp_almost_finite_part.        
    - now apply Rbar_rvplus_rv.      
    - typeclasses eauto.
    - now apply Rbar_finexp_almost_plus.
  Qed.

  Lemma pos_part_neg_part_rvplus (f g : Ts -> R) :
    rv_eq
      (rvplus 
         (pos_fun_part (rvplus f g))
         (rvplus
            (neg_fun_part f)
            (neg_fun_part g)))
      (rvplus
         (neg_fun_part (Rbar_rvplus f g))
         (rvplus
            (pos_fun_part f)
            (pos_fun_part g))).
    Proof.
      intro x.
      rv_unfold; simpl.
      unfold Rmax.
      repeat match_destr; lra.
    Qed.


  Lemma pos_part_neg_part_Rbar_rvplus (f g : Ts -> Rbar) :
    (forall x, ex_Rbar_plus (f x) (g x)) ->
    rv_eq
      (Rbar_rvplus 
         (Rbar_pos_fun_part (Rbar_rvplus f g))
         (Rbar_rvplus
            (Rbar_neg_fun_part f)
            (Rbar_neg_fun_part g)))
      (Rbar_rvplus
         (Rbar_neg_fun_part (Rbar_rvplus f g))
         (Rbar_rvplus
            (Rbar_pos_fun_part f)
            (Rbar_pos_fun_part g))).
    Proof.
      intros explus x.
      unfold Rbar_rvplus, Rbar_pos_fun_part, Rbar_neg_fun_part, Rbar_rvopp.
      unfold Rbar_max.
      specialize (explus x).
      destruct (f x); destruct (g x); simpl; repeat match_destr; simpl in *; apply Rbar_finite_eq; try lra.
      Qed.

  Lemma Rbar_NonnegExpectation_pos_part_neg_part_Rbar_rvplus (f g : Ts -> Rbar)
        {rvf : RandomVariable dom Rbar_borel_sa f}
        {rvg : RandomVariable dom Rbar_borel_sa g}  :
    (forall x, ex_Rbar_plus (f x) (g x)) ->
    Rbar_plus 
      (Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvplus f g)))
      (Rbar_plus
          (Rbar_NonnegExpectation (Rbar_neg_fun_part f))
          (Rbar_NonnegExpectation (Rbar_neg_fun_part g))) = 
    Rbar_plus
      (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvplus f g)))
      (Rbar_plus
         (Rbar_NonnegExpectation (Rbar_pos_fun_part f))
         (Rbar_NonnegExpectation (Rbar_pos_fun_part g))).
   Proof.
     intros.
     generalize (pos_part_neg_part_Rbar_rvplus f g H); intros.
     assert
       (Rbar_NonnegExpectation
          (Rbar_rvplus (Rbar_pos_fun_part (Rbar_rvplus f g))
                       (Rbar_rvplus (Rbar_neg_fun_part f) (Rbar_neg_fun_part g))) =
        Rbar_NonnegExpectation
          (Rbar_rvplus (Rbar_neg_fun_part (Rbar_rvplus f g))
                       (Rbar_rvplus (Rbar_pos_fun_part f) (Rbar_pos_fun_part g)))).
     {
       now apply Rbar_NonnegExpectation_ext.
     }
     assert (RandomVariable dom Rbar_borel_sa (Rbar_rvplus f g)).
     {
       now apply Rbar_rvplus_rv.
     }
     rewrite Rbar_NonnegExpectation_plus in H1.
     rewrite Rbar_NonnegExpectation_plus in H1.
     rewrite Rbar_NonnegExpectation_plus in H1.
     rewrite Rbar_NonnegExpectation_plus in H1.
     - apply H1.
     - now apply Rbar_pos_fun_part_rv.
     - now apply Rbar_pos_fun_part_rv.
     - now apply Rbar_neg_fun_part_rv.
     - apply Rbar_rvplus_rv; now apply Rbar_pos_fun_part_rv.
     - now apply Rbar_neg_fun_part_rv.
     - now apply Rbar_neg_fun_part_rv.
     - now apply Rbar_pos_fun_part_rv.
     - apply Rbar_rvplus_rv; now apply Rbar_neg_fun_part_rv.
   Qed.

    Lemma Rbar_IsFiniteNonnegExpectation (X:Ts->Rbar) 
          {posX: Rbar_NonnegativeFunction X}
          {isfeX: Rbar_IsFiniteExpectation X} :
      is_finite (Rbar_NonnegExpectation  X).
    Proof.
      red in isfeX.
      rewrite Rbar_Expectation_pos_pofrf with (nnf:=posX) in isfeX.
      match_destr_in isfeX; try tauto.
      reflexivity.
   Qed.

    Lemma Rbar_pos_sum_bound (rv_X1 rv_X2 : Ts -> Rbar) :
      (forall x, ex_Rbar_plus (rv_X1 x) (rv_X2 x)) ->    
      Rbar_rv_le (Rbar_pos_fun_part (Rbar_rvplus rv_X1 rv_X2))
                 (Rbar_rvplus (Rbar_pos_fun_part rv_X1)
                              (Rbar_pos_fun_part rv_X2)).
    Proof.
      intros explus x.
      unfold Rbar_pos_fun_part, Rbar_rvplus.
      unfold Rbar_max.
      destruct (rv_X1 x); destruct (rv_X2 x); simpl; repeat match_destr; simpl in *; try lra.
    Qed.

    Lemma Rbar_neg_sum_bound (rv_X1 rv_X2 : Ts -> Rbar) :
      (forall x, ex_Rbar_plus (rv_X1 x) (rv_X2 x)) ->    
      Rbar_rv_le (Rbar_neg_fun_part (Rbar_rvplus rv_X1 rv_X2))
                 (Rbar_rvplus (Rbar_neg_fun_part rv_X1)
                              (Rbar_neg_fun_part rv_X2)).
    Proof.
      intros explus x.
      unfold Rbar_neg_fun_part, Rbar_rvplus.
      unfold Rbar_max.
      destruct (rv_X1 x); destruct (rv_X2 x); simpl; repeat match_destr; simpl in *; try lra.
    Qed.

  Lemma Rbar_Expectation_finite
        (rv_X1 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1} :
    Rbar_IsFiniteExpectation rv_X1 ->
    is_finite (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X1)) /\
    is_finite (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X1)).
  Proof.
    intros.
    destruct (Rbar_IsFiniteExpectation_parts rv_X1 H).     
    split; now apply Rbar_IsFiniteNonnegExpectation.
  Qed.    

  Lemma Rbar_Expectation_pinf 
        (rv_X1 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1} :
    Rbar_Expectation rv_X1 = Some p_infty ->
    Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X1) = p_infty /\
    is_finite (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X1)).
  Proof.
    intros.
    unfold Rbar_Expectation in H.
    generalize (Rbar_NonnegExpectation_pos (Rbar_pos_fun_part rv_X1)); intros.         
    generalize (Rbar_NonnegExpectation_pos (Rbar_neg_fun_part rv_X1)); intros.         
    assert (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X1) = p_infty).
    {
      case_eq (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X1)); intros;
        case_eq (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X1)); 
        intros; rewrite H2,H3 in H; simpl in H; try easy.
      now rewrite H3 in H1.
    }
    split; trivial.
    rewrite H2 in H.
    case_eq (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X1)); intros.
    - now simpl.
    - rewrite H3 in H; simpl in H; congruence.
    - rewrite H3 in H1.
      now simpl in H1.
  Qed.

  Lemma Rbar_Expectation_minf 
        (rv_X1 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1} :
    Rbar_Expectation rv_X1 = Some m_infty ->
    is_finite (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X1)) /\
    Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X1) = p_infty.
  Proof.
    intros.
    unfold Rbar_Expectation in H.
    generalize (Rbar_NonnegExpectation_pos (Rbar_pos_fun_part rv_X1)); intros.         
    generalize (Rbar_NonnegExpectation_pos (Rbar_neg_fun_part rv_X1)); intros.         
    assert (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X1) = p_infty).
    {
      case_eq (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X1)); intros;
        case_eq (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X1)); 
        intros; rewrite H2,H3 in H; simpl in H; try easy.
      now rewrite H2 in H0.
    }
    split; trivial.
    rewrite H2 in H.
    case_eq (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X1)); intros.
    - now simpl.
    - rewrite H3 in H; simpl in H; congruence.
    - rewrite H3 in H0.
      now simpl in H0.
  Qed.

  Lemma Rbar_Expectation_sum_finite_left
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} :
    (forall x, ex_Rbar_plus (rv_X1 x) (rv_X2 x)) ->    
    forall (e1:R) (e2:Rbar), 
      Rbar_Expectation rv_X1 = Some (Finite e1) ->
      Rbar_Expectation rv_X2 = Some e2 ->
      Rbar_Expectation (Rbar_rvplus rv_X1 rv_X2) = Some (Rbar_plus e1 e2).
   Proof.
     intros.
     assert (Rbar_IsFiniteExpectation rv_X1).
     {
       unfold Rbar_IsFiniteExpectation.
       now rewrite H0.
     }
     destruct (Rbar_Expectation_finite rv_X1 H2).
     case_eq e2; intros; rewrite H5 in H1.
     - now apply Rbar_Expectation_sum_finite.
     - simpl.
       destruct (Rbar_Expectation_pinf rv_X2 H1).
       unfold Rbar_Expectation.
       assert (is_finite (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvplus rv_X1 rv_X2)))).
       {
         generalize (Rbar_neg_sum_bound rv_X1 rv_X2 H); intros.
         apply (is_finite_Rbar_NonnegExpectation_le _ _ H8).
         rewrite Rbar_NonnegExpectation_plus.
         - rewrite <- H4.
           rewrite <- H7.
           unfold is_finite.
           now simpl.
        - now apply Rbar_neg_fun_part_rv.
        - now apply Rbar_neg_fun_part_rv.
      }
      rewrite <- H8.
      assert (Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvplus rv_X1 rv_X2)) = p_infty).
      {
        generalize ( Rbar_NonnegExpectation_pos_part_neg_part_Rbar_rvplus rv_X1 rv_X2 H); intros.
        rewrite H6 in H9.
        rewrite <- H3 in H9.
        rewrite <- H4 in H9.
        rewrite <- H7 in H9.
        rewrite <- H8 in H9.
        simpl in H9.
        destruct (Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvplus rv_X1 rv_X2))).
        - discriminate H9.
        - tauto.
        - discriminate H9.
      }
      rewrite H9.
      now simpl.
    - simpl.
      destruct (Rbar_Expectation_minf rv_X2 H1).
      unfold Rbar_Expectation.
      assert (is_finite (Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvplus rv_X1 rv_X2)))).
      {
        generalize (Rbar_pos_sum_bound rv_X1 rv_X2 H); intros.
        apply (is_finite_Rbar_NonnegExpectation_le _ _ H8).
        rewrite Rbar_NonnegExpectation_plus.
        - rewrite <- H3.
          rewrite <- H6.
          unfold is_finite.
          now simpl.
        - now apply Rbar_pos_fun_part_rv.
        - now apply Rbar_pos_fun_part_rv.
      }
      rewrite <- H8.
      assert (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvplus rv_X1 rv_X2)) = p_infty).
      {
        generalize ( Rbar_NonnegExpectation_pos_part_neg_part_Rbar_rvplus rv_X1 rv_X2 H); intros.
        rewrite H7 in H9.
        rewrite <- H3 in H9.
        rewrite <- H4 in H9.
        rewrite <- H6 in H9.
        rewrite <- H8 in H9.
        simpl in H9.
        destruct (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvplus rv_X1 rv_X2))).
        - discriminate H9.
        - tauto.
        - discriminate H9.
      }
      rewrite H9.
      now simpl.
   Qed.      

  Lemma Rbar_Expectation_sum_finite_right
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} :
    (forall x, ex_Rbar_plus (rv_X1 x) (rv_X2 x)) ->    
    forall (e1:Rbar) (e2:R), 
      Rbar_Expectation rv_X1 = Some e1 ->
      Rbar_Expectation rv_X2 = Some (Finite e2) ->
      Rbar_Expectation (Rbar_rvplus rv_X1 rv_X2) = Some (Rbar_plus e1 e2).
  Proof.
    intros.
    rewrite Rbar_plus_comm.
    assert (rv_eq (Rbar_rvplus rv_X1 rv_X2) (Rbar_rvplus rv_X2 rv_X1)).
    {
      intro x.
      unfold Rbar_rvplus.
      now rewrite Rbar_plus_comm.
   }
    rewrite (Rbar_Expectation_ext H2).
    apply Rbar_Expectation_sum_finite_left; trivial.
    intro.
    now apply ex_Rbar_plus_comm.
  Qed.

  Lemma Rbar_Expectation_sum
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} :
    (forall x, ex_Rbar_plus (rv_X1 x) (rv_X2 x)) ->    
    forall (e1 e2:Rbar), 
      Rbar_Expectation rv_X1 = Some e1 ->
      Rbar_Expectation rv_X2 = Some e2 ->
      ex_Rbar_plus e1 e2 ->
      Rbar_Expectation (Rbar_rvplus rv_X1 rv_X2) = Some (Rbar_plus e1 e2).
   Proof.
     intros.
     generalize (Rbar_NonnegExpectation_pos_part_neg_part_Rbar_rvplus rv_X1 rv_X2 H); intros.
     destruct e1.
     - now apply Rbar_Expectation_sum_finite_left.
     - destruct e2.
       + now apply Rbar_Expectation_sum_finite_right.
       + destruct (Rbar_Expectation_pinf rv_X1 H0).
         destruct (Rbar_Expectation_pinf rv_X2 H1).
         rewrite H4, H6 in H3.
         rewrite <- H5, <- H7 in H3.
         simpl in H3.
         assert (is_finite (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvplus rv_X1 rv_X2)))).
         {
           generalize (Rbar_neg_sum_bound rv_X1 rv_X2 H); intros.
           apply (is_finite_Rbar_NonnegExpectation_le _ _ H8).
           rewrite Rbar_NonnegExpectation_plus.
           - rewrite <- H5, <- H7.
             now simpl.
           - now apply Rbar_neg_fun_part_rv.
           - now apply Rbar_neg_fun_part_rv.
         }
         rewrite <- H8 in H3.
         simpl in H3.
         assert (Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvplus rv_X1 rv_X2)) = p_infty).
         {
            destruct (Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvplus rv_X1 rv_X2))).
            - discriminate H3.
            - tauto.
            - discriminate H3.
         }
         unfold Rbar_Expectation.
         rewrite H9.
         rewrite <- H8.
         now simpl.
       + now simpl in H2.
     - destruct e2.
       + now apply Rbar_Expectation_sum_finite_right.
       + now simpl in H2.
       + destruct (Rbar_Expectation_minf rv_X1 H0).
         destruct (Rbar_Expectation_minf rv_X2 H1).
         rewrite H5, H7 in H3.
         rewrite <- H4, <- H6 in H3.
         simpl in H3.
         assert (is_finite (Rbar_NonnegExpectation (Rbar_pos_fun_part (Rbar_rvplus rv_X1 rv_X2)))).
         {
           generalize (Rbar_pos_sum_bound rv_X1 rv_X2 H); intros.
           apply (is_finite_Rbar_NonnegExpectation_le _ _ H8).
           rewrite Rbar_NonnegExpectation_plus.
           - rewrite <- H4, <- H6.
             now simpl.
           - now apply Rbar_pos_fun_part_rv.
           - now apply Rbar_pos_fun_part_rv.
         }
         rewrite <- H8 in H3.
         simpl in H3.
         assert (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvplus rv_X1 rv_X2)) = p_infty).
         {
            destruct (Rbar_NonnegExpectation (Rbar_neg_fun_part (Rbar_rvplus rv_X1 rv_X2))).
            - discriminate H3.
            - tauto.
            - discriminate H3.
         }
         unfold Rbar_Expectation.
         rewrite H9.
         rewrite <- H8.
         now simpl.
    Qed.
   
  Lemma Rbar_Expectation_minus_finite 
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} :
    forall (e1 e2:R), 
      Rbar_Expectation rv_X1 = Some (Finite e1) ->
      Rbar_Expectation rv_X2 = Some (Finite e2) ->
      Rbar_Expectation (Rbar_rvminus rv_X1 rv_X2) = Some (Finite (e1 - e2)).
  Proof.
    intros.
    unfold Rbar_rvminus.
    apply Rbar_Expectation_sum_finite; trivial.
    - typeclasses eauto.
    - generalize (Rbar_Expectation_opp rv_X2); intros.
      simpl in H1.
      rewrite H1.
      rewrite H0.
      now simpl.
  Qed.

  Lemma Rbar_FiniteExpectation_Rbar_Expectation (rv_X:Ts->Rbar)
        {isfe:Rbar_IsFiniteExpectation rv_X} : 
    Rbar_Expectation rv_X = Some (Finite (Rbar_FiniteExpectation rv_X)).
  Proof.
    unfold Rbar_IsFiniteExpectation in isfe.
    unfold Rbar_FiniteExpectation.
    unfold Rbar_Expectation.
    now Rbar_simpl_finite.
  Qed.

  Lemma Rbar_FiniteExpectation_plus
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} 
        {isfe1:Rbar_IsFiniteExpectation rv_X1}
        {isfe2:Rbar_IsFiniteExpectation rv_X2} :
    Rbar_FiniteExpectation (Rbar_rvplus rv_X1 rv_X2) =
    Rbar_FiniteExpectation rv_X1 + Rbar_FiniteExpectation rv_X2.
  Proof.
    destruct (Rbar_IsFiniteExpectation_Finite rv_X1) as [r1 e1].
    destruct (Rbar_IsFiniteExpectation_Finite rv_X2) as [r2 e2].
    generalize (Rbar_Expectation_sum_finite rv_X1 rv_X2 r1 r2 e1 e2); trivial
    ; intros HH.
    erewrite Rbar_FiniteExpectation_Rbar_Expectation in e1,e2,HH.
    invcs HH.
    invcs e1.
    invcs e2.
    rewrite H0, H1, H2.
    trivial.
  Qed.

  Lemma Rbar_IsFiniteExpectation_opp (rv_X : Ts -> Rbar)
        {rv : RandomVariable dom Rbar_borel_sa rv_X} 
        {isfe: Rbar_IsFiniteExpectation rv_X} :
    Rbar_IsFiniteExpectation (Rbar_rvopp rv_X).
  Proof.
    generalize (Rbar_Expectation_opp rv_X); intros.
    simpl in H.
    unfold Rbar_IsFiniteExpectation.
    rewrite H.
    unfold Rbar_IsFiniteExpectation in isfe.
    match_destr_in isfe.
    destruct r; tauto.
  Qed.

  Global Instance Rbar_is_finite_expectation_isfe_minus
         (rv_X1 rv_X2 : Ts -> Rbar)
         {rv1 : RandomVariable dom Rbar_borel_sa rv_X1} 
         {rv2 : RandomVariable dom Rbar_borel_sa rv_X2}
         {isfe1: Rbar_IsFiniteExpectation rv_X1}
         {isfe2: Rbar_IsFiniteExpectation rv_X2} :
    Rbar_IsFiniteExpectation (Rbar_rvminus rv_X1 rv_X2).
  Proof.
    unfold Rbar_rvminus.
    apply Rbar_is_finite_expectation_isfe_plus; trivial.
    - typeclasses eauto.
    - now apply Rbar_IsFiniteExpectation_opp.
  Qed.
  
  Lemma Rbar_FiniteExpectation_minus
        (rv_X1 rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2} 
        {isfe1:Rbar_IsFiniteExpectation rv_X1}
        {isfe2:Rbar_IsFiniteExpectation rv_X2} :
    Rbar_FiniteExpectation (Rbar_rvminus rv_X1 rv_X2) =
    Rbar_FiniteExpectation rv_X1 - Rbar_FiniteExpectation rv_X2.
  Proof.
    destruct (Rbar_IsFiniteExpectation_Finite rv_X1) as [r1 e1].
    destruct (Rbar_IsFiniteExpectation_Finite rv_X2) as [r2 e2].
    generalize (Rbar_Expectation_minus_finite rv_X1 rv_X2 r1 r2 e1 e2); trivial
    ; intros HH.
    erewrite Rbar_FiniteExpectation_Rbar_Expectation in e1,e2,HH.
    invcs HH.
    invcs e1.
    invcs e2.
    rewrite H0, H1, H2.
    trivial.
  Qed.

  Lemma Rbar_NonnegExpectation_minus_bounded2 
        (rv_X1 : Ts -> Rbar)
        (rv_X2 : Ts -> Rbar)
        {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
        {rv2 : RandomVariable dom Rbar_borel_sa rv_X2}
        {nnf1:Rbar_NonnegativeFunction rv_X1}
        (c:R)
        (cpos:0 <= c)
        (bounded2: Rbar_rv_le rv_X2 (const c))
        {nnf2:Rbar_NonnegativeFunction rv_X2}
        {nnf12:Rbar_NonnegativeFunction (Rbar_rvminus rv_X1 rv_X2)} :
    Rbar_NonnegExpectation (Rbar_rvminus rv_X1 rv_X2) =
    Rbar_minus (Rbar_NonnegExpectation rv_X1) (Rbar_NonnegExpectation rv_X2).
  Proof.
    assert (isf:forall omega, is_finite (rv_X2 omega)).
    {
      intros omega.
      specialize (bounded2 omega).
      simpl in bounded2.
      eapply bounded_is_finite; eauto.
    } 
    
    assert (isfe:is_finite (Rbar_NonnegExpectation rv_X2)).
    {
      eapply (is_finite_Rbar_NonnegExpectation_le _ (const c)).
      - intros ?.
        unfold const.
        simpl.
        apply bounded2.
      - erewrite (Rbar_NonnegExpectation_pf_irrel _ (nnfconst _ _)).
        rewrite Rbar_NonnegExpectation_const.
        now trivial.
    } 

    assert (minus_rv:RandomVariable dom Rbar_borel_sa (Rbar_rvminus rv_X1 rv_X2)).
    {
      apply Rbar_rvplus_rv; trivial.
      typeclasses eauto.
    } 
    
    generalize (Rbar_NonnegExpectation_plus (Rbar_rvminus rv_X1 rv_X2) rv_X2)
    ; intros eqq1.
    assert (eqq2:rv_eq (Rbar_rvplus (Rbar_rvminus rv_X1 rv_X2) rv_X2) rv_X1).
    { 
      intros a.
      unfold Rbar_rvminus, Rbar_rvopp, Rbar_rvplus in *.
      rewrite <- isf.
      clear eqq1 isf isfe.
      specialize (nnf12 a).
      specialize (nnf1 a).
      specialize (nnf2 a).
      simpl in *.
      destruct (rv_X1 a); simpl in *; try tauto.
      f_equal; lra.
    }
    rewrite (Rbar_NonnegExpectation_ext _ _ eqq2) in eqq1.
    rewrite eqq1.
    generalize (Rbar_NonnegExpectation_pos _ (nnf:=nnf12))
    ; intros nneg12.
    clear eqq1 eqq2.

    now rewrite <- isfe, Rbar_minus_plus_fin.
    Unshelve.
    - intros ?; simpl.
      now unfold const.
    - trivial.
  Qed.

End almost.

Section sa_sub.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Lemma Rbar_NonnegExpectation_prob_space_sa_sub
        (x:Ts->Rbar)
        {pofrf:Rbar_NonnegativeFunction x}
        {rv:RandomVariable dom2 Rbar_borel_sa x}
        
    :
      @Rbar_NonnegExpectation Ts dom2 (prob_space_sa_sub prts sub) x pofrf =
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
    @Rbar_Expectation Ts dom2 (prob_space_sa_sub prts sub)  x =
    @Rbar_Expectation Ts dom prts x.
  Proof.
    generalize ((RandomVariable_sa_sub sub x (rv_x:=rv)))
    ; intros rv1.

    unfold Rbar_Expectation.
    repeat rewrite Rbar_NonnegExpectation_prob_space_sa_sub by typeclasses eauto.
    reflexivity.
  Qed.

  Lemma Rbar_IsFiniteExpectation_prob_space_sa_sub
        (x:Ts->Rbar)
        {rv:RandomVariable dom2 Rbar_borel_sa x}
        {isfe:Rbar_IsFiniteExpectation (prob_space_sa_sub prts sub) x} :
    Rbar_IsFiniteExpectation prts x.
  Proof.
    unfold Rbar_IsFiniteExpectation in *.
    now rewrite Rbar_Expectation_prob_space_sa_sub in isfe by trivial.
  Qed.

  Lemma Rbar_IsFiniteExpectation_prob_space_sa_sub_f
        (x:Ts->Rbar)
        {rv:RandomVariable dom2 Rbar_borel_sa x}
        {isfe:Rbar_IsFiniteExpectation prts x} :
    Rbar_IsFiniteExpectation (prob_space_sa_sub prts sub) x.
  Proof.
    unfold Rbar_IsFiniteExpectation in *.
    now erewrite Rbar_Expectation_prob_space_sa_sub.
  Qed.
  
End sa_sub.
