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
Require Import Measures.
Require Import DiscreteProbSpace.
Require Import Expectation RbarExpectation RandomVariableFinite Dynkin.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

Section ps_product.

  Context {X:Type}.
  Context {Y:X->Type}.
  Context {A:SigmaAlgebra X}.
  Context {B:forall (x:X), SigmaAlgebra (Y x)}.

  Context (psA : ProbSpace A).
  Context (psB : forall (a:X), ProbSpace (B a)).
  Context {psB_rv: forall (b:forall (a:X), event (B a)), RandomVariable A borel_sa (fun a:X => ps_P (b a))}.

  Definition is_measurable_rectangle (ab : pre_event (sigT Y)) : Prop
    := exists (a:event A) (b:forall (x:X), event (B x)),
      (forall (x:X) (y:Y x), ab (existT _ x y) <-> a x /\ b x y).

  Lemma is_measurable_rectangle_none : is_measurable_rectangle pre_event_none.
  Proof.
    exists event_none, (fun _ => event_none).
    unfold event_none, pre_event_none; simpl; split; tauto.
  Qed.
  
  Program Instance PairSemiAlgebra : SemiAlgebra (sigT Y)
    := {|
      salg_in (x:pre_event (sigT Y)) := is_measurable_rectangle x
    |}.
  Next Obligation.
    exists pre_event_none.
    apply is_measurable_rectangle_none.
  Qed.
  Next Obligation.
    destruct H as [a1[b1 HH1]]; destruct H0 as [a2[b2 HH2]].
    exists (event_inter a1 a2).
    exists (fun x => event_inter (b1 x) (b2 x)).
    intros.
    split; intros [HHa HHb].
    - apply HH1 in HHa.
      apply HH2 in HHb.
      repeat split; try apply HHa; try apply HHb.
    - destruct HHa.
      destruct HHb.
      split.
      + apply HH1.
        split; trivial.
      + apply HH2.
        split; trivial.
  Qed.
  Next Obligation.
    destruct H as [a1[b1 ?]].
    exists ([(fun (ab:sigT Y) => (event_complement a1) (projT1 ab) /\ b1 (projT1 ab) (projT2 ab))
        ; (fun ab => a1 (projT1 ab) /\ event_complement (b1 (projT1 ab)) (projT2 ab))
        ; (fun ab => event_complement a1 (projT1 ab) /\ event_complement (b1 (projT1 ab)) (projT2 ab))]).
    split;[ | split].
    - intros [x y].
      destruct a1; simpl.
      unfold pre_list_union, pre_event_complement.
      specialize (H x y).
      apply not_iff_compat in H.
      simpl in *; split.
      + intros ?.
        apply H in H0.
        apply not_and_or in H0.
        destruct H0.
        * destruct (classic (b1 x y)).
          -- eexists; split; [left; reflexivity |].
             now simpl.
          -- eexists; split; [right; right; left; reflexivity |].
             now simpl.
        * destruct (classic (x0 x)).
          -- eexists; split; [right; left; reflexivity |].
             now simpl.
          -- eexists; split; [right; right; left; reflexivity |].
             now simpl.
      + intros [??].
        apply H.
        repeat destruct H0; simpl in *; tauto.
    - repeat constructor; intros ???
      ; destruct a1; destruct b1; simpl in *; firstorder.
    - repeat constructor.
      + exists (event_complement a1), b1; intros; tauto.
      + exists a1, (fun z => (event_complement (b1 z))); intros; tauto.
      + exists (event_complement a1), (fun z => event_complement (b1 z)); intros; tauto.
  Qed.

  (* this is very classic *)
  Definition measurable_rectangle_pm (ab:salg_set PairSemiAlgebra) : Rbar.
  Proof.
    destruct ab as [? HH].
    simpl in HH.
    unfold is_measurable_rectangle in HH.
    apply IndefiniteDescription.constructive_indefinite_description in HH.
    destruct HH as [a HH].
    apply IndefiniteDescription.constructive_indefinite_description in HH.
    destruct HH as [b HH].
    assert (nneg:(NonnegativeFunction (rvmult (EventIndicator (classic_dec a)) (fun x => ps_P (b x))))).
    {
      apply NonNegMult.
      - intros ?.
        apply ps_pos.
      - typeclasses eauto.
    } 
    exact ((NonnegExpectation (Prts:=psA) (rvmult (EventIndicator (classic_dec a)) (fun x => ps_P (b x))))).
  Defined.

  Lemma ps_union_diff {T:Type} {σ:SigmaAlgebra T} (ps:ProbSpace σ) (x y : event σ) :
    ps_P x = ps_P (x \ y) + ps_P (x ∩ y).
  Proof.
    rewrite (union_diff x y) at 1.
    apply ps_disjoint_union.
    firstorder.
  Qed.

  (* well, at least the definition is meaningful and proper *)
  Lemma measurable_rectangle_pm_proper' ab ab2
        (pf1:is_measurable_rectangle ab) (pf2:is_measurable_rectangle ab2) :
    pre_event_equiv ab ab2 ->
    measurable_rectangle_pm (exist _ ab pf1) = measurable_rectangle_pm (exist _ ab2 pf2).
  Proof.
    intros eqq.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    clear e e0.
    rename x into a1.
    rename x1 into a2.
    rename x0 into b1.
    rename x2 into b2.
    assert (eqq1:forall x y, a1 x /\ b1 x y <-> a2 x /\ b2 x y).
    {
      intros.
      rewrite <- i, <- i0.
      apply eqq.
    } 
    clear ab ab2 i i0 eqq pf1 pf2.
    apply NonnegExpectation_ext; intros ?.
    unfold rvscale, rvmult, EventIndicator.
    repeat match_destr.
    + repeat rewrite Rmult_1_l.
      apply ps_proper; intros b.
      split; intros HH
      ; apply eqq1; tauto.
    + destruct (Req_EM_T (ps_P (b1 a)) 0).
      * rewrite e0; lra.
      * destruct (zero_prob_or_witness _ n0) as [b ?].
        generalize (conj e H); intros HH.
        apply eqq1 in HH.
        tauto.
    + destruct (Req_EM_T (ps_P (b2 a)) 0).
      * rewrite e0; lra.
      * destruct (zero_prob_or_witness _ n0) as [b ?].
        generalize (conj e H); intros HH.
        apply eqq1 in HH.
        tauto.
    + lra.
  Qed.
  
  Global Instance measurable_rectangle_pm_proper : Proper (salg_equiv ==> eq) measurable_rectangle_pm.
  Proof.
    intros ???.
    destruct x; destruct y.
    red in H; simpl in H.
    now apply measurable_rectangle_pm_proper'.
  Qed.

  Lemma measurable_rectangle_pm_nneg ab :
    Rbar_le 0 (measurable_rectangle_pm ab).
  Proof.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    apply NonnegExpectation_pos.
  Qed.

  Lemma measurable_rectangle_pm_none :
    measurable_rectangle_pm (exist _ _ is_measurable_rectangle_none) = 0.
  Proof.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    unfold pre_event_none in i.
    rewrite <- (NonnegExpectation_const0 (Prts:=psA)).
    apply NonnegExpectation_ext; intros a; rv_unfold.
    match_destr.
    - destruct (classic_event_none_or_has (x0 a)) as [[??]|?].
      + generalize (conj e0 H); intros HH.
        apply i in HH.
        tauto.
      + rewrite H, ps_none; lra.
    - lra.
  Qed.
  
  Instance measurable_rectangle_pm_semipremeasure : is_semipremeasure measurable_rectangle_pm.
  Proof.
    apply (semipremeasure_with_zero_simpl) with (has_none:=is_measurable_rectangle_none).
    - apply measurable_rectangle_pm_proper.
    - apply measurable_rectangle_pm_nneg.
    - apply measurable_rectangle_pm_none.
    - {
        intros c cdisj pf.
        unfold measurable_rectangle_pm at 1.
        repeat match_destr.
        clear e.

        assert (HH:forall s, exists (ab:(event A * (forall (x:X), event (B x)))), forall x y, (c s) (existT _ x y) <-> fst ab x /\ snd ab x y).
        {
          intros.
          destruct (c s); simpl.
          destruct s0 as [?[??]].
          exists (x2,x3); auto.
        }
        apply choice in HH.
        destruct HH as [cp HH].

        assert (forall n,
                   NonnegativeFunction (rvmult (EventIndicator (classic_dec (fst (cp n))))
                                               (fun a : X => ps_P (snd (cp n) a)))).
        {
          intros ?.
          apply NonNegMult.
          - intros ?.
            apply ps_pos.
          - typeclasses eauto.
        }
        transitivity (ELim_seq (sum_Rbar_n
                                  (fun n : nat =>
                                     Rbar_NonnegExpectation (rvmult (EventIndicator (classic_dec (fst (cp n))))
                                                               (fun a : X => ps_P (snd (cp n) a)))))).
        - {
            rewrite NNExpectation_Rbar_NNExpectation.

            assert (nneg0:forall (a:event A) (b:forall a, event (B a)),
                       Rbar_NonnegativeFunction (rvmult (EventIndicator (classic_dec a))
                                                        (fun a : X => ps_P (b a)))).
            {
              intros ??.
              apply NonNegMult.
              - intros ?.
                apply ps_pos.
              - typeclasses eauto.
            } 
                         
            assert (nneg1:forall (a:event A) (b:forall a, event (B a)), 
                       Rbar_NonnegativeFunction (Rbar_rvmult (EventIndicator (classic_dec a))
                                                             (fun a => Rbar_NonnegExpectation (EventIndicator (classic_dec (b a)))))).
            {
              intros.
              apply Rbar_rvmult_nnf.
              - typeclasses eauto.
              - intros ?.
                apply Rbar_NonnegExpectation_pos.
            }

            assert (eqq1:forall (a:event A) (b:forall a, event (B a)), 
                       Rbar_NonnegExpectation (rvmult (EventIndicator (classic_dec a))
                                                      (fun a : X => ps_P (b a))) =
                         Rbar_NonnegExpectation (Rbar_rvmult (EventIndicator (classic_dec a))
                                                        (fun a => Rbar_NonnegExpectation (EventIndicator (classic_dec (b a)))))).
            {
              intros.
              apply Rbar_NonnegExpectation_ext; intros ?.
              unfold Rbar_rvmult, rvmult; simpl.
              generalize (Expectation_pos_pofrf (EventIndicator (classic_dec (b a0))))
              ; intros HH2.
              rewrite Expectation_EventIndicator in HH2.
              invcs HH2.
              rewrite NNExpectation_Rbar_NNExpectation in H1.
              rewrite <- H1.
              now simpl.
            }

            assert (nneg2inner:forall (a:event A) (b:forall a, event (B a)) x, 
                       Rbar_NonnegativeFunction
                             (Rbar_rvmult
                                (const (Finite (EventIndicator (classic_dec a) x)))
                                (EventIndicator (classic_dec (b x))))).
            {
              intros.
              apply Rbar_rvmult_nnf.
              - apply nnfconst.
                apply EventIndicator_pos.
              - typeclasses eauto.
            } 

            assert (nneg2:forall (a:event A) (b:forall a, event (B a)), 
                     Rbar_NonnegativeFunction
                        (fun x => 
                           Rbar_NonnegExpectation
                             (Rbar_rvmult
                                (const (Finite (EventIndicator (classic_dec a) x)))
                                (EventIndicator (classic_dec (b x)))))).
            {
              intros ???.
              apply Rbar_NonnegExpectation_pos.
            } 

            assert (eqq2:forall (a:event A) (b:forall a, event (B a)), 
                       Rbar_NonnegExpectation (rvmult (EventIndicator (classic_dec a))
                                                      (fun a : X => ps_P (b a))) =
                         Rbar_NonnegExpectation (fun x => 
                                                Rbar_NonnegExpectation
                                                  (Rbar_rvmult
                                                     (const (Finite (EventIndicator (classic_dec a) x)))
                                                     (EventIndicator (classic_dec (b x)))))).
            {
              intros.
              apply Rbar_NonnegExpectation_ext; intros ?.
              erewrite Rbar_NonnegExpectation_scale'.
              - generalize (Expectation_pos_pofrf (EventIndicator (classic_dec (b a0))))
                ; intros HH2.
                rewrite Expectation_EventIndicator in HH2.
                invcs HH2.
                rewrite NNExpectation_Rbar_NNExpectation in H1.
                rewrite <- H1.
                now simpl.
              - typeclasses eauto.
              - apply EventIndicator_pos.
            }
            etransitivity; [etransitivity |]; [| apply (eqq2 x x0) |]
            ; [apply Rbar_NonnegExpectation_ext; reflexivity |].

            etransitivity.
            2: {
              apply ELim_seq_ext; intros.
              apply sum_Rbar_n_proper; [| reflexivity]; intros ?.
              rewrite <- eqq2.
              reflexivity.
            }
            clear eqq1 eqq2.
            {
              erewrite RbarExpectation.Rbar_series_expectation.
              Unshelve.
              shelve.
              - intros.
                eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)).
                + intros ?.
                  apply Rbar_NonnegExpectation_scale'; try typeclasses eauto.
                  apply EventIndicator_pos.
                + apply Rbar_rvmult_rv.
                  * typeclasses eauto.
                  * eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)).
                    -- intros ?.
                       generalize (Expectation_pos_pofrf (EventIndicator (classic_dec (snd (cp n) a))))
                       ; intros HH2.
                       rewrite Expectation_EventIndicator in HH2.
                       invcs HH2.
                       rewrite NNExpectation_Rbar_NNExpectation in H1.
                       rewrite <- H1.
                       reflexivity.
                    -- apply Real_Rbar_rv.
                       apply psB_rv.
              - intros ?.
                apply ELim_seq_nneg; intros.
                apply sum_Rbar_n_nneg_nneg; intros ??.
                apply nneg2.
            } 
            Unshelve.
            apply Rbar_NonnegExpectation_ext; intros x'.
            {
              erewrite Rbar_series_expectation; trivial.
              Unshelve.
              shelve.
              - intros.
                apply Rbar_rvmult_rv; typeclasses eauto.
              - intros ?.
                apply ELim_seq_nneg; intros.
                apply sum_Rbar_n_nneg_nneg; intros ??.
                apply Rbar_rvmult_nnf
                ; apply EventIndicator_pos.
            } 
            Unshelve.
            apply Rbar_NonnegExpectation_ext; intros y.
            unfold Rbar_rvmult, EventIndicator; simpl.
            rewrite <- Lim_seq_sum_Elim.
            (* now we finally have it down to points *)
            {
              destruct (lim_seq_sum_singleton_is_one
                          (fun n0 : nat =>
                             (if classic_dec (fst (cp n0)) x' then 1 else 0) * (if classic_dec (snd (cp n0) x') y then 1 else 0))) as [m HH2].
              - intros.
                repeat match_destr; try lra.
                destruct (HH n1 x' y) as [_ HH1].
                cut_to HH1; [| tauto].
                destruct (HH n2 x' y) as [_ HH2].
                cut_to HH2; [| tauto].
                eelim cdisj; eauto.
              - setoid_rewrite HH2.
                destruct (Req_EM_T ((if classic_dec (fst (cp m)) x' then 1 else 0) * (if classic_dec (snd (cp m) x') y then 1 else 0)) 0).
                + rewrite e in HH2.
                  rewrite e.
                  f_equal.
                  repeat match_destr; simpl; try lra.
                  destruct (i x' y) as [_ HH3].
                  cut_to HH3; [| tauto].
                  destruct HH3 as [n cpn].
                  apply HH in cpn.
                  destruct cpn as [cpnx cpny].

                  
                  
                  assert (HH4:forall n,
                             Finite (sum_n
                                       (fun n0 : nat =>
                                          (if classic_dec (fst (cp n0)) x' then 1 else 0) *
                                            (if classic_dec (snd (cp n0) x') y then 1 else 0)) n) = Finite 0).
                  {
                    intros.
                    apply Rbar_le_antisym.
                    - rewrite <- HH2.
                      apply Lim_seq_increasing_le; intros.
                      apply sum_n_pos_incr; intros; try lia.
                      repeat match_destr; lra.
                    - apply sum_n_nneg; intros.
                      repeat match_destr; lra.
                  }
                  specialize (HH4 n).
                  apply (f_equal real) in HH4; simpl in HH4.
                  destruct n.
                  * rewrite sum_O in HH4.
                    repeat match_destr_in HH4; invcs HH4; try tauto.
                  * rewrite sum_Sn in HH4.
                    unfold plus in HH4; simpl in *.
                    rewrite Rplus_comm in HH4.
                    apply Rplus_eq_0_l in HH4.
                    -- repeat match_destr_in HH4; try tauto.
                    -- repeat match_destr; lra.
                    -- apply sum_n_nneg; intros.
                       repeat match_destr; lra.
                + repeat match_destr_in n; try lra.
                  destruct (i x' y) as [[??] _].
                  * exists m.
                    apply HH; tauto.
                  * repeat match_destr; tauto.
            }
          }             
        - apply ELim_seq_ext; intros.
          unfold sum_Rbar_n.
          f_equal.
          apply map_ext; intros.
          rewrite <- NNExpectation_Rbar_NNExpectation.

          unfold measurable_rectangle_pm.
          specialize (HH a).
          repeat match_destr.
          simpl in HH.
          assert (eqq:forall a1 b1, fst (cp a) a1 /\ snd (cp a) a1 b1 <-> x2 a1 /\ x3 a1 b1).
          {
            intros.
            etransitivity.
            - symmetry; apply HH.
            - apply i0.
          }
          clear HH i0 e.
          apply NonnegExpectation_ext; intros ?.
          rv_unfold.
          revert eqq; clear; intros eqq.
          repeat match_destr.
          + repeat rewrite Rmult_1_l.
            apply ps_proper; intros b.
            split; intros HH.
            * generalize (conj e HH); intros HH2.
              apply eqq in HH2; tauto.
            * generalize (conj e0 HH); intros HH2.
              apply eqq in HH2; tauto.
          + rewrite Rmult_0_l.
            destruct (classic_event_none_or_has (snd (cp a) a0)) as [[??]|?]; [| eauto].
            * generalize (conj e H); intros HH2.
              apply eqq in HH2; tauto.
            * rewrite H, ps_none; lra.
          + rewrite Rmult_0_l.
            destruct (classic_event_none_or_has (x3 a0)) as [[??]|?]; [| eauto].
            * generalize (conj e H); intros HH2.
              apply eqq in HH2; tauto.
            * rewrite H, ps_none; lra.
          + lra.
      } 
  Qed.

  Definition product_measure := semi_μ measurable_rectangle_pm.

  Instance product_measure_is_measurable_large :
    is_measure (σ:= semi_σ is_measurable_rectangle_none
                           measurable_rectangle_pm
                           measurable_rectangle_pm_none
               ) product_measure
    := semi_μ_measurable _ _ _.
  
  Global Instance product_measure_is_measurable :
    is_measure (σ:=dep_product_sa A B) product_measure.
  Proof.
    generalize product_measure_is_measurable_large; intros HH.
    assert (sub:sa_sub (dep_product_sa A B)
                       (semi_σ is_measurable_rectangle_none
                               measurable_rectangle_pm
                               measurable_rectangle_pm_none
           )).
    {
      unfold dep_product_sa; intros ?.
      apply generated_sa_minimal; simpl; intros.
      apply semi_σ_in.
      simpl.
      destruct H as [?[?[?[??]]]].
      red.
      exists (exist _ _ H).
      exists (fun (a:X) => match classic_dec x1 a with
                   | left pf => exist _ _ (H0 _ pf)
                   | right _ => event_none
                   end).
      intros.
      simpl.
      etransitivity; try eapply H1; simpl.
      match_destr; tauto.
    } 
    apply (is_measure_proper_sub _ _ sub) in HH.
    now simpl in HH.
  Qed.

  Instance product_measure_nneg (a:event A) (b:forall a, event (B a)) :
    NonnegativeFunction (rvmult (EventIndicator (classic_dec a)) (fun x => ps_P (b x))).
  Proof.
    apply NonNegMult.
    - intros ?.
      apply ps_pos.
    - typeclasses eauto.
  Qed.
  
  Theorem product_measure_product (a:event A) (b:forall a, event (B a)) :
    product_measure (fun '(existT x y) => a x /\ b x y) =
      (NonnegExpectation (Prts:=psA) (rvmult (EventIndicator (classic_dec a)) (fun x => ps_P (b x)))).
  Proof.
    unfold product_measure.
    generalize (semi_μ_λ is_measurable_rectangle_none _ measurable_rectangle_pm_none)
    ; intros HH.
    assert (pin:salg_in (fun '(existT x1 y) => a x1 /\ b x1 y)).
    {
      simpl.
      exists a; exists b; tauto.
    }
    specialize (HH (exist _ _ pin)).
    simpl in *.
    rewrite HH.
    repeat match_destr.
    apply NonnegExpectation_ext; intros ?.
    rv_unfold.
    repeat match_destr.
    - repeat rewrite Rmult_1_l.
      apply ps_proper.
      intros ?; simpl.
      specialize (i a0 x1); tauto.
    - rewrite Rmult_0_l.
      destruct (classic_event_none_or_has (x0 a0)) as [[??]|?]; [| eauto].
      + generalize (conj e0 H); intros HH2.
        apply i in HH2; tauto.
      + rewrite H, ps_none; lra.
    - rewrite Rmult_0_l.
      destruct (classic_event_none_or_has (b a0)) as [[??]|?]; [| eauto].
      + generalize (conj e0 H); intros HH2.
        apply i in HH2; tauto.
      + rewrite H, ps_none; lra.
    - lra.
  Qed.

  Global Instance dep_product_ps : ProbSpace (dep_product_sa A B).
  Proof.
    apply (measure_all_one_ps product_measure).
    generalize (product_measure_product Ω (fun _ => Ω))
    ; intros HH.
    etransitivity; [etransitivity |]; [| apply HH |].
    - unfold product_measure.
      assert (pre_eqq:pre_event_equiv
                        pre_Ω
                        (fun '(existT x y) => @pre_Ω X x /\ @pre_Ω (Y x) y)).
      {
        intros [??]; tauto.
      }
      assert (sa:sa_sigma (SigmaAlgebra:=dep_product_sa A B) (fun '(existT x y) => @pre_Ω X x /\ @pre_Ω (Y x) y)).
      { 
        rewrite <- pre_eqq.
        apply sa_all.
      }
      apply (measure_proper (σ:=dep_product_sa A B) (μ:=product_measure) Ω (exist _ _ sa)).
      now red; simpl.
    - assert (0 <= 1) by lra.
      rewrite <- (NonnegExpectation_const (Prts:=psA) R1) with (nnc:=H).
      apply NonnegExpectation_ext; intros ?.
      rv_unfold.
      rewrite ps_one.
      match_destr.
      + lra.
      + elim n; red; apply I.
  Defined.

  Theorem dep_product_sa_product (a:event A) (b:forall a, event (B a)) :
    ps_P (ProbSpace:=dep_product_ps) (dep_product_sa_event a b) =
      (NonnegExpectation (Prts:=psA) (rvmult (EventIndicator (classic_dec a)) (fun x => ps_P (b x)))).
  Proof.
    simpl.
    now rewrite product_measure_product; simpl.
  Qed.

  Lemma pre_event_set_dep_product_pi : Pi_system (pre_event_set_dep_product (@sa_sigma _ A) (fun a => @sa_sigma _ (B a))).
  Proof.
    unfold pre_event_set_dep_product; intros ?[?[?[?[??]]]]?[?[?[?[??]]]].
    exists (pre_event_inter x x1).
    exists (fun a => pre_event_inter (x0 a) (x2 a)).
    split; [| split].
    - now apply sa_inter.
    - intros ? [??].
      apply sa_inter; auto.
    - rewrite H1, H4.
      unfold pre_event_inter; simpl; intros [??].
      tauto.
  Qed.
            
  (* dep_product_ps is the unique probability space that preserves the product/integration rule. *)
  Theorem dep_product_ps_unique (ps:ProbSpace (dep_product_sa A B)) :
    (forall a b, ps_P (ProbSpace:=ps) (dep_product_sa_event a b) =
               (NonnegExpectation (Prts:=psA) (rvmult (EventIndicator (classic_dec a)) (fun x => ps_P (b x))))) ->
    forall x, ps_P (ProbSpace:=ps) x = ps_P (ProbSpace:=dep_product_ps) x.
  Proof.
    intros.
    apply pi_prob_extension_unique.
    - apply pre_event_set_dep_product_pi.
    - intros.
      assert (exists x y, event_equiv (generated_sa_base_event Ca) (dep_product_sa_event x y)).
      {
        destruct Ca as [?[?[?[??]]]]; simpl.
        exists (exist _ x0 s).
        exists (fun (a:X) => match classic_dec x0 a with
                     | left pf => exist _ _ (s0 _ pf)
                     | right _ => event_none
                     end).
        intros [??]; simpl.
        etransitivity; try apply e.
        simpl.
        match_destr; tauto.
      } 
      destruct H0 as [?[? eqq]].
      repeat rewrite eqq.
      rewrite H.
      now rewrite dep_product_sa_product.
  Qed.

End ps_product.
