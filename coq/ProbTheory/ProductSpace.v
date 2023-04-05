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

Require Import utils.Utils DVector PushNeg.
Import ListNotations.
Require Export Event SigmaAlgebras ProbSpace.
Require Export RandomVariable VectorRandomVariable.
Require Import IndefiniteDescription ClassicalDescription.
Require Import Measures.
Require Import Dynkin.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope prob.

Section measure_product.

  Context {X Y:Type}.
  Context {A:SigmaAlgebra X}.
  Context {B:SigmaAlgebra Y}.

  Definition is_measurable_rectangle (ab : pre_event (X*Y)) : Prop
    := exists (a:event A) (b:event B), forall x y, ab (x,y) <-> a x /\ b y.

  Lemma is_measurable_rectangle_none : is_measurable_rectangle pre_event_none.
  Proof.
    exists event_none, event_none.
    unfold event_none, pre_event_none; simpl; tauto.
  Qed.
  
  Program Instance PairSemiAlgebra : SemiAlgebra (X*Y)
    := {|
      salg_in (x:pre_event (X*Y)) := is_measurable_rectangle x
    |}.
  Next Obligation.
    exists pre_Ω.
    exists Ω, Ω; intros; unfold Ω, pre_Ω; simpl.
    tauto.
  Qed.
  Next Obligation.
    destruct H as [a1[b1 ?]]; destruct H0 as [a2[b2 ?]].
    exists (event_inter a1 a2).
    exists (event_inter b1 b2).
    intros.
    split; intros [??].
    - apply H in H1.
      apply H0 in H2.
      repeat split; try apply H1; try apply H2.
    - destruct H1.
      destruct H2.
      split.
      + apply H.
        split; trivial.
      + apply H0.
        split; trivial.
  Qed.
  Next Obligation.
    destruct H as [a1[b1 ?]].
    exists ([(fun ab => event_complement a1 (fst ab) /\ b1 (snd ab))
        ; (fun ab => a1 (fst ab) /\ event_complement b1 (snd ab))
        ; (fun ab => event_complement a1 (fst ab) /\ event_complement b1 (snd ab))]).
    split;[ | split].
    - intros [x y].
      destruct a1; destruct b1; simpl.
      unfold pre_list_union, pre_event_complement.
      specialize (H x y).
      apply not_iff_compat in H.
      simpl in *; split.
      + intros ?.
        apply H in H0.
        apply not_and_or in H0.
        destruct H0.
        * destruct (classic (x1 y)).
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
      + exists a1, (event_complement b1); intros; tauto.
      + exists (event_complement a1), (event_complement b1); intros; tauto.
  Qed.

  Context (α : event A -> Rbar) (meas_α : is_measure α).
  Context (β : event B -> Rbar) (meas_β : is_measure β).
  

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
    exact (Rbar_mult (α a) (β b)).
  Defined.

  (* well, at least the definition is meaningful and proper *)
  Lemma measurable_rectangle_pm_proper' ab ab2
        (pf1:is_measurable_rectangle ab) (pf2:is_measurable_rectangle ab2) :
    pre_event_equiv ab ab2 ->
    measurable_rectangle_pm (exist _ ab pf1) = measurable_rectangle_pm (exist _ ab2 pf2).
  Proof.
    intros eqq.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    destruct e as [??].
    destruct e0 as [??].
    destruct pf1 as [? [??]].
    destruct pf2 as [? [??]].

    destruct (classic_event_none_or_has x) as [[??]|?].
    - destruct (classic_event_none_or_has x0) as [[??]|?].
      + destruct (i x9 x10) as [_ ?].
        cut_to H5; [| tauto].
        apply eqq in H5.
        apply i0 in H5.
        destruct H5.
        f_equal.
        * apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i c x10).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i0 in H7.
             tauto.
          -- specialize (i0 c x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i in H7.
             tauto.
        * apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i x9 c).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i0 in H7.
             tauto.
          -- specialize (i0 x9 c).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i in H7.
             tauto.
      + rewrite H4.
        destruct (classic_event_none_or_has x2) as [[??]|?].
        * destruct (classic_event_none_or_has x1) as [[??]|?].
          -- specialize (i0 x11 x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             apply eqq in H7.
             apply i in H7.
             destruct H7 as [_ HH].
             apply H4 in HH.
             red in HH; tauto.
          -- rewrite H6.
             repeat rewrite measure_none.
             now rewrite Rbar_mult_0_l, Rbar_mult_0_r.
        * rewrite H5.
          repeat rewrite measure_none.
          now repeat rewrite Rbar_mult_0_r.
    - rewrite H3.
      destruct (classic_event_none_or_has x1) as [[??]|?].
      + destruct (classic_event_none_or_has x2) as [[??]|?].
        * destruct (i0 x9 x10) as [_ ?].
          cut_to H6; [| tauto].
          apply eqq in H6.
          apply i in H6.
          destruct H6 as [HH _].
          apply H3 in HH.
          red in HH; tauto.
        * rewrite H5.
          repeat rewrite measure_none.
          now rewrite Rbar_mult_0_l, Rbar_mult_0_r.
      + rewrite H4.
        repeat rewrite measure_none.
        now repeat rewrite Rbar_mult_0_l.
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
    apply Rbar_mult_nneg_compat; apply measure_nneg.
  Qed.

  Lemma measurable_rectangle_pm_none :
    measurable_rectangle_pm (exist _ _ is_measurable_rectangle_none) = 0.
  Proof.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    destruct (classic_event_none_or_has x) as [[??]|?].
    - destruct (classic_event_none_or_has x0) as [[??]|?].
      + destruct (i x1 x2) as [_ HH].
        cut_to HH; [| tauto].
        now red in HH.
      + rewrite H0.
        now rewrite measure_none, Rbar_mult_0_r.
    - rewrite H.
      now rewrite measure_none, Rbar_mult_0_l.
  Qed.

  (* this lemma could be used to clean up some of the above *)
  Lemma measurable_rectangle_eq_decompose
        (fx:event A) (fy:event B) (gx:event A) (gy:event B) :
    (forall (x : X) (y : Y), fx x /\ fy y <-> gx x /\ gy y) ->
    ((event_equiv fx ∅ \/ event_equiv fy ∅) /\ (event_equiv gx ∅ \/ event_equiv gy ∅))
    \/ (event_equiv fx gx /\ event_equiv fy gy).
  Proof.
    intros.
    destruct (classic_event_none_or_has fx) as [[??]|?].
    - destruct (classic_event_none_or_has fy) as [[??]|?].
      + right.
        split; intros c; split; intros HH.
        * destruct (H c x0) as [[??] _]; tauto.
        * destruct (H c x0) as [_ [??]]; trivial.
          split; trivial.
          destruct (H x x0) as [[??] _]; tauto.
        * destruct (H x c) as [[??] _]; tauto.
        * destruct (H x c) as [_ [??]]; trivial.
          split; trivial.
          destruct (H x x0) as [[??] _]; tauto.
      + destruct (classic_event_none_or_has gx) as [[??]|?]; [| eauto].
        destruct (classic_event_none_or_has gy) as [[??]|?]; [| eauto].
        destruct (H x0 x1) as [_ [??]]; [tauto |].
        apply H1 in H5; tauto.
    - left.
      destruct (classic_event_none_or_has gx) as [[??]|?]; [| eauto].
      destruct (classic_event_none_or_has gy) as [[??]|?]; [| eauto].
      destruct (H x x0) as [_ [??]]; [tauto |].
      apply H0 in H3; tauto.
  Qed.      

  Definition product_measure := semi_μ measurable_rectangle_pm.

  (* This hypothesis is true, however all the proofs that I have found use 
     the MCT (monotone convergence theorom) over the measure integral, which we have not defined
     in general.
     However, our immediate goal is to define the product of probability spaces,
     where we have defined it (Expectation), and proven the MCT.
     So for now, we leave it as an obligation, which we will discharge in the context we care about
   *)
  Definition measure_rectangle_pm_additive_Hyp :=
             forall B0 : nat -> salg_set PairSemiAlgebra,
  pre_collection_is_pairwise_disjoint (fun x : nat => B0 x) ->
  forall pf : salg_in (pre_union_of_collection (fun x : nat => B0 x)),
  measurable_rectangle_pm (exist salg_in (pre_union_of_collection (fun x : nat => B0 x)) pf) =
    ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => measurable_rectangle_pm (B0 n)) i).

  Context (Hyp : measure_rectangle_pm_additive_Hyp).
          
  Instance measurable_rectangle_pm_semipremeasure : is_semipremeasure measurable_rectangle_pm.
  Proof.
    apply (semipremeasure_with_zero_simpl) with (has_none:=is_measurable_rectangle_none).
    - apply measurable_rectangle_pm_proper.
    - apply measurable_rectangle_pm_nneg.
    - apply measurable_rectangle_pm_none.
    - exact Hyp.
  Qed.

  Instance product_measure_proper : Proper (pre_event_equiv ==> eq) product_measure.
  Proof.
    intros ???.
    unfold product_measure.
    eapply semi_μ_proper; trivial.
    - apply measurable_rectangle_pm_semipremeasure.
    - apply measurable_rectangle_pm_none.
  Qed.    

  Instance product_measure_is_measurable_large :
    is_measure (σ:= semi_σ is_measurable_rectangle_none
                           measurable_rectangle_pm
                           measurable_rectangle_pm_none
               ) product_measure
    := semi_μ_measurable _ _ _.

  (* we can cut down to the (possibly smaller)
     generated sigma algebra *)
  Global Instance product_measure_is_measurable :
    is_measure (σ:=product_sa A B) product_measure.
  Proof.
    generalize product_measure_is_measurable_large; intros HH.
    assert (sub:sa_sub (product_sa A B)
                       (semi_σ is_measurable_rectangle_none
                               measurable_rectangle_pm
                               measurable_rectangle_pm_none
           )).
    {
      unfold product_sa; intros ?.
      apply generated_sa_minimal; simpl; intros.
      apply semi_σ_in.
      simpl.
      destruct H as [?[?[?[??]]]].
      red.
      exists (exist _ _ H).
      exists (exist _ _ H0); intros.
      apply H1.
    } 
    apply (is_measure_proper_sub _ _ sub) in HH.
    now simpl in HH.
  Qed.

  Theorem product_measure_product (a:event A) (b:event B) :
    product_measure (fun '(x,y) => a x /\ b y) = Rbar_mult (α a) (β b).
  Proof.
    unfold product_measure.
    generalize (semi_μ_λ is_measurable_rectangle_none _ measurable_rectangle_pm_none)
    ; intros HH.
    assert (pin:salg_in (fun '(x1, y) => a x1 /\ b y)).
    {
      simpl.
      exists a; exists b; tauto.
    }
    specialize (HH (exist _ _ pin)).
    simpl in *.
    rewrite HH.
    repeat match_destr.
    apply measurable_rectangle_eq_decompose in i.
    destruct i as [[[?|?][?|?]]|[??]]
    ; try solve [
          rewrite H, H0
          ; repeat rewrite measure_none
          ; repeat rewrite Rbar_mult_0_r
          ; repeat rewrite Rbar_mult_0_l; trivial].      
  Qed.
  
End measure_product.

Require Import RandomVariableFinite.
Require Import RbarExpectation.
Require Import Almost.
Require Import RandomVariableLpR.
Require Import ConditionalExpectation.

Section ps_product.
  Context {X Y:Type}.
  Context {A:SigmaAlgebra X}.
  Context {B:SigmaAlgebra Y}.

  Context (ps1 : ProbSpace A).
  Context (ps2 : ProbSpace B).
  
  Lemma product_measure_Hyp_ps :
    measure_rectangle_pm_additive_Hyp (ps_P (σ:=A)) (ps_P (σ:=B)).
  Proof.
    red.
    intros c cdisj pf.

    assert (HH:forall s, exists (ab:(event A * event B)), forall x y, (c s) (x,y) <-> fst ab x /\ snd ab y).
    {
      intros.
      destruct (c s); simpl.
      destruct s0 as [?[??]].
      exists (x0,x1); auto.
    }
    apply choice in HH.
    destruct HH as [cp HH].
    pose (α := (ps_P (σ:=A))).
    pose (β := (ps_P (σ:=B))).
    transitivity (ELim_seq (sum_Rbar_n
                              (fun n : nat =>
                                 (Rbar_mult (α (fst (cp n))) (β (snd (cp n))))))).
    - unfold measurable_rectangle_pm.
      repeat match_destr.
      clear e.
      rename x into a.
      rename x0 into b.
      assert (forall x y, (exists n, (fst (cp n) x) /\ snd (cp n) y) <-> a x /\ b y).
      {
        unfold pre_union_of_collection in i.
        intros.
        rewrite <- (i x y).
        split; intros [??]
        ; apply HH in H; eauto.
      }

      unfold α, β in *.
      simpl.
      Existing Instance IsFiniteExpectation_simple.
      
      assert (eqq1:forall (a:event A) (b:event B),
                 Finite ((ps_P a) * (ps_P b)) =
                   Rbar_mult (Rbar_NonnegExpectation (EventIndicator (classic_dec a))) (Rbar_NonnegExpectation (EventIndicator (classic_dec b)))).
      {
        intros.
        generalize (Expectation_pos_pofrf (EventIndicator (classic_dec a0)))
        ; intros HH1.
        generalize (Expectation_pos_pofrf (EventIndicator (classic_dec b0)))
        ; intros HH2.
        rewrite Expectation_EventIndicator in HH1.
        rewrite Expectation_EventIndicator in HH2.
        invcs HH1; invcs HH2.
        rewrite NNExpectation_Rbar_NNExpectation in H1.
        rewrite NNExpectation_Rbar_NNExpectation in H2.
        rewrite <- H1, <- H2.
        now simpl.
      }

      assert (poffrf:forall (a:event A) (b:event B),
               Rbar_NonnegativeFunction (Rbar_rvmult (const (Rbar_NonnegExpectation (EventIndicator (classic_dec a))))
                                                   (EventIndicator (classic_dec b))
             )).
      {
        intros.
        apply Rbar_rvmult_nnf.
        - intros ?.
          apply Rbar_NonnegExpectation_pos.
        - typeclasses eauto.
      }       
      assert (eqq2:forall (a:event A) (b:event B),
                 Finite ((ps_P a) * (ps_P b)) =
                   Rbar_NonnegExpectation 
                                     (Rbar_rvmult (const (Rbar_NonnegExpectation (EventIndicator (classic_dec a))))
                                                   (EventIndicator (classic_dec b))
             )).
      {
        intros; rewrite eqq1.
        erewrite Rbar_NonnegExpectation_scale'.
        - reflexivity.
        - typeclasses eauto.
        - apply Rbar_NonnegExpectation_pos.
      } 

      assert (eqq3': forall (a:event A) (b:event B),
                 rv_eq
                   (Rbar_rvmult (const (Rbar_NonnegExpectation (EventIndicator (classic_dec a))))
                                (fun x : Y => EventIndicator (classic_dec b) x))

                       (fun y : Y =>
                          Rbar_NonnegExpectation (fun x : X => EventIndicator (classic_dec b) y * EventIndicator (classic_dec a) x))).
      {
        intros ???.
        unfold Rbar_rvmult, const.
        repeat rewrite NNExpectation_Rbar_NNExpectation.
        simpl.
        rewrite Rbar_mult_comm.
        erewrite <- Rbar_NonnegExpectation_scale'; trivial.
        - typeclasses eauto.
        - unfold EventIndicator; match_destr; simpl; lra.
      } 

      assert (pos2:forall (a:event A) (b:event B),
               Rbar_NonnegativeFunction (fun y => Rbar_NonnegExpectation (fun x => (EventIndicator (classic_dec b) y) * (EventIndicator (classic_dec a) x)))).
      {
        intros ???.
        apply Rbar_NonnegExpectation_pos.
      }

      assert (forall (a:event A) (b:event B) y,
                 Rbar_NonnegativeFunction (fun x => (EventIndicator (classic_dec b) y) * (EventIndicator (classic_dec a) x))).
      {
        intros ????.
        unfold EventIndicator; repeat match_destr; simpl; lra.
      } 

      assert (eqq3:forall (a:event A) (b:event B),
                 Finite ((ps_P a) * (ps_P b)) =
                   Rbar_NonnegExpectation 
                                     (fun y => Rbar_NonnegExpectation (fun x => (EventIndicator (classic_dec b) y) * (EventIndicator (classic_dec a) x)))).
                            
      {
        intros; rewrite eqq2.
        f_equal.
        apply Rbar_NonnegExpectation_ext.
        apply eqq3'.
      } 

      clear eqq1 eqq2 eqq3'.
      rewrite eqq3.
      symmetry.
      etransitivity.
      {
        apply ELim_seq_ext; intros ?.
        apply sum_Rbar_n_proper; [| reflexivity]; intros ?.
        rewrite eqq3.
        reflexivity.
      }

      {
        assert (rvf: forall n, RandomVariable B Rbar_borel_sa
                                    (fun y : Y =>
                                       Rbar_NonnegExpectation
                       (fun x : X =>
                          EventIndicator (classic_dec (snd (cp n))) y * EventIndicator (classic_dec (fst (cp n))) x))).
        {
          intros n.
          eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)
                 _ (fun y : Y =>
                       Rbar_NonnegExpectation
                         (Rbar_rvmult (const (Finite (EventIndicator (classic_dec (snd (cp n))) y))) (EventIndicator (classic_dec (fst (cp n))))))).
          { intros ?; reflexivity. }
          eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)
                                        _ (fun y : Y =>
                                             (Rbar_mult (EventIndicator (classic_dec (snd (cp n))) y)
                       (Rbar_NonnegExpectation
                          (EventIndicator (classic_dec (fst (cp n)))))))).
          {
            intros ?.
            apply Rbar_NonnegExpectation_scale'.
            - typeclasses eauto.
            - unfold EventIndicator; simpl; match_destr; lra.
          }
          apply Rbar_rvmult_rv.
          - typeclasses eauto.
          - apply rvconst.
        }
        erewrite Rbar_series_expectation; trivial.
        Unshelve.
        shelve.
        - intros ?.
          apply ELim_seq_nneg; intros.
          apply sum_Rbar_n_nneg_nneg; intros ??.
          apply Rbar_NonnegExpectation_pos.
      }
      Unshelve.
      apply Rbar_NonnegExpectation_ext; intros y.
      {
        erewrite Rbar_series_expectation; trivial.
        Unshelve.
        shelve.
        - intros.
          typeclasses eauto.
        - intros ?.
          apply ELim_seq_nneg; intros.
          apply sum_Rbar_n_nneg_nneg; intros ??.
          unfold EventIndicator; simpl; repeat match_destr; lra.
      }
      Unshelve.
      apply Rbar_NonnegExpectation_ext; intros x.
      unfold EventIndicator.
      rewrite <- Lim_seq_sum_Elim.
      (* now we finally have it down to points *)
      {
        destruct (lim_seq_sum_singleton_is_one
                    (fun n0 : nat =>
                       (if classic_dec (snd (cp n0)) y then 1 else 0) * (if classic_dec (fst (cp n0)) x then 1 else 0))) as [m HH2].
        - intros.
          repeat match_destr; try lra.
          destruct (HH n1 x y) as [_ HH1].
          cut_to HH1; [| tauto].
          destruct (HH n2 x y) as [_ HH2].
          cut_to HH2; [| tauto].
          eelim cdisj; eauto.
        - setoid_rewrite HH2.
          f_equal.
          destruct (Req_EM_T ((if classic_dec (snd (cp m)) y then 1 else 0) * (if classic_dec (fst (cp m)) x then 1 else 0)) 0).
          + rewrite e in HH2.
            rewrite e.
            repeat match_destr; simpl; try lra.
            destruct (H x y) as [_ HH3].
            cut_to HH3; [| tauto].
            destruct HH3 as [n [cpnx cpny]].
            
            assert (HH4:forall n,
                       Finite (sum_n
                          (fun n0 : nat =>
                             (if classic_dec (snd (cp n0)) y then 1 else 0) *
                               (if classic_dec (fst (cp n0)) x then 1 else 0)) n) = Finite 0).
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
            assert ((if classic_dec (snd (cp n)) y then 1 else 0) * (if classic_dec (fst (cp n)) x then 1 else 0) = 0).
            {
              specialize (HH4 n).
              apply (f_equal real) in HH4; simpl in HH4.
            destruct n.
            - now rewrite sum_O in HH4.
            - rewrite sum_Sn in HH4.
              unfold plus in HH4; simpl in *.
              rewrite Rplus_comm in HH4.
              apply Rplus_eq_0_l in HH4; trivial.
              + repeat match_destr; lra.
              + apply sum_n_nneg; intros.
                repeat match_destr; lra.
            }
            repeat match_destr_in H1; try tauto; lra.
          + repeat match_destr_in n; try lra.
            destruct (H x y) as [HH3 _].
            cut_to HH3;[| eauto].
            repeat match_destr; tauto.
      }
    - apply ELim_seq_ext; intros.
      unfold sum_Rbar_n.
      f_equal.
      apply map_ext; intros.
      unfold measurable_rectangle_pm.
      clear n.
      specialize (HH a).
      repeat match_destr.
      simpl in HH.
      assert (eqq:forall a1 b1, fst (cp a) a1 /\ snd (cp a) b1 <-> x0 a1 /\ x1 b1).
      {
        intros.
        etransitivity.
        - symmetry; apply HH.
        - apply i.
      }
      clear HH i e.
      apply measurable_rectangle_eq_decompose in eqq.
      unfold α, β in *.
      destruct eqq as [[[?|?][?|?]]|[??]]
      ; try solve [
            rewrite H, H0
            ; repeat rewrite ps_none
            ; repeat rewrite Rbar_mult_0_r
            ; repeat rewrite Rbar_mult_0_l; trivial].      
  Qed.
  
  (* We discharge the extra hypothesis here *)
  Instance product_measure_is_measurable_ps :
    is_measure (σ:=product_sa A B)
               (product_measure (ps_P (σ:=A)) (ps_P (σ:=B))).
  Proof.
    apply product_measure_is_measurable.
    - apply ps_measure.
    - apply ps_measure.
    - apply product_measure_Hyp_ps.
  Qed.

  Global Instance product_ps : ProbSpace (product_sa A B).
  Proof.
    apply (measure_all_one_ps (product_measure (ps_P (σ:=A)) (ps_P (σ:=B)))).
    generalize (product_measure_product (ps_P (σ:=A)) (ps_measure _) (ps_P (σ:=B)) (ps_measure _) product_measure_Hyp_ps Ω Ω)
    ; intros HH.
    repeat rewrite ps_one in HH.
    rewrite Rbar_mult_1_r in HH.
    rewrite <- HH.
    assert (pre_eqq:pre_event_equiv
              pre_Ω
              (fun '(x,y) => @pre_Ω X x /\ @pre_Ω Y y)).
    {
      intros [??]; tauto.
    }
    assert (sa:sa_sigma (product_sa A B) (fun '(x,y) => @pre_Ω X x /\ @pre_Ω Y y)).
    { 
      rewrite <- pre_eqq.
      apply sa_all.
    }
    apply (measure_proper (σ:=product_sa A B) (μ:=product_measure (fun x : event A => ps_P x) (fun x : event B => ps_P x) 
                                                                  ) Ω (exist _ _ sa)).
    now red; simpl.
  Defined.

  Global Instance product_ps_proper : Proper (pre_event_equiv ==> eq)
                                                  (product_measure (ps_P (σ:=A)) (ps_P (σ:=B))).
  Proof.
    apply product_measure_proper.
    - apply ps_measure.
    - apply ps_measure.
    - apply product_measure_Hyp_ps.
  Qed.    
  
  Theorem product_sa_product (a:event A) (b:event B) :
    ps_P (ProbSpace:=product_ps) (product_sa_event a b) =
      ps_P a * ps_P b.
  Proof.
    simpl.
    rewrite product_measure_product; simpl; trivial.
    - apply ps_measure.
    - apply ps_measure.
    - apply product_measure_Hyp_ps.
  Qed.

  Lemma pre_event_set_product_pi : Pi_system (pre_event_set_product (@sa_sigma _ A) (@sa_sigma _ B)).
  Proof.
    unfold pre_event_set_product; intros ?[?[?[?[??]]]]?[?[?[?[??]]]].
    exists (pre_event_inter x x1).
    exists (pre_event_inter x0 x2).
    split; [| split].
    - now apply sa_inter.
    - now apply sa_inter.
    - rewrite H1, H4.
      unfold pre_event_inter; simpl; intros [??].
      tauto.
  Qed.
            
  (* product_ps is the unique probability space that preserves the product rule. *)
  Theorem product_ps_unique (ps:ProbSpace (product_sa A B)) :
    (forall a b, ps_P (ProbSpace:=ps) (product_sa_event a b) =
              ps_P a * ps_P b) ->
    forall x, ps_P (ProbSpace:=ps) x = ps_P (ProbSpace:=product_ps) x.
  Proof.
    intros.
    apply pi_prob_extension_unique.
    - apply pre_event_set_product_pi.
    - intros.
      assert (exists x y, event_equiv (generated_sa_base_event Ca) (product_sa_event x y)).
      {
        destruct Ca as [?[?[?[??]]]]; simpl.
        exists (exist _ x0 s).
        exists (exist _ x1 s0).
        intros ?; simpl.
        apply e.
      } 
      destruct H0 as [?[? eqq]].
      repeat rewrite eqq.
      rewrite H.
      now rewrite product_sa_product.
  Qed.

  Lemma product_independent_fst_snd :
    independent_rvs product_ps A B fst snd.
  Proof.
    unfold independent_rvs.
    intros.
    unfold independent_events.
    generalize product_sa_product; intros.
    assert (ps_P  (rv_preimage (dom := product_sa A B) fst A0) = ps_P A0).
    {
      specialize (H A0 Ω).
      rewrite ps_one, Rmult_1_r in H.
      rewrite <- H.
      apply ps_proper.
      intro x; simpl.
      destruct x; destruct A0; now simpl.
    }
    assert (ps_P (rv_preimage (dom := product_sa A B) snd B0) = ps_P B0).
    {
      specialize (H Ω B0).
      rewrite ps_one, Rmult_1_l in H.
      rewrite <- H.
      apply ps_proper.
      intro x; simpl.
      destruct x; destruct B0; now simpl.
    }
    rewrite H0, H1, <- H.
    apply ps_proper.
    intro x; simpl.
    destruct x; destruct A0; destruct B0.
    now simpl.
 Qed.
  
  Lemma product_independent_sas :
    independent_sas product_ps
                    (pullback_rv_sub (product_sa A B) A fst (fst_rv _ _))
                    (pullback_rv_sub (product_sa A B) B snd (snd_rv _ _)).
  Proof.
    rewrite <- independent_rv_sas.
    apply product_independent_fst_snd.
  Qed.

  Lemma product_pullback_fst :
    forall (a : event A),
      ps_P (ProbSpace := ps1) a = 
      ps_P (ProbSpace := (pullback_ps _ _  product_ps fst)) a.
  Proof.
    intros.
    unfold product_ps, pullback_ps; simpl.
    generalize (product_measure_product  
                  (fun x : event A => Rbar.Finite (ps_P x))
                  (Measures.ps_measure ps1)
                  (fun x : event B => Rbar.Finite (ps_P x))
                  (Measures.ps_measure ps2)); intros.
    cut_to H; [|apply product_measure_Hyp_ps].
    specialize (H a Ω).
    rewrite ps_all in H.
    simpl in H.
    rewrite Rmult_1_r in H.
    replace (ps_P a) with (Rbar.real (Rbar.Finite (ps_P a))) by now simpl.
    f_equal.
    rewrite <- H.
    apply product_ps_proper.
    intros [??]; destruct a; simpl.
    unfold event_preimage, pre_Ω, proj1_sig; simpl.
    tauto.
  Qed.
  
  Lemma product_pullback_snd :
    forall (b : event B),
      ps_P (ProbSpace := ps2) b = 
      ps_P (ProbSpace := (pullback_ps _ _  product_ps snd)) b.
  Proof.
    intros.
    unfold product_ps, pullback_ps; simpl.
    generalize (product_measure_product  
                  (fun x : event A => Rbar.Finite (ps_P x))
                  (Measures.ps_measure ps1)
                  (fun x : event B => Rbar.Finite (ps_P x))
                  (Measures.ps_measure ps2)); intros.
    cut_to H; [|apply product_measure_Hyp_ps].
    specialize (H Ω b).
    rewrite ps_all in H.
    simpl in H.
    rewrite Rmult_1_l in H.
    replace (ps_P b) with (Rbar.real (Rbar.Finite (ps_P b))) by now simpl.
    f_equal.
    rewrite <- H.
    apply product_ps_proper.
    intros [??]; destruct b; simpl.
    unfold event_preimage, pre_Ω, proj1_sig; simpl.
    tauto.
  Qed.

    Lemma product_ps_section_measurable_fst (E:event (product_sa A B)) :
      RandomVariable A borel_sa 
                   (fun x => ps_P (exist _ _ (product_section_fst E x))).
  Proof.
    pose (FF := fun (e : pre_event (X * Y)) =>
                  exists (pf: sa_sigma (product_sa A B) e),
                    RandomVariable A borel_sa 
                                   (fun x => ps_P (exist _ _ (product_section_fst (exist _ e pf)  x)))).
    assert (forall (a : event A) (b : event B),
               FF (fun '(x,y) => a x /\ b y)).
    {
      intros.
      unfold FF.
      exists (product_sa_sa a b).
      assert (RandomVariable A borel_sa
                             (fun x => (ps_P b) * (EventIndicator (classic_dec a) x))) by typeclasses eauto.
      revert H.
      apply RandomVariable_proper; try easy.
      intro x.
      unfold EventIndicator.
      match_destr.
      - rewrite Rmult_1_r.
        apply ps_proper.
        intro y.
        simpl.
        tauto.
      - rewrite Rmult_0_r.
        generalize (ps_none ps2); intros.
        replace R0 with 0 in H by lra.
        rewrite <- H.
        apply ps_proper.
        intro y.
        simpl.
        unfold pre_event_none.
        tauto.
    }
    assert (Lambda_system FF).
    {
      apply lambda_union_alt_suffices.
      - specialize (H Ω Ω).
        unfold FF in *.
        destruct H.
        assert  (pf : sa_sigma (product_sa A B) pre_Ω) by apply sa_all.
        exists pf.
        revert H.
        apply RandomVariable_proper; try easy.
        intro xx.
        apply ps_proper.
        intro y; simpl.
        unfold pre_Ω; tauto.
      - intros ???.
        unfold FF.
        split; intros; destruct H1.
        + assert (sa_sigma (product_sa A B) y) by now rewrite <- H0.
          exists H2.
          revert H1.
          apply RandomVariable_proper; try easy.
          intro xx.
          apply ps_proper.
          intro yy.
          simpl.
          now specialize (H0 (xx, yy)).
        + assert (sa_sigma (product_sa A B) x) by now rewrite H0.
          exists H2.
          revert H1.
          apply RandomVariable_proper; try easy.
          intro xx.
          apply ps_proper.
          intro yy.
          simpl.
          now specialize (H0 (xx, yy)).
      - unfold FF; intros.
        destruct H0 as [pfa ?].
        destruct H1 as [pfb ?].
        exists (sa_diff pfb pfa).
        assert (RandomVariable 
                A borel_sa
                (rvminus 
                   (fun x =>
                      (ps_P
                         (exist (sa_sigma B) (fun y : Y => b (x, y)) (product_section_fst (exist _ b pfb) x))))
                   (fun x => (ps_P
                      (exist (sa_sigma B) (fun y : Y => a (x, y)) (product_section_fst (exist _ a pfa) x)))))) by typeclasses eauto.
        revert H3.
        apply RandomVariable_proper; try easy.
        intro x.
        rv_unfold.
        generalize (ps_diff_sub 
                    ps2
                    (exist (sa_sigma B) (fun y => b (x, y)) (product_section_fst (exist _ b pfb) x))
                    (exist (sa_sigma B) (fun y => a (x, y)) (product_section_fst (exist _ a pfa) x))); intros.
        cut_to H3.
        + etransitivity; [etransitivity |]; [| apply H3 |]; try lra.
          apply ps_proper.
          intro xx.
          simpl.
          unfold pre_event_diff.
          tauto.
        + intro xx.
          simpl.
          apply H2.
     - unfold FF; intros.
       assert (forall x, sa_sigma (product_sa A B) (an x)).
       {
         intros.
         now destruct (H0 x).
       }         
       assert (pf : sa_sigma (product_sa A B) (pre_union_of_collection an)).
       {
         now apply sa_countable_union.
       }
       exists pf.
       assert (RandomVariable A borel_sa
                             (rvlim
                                (fun n x =>
                                   ps_P 
                                     (exist _ (fun y => an n (x,y)) 
                                            (product_section_fst (exist _ (an n) (H2 n)) x))))).
      {
        apply rvlim_rv.
        - intros.
          destruct (H0 n).
          revert H3.
          apply RandomVariable_proper; try easy.
          intro xx.
          apply ps_proper.
          intro y.
          now simpl.
        - intros.
          apply ex_finite_lim_seq_incr with (M := 1).
          + intros.
            apply ps_sub.
            intros y.
            simpl.
            apply H1.
          + intros.
            apply ps_le1.
      }
      revert H3.
      apply RandomVariable_proper; try easy.
      intro x.
      unfold rvlim.
      generalize (is_lim_ascending 
                    ps2
                    (fun n : nat =>
                       (exist (sa_sigma B) (fun y => an n (x, y))
                              (product_section_fst (exist _ (an n) (H2 n)) x)))); intros.
      cut_to H3.
      + apply is_lim_seq_unique in H3.
        assert (is_finite
                  (Lim_seq
         (fun n : nat =>
          ps_P
            (exist (sa_sigma B) (fun y => an n (x, y))
               (product_section_fst (exist _ (an n) (H2 n)) x))))).
        {
          now rewrite H3.
        }
        rewrite <- H4 in H3.
        apply Rbar_finite_eq in H3.
        unfold pre_event in H3.
        unfold pre_event.
        rewrite H3.
        apply ps_proper.
        intro y.
        simpl.
        tauto.
      + unfold ascending_collection.
        intros.
        intro y.
        simpl.
        apply H1.
    }
    pose (CC := (pre_event_set_product (sa_sigma A) (sa_sigma B))).
    assert (Pi_system CC).
    {
      unfold Pi_system, CC.
      intros.
      destruct H1 as [? [? [? [? ?]]]].
      destruct H2 as [? [? [? [? ?]]]].
      unfold pre_event_set_product.
      exists (pre_event_inter x x1).
      exists (pre_event_inter x0 x2).
      split; try apply sa_inter; try easy.
      split; try apply sa_inter; try easy.
      rewrite H4, H6.
      unfold pre_event_inter.
      intro z; destruct z; simpl.
      tauto.
    }
    assert (pre_event_equiv FF (sa_sigma (product_sa A B))).
    {
      intros ?.
      split; intros.
      - now destruct H2.
      - apply (Dynkin CC FF).
        + unfold pre_event_sub, CC, FF.
          intros.
          unfold pre_event_set_product in H3.
          destruct H3 as [? [? [? [? ?]]]].
          specialize (H (exist _ _ H3) (exist _ _ H4)).
          assert (pf : sa_sigma (product_sa A B) x0).
          {
            rewrite H5.
            generalize (product_sa_sa (exist _ _ H3) (exist _ _ H4)); intros.
            revert H6.
            apply sa_proper.
            intro z; now destruct z.
          }
          exists pf.
          destruct H.
          revert H.
          apply RandomVariable_proper; try easy.
          intro xx.
          apply ps_proper.
          intro y.
          simpl.
          specialize (H5 (xx, y)).
          now simpl in H5.
        + apply H2.
    }
    assert (FF E).
    {
      apply H2.
      apply (proj2_sig E).
    }
    unfold FF in H3.
    destruct H3.
    revert H3.
    apply RandomVariable_proper; try easy.
    intro xx.
    apply ps_proper.
    intro y.
    now simpl.
  Qed.

    
  Lemma product_ps_section_measurable_snd (E:event (product_sa A B)) :
    RandomVariable B borel_sa 
                   (fun y => ps_P (exist _ _ (product_section_snd E y))).
  Proof.
    pose (FF := fun (e : pre_event (X * Y)) =>
                  exists (pf: sa_sigma (product_sa A B) e),
                    RandomVariable B borel_sa 
                                   (fun y => ps_P (exist _ _ (product_section_snd (exist _ e pf)  y)))).
    assert (forall (a : event A) (b : event B),
               FF (fun '(x,y) => a x /\ b y)).
    {
      intros.
      unfold FF.
      exists (product_sa_sa a b).
      assert (RandomVariable B borel_sa
                             (fun y => (ps_P a) * (EventIndicator (classic_dec b) y))) by typeclasses eauto.
      revert H.
      apply RandomVariable_proper; try easy.
      intro x.
      unfold EventIndicator.
      match_destr.
      - rewrite Rmult_1_r.
        apply ps_proper.
        intro y.
        simpl.
        tauto.
      - rewrite Rmult_0_r.
        generalize (ps_none ps1); intros.
        replace R0 with 0 in H by lra.
        rewrite <- H.
        apply ps_proper.
        intro y.
        simpl.
        unfold pre_event_none.
        tauto.
    }
    assert (Lambda_system FF).
    {
      apply lambda_union_alt_suffices.
      - specialize (H Ω Ω).
        unfold FF in *.
        destruct H.
        assert  (pf : sa_sigma (product_sa A B) pre_Ω) by apply sa_all.
        exists pf.
        revert H.
        apply RandomVariable_proper; try easy.
        intro y.
        apply ps_proper.
        intro xx; simpl.
        unfold pre_Ω; tauto.
      - intros ???.
        unfold FF.
        split; intros; destruct H1.
        + assert (sa_sigma (product_sa A B) y) by now rewrite <- H0.
          exists H2.
          revert H1.
          apply RandomVariable_proper; try easy.
          intro yy.
          apply ps_proper.
          intro xx.
          simpl.
          now specialize (H0 (xx, yy)).
        + assert (sa_sigma (product_sa A B) x) by now rewrite H0.
          exists H2.
          revert H1.
          apply RandomVariable_proper; try easy.
          intro yy.
          apply ps_proper.
          intro xx.
          simpl.
          now specialize (H0 (xx, yy)).
      - unfold FF; intros.
        destruct H0.
        destruct H1.
        exists (sa_diff x0 x).
        assert (RandomVariable 
                  B borel_sa
                  (rvminus 
                     (fun y =>
                        (ps_P
                           (exist (sa_sigma A) (fun x => b (x, y)) (product_section_snd (exist _ b x0) y))))
                     (fun y => (ps_P
                                  (exist (sa_sigma A) (fun x => a (x, y)) (product_section_snd (exist _ a x) y)))))) by typeclasses eauto.
        revert H3.
        apply RandomVariable_proper; try easy.
        intro y.
        rv_unfold.
        generalize (ps_diff_sub 
                    ps1
                    (exist (sa_sigma A) (fun x => b (x, y)) (product_section_snd (exist _ b x0) y))
                    (exist (sa_sigma A) (fun x => a (x, y)) (product_section_snd (exist _ a x) y))); intros.
        cut_to H3.
        + etransitivity; [etransitivity |]; [| apply H3 |]; try lra.
          apply ps_proper.
          intro xx.
          simpl.
          unfold pre_event_diff.
          tauto.
        + intro xx.
          simpl.
          apply H2.
     - unfold FF; intros.
       assert (forall x, sa_sigma (product_sa A B) (an x)).
       {
         intros.
         now destruct (H0 x).
       }         
       assert (pf : sa_sigma (product_sa A B) (pre_union_of_collection an)).
       {
         now apply sa_countable_union.
       }
       exists pf.
       assert (RandomVariable B borel_sa
                             (rvlim
                                (fun n y =>
                                   ps_P 
                                     (exist _ (fun x => an n (x,y)) 
                                            (product_section_snd (exist _ (an n) (H2 n)) y))))).
      {
        apply rvlim_rv.
        - intros.
          destruct (H0 n).
          revert H3.
          apply RandomVariable_proper; try easy.
          intro y.
          apply ps_proper.
          intro xx.
          now simpl.
        - intros.
          apply ex_finite_lim_seq_incr with (M := 1).
          + intros.
            apply ps_sub.
            intros xx.
            simpl.
            apply H1.
          + intros.
            apply ps_le1.
      }
      revert H3.
      apply RandomVariable_proper; try easy.
      intro y.
      unfold rvlim.
      generalize (is_lim_ascending 
                    ps1
                    (fun n : nat =>
                       (exist (sa_sigma A) (fun x : X => an n (x, y))
                              (product_section_snd (exist _ (an n) (H2 n)) y)))); intros.
      cut_to H3.
      + apply is_lim_seq_unique in H3.
        assert (is_finite
                  (Lim_seq
         (fun n : nat =>
          ps_P
            (exist (sa_sigma A) (fun x => an n (x, y))
               (product_section_snd (exist _ (an n) (H2 n)) y))))).
        {
          now rewrite H3.
        }
        rewrite <- H4 in H3.
        apply Rbar_finite_eq in H3.
        unfold pre_event in H3.
        unfold pre_event.
        rewrite H3.
        apply ps_proper.
        intro x.
        simpl.
        tauto.
      + unfold ascending_collection.
        intros.
        intro x.
        simpl.
        apply H1.
    }
    pose (CC := (pre_event_set_product (sa_sigma A) (sa_sigma B))).
    assert (Pi_system CC).
    {
      unfold Pi_system, CC.
      intros.
      destruct H1 as [? [? [? [? ?]]]].
      destruct H2 as [? [? [? [? ?]]]].
      unfold pre_event_set_product.
      exists (pre_event_inter x x1).
      exists (pre_event_inter x0 x2).
      split; try apply sa_inter; try easy.
      split; try apply sa_inter; try easy.
      rewrite H4, H6.
      unfold pre_event_inter.
      intro z; destruct z; simpl.
      tauto.
    }
    assert (pre_event_equiv FF (sa_sigma (product_sa A B))).
    {
      intros ?.
      split; intros.
      - now destruct H2.
      - apply (Dynkin CC FF).
        + unfold pre_event_sub, CC, FF.
          intros.
          unfold pre_event_set_product in H3.
          destruct H3 as [? [? [? [? ?]]]].
          specialize (H (exist _ _ H3) (exist _ _ H4)).
          assert (pf : sa_sigma (product_sa A B) x0).
          {
            rewrite H5.
            generalize (product_sa_sa (exist _ _ H3) (exist _ _ H4)); intros.
            revert H6.
            apply sa_proper.
            intro z; now destruct z.
          }
          exists pf.
          destruct H.
          revert H.
          apply RandomVariable_proper; try easy.
          intro y.
          apply ps_proper.
          intro xx.
          simpl.
          specialize (H5 (xx, y)).
          now simpl in H5.
        + apply H2.
    }
    assert (FF E).
    {
      apply H2.
      apply (proj2_sig E).
    }
    unfold FF in H3.
    destruct H3.
    revert H3.
    apply RandomVariable_proper; try easy.
    intro y.
    apply ps_proper.
    intro xx.
    now simpl.
  Qed.

  Instance nonneg_prod_section_fst (e : event (product_sa A B)) :
    NonnegativeFunction 
      (fun x => ps_P (exist _ _ (product_section_fst e x))).
  Proof.
    intro x.
    apply ps_pos.
  Qed.

  Instance nonneg_prod_section_snd (e : event (product_sa A B)) :
    NonnegativeFunction 
      (fun y => ps_P (exist _ _ (product_section_snd e y))).
  Proof.
    intro y.
    apply ps_pos.
  Qed.

  Lemma explicit_product_measure_fst :
    is_measure (fun (e : event (product_sa A B)) =>
                  NonnegExpectation (fun x => ps_P (exist _ _ (product_section_fst e x)))).
  Proof.
    constructor.
    - intros ???.
      apply NonnegExpectation_ext.
      intro xx.
      apply ps_proper.
      intro yy.
      simpl.
      specialize (H (xx, yy)).
      destruct x; destruct y.
      now simpl in *.
    - assert (0 <= 0) by lra.
      assert (NonnegativeFunction (fun (x : X) => 0)) by (intro x; apply H).
      rewrite NonnegExpectation_ext with (nnf2 := H0).
      + apply NonnegExpectation_const0.
      + intro x.
        replace (0) with (ps_P (ProbSpace := ps2) ∅) by apply ps_none.
        apply ps_proper.
        intro y.
        now simpl.
    - intros.
      apply NonnegExpectation_pos.
    - intros.
      assert (forall (x:X),
                 collection_is_pairwise_disjoint
                   (fun n => exist _ _ (product_section_fst (B0 n) x))).
      {
       unfold collection_is_pairwise_disjoint.
       intros.
       specialize (H n1 n2 H0).
       unfold event_disjoint, pre_event_disjoint, proj1_sig in *.
       intros.
       specialize (H (x, x0)).
       match_destr_in H.
       match_destr_in H.
       simpl in H1.
       simpl in H2.
       now specialize (H H1 H2).
      }
      assert (forall (x:X),
                  sum_of_probs_equals ps_P (fun n => exist _ _ (product_section_fst (B0 n) x))
                                      (ps_P (union_of_collection (fun n => exist _ _ (product_section_fst (B0 n) x))))).
      {
        intros.
        destruct ps2.
        now apply ps_countable_disjoint_union.
      }
      unfold sum_of_probs_equals in H1.
      rewrite NNExpectation_Rbar_NNExpectation.
      generalize (Rbar_series_expectation ps1); intros.
      specialize (H2 (fun n x =>
                        ps_P
                          (exist (sa_sigma B) (fun y : Y => B0 n (x, y))
                                 (product_section_fst (B0 n) x)))).
      assert (forall n,
                 RandomVariable 
                   A Rbar_borel_sa
                   (fun x => 
                      ps_P
                        (exist (sa_sigma B) (fun y : Y => B0 n (x, y))
                               (product_section_fst (B0 n) x)))).
      {
        intros.
        generalize (product_ps_section_measurable_fst (B0 n)); intros.
        now apply Real_Rbar_rv in H3.
      }
      assert (forall n,
                 (Rbar_NonnegativeFunction
                   (fun x => 
                      ps_P
                        (exist (sa_sigma B) (fun y : Y => B0 n (x, y))
                               (product_section_fst (B0 n) x))))).
      {
        intros.
        intro x.
        apply ps_pos.
      }
      assert (Xlim_pos : Rbar_NonnegativeFunction
                      (fun omega : X =>
                       ELim_seq
                         (sum_Rbar_n
                            (fun n : nat =>
                             (fun (n0 : nat) (x : X) =>
                              Finite
                                (ps_P
                                   (exist (sa_sigma B)
                                      (fun y : Y => B0 n0 (x, y))
                                      (product_section_fst (B0 n0) x)))) n omega)))).
      {
        intros x.
        apply ELim_seq_nneg.
        intros.
        apply sum_Rbar_n_nneg_nneg.
        intros.
        apply ps_pos.
      }
      specialize (H2 H3 H4 Xlim_pos).
      symmetry.
      etransitivity; [etransitivity |]; [| apply H2 |].
      + apply ELim_seq_ext.
        intros.
        apply sum_Rbar_n_proper; trivial.
        red; intros.
        now rewrite NNExpectation_Rbar_NNExpectation.
      + apply Rbar_NonnegExpectation_ext.
        intro x.
        specialize (H1 x).
        clear Xlim_pos H2 H3 H4.
        rewrite <- infinite_sum_infinite_sum' in H1.        
        rewrite <- infinite_sum_is_lim_seq in H1.
        rewrite <- ELim_seq_incr_1.
        apply is_lim_seq_unique in H1.
        rewrite <- Elim_seq_fin in H1.
        etransitivity; [etransitivity |]; [| apply H1 |].        
        * apply ELim_seq_ext.
          intros.
          rewrite <- sum_n_Reals.
          rewrite <- sum_Rbar_n_finite_sum_n.
          apply sum_Rbar_n_proper; trivial.
          now red; intros.
        * apply Rbar_finite_eq.
          apply ps_proper.
          easy.
    Qed.
         
  Lemma explicit_product_measure_snd :
    is_measure (fun (e : event (product_sa A B)) =>
                  NonnegExpectation (fun y => ps_P (exist _ _ (product_section_snd e y)))).
    Proof.
    constructor.
    - intros ???.
      apply NonnegExpectation_ext.
      intro yy.
      apply ps_proper.
      intro xx.
      simpl.
      specialize (H (xx, yy)).
      destruct x; destruct y.
      now simpl in *.
    - assert (0 <= 0) by lra.
      assert (NonnegativeFunction (fun (y : Y) => 0)) by (intro y; apply H).
      rewrite NonnegExpectation_ext with (nnf2 := H0).
      + apply NonnegExpectation_const0.
      + intro y.
        replace (0) with (ps_P (ProbSpace := ps1) ∅) by apply ps_none.
        apply ps_proper.
        intro x.
        now simpl.
    - intros.
      apply NonnegExpectation_pos.
    - intros.
      assert (forall (y:Y),
                 collection_is_pairwise_disjoint
                   (fun n => exist _ _ (product_section_snd (B0 n) y))).
      {
       unfold collection_is_pairwise_disjoint.
       intros.
       specialize (H n1 n2 H0).
       unfold event_disjoint, pre_event_disjoint, proj1_sig in *.
       intros.
       specialize (H (x, y)).
       match_destr_in H.
       match_destr_in H.
       simpl in H1.
       simpl in H2.
       now specialize (H H1 H2).
      }
      assert (forall (y:Y),
                  sum_of_probs_equals ps_P (fun n => exist _ _ (product_section_snd (B0 n) y))
                                      (ps_P (union_of_collection (fun n => exist _ _ (product_section_snd (B0 n) y))))).
      {
        intros.
        destruct ps1.
        now apply ps_countable_disjoint_union.
      }
      unfold sum_of_probs_equals in H1.
      rewrite NNExpectation_Rbar_NNExpectation.
      generalize (Rbar_series_expectation ps2); intros.
      specialize (H2 (fun n y =>
                        ps_P
                          (exist (sa_sigma A) (fun x : X => B0 n (x, y))
                                 (product_section_snd (B0 n) y)))).
      assert (forall n,
                 RandomVariable 
                   B Rbar_borel_sa
                   (fun y => 
                      ps_P
                        (exist (sa_sigma A) (fun x : X => B0 n (x, y))
                               (product_section_snd (B0 n) y)))).
      {
        intros.
        generalize (product_ps_section_measurable_snd (B0 n)); intros.
        now apply Real_Rbar_rv in H3.
      }
      assert (forall n,
                 (Rbar_NonnegativeFunction
                   (fun y => 
                      ps_P
                        (exist (sa_sigma A) (fun x : X => B0 n (x, y))
                               (product_section_snd (B0 n) y))))).
      {
        intros.
        intro y.
        apply ps_pos.
      }
      assert (Xlim_pos : Rbar_NonnegativeFunction
                      (fun omega : Y =>
                       ELim_seq
                         (sum_Rbar_n
                            (fun n : nat =>
                             (fun (n0 : nat) (y : Y) =>
                              Finite
                                (ps_P
                                   (exist (sa_sigma A)
                                      (fun x : X => B0 n0 (x, y))
                                      (product_section_snd (B0 n0) y)))) n omega)))).
      {
        intros x.
        apply ELim_seq_nneg.
        intros.
        apply sum_Rbar_n_nneg_nneg.
        intros.
        apply ps_pos.
      }
      specialize (H2 H3 H4 Xlim_pos).
      symmetry.
      etransitivity; [etransitivity |]; [| apply H2 |].
      + apply ELim_seq_ext.
        intros.
        apply sum_Rbar_n_proper; trivial.
        red; intros.
        now rewrite NNExpectation_Rbar_NNExpectation.
      + apply Rbar_NonnegExpectation_ext.
        intro y.
        specialize (H1 y).
        clear Xlim_pos H2 H3 H4.
        rewrite <- infinite_sum_infinite_sum' in H1.        
        rewrite <- infinite_sum_is_lim_seq in H1.
        rewrite <- ELim_seq_incr_1.
        apply is_lim_seq_unique in H1.
        rewrite <- Elim_seq_fin in H1.
        etransitivity; [etransitivity |]; [| apply H1 |].        
        * apply ELim_seq_ext.
          intros.
          rewrite <- sum_n_Reals.
          rewrite <- sum_Rbar_n_finite_sum_n.
          apply sum_Rbar_n_proper; trivial.
          now red; intros.
        * apply Rbar_finite_eq.
          apply ps_proper.
          easy.
    Qed.

    Lemma NonnegExpectation_EventIndicator {Ts : Type} {dom : SigmaAlgebra Ts} {Prts : ProbSpace dom}
          {P : event dom} (dec : forall x : Ts, {P x} + {~ P x}):
      NonnegExpectation (EventIndicator dec) = Finite (ps_P P).
    Proof.
      generalize (Expectation_EventIndicator dec); intros.
      erewrite Expectation_pos_pofrf in H.
      now invcs H.
    Qed.

    Theorem explicit_product_sa_product_fst (a:event A) (b:event B) :
      NonnegExpectation (fun x => ps_P (exist _ _ (product_section_fst (product_sa_event a b) x))) = 
      ps_P a * ps_P b.
    Proof.
      assert (NonnegativeFunction
                 (rvscale (ps_P b) (EventIndicator (classic_dec a)))).
      {
        intro x.
        apply Rmult_le_pos.
        - apply ps_pos.
        - apply EventIndicator_pos.
      }
      replace (Finite (ps_P a * ps_P b)) with (Finite (Rbar_mult (ps_P a) (ps_P b))).
      - rewrite NonnegExpectation_ext with (nnf2 := H).
        + erewrite NonnegExpectation_scale'.
          rewrite NonnegExpectation_EventIndicator.
          * now rewrite Rbar_mult_comm.
          * apply ps_pos.
        + intro x.
          unfold EventIndicator, rvscale.
          simpl.
          destruct (classic_dec a x).
          * rewrite Rmult_1_r.
            apply ps_proper.
            intros y.
            simpl.
            tauto.
          * rewrite Rmult_0_r.
            generalize (ps_none ps2); intros.
            replace R0 with 0 in H0 by lra.
            rewrite <- H0.
            apply ps_proper.
            intro y.
            simpl.
            unfold pre_event_none.
            tauto.
      - now simpl.
    Qed.

    Theorem explicit_product_sa_product_snd (a:event A) (b:event B) :
      NonnegExpectation (fun y => ps_P (exist _ _ (product_section_snd (product_sa_event a b) y))) = 
      ps_P a * ps_P b.
    Proof.
      assert (NonnegativeFunction
                 (rvscale (ps_P a) (EventIndicator (classic_dec b)))).
      {
        intro y.
        apply Rmult_le_pos.
        - apply ps_pos.
        - apply EventIndicator_pos.
      }
      replace (Finite (ps_P a * ps_P b)) with (Finite (Rbar_mult (ps_P a) (ps_P b))).
      - rewrite NonnegExpectation_ext with (nnf2 := H).
        + erewrite NonnegExpectation_scale'.
          rewrite NonnegExpectation_EventIndicator.
          * now rewrite Rbar_mult_comm.
          * apply ps_pos.
        + intro y.
          unfold EventIndicator, rvscale.
          simpl.
          destruct (classic_dec b y).
          * rewrite Rmult_1_r.
            apply ps_proper.
            intros x.
            simpl.
            tauto.
          * rewrite Rmult_0_r.
            generalize (ps_none ps1); intros.
            replace R0 with 0 in H0 by lra.
            rewrite <- H0.
            apply ps_proper.
            intro x.
            simpl.
            unfold pre_event_none.
            tauto.
      - now simpl.
    Qed.

   Lemma explicit_product_1_fst :
     (fun e : event (product_sa A B) =>
        NonnegExpectation
          (fun x : X =>
           ps_P
             (exist (sa_sigma B) (fun y : Y => e (x, y))
                    (product_section_fst e x)))) Ω = R1 .
     Proof.
       simpl.
       generalize (explicit_product_sa_product_fst Ω Ω); intros.
       do 2 rewrite ps_all in H.
       rewrite Rmult_1_r in H.
       rewrite <- H.
       apply NonnegExpectation_ext.
       intro x.
       apply ps_proper.
       intro y.
       simpl.
       tauto.       
    Qed.

   Lemma explicit_product_1_snd :
     (fun e : event (product_sa A B) =>
        NonnegExpectation
          (fun y: Y =>
           ps_P
             (exist (sa_sigma A) (fun x : X => e (x, y))
                    (product_section_snd e y)))) Ω = R1 .
     Proof.
       simpl.
       generalize (explicit_product_sa_product_snd Ω Ω); intros.
       do 2 rewrite ps_all in H.
       rewrite Rmult_1_r in H.
       rewrite <- H.
       apply NonnegExpectation_ext.
       intro x.
       apply ps_proper.
       intro y.
       simpl.
       tauto.       
    Qed.

  Theorem explicit_product_product_pse_fst :
    forall e, 
      Finite (ps_P (ProbSpace:=product_ps) e) =
      NonnegExpectation (fun x => ps_P (exist _ _ (product_section_fst e x))).
  Proof.
    intros.
    generalize explicit_product_measure_fst; intros.
    symmetry.
    assert (is_finite (NonnegExpectation (fun x => ps_P (exist _ _ (product_section_fst e x))))).
    {
      assert (0 <= 1) by lra.
      apply Finite_NonnegExpectation_le with (nnf2 := nnfconst 1 H0).
      - intros ?.
        apply ps_le1.
      - now rewrite NonnegExpectation_const.
    }
    rewrite <- H0.
    apply Rbar_finite_eq.
    apply (product_ps_unique (measure_all_one_ps 
                  (T := X * Y) 
                  (σ := product_sa A B) _
                  explicit_product_1_fst)).
    intros; simpl.
    generalize (explicit_product_sa_product_fst a b); intros HH.
    erewrite NonnegExpectation_ext; [now rewrite HH |].
    reflexivity.
  Qed.

  Theorem explicit_product_product_pse_snd :
    forall e, 
      Finite (ps_P (ProbSpace:=product_ps) e) =
      NonnegExpectation (fun y => ps_P (exist _ _ (product_section_snd e y))).
  Proof.
    intros.
    generalize explicit_product_measure_snd; intros.
    symmetry.
    assert (is_finite (NonnegExpectation (fun y => ps_P (exist _ _ (product_section_snd e y))))).
    {
      assert (0 <= 1) by lra.
      apply Finite_NonnegExpectation_le with (nnf2 := nnfconst 1 H0).
      - intros ?.
        apply ps_le1.
      - now rewrite NonnegExpectation_const.
    }
    rewrite <- H0.
    apply Rbar_finite_eq.
    apply (product_ps_unique (measure_all_one_ps 
                  (T := X * Y) 
                  (σ := product_sa A B) _
                  explicit_product_1_snd)).
    intros; simpl.
    generalize (explicit_product_sa_product_snd a b); intros HH.
    erewrite NonnegExpectation_ext; [now rewrite HH |].
    reflexivity.
  Qed.

Instance Rbar_nneg_section_fst (f : (X * Y) -> Rbar)
         {nnf : Rbar_NonnegativeFunction f} :
  forall x, Rbar_NonnegativeFunction (fun y => f (x, y)).
Proof.
  intros ??.
  apply nnf.
Qed.
  
Instance Rbar_nneg_section_snd (f : (X * Y) -> Rbar)
         {nnf : Rbar_NonnegativeFunction f} :
  forall y, Rbar_NonnegativeFunction (fun x => f (x, y)).
Proof.
  intros ??.
  apply nnf.
Qed.

Instance nneg_section_fst (f : (X * Y) -> R)
         {nnf : NonnegativeFunction f} :
  forall x, NonnegativeFunction (fun y => f (x, y)).
Proof.
  intros ??.
  apply nnf.
Qed.
  
Instance nneg_section_snd (f : (X * Y) -> R)
         {nnf : NonnegativeFunction f} :
  forall y, NonnegativeFunction (fun x => f (x, y)).
Proof.
  intros ??.
  apply nnf.
Qed.

Program Instance frf_section_fst (f : (X * Y) -> R) (x : X)
         {frf : FiniteRangeFunction f} :
  FiniteRangeFunction (fun y => f (x,y)) :=
  { frf_vals := frf_vals}.
Next Obligation.
  apply frf_vals_complete.
Qed.

Program Instance frf_section_snd (f : (X * Y) -> R) (y : Y)
         {frf : FiniteRangeFunction f} :
  FiniteRangeFunction (fun x => f (x,y)) :=
  { frf_vals := frf_vals}.
Next Obligation.
  apply frf_vals_complete.
Qed.

Instance tonelli_nnexp_section_fst_simple_rv (f : (X * Y) -> R) 
      {frf : FiniteRangeFunction f}
      {nnf : NonnegativeFunction f} 
      {rv : RandomVariable (product_sa A B) borel_sa f} :
    RandomVariable A Rbar_borel_sa
                   (fun x => NonnegExpectation (fun y => f (x, y))).
  Proof.
(*
  assert (forall E : event (product_sa A B), 
             RandomVariable 
               A Rbar_borel_sa
               (fun x => NonnegExpectation 
                           (EventIndicator (classic_dec
                                              (fun y : Y => E (x, y)))))).
  {
    intros.
    generalize (product_ps_section_measurable_fst E); intros.
    apply (Real_Rbar_rv (dom := A)) in H.
    revert H.
    apply RandomVariable_proper; try easy.
    intros ?.
    erewrite <- NonnegExpectation_EventIndicator.
    apply NonnegExpectation_pf_irrel.
  }
*)
  assert (RandomVariable 
            A borel_sa
            (fun x : X => SimpleExpectation (fun y : Y => f (x, y)))).
  {
    unfold SimpleExpectation.
    simpl.
    apply list_sum_rv; intros.
    apply rvscale_rv.
    unfold preimage_singleton, pre_event_preimage, pre_event_singleton.
    assert (saE:sa_sigma (product_sa A B) (fun '(x, y) => f (x, y) = c)).
    {
      generalize (sa_preimage_singleton f); intros.
      generalize (rv (exist _ _ (borel_singleton c))).
      now apply sa_proper; intros [??]; simpl.
    }
    generalize (product_ps_section_measurable_fst (exist _ _ saE)).
    apply RandomVariable_proper; try reflexivity.
    intros ?.
    now apply ps_proper; intros ?; simpl.
  }
  apply Real_Rbar_rv in H.
  revert H.
  apply RandomVariable_proper; try easy.
  intros ?.
  now erewrite simple_NonnegExpectation.
  Qed.

Instance tonelli_nnexp_section_fst_rv (f : (X * Y) -> Rbar) 
      {nnf : Rbar_NonnegativeFunction f} 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} :
    RandomVariable A Rbar_borel_sa
                   (fun x => Rbar_NonnegExpectation (fun y => f (x, y))).
Proof.
  generalize (simple_approx_lim_seq f nnf); intros.
  generalize (simple_approx_rv (dom := product_sa A B) f); intros apx_rv.
  generalize (simple_approx_pofrf f); intro apx_nnf.
  generalize (simple_approx_frf f); intro apx_frf. 
  generalize (simple_approx_increasing f nnf); intro apx_inc.

  assert (RandomVariable 
            A Rbar_borel_sa
            (fun x => Rbar_NonnegExpectation (Rbar_rvlim (fun n y => simple_approx f n (x, y))))).
  {
    assert (RandomVariable 
              A Rbar_borel_sa
              (Rbar_rvlim (fun n x => NonnegExpectation (fun y => simple_approx f n (x, y))))).
    {
      apply Rbar_rvlim_rv.
      intros.
      now apply tonelli_nnexp_section_fst_simple_rv.
    }
    revert H0.
    apply RandomVariable_proper; try easy.
    intros ?.
    rewrite <- monotone_convergence_Rbar_rvlim.
    - unfold Rbar_rvlim.
      apply ELim_seq_ext.
      intros.
      now rewrite NNExpectation_Rbar_NNExpectation.
    - intros.
      apply Real_Rbar_rv.
      now apply prod_section_fst_rv.
    - intros ??.
      apply apx_inc.
  }
  revert H0.
  apply RandomVariable_proper; try easy.
  intros ?.
  apply Rbar_NonnegExpectation_ext.
  intros ?.
  unfold Rbar_rvlim.
  specialize (H (a, a0)).
  apply is_lim_seq_unique in H.
  rewrite <- H.
  now rewrite Elim_seq_fin.
 Qed.

Lemma tonelli_nnexp_section_fst_Indicator (E : event (product_sa A B))
      {nnf : Rbar_NonnegativeFunction
               (fun x => NonnegExpectation 
                           (EventIndicator (classic_dec
                                              (fun y : Y => E (x, y)))))} :
    NonnegExpectation (Prts := product_ps) (EventIndicator (classic_dec E)) =  
    Rbar_NonnegExpectation
      (fun x => NonnegExpectation 
                  (EventIndicator (classic_dec
                                     (fun y : Y => E (x, y))))).
Proof.
  rewrite NonnegExpectation_EventIndicator.
  rewrite explicit_product_product_pse_fst.
  rewrite NNExpectation_Rbar_NNExpectation.
  apply Rbar_NonnegExpectation_ext.
  intros ?.
  erewrite <- NonnegExpectation_EventIndicator.
  reflexivity.
Qed.

Lemma NonnegExpectation_list_sum_map_all
  {Ts : Type} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) {T : Type} 
  (f : T -> Ts -> R) (l : list T)
  {rvX : forall x : T, RandomVariable dom borel_sa (f x)}
  {frf: NonnegativeFunction (fun omega : Ts => list_sum (map (fun x : T => f x omega) l))}
  {frfX : forall x : T, NonnegativeFunction (f x)}
  :
  NonnegExpectation (fun omega : Ts => list_sum (map (fun x : T => f x omega) l)) =
    list_Rbar_sum (map (fun x : T => NonnegExpectation (f x)) l).
Proof.
  induction l; simpl.
  - rewrite <- (NonnegExpectation_const 0 (reflexivity _)).
    apply NonnegExpectation_pf_irrel.
  - Existing Instance list_sum_map_rv.
      
    assert (nnf2 : NonnegativeFunction (fun omega : Ts => list_sum (map (fun x : T => f x omega) l))).
    {
      intros ?.
      apply list_sum_pos_pos'.
      apply Forall_map.
      apply Forall_forall; intros.
      apply frfX.
    }
    etransitivity; [etransitivity |]; [ | 
                                        apply  (NonnegExpectation_sum (f a) (fun omega => list_sum (map (fun x : T => f x omega) l))) | ].
    + reflexivity.
    + f_equal.
      now rewrite IHl.
Qed.

Instance list_Rbar_sum_map_rv {Ts} {dom:SigmaAlgebra Ts} {T} f (l:list T)
             {rv : forall x, RandomVariable dom Rbar_borel_sa (f x)} :
  RandomVariable dom Rbar_borel_sa (fun omega => list_Rbar_sum (map (fun x => f x omega) l)).
Proof.
  induction l.
  - simpl.
    apply rvconst.
  - apply Rbar_rvplus_rv; trivial.
Qed.

    
Lemma Rbar_NonnegExpectation_list_sum_map_all
  {Ts : Type} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) {T : Type} 
  (f : T -> Ts -> Rbar) (l : list T)
  {rvX : forall x : T, RandomVariable dom Rbar_borel_sa (f x)}
  {frf: Rbar_NonnegativeFunction (fun omega : Ts => list_Rbar_sum (map (fun x : T => f x omega) l))}
  {frfX : forall x : T, Rbar_NonnegativeFunction (f x)}
  :
  Rbar_NonnegExpectation (fun omega : Ts => list_Rbar_sum (map (fun x : T => f x omega) l)) =
    list_Rbar_sum (map (fun x : T => Rbar_NonnegExpectation (f x)) l).
Proof.
  induction l; simpl.
  - rewrite <- (Rbar_NonnegExpectation_const 0 (reflexivity _)).
    apply Rbar_NonnegExpectation_pf_irrel.
  - Existing Instance list_Rbar_sum_map_rv.
      
    assert (nnf2 : Rbar_NonnegativeFunction (fun omega : Ts => list_Rbar_sum (map (fun x : T => f x omega) l))).
    {
      intros ?.
      apply list_Rbar_sum_nneg_nneg; intros.
      apply in_map_iff in H.
      destruct H as [? [??]]; subst.
      apply frfX.
    }
    etransitivity; [etransitivity |];
      [ | 
        apply  (Rbar_NonnegExpectation_plus (f a) (fun omega => list_Rbar_sum (map (fun x : T => f x omega) l))); trivial | ].
    + reflexivity.
    + f_equal.
      now rewrite IHl.
Qed.


Program Instance Nonnegative_FiniteRangeFunction {Ts} (f: Ts -> R)
  (frf:FiniteRangeFunction f) (nnf:NonnegativeFunction f) : FiniteRangeFunction f
  := {|
    frf_vals := filter (fun x => if Rle_dec 0 x then true else false) frf_vals
  |} .
Next Obligation.
  apply filter_In.
  split.
  - apply frf_vals_complete.
  - match_destr.
    specialize (nnf x); congruence.
Qed.

(* Global Arguments frf_vals {Ts Td} {rv_X} FiniteRangeFunction. *)

Lemma Nonnegative_FiniteRangeFunction_nneg {Ts} {f: Ts -> R}
  (frf:FiniteRangeFunction f) (nnf:NonnegativeFunction f) :
  Forall (Rle 0) (frf_vals (FiniteRangeFunction:=Nonnegative_FiniteRangeFunction f frf nnf)).
Proof.
  simpl.
  apply Forall_forall; intros ? inn.
  apply filter_In in inn.
  destruct inn.
  match_destr_in H0.
Qed.

Lemma tonelli_nnexp_section_fst_simple (f : (X * Y) -> R) 
      {frf : FiniteRangeFunction f}
      {nnf : NonnegativeFunction f}
      {nnf3 : Rbar_NonnegativeFunction (fun x => NonnegExpectation (fun y => f (x, y)))}
      {rv : RandomVariable (product_sa A B) borel_sa f} :
  NonnegExpectation (Prts := product_ps) f =
  Rbar_NonnegExpectation (fun x => NonnegExpectation (fun y => f (x, y))).
Proof.
  rewrite <- (simple_NonnegExpectation _ (frf:=Nonnegative_FiniteRangeFunction _ frf nnf)).
  
  assert (Rbar_NonnegativeFunction (fun x : X => SimpleExpectation (frf:=Nonnegative_FiniteRangeFunction _ _ _) (fun y : Y => f (x, y)))).
  {
    intros ?; simpl.
    now apply SimpleExpectation_nneg.
  }
  
  transitivity (Rbar_NonnegExpectation (fun x : X => SimpleExpectation (frf:=Nonnegative_FiniteRangeFunction _ _ _) (fun y : Y => f (x, y)))); cycle 1.
  {
    apply Rbar_NonnegExpectation_ext; intros ?.
    now rewrite <- (simple_NonnegExpectation _ (frf:=Nonnegative_FiniteRangeFunction _ _ _)).
  }
  rewrite frf_indicator_sum_simple_expectation.

    assert (nneg : forall x x0, 0 <= x * SimpleExpectation (frf:= Nonnegative_FiniteRangeFunction _ _ _) (fun y : Y => val_indicator f x (x0, y))).
  {
    intros.
    unfold val_indicator.
    destruct (Rle_dec 0 x).
    - apply Rmult_le_pos; trivial.
      apply SimpleExpectation_nneg.
      apply EventIndicator_pos.
    - replace (SimpleExpectation
                 (fun y : Y => EventIndicator (classic_dec (fun omega : X * Y => f omega = x)) (x0, y))) with 0; [lra |].
      unfold SimpleExpectation.
      symmetry.
      apply list_sum0_is0.
      apply Forall_map.
      apply Forall_forall; intros.
      destruct (Req_EM_T x1 0); [subst; lra |].
      replace (ps_P
    (preimage_singleton
       (fun y : Y => EventIndicator (classic_dec (fun omega : X * Y => f omega = x)) (x0, y)) x1))
        with (ps_P ∅); [rewrite ps_none; lra |].
      apply ps_proper
      ; intros ?; simpl
      ; unfold pre_event_none, pre_event_preimage, pre_event_singleton.
      split; [tauto |].
      unfold EventIndicator.
      match_destr; [| congruence].
      subst.
      generalize (nnf (x0, x2)); lra.
  } 

  assert (NonnegativeFunction (fun x : X =>
                                 list_sum (map (fun c : R => c * (SimpleExpectation (frf:= Nonnegative_FiniteRangeFunction _ _ _)(fun y => (val_indicator f c) (x, y)))) (nodup Req_EM_T (frf_vals (FiniteRangeFunction:=Nonnegative_FiniteRangeFunction _ _ _)))))).
  {
    intros ?.
    apply list_sum_pos_pos'.
    apply Forall_map.
    apply Forall_nodup.
    apply Forall_forall; intros.
    apply nneg.
  } 

  transitivity (NonnegExpectation
                      (fun x : X =>
                         list_sum (map (fun c : R => c * (SimpleExpectation (frf:= Nonnegative_FiniteRangeFunction _ _ _)(fun y => (val_indicator f c) (x, y)))) (nodup Req_EM_T (frf_vals (FiniteRangeFunction:=Nonnegative_FiniteRangeFunction _ _ _)))))); cycle 1.
  {
    rewrite NNExpectation_Rbar_NNExpectation.
    apply Rbar_NonnegExpectation_ext; intros ?.
    rewrite (frf_indicator_sum_simple_expectation _ _).
    do 2 f_equal.
    apply map_ext; intros.
    f_equal.
    apply SimpleExpectation_ext; reflexivity.
  }

  simpl.

  assert (sasE:forall a, sa_sigma (product_sa _ _) (fun omega : X * Y => f omega = a)); intros.
  {
    apply (rv (exist _ _ (borel_singleton a))).
  }

  erewrite (NonnegExpectation_list_sum_map_all).
  Unshelve.
  - rewrite <- list_Rbar_sum_map_finite, map_map.
    f_equal.
    apply map_ext_in; intros.
    apply nodup_In in H1.
    apply filter_In in H1.
    destruct H1 as [_ eqq].
    match_destr_in eqq; clear eqq.
    
    assert (NonnegativeFunction
                             (rvscale a
                                (fun omega : X =>
                                   SimpleExpectation (frf:= Nonnegative_FiniteRangeFunction _ _ _) (fun y : Y => val_indicator f a (omega, y))))).
    {
      intros ?.
      apply nneg.
    }
    
    transitivity (NonnegExpectation
                    (rvscale a (fun omega : X =>SimpleExpectation (fun y : Y => val_indicator f a (omega, y))))); [| apply NonnegExpectation_pf_irrel].
    erewrite (NonnegExpectation_scale' a); trivial.
    Unshelve.
    + transitivity (Rbar_mult a (NonnegExpectation (Prts:=product_ps) (val_indicator f a))).
      {
        now rewrite <- (simple_NonnegExpectation _); simpl.
      }
      f_equal.
      unfold val_indicator.
      assert (nnf0 : Rbar_NonnegativeFunction
                       (fun x : X =>
                          NonnegExpectation (EventIndicator (classic_dec (fun y : Y => f (x, y) = a))))).
      {
        intros ?; apply NonnegExpectation_pos.
      } 
      generalize (@tonelli_nnexp_section_fst_Indicator (exist _ _ (sasE _)) nnf0); simpl; intros HH.
      rewrite HH.
      rewrite NNExpectation_Rbar_NNExpectation.
      apply Rbar_NonnegExpectation_ext; intros ?.
      now rewrite <- (simple_NonnegExpectation _ (frf:=Nonnegative_FiniteRangeFunction _ _ _)); simpl.
    +  intros ?.
      apply SimpleExpectation_nneg.
      unfold val_indicator.
      apply EventIndicator_pos.
  - intros.
    apply rvscale_rv.
    apply borel_Rbar_borel.
    generalize (@tonelli_nnexp_section_fst_simple_rv (val_indicator f x) _ _ _).
    apply RandomVariable_proper; try reflexivity.
    intros ?.
    now rewrite <- (simple_NonnegExpectation _  (frf:=Nonnegative_FiniteRangeFunction _ _ _)); simpl.
  - intros ??.
    apply nneg.
Qed.


Lemma tonelli_nnexp_section_fst (f : (X * Y) -> Rbar) 
      {nnf : Rbar_NonnegativeFunction f}
      {nnf2 : Rbar_NonnegativeFunction (fun x => Rbar_NonnegExpectation (fun y => f (x, y)))}
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} :
  Rbar_NonnegExpectation (Prts := product_ps) f =
  Rbar_NonnegExpectation (fun x => Rbar_NonnegExpectation (fun y => f (x, y))).
Proof.
  generalize (simple_approx_lim_seq f nnf); intro flim.
  generalize (simple_approx_frf f); intro apx_frf.
  generalize (simple_approx_pofrf f); intro apx_nnf.
  generalize (simple_approx_rv (dom := product_sa A B) f); intros apx_rv.
  generalize (simple_approx_le f nnf); intro apx_le.
  generalize (simple_approx_increasing f nnf); intro apx_inc.  

  assert (forall n,
              Rbar_NonnegativeFunction
                (fun x : X => Rbar_NonnegExpectation (fun y : Y => (simple_approx f n) (x, y)))).
  {
    intros ??.
    apply Rbar_NonnegExpectation_pos.
  }
  assert (forall n,
             Rbar_NonnegExpectation (Prts := product_ps) (simple_approx f n) = 
             Rbar_NonnegExpectation (fun x : X => Rbar_NonnegExpectation (fun y : Y => (simple_approx f n) (x, y)))).
  {
    intros.
    rewrite <- NNExpectation_Rbar_NNExpectation.
    now erewrite tonelli_nnexp_section_fst_simple.
  }
  assert (nn_lim_apx: Rbar_NonnegativeFunction (Rbar_rvlim (fun n => simple_approx f n))).
  {
    intros ?.
    apply ELim_seq_nneg.
    intros.
    apply simple_approx_pofrf.
  }
  rewrite <- (Rbar_monotone_convergence 
                f (simple_approx f) rv nnf
                (fun n => Real_Rbar_rv _ (rv:=apx_rv n)) apx_nnf apx_le apx_inc); [|intros; now apply is_Elim_seq_fin].
  assert (forall x,
             Rbar_NonnegExpectation (fun y => f (x, y)) =
             ELim_seq (fun n : nat => Rbar_NonnegExpectation (fun y => simple_approx f n (x, y)))).
    {
      intros.
      rewrite (Rbar_monotone_convergence 
                 (fun y => f (x,y))
                 (fun n y => simple_approx f n (x, y))
                 (prod_section_fst_rv _ _) _ _ _ ); trivial.
      - intros ??.
        now apply simple_approx_le.
      - intros ??.
        now apply simple_approx_increasing.
      - intros.
        apply is_Elim_seq_fin.
        now apply simple_approx_lim_seq.
   }
  assert (nn_lim_sec_apx: 
            Rbar_NonnegativeFunction 
              (fun x => ELim_seq (fun n : nat => Rbar_NonnegExpectation (fun y : Y => simple_approx f n (x, y))))).
  {
    intros ?.
    apply ELim_seq_nneg.
    intros.
    apply Rbar_NonnegExpectation_pos.
  }
  rewrite (@Rbar_NonnegExpectation_ext _ _ _ _ _ _ nn_lim_sec_apx); [|intros ?; apply H1].
  assert (forall n : nat,
    RandomVariable A Rbar_borel_sa (fun x : X => Rbar_NonnegExpectation (fun y : Y => simple_approx f n (x, y)))).
  {
    intros.
    apply (tonelli_nnexp_section_fst_rv (simple_approx f n)).
  }
  assert (RandomVariable A Rbar_borel_sa
         (fun x : X => ELim_seq (fun n : nat => Rbar_NonnegExpectation (fun y : Y => simple_approx f n (x, y))))).
  {
    now apply Rbar_rvlim_rv.
  }
  assert (posX : Rbar_NonnegativeFunction
                   (fun x : X =>
                      ELim_seq (fun n : nat => Rbar_NonnegExpectation (fun y : Y => simple_approx f n (x, y))))).
  {
    intros ?.
    apply ELim_seq_nneg.
    intros.
    apply Rbar_NonnegExpectation_pos.
  }
  assert (Xn_pos : forall n : nat,
              Rbar_NonnegativeFunction
                (fun x : X => Rbar_NonnegExpectation (fun y : Y => simple_approx f n (x, y)))).
  {
    intros ??.
    apply Rbar_NonnegExpectation_pos.
  }
  rewrite <- (Rbar_monotone_convergence  
                (fun x : X => ELim_seq (fun n : nat => Rbar_NonnegExpectation (fun y : Y => simple_approx f n (x, y))))
                (fun n x => Rbar_NonnegExpectation (fun y : Y => simple_approx f n (x, y))) _ _ _ _).
  - apply ELim_seq_ext.
    intros.
    now rewrite H0.
  - intros ??.
    apply (Elim_seq_incr_elem  (fun n0 : nat => Rbar_NonnegExpectation (fun y : Y => simple_approx f n0 (a, y)))).
    intros.
    apply Rbar_NonnegExpectation_le.
    intros ?.
    now apply simple_approx_increasing.    
  - intros ??.
    apply Rbar_NonnegExpectation_le.
    intros ?.
    now apply simple_approx_increasing.    
  - intros.
    apply ELim_seq_correct.
    apply ex_Elim_seq_incr.
    intros.
    apply Rbar_NonnegExpectation_le.
    intros ?.
    now apply simple_approx_increasing.    
  Qed.


Lemma fubini_section_fst_almost_integrable (f : (X * Y) -> Rbar) 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} 
      {isfe : Rbar_IsFiniteExpectation product_ps f} :
  almost ps1 (fun x => Rbar_IsFiniteExpectation ps2 (fun y => f (x, y))).
Proof.
  generalize (tonelli_nnexp_section_fst_rv (Rbar_pos_fun_part f)); intros. 
  generalize (tonelli_nnexp_section_fst_rv (Rbar_neg_fun_part f)); intros.   
  destruct (Rbar_IsFiniteExpectation_parts product_ps f isfe).
  assert (Rbar_NonnegativeFunction
               (fun x : X => Rbar_NonnegExpectation (fun y : Y => Rbar_pos_fun_part f (x, y)))).
  {
    intros ?.
    apply Rbar_NonnegExpectation_pos.
  }
  assert (Rbar_NonnegativeFunction
               (fun x : X => Rbar_NonnegExpectation (fun y : Y => Rbar_neg_fun_part f (x, y)))).
  {
    intros ?.
    apply Rbar_NonnegExpectation_pos.
  }
  assert (isfe_pos:Rbar_IsFiniteExpectation 
                     ps1
                     (fun x => Rbar_NonnegExpectation (fun y => Rbar_pos_fun_part f (x, y)))).
  
  {
    unfold Rbar_IsFiniteExpectation.
    erewrite Rbar_Expectation_pos_pofrf.
    erewrite <- (tonelli_nnexp_section_fst (Rbar_pos_fun_part f)); try typeclasses eauto.
    apply Rbar_IsFiniteNonnegExpectation with (posX := Rbar_pos_fun_pos f)in H1.
    match_destr.
  }
  assert (isfe_neg:Rbar_IsFiniteExpectation 
                     ps1
                     (fun x => Rbar_NonnegExpectation (fun y => Rbar_neg_fun_part f (x, y)))).
  
  {
    unfold Rbar_IsFiniteExpectation.
    erewrite Rbar_Expectation_pos_pofrf.
    erewrite <- (tonelli_nnexp_section_fst (Rbar_neg_fun_part f)); try typeclasses eauto.
    apply Rbar_IsFiniteNonnegExpectation with (posX := Rbar_neg_fun_pos f)in H2.
    match_destr.
  }
  generalize (IsFiniteExpectation_nneg_is_almost_finite _ _ isfe_pos); intros finpos.
  generalize (IsFiniteExpectation_nneg_is_almost_finite _ _ isfe_neg); intros finneg.
  revert finpos; apply almost_impl.
  revert finneg; apply almost_impl.
  apply all_almost; intros ???.
  apply Rbar_IsFiniteExpectation_from_fin_parts.
  - now rewrite <- H6.
  - now rewrite <- H5.
 Qed.

Definition Rbar_Expectation0 {Ts : Type} {dom : SigmaAlgebra Ts} (Prts : ProbSpace dom)
  (rv_X : Ts -> Rbar) : Rbar
  := match Rbar_Expectation rv_X with
     | Some v => v
     | None => 0
     end.

Lemma Rbar_Expectation0_finite {Ts : Type} {dom : SigmaAlgebra Ts} (Prts : ProbSpace dom)
  (rv_X : Ts -> Rbar)
  {isfe:Rbar_IsFiniteExpectation Prts rv_X} :
 Rbar_Expectation0 Prts rv_X = Rbar_FiniteExpectation Prts rv_X.
Proof.
  unfold Rbar_Expectation0.
  now rewrite (Rbar_FiniteExpectation_Rbar_Expectation _ _).
Qed.

Definition Rbar_FiniteExpectation0 {Ts : Type} {dom : SigmaAlgebra Ts} (Prts : ProbSpace dom)
  (rv_X : Ts -> Rbar) : R
  := match Rbar_Expectation rv_X with
     | Some (Finite v) => v
     | _ => 0
     end.

Lemma Rbar_FiniteExpectation0_finite {Ts : Type} {dom : SigmaAlgebra Ts} (Prts : ProbSpace dom)
  (rv_X : Ts -> Rbar)
  {isfe:Rbar_IsFiniteExpectation Prts rv_X} :
 Rbar_FiniteExpectation0 Prts rv_X = Rbar_FiniteExpectation Prts rv_X.
Proof.
  unfold Rbar_FiniteExpectation0.
  now rewrite (Rbar_FiniteExpectation_Rbar_Expectation _ _).
Qed.

Lemma IsL1_Rbar_FiniteExpectation0_section_fst  (f : (X * Y) -> Rbar)  
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f}
      {isfe1 : Rbar_IsFiniteExpectation (product_ps) f} :
  (RandomVariable A borel_sa 
                  (fun x => Rbar_FiniteExpectation0 ps2 (fun y => f (x, y)))) /\
  (IsLp ps1 1 (fun x => Rbar_FiniteExpectation0 ps2 (fun y => f (x, y)))).
Proof.
  destruct (Rbar_IsFiniteExpectation_parts product_ps f isfe1) as [HH1 HH2].
  assert (rvpos : RandomVariable 
                    A Rbar_borel_sa 
                    (fun x => Rbar_NonnegExpectation (fun y => Rbar_pos_fun_part f (x, y)))).
  {
    eapply tonelli_nnexp_section_fst_rv.
    now apply Rbar_pos_fun_part_rv.
  }
  assert (rvneg : RandomVariable 
                    A Rbar_borel_sa 
                    (fun x => Rbar_NonnegExpectation (fun y => Rbar_neg_fun_part f (x, y)))).
  {
    eapply tonelli_nnexp_section_fst_rv.
    now apply Rbar_neg_fun_part_rv.
  }
  assert (RandomVariable A borel_sa 
                         (fun x => Rbar_FiniteExpectation0 ps2 (fun y => f (x, y)))).
  {
    assert (RandomVariable 
              A borel_sa
              (Rbar_finite_part
                 (Rbar_rvminus
                    (fun x =>
                       (Rbar_NonnegExpectation 
                          (Rbar_pos_fun_part (fun y => f (x, y)))))
                    (fun x => 
                       (Rbar_NonnegExpectation 
                          (Rbar_neg_fun_part (fun y => f (x, y)))))))).
    {
      apply finite_part_rv.
      now apply Rbar_rvminus_rv.
    }
    revert H.
    apply RandomVariable_proper; try easy.
    intros ?.
    unfold Rbar_FiniteExpectation0.
    unfold Rbar_Expectation.
    unfold Rbar_minus', Rbar_plus', Rbar_finite_part, Rbar_opp, Rbar_rvminus, Rbar_rvopp, Rbar_rvplus.
    rv_unfold'.
    case_eq (Rbar_NonnegExpectation (Rbar_pos_fun_part (fun y : Y => f (a, y))));
      case_eq (Rbar_NonnegExpectation (Rbar_neg_fun_part (fun y : Y => f (a, y)))); intros; simpl; try reflexivity.
  }
  split; trivial.
  apply Finite_abs_IsL1.
  apply IsFiniteExpectation_abs; trivial.
  assert (isfex1 : Rbar_IsFiniteExpectation ps1
                                              (fun x : X =>
                     Rbar_NonnegExpectation
                       (Rbar_pos_fun_part (fun y : Y => f (x, y))))).
  {
    unfold Rbar_IsFiniteExpectation.
    erewrite Rbar_Expectation_pos_pofrf.
    erewrite <- (tonelli_nnexp_section_fst (Rbar_pos_fun_part f)); try typeclasses eauto.
    apply Rbar_IsFiniteNonnegExpectation with (posX := Rbar_pos_fun_pos f)in HH1.
    match_destr.
    Unshelve.
    intros ?.
    apply Rbar_NonnegExpectation_pos.    
  }
  assert (isfex2 : Rbar_IsFiniteExpectation ps1
                    (fun x : X =>
                     Rbar_NonnegExpectation
                       (Rbar_neg_fun_part (fun y : Y => f (x, y))))).
  {
    unfold Rbar_IsFiniteExpectation.
    erewrite Rbar_Expectation_pos_pofrf.
    erewrite <- (tonelli_nnexp_section_fst (Rbar_neg_fun_part f)); try typeclasses eauto.
    apply Rbar_IsFiniteNonnegExpectation with (posX := Rbar_neg_fun_pos f)in HH2.
    match_destr.
    Unshelve.
    intros ?.
    apply Rbar_NonnegExpectation_pos.    
  }

  assert (rv_eq
            (fun x : X => (Rbar_FiniteExpectation0 ps2 (fun y : Y => f (x, y))))
              (Rbar_finite_part
                 (Rbar_rvminus
                    (fun x =>
                       (Rbar_NonnegExpectation 
                          (Rbar_pos_fun_part (fun y => f (x, y)))))
                    (fun x => 
                       (Rbar_NonnegExpectation 
                          (Rbar_neg_fun_part (fun y => f (x, y)))))))).
    {
      intros ?.
      unfold Rbar_FiniteExpectation0.
      unfold Rbar_Expectation.
      unfold Rbar_minus', Rbar_plus', Rbar_finite_part, Rbar_opp, Rbar_rvminus, Rbar_rvopp, Rbar_rvplus.
      rv_unfold'.
      case_eq (Rbar_NonnegExpectation (Rbar_pos_fun_part (fun y : Y => f (a, y))));
      case_eq (Rbar_NonnegExpectation (Rbar_neg_fun_part (fun y : Y => f (a, y)))); intros; simpl; try reflexivity.
    }
    rewrite H0.
    apply Rbar_finexp_finexp.
    - now apply Rbar_rvminus_rv.
    - now apply Rbar_is_finite_expectation_isfe_minus.
  Qed.
                        
Lemma Rbar_Expectation_pos_part_finite  {Ts : Type} {dom : SigmaAlgebra Ts} (Prts : ProbSpace dom)
      (rv_X : Ts -> Rbar)
      {isfe:Rbar_IsFiniteExpectation Prts rv_X} :
    is_finite (Rbar_NonnegExpectation (Rbar_pos_fun_part rv_X)).
  Proof.
    red in isfe.
    unfold Rbar_Expectation in isfe.
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_pos_fun_part rv_X x)).
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_neg_fun_part rv_X x)).     
    now unfold is_finite.
    simpl in isfe; tauto.
    simpl in isfe; tauto.     
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_neg_fun_part rv_X x));
      simpl in isfe; tauto.
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_neg_fun_part rv_X x));
      simpl in isfe; tauto.
  Qed.

  Lemma Rbar_Expectation_neg_part_finite  {Ts : Type} {dom : SigmaAlgebra Ts} (Prts : ProbSpace dom)
        (rv_X : Ts -> Rbar)
        {isfe:Rbar_IsFiniteExpectation Prts rv_X} :
    is_finite (Rbar_NonnegExpectation (Rbar_neg_fun_part rv_X)).
  Proof.
    red in isfe.
    unfold Rbar_Expectation in isfe.
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_pos_fun_part rv_X x)).
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_neg_fun_part rv_X x)).     
    now unfold is_finite.
    simpl in isfe; tauto.
    simpl in isfe; tauto.     
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_neg_fun_part rv_X x));
      simpl in isfe; tauto.
    destruct (Rbar_NonnegExpectation (fun x : Ts => Rbar_neg_fun_part rv_X x));
      simpl in isfe; tauto.
  Qed.

   Lemma Rbar_Finite_expectation_pos_neg_parts {Ts : Type} {dom : SigmaAlgebra Ts} (Prts : ProbSpace dom)
         (rv_X : Ts -> Rbar) 
         {rvx : RandomVariable dom Rbar_borel_sa rv_X}
         {isfe : Rbar_IsFiniteExpectation Prts rv_X} :
     Rbar_FiniteExpectation Prts rv_X = Rbar_NonnegExpectation(Rbar_pos_fun_part rv_X) -
                                     Rbar_NonnegExpectation(Rbar_neg_fun_part rv_X).
   Proof.
     unfold Rbar_FiniteExpectation, proj1_sig.
     match_destr.
     unfold Rbar_Expectation in e.
     rewrite <- (Rbar_Expectation_pos_part_finite Prts rv_X) in e.
     rewrite <- (Rbar_Expectation_neg_part_finite Prts rv_X) in e.     
     simpl in e.
     invcs e.
     simpl.
     ring.
  Qed.

Instance isfe_fubini_section_fst (f : (X * Y) -> Rbar) 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} 
      {isfe1 : Rbar_IsFiniteExpectation (product_ps) f} :
IsFiniteExpectation ps1 (fun x => Rbar_FiniteExpectation0 ps2 (fun y => f (x, y))).
Proof.
  destruct (IsL1_Rbar_FiniteExpectation0_section_fst f).
  now apply IsL1_Finite.
Qed.
  
Instance Rbar_isfe_fubini_section_fst (f : (X * Y) -> Rbar) 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} 
      {isfe1 : Rbar_IsFiniteExpectation (product_ps) f} :
  Rbar_IsFiniteExpectation ps1 (fun x => Rbar_FiniteExpectation0 ps2 (fun y => f (x, y))).
Proof.
  destruct (IsL1_Rbar_FiniteExpectation0_section_fst f).
  apply IsFiniteExpectation_Rbar.
  now apply IsL1_Finite.
Qed.

Theorem fubini_section_fst0 (f : (X * Y) -> Rbar) 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} 
      {isfe1 : Rbar_IsFiniteExpectation (product_ps) f} :
  Rbar_FiniteExpectation (product_ps) f =
  Rbar_FiniteExpectation ps1 (fun x => Rbar_FiniteExpectation0 ps2 (fun y => f (x, y))).
Proof.
  destruct (IsL1_Rbar_FiniteExpectation0_section_fst f).
  rewrite Rbar_Finite_expectation_pos_neg_parts; trivial.
  destruct (Rbar_IsFiniteExpectation_parts product_ps f isfe1) as [HH1 HH2].
  assert  (rv1 : RandomVariable A Rbar_borel_sa
                                (fun x : X =>
                                   Rbar_NonnegExpectation
                                     (Rbar_pos_fun_part (fun y : Y => f (x, y))))).
  {
    generalize (tonelli_nnexp_section_fst_rv (Rbar_pos_fun_part f)); intros. 
    revert H1.
    apply RandomVariable_proper; reflexivity.
  }
  assert (rv2 : RandomVariable A Rbar_borel_sa
                               (fun x : X =>
                                  Rbar_NonnegExpectation
                                    (Rbar_neg_fun_part (fun y : Y => f (x, y))))).
  {
    generalize (tonelli_nnexp_section_fst_rv (Rbar_neg_fun_part f)); intros. 
    revert H1.
    apply RandomVariable_proper; reflexivity.
  }
  assert (isfex1 : Rbar_IsFiniteExpectation ps1
                    (fun x : X =>
                     Rbar_NonnegExpectation
                       (Rbar_pos_fun_part (fun y : Y => f (x, y))))).
  {
    unfold Rbar_IsFiniteExpectation.
    erewrite Rbar_Expectation_pos_pofrf.
    erewrite <- (tonelli_nnexp_section_fst (Rbar_pos_fun_part f)); try typeclasses eauto.
    apply Rbar_IsFiniteNonnegExpectation with (posX := Rbar_pos_fun_pos f)in HH1.
    match_destr.
    Unshelve.
    intros ?.
    apply Rbar_NonnegExpectation_pos.    
  }
  assert (isfex2 : Rbar_IsFiniteExpectation ps1
                    (fun x : X =>
                     Rbar_NonnegExpectation
                       (Rbar_neg_fun_part (fun y : Y => f (x, y))))).
  {
    unfold Rbar_IsFiniteExpectation.
    erewrite Rbar_Expectation_pos_pofrf.
    erewrite <- (tonelli_nnexp_section_fst (Rbar_neg_fun_part f)); try typeclasses eauto.
    apply Rbar_IsFiniteNonnegExpectation with (posX := Rbar_neg_fun_pos f)in HH2.
    match_destr.
    Unshelve.
    intros ?.
    apply Rbar_NonnegExpectation_pos.    
  }

  assert (almostR2 ps1 eq
                   (fun x : X => (Finite (Rbar_FiniteExpectation0 ps2 (fun y : Y => f (x, y)))))
                   (Rbar_rvminus
                      (fun x : X =>
                         Rbar_NonnegExpectation (Rbar_pos_fun_part (fun y : Y => f (x, y))))
                      (fun x : X =>
                         Rbar_NonnegExpectation (Rbar_neg_fun_part (fun y : Y => f (x, y)))))).
  {
    assert (rv_eq
              (fun x : X => (Finite (Rbar_FiniteExpectation0 ps2 (fun y : Y => f (x, y)))))
              (Rbar_finite_part
                 (Rbar_rvminus
                    (fun x =>
                       (Rbar_NonnegExpectation 
                          (Rbar_pos_fun_part (fun y => f (x, y)))))
                    (fun x => 
                       (Rbar_NonnegExpectation 
                          (Rbar_neg_fun_part (fun y => f (x, y)))))))).
    {
      intros ?.
      unfold Rbar_FiniteExpectation0.
      unfold Rbar_Expectation.
      unfold Rbar_minus', Rbar_plus', Rbar_finite_part, Rbar_opp, Rbar_rvminus, Rbar_rvopp, Rbar_rvplus.
      rv_unfold'.
      case_eq (Rbar_NonnegExpectation (Rbar_pos_fun_part (fun y : Y => f (a, y))));
      case_eq (Rbar_NonnegExpectation (Rbar_neg_fun_part (fun y : Y => f (a, y)))); intros; simpl; try reflexivity.
    }
    apply finexp_almost_finite in isfex1; trivial.
    apply finexp_almost_finite in isfex2; trivial.
    revert isfex1; apply almost_impl.
    revert isfex2; apply almost_impl.
    apply all_almost; intros ???.
    rewrite H1.
    unfold Rbar_rvminus, Rbar_rvopp, Rbar_rvplus, Rbar_finite_part.
    rewrite <- H2.
    rewrite <- H3.
    simpl.
    now apply Rbar_finite_eq.
  }
  eapply Rbar_FiniteExpectation_proper_almostR2 in H1; trivial.
  - rewrite H1.
    generalize (Rbar_FiniteExpectation_minus ps1
               (fun x : X =>
        Rbar_NonnegExpectation (Rbar_pos_fun_part (fun y : Y => f (x, y))))
               (fun x : X =>
        Rbar_NonnegExpectation (Rbar_neg_fun_part (fun y : Y => f (x, y))))); intros.
    erewrite H2.
    f_equal.
    + erewrite  tonelli_nnexp_section_fst; try typeclasses eauto.
      erewrite Rbar_FiniteExpectation_Rbar_NonnegExpectation.
      simpl.
      reflexivity.
    + erewrite  tonelli_nnexp_section_fst; try typeclasses eauto.
      erewrite Rbar_FiniteExpectation_Rbar_NonnegExpectation.
      simpl.
      reflexivity.
  - now apply Real_Rbar_rv.
  - now apply Rbar_rvminus_rv.
    Unshelve.
    + intros ?.
      apply Rbar_NonnegExpectation_pos.
    + intros ?.
      apply Rbar_NonnegExpectation_pos.
 Qed.

Theorem fubini_section_fst (f : (X * Y) -> Rbar) 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} 
      {isfe1 : Rbar_IsFiniteExpectation (product_ps) f} 
      {isfe2 : forall x, Rbar_IsFiniteExpectation ps2 (fun y => f (x, y))} 
      {isfe3 : Rbar_IsFiniteExpectation ps1 (fun x => Rbar_FiniteExpectation ps2 (fun y => f (x, y)))} :
  Rbar_FiniteExpectation (product_ps) f =
  Rbar_FiniteExpectation ps1 (fun x => Rbar_FiniteExpectation ps2 (fun y => f (x, y))).
 Proof.
   erewrite fubini_section_fst0.
   apply Rbar_FiniteExpectation_ext.
   intros ?.
   unfold Rbar_FiniteExpectation, Rbar_FiniteExpectation0, proj1_sig.
   symmetry.
   match_destr.
   now rewrite e.
 Qed.

 Lemma fubini_section_fst_rv  (f : (X * Y) -> Rbar)  
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f}
      {isfe1 : Rbar_IsFiniteExpectation (product_ps) f} 
      {isfe2 : forall x, Rbar_IsFiniteExpectation ps2 (fun y => f (x, y))} :
  (RandomVariable A borel_sa 
                  (fun x => Rbar_FiniteExpectation ps2 (fun y => f (x, y)))).
 Proof.
   destruct (IsL1_Rbar_FiniteExpectation0_section_fst f).
   revert H.
   apply RandomVariable_proper; try easy.
   intros ?.
   unfold Rbar_FiniteExpectation, Rbar_FiniteExpectation0, proj1_sig.
   symmetry.
   match_destr.
   now rewrite e.
Qed.
   
End ps_product.

Local Instance product_flip_rv {X Y:Type} {A:SigmaAlgebra X} {B:SigmaAlgebra Y} :
  RandomVariable (product_sa B A) (product_sa A B) (fun '(a, b) => (b, a)).
Proof.
  generalize (pullback_rv (product_sa A B)  (fun '(a, b) => (b, a))).
  apply RandomVariable_proper; try reflexivity.
  apply product_flip. 
Qed.

   Program Instance rev_sa {X Y:Type} (sa : SigmaAlgebra (X * Y)) : SigmaAlgebra (Y * X)
  := {
      sa_sigma := (fun (f:pre_event (Y * X)) =>
        sa_sigma sa (fun (v : (X * Y)) => f (snd v, fst v)))
    }.
   Next Obligation.
     now apply sa_countable_union.
   Qed.
   Next Obligation.
     now apply sa_complement in H.
   Qed.
   Next Obligation.
     apply sa_all.
   Qed.

   Lemma rev_sa_involutive {X Y: Type} (S : SigmaAlgebra (X * Y)) :
     rev_sa (rev_sa S) === S.
   Proof.
     intros; split; intros
     ; unfold rev_sa in *; simpl in *
     ; eapply sa_proper; try apply H
     ; intros [??]; simpl; tauto.
   Qed.

   Lemma rev_sa_generated {X Y: Type} (S:pre_event (X*Y) -> Prop) (propS:Proper (pre_event_equiv ==> iff) S):
     rev_sa (generated_sa S) === generated_sa (fun f => S (fun v => f (snd v, fst v))).
   Proof.
     intros v; split; simpl; intros HH.
     - intros sa saAll.
       specialize (HH (rev_sa sa)).
       simpl in HH.
       eapply sa_proper; try apply HH.
       + now intros [??].
       + intros ??.
         simpl.
         apply saAll; simpl.
         eapply propS; try eapply H.
         now intros [??].
     - intros sa saAll.
       specialize (HH (rev_sa sa)).
       simpl in HH.
       eapply sa_proper; try apply HH.
       + now intros [??].
       + intros ??.
         simpl.
         apply saAll; simpl.
         eapply propS; try eapply H.
         now intros [??].
   Qed.

   Lemma pre_event_set_product_flip {X Y: Type} {A : SigmaAlgebra X} {B : SigmaAlgebra Y} :
     pre_event_equiv (pre_event_set_product (sa_sigma B) (sa_sigma A))
       (fun f : pre_event (Y * X) =>
          pre_event_set_product (sa_sigma A) (sa_sigma B) (fun v : X * Y => f (snd v, fst v))).
   Proof.
     intros x; split
     ; intros [a[b[?[??]]]]
     ; exists b; exists a
     ; do 2 (split; trivial)
     ; intros [??]; simpl.
     - firstorder.
     - specialize (H1 (x0,y)); simpl in *; firstorder.
   Qed.
     
   Lemma rev_sa_product_sa {X Y : Type} (A : SigmaAlgebra X) (B : SigmaAlgebra Y) :
     product_sa B A === rev_sa (product_sa A B).
   Proof.
     unfold product_sa.
     rewrite rev_sa_generated.
     - apply generated_sa_proper.
       apply pre_event_set_product_flip.
     - apply pre_event_set_product_proper; try reflexivity.
   Qed.

  Lemma product_sa_rev {X Y : Type} {A : SigmaAlgebra X} {B : SigmaAlgebra Y}
      (e : pre_event (X * Y))
      (sae : sa_sigma (product_sa A B) e) :
    sa_sigma (product_sa B A) (fun '(a,b) => e (b,a)).
  Proof.
    assert (sa_sigma (rev_sa (product_sa A B)) (fun '(a,b) => e (b,a))).
    {
      simpl; intros.
      specialize (sae sa H).
      revert sae.
      apply sa_proper.
      intros ?.
      destruct x.
      now simpl.
    }
    generalize (rev_sa_product_sa A B (fun '(a,b) => e (b,a))); intros.
    now apply H0 in H.
  Qed.

  Lemma RandomVariable_rev {X Y : Type} {A : SigmaAlgebra X} {B : SigmaAlgebra Y} :
    RandomVariable (product_sa B A) (product_sa A B) (fun '(a,b) => (b,a)).
  Proof.
    unfold RandomVariable.
    intros.
    unfold event_preimage.
    destruct B0.
    generalize (product_sa_rev x s).
    apply sa_proper.
    intros ?.
    destruct x0.
    now simpl.
  Qed.

  Lemma product_ps_rev (X Y : Type) (A : SigmaAlgebra X) (B : SigmaAlgebra Y)
        (ps1 : ProbSpace A) (ps2 : ProbSpace B)
        (e : pre_event (X * Y))
        (sae : sa_sigma (product_sa A B) e) :
    ps_P (ProbSpace := product_ps ps1 ps2) (exist _ _ sae) = 
    ps_P (ProbSpace := product_ps ps2 ps1) (exist _ _ (product_sa_rev e sae)).
  Proof.
    apply Rbar_finite_eq.
    rewrite (explicit_product_product_pse_fst ps1 ps2).
    rewrite (explicit_product_product_pse_snd ps2 ps1).
    apply NonnegExpectation_ext.
    intros ?.
    apply ps_proper.
    intros ?.
    now simpl.
  Qed.

  Section ps_ivector_product.
    

  Program Global Instance trivial_ps {T} (elem:inhabited T) : ProbSpace (trivial_sa T)
    := {|
      ps_P e := if ClassicalDescription.excluded_middle_informative (exists y, proj1_sig e y)
                then 1%R
                else 0%R
    |}.
  Next Obligation.
    repeat red; intros.
    repeat match_destr; firstorder.
  Qed.
  Next Obligation.
    red.
    match_destr.
    - destruct e as [x [n ?]].
      apply (infinite_sum'_one _ n).
      + intros.
        match_destr.
        destruct e as [y ?].
        specialize (H _ _ H1).
        destruct (collection n); simpl in *.
        destruct (collection n'); simpl in *.
        repeat red in H.
        simpl in H.
        destruct s.
        * apply H3 in H0.
          now red in H0.
        * destruct s0.
          -- apply H4 in H2.
             now red in H2.
          -- elim (H x); trivial.
             apply H4.
             now red.
      + match_destr.
        firstorder.
    - eapply infinite_sum'_ext; try apply infinite_sum'0; simpl; intros.
      match_destr.
      firstorder.
  Qed.
  Next Obligation.
    match_destr.
    elim n.
    destruct elem.
    exists X; now red.
  Qed.
  Next Obligation.
    match_destr; lra.
  Qed.
    
  Fixpoint ivector_ps {n} {T} {σ:SigmaAlgebra T} : ivector (ProbSpace σ) n -> ProbSpace (ivector_sa (ivector_const n σ))
    := match n with
       | 0%nat => fun _ => trivial_ps (inhabits tt)
       | S _ => fun '(hd,tl) => product_ps hd (ivector_ps tl)
       end.

  Theorem ivector_sa_product {n} {T} {σ:SigmaAlgebra T} (vps:ivector (ProbSpace σ) n)
          (ve:ivector (event σ) n)
    :
    ps_P (ProbSpace:=ivector_ps vps) (ivector_sa_event ve)
    = ivector_fold_left Rmult (ivector_map (fun '(p,e) => ps_P (ProbSpace:=p) e) (ivector_zip vps ve)) 1.
  Proof.
    cut (forall acc, ps_P (ProbSpace:=ivector_ps vps) (ivector_sa_event ve) * acc =
                  ivector_fold_left Rmult (ivector_map (fun '(p, e) => ps_P e) (ivector_zip vps ve)) acc).
    { intros HH; rewrite <- HH; lra. }
    revert vps ve.
    induction n; simpl.
    - intros.
      match_destr.
      + lra.
      + elim n.
        exists tt; trivial.
    - intros [??] [??] acc.
      rewrite <- IHn.
      rewrite ivector_sa_event_as_prod.
      rewrite product_sa_product.
      lra.
  Qed.

  Lemma ivector_product_section {n} {T} 
        (ivsa : ivector (SigmaAlgebra T) (S n))
        (E:event (ivector_sa ivsa)) :
    forall x, sa_sigma (ivector_sa (ivector_tl ivsa)) (fun y => E (x, y)).
  Proof.
    intros.
    destruct ivsa. 
    apply product_section_fst.
  Qed.

  Instance ivector_ps_section_nneg {n} {T}  {σ:SigmaAlgebra T} 
           (vps : ivector (ProbSpace σ) (S n)) 
           (e : event (ivector_sa (ivector_const (S n) σ))) :
    NonnegativeFunction
        (fun x => ps_P 
                    (ProbSpace := ivector_ps (ivector_tl vps))
                    (exist _ _ (ivector_product_section (ivector_const (S n) σ) e x))).
  Proof.
    intro yy.
    apply ps_pos.
  Qed.
  
  Theorem explicit_ivector_product_pse {n} {T}  {σ:SigmaAlgebra T} 
          (vps : ivector (ProbSpace σ) (S n)) :
    forall e, 
      Finite (ps_P (ProbSpace:=ivector_ps vps) e) =
      NonnegExpectation 
        (Prts := (ivector_hd vps))
        (fun x => ps_P 
                    (ProbSpace := ivector_ps (ivector_tl vps))
                    (exist _ _ (ivector_product_section (ivector_const (S n) σ) e x))).
  Proof.
    intros.
    generalize (explicit_product_product_pse_fst (ivector_hd vps) 
                                                 (ivector_ps (ivector_tl vps)) e); intros.
    etransitivity; [etransitivity |]; [| apply H |].        
    - destruct vps.
      now simpl.
    - f_equal.
      apply NonnegExpectation_ext.
      intro x.
      apply ps_proper.
      intro yy.
      now simpl.
   Qed.

  Lemma ivector_nth_rv {n} {T} (ivsa : ivector (SigmaAlgebra T) n) (idx : nat)
        (idx_lt : (idx < n)%nat) :
        RandomVariable (ivector_sa ivsa) 
                       (ivector_nth idx idx_lt ivsa)
                       (ivector_nth idx idx_lt).
  Proof.
    revert ivsa idx idx_lt.
    induction n; simpl; [lia |].
    intros [??] idx idx_lt.
    destruct idx.
    - apply fst_rv.
    - generalize compose_rv; intros HH.
      cut (
          RandomVariable (product_sa s (ivector_sa i)) (ivector_nth idx (lt_S_n idx n idx_lt) i)
                         (ivector_nth idx (lt_S_n idx n idx_lt) ∘ snd)).
      {
        apply RandomVariable_proper; try reflexivity.
        now intros [??].
      }
      apply (compose_rv (dom2:=ivector_sa i)).
      + apply snd_rv.
      + apply IHn.
  Qed.

  Instance ivector_nth_rv_const {n} {T} {σ:SigmaAlgebra T} idx pf :
            RandomVariable (ivector_sa (ivector_const n σ)) σ
                           (fun x : ivector T n => ivector_nth idx pf x) .
  Proof.
    generalize (ivector_nth_rv (ivector_const n σ) idx pf); intros.
    now rewrite ivector_nth_const in H.
  Qed.
           
  Lemma ivector_nth_independent_rvs_0 {n} {T} {σ:SigmaAlgebra T} 
        (ivec_ps : ivector (ProbSpace σ) n) :
    forall idx2 pf1 pf2,
      independent_rvs (ivector_ps ivec_ps)  σ  σ
                      (fun x => ivector_nth 0 pf1 x)
                      (fun x => ivector_nth (S idx2) pf2 x).
   Proof.
     intros.
     destruct n; try lia.
     assert (RandomVariable (ivector_sa (ivector_const (S n) σ)) σ (fun x : ivector T (S n) => ivector_nth idx2 (lt_S_n idx2 n pf2) (ivector_tl x))).
     {
       generalize (compose_rv (dom1 := (ivector_sa (ivector_const (S n) σ)))
                              (dom2 := (ivector_sa (ivector_const n σ)))
                              ivector_tl
                              (fun x => ivector_nth idx2 (lt_S_n idx2 n pf2) x)); intros.
       apply H; typeclasses eauto.
     }
     assert (independent_rvs (ivector_ps ivec_ps) σ σ ivector_hd
                             (fun x => ivector_nth idx2 _ (ivector_tl x))).
     {
       generalize (independent_rv_compose 
                     (ivector_ps ivec_ps) σ (ivector_sa (ivector_const n σ)) σ σ
                     ivector_hd ivector_tl
                     (fun x => x) (fun x => ivector_nth idx2 (lt_S_n idx2 n pf2) x)
                  ); intros.
       cut_to H0.
       - revert H0.
         now apply independent_rvs_proper.
       - unfold ivector_hd, ivector_tl.
         destruct ivec_ps.
         simpl.
         apply product_independent_fst_snd.
     }
     revert H0.
     apply independent_rvs_proper; try easy.       
     intros [?]; simpl.
     now apply ivector_nth_ext.
  Qed.

  Lemma ivector_nth_independent_rvs {n} {T} {σ:SigmaAlgebra T} 
        (ivec_ps : ivector (ProbSpace σ) n) :
    forall idx1 idx2 pf1 pf2,
      (idx1 < idx2)%nat ->
      independent_rvs (ivector_ps ivec_ps)  σ  σ
                      (fun x => ivector_nth idx1 pf1 x)
                      (fun x => ivector_nth idx2 pf2 x).
  Proof.
    revert ivec_ps.
    induction n; simpl.
    - intros.
      repeat red; intros.
      unfold rv_preimage; simpl.
      repeat match_destr; try lra; intuition.
    - intros [??]?????.
      destruct idx2; [lia |].
      destruct idx1.
      + apply (ivector_nth_independent_rvs_0 (n:=S n) (p,i) idx2).
      + generalize (IHn i idx1 idx2 (lt_S_n idx1 n pf1) (lt_S_n idx2 n pf2) (lt_S_n idx1 idx2 H)).
        unfold independent_rvs, independent_events; intros HH A B.
        specialize (HH A B).
        etransitivity; [| etransitivity; [apply HH |]].
        * generalize (product_sa_product p (ivector_ps i)
                                         Ω
                                         (rv_preimage (fun tl => ivector_nth idx1 (lt_S_n idx1 n pf1) tl) A
                                                      ∩ rv_preimage (fun tl => ivector_nth idx2 (lt_S_n idx2 n pf2) tl) B)); intros HH2.
        rewrite ps_one, Rmult_1_l in HH2.
        rewrite <- HH2.
        apply ps_proper; intros [??]; simpl.
        unfold pre_Ω, event_preimage, pre_event_inter; tauto.
        * { f_equal.
            - generalize (product_sa_product p (ivector_ps i)
                                             Ω
                                             (rv_preimage (fun tl => ivector_nth idx1 (lt_S_n idx1 n pf1) tl) A)); intros HH2.
              rewrite ps_one, Rmult_1_l in HH2.
              rewrite <- HH2.
              apply ps_proper; intros [??]; simpl.
              unfold pre_Ω, event_preimage, pre_event_inter; tauto.
            - generalize (product_sa_product p (ivector_ps i)
                                             Ω
                                             (rv_preimage (fun tl => ivector_nth idx2 (lt_S_n idx2 n pf2) tl) B)); intros HH2.
              rewrite ps_one, Rmult_1_l in HH2.
              rewrite <- HH2.
              apply ps_proper; intros [??]; simpl.
              unfold pre_Ω, event_preimage, pre_event_inter; tauto.
          }
  Qed.
   
  Lemma ivector_nth_pullback {n} {T} {σ:SigmaAlgebra T} 
        (ivec_ps : ivector (ProbSpace σ) n) :
     forall idx pf,
     forall (a : event σ),
       ps_P (ProbSpace := (ivector_nth idx pf ivec_ps)) a = 
       ps_P (ProbSpace := (pullback_ps _ _  (ivector_ps ivec_ps) 
                                       (fun x => ivector_nth idx pf x))) a.
    Proof.
      intros.
      revert ivec_ps idx pf.
      induction n; simpl; [lia |].
      intros.
      destruct idx.
      - match_destr.
        apply product_pullback_fst.
      - match_destr.
        erewrite IHn.
        unfold pullback_ps; simpl.
        generalize (product_measure_product
                      (fun x : event σ => ps_P x) (ps_measure p)
                      (fun x : event (ivector_sa (ivector_const n σ)) => ps_P  x)
                      (ps_measure (ivector_ps i))); intros.
        cut_to H; [|apply product_measure_Hyp_ps].
        specialize (H Ω).
        rewrite ps_all in H.
        simpl in H.
        setoid_rewrite Rmult_1_l in H.
        match goal with
        | [ |- ?X  = _ ] =>
          replace X with (real (Finite X)) by (simpl; now apply ps_proper)
        end.
        f_equal.
        rewrite <- H.
        apply product_ps_proper.
        intros [??]; destruct a; simpl.
        unfold event_preimage, pre_Ω, proj1_sig; simpl.
        tauto.
   Qed.
     
  Instance ivector_take_rv {n} {T} (ivsa : ivector (SigmaAlgebra T) n) (idx : nat)
        (idx_le : (idx <= n)%nat) :
        RandomVariable (ivector_sa ivsa) 
                       (ivector_sa (ivector_take n idx idx_le ivsa))
                       (ivector_take n idx idx_le).
  Proof.
    revert ivsa idx idx_le.
    induction n; simpl.
    - intros.
      destruct idx; [| lia].
      apply rvconst.
    - intros [??] idx idx_le.
      destruct idx.
      + simpl.
        generalize (rvconst (product_sa s (ivector_sa i)) (trivial_sa ()) ()).
        apply RandomVariable_proper; try reflexivity.
        intros [??]; reflexivity.
      + simpl.
        cut (RandomVariable (product_sa s (ivector_sa i))
                            (product_sa s (ivector_sa (ivector_take n idx (le_S_n idx n idx_le) i)))
                            (fun x => (fst x, ivector_take n idx (le_S_n idx n idx_le) (snd x)))).
        { apply RandomVariable_proper; try reflexivity.
          intros [??]; reflexivity.
        }
        apply product_sa_rv.
        * apply fst_rv.
        * apply (compose_rv (dom2:= (ivector_sa i))).
          -- apply snd_rv.
          -- apply IHn.
  Qed.

  
  Instance ivector_take_rv_const {n} {T} {σ:SigmaAlgebra T} (idx : nat)
        (idx_le : (idx <= n)%nat) :
        RandomVariable (ivector_sa (ivector_const n σ))
                       (ivector_sa (ivector_const idx σ))
                       (ivector_take n idx idx_le).
  Proof.
    generalize (ivector_take_rv (ivector_const n σ) idx idx_le); intros.
    now rewrite ivector_take_const in H.
  Qed.


  Lemma ivector_take_pullback {n} {T} {σ:SigmaAlgebra T}
        (ivec_ps : ivector (ProbSpace σ) n) idx pf :
     forall (a : event (ivector_sa (ivector_const idx σ))),
       ps_P (ProbSpace := ivector_ps (ivector_take n idx pf ivec_ps)) a = 
       ps_P (ProbSpace := pullback_ps _ _  (ivector_ps ivec_ps) (ivector_take n idx pf)) a.
  Proof.
    intros.
    revert n pf ivec_ps.
    induction idx.
    - intros.
      destruct a.
      destruct s.
      + assert (event_equiv
                   (exist
                      (fun e0 : pre_event (ivector T 0) =>
                         sa_sigma (ivector_sa (ivector_const 0 σ)) e0) x 
                      (or_introl e))
                   ∅).
        {
          intros ?.
          simpl.
          now rewrite (e x0).
        }
        rewrite H.
        now do 2 rewrite ps_none.
      + assert (event_equiv
                   (exist
                      (fun e0 : pre_event (ivector T 0) =>
                         sa_sigma (ivector_sa (ivector_const 0 σ)) e0) x 
                      (or_intror e))
                   Ω).
        {
          intros ?.
          simpl.
          now rewrite (e x0).
        }
        rewrite H.
        now do 2 rewrite ps_all.
    - intros.
      apply Rbar_finite_eq.
      rewrite explicit_ivector_product_pse.      
      simpl.
      simpl in IHidx.
      destruct n; try lia.
      rewrite explicit_ivector_product_pse, ivector_hd_take.
      apply NonnegExpectation_ext.
      intros ?.
      rewrite ivector_tl_take, IHidx.
      apply ps_proper.
      intros ?.
      tauto.
  Qed.
  
End ps_ivector_product.
Section ps_sequence_product.

  Definition inf_cylinder_event {T} {n} {σ:SigmaAlgebra T} 
             (e : pre_event (ivector T n)) : (pre_event (nat -> T)) :=
    fun (w : nat -> T) => e (sequence_to_ivector w 0%nat n).

  Definition inf_cylinder {T} {σ:SigmaAlgebra T} : (pre_event (nat -> T)) -> Prop :=
    fun (e : pre_event (nat -> T)) =>
      exists (n : nat),
        exists (ee : pre_event (ivector T (S n))),
          sa_sigma (ivector_sa (ivector_const (S n) σ)) ee /\ 
          e === inf_cylinder_event ee.

  Lemma sa_cylinder_drop_fst {T} {σ:SigmaAlgebra T}
        (n : nat) (e : pre_event (ivector T n)) :
    sa_sigma (ivector_sa (ivector_const n σ)) e ->
    sa_sigma (ivector_sa (ivector_const (S n) σ)) 
             (fun v => e (ivector_tl v)).
  Proof.
    simpl; intros.
    apply H0.
    exists pre_Ω; exists e.
    split.
    - apply sa_all.
    - split; trivial.
      intros ?.
      match_destr; simpl.
      unfold pre_Ω; tauto.
  Qed.

  Lemma sa_cylinder_shift {T} {σ:SigmaAlgebra T}
        (n m : nat) (e : pre_event (ivector T n))
        {lt : (n <= m)%nat} :
    sa_sigma (ivector_sa (ivector_const n σ)) e ->
    sa_sigma (ivector_sa (ivector_const m σ)) 
             (fun v => e (ivector_take m n lt v)).
  Proof.
    intros.
    generalize (ivector_take_rv (ivector_const m σ) _ lt); intros.
    unfold RandomVariable in H0.
    rewrite ivector_take_const in H0.
    specialize (H0 (exist _ e H)).
    revert H0.
    apply sa_proper.
    intros ?.
    now simpl.
  Qed.

  Lemma ps_cylinder_drop_fst {T} {σ:SigmaAlgebra T}
        (n : nat) (e : pre_event (ivector T n))
        (sae: sa_sigma (ivector_sa (ivector_const n σ)) e)
        (ps : nat -> ProbSpace σ) :
    ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 1%nat n)) 
         (exist _ _ sae) =
    ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 0%nat (S n)))
         (exist _ _ (sa_cylinder_drop_fst n e sae)).
  Proof.
    generalize (product_sa_product (ps 0%nat) (ivector_ps (sequence_to_ivector ps 1%nat n)) Ω (exist _ e sae)); intros.
    rewrite ps_all in H.
    rewrite Rmult_1_l in H.
    rewrite <- H.
    simpl.
    f_equal.
    apply product_measure_proper.
    - apply ps_measure.
    - apply ps_measure.
    - apply product_measure_Hyp_ps.
    - intros ?.
      unfold pre_Ω.
      match_destr.
      tauto.
    Qed.

  Program Instance ivector_rev_sa {T} {n : nat}
          (sa : SigmaAlgebra (ivector T n)) : SigmaAlgebra (ivector T n)
  := {
      sa_sigma := (fun (f:pre_event (ivector T n)) =>
        sa_sigma sa (fun (v : ivector T n) => f (ivector_rev v)))
    }.
   Next Obligation.
     now apply sa_countable_union.
   Qed.
   Next Obligation.
     now apply sa_complement in H.
   Qed.
   Next Obligation.
     apply sa_all.
   Qed.

   Lemma ivector_sa_rev_sa_pullback {T} {n : nat} (σ:SigmaAlgebra (ivector T n)):
     sa_equiv (ivector_rev_sa σ) (pullback_sa σ ivector_rev).
   Proof.
     intros ?; simpl.
     unfold pullback_sa_sigma.
     split.
     - intros HH.
       eexists; split; [apply HH |]; simpl; intros.
       now rewrite ivector_rev_involutive.
     - intros [? [??]].
       eapply sa_proper; try apply H.
       intros ?.
       rewrite H0.
       now rewrite ivector_rev_involutive.
   Qed.

   Lemma ivector_add_to_end_const {n} {T} (x : T):
     ivector_add_to_end x (ivector_const n x) = (x, ivector_const n x).
   Proof.
     induction n.
     - now simpl.
     - simpl.
       now rewrite IHn.
   Qed.
   
   Lemma ivector_rev_const {n} {T} (x : T):
     ivector_rev (ivector_const n x) = ivector_const n x.
   Proof.
     induction n.
     - now simpl.
     - simpl.
       rewrite IHn.
       now rewrite ivector_add_to_end_const.
   Qed.

   Lemma ivector_sa_rev {T} {σ:SigmaAlgebra T} {n : nat} 
      (e : pre_event (ivector T n))
      (sae : sa_sigma (ivector_sa (ivector_const n σ)) e) :
   sa_sigma (ivector_sa (ivector_const n σ)) (fun v => e (ivector_rev v)).
   Proof.
     assert (sa_sigma (pullback_sa (ivector_sa (ivector_const n σ)) ivector_rev) 
                      (fun v => e (ivector_rev v))).
     {
       simpl.
       unfold pullback_sa_sigma.
       exists e.
       split; trivial.
       now intros.
     }
     generalize (pullback_ivector_sa_rev_alt (ivector_const n σ)); intros.
     specialize (H0 (fun v : ivector T n => e (ivector_rev v))).
     rewrite H0 in H.
     now rewrite ivector_rev_const in H.
  Qed.

  Lemma ps_cylinder_shift {T} {σ:SigmaAlgebra T}
        (n m : nat) (e : pre_event (ivector T n))
        (sae: sa_sigma (ivector_sa (ivector_const n σ)) e)
        (ps : nat -> ProbSpace σ)
        {lt : (n <= m)%nat} :
    ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 0%nat n)) 
         (exist _ _ sae) =
    ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 0%nat m))
         (exist _ _ (sa_cylinder_shift (lt := lt) n m e sae)).
  Proof.
    generalize (ivector_take_pullback (sequence_to_ivector ps 0%nat m) n lt (exist _ _ sae)); intros.
    rewrite <- ivector_take_sequence in H.
    rewrite H.
    unfold pullback_ps; simpl.
    apply ps_proper.
    intros ?.
    now simpl.
  Qed.

  Lemma ps_cylinder_shift1 {T} {σ:SigmaAlgebra T}
        (n m : nat) (e : pre_event (ivector T n))
        (sae: sa_sigma (ivector_sa (ivector_const n σ)) e)
        (ps : nat -> ProbSpace σ)
        {lt : (n <= m)%nat} :
    ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 1%nat n)) 
         (exist _ _ sae) =
    ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 1%nat m))
         (exist _ _ (sa_cylinder_shift (lt := lt) n m e sae)).
  Proof.
    generalize (ivector_take_pullback (sequence_to_ivector ps 1%nat m) n lt (exist _ _ sae)); intros.
    rewrite <- ivector_take_sequence in H.
    rewrite H.
    unfold pullback_ps; simpl.
    apply ps_proper.
    intros ?.
    now simpl.
  Qed.

  Lemma inf_cylinder_shift {T} {σ:SigmaAlgebra T}
        (n : nat) (e : pre_event (ivector T n))
        {sa : sa_sigma (ivector_sa (ivector_const n σ)) e} :
    forall (m : nat) (pf : (n <= m)%nat),
      inf_cylinder_event e === 
      inf_cylinder_event (fun v => e (ivector_take m n pf v)).
  Proof.
    intros.
    unfold inf_cylinder_event.
    intros ?.
    now rewrite (ivector_take_sequence _ _ _ m pf).
  Qed.

  Definition section_seq_event {T} {σ:SigmaAlgebra T} (x : T) 
             (e : pre_event (nat -> T)) : pre_event (nat -> T) :=
    fun (w : (nat -> T)) => e (sequence_cons x w).

  Lemma section_inf_cylinder_sa {T} {σ:SigmaAlgebra T} (x : T) 
        (x0 : nat)
        (x1 : pre_event (ivector T (S x0)))
        (sa : sa_sigma (ivector_sa (ivector_const (S x0) σ)) x1) 
        (pf : ((S x0) <= (S (S x0)))%nat) :
    sa_sigma (ivector_sa (ivector_const (S x0) σ))
             (fun v : ivector T (S x0) => x1 (ivector_take (S (S x0)) (S x0) pf (x, v))).
  Proof.
    generalize (sa_cylinder_shift (S x0) (S (S x0)) x1 (lt := pf) sa); intros.
    apply (ivector_product_section (ivector_const (S (S x0)) σ) (exist _ _ H) x).
  Qed.

  Lemma section_inf_cylinder {T} {σ:SigmaAlgebra T} (x : T) (e : pre_event (nat -> T)) (ecyl : inf_cylinder e):
    inf_cylinder (section_seq_event x e).
  Proof.
    destruct ecyl as [? [? [? ?]]].
    assert (ltS: (S x0 <= S (S x0))%nat) by lia.
    unfold inf_cylinder.
    exists x0.
    exists (fun (v : ivector T (S x0)) => x1 (ivector_take (S (S x0)) (S x0) ltS (x, v))).
    split.
    - now apply section_inf_cylinder_sa.
    - intros ?.
      specialize (H0 (sequence_cons x x2)).
      rewrite H0.
      unfold inf_cylinder_event.
      rewrite sequence_to_ivector_cons.
      rewrite ivector_take_cons.
      now rewrite <- ivector_take_sequence.
  Qed.

  Definition ps_P_cylinder  {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) : R.
    unfold inf_cylinder in ecyl.
    apply constructive_indefinite_description in ecyl; destruct ecyl as [n HH].
    apply constructive_indefinite_description in HH; destruct HH as [ee [sa_ee eq_e]].
    exact (ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 0%nat (S n)))
                (exist _ _ sa_ee)).
  Defined.

  Instance ps_P_cyl_nonneg {T} {σ:SigmaAlgebra T} {n} 
           (ps : nat -> ProbSpace σ)
           (ee : event (ivector_sa (ivector_const (S n) σ))) :
    let vps := sequence_to_ivector ps 0%nat(S n) in
    NonnegativeFunction
          (fun x : T =>
             ps_P (ProbSpace := ivector_ps (ivector_tl vps))
               (exist
                  (sa_sigma (ivector_sa (ivector_tl (ivector_const (S n) σ))))
                  (fun y : ivector T n => ee (x, y))
                  (ivector_product_section (ivector_const (S n) σ) ee x))).
  Proof.
    intros.
    unfold NonnegativeFunction.
    intros.
    apply ps_pos.
  Qed.

  Lemma ps_P_cylinder_expectation {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) : 
    { n & 
      let vps := sequence_to_ivector ps 0%nat (S n) in
      {ee : event (ivector_sa (ivector_const (S n) σ)) |
          sa_sigma (ivector_sa (ivector_const (S n) σ)) ee /\ 
          e === inf_cylinder_event ee /\
          Finite  (ps_P_cylinder ps e ecyl) =
          NonnegExpectation 
            (Prts := (ivector_hd vps))
            (fun x => ps_P 
                        (ProbSpace := ivector_ps (ivector_tl vps))
                        (exist _ _ 
                               (ivector_product_section (ivector_const (S n) σ) 
                                                        ee x)))}}.
  Proof.
    unfold ps_P_cylinder.
    match_destr; intros.
    match_destr; intros.
    match_destr; intros.
    exists x.
    exists (exist _ x0 s).
    split; try easy.
    split; try easy.
    now rewrite explicit_ivector_product_pse.
  Defined.

  Definition ps_P_cylinder_g {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             
             (e : (pre_event (nat -> T)))
             (ecyl :inf_cylinder e) : T -> nonnegreal.
  Proof.
    destruct (ps_P_cylinder_expectation ps e ecyl) as [n [g ?]].
    refine (fun x : T =>
              mknonnegreal (ps_P
               (exist (sa_sigma (ivector_sa (ivector_tl (ivector_const (S n) σ))))
                      (fun y : ivector T n => g (x, y)) (ivector_product_section (ivector_const (S n) σ) g x))) _).
    apply (ps_pos (ProbSpace := ivector_ps (ivector_tl (sequence_to_ivector ps 0%nat (S n))))).
  Defined.
  
  Instance nonneg_fun_nonnegreal {T} (g : T -> nonnegreal) :
    NonnegativeFunction g.
  Proof.
    intro x.
    apply cond_nonneg.
  Qed.

  Lemma ps_P_cylinder_g_proper {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) :
              Finite  (ps_P_cylinder ps e ecyl) =
                NonnegExpectation 
                  (Prts := ps 0%nat)
                  (ps_P_cylinder_g ps e ecyl).
  Proof.
    unfold ps_P_cylinder_g.
    simpl.
    destruct (ps_P_cylinder_expectation ps e ecyl) as [n [ee [_ [_ HH]]]].
    now simpl.
  Qed.

  Lemma ps_P_cylinder_g_rv {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) : 
    RandomVariable σ borel_sa (ps_P_cylinder_g ps e ecyl).
  Proof.
    unfold ps_P_cylinder_g.
    match_destr; match_destr.
    simpl.
    generalize (product_ps_section_measurable_fst (ivector_ps 
                                                        (ivector_tl (sequence_to_ivector ps 0%nat (S x)))) x0); intros.
    revert H.
    apply RandomVariable_proper; try easy.
    intro x1.
    apply ps_proper.
    now intro xx.
  Qed.

  Lemma ps_P_cylinder_g_le_1 {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) : 
    forall x, ps_P_cylinder_g ps e ecyl x <= 1.
  Proof.
    intros.
    unfold ps_P_cylinder_g.
    match_destr; match_destr.
    apply ps_le1.
  Qed.

   Lemma Lim_seq_decreasing_pos (f : nat -> nonnegreal) :
     (forall n, f (S n) <= f n) ->
     Rbar_gt (Lim_seq f) 0 ->
     forall n, f n > 0.
   Proof.
     intro decr.
     contrapose.
     intros.
     rewrite not_forall in H.
     destruct H.
     generalize (cond_nonneg (f x)); intros.
     assert (nonneg (f x) = 0) by lra.
     rewrite <- Lim_seq_incr_n with (N := x).
     rewrite Lim_seq_ext with (v := fun _ => 0).
     - rewrite Lim_seq_const.
       simpl.
       lra.
     - intros.
       assert (f (n + x)%nat <= f x).
       {
         induction n.
         - replace (0 + x)%nat with (x) by lia; lra.
         - apply Rle_trans with (r2 := f (n + x)%nat); trivial.
           now replace (S n + x)%nat with (S (n + x)) by lia.
       }
       generalize (cond_nonneg (f (n + x)%nat)); intros.
       lra.
   Qed.

   Lemma NonnegExpectation_const_minus {Ts} {dom : SigmaAlgebra Ts}
         (Prts : ProbSpace dom)
         (c : R) (rv_X : Ts -> R)
         {rv : RandomVariable dom borel_sa rv_X}
         {nnf : NonnegativeFunction rv_X} 
         {nncf : NonnegativeFunction (rvminus (fun _ : Ts => c) rv_X)}:
     0 <= c ->
     NonnegExpectation (rvminus (fun (_:Ts) => c) rv_X) =
     Rbar_minus c (NonnegExpectation rv_X).
   Proof.
     intros.
     assert (Expectation (rvminus rv_X (fun (_:Ts) => c)) =
             Some (Rbar_minus (NonnegExpectation rv_X) c)).
     {
       generalize (NonnegExpectation_const c H); intros.
       unfold const in H0.
       erewrite Expectation_dif_pos_unique with (p := nnf); try easy.
       - rewrite H0.
         destruct (NonnegExpectation rv_X); now simpl.
       - apply rvconst.
       - rewrite H0.
         now simpl.
     }
     assert (rv_eq (rvminus rv_X (fun _ : Ts => c))
                   (rvopp (rvminus (fun _ : Ts => c) rv_X))).
     {
       intros ?.
       rv_unfold.
       lra.
     }
     rewrite (Expectation_ext H1) in H0.
     rewrite Expectation_opp in H0.
     match_case_in H0; intros.
     - rewrite H2 in H0.
       inversion H0.
       rewrite <- Rbar_opp_minus in H4.
       apply (f_equal Rbar_opp) in H4.
       repeat rewrite Rbar_opp_involutive in H4.
       rewrite (@Expectation_pos_pofrf _ _ _ _ nncf) in H2.  
       inversion H2.
       now rewrite H4 in H5.
     - rewrite H2 in H0.
       congruence.
   Qed.
                                
   Lemma monotone_convergence_descending_bounded {Ts} {dom : SigmaAlgebra Ts}
         (Prts : ProbSpace dom)
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (bound : nonnegreal) 
        (rvx : RandomVariable dom borel_sa X)
        (posX: NonnegativeFunction X) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :

    (forall (omega : Ts), X omega <= bound) ->
    (forall n omega, Xn n omega <= bound) ->
    (forall (n:nat), rv_le X (Xn n)) ->
    (forall (n:nat), rv_le (Xn (S n)) (Xn n)) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
    Lim_seq (fun n => NonnegExpectation (Xn n)) = (NonnegExpectation X).
   Proof.
     generalize (monotone_convergence 
                   (rvminus (fun (x:Ts) => bound) X)
                   (fun n => rvminus (fun (x:Ts) => bound) (Xn n))
                ); intros.
     cut_to H.
     assert (forall n : nat,
                NonnegativeFunction (rvminus (fun _ : Ts => bound) (Xn n))).
     {
       intros ? ?.
       rv_unfold.
       specialize (H1 n x).
       lra.
     }
     assert (NonnegativeFunction (rvminus (fun _ : Ts => bound) X)).
     {
       intros ?.
       rv_unfold.
       specialize (H0 x).
       lra.
     }
     specialize (H H7).
     cut_to H.
     specialize (H H6).
     cut_to H.
     - rewrite NonnegExpectation_const_minus with (nnf := posX) in H; trivial.
       + rewrite Lim_seq_ext with
             (v := fun n => bound - NonnegExpectation (Xn n)) in H.
         * rewrite Lim_seq_minus in H.
           rewrite Lim_seq_const in H.
           -- destruct (Lim_seq (fun n : nat => NonnegExpectation (Xn n))).
              ++ destruct (NonnegExpectation X); simpl in H; try congruence.
                 apply Rbar_finite_eq in H.
                 apply Rbar_finite_eq.
                 lra.
              ++ destruct (NonnegExpectation X); simpl in H; try congruence.
              ++ destruct (NonnegExpectation X); simpl in H; try congruence.
           -- apply ex_lim_seq_const.
           -- apply ex_lim_seq_decr.
              intros.
              generalize (NonnegExpectation_le (Xn (S n)) (Xn n) (H3 n)); intros.
              rewrite <- (H4 (S n)) in H8.
              rewrite <- (H4 n) in H8.
              now simpl in H8.
           -- rewrite Lim_seq_const.
              unfold ex_Rbar_minus, ex_Rbar_plus.
              simpl.
              now destruct (Rbar_opp (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
         * intros.
           rewrite NonnegExpectation_const_minus with (nnf := Xn_pos n); trivial.
           -- rewrite <- (H4 n).
              simpl; lra.
           -- apply cond_nonneg.           
       + apply cond_nonneg.
     - intros ? ?.
       rv_unfold.
       specialize (H2 n a).
       lra.
     - intros ? ?.
       rv_unfold.
       specialize (H3 n a).
       lra.
     - intros.
       rewrite NonnegExpectation_const_minus with (nnf := Xn_pos n); trivial.
       + rewrite <- (H4 n); simpl.
         unfold is_finite.
         simpl.
         apply Rbar_finite_eq.
         lra.
       + apply cond_nonneg.
     - intros.
       specialize (H5 omega).
       rv_unfold.
       apply is_lim_seq_plus'.
       + apply is_lim_seq_const.
       + now apply is_lim_seq_scal_l with (a := -1) (lu := X omega).
     - intros.
       apply rvminus_rv; trivial.
       apply rvconst.
     - apply rvminus_rv; trivial.
       apply rvconst.
  Qed.

  Lemma decr_le_strong f 
        (decr:forall (n:nat), f (S n) <= f n) a b :
    (a <= b)%nat -> f b <= f a.
  Proof.
    revert a.
    induction b; intros.
    - assert (a = 0%nat) by lia.
      subst.
      lra.
    - apply Nat.le_succ_r in H.
      destruct H.
      + apply Rle_trans with (r2 := f b).
        * apply decr.
        * now apply IHb.
      + subst.
        lra.
  Qed.

  Lemma Lim_seq_decreasing_le (f : nat -> R) :
    (forall n, f (S n) <= f n) ->
    forall n, Rbar_le (Lim_seq f) (f n).
  Proof.
    intros.
    rewrite <- Lim_seq_const.
    apply Lim_seq_le_loc.
    exists n.
    intros.
    now apply decr_le_strong.
  Qed.

   Lemma Lim_seq_decreasing_ge (f : nat -> R) (eps : R):
     (forall n, f (S n) <= f n) ->
     Rbar_ge (Lim_seq f) eps ->
     forall n, f n >= eps.
   Proof.
     intros.
     generalize (Lim_seq_decreasing_le f H); intros.
     unfold Rbar_ge in H0.
     assert (Rbar_le (Finite eps) (Finite (f n))).
     {
       now apply Rbar_le_trans with (y := Lim_seq f).
     }
     simpl in H2.
     lra.
   Qed.

  Lemma pre_event_sub_ivector {T} {σ:SigmaAlgebra T}
        (e1 e2 : pre_event (nat -> T)) :
    pre_event_sub e1 e2 ->
    forall (n : nat),
      pre_event_sub 
        (fun (v : ivector T (S n)) =>
           exists (w : nat -> T),
             e1 w /\ (v = sequence_to_ivector w 0 (S n)))
        (fun (v : ivector T (S n)) =>
           exists (w : nat -> T),
             e2 w /\ (v = sequence_to_ivector w 0 (S n))).
   Proof.
     intros ? ? ? [? [? ?]].
     exists x0.
     split; trivial.
     now apply H.
   Qed.

  Lemma decreasing_cyl_nonempty_1  {T} {σ:SigmaAlgebra T}
             (ps : nat -> ProbSpace σ)        
             (es : nat -> (pre_event (nat -> T))) 
             (ecyl : forall n, inf_cylinder (es n)) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    Rbar_gt (Lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n))) 0 ->
    exists (x : T),
    forall n, 
      ((ps_P_cylinder_g ps (es n) (ecyl n)) x) > 0.
  Proof.
    intros.
    generalize (ps_P_cylinder_g_proper ps); intros X.
    pose (f1 := rvlim (fun n x1 => (ps_P_cylinder_g ps (es n) (ecyl n)) x1)).
    assert (NonnegativeFunction f1).
    {
      apply nnflim.
      intros.
      intro z.
      simpl.
      apply cond_nonneg.
    }
    assert (decrx: forall n omega,
             (ps_P_cylinder_g ps (es (S n)) (ecyl (S n))) omega <= 
             (ps_P_cylinder_g ps (es n) (ecyl n)) omega).
    {
      intros.
      unfold ps_P_cylinder_g.
      match_destr; match_destr.
      match_destr; match_destr.
      simpl.
      pose (N := max x x1).
      destruct a as [? [? ?]].
      destruct a0 as [? [? ?]].
      assert (ltx: (S x <= S N)%nat) by lia.      
      assert (ltx1: (S x1 <= S N)%nat) by lia.
      simpl.
      clear H4 H7 X H0.
      generalize (ps_cylinder_shift1 
                    x N
                    (fun y : ivector T x => x0 (omega, y))
                    (ivector_product_section (σ, ivector_const x σ) x0 omega)
                 ); intros cylx.
      specialize (cylx ps (le_S_n _ _ ltx)).
      unfold ivector_sa at 1 in cylx.
      simpl in cylx.
      rewrite cylx.
      generalize (ps_cylinder_shift1
                    x1 N
                    (fun y : ivector T x1 => x2 (omega, y))
                    (ivector_product_section (σ, ivector_const x1 σ) x2 omega)
                 ); intros cylx1.
      specialize (cylx1 ps (le_S_n _ _ ltx1)).
      unfold ivector_sa at 1 in cylx1.
      simpl in cylx1.
      rewrite cylx1.
      apply ps_sub.
      clear cylx cylx1.
      specialize (H n).
      rewrite H3, H6 in H.
      unfold inf_cylinder_event, pre_event_sub in H.
      unfold event_sub, proj1_sig, pre_event_sub.
      intros.
      specialize (H (sequence_cons omega (ivector_to_sequence x3 omega))).
      rewrite (ivector_take_sequence _ 0 _ _ ltx) in H.
      rewrite (ivector_take_sequence _ 0 _ _ ltx1) in H.        
      rewrite sequence_to_ivector_cons in H.
      rewrite <- (ivec_to_seq_to_ivec x3 omega) in H.
      do 2 rewrite ivector_take_cons in H.
      now apply H.
    }
    assert (exfin: forall omega,  
               ex_finite_lim_seq (fun n : nat => 
                                    (ps_P_cylinder_g ps (es n) (ecyl n)) omega)).
    {
      intros.
      apply ex_finite_lim_seq_decr with (M := 0).
      - intros.
        apply decrx.
      - intros.
        apply cond_nonneg.
     }
    assert (RandomVariable σ borel_sa f1).
    {
      apply rvlim_rv.
      - intros.
        simpl.
        apply ps_P_cylinder_g_rv.
      - intros.
        apply exfin.
    }
    generalize (NonnegExpectation_gt_val_nneg (Prts := ps 0%nat) f1 0); intros.
    cut_to H3; try lra.
    - destruct H3.
      exists x.
      intros.
      simpl.
      apply (Lim_seq_decreasing_pos (fun n =>  
                                       (ps_P_cylinder_g ps (es n) (ecyl n)) x)).
      + intros; apply decrx.
      + simpl in f1.
        unfold rvlim in f1.
        unfold f1 in H3.
        specialize (exfin x).
        apply ex_finite_lim_seq_correct in exfin.
        destruct exfin.
        rewrite <- H5.
        simpl.
        apply H3.
    - assert (nneg1: 0 <= 1) by lra.
      generalize (monotone_convergence_descending_bounded 
                    (ps 0%nat) f1  
                    (fun (n : nat) (x1 : T) => 
                       ((ps_P_cylinder_g ps (es n) (ecyl n)) x1)) 
                    (mknonnegreal 1 nneg1) H2 H1); intros.
      erewrite <- H4.
      + rewrite Lim_seq_ext with
            (v := fun n => Finite (ps_P_cylinder ps (es n) (ecyl n))); trivial.
        intros.
        now rewrite (X (es n) (ecyl n)).
      + intros.
        apply ps_P_cylinder_g_rv.
      + intros.
        unfold f1, rvlim.
        generalize (Lim_seq_le_loc 
                      (fun n : nat => ps_P_cylinder_g ps (es n) (ecyl n) omega)
                      (fun _ => 1)); intros.
        cut_to H5.
        * rewrite Lim_seq_const in H5.
          specialize (exfin omega).
          apply ex_finite_lim_seq_correct in exfin.
          destruct exfin.
          rewrite <- H7 in H5.
          now simpl in H5.
        * exists 0%nat.
          intros.
          apply ps_P_cylinder_g_le_1. 
      + intros.
        apply ps_P_cylinder_g_le_1.
      + intros.
        unfold f1, rvlim.
        intros ?.
        generalize (Lim_seq_decreasing_le (fun n0 : nat => ps_P_cylinder_g ps (es n0) (ecyl n0) a)); intros.
        cut_to H5; try easy.
        specialize (H5 n).
        specialize (exfin a).
        apply ex_finite_lim_seq_correct in exfin.
        destruct exfin.
        rewrite <- H7 in H5.
        now simpl in H5.
      + intros ? ?.
        apply decrx.
      + intros.
        now rewrite <- X.
      + intros.
        now apply Lim_seq_correct'.
  Qed.

  Lemma rvpos_nnexp {T} {σ:SigmaAlgebra T} (prts : ProbSpace σ) (X : T -> R)
        (rv : RandomVariable σ borel_sa X)
        (Xpos : NonnegativeFunction X) :
    (forall (t : T), X t > 0) ->
    Rbar_gt (NonnegExpectation X) 0.
  Proof.
    intros.
    assert (event_equiv Ω
                        (union_of_collection
                           (fun n => event_ge σ X (/ (INR (S n)))))).
    {
      intros ?.
      simpl.
      unfold pre_Ω.
      assert (exists n : nat, X x >= / INR (S n)).
      {
        specialize (H x).
        exists (Z.to_nat(up (/ X x))).
        generalize archimed; intros.
        replace (X x) with (/ / (X x)) at 1.
        apply Rle_ge, Rinv_le_contravar.
        - now apply Rinv_0_lt_compat.
        - apply Rle_trans with (r2 := INR (Z.to_nat (up (/ X x)))).
          + rewrite INR_up_pos.
            * specialize (H0 (/ X x)).
              lra.
            * left; apply Rlt_gt, Rinv_0_lt_compat; lra.
          + apply le_INR; lia.
        - apply Rinv_involutive.
          now apply Rgt_not_eq.
      }
      tauto.
    }
    assert (exists n, ps_P (event_ge σ X (/ (INR (S n)))) > 0).
    {
      generalize (ps_zero_countable_union prts (fun n => event_ge σ X (/ (INR (S n))))); intros.
      assert (ps_P (union_of_collection (fun n : nat => event_ge σ X (/ INR (S n)))) = 1).
      {
        rewrite <- H0.
        apply ps_all.
      }
      rewrite <- not_impl_contr in H1.
      cut_to H1; try lra.
      rewrite not_forall in H1.
      destruct H1.
      exists x.
      generalize (ps_pos  (event_ge σ X (/ INR (S x)))); intros.
      lra.
    }
    destruct H1.
    assert (0 < / INR (S x)).
    {
      apply Rinv_0_lt_compat.
      apply lt_0_INR; lia.
    }
    generalize (NonnegExpectation_le (rvscale (mkposreal _ H2)
                                              (EventIndicator (classic_dec (event_ge σ X (/ INR (S x))))))
                                     (rvmult X (EventIndicator (classic_dec (event_ge σ X (/ INR (S x))))))); intros.
    unfold Rbar_gt.
    apply Rbar_lt_le_trans with (y := (NonnegExpectation (rvscale (mkposreal _ H2) 
                                                                  (EventIndicator (classic_dec (event_ge σ X (/ INR (S x)))))))).
    - rewrite NonnegExpectation_scale, NonnegExpectation_EventIndicator.
      simpl; now apply Rmult_lt_0_compat.
    - apply Rbar_le_trans with (y := (NonnegExpectation (rvmult X (EventIndicator (classic_dec (event_ge σ X (/ INR (S x)))))))).
      + apply H3.
        intros ?.
        rv_unfold.
        simpl.
        match_destr; match_destr; try lra.
      + apply NonnegExpectation_le.
        intros ?.
        rv_unfold.
        match_destr; try lra.
        rewrite Rmult_0_r.
        apply Xpos.
   Qed.

  Lemma rvpos_finexp {T} {σ:SigmaAlgebra T} (prts : ProbSpace σ) (X : T -> R)
        (rv : RandomVariable σ borel_sa X)
        (isfe : IsFiniteExpectation prts X) :
    (forall (t : T), X t > 0) ->
    (FiniteExpectation prts X) > 0.
  Proof.
    intros.
    assert (NonnegativeFunction X).
    {
      intros ?.
      specialize (H x).
      lra.
    }
    generalize (rvpos_nnexp prts X rv H0 H); intros.
    rewrite FiniteNonnegExpectation with (posX := H0).
    now rewrite <- IsFiniteNonnegExpectation in H1.
  Qed.

   Lemma rvneg_finexp {T} {σ:SigmaAlgebra T} (prts : ProbSpace σ) (X : T -> R)
        (rv : RandomVariable σ borel_sa X)
        (isfe : IsFiniteExpectation prts X) :
    (forall (t : T), X t < 0) ->
    (FiniteExpectation prts X) < 0.
   Proof.
     intros.
     assert (RandomVariable σ borel_sa (rvopp X)) by typeclasses eauto.
     generalize (rvpos_finexp prts (rvopp X) H0 (IsFiniteExpectation_opp prts X)); intros.     
     rewrite FiniteExpectation_opp in H1.
     cut_to H1; try lra.
     intros; rv_unfold.
     specialize (H t); lra.
  Qed.
     
  Lemma rvgt_finexp {T} {σ:SigmaAlgebra T} (prts : ProbSpace σ) (X : T -> R) (c : R)
        (rv : RandomVariable σ borel_sa X)
        (isfe : IsFiniteExpectation prts X) :
    (forall (t : T), X t > c) ->
    (FiniteExpectation prts X) > c.
  Proof.
    intros.
    assert (RandomVariable σ borel_sa (rvminus X (const c))) by typeclasses eauto.
    generalize (rvpos_finexp prts (rvminus X (const c)) H0  
                             (@IsFiniteExpectation_minus T σ prts X (const c) rv (rvconst σ borel_sa c) isfe
                                                         (IsFiniteExpectation_const prts c))); intros.
    rewrite FiniteExpectation_minus, FiniteExpectation_const in H1.
    cut_to H1; try lra.
    intros.
    specialize (H t).
    rv_unfold; lra.
  Qed.

  Lemma rvlt_finexp  {T} {σ:SigmaAlgebra T} (prts : ProbSpace σ) (X : T -> R)
        (rv : RandomVariable σ borel_sa X)
        (isfe : IsFiniteExpectation prts X) (c : R) :
    (forall (t : T), X t < c) ->
    (FiniteExpectation prts X) < c.
  Proof.
    intros.
    assert (RandomVariable σ borel_sa (rvminus X (const c))) by typeclasses eauto.
    generalize (rvneg_finexp prts (rvminus X (const c)) H0  
                             (@IsFiniteExpectation_minus T σ prts X (const c) rv (rvconst σ borel_sa c) isfe
                                                         (IsFiniteExpectation_const prts c))); intros.
    rewrite FiniteExpectation_minus, FiniteExpectation_const in H1.
    cut_to H1; try lra.
    intros.
    specialize (H t).
    rv_unfold; lra.
  Qed.

  Lemma rvlt_finexp_contra {T} {σ:SigmaAlgebra T} (prts : ProbSpace σ) (X : T -> R)
        (rv : RandomVariable σ borel_sa X)
        (isfe : IsFiniteExpectation prts X) (c : R) :
    (FiniteExpectation prts X) >= c ->
    exists (t : T), X t >= c.
  Proof.
    contrapose.
    intros.
    generalize (rvlt_finexp prts X rv isfe c); intros.
    cut_to H0; try lra.
    rewrite not_exists in H.
    intros.
    specialize (H t); lra.
  Qed.

  Lemma rvlt_nnexp_contra {T} {σ:SigmaAlgebra T} (prts : ProbSpace σ) (X : T -> R)
        (rv : RandomVariable σ borel_sa X)
        (Xpos : NonnegativeFunction X) (c : R) 
        {inh : NonEmpty T}:
    Rbar_ge (NonnegExpectation X) c ->
    exists (t : T), X t >= c.
  Proof.
    intros.
    case_eq (NonnegExpectation X); intros.
    - assert (IsFiniteExpectation prts X).
      {
        unfold IsFiniteExpectation.        
        rewrite Expectation_pos_pofrf with (nnf := Xpos).
        now rewrite H0.
      }
      apply (rvlt_finexp_contra prts _ _ H1); trivial.
      rewrite H0 in H.
      simpl in H.
      rewrite FiniteNonnegExpectation with (posX := Xpos).
      rewrite H0.
      simpl; lra.
    - destruct (Rlt_dec 0 c).
      + assert ((forall t, X t < c) -> IsFiniteExpectation prts X).
        {
          assert (cnneg: 0 <= c) by lra.
          generalize (NonnegExpectation_le X (const c) (nnf2 := nnfconst c cnneg)); intros.
          rewrite NonnegExpectation_const in H1.
          cut_to H1.
          - generalize (IsFiniteExpectation_bounded prts (const 0) X (const c)); intros.
            apply H3.
            + apply Xpos.
            + intros ?.
              unfold const.
              specialize (H2 a); lra.
          - intros ?.
            unfold const.
            specialize (H2 a); lra.
        }
        rewrite <- not_impl_contr in H1.
        rewrite not_forall in H1.
        cut_to H1.
        * destruct H1.
          exists x.
          lra.
        * unfold IsFiniteExpectation.
          rewrite Expectation_pos_pofrf with (nnf := Xpos).
          now rewrite H0.
      + exists inh.
        generalize (Xpos inh); intros.
        lra.
    - rewrite H0 in H.
      now simpl in H.
  Qed.

  Lemma decreasing_cyl_nonempty_1_alt  {T} {σ:SigmaAlgebra T}
        {inh : NonEmpty T}
        (ps : nat -> ProbSpace σ)        
        (es : nat -> (pre_event (nat -> T))) 
        (ecyl : forall n, inf_cylinder (es n)) (eps : posreal) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    (forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) ->
    exists (x : T),
    forall n, 
      ((ps_P_cylinder_g ps (es n) (ecyl n)) x) >= eps.
  Proof.
    intros.
    generalize (ps_P_cylinder_g_proper ps); intros X.
    pose (f1 := rvlim (fun n x1 => (ps_P_cylinder_g ps (es n) (ecyl n)) x1)).
    assert (NonnegativeFunction f1).
    {
      apply nnflim.
      intros.
      intro z.
      simpl.
      apply cond_nonneg.
    }
    assert (decrx: forall n omega,
             (ps_P_cylinder_g ps (es (S n)) (ecyl (S n))) omega <= 
             (ps_P_cylinder_g ps (es n) (ecyl n)) omega).
    {
      intros.
      unfold ps_P_cylinder_g.
      match_destr; match_destr.
      match_destr; match_destr.
      simpl.
      pose (N := max x x1).
      destruct a as [? [? ?]].
      destruct a0 as [? [? ?]].
      assert (ltx: (S x <= S N)%nat) by lia.      
      assert (ltx1: (S x1 <= S N)%nat) by lia.
      simpl.
      clear H4 H7 X H0.
      generalize (ps_cylinder_shift1 
                    x N
                    (fun y : ivector T x => x0 (omega, y))
                    (ivector_product_section (σ, ivector_const x σ) x0 omega)
                 ); intros cylx.
      specialize (cylx ps (le_S_n _ _ ltx)).
      unfold ivector_sa at 1 in cylx.
      simpl in cylx.
      rewrite cylx.
      generalize (ps_cylinder_shift1
                    x1 N
                    (fun y : ivector T x1 => x2 (omega, y))
                    (ivector_product_section (σ, ivector_const x1 σ) x2 omega)
                 ); intros cylx1.
      specialize (cylx1 ps (le_S_n _ _ ltx1)).
      unfold ivector_sa at 1 in cylx1.
      simpl in cylx1.
      rewrite cylx1.
      apply ps_sub.
      clear cylx cylx1.
      specialize (H n).
      rewrite H3, H6 in H.
      unfold inf_cylinder_event, pre_event_sub in H.
      unfold event_sub, proj1_sig, pre_event_sub.
      intros.
      specialize (H (sequence_cons omega (ivector_to_sequence x3 omega))).
      rewrite (ivector_take_sequence _ 0 _ _ ltx) in H.
      rewrite (ivector_take_sequence _ 0 _ _ ltx1) in H.        
      rewrite sequence_to_ivector_cons in H.
      rewrite <- (ivec_to_seq_to_ivec x3 omega) in H.
      do 2 rewrite ivector_take_cons in H.
      now apply H.
    }
    assert (decrx2 : forall omega n,
               ps_P_cylinder_g ps (es (S n)) (ecyl (S n)) omega <= ps_P_cylinder_g ps (es n) (ecyl n) omega).
    {
      intros.
      apply decrx.
    }
    assert (exfin: forall omega,  
               ex_finite_lim_seq (fun n : nat => 
                                    (ps_P_cylinder_g ps (es n) (ecyl n)) omega)).
    {
      intros.
      apply ex_finite_lim_seq_decr with (M := 0).
      - intros.
        apply decrx.
      - intros.
        apply cond_nonneg.
     }
    assert (RandomVariable σ borel_sa f1).
    {
      apply rvlim_rv.
      - intros.
        simpl.
        apply ps_P_cylinder_g_rv.
      - intros.
        apply exfin.
    }
    generalize (rvlt_nnexp_contra (ps 0%nat) f1 H2 H1 eps); intros.
    cut_to H3.
    - destruct H3.
      exists x.
      intros.
      simpl.
      unfold f1 in H3.
      unfold rvlim in H3.
      generalize (Lim_seq_decreasing_le  (fun n : nat => ps_P_cylinder_g ps (es n) (ecyl n) x)); intros.
      cut_to H4.
      + specialize (H4 n).
        apply (Lim_seq_decreasing_ge _ eps (decrx2 x)).
        specialize (exfin x).
        rewrite ex_finite_lim_seq_correct in exfin.
        destruct exfin.
        rewrite <- H6.
        simpl; lra.
      + apply decrx2.
    - assert (nneg1: 0 <= 1) by lra.
      generalize (monotone_convergence_descending_bounded 
                    (ps 0%nat) f1  
                    (fun (n : nat) (x1 : T) => 
                       ((ps_P_cylinder_g ps (es n) (ecyl n)) x1)) 
                    (mknonnegreal 1 nneg1) H2 H1); intros.
      erewrite <- H4.
      + rewrite Lim_seq_ext with
            (v := fun n => Finite (ps_P_cylinder ps (es n) (ecyl n))).
        * unfold Rbar_ge.
          rewrite <- (Lim_seq_const eps).
          apply Lim_seq_le_loc.
          exists 0%nat.
          intros.
          specialize (H0 n).
          simpl; lra.
        * intros.
          now rewrite (X (es n) (ecyl n)).
      + intros.
        apply ps_P_cylinder_g_rv.
      + intros.
        unfold f1, rvlim.
        generalize (Lim_seq_le_loc 
                      (fun n : nat => ps_P_cylinder_g ps (es n) (ecyl n) omega)
                      (fun _ => 1)); intros.
        cut_to H5.
        * rewrite Lim_seq_const in H5.
          specialize (exfin omega).
          apply ex_finite_lim_seq_correct in exfin.
          destruct exfin.
          rewrite <- H7 in H5.
          now simpl in H5.
        * exists 0%nat.
          intros.
          apply ps_P_cylinder_g_le_1. 
      + intros.
        apply ps_P_cylinder_g_le_1.
      + intros.
        unfold f1, rvlim.
        intros ?.
        generalize (Lim_seq_decreasing_le (fun n0 : nat => ps_P_cylinder_g ps (es n0) (ecyl n0) a)); intros.
        cut_to H5; try easy.
        specialize (H5 n).
        specialize (exfin a).
        apply ex_finite_lim_seq_correct in exfin.
        destruct exfin.
        rewrite <- H7 in H5.
        now simpl in H5.
      + intros ? ?.
        apply decrx.
      + intros.
        now rewrite <- X.
      + intros.
        now apply Lim_seq_correct'.
  Qed.
   
   
   Lemma decreasing_cyl_nonempty_2  {T}  {σ:SigmaAlgebra T}
         {inh : NonEmpty T}
         (ps : nat -> ProbSpace σ)        
         (es : nat -> (pre_event (nat -> T))) 
         (ecyl : forall n, inf_cylinder (es n))
         (eps : posreal) :
     (forall n, pre_event_sub (es (S n)) (es n)) ->
     (forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) ->
     exists (x : T),
     (forall n, 
         pre_event_sub
           (section_seq_event x (es (S n)))
           (section_seq_event x (es n))) /\        
     (forall n, 
         (ps_P_cylinder (fun n => ps (S n)) 
                        (section_seq_event x (es n)) 
                        (section_inf_cylinder x (es n) (ecyl n))) >= eps).
  Proof.
    intros.
    destruct (decreasing_cyl_nonempty_1_alt ps es ecyl eps H H0).
    exists x.
    split.
    - intros ? ?.
      unfold section_seq_event.
      apply H.
    - intros.
      specialize (H1 n).
      generalize (ps_P_cylinder_g_proper ps); intros X.
      assert (nonneg (ps_P_cylinder_g ps (es n) (ecyl n) x) =
              (ps_P_cylinder (fun n0 : nat => ps (S n0)) (section_seq_event x (es n)) (section_inf_cylinder x (es n) (ecyl n)))).
      {
        unfold ps_P_cylinder_g.
        repeat match_destr.
        simpl.
        destruct a as [? [? ?]].
        unfold ps_P_cylinder.
        repeat match_destr.
        pose (N := max x0 (S x2)).
        assert (lex2: ((S x2) <= N)%nat) by lia.
        generalize (ps_cylinder_shift (S x2) N x3 s (lt := lex2) (fun n0 => ps (S n0))); intros.
        rewrite H5.

        assert (lex0: (x0 <= N)%nat) by lia.
        generalize (ps_cylinder_shift1 x0 N  (fun y : ivector T x0 => x1 (x, y))
                                      (ivector_product_section (σ, ivector_const x0 σ) x1 x) 
                                      (lt := lex0)
                                      ps
                   ); intros.
        unfold ivector_sa at 1 in H6.
        simpl in H6.
        rewrite H6.
        replace (@sequence_to_ivector (@ProbSpace T σ) (fun n0 : nat => ps (S n0)) O N) with
            (@sequence_to_ivector (@ProbSpace T σ) ps (S O) N).
        - apply ps_proper.
          intros ?.
          simpl.
          unfold inf_cylinder_event, section_seq_event in e0.
          unfold inf_cylinder_event in H3.
          pose (w := fun i => match lt_dec i N with
                              | left pf => ivector_nth i pf x4
                              | right _ => inh
                              end).
          assert (x4 = sequence_to_ivector w 0 N).
          {
            subst w.
            clear.
            induction N; simpl in *; destruct x4; trivial.
            f_equal.
            rewrite sequence_to_ivector_shift.
            rewrite (IHN i) at 1.
            apply sequence_to_ivector_ext; intros n.
            repeat match_destr; try lia.
            now apply ivector_nth_ext.
          }

          specialize (e0 w); simpl in e0.
          specialize (H3 (sequence_cons x w)); simpl in H3.
          replace (ivector_take N x0 lex0 x4) with (sequence_to_ivector (sequence_cons x w) 1 x0).
          + replace (ivector_take N (S x2) lex2 x4) with (w 0%nat, sequence_to_ivector w 1 x2).
            * now rewrite <- e0, <- H3.
            * rewrite cons_sequence_to_ivector.
              rewrite H7.
              now rewrite <- ivector_take_sequence.
          + rewrite sequence_to_ivector_cons_shift.
            rewrite H7.
            now rewrite <- ivector_take_sequence.            
        - apply sequence_to_ivector_shift.
      }
      now rewrite <- H2.
  Qed.

   Definition iter_section_seq_event {T} {σ:SigmaAlgebra T} (x : nat -> T) (N : nat) 
             (e : pre_event (nat -> T)) : pre_event (nat -> T) :=
     fun (w : (nat -> T)) => e (sequence_prefix x w N).


  Lemma iter_section_ivector_product {T} {σ:SigmaAlgebra T} (n1 n2 : nat)
        (E:event (ivector_sa (ivector_const (n1 + n2)%nat σ))) :
    forall (x : ivector T n1),
      sa_sigma (ivector_sa (ivector_const n2 σ)) 
               (fun y => E (ivector_append x y)).
  Proof.
    intros.
    induction n1.
    - apply sa_sigma_event_pre.
    - destruct x.
      simpl.
      assert (pf1:sa_sigma (ivector_sa (ivector_const (n1 + n2) σ)) (fun y => E (t, y))).
      {
        apply product_section_fst.
      }
      specialize (IHn1 (exist _ (fun y => E (t, y)) pf1) i).
      now simpl.
  Qed.

  Lemma iter_section_inf_cylinder_sa {T} {σ:SigmaAlgebra T} (x : nat -> T) (N : nat)
        (x0 : nat)
        (x1 : pre_event (ivector T (S x0)))
        (sa : sa_sigma (ivector_sa (ivector_const (S x0) σ)) x1) 
        (pf : (S x0 <= N + S x0)%nat) :
    sa_sigma (ivector_sa (ivector_const (S x0) σ))
             (fun v : ivector T (S x0) => x1 (ivector_take (N + S x0) (S x0) pf (ivector_append (sequence_to_ivector x 0 N) v))).
  Proof.
    generalize (sa_cylinder_shift (S x0) (N + (S x0))%nat x1 (lt := pf) sa); intros.
    apply (iter_section_ivector_product N  (S x0) (exist _ _ H)).
  Qed.

  Lemma iter_section_inf_cylinder {T} {σ:SigmaAlgebra T} (x : nat -> T) (e : pre_event (nat -> T)) (ecyl : inf_cylinder e) (N : nat) :
    inf_cylinder (iter_section_seq_event x N e).
  Proof.
    destruct ecyl as [? [? [? ?]]].
    exists x0.
    assert (pf: (S x0 <= N + S x0)%nat) by lia.
    unfold iter_section_seq_event, inf_cylinder_event.
    exists (fun (v : ivector T (S x0)) => x1 (ivector_take (N + S x0)%nat (S x0) pf
                                                           (ivector_append (sequence_to_ivector x 0 N) v))).
    split.
    - now apply iter_section_inf_cylinder_sa.
    - intros ?.
      specialize (H0 (sequence_prefix x x2 N)).
      rewrite H0.
      unfold inf_cylinder_event.
      f_equiv.
      rewrite <- sequence_prefix_ivector_append.
      now rewrite <- ivector_take_sequence.
  Qed.

  Definition ps_equiv {T} {σ:SigmaAlgebra T} (ps1 ps2 : ProbSpace σ)
    := forall x, ps_P (ProbSpace:=ps1) x = ps_P (ProbSpace:=ps2) x.

  Global Instance ps_equiv_equiv {T} {σ:SigmaAlgebra T} :
    Equivalence ps_equiv.
  Proof.
    constructor; repeat red; intros.
    - reflexivity.
    - now symmetry.
    - etransitivity; eauto.
  Qed.

  Definition salg_equiv' {T}  (SAlg1 SAlg2 : SemiAlgebra T)
    := forall x, salg_in (SemiAlgebra:=SAlg1) x <-> salg_in (SemiAlgebra:=SAlg2) x.

  Global Instance salg_equiv_equiv' {T} : Equivalence (@salg_equiv' T).
  Proof.
    firstorder.
  Qed.

  Definition alg_equiv' {T}  (Alg1 Alg2 : Algebra T)
    := forall x, alg_in (Algebra:=Alg1) x <-> alg_in (Algebra:=Alg2) x.

  Global Instance alg_equiv_equiv' {T} : Equivalence (@alg_equiv' T).
  Proof.
    firstorder.
  Qed.

  Definition alg_transport {T : Type} {Alg1 Alg2 : Algebra T}
                           (x:alg_set Alg1)
                           (eqq:alg_equiv' Alg1 Alg2) :
    alg_set Alg2.
  Proof.
    destruct x.
    exists x.
    now apply eqq.
  Defined.
  
  Lemma outer_λ_proper' {T : Type} (Alg1 Alg2 : Algebra T)
    (eqq1 : alg_equiv' Alg1 Alg2)
    (λ1 : alg_set Alg1 -> Rbar)
    (λ2 : alg_set Alg2 -> Rbar)
    (eqq2 : forall x y, proj1_sig x = proj1_sig y ->
                   λ1 x = λ2 y) :
    forall e, outer_λ λ1 e = outer_λ λ2 e.
  Proof.
    intros.
    unfold outer_λ.
    apply Rbar_glb_rw; intros.
    split; intros [? [??]].
    - exists (fun n => alg_transport (x0 n) eqq1).
      split.
      + intros ??.
        red.
        destruct (H x1 H1).
        exists x2.
        unfold alg_transport.
        now destruct (x0 x2).
      + rewrite H0.
        unfold outer_λ_of_covers.
        apply ELim_seq_ext; intros.
        apply sum_Rbar_n_proper; trivial; intros ?.
        apply eqq2.
        now destruct (x0 a).
    - exists (fun n => alg_transport (x0 n) (symmetry eqq1)).
      split.
      + intros ??.
        red.
        destruct (H x1 H1).
        exists x2.
        unfold alg_transport.
        now destruct (x0 x2).
      + rewrite H0.
        unfold outer_λ_of_covers.
        apply ELim_seq_ext; intros.
        apply sum_Rbar_n_proper; trivial; intros ?.
        symmetry.
        apply eqq2.
        now destruct (x0 a).
  Qed.        

  Instance SemiAlgebra_Algebra_proper {T} :
    Proper (salg_equiv' ==> alg_equiv') (@SemiAlgebra_Algebra T).
  Proof.
    intros ????; simpl.
    unfold salgebra_algebra_in.
    split; intros [? [?[??]]].
    - exists x1.
      split; [| tauto].
      rewrite Forall_forall in H0 |- *.
      firstorder.
    - exists x1.
      split; [| tauto].
      rewrite Forall_forall in H0 |- *.
      firstorder.
  Qed.

  Lemma premeasure_of_semipremeasure_ext {T : Type}
    {SAlg1 SAlg2 : SemiAlgebra T}
    {eqq1 : salg_equiv' SAlg1 SAlg2}
    {λ1 : salg_set SAlg1 -> Rbar}
    {λ2 : salg_set SAlg2 -> Rbar}
    {meas1 : is_semipremeasure λ1}
    {meas2 : is_semipremeasure λ2}
    {eqq2 : forall (x : {x : pre_event T | salg_in x})
           (y : {x0 : pre_event T | salg_in x0}), ` x = ` y -> λ1 x = λ2 y} :
    forall (x : {x : pre_event T | alg_in x}) (y : {x0 : pre_event T | alg_in x0}),
      ` x = ` y ->
      premeasure_of_semipremeasure λ1 x = premeasure_of_semipremeasure λ2 y.
  Proof.

    intros.
    unfold premeasure_of_semipremeasure.
    repeat match_destr.
    simpl in *; subst.
    destruct a0; destruct a2.
    generalize (semipremeasure_disjoint_list_irrel); intros HH.
    assert (Forall (@salg_in _ SAlg2) x0).
    {
      revert f.
      apply Forall_impl.
      apply eqq1.
    }
    rewrite (HH λ2 meas2 (list_dep_zip x2 f0) (list_dep_zip x0 H3)); trivial.
    - f_equal.
      revert eqq2; clear; intros.
      induction x0; simpl; trivial.
      f_equal.
      + now apply eqq2.
      + apply IHx0.
    - unfold salg_pre, salg_set.
      now rewrite list_dep_zip_map1.
    - unfold salg_pre, salg_set.
      now rewrite list_dep_zip_map1.
    - unfold salg_pre, salg_set.
      repeat rewrite list_dep_zip_map1.
      now rewrite <- H0, H2.
  Qed.
                                                                   
  Lemma semi_μ_proper' {T : Type} (SAlg1 SAlg2 : SemiAlgebra T)
    (eqq1 : salg_equiv' SAlg1 SAlg2)
    (λ1 : salg_set SAlg1 -> Rbar)
    (λ2 : salg_set SAlg2 -> Rbar)
    {meas1 : is_semipremeasure λ1}
    {meas2 : is_semipremeasure λ2}
    (eqq2 : forall x y, proj1_sig x = proj1_sig y ->
                   λ1 x = λ2 y) :
    forall e, semi_μ λ1 e = semi_μ λ2 e.
  Proof.
    unfold semi_μ.
    apply outer_λ_proper'.
    - now apply SemiAlgebra_Algebra_proper.
    - intros.
      now eapply premeasure_of_semipremeasure_ext.
      Unshelve.
      eauto.
      eauto.
  Qed.


  Lemma measurable_rectangle_pm_proper'' {X Y} {A:SigmaAlgebra X} {B:SigmaAlgebra Y}
    (α α' : event A -> Rbar)
    (meas_α : is_measure α) (meas_α' : is_measure α')
    (eqqα:pointwise_relation _ eq α α')
    (β β' : event B -> Rbar)
    (meas_β : is_measure β) (meas_β' : is_measure β')
    (eqqβ:pointwise_relation _ eq β β') (ab:pre_event (X*Y)) (ab2:pre_event (X*Y))
    (pf1:is_measurable_rectangle ab) (pf2:is_measurable_rectangle ab2) :
    (forall x, ab x = ab2 x) ->
    measurable_rectangle_pm α β (exist is_measurable_rectangle ab pf1) =
      measurable_rectangle_pm α' β' (exist _ ab2 pf2).
  Proof.
    intros eqq.
    unfold measurable_rectangle_pm.
    repeat match_destr.
    destruct e as [??].
    destruct e0 as [??].
    simpl in *.
    destruct pf1 as [? [??]].
    destruct pf2 as [? [??]].

    destruct (classic_event_none_or_has x) as [[??]|?].
    - destruct (classic_event_none_or_has x0) as [[??]|?].
      + destruct (i x9 x10) as [_ ?].
        cut_to H5; [| tauto].
        rewrite eqq in H5.
        apply i0 in H5.
        destruct H5.
        f_equal.
        * rewrite eqqα. apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i c x10).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             rewrite eqq in H7.
             apply i0 in H7.
             tauto.
          -- specialize (i0 c x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             rewrite <- eqq in H7.
             apply i in H7.
             tauto.
        * rewrite eqqβ; apply measure_proper; intros c.
          split; intros HH.
          -- specialize (i x9 c).
             destruct i as [_ ?].
             cut_to H7; [| tauto].
             rewrite eqq in H7.
             apply i0 in H7.
             tauto.
          -- specialize (i0 x9 c).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             rewrite <- eqq in H7.
             apply i in H7.
             tauto.
      + rewrite H4.
        destruct (classic_event_none_or_has x2) as [[??]|?].
        * destruct (classic_event_none_or_has x1) as [[??]|?].
          -- specialize (i0 x11 x10).
             destruct i0 as [_ ?].
             cut_to H7; [| tauto].
             rewrite <- eqq in H7.
             apply i in H7.
             destruct H7 as [_ HH].
             apply H4 in HH.
             red in HH; tauto.
          -- rewrite H6.
             repeat rewrite measure_none.
             now rewrite Rbar_mult_0_l, Rbar_mult_0_r.
        * rewrite H5.
          repeat rewrite measure_none.
          now repeat rewrite Rbar_mult_0_r.
    - rewrite H3.
      destruct (classic_event_none_or_has x1) as [[??]|?].
      + destruct (classic_event_none_or_has x2) as [[??]|?].
        * destruct (i0 x9 x10) as [_ ?].
          cut_to H6; [| tauto].
          rewrite <- eqq in H6.
          apply i in H6.
          destruct H6 as [HH _].
          apply H3 in HH.
          red in HH; tauto.
        * rewrite H5.
          repeat rewrite measure_none.
          now rewrite Rbar_mult_0_l, Rbar_mult_0_r.
      + rewrite H4.
        repeat rewrite measure_none.
        now repeat rewrite Rbar_mult_0_l.
  Qed.

  Lemma product_measure_proper' {X Y} {A:SigmaAlgebra X} {B:SigmaAlgebra Y}
    (α α' : event A -> Rbar)
    (meas_α : is_measure α) (meas_α' : is_measure α')
    (eqqα:pointwise_relation _ eq α α')
    (β β' : event B -> Rbar)
    (meas_β : is_measure β) (meas_β' : is_measure β')
    (eqqβ:pointwise_relation _ eq β β')
    (Hyp:measure_rectangle_pm_additive_Hyp α β)
    (Hyp':measure_rectangle_pm_additive_Hyp α' β')
:
    pointwise_relation _ eq
      (product_measure α β)
      (product_measure α' β').
  Proof.
    intros ?.
    unfold product_measure.
    apply semi_μ_proper'.
    - reflexivity.
    - now apply measurable_rectangle_pm_semipremeasure.
    - now apply measurable_rectangle_pm_semipremeasure.
    - intros.
      destruct x; destruct y; simpl in *; subst.
      now apply measurable_rectangle_pm_proper''.
Qed.
    
  Instance product_ps_proper' {X Y} {A:SigmaAlgebra X} {B:SigmaAlgebra Y} :
    Proper (ps_equiv ==> ps_equiv ==> ps_equiv) (@product_ps X Y A B).
  Proof.
    intros ???????.
    simpl.
    f_equal.
    apply product_measure_proper'
    ; try apply ps_measure; intros ?
    ; f_equal; auto
    ; apply product_measure_Hyp_ps.
  Qed.

  Instance ivector_ps_proper {T} {σ:SigmaAlgebra T} {N} :
    Proper (ivector_Forall2 ps_equiv ==> ps_equiv) (@ivector_ps N T σ).
  Proof.
    intros ????.
    induction N; simpl; trivial.
    destruct x; destruct y.
    invcs H.
    apply product_ps_proper'; trivial.
    intros ?.
    now apply IHN.
  Qed.


  Lemma ivector_ps_seq_ext {T} {σ:SigmaAlgebra T} 
    (ps1 ps2 : nat -> ProbSpace σ) N : 
    (forall n, (n <= N)%nat -> ps_equiv (ps1 n) (ps2 n)) -> 
    (ps_equiv (@ivector_ps N T σ (@sequence_to_ivector (@ProbSpace T σ) ps1 O N))
       (@ivector_ps N T σ (@sequence_to_ivector (@ProbSpace T σ) ps2 O N))).
  Proof.
    intros.
    apply ivector_ps_proper.
    apply sequence_to_ivector_Forall2.
    intros; apply H; lia.
  Qed.      

 Lemma ps_P_cylinder_ext {T} {σ:SigmaAlgebra T} 
    (ps1 ps2 : nat -> ProbSpace σ)
    (eqq1:forall n, ps_equiv (ps1 n) (ps2 n))
    (e1 e2 : (pre_event (nat -> T)))
    (eqq2: pre_event_equiv e1 e2)
    (ecyl1 : inf_cylinder e1)
    (ecyl2 : inf_cylinder e2) :
    ps_P_cylinder ps1 e1 ecyl1 = ps_P_cylinder ps2 e2 ecyl2.
  Proof.
    unfold ps_P_cylinder.
    repeat match_destr.
    unfold equiv in *.
    pose (N := max x x1).
    assert (lex: ((S x) <= S N)%nat) by lia.
    rewrite (ps_cylinder_shift (S x) (S N) x0 s ps1 (lt := lex)).
    assert (lex1: ((S x1) <= S N)%nat) by lia.
    rewrite (ps_cylinder_shift (S x1) (S N) x2 s0 ps2 (lt := lex1)).
    rewrite (ivector_ps_seq_ext _ ps2).
    - apply ps_proper.
      intros ?.
      unfold proj1_sig.
      assert (0 < (S N))%nat by lia.
      pose (seq := ivector_to_sequence x3 (ivector_nth 0 H x3)).
      rewrite eqq2 in e0.
      rewrite e0 in e4.
      specialize (e4 seq).
      unfold inf_cylinder_event, seq in e4.
      rewrite (ivec_to_seq_to_ivec x3 (ivector_nth 0 H x3)).
      now do 2 rewrite <- ivector_take_sequence.
    - auto.
  Qed.

   Lemma decreasing_cyl_nonempty_2_alt {T : Type}
            {σ:SigmaAlgebra T}
            {inh : NonEmpty T}
            (ps : nat -> ProbSpace σ)        
            (es : nat -> (pre_event (nat -> T))) 
            (ecyl : forall n, inf_cylinder (es n))
            (eps : posreal) :
     (forall n, pre_event_sub (es (S n)) (es n)) ->
     (forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) ->
     {x : T |
       (forall n, 
           pre_event_sub
             (section_seq_event x (es (S n)))
             (section_seq_event x (es n))) /\        
       (forall n, 
           (ps_P_cylinder (fun n => ps (S n)) 
                          (section_seq_event x (es n)) 
                          (section_inf_cylinder x (es n) (ecyl n))) >= eps)}.
   Proof.
     intros.
     generalize (decreasing_cyl_nonempty_2 ps es ecyl eps H H0); intros.
     now apply constructive_indefinite_description in H1.
  Qed.

  Lemma ps_P_cylinder_decreasing  {T} {σ:SigmaAlgebra T}
             (ps : nat -> ProbSpace σ)        
             (es : nat -> (pre_event (nat -> T))) 
             (ecyl : forall n, inf_cylinder (es n)) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    forall n,
      ps_P_cylinder ps (es (S n)) (ecyl (S n)) <=
      ps_P_cylinder ps (es n) (ecyl n).
  Proof.
    intros.
    unfold ps_P_cylinder.
    repeat match_destr.
    pose (N := max x x1).
    assert (lex: ((S x) <= S N)%nat) by lia.
    rewrite (ps_cylinder_shift (S x) (S N) x0 s ps (lt := lex)).
    assert (lex1: ((S x1) <= S N)%nat) by lia.
    rewrite (ps_cylinder_shift (S x1) (S N) x2 s0 ps (lt := lex1)).
    apply ps_sub.
    intros ?.
    simpl.
    match_destr.
    specialize (H n).
    rewrite e0, e2 in H.
    unfold inf_cylinder_event, pre_event_sub in H.
    specialize (H (sequence_cons t (ivector_to_sequence i t))).
    rewrite (ivector_take_sequence _ 0 _ _ lex) in H.
    rewrite (ivector_take_sequence _ 0 _ _ lex1) in H.
    rewrite sequence_to_ivector_cons in H.
    rewrite <- ivec_to_seq_to_ivec in H.
    do 2 rewrite ivector_take_cons in H.    
    now apply H.
  Qed.


  Lemma decreasing_lim_pos_eps (f : nat -> R) :
    (forall n, f (S n) <= f n) ->
    Rbar_gt (Lim_seq f) 0 ->
    exists (eps : posreal),
      forall n, f n >= eps.
  Proof.
    intros.
    generalize (Lim_seq_decreasing_le f H); intros.
    assert (ex_finite_lim_seq f).
    {
      apply ex_finite_lim_seq_decr with (M := 0); trivial.
      unfold Rbar_gt in H0.
      left.
      assert (Rbar_lt 0 (f n)).
      {
        eapply Rbar_lt_le_trans; trivial.
        apply H0.
      }
      now simpl in H2.
   }
    destruct H2.
    apply is_lim_seq_unique in H2.
    rewrite H2 in H0.
    simpl in H0.
    exists (mkposreal _ H0).
    intro.
    simpl.
    specialize (H1 n).
    rewrite H2 in H1.
    simpl in H1.
    lra.
  Qed.

  Lemma ps_P_cylinder_nneg  {T} {σ:SigmaAlgebra T}
             (ps : nat -> ProbSpace σ)        
             (es : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder es) :
    0 <= ps_P_cylinder ps es ecyl.
  Proof.
    intros.
    unfold ps_P_cylinder.
    repeat match_destr.
    apply ps_pos.
  Qed.

  Section Decreasing_cyl_nonempty.
    Context {T : Type}
            {inh : NonEmpty T}
            {σ:SigmaAlgebra T}
            (ps : nat -> ProbSpace σ)        
            (es : nat -> (pre_event (nat -> T))) 
            (ecyl : forall n, inf_cylinder (es n))
            (decr:(forall n, pre_event_sub (es (S n)) (es n))).

  Definition decreasing_cyl_nonempty_2_seq 
         (eps : posreal) 
         (epsbound:(forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps)) (n:nat) :
    {t : T & { tes : (nat -> (pre_event (nat -> T))) & { tecyl : forall n, inf_cylinder (tes n) |
       (forall i, 
           pre_event_sub
             (tes (S i))
             (tes i)) /\ 
       (forall i, 
           (ps_P_cylinder (fun j => ps (n + S j))%nat
                          (tes i)
                          (tecyl i)) >= eps) }}}.
  Proof.
    induction n.
    - destruct (decreasing_cyl_nonempty_2_alt ps es ecyl eps decr epsbound)
        as [t [tdecr tepsbound]].
      exists t.
      exists (fun i => section_seq_event t (es i)).
      exists (fun i => section_inf_cylinder t (es i) (ecyl i)).
      auto.
    - destruct IHn as [t [tes [tecyl [tdecr tepsbound]]]].
      destruct (decreasing_cyl_nonempty_2_alt
                  (fun i => ps (n + S i)%nat)
                  tes
                  tecyl
                  eps
               )
        as [t' [tdecr' tepsbound']]
      ; trivial.
      exists t'.
      exists (fun i => section_seq_event t' (tes i)).
      exists (fun i => section_inf_cylinder t' (tes i) (tecyl i)).
      split; intros.
      + auto.
      + specialize (tepsbound' i).
        assert (ps_P_cylinder (fun n0 : nat => ps (n + S (S n0))%nat)
                              (section_seq_event t' (tes i))
                              (section_inf_cylinder t' (tes i) (tecyl i)) =
                ps_P_cylinder (fun j : nat => ps (S n + S j)%nat)
                              (section_seq_event t' (tes i))
                              (section_inf_cylinder t' (tes i) (tecyl i))).
        {
          apply ps_P_cylinder_ext; try easy.
          intros ?.
          now replace (n + S (S n0))%nat with (S n + S n0)%nat by lia.
        }
        now rewrite <- H.
  Defined.


  Definition decreasing_cyl_seq 
         (eps : posreal) 
         (epsbound:(forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps)) n :=
    projT1 (decreasing_cyl_nonempty_2_seq eps epsbound n).
  

  Lemma iter_section_seq_event_Sn (x : nat -> T)
             (e : pre_event (nat -> T)) :
    forall N,
      pre_event_equiv
        (iter_section_seq_event x (S N) e)
        (section_seq_event (x N) (iter_section_seq_event x N e)).
  Proof.
    unfold iter_section_seq_event, section_seq_event.
    intros ? ?.
    f_equiv.
    apply sequence_prefix_cons.
  Qed.      

(*
  Lemma iter_decreasing_cyl_section_seq_event 
         (eps : posreal) 
         (epsbound:(forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps)) :
    let x := (decreasing_cyl_seq eps epsbound) in
    let tes := decreasing_cyl_tes eps epsbound in 
    forall j n,
      pre_event_equiv (tes n j)
                      (iter_section_seq_event x n (es j)).
  Proof.
    intros.
    induction n.
    - intros ?.
      now unfold iter_section_seq_event.
    - unfold tes.
      rewrite decreasing_cyl_section_seq_event.
      intros ?.
      rewrite (iter_section_seq_event_Sn x (es j) n x0).
      unfold x.
      unfold section_seq_event.
      specialize (IHn (sequence_cons (decreasing_cyl_seq eps epsbound n) x0)).
      unfold x in IHn.
      now rewrite <- IHn.
  Qed.
*)
  Lemma decreasing_cyl_section_seq_event_alt
         (eps : posreal) 
         (epsbound:(forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps)) :
    let xx := decreasing_cyl_nonempty_2_seq eps epsbound in
    forall j n,
      projT1 (projT2 (xx (S j))) n =
        section_seq_event (projT1 (xx (S j)))
                          (projT1 (projT2 (xx j)) n).
    Proof.
      intros.
      unfold xx.
      simpl.
      match_destr.
      destruct s as [? [? [? ?]]].
      match_destr.
      now destruct a.
    Qed.

  Lemma iter_decreasing_cyl_section_seq_event_alt
         (eps : posreal) 
         (epsbound:(forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps)) :
    let x := (decreasing_cyl_seq eps epsbound) in
    forall j n,
      pre_event_equiv
        (projT1 (projT2 (decreasing_cyl_nonempty_2_seq eps epsbound j)) n)
        (iter_section_seq_event x (S j) (es n)).
  Proof.
    intros.
    induction j.
    - intros ?.
      unfold x, iter_section_seq_event, decreasing_cyl_seq.
      simpl.
      match_destr.
      destruct a.
      now simpl.
    - rewrite decreasing_cyl_section_seq_event_alt.
      rewrite iter_section_seq_event_Sn.
      intros ?.
      unfold x.
      unfold section_seq_event.
      specialize (IHj (sequence_cons (decreasing_cyl_seq eps epsbound (S j)) x0)).
      unfold x in IHj.
      now rewrite <- IHj.
   Qed.

  Lemma iter_decreasing_cyl_eps_ps_P_cyl
         (eps : posreal) 
         (epsbound: forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) :
     let xx := (decreasing_cyl_nonempty_2_seq eps epsbound) in
     forall n j,
       ps_P_cylinder (fun k => ps (j + S k)%nat)
                     (projT1 (projT2 (xx j)) n)
                     (proj1_sig (projT2 (projT2 (xx j))) n) >= eps.
   Proof.
     intros.
     destruct (xx j) as [? [? [? [? ?]]]].
     now simpl.
   Qed.

  Lemma ps_P_cylinder_iter_section_seq1
         (eps : posreal) 
         (epsbound: forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) :
     let x := (decreasing_cyl_seq eps epsbound) in
     forall n j,
       ps_P_cylinder (fun n => ps (j + S n)%nat)
                     (iter_section_seq_event x (S j) (es n))
                     (iter_section_inf_cylinder x (es n) (ecyl n) (S j)) >= eps.
   Proof.
     intros.
     generalize (iter_decreasing_cyl_eps_ps_P_cyl eps epsbound n j); intros.
     eapply Rge_trans; try apply H.
     right.
     apply ps_P_cylinder_ext.
     - reflexivity.
     - symmetry; apply iter_decreasing_cyl_section_seq_event_alt.
   Qed.

  Lemma ps_P_cylinder_iter_section_seq
         (eps : posreal) 
         (epsbound: forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) :
     let x := (decreasing_cyl_seq eps epsbound) in
     forall n j,
       ps_P_cylinder (fun n => ps (j + n)%nat)
                     (iter_section_seq_event x j (es n))
                     (iter_section_inf_cylinder x (es n) (ecyl n) j) >= eps.
    Proof.
      destruct j.
      - unfold iter_section_seq_event.
        simpl.
        generalize (epsbound n); intros.
        eapply Rge_trans; try apply H.
        right.
        apply ps_P_cylinder_ext; try reflexivity.
      - generalize (ps_P_cylinder_iter_section_seq1 eps epsbound n j); intros.
        unfold x.
        eapply Rge_trans; try apply H.
        right.
        apply ps_P_cylinder_ext; try reflexivity.
        intros.
        now replace (S j + n0)%nat with (j + S n0)%nat by lia.
    Qed.


  Lemma decreasing_cyl_nonempty_eps
         (eps : posreal) 
         (epsbound : forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) :
    forall n,
      (es n) (decreasing_cyl_seq eps epsbound).
  Proof.
    intros.
    destruct (ecyl n) as [? [? [? ?]]].
    generalize (ps_P_cylinder_iter_section_seq eps epsbound n); intros.
    destruct (classic (es n (decreasing_cyl_seq eps epsbound))); trivial.
    assert (ps_P_cylinder
              (fun n : nat => ps ((S x) + n))
              (iter_section_seq_event (decreasing_cyl_seq eps epsbound) (S x) (es n))
              (iter_section_inf_cylinder (decreasing_cyl_seq eps epsbound) 
                                         (es n) (ecyl n) (S x)) = 0).
    {
      unfold ps_P_cylinder.
      repeat match_destr.
      rewrite (H0  (decreasing_cyl_seq eps epsbound)) in H2.
      assert (@event_equiv _ (ivector_sa (ivector_const (S x1) σ))
                (exist (sa_sigma (ivector_sa (ivector_const (S x1) σ))) x2 s) 
                (event_none)).
      {
        unfold iter_section_seq_event, inf_cylinder_event in e0.
        intros ?.
        simpl.
        unfold pre_event_none.
        assert (0 < S x1)%nat by lia.
        pose (default := ivector_nth 0 H3 x3).
        specialize (e0 (ivector_to_sequence x3 default)).
        simpl in e0.
        generalize (ivec_to_seq_to_ivec x3 default); intros.
        simpl in H4.
        rewrite <- H4 in e0.
        split; intros; try easy.
        apply H2.
        rewrite <- e0 in H5.
        rewrite (H0 _) in H5.
        unfold inf_cylinder_event in H5.
        rewrite sequence_cons_prefix_shift in H5.
        now rewrite sequence_to_ivector_prefix in H5.
      }
      rewrite H3.
      apply ps_none.
    }
    specialize (H1 (S x)).
    rewrite H3 in H1.
    generalize (cond_pos eps); lra.
  Qed.
      
  Lemma decreasing_cyl_nonempty :
    Rbar_gt (Lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n))) 0 ->
    exists (z : nat -> T), (pre_inter_of_collection es) z.
  Proof.
    intros limpos.
    generalize (ps_P_cylinder_decreasing ps es ecyl decr); intros ps_decr.
    destruct (decreasing_lim_pos_eps (fun n => ps_P_cylinder ps (es n) (ecyl n)) ps_decr limpos) as [eps ?].
    exists (decreasing_cyl_seq eps H).
    intros ?.
    apply decreasing_cyl_nonempty_eps.
  Qed.

  Lemma decreasing_cyl_empty_lim_0 :
    pre_event_equiv (pre_inter_of_collection es) pre_event_none ->
    Lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n)) = 0.
  Proof.
    contrapose.
    intros.
    destruct (decreasing_cyl_nonempty).
    - generalize (Lim_seq_pos (fun n => ps_P_cylinder ps (es n) (ecyl n))); intros.
      cut_to H0.
      + unfold Rbar_gt.
        apply Rbar_le_lt_or_eq_dec in H0.
        destruct H0; trivial.
        unfold not in H.
        rewrite <- e in H.
        tauto.
      + intros.
        apply ps_P_cylinder_nneg.
    - unfold not.
      intros.
      specialize (H1 x).
      unfold pre_event_none in H1.
      tauto.
  Qed.

  Lemma decreasing_cyl_empty_is_lim_0 :
    pre_event_equiv (pre_inter_of_collection es) pre_event_none ->
    is_lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n)) 0.
  Proof.
    intros.
    generalize (decreasing_cyl_empty_lim_0 H); intros.
    rewrite <- H0.
    apply Lim_seq_correct.
    apply ex_lim_seq_decr.
    intros.
    apply ps_P_cylinder_decreasing.
    now intros.
  Qed.

  End Decreasing_cyl_nonempty.


  Lemma inf_cylinder_union {T} {σ:SigmaAlgebra T}
             (es1 es2 : (pre_event (nat -> T))) 
             (ecyl1 : inf_cylinder es1) 
             (ecyl2 : inf_cylinder es2) :
    inf_cylinder (pre_event_union es1 es2).
  Proof.
    intros.
    destruct ecyl1 as [? [? [? ?]]].
    destruct ecyl2 as [? [? [? ?]]].    
    pose (N := max x x1).
    exists N.
    assert (S x <= S N)%nat by lia.
    generalize (inf_cylinder_shift (S x) x0 (sa := H) (S N) H3); intros.
    assert (S x1 <= S N)%nat by lia.
    generalize (inf_cylinder_shift (S x1) x2 (sa := H1) (S N) H5); intros.
    exists (pre_event_union
              (fun v : ivector T (S N) => x0 (ivector_take (S N) (S x) H3 v))
              (fun v : ivector T (S N) => x2 (ivector_take (S N) (S x1) H5 v))).
    split.
    - apply sa_union; now apply sa_cylinder_shift.
    - rewrite H0, H2.
      now rewrite H4, H6.
  Qed.


  Lemma inf_cylinder_inter {T} {σ:SigmaAlgebra T}
             (es1 es2 : (pre_event (nat -> T))) 
             (ecyl1 : inf_cylinder es1) 
             (ecyl2 : inf_cylinder es2) :
    inf_cylinder (pre_event_inter es1 es2).
  Proof.
    intros.
    destruct ecyl1 as [? [? [? ?]]].
    destruct ecyl2 as [? [? [? ?]]].    
    pose (N := max x x1).
    exists N.
    assert (S x <= S N)%nat by lia.
    generalize (inf_cylinder_shift (S x) x0 (sa := H) (S N) H3); intros.
    assert (S x1 <= S N)%nat by lia.
    generalize (inf_cylinder_shift (S x1) x2 (sa := H1) (S N) H5); intros.
    exists (pre_event_inter
              (fun v : ivector T (S N) => x0 (ivector_take (S N) (S x) H3 v))
              (fun v : ivector T (S N) => x2 (ivector_take (S N) (S x1) H5 v))).
    split.
    - apply sa_inter; now apply sa_cylinder_shift.
    - rewrite H0, H2.
      now rewrite H4, H6.
  Qed.

  Lemma inf_cylinder_complement {T} {σ:SigmaAlgebra T}
             (es : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder es) :
    inf_cylinder (pre_event_complement es).
  Proof.
    unfold inf_cylinder in *.
    destruct ecyl as [? [? [? ?]]].
    exists x.
    exists (pre_event_complement x0).
    split.
    - now apply sa_complement.
    - now rewrite H0.
  Qed.

  Lemma inf_cylinder_all {T} {σ:SigmaAlgebra T} :
    inf_cylinder pre_Ω.
  Proof.
    unfold inf_cylinder.
    exists 0%nat.
    exists pre_Ω.
    split; try easy.
    apply sa_all.
  Qed.
  
  Lemma inf_cylinder_none {T} {σ:SigmaAlgebra T} :
    inf_cylinder pre_event_none.
   Proof.
     unfold inf_cylinder.
     exists 0%nat.
     exists pre_event_none.
     split; try easy.
     apply sa_none.
  Qed.

  Lemma inf_cylinder_ext {T} {σ:SigmaAlgebra T} (e1 e2 : pre_event (nat -> T)) :
    pre_event_equiv e1 e2 ->
    inf_cylinder e1 <-> inf_cylinder e2.
  Proof.
    intros.
    unfold inf_cylinder.
    split; intros.
    - destruct H0 as [? [? [? ?]]].
      exists x.
      exists x0.
      split; trivial.
      now rewrite <- H.
    - destruct H0 as [? [? [? ?]]].
      exists x.
      exists x0.
      split; trivial.
      now rewrite H.
  Qed.

  Lemma inf_cylinder_list_union {T} {σ:SigmaAlgebra T}
             (l : list (pre_event (nat -> T))) :
    Forall (fun x : pre_event (nat -> T) => inf_cylinder x) l ->
    inf_cylinder (pre_list_union l).
  Proof.
    intros.
    induction l.
    - generalize (pre_list_union_nil (T := nat -> T)); intros.
      rewrite (inf_cylinder_ext _ _ H0).
      apply inf_cylinder_none.
    - generalize (pre_list_union_cons a l); intros.
      rewrite (inf_cylinder_ext _ _ H0).
      apply inf_cylinder_union.
      + rewrite Forall_forall in H.
        apply H.
        simpl; tauto.
      + apply IHl.
        now apply Forall_inv_tail in H.
   Qed.

  Instance inf_cylinder_algebra {T} (σ:SigmaAlgebra T) : 
    Algebra (nat -> T) :=
    {| alg_in (x : pre_event (nat -> T)) := inf_cylinder x ;
       alg_in_list_union := inf_cylinder_list_union;
       alg_in_complement := inf_cylinder_complement;
       alg_in_all := inf_cylinder_all
    |}.
    
  Lemma ps_P_cylinder_additive  {T} {σ:SigmaAlgebra T}
             (ps : nat -> ProbSpace σ)        
             (es1 es2 : (pre_event (nat -> T))) 
             (ecyl1 : inf_cylinder es1) 
             (ecyl2 : inf_cylinder es2) :
    pre_event_disjoint es1 es2 ->
    ps_P_cylinder ps (pre_event_union es1 es2) 
                  (inf_cylinder_union es1 es2 ecyl1 ecyl2) = 
    ps_P_cylinder ps es1 ecyl1 + ps_P_cylinder ps es2 ecyl2.
  Proof.
    intros.
    unfold ps_P_cylinder.
    repeat match_destr.
    
    pose (N := max (max x x1) x3).
    assert (S x <= S N)%nat by lia.
    generalize (ps_cylinder_shift (S x) (S N) x0 s ps (lt := H0)); intros.
    assert (S x1 <= S N)%nat by lia.
    generalize (ps_cylinder_shift (S x1) (S N) x2 s0 ps (lt := H2)); intros.    
    assert (S x3 <= S N)%nat by lia.
    generalize (ps_cylinder_shift (S x3) (S N) x4 s1 ps (lt := H4)); intros.
    
    rewrite H1, H3, H5.
    clear H1 H3 H5.
    rewrite <- ps_disjoint_union.
    - apply ps_proper.
      intros ?.
      unfold event_union, pre_event_union, proj1_sig.
      clear e e1 e3.
      assert (0 < S N)%nat by lia.
      pose (seq := ivector_to_sequence x5 (ivector_nth 0 H1 x5)).
      specialize (e0 seq).
      unfold pre_event_union in e0.
      rewrite (e2 seq), (e4 seq) in e0.
      unfold inf_cylinder_event in e0.
      symmetry in e0.
      unfold seq in e0.
      rewrite (ivec_to_seq_to_ivec x5 (ivector_nth 0 H1 x5)).
      now do 3 rewrite <- ivector_take_sequence.
    - intros ?.
      unfold proj1_sig.
      unfold pre_event_disjoint in H.
      unfold inf_cylinder_event in e4.
      unfold inf_cylinder_event in e2.
      assert (0 < S N)%nat by lia.
      pose (seq := ivector_to_sequence x5 (ivector_nth 0 H1 x5)).
      specialize (H seq).
      specialize (e2 seq).
      specialize (e4 seq).
      rewrite e2, e4 in H.
      rewrite (ivec_to_seq_to_ivec x5 (ivector_nth 0 H1 x5)).
      do 2 rewrite <- ivector_take_sequence.
      apply H.
   Qed.

  Lemma ps_P_cylinder_none {T} {σ:SigmaAlgebra T} 
          (ps : nat -> ProbSpace σ) :
    ps_P_cylinder ps pre_event_none (alg_in_none (inf_cylinder_algebra σ)) = 0.
  Proof.
    unfold ps_P_cylinder.
    repeat match_destr.
    generalize (ps_none (ivector_ps (sequence_to_ivector ps 0 (S x)))); intros.
    replace 0 with R0 by lra.
    rewrite <- H.
    apply ps_proper.
    intros ?.
    simpl.
    assert (0 < S x)%nat by lia.
    pose (seq := ivector_to_sequence x1 (ivector_nth 0 H0 x1)).
    specialize (e0 seq).
    unfold seq, inf_cylinder_event in e0.
    rewrite (ivec_to_seq_to_ivec x1 (ivector_nth 0 H0 x1)).
    now rewrite e0.
  Qed.

  Instance alg_set_inf_cyl_proper {T} {σ:SigmaAlgebra T} (ps : nat -> ProbSpace σ) :
    Proper (alg_equiv ==> eq) (fun x : alg_set (inf_cylinder_algebra σ) => (ps_P_cylinder ps (` x) (proj2_sig x))).
  Proof.
    intros [??][??] eqq1.
    red in eqq1; simpl in *.
    now apply ps_P_cylinder_ext.
  Qed.

  Instance alg_set_inf_cyl_fin_proper {T} {σ:SigmaAlgebra T} (ps : nat -> ProbSpace σ) :
    Proper (alg_equiv ==> eq) (fun x : alg_set (inf_cylinder_algebra σ) => Finite (ps_P_cylinder ps (` x) (proj2_sig x))).
  Proof.
    intros [??][??] eqq1.
    red in eqq1; simpl in *.
    f_equal.
    now apply ps_P_cylinder_ext.
  Qed.

  Instance ps_P_cylinder_is_premeasure {T} {σ:SigmaAlgebra T} 
          {inh : NonEmpty T}
          (ps : nat -> ProbSpace σ) :
    is_premeasure (fun (x : alg_set (inf_cylinder_algebra σ)) =>
                     ps_P_cylinder ps (proj1_sig x) (proj2_sig x)).
  Proof.
    constructor.
    - apply alg_set_inf_cyl_fin_proper.
    - apply Rbar_finite_eq.
      now apply ps_P_cylinder_none.
    - intros.
      apply ps_P_cylinder_nneg.
    - apply (Ash_1_2_8_b (fun (x : alg_set (inf_cylinder_algebra σ)) =>
                            ps_P_cylinder ps (proj1_sig x) (proj2_sig x))); try easy.
      + apply finitely_additive_2.
        * apply alg_set_inf_cyl_fin_proper.
        * apply Rbar_finite_eq.
          now apply ps_P_cylinder_none.
        * intros.
          simpl.
          rewrite <- ps_P_cylinder_additive; try easy.
          apply Rbar_finite_eq.
          apply ps_P_cylinder_ext; try reflexivity.
      + apply alg_set_inf_cyl_fin_proper.
      + intros.
        rewrite is_Elim_seq_fin.
        apply (decreasing_cyl_empty_is_lim_0 ps B (fun n => proj2_sig (B n)) H H0).
  Qed.

  Definition ps_P_cylinder_measure {T} {σ:SigmaAlgebra T}
    (ps : nat -> ProbSpace σ) :=
      outer_λ
        (fun (x : alg_set (inf_cylinder_algebra σ)) =>
           ps_P_cylinder ps (proj1_sig x) (proj2_sig x)).

  Instance ps_P_cylinder_measure_is_meas_large {T} {σ:SigmaAlgebra T}
    {inh : NonEmpty T}
    (ps : nat -> ProbSpace σ) 
    : is_measure (σ:=μ_measurable_sa (ps_P_cylinder_measure ps)) (ps_P_cylinder_measure ps).
  Proof.
    apply μ_measurable_sa_measure.
  Qed.

  Definition infinite_product_sa {T} (σ:SigmaAlgebra T)
    := generated_sa (alg_in (Algebra:=inf_cylinder_algebra σ)).
  
  Instance ps_P_cylinder_measure_is_meas {T} {σ:SigmaAlgebra T}
    {inh : NonEmpty T}
    (ps : nat -> ProbSpace σ) 
    : is_measure (σ:=infinite_product_sa σ) (ps_P_cylinder_measure ps).
  Proof.
    assert (sub:sa_sub (generated_sa alg_in) (μ_measurable_sa (ps_P_cylinder_measure ps))).
    {
      intros ?.
      apply generated_sa_minimal; simpl; intros.
      apply (outer_λ_is_measurable (fun x1 : alg_set (inf_cylinder_algebra σ) => ps_P_cylinder ps (` x1) (proj2_sig x1)) (exist _ _ H)).
    } 
    generalize (ps_P_cylinder_measure_is_meas_large ps); intros HH.
    apply (is_measure_proper_sub _ _ sub) in HH.
    now simpl in HH.
  Qed.

  Lemma ps_P_cylinder_measure_is_one {T} {σ:SigmaAlgebra T}
    {inh : NonEmpty T}
    (ps : nat -> ProbSpace σ) : 
    ps_P_cylinder_measure ps (@Ω _ (infinite_product_sa σ))  = R1.
  Proof.
    unfold ps_P_cylinder_measure.
    simpl.
    generalize (outer_λ_λ (fun (x : alg_set (inf_cylinder_algebra σ)) =>
                             ps_P_cylinder ps (proj1_sig x) (proj2_sig x)) alg_all); intros HH.
    simpl in HH.
    rewrite HH.
    unfold ps_P_cylinder.
    repeat match_destr.
    unfold inf_cylinder_event in e0.
    unfold  pre_Ω in e0.
    assert (@event_equiv _ (ivector_sa (ivector_const (S x) σ))
              (exist (sa_sigma (ivector_sa (ivector_const (S x) σ))) x0 s)
              Ω).
    {
      intros ?.
      simpl.
      assert (0 < S x)%nat by lia.
      pose (default := ivector_nth 0 H x1).
      specialize (e0 (ivector_to_sequence x1 default)).
      simpl in e0.
      generalize (ivec_to_seq_to_ivec x1 default); intros.
      simpl in H0.
      rewrite <- H0 in e0.
      now rewrite <- e0.
    }
    rewrite H.
    apply Rbar_finite_eq.
    apply ps_all.
  Qed.

  Instance infinite_product_ps {T} {σ:SigmaAlgebra T}
    {inh : NonEmpty T}
    (ps : nat -> ProbSpace σ) : ProbSpace (infinite_product_sa σ)
    := measure_all_one_ps (ps_P_cylinder_measure ps) (ps_P_cylinder_measure_is_one ps).

  Lemma inf_cylinder_sa {T} {σ:SigmaAlgebra T}
        (e : pre_event (nat -> T))
        (cyl : inf_cylinder e) :
    sa_sigma (infinite_product_sa σ) e.
  Proof.
    assert ((alg_in (Algebra:=inf_cylinder_algebra σ)) e) by apply cyl.
    apply (generated_sa_sub _ _  H).
  Qed.

  Lemma infinite_product_ps_cylinder {T} {σ:SigmaAlgebra T}
    {inh : NonEmpty T}
    (ps : nat -> ProbSpace σ) :
    forall (e : pre_event (nat -> T))
           (cyl : inf_cylinder e),
      (ps_P_cylinder ps e cyl) = ps_P (ProbSpace := infinite_product_ps ps)
                                    (exist _ e (inf_cylinder_sa e cyl)).

   Proof.
     intros.
     generalize (outer_λ_λ (fun (x : alg_set (inf_cylinder_algebra σ)) =>
                              ps_P_cylinder ps (proj1_sig x) (proj2_sig x)) (exist _ _ cyl)); intros HH.
     unfold ps_P, infinite_product_ps, measure_all_one_ps, ps_P_cylinder_measure.
     simpl in HH; simpl.
     now rewrite HH.
   Qed.

  Instance seq_nth_rv {T} {σ:SigmaAlgebra T} (idx : nat) :
    RandomVariable (infinite_product_sa σ) σ (fun (x : nat -> T) => x idx).
  Proof.
    intros ?.
    apply inf_cylinder_sa.
    exists idx.
    exists (event_preimage (fun x : ivector T (S idx) => ivector_nth idx (Nat.lt_succ_diag_r idx) x) B).
    split.
    - apply ivector_nth_rv_const.
    - intros ?.
      destruct B.
      unfold event_preimage, proj1_sig, inf_cylinder_event.
      rewrite <- sequence_to_ivector_nth, Nat.add_comm.
      now simpl.
  Qed.

  Lemma inf_cylinder_preimage_nth  {T} {σ:SigmaAlgebra T} idx
        (A : event  σ) :
    (inf_cylinder (rv_preimage (dom := (infinite_product_sa σ))
                                (fun x : nat -> T => x idx) A)).
  Proof.
    exists idx.
    exists (event_preimage (fun x : ivector T (S idx) => ivector_nth idx (Nat.lt_succ_diag_r idx) x) A).
    split.
    - apply ivector_nth_rv_const.
    - intros ?.
      destruct A.
      unfold event_preimage, proj1_sig, inf_cylinder_event.
      rewrite <- sequence_to_ivector_nth, Nat.add_comm.
      now simpl.
  Qed.

  Instance seq_to_ivec_rv {T} {σ:SigmaAlgebra T} (idx : nat) :
    RandomVariable (infinite_product_sa σ)
                   (ivector_sa (ivector_const (S idx) σ))
                   (fun x : nat -> T => sequence_to_ivector x 0 (S idx)).
  Proof.
    intros ?.
    apply inf_cylinder_sa.
    exists idx.
    destruct B.
    now exists x.
  Qed.

  Lemma inf_cylinder_preimage_seq_to_ivector  {T} {σ:SigmaAlgebra T} idx
        (A : event (ivector_sa (ivector_const (S idx) σ))) :
    (inf_cylinder (rv_preimage (dom := (infinite_product_sa σ))
                               (fun x : nat -> T => sequence_to_ivector x 0 (S idx)) A)).
  Proof.
    exists idx.
    destruct A.
    now exists x.
  Qed.
    
  Lemma seq_nth_independent_rvs {T} {σ:SigmaAlgebra T} 
        {inh : NonEmpty T}
        (ps : nat -> ProbSpace σ) :
       forall idx1 idx2,
      (idx1 < idx2)%nat ->
      independent_rvs (infinite_product_ps ps) σ σ
                      (fun x => x idx1)
                      (fun x => x idx2).
  Proof.
    unfold independent_rvs.
    intros.
    unfold independent_events.
    generalize (inf_cylinder_preimage_nth idx1 A); intros cylA.
    generalize (inf_cylinder_preimage_nth idx2 B); intros cylB.
    generalize (infinite_product_ps_cylinder ps _ cylA); intros.
    generalize (infinite_product_ps_cylinder ps _ cylB); intros.
    generalize (infinite_product_ps_cylinder 
                  ps _ (inf_cylinder_inter _ _ cylA cylB)); intros.
    replace (ps_P (@rv_preimage _ T (infinite_product_sa σ) σ
                                (fun x => x idx1) _ A)) with
        (ps_P_cylinder ps (rv_preimage (fun x => x idx1) A) cylA).
    replace  (ps_P (@rv_preimage _ T (infinite_product_sa σ) σ
                                 (fun x => x idx2) _ B)) 
      with (ps_P_cylinder ps (rv_preimage (fun x => x idx2) B) cylB).
    replace (ps_P (event_inter
                     (@rv_preimage _ T (@infinite_product_sa T σ) σ
                                   (fun x => x idx1) _ A)
                     (@rv_preimage _ T (@infinite_product_sa T σ) σ
                                   (fun x => x idx2) _ B))) with
        (ps_P_cylinder ps
                       (pre_event_inter (rv_preimage (fun x => x idx1) A)
                                        (rv_preimage (fun x => x idx2) B))
                       (inf_cylinder_inter (rv_preimage (fun x => x idx1) A)
                                           (rv_preimage (fun x => x idx2) B) cylA cylB)).
    clear H0 H1 H2.
    unfold ps_P_cylinder.
    repeat match_destr.
    pose (xx := max (max x idx2) (max x1 x3)).
    assert (ltx: (S x <= S xx)%nat) by lia.
    assert (ltx1: (S x1 <= S xx)%nat) by lia.
    assert (ltx3: (S x3 <= S xx)%nat) by lia. 
    rewrite (ps_cylinder_shift (S x) (S xx)) with (lt := ltx).
    rewrite (ps_cylinder_shift (S x1) (S xx)) with (lt := ltx1).
    rewrite (ps_cylinder_shift (S x3) (S xx)) with (lt := ltx3).
    generalize (ivector_nth_independent_rvs (sequence_to_ivector ps 0 (S xx)) idx1 idx2); intros.
    unfold independent_rvs, independent_events, rv_preimage in H0.
    assert (idx1 < S xx)%nat by lia.
    assert (idx2 < S xx)%nat by lia.
    specialize (H0 H1 H2 H A B).
    etransitivity; [etransitivity |]; [| apply H0 |].
    - clear H0.
      apply ps_proper.
      intros ?.
      unfold proj1_sig.
      unfold rv_preimage, inf_cylinder_event, event_preimage in e0.
      specialize (e0 (ivector_to_sequence x5 inh)).
      simpl in e0.
      replace (ivector_to_sequence x5 inh 0, sequence_to_ivector (ivector_to_sequence x5 inh) 1 x) with
          (sequence_to_ivector (ivector_to_sequence x5 inh) 0 (S x)) in e0 by now simpl.
      replace (sequence_to_ivector (ivector_to_sequence x5 inh) 0 (S x)) with
          (ivector_take (S xx) (S x) ltx x5) in e0.
      + rewrite <- e0.
        unfold event_inter, pre_event_inter, event_preimage, proj1_sig.
        f_equiv.
        * destruct A.
          f_equiv.
          now rewrite ivector_to_sequence_nth with (pf := H1).
        * destruct B.
          f_equiv.
          now rewrite ivector_to_sequence_nth with (pf := H2).          
      + now rewrite sequence_to_ivector_take with (pf := ltx).
    - f_equal; apply ps_proper; intros ?; unfold proj1_sig, rv_preimage, event_preimage; clear H0.
      + unfold rv_preimage, inf_cylinder_event, event_preimage in e2.
        specialize (e2 (ivector_to_sequence x5 inh)).
        simpl in e2.
        replace (ivector_to_sequence x5 inh 0, sequence_to_ivector (ivector_to_sequence x5 inh) 1 x1) with
          (sequence_to_ivector (ivector_to_sequence x5 inh) 0 (S x1)) in e2 by now simpl.
        replace (ivector_nth idx1 H1 x5) with (ivector_to_sequence x5 inh idx1).
        * rewrite e2.
          f_equiv.
          now rewrite sequence_to_ivector_take with (pf := ltx1).
        * now rewrite ivector_to_sequence_nth with (pf := H1).
     +  unfold rv_preimage, inf_cylinder_event, event_preimage in e4.
        specialize (e4 (ivector_to_sequence x5 inh)).
        simpl in e4.
        replace (ivector_to_sequence x5 inh 0, sequence_to_ivector (ivector_to_sequence x5 inh) 1 x3) with
          (sequence_to_ivector (ivector_to_sequence x5 inh) 0 (S x3)) in e4 by now simpl.
        replace (ivector_nth idx2 H2 x5) with (ivector_to_sequence x5 inh idx2).
        * rewrite e4.
          f_equiv.
          now rewrite sequence_to_ivector_take with (pf := ltx3).
        * now rewrite ivector_to_sequence_nth with (pf := H2).
  Qed.

  Lemma sequence_nth_pullback {T} {σ:SigmaAlgebra T} 
        {inh : NonEmpty T}
        (ps : nat -> ProbSpace σ) :
     forall idx,
     forall (a : event σ),
       ps_P (ProbSpace := ps idx) a = 
       ps_P (ProbSpace := (pullback_ps _ _ (infinite_product_ps ps) 
                                       (fun x => x idx))) a.
  Proof.
    intros.
    generalize (inf_cylinder_preimage_nth idx a); intros cyl.
    generalize (infinite_product_ps_cylinder ps _ cyl); intros.
    simpl in H.
    unfold pullback_ps; simpl.
    rewrite <- H.
    unfold ps_P_cylinder.
    repeat match_destr.
    pose (xx := max idx x).
    assert (ltx: (S x <= S xx)%nat) by lia.
    generalize (ps_cylinder_shift (S x) (S xx)); intros.
    rewrite H0 with (lt := ltx).
    assert (ltidx: (idx < S xx)%nat) by lia.
    generalize (ivector_nth_pullback (sequence_to_ivector ps 0 (S xx)) idx ltidx a); intros.
    rewrite <- sequence_to_ivector_nth in H1.
    replace (idx + 0)%nat with idx in H1 by lia.
    rewrite H1.
    unfold pullback_ps, ps_P.
    repeat match_destr.
    apply ps_proper.
    intros ?.
    destruct a.
    unfold rv_preimage, event_preimage, proj1_sig.
    rewrite <- ivector_to_sequence_nth with (default := inh).
    rewrite (e0 (ivector_to_sequence x1 inh)).
    unfold inf_cylinder_event.
    now rewrite sequence_to_ivector_take with (pf := ltx).
  Qed.

  Lemma sequence_ivector_pullback {T} {σ:SigmaAlgebra T}
        {inh : NonEmpty T}
        (ps : nat -> ProbSpace σ) :
    forall idx,
     forall (a : event (ivector_sa (ivector_const (S idx) σ))),
       ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 0%nat (S idx))) a = 
       ps_P (ProbSpace := pullback_ps _ _ (infinite_product_ps ps)
                                      (fun x => sequence_to_ivector x 0%nat (S idx))) a.
  Proof.
    intros ??.
    generalize (inf_cylinder_preimage_seq_to_ivector idx a); intros cyl.
    generalize (infinite_product_ps_cylinder ps _ cyl); intros.    
    simpl in H.
    replace 
      (ps_P
         (ProbSpace := (pullback_ps (infinite_product_sa σ) (ivector_sa (ivector_const (S idx) σ))
                      (infinite_product_ps ps)
                      (fun x : nat -> T => sequence_to_ivector x 0 (S idx)))) a) 
      with
        (ps_P_cylinder ps
                       (event_preimage
                          (fun x : nat -> T => (x 0%nat, sequence_to_ivector x 1 idx)) a) cyl).
    unfold ps_P_cylinder.
    repeat match_destr.
    pose (xx := max idx x).
    assert (ltx: (S x <= S xx)%nat) by lia.
    generalize (ps_cylinder_shift (S x) (S xx)); intros.
    rewrite H0 with (lt := ltx).
    assert (ltidx: (S idx <= S xx)%nat) by lia.
    generalize (ps_cylinder_shift (S idx) (S xx)); intros.
    destruct a.
    rewrite H1 with (lt := ltidx).
    apply ps_proper.
    intros ?.
    unfold proj1_sig.
    specialize (e0 (ivector_to_sequence x2 inh)).
    simpl in e0.
    unfold inf_cylinder_event in e0.
    rewrite sequence_to_ivector_take with (pf := ltx) in e0.
    rewrite <- e0.
    f_equiv.
    replace  (ivector_to_sequence x2 inh 0,
              sequence_to_ivector (ivector_to_sequence x2 inh) 1 idx)
      with
        (sequence_to_ivector (ivector_to_sequence x2 inh) 0 (S idx)) by now simpl.
    now rewrite sequence_to_ivector_take with (pf := ltidx).
  Qed.

End ps_sequence_product.


Section ps_product'.

  Lemma SimpleExpectation_iso {X Y} (iso:Isomorphism X Y) {σ:SigmaAlgebra X} (ps:ProbSpace σ)
    (f : X -> R)
    {frf : FiniteRangeFunction f}
    {rv : RandomVariable σ borel_sa f}
    :
    SimpleExpectation (Prts:=ps) f =
      SimpleExpectation (Prts:=iso_ps ps iso) (rv:=rv_dom_iso_sa_f iso rv) (f ∘ (iso_b (Isomorphism:=iso))).
  Proof.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext; intros.
    f_equal.
    simpl.
    apply ps_proper; intros ?; simpl.
    unfold pre_event_preimage, pre_event_singleton.
    unfold compose.
    now rewrite iso_b_f.
  Qed.

  Lemma Rbar_NonnegExpectation_iso {X Y} (iso:Isomorphism X Y) {σ:SigmaAlgebra X} (ps:ProbSpace σ)
    (f : X -> Rbar)
    {rv : RandomVariable σ Rbar_borel_sa f}
    {nnf : Rbar_NonnegativeFunction f}
    :
    Rbar_NonnegExpectation (Prts:=ps) f =
      Rbar_NonnegExpectation (Prts:=iso_ps ps iso) (f ∘ (iso_b (Isomorphism:=iso))).
  Proof.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup.
    apply Lub_Rbar_eqset; intros.
    split; intros [?[?[?[[??]?]]]]; subst.
    - exists ((x0 ∘ (iso_b (Isomorphism:=iso)))).
      exists (rv_dom_iso_sa_f iso x1), _.
      split.
      + split.
        * unfold compose; intros ?.
          apply H.
        * intros ?.
          apply H0.
      + now rewrite <- SimpleExpectation_iso.
    - exists ((x0 ∘ (iso_f (Isomorphism:=iso)))).
      assert (rv' : RandomVariable σ borel_sa (x0 ∘ iso_f)).
      {
        apply (rv_dom_iso_sa_b _ _ _ iso).
        unfold compose.
        revert x1.
        apply RandomVariable_proper; try reflexivity.
        now intros ?; rewrite iso_f_b.
      }
      exists _, _.
      split.
      + split.
        * unfold compose; intros ?.
          apply H.
        * intros ?.
          eapply Rbar_le_trans; [apply H0 |].
          unfold compose.
          rewrite iso_b_f.
          apply Rbar_le_refl.
      + rewrite (SimpleExpectation_iso iso).
        apply SimpleExpectation_ext; intros ?.
        unfold compose.
        now rewrite iso_f_b.
  Qed.

  Lemma Rbar_Expectation_iso {X Y} (iso:Isomorphism X Y) {σ:SigmaAlgebra X} (ps:ProbSpace σ)
    (f : X -> Rbar)
    {rv : RandomVariable σ Rbar_borel_sa f}
    :
    Rbar_Expectation (Prts:=ps) f =
      Rbar_Expectation (Prts:=iso_ps ps iso) (f ∘ (iso_b (Isomorphism:=iso))).
  Proof.
    unfold Rbar_Expectation.
    now repeat rewrite (Rbar_NonnegExpectation_iso iso) by typeclasses eauto.
  Qed.

  Lemma SimpleExpectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g
    {rvf:RandomVariable σ1 borel_sa f}
    {rvg:RandomVariable σ2 borel_sa g}
    {ffrf : FiniteRangeFunction f}
    {gfrf : FiniteRangeFunction g} :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    SimpleExpectation (Prts:=ps1) f = SimpleExpectation (Prts:=ps2) g.
  Proof.
    intros.
    assert (rvg' : RandomVariable σ1 borel_sa g).
    {
      revert rvg.
      now apply RandomVariable_proper.
    } 

    transitivity (@SimpleExpectation Ts σ1 ps1 g rvg' gfrf).
    - now apply SimpleExpectation_ext.
    - unfold SimpleExpectation.
      f_equal.
      apply map_ext; intros.
      f_equal.
      now apply H0.
  Qed.
    
  Lemma Rbar_NonnegExpectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g {fnneg : Rbar_NonnegativeFunction f} {gnneg : Rbar_NonnegativeFunction g} :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    Rbar_NonnegExpectation (Prts:=ps1) f = Rbar_NonnegExpectation (Prts:=ps2) g.
  Proof.
    intros.
    unfold Rbar_NonnegExpectation.
    apply Lub_Rbar_eqset; intros.
    split; intros [?[?[?[[??]?]]]]; subst.
    - exists x0.
      assert (RandomVariable σ2 borel_sa x0).
      {
        revert x1.
        now apply RandomVariable_proper.
      }
      exists _, _.
      split; [split |]; trivial.
      + now intros ?; rewrite <- H1.
      + apply SimpleExpectation_ext_ps.
        * now symmetry.
        * intros.
          symmetry.
          apply H0.
          now symmetry.
        * reflexivity.
    - exists x0.
      assert (RandomVariable σ1 borel_sa x0).
      {
        revert x1.
        now apply RandomVariable_proper.
      }
      exists _, _.
      split; [split |]; trivial.
      + now intros ?; rewrite H1.
      + now apply SimpleExpectation_ext_ps.
  Qed.          
  
  Lemma Rbar_Expectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    Rbar_Expectation (Prts:=ps1) f = Rbar_Expectation (Prts:=ps2) g.
  Proof.
    unfold Rbar_Expectation; intros.
    rewrite (Rbar_NonnegExpectation_ext_ps ps1 ps2 (Rbar_pos_fun_part f) (Rbar_pos_fun_part g)), (Rbar_NonnegExpectation_ext_ps ps1 ps2 (Rbar_neg_fun_part f) (Rbar_neg_fun_part g)); trivial
    ; now unfold Rbar_neg_fun_part, Rbar_pos_fun_part; intros ?; rewrite H1.
  Qed.

  Lemma Expectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    Expectation (Prts:=ps1) f = Expectation (Prts:=ps2) g.
  Proof.
    intros.
    repeat rewrite Expectation_Rbar_Expectation.
    apply Rbar_Expectation_ext_ps; trivial.
    intros ?; congruence.
  Qed.

  Instance Rbar_IsFiniteExpectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    Rbar_IsFiniteExpectation ps1 f -> Rbar_IsFiniteExpectation ps2 g.
  Proof.
    unfold Rbar_IsFiniteExpectation; intros.
    now rewrite <- (Rbar_Expectation_ext_ps _ _ _ _ H H0 H1).
  Qed.

  Instance IsFiniteExpectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    IsFiniteExpectation ps1 f -> IsFiniteExpectation ps2 g.
  Proof.
    unfold IsFiniteExpectation; intros.
    now rewrite <- (Expectation_ext_ps _ _ _ _ H H0 H1).
  Qed.

  Lemma Rbar_FiniteExpectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g
    {isfe1: Rbar_IsFiniteExpectation ps1 f}
    {isfe2: Rbar_IsFiniteExpectation ps2 g}
    :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    Rbar_FiniteExpectation ps1 f = Rbar_FiniteExpectation ps2 g.
  Proof.
    intros.

    cut (Some (Finite (Rbar_FiniteExpectation ps1 f)) = Some (Finite (Rbar_FiniteExpectation ps2 g))); [congruence |].
    repeat rewrite <- (Rbar_FiniteExpectation_Rbar_Expectation _ _).
    now apply Rbar_Expectation_ext_ps.
  Qed.

    Lemma FiniteExpectation_ext_ps {Ts} {σ1 σ2: SigmaAlgebra Ts} (ps1 : ProbSpace σ1) (ps2 : ProbSpace σ2) f g
    {isfe1: IsFiniteExpectation ps1 f}
    {isfe2: IsFiniteExpectation ps2 g}
    :
    sa_equiv σ1 σ2 ->
    (forall (A:event σ1) (B:event σ2), pre_event_equiv A B -> ps_P (ProbSpace:=ps1) A = ps_P (ProbSpace:=ps2) B) ->
    rv_eq f g ->
    FiniteExpectation ps1 f = FiniteExpectation ps2 g.
  Proof.
    intros.

    cut (Some (Finite (FiniteExpectation ps1 f)) = Some (Finite (FiniteExpectation ps2 g))); [congruence |].
    repeat rewrite <- (FiniteExpectation_Expectation _ _).
    now apply Expectation_ext_ps.
  Qed.

  Global Instance Rbar_Expectation_ext_ps' {Ts} {σ: SigmaAlgebra Ts} :
    Proper (ps_equiv ==> rv_eq ==> eq) (@Rbar_Expectation Ts σ).
  Proof.
    intros ??????.
    apply Rbar_Expectation_ext_ps; trivial.
    - reflexivity.
    - intros.
      rewrite H.
      now apply ps_proper.
  Qed.

  Global Instance Expectation_ext_ps' {Ts} {σ: SigmaAlgebra Ts} :
    Proper (ps_equiv ==> rv_eq ==> eq) (@Expectation Ts σ).
  Proof.
    intros ??????.
    apply Expectation_ext_ps; trivial.
    - reflexivity.
    - intros.
      rewrite H.
      now apply ps_proper.
  Qed.

  Global Instance Rbar_IsFiniteExpectation_ext_ps' {Ts} {σ: SigmaAlgebra Ts} :
    Proper (ps_equiv ==> rv_eq ==> iff) (@Rbar_IsFiniteExpectation Ts σ).
  Proof.
    intros ??????.
    split; apply Rbar_IsFiniteExpectation_ext_ps; trivial; try reflexivity.
    - intros.
      rewrite H.
      now apply ps_proper.
    - intros.
      rewrite H.
      now apply ps_proper.
    - now symmetry.
  Qed.

  Global Instance IsFiniteExpectation_ext_ps' {Ts} {σ: SigmaAlgebra Ts} :
    Proper (ps_equiv ==> rv_eq ==> iff) (@IsFiniteExpectation Ts σ).
  Proof.
    intros ??????.
    split; apply IsFiniteExpectation_ext_ps; trivial; try reflexivity.
    - intros.
      rewrite H.
      now apply ps_proper.
    - intros.
      rewrite H.
      now apply ps_proper.
    - now symmetry.
  Qed.

  Lemma Rbar_FiniteExpectation_ext_ps' {Ts} {σ: SigmaAlgebra Ts}
    (ps1 ps2 : ProbSpace σ)
    (pseq : ps_equiv ps1 ps2)
    f g
    (fgeq:rv_eq f g)
    {fisfe : Rbar_IsFiniteExpectation ps1 f}
    {gisfe : Rbar_IsFiniteExpectation ps2 g}
    :
    Rbar_FiniteExpectation ps1 f = Rbar_FiniteExpectation ps2 g.
  Proof.
    apply Rbar_FiniteExpectation_ext_ps; trivial; try reflexivity.
    - intros.
      rewrite pseq.
      now apply ps_proper.
  Qed.

    Lemma FiniteExpectation_ext_ps' {Ts} {σ: SigmaAlgebra Ts}
    (ps1 ps2 : ProbSpace σ)
    (pseq : ps_equiv ps1 ps2)
    f g
    (fgeq:rv_eq f g)
    {fisfe : IsFiniteExpectation ps1 f}
    {gisfe : IsFiniteExpectation ps2 g}
    :
    FiniteExpectation ps1 f = FiniteExpectation ps2 g.
  Proof.
    apply FiniteExpectation_ext_ps; trivial; try reflexivity.
    - intros.
      rewrite pseq.
      now apply ps_proper.
  Qed.

  Context {X Y:Type}.
  Context {A:SigmaAlgebra X}.
  Context {B:SigmaAlgebra Y}.

  Context (ps1 : ProbSpace A).
  Context (ps2 : ProbSpace B).

  Existing Instance Rbar_nneg_section_fst.
  Existing Instance Rbar_nneg_section_snd.


Instance tonelli_nnexp_section_snd_rv (f : (X * Y) -> Rbar) 
      {nnf : Rbar_NonnegativeFunction f} 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} :
    RandomVariable B Rbar_borel_sa
                   (fun y => Rbar_NonnegExpectation (fun x => f (x, y))).
  Proof.
    assert (nnfflip: Rbar_NonnegativeFunction (f ∘ (fun '(a, b) => (b, a)))).
    {
      intros [??].
      apply nnf.
    }
    apply (@tonelli_nnexp_section_fst_rv _ _ B A ps1 (f ∘ (fun '(a, b) => (b,a))) nnfflip).
    apply (compose_rv (dom2:=product_sa A B)); trivial.
    apply product_flip_rv.
  Qed.

  Lemma Rbar_Expectation_product_flip (f : (X * Y) -> Rbar)
    {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} :
    Rbar_Expectation (Prts:=product_ps ps1 ps2) f =
      Rbar_Expectation (Prts:=product_ps ps2 ps1) (f ∘ (fun '(a, b) => (b, a))).
  Proof.
    rewrite (Rbar_Expectation_iso (Isomorphism_flip) _ _).
    apply Rbar_Expectation_ext_ps.
    - rewrite (product_flip B A).
      apply pullback_sa_proper; try reflexivity.
      now intros [??].
    - intros [??] [??] ?.
      rewrite product_ps_rev.
      simpl.
      f_equal.
      apply product_ps_proper; intros [??].
      apply H.
    - now intros [??].
  Qed.

  Lemma Rbar_NonnegExpectation_product_flip (f : (X * Y) -> Rbar)
    {nnf : Rbar_NonnegativeFunction f}
    {nnfflip: Rbar_NonnegativeFunction (f ∘ (fun '(a, b) => (b, a)))}
    {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} 
    {rvflip : RandomVariable (product_sa B A) Rbar_borel_sa (f ∘ (fun '(a, b) => (b, a)))} :
    Rbar_NonnegExpectation (Prts:=product_ps ps1 ps2) f =
      Rbar_NonnegExpectation (Prts:=product_ps ps2 ps1) (f ∘ (fun '(a, b) => (b, a))).
  Proof.
    cut (Some (Rbar_NonnegExpectation (Prts:=product_ps ps1 ps2) f) =
           Some (Rbar_NonnegExpectation (Prts:=product_ps ps2 ps1) (f ∘ (fun '(a, b) => (b, a))))); [congruence |].
    repeat rewrite <- Rbar_Expectation_pos_pofrf.
    now apply Rbar_Expectation_product_flip.
  Qed.

  Lemma Rbar_FiniteExpectation_product_flip (f : (X * Y) -> Rbar)
    {rv : RandomVariable (product_sa A B) Rbar_borel_sa f}
    {isfe1:Rbar_IsFiniteExpectation (product_ps ps1 ps2) f}
    {isfe2:Rbar_IsFiniteExpectation (product_ps ps2 ps1) (f ∘ (fun '(a, b) => (b, a)))}
    :
    Rbar_FiniteExpectation (product_ps ps1 ps2) f =
      Rbar_FiniteExpectation (product_ps ps2 ps1) (f ∘ (fun '(a, b) => (b, a))).
  Proof.
    generalize (Rbar_Expectation_product_flip f).
    repeat rewrite (Rbar_FiniteExpectation_Rbar_Expectation _ _).
    congruence.
  Qed.

  Instance Rbar_IsFiniteExpectation_product_flip (f : (X * Y) -> Rbar)
    {rv : RandomVariable (product_sa A B) Rbar_borel_sa f}
    {isfe1:Rbar_IsFiniteExpectation (product_ps ps1 ps2) f} : 
    Rbar_IsFiniteExpectation (product_ps ps2 ps1) (f ∘ (fun '(a, b) => (b, a))).
  Proof.
    unfold Rbar_IsFiniteExpectation.
    now rewrite <- Rbar_Expectation_product_flip.
  Qed.

  Lemma tonelli_nnexp_section_snd (f : (X * Y) -> Rbar) 
        {nnf : Rbar_NonnegativeFunction f}
        {nnf2 : Rbar_NonnegativeFunction (fun y => Rbar_NonnegExpectation (fun x => f (x, y)))}
        {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} :
    Rbar_NonnegExpectation (Prts := product_ps ps1 ps2) f =
    Rbar_NonnegExpectation (fun y => Rbar_NonnegExpectation (fun x => f (x, y))).
  Proof.
    assert (nnfflip: Rbar_NonnegativeFunction (f ∘ (fun '(a, b) => (b, a)))).
    {
      intros [??].
      apply nnf.
    }

    assert (nnf3 : Rbar_NonnegativeFunction
              (fun x : Y =>
                 Rbar_NonnegExpectation (fun y : X => (f ∘ (fun '(a, b) => (b, a))) (x, y)))).
    {
      intros ?.
      apply Rbar_NonnegExpectation_pos.
    }
    generalize (@tonelli_nnexp_section_fst _ _ _ _ ps2 ps1 (f ∘ (fun '(a, b) => (b, a))) _ _); intros HH.
    cut_to HH.
    - etransitivity; [| etransitivity]; [| apply HH |].
      + apply Rbar_NonnegExpectation_product_flip; trivial.
        apply (compose_rv (dom2:=product_sa A B)); trivial.
        apply product_flip_rv.
      + apply Rbar_NonnegExpectation_pf_irrel.
    - apply (compose_rv (dom2:=product_sa A B)); trivial.
      apply product_flip_rv.
  Qed.

  Theorem fubini_section_snd (f : (X * Y) -> Rbar) 
      {rv : RandomVariable (product_sa A B) Rbar_borel_sa f} 
      {isfe1 : Rbar_IsFiniteExpectation (product_ps ps1 ps2) f}
      {isfe2 : forall y, Rbar_IsFiniteExpectation ps1 (fun x => f (x, y)) }
      {isfe3 : Rbar_IsFiniteExpectation ps2 (fun y => Rbar_FiniteExpectation ps1 (fun x => f (x, y)))} :
  Rbar_FiniteExpectation (product_ps ps1 ps2) f =
  Rbar_FiniteExpectation ps2 (fun y => Rbar_FiniteExpectation ps1 (fun x => f (x, y))).
  Proof.
    assert (rv':RandomVariable (product_sa B A) Rbar_borel_sa (f ∘ (fun '(a, b) => (b, a)))).
    {
      apply (compose_rv (dom2:=product_sa A B)); trivial.
      apply product_flip_rv.
    }
    assert (isfe': forall x : Y, Rbar_IsFiniteExpectation ps1 (fun y : X => (f ∘ (fun '(a, b) => (b, a))) (x, y))).
    {
      intros.
      generalize (isfe2 x).
      apply Rbar_IsFiniteExpectation_proper; reflexivity.
    }
    assert (isfe'2:Rbar_IsFiniteExpectation ps2
              (fun x : Y => Rbar_FiniteExpectation ps1 (fun y : X => (f ∘ (fun '(a, b) => (b, a))) (x, y)))).
    {
      revert isfe3.
      apply Rbar_IsFiniteExpectation_proper; intros ?.
      f_equal.
      apply Rbar_FiniteExpectation_ext; reflexivity.
    }
  
    
    etransitivity; [| etransitivity]; [| apply (@fubini_section_fst _ _ _ _ ps2 ps1 (f ∘ (fun '(a, b) => (b, a))) _ _ _ _) |].
    - apply Rbar_FiniteExpectation_product_flip; trivial.
    - apply Rbar_FiniteExpectation_ext; intros ?.
      f_equal.
      now apply Rbar_FiniteExpectation_ext.
  Qed.

  Lemma pullback_law_frf {Ts1 Ts2} {dom1 : SigmaAlgebra Ts1} {dom2 : SigmaAlgebra Ts2} {prts : ProbSpace dom1}
        (rv_X : Ts1 -> Ts2)
        (rv_Y : Ts2 -> R)
        {rvx : RandomVariable dom1 dom2 rv_X}
        {rvy : RandomVariable dom2 borel_sa rv_Y} 
        {frfy : FiniteRangeFunction rv_Y} :
    SimpleExpectation (Prts := prts) (rv_Y ∘ rv_X) =
    SimpleExpectation (Prts := pullback_ps _ _ prts rv_X) rv_Y.
  Proof.
    rewrite frf_indicator_sum_simple_expectation.
    rewrite frf_indicator_sum_simple_expectation.
    simpl.
    f_equal.
    apply map_ext.
    intros.
    f_equal.
    unfold val_indicator.
    assert (sa_sigma  dom1 (fun omega : Ts1 => (rv_Y ∘ rv_X) omega = a)).
    {
      apply sa_le_pt.
      intros.
      apply rv_measurable.
      typeclasses eauto.
    }
    generalize (@SimpleExpectation_pre_EventIndicator 
                  Ts1 dom1 prts _ H 
                  (classic_dec (fun omega : Ts1 => (rv_Y ∘ rv_X) omega = a))); intros.
    assert (sa_sigma dom2 (fun omega : Ts2 => rv_Y omega = a)).
    {
      apply sa_le_pt.
      intros.
      now apply rv_measurable.
    }
    generalize (@SimpleExpectation_pre_EventIndicator Ts2 dom2); intros.
    specialize (H2 (@pullback_ps Ts1 Ts2 dom1 dom2 prts rv_X rvx) _ H1).
    specialize (H2 (classic_dec (fun omega : Ts2 => rv_Y omega = a))).
    etransitivity; [| etransitivity]; [|apply H0|].
    + apply SimpleExpectation_pf_irrel.
    + symmetry.
      etransitivity; [| etransitivity]; [|apply H2|].
      * apply SimpleExpectation_pf_irrel.
      * simpl.
        now apply ps_proper.
  Qed.

  Instance Rbar_nneg_compose {Ts1 Ts2} (f : Ts1 -> Ts2) (g : Ts2 -> Rbar) :
    Rbar_NonnegativeFunction g -> 
    Rbar_NonnegativeFunction  (g  ∘ f).
  Proof.
    intros ??.
    apply H.
  Qed.

  Lemma pullback_law_nneg {Ts1 Ts2} {dom1 : SigmaAlgebra Ts1} {dom2 : SigmaAlgebra Ts2} {prts : ProbSpace dom1}
        (rv_X : Ts1 -> Ts2)
        (rv_Y : Ts2 -> Rbar)
        {rvx : RandomVariable dom1 dom2 rv_X}
        {rvy : RandomVariable dom2 Rbar_borel_sa rv_Y} 
        {nny : Rbar_NonnegativeFunction rv_Y} :
    Rbar_NonnegExpectation (Prts := prts) (rv_Y  ∘ rv_X) =
    Rbar_NonnegExpectation (Prts := pullback_ps _ _ prts rv_X) rv_Y.
  Proof.
  generalize (simple_approx_lim_seq rv_Y nny); intro flim.
  generalize (simple_approx_frf rv_Y); intro apx_frf.
  generalize (simple_approx_pofrf rv_Y); intro apx_nnf.
  generalize (simple_approx_rv (dom := dom2) rv_Y); intros apx_rv.
  generalize (simple_approx_le rv_Y nny); intro apx_le.
  generalize (simple_approx_increasing rv_Y nny); intro apx_inc.
  
  assert (nn_lim_apx: Rbar_NonnegativeFunction (Rbar_rvlim (fun n => simple_approx rv_Y n))).
  {
    intros ?.
    apply ELim_seq_nneg.
    intros.
    apply simple_approx_pofrf.
  }
  generalize (Rbar_monotone_convergence (Prts := pullback_ps _ _ prts rv_X) 
                rv_Y (simple_approx rv_Y) rvy nny _ _ ); intros.
  rewrite <- H; try easy; [|intros; now apply is_Elim_seq_fin]; clear H.
  generalize (Rbar_monotone_convergence (rv_Y  ∘ rv_X) (fun n => ((simple_approx rv_Y n)  ∘ rv_X)) ); intros.
  assert (RandomVariable dom1 Rbar_borel_sa (rv_Y ∘ rv_X)).
  {
    now apply compose_rv.
  }
  assert (Xn_pos: forall n : nat,
             Rbar_NonnegativeFunction (fun x : Ts1 => (simple_approx rv_Y n ∘ rv_X) x)).
  {
    intros ??.
    apply (Rbar_NonnegativeFunction_compose (simple_approx rv_Y n) rv_X).
    apply apx_nnf.
  }
  rewrite <- (H H0 _ _ Xn_pos); clear H.
  - apply ELim_seq_ext.
    intros.
    rewrite <- NNExpectation_Rbar_NNExpectation.
    assert (NonnegativeFunction (fun x : Ts1 => (simple_approx rv_Y n ∘ rv_X) x)).
    {
      intros ?.
      apply (NonnegativeFunction_compose (simple_approx rv_Y n) rv_X).
      apply apx_nnf.
    }
    generalize (NNExpectation_Rbar_NNExpectation _ H); intros.
    symmetry.
    etransitivity; [| etransitivity]; [|apply H1|]; [|apply Rbar_NonnegExpectation_pf_irrel].
    erewrite frf_NonnegExpectation.
    erewrite frf_NonnegExpectation.
    now rewrite pullback_law_frf.
  - intros ??.
    apply apx_le.
  - intros ??.
    apply apx_inc.
  - intros.
    apply is_Elim_seq_fin.
    apply flim.
  Qed.

  Lemma Rbar_rv_pos_neg_id' {Ts} (rv_X:Ts->Rbar) : 
      rv_eq (rv_X) (Rbar_rvminus (Rbar_pos_fun_part rv_X) (Rbar_neg_fun_part rv_X)).
  Proof.
    intros ?.
    rewrite Rbar_rv_pos_neg_id.
    now unfold Rbar_rvminus.
  Qed.

  Lemma ex_Rbar_plus_pos_neg_part {Ts} (f : Ts -> Rbar) :
    forall x,
      ex_Rbar_plus (Rbar_pos_fun_part f x) (Rbar_rvopp (Rbar_neg_fun_part f) x).
  Proof.
    intros.
    unfold Rbar_pos_fun_part, Rbar_neg_fun_part, Rbar_rvopp.
    unfold Rbar_max.
    match_destr; match_destr; simpl; trivial.
    - apply ex_Rbar_plus_Finite_l.
    - apply ex_Rbar_plus_Finite_r.
    - rewrite Rbar_opp_involutive.
      unfold ex_Rbar_plus.
      destruct (f x); now simpl.
  Qed.

  Lemma pullback_law {Ts1 Ts2} {dom1 : SigmaAlgebra Ts1} {dom2 : SigmaAlgebra Ts2} {prts : ProbSpace dom1}
        (rv_X : Ts1 -> Ts2)
        (rv_Y : Ts2 -> Rbar)
        {rvx : RandomVariable dom1 dom2 rv_X}
        {rvy : RandomVariable dom2 Rbar_borel_sa rv_Y} :
    Rbar_Expectation (rv_Y  ∘ rv_X) =
    Rbar_Expectation (Prts := (pullback_ps _ _ prts rv_X)) rv_Y.
  Proof.
    generalize (Rbar_rv_pos_neg_id' rv_Y); intros.
    rewrite (Rbar_Expectation_ext (Prts := (pullback_ps _ _ prts rv_X)) H).
    assert (rv_eq
              (rv_Y ∘ rv_X)
              (Rbar_rvminus ((Rbar_pos_fun_part rv_Y) ∘ rv_X) ((Rbar_neg_fun_part rv_Y) ∘ rv_X))).
    {
      intros ?.
      unfold compose.
      now rewrite H.
    }
    rewrite (Rbar_Expectation_ext H0).
    unfold Rbar_Expectation.
    f_equal; erewrite <- pullback_law_nneg; try reflexivity.
    - apply Rbar_pos_fun_part_rv.
      apply Rbar_rvminus_rv.
      + now apply Rbar_pos_fun_part_rv.
      + now apply Rbar_neg_fun_part_rv.     
    - apply Rbar_neg_fun_part_rv.
      apply Rbar_rvminus_rv.
      + now apply Rbar_pos_fun_part_rv.
      + now apply Rbar_neg_fun_part_rv.     
  Qed.

  Instance pullback_law_Rbar_isfe {Ts1 Ts2} {dom1 : SigmaAlgebra Ts1} {dom2 : SigmaAlgebra Ts2} {prts : ProbSpace dom1}
        (rv_X : Ts1 -> Ts2)
        (rv_Y : Ts2 -> Rbar)
        {rvx : RandomVariable dom1 dom2 rv_X}
        {rvy : RandomVariable dom2 Rbar_borel_sa rv_Y} :
    Rbar_IsFiniteExpectation prts (rv_Y  ∘ rv_X) ->
    Rbar_IsFiniteExpectation (pullback_ps _ _ prts rv_X) rv_Y.
  Proof.
    unfold Rbar_IsFiniteExpectation.
    now rewrite (pullback_law _ _).
  Qed.

  Instance pullback_law_isfe {Ts1 Ts2} {dom1 : SigmaAlgebra Ts1} {dom2 : SigmaAlgebra Ts2} {prts : ProbSpace dom1}
        (rv_X : Ts1 -> Ts2)
        (rv_Y : Ts2 -> R)
        {rvx : RandomVariable dom1 dom2 rv_X}
        {rvy : RandomVariable dom2 borel_sa rv_Y} :
    IsFiniteExpectation prts (rv_Y  ∘ rv_X) ->
    IsFiniteExpectation (pullback_ps _ _ prts rv_X) rv_Y.
    Proof.
      unfold IsFiniteExpectation.
      repeat rewrite Expectation_Rbar_Expectation.
      rewrite <- (pullback_law _ _).
      rewrite (Rbar_Expectation_ext (rv_X2:=(@compose Ts1 Ts2 Rbar (fun x : Ts2 => Finite (rv_Y x)) rv_X))); try reflexivity; tauto.
  Qed.

  Lemma pullback_law_Rbar_fin {Ts1 Ts2} {dom1 : SigmaAlgebra Ts1} {dom2 : SigmaAlgebra Ts2} {prts : ProbSpace dom1}
        (rv_X : Ts1 -> Ts2)
        (rv_Y : Ts2 -> Rbar)
        {rvx : RandomVariable dom1 dom2 rv_X}
        {rvy : RandomVariable dom2 Rbar_borel_sa rv_Y} 
        {isfey : Rbar_IsFiniteExpectation (pullback_ps _ _ prts rv_X) rv_Y}
        {isfexy : Rbar_IsFiniteExpectation prts (rv_Y  ∘ rv_X)} :
    Rbar_FiniteExpectation prts (rv_Y  ∘ rv_X) =
    Rbar_FiniteExpectation (pullback_ps _ _ prts rv_X) rv_Y.
  Proof.
    cut (Some (Finite (Rbar_FiniteExpectation prts (rv_Y  ∘ rv_X))) =
         Some (Finite (Rbar_FiniteExpectation (pullback_ps _ _ prts rv_X) rv_Y))); intros.
    now inversion H.
    do 2 rewrite <- Rbar_FiniteExpectation_Rbar_Expectation.
    now apply pullback_law.
  Qed.

  Lemma product_pair_law {Ts Td1 Td2} {dom : SigmaAlgebra Ts} {prts : ProbSpace dom}
        {cod1 : SigmaAlgebra Td1} {cod2 : SigmaAlgebra Td2}
        (rv_X : Ts -> Td1) (rv_Y : Ts -> Td2) 
        {rv1:RandomVariable dom cod1 rv_X}
        {rv2:RandomVariable dom cod2 rv_Y} :
    independent_rvs prts cod1 cod2 rv_X rv_Y ->
    ps_equiv (product_ps (pullback_ps _ _ prts rv_X) (pullback_ps _ _ prts rv_Y))
             (pullback_ps _ _ prts (fun ω => (rv_X ω, rv_Y ω))).
  Proof.
    intros ??.
    symmetry.
    apply product_ps_unique.
    intros.
    simpl.
    specialize (H a b).
    unfold independent_events in H.
    rewrite <- H.
    apply ps_proper.
    intros ?; reflexivity.
  Qed.

  Lemma IsFiniteExpectation_mult_bounded {Ts} {dom : SigmaAlgebra Ts} {prts : ProbSpace dom}
        (f g : Ts -> R) (gmin gmax : R)
        {rvf : RandomVariable dom borel_sa f}  :
    (forall x, gmin <= g x <= gmax) ->
    IsFiniteExpectation prts f ->
    IsFiniteExpectation prts (rvmult f g).
 Proof.
   intros.
   assert (forall a,
              0 <= f a ->
              f a * gmin  <= f a * g a <= f a * gmax).
   {
     intros; split; apply Rmult_le_compat_l; trivial; apply H.
   }
   assert (forall a,
              f a <= 0 ->
              f a * gmax <= f a * g a <= f a * gmin).
   {
     intros; split; apply Rmult_le_compat_neg_l; trivial; apply H.
   }
   apply IsFiniteExpectation_bounded with
       (rv_X1 := rvmin (rvscale gmin f) (rvscale gmax f))
       (rv_X3 := rvmax (rvscale gmin f) (rvscale gmax f)).
   - apply IsFiniteExpectation_min; typeclasses eauto.
   - apply IsFiniteExpectation_max; typeclasses eauto.
   - intros ?.
     specialize (H1 a).
     specialize (H2 a).
     rv_unfold;  unfold Rmin.
     match_destr; destruct (Rle_dec 0 (f a)); lra.
   - intros ?.
     specialize (H1 a).
     specialize (H2 a).
     rv_unfold;  unfold Rmax.
     match_destr; destruct (Rle_dec 0 (f a)); lra.
  Qed.     

  Lemma freezing_rvce {Ts} {dom : SigmaAlgebra Ts} {prts : ProbSpace dom}
        (rv_f : (X * Y) -> R) 
        (rv_X : Ts -> X)
        (rv_Y : Ts -> Y)
        {rvf : RandomVariable (product_sa A B) borel_sa rv_f}
        {rvf2 : RandomVariable dom borel_sa (fun ω : Ts => rv_f (rv_X ω, rv_Y ω))}
        {rvX : RandomVariable dom A rv_X}
        {rvY : RandomVariable dom B rv_Y}
        {indep: independent_rvs prts A B rv_X rv_Y}
        {isfe:  IsFiniteExpectation prts (fun x : Ts => rv_f (rv_X x, rv_Y x)) }
        {isfe2 : forall x, IsFiniteExpectation prts (fun ω0 => rv_f (x, rv_Y ω0))} :
    RandomVariable 
      (pullback_sa A rv_X) Rbar_borel_sa
      (fun ω : Ts => (fun x : X => FiniteExpectation prts (fun ω0 : Ts => rv_f (x, rv_Y ω0))) (rv_X ω)).
  Proof.
      apply Real_Rbar_rv.
      generalize (pullback_compose_rv rv_X (dom3 := borel_sa)); intros.
      specialize (H (fun x0 => FiniteExpectation prts (fun ω0 : Ts => rv_f (x0, rv_Y ω0)))).
      apply H.

      assert (isfe4: forall x0, Rbar_IsFiniteExpectation prts (fun ω0 : Ts => rv_f (x0, rv_Y ω0))).
      {
        intros.
        now apply IsFiniteExpectation_Rbar.
      }
      assert (isfe5 : forall x : X, Rbar_IsFiniteExpectation (pullback_ps dom B prts rv_Y) (fun y : Y => (fun x0 : X * Y => Finite (rv_f x0)) (x, y))).
      {
        intros.
        apply IsFiniteExpectation_Rbar.
        apply pullback_law_isfe.
        - now apply prod_section_fst_rv.
        - now unfold compose.
      }
      assert ( RandomVariable A borel_sa (fun x0 : X => Rbar_FiniteExpectation prts (fun ω0 : Ts => rv_f (x0, rv_Y ω0)))).
      {
        generalize (fubini_section_fst_rv (A := A) (pullback_ps dom A prts rv_X)  (pullback_ps dom B prts rv_Y)); intros.
        specialize (H0 rv_f _).
        cut_to H0.
        - specialize (H0 isfe5).
          revert H0.
          apply RandomVariable_proper; try easy.
          intros ?.
          generalize (pullback_law_Rbar_fin (dom2 := B) rv_Y); intros.
          specialize (H0 (fun y : Y => rv_f (a, y)) _ _ _ ).
          now rewrite H0.
        - apply IsFiniteExpectation_Rbar.
          generalize (product_pair_law _ _ indep); intros.
          assert (IsFiniteExpectation (pullback_ps dom (product_sa A B) prts (fun ω : Ts => (rv_X ω, rv_Y ω))) rv_f).
          {
            apply pullback_law_isfe; trivial.
          }
          revert H2.
          apply IsFiniteExpectation_ext_ps'; easy.
      }
      revert H0.
      apply RandomVariable_proper; try easy.
      intros ?.
      rewrite <- FinExp_Rbar_FinExp.
      - apply Rbar_FiniteExpectation_ext; reflexivity.
      - apply (compose_rv rv_Y (fun y0 => rv_f (a, y0))).
   Qed.

Lemma freezing {Ts} {dom : SigmaAlgebra Ts} {prts : ProbSpace dom}
        (rv_f : (X * Y) -> R) 
        (rv_X : Ts -> X)
        (rv_Y : Ts -> Y)
        {rvf : RandomVariable (product_sa A B) borel_sa rv_f}
        {rvf2 : RandomVariable dom borel_sa (fun ω : Ts => rv_f (rv_X ω, rv_Y ω))}
        {rvX : RandomVariable dom A rv_X}
        {rvY : RandomVariable dom B rv_Y} 
        {indep: independent_rvs prts A B rv_X rv_Y }
        {isfe : IsFiniteExpectation prts (fun x : Ts => rv_f (rv_X x, rv_Y x))} 
        {isfe2 : forall x, IsFiniteExpectation prts (fun ω0 => rv_f (x, rv_Y ω0))} :
    is_conditional_expectation prts (pullback_sa A rv_X) 
                               (fun ω => rv_f (rv_X ω, rv_Y ω))
                               (fun ω => ((fun x => FiniteExpectation prts (fun ω0 => rv_f (x, rv_Y ω0))) (rv_X ω)))
                               (rvce := freezing_rvce rv_f rv_X rv_Y (indep := indep)).
  Proof.
    unfold is_conditional_expectation.
    intros.
    assert (RandomVariable (pullback_sa A rv_X) borel_sa (EventIndicator dec)).
    {
      now apply EventIndicator_pre_rv.
    }
    destruct (event_indicator_expressible_if_measurable rv_X (exist _ _ H)) as [E [? ?]].
    pose (g := EventIndicator (classic_dec E)).
    assert (HH3: rv_eq (EventIndicator dec) (g ∘ rv_X)).
    {
      intros ?.
      unfold g.
      unfold compose.
      rewrite <- H2.
      apply EventIndicator_ext.
      intros ?.
      now simpl.
    }
    assert (rv_eq
              (EventIndicator dec)
              (compose (compose g fst) (fun ω => (rv_X ω, rv_Y ω)))).
    {
      intros ?.
      rewrite HH3.
      tauto.
    }
    assert (rv_eq
              (rvmult (fun ω : Ts => rv_f (rv_X ω, rv_Y ω)) (EventIndicator dec))
              (compose (rvmult rv_f (compose g fst)) (fun ω => (rv_X ω, rv_Y ω)))).
    {
      intros ?.
      unfold rvmult, compose.
      now rewrite H3.
    }
    rewrite (Expectation_ext H4).
    rewrite Expectation_Rbar_Expectation.
    generalize (pullback_law (fun ω : Ts => (rv_X ω, rv_Y ω)) (dom2 := product_sa A B)); intros.
    specialize (H5 (rvmult rv_f  (g ∘ fst)) _ _).
    unfold compose in H5.
    unfold compose.
    rewrite H5.
    generalize (product_pair_law rv_X rv_Y indep); intros.
    symmetry in H6.
    generalize (Rbar_Expectation_ext_ps' _ _ H6 ); intros.
    etransitivity; [| etransitivity]; [|apply H7|]; [now eapply Rbar_Expectation_ext| apply reflexivity |].
    symmetry in H6.
    assert (isfe': IsFiniteExpectation (product_ps (pullback_ps dom A prts rv_X) (pullback_ps dom B prts rv_Y)) rv_f).
    {
      assert (IsFiniteExpectation (pullback_ps dom (product_sa A B) prts (fun ω : Ts => (rv_X ω, rv_Y ω))) rv_f).
      {
        now apply pullback_law_isfe.
      }
      revert H8.
      apply IsFiniteExpectation_ext_ps'; trivial.
      reflexivity.
    }
    
    assert (isfe3: Rbar_IsFiniteExpectation (product_ps (pullback_ps dom A prts rv_X) (pullback_ps dom B prts rv_Y))
                                            (fun omega : X * Y => rvmult rv_f (fun x : X * Y => g (fst x)) omega)).
    {
      apply IsFiniteExpectation_Rbar.
      apply IsFiniteExpectation_mult_bounded with (gmin := 0) (gmax := 1); trivial.
      intros.
      unfold g.
      unfold EventIndicator.
      match_destr; lra.
    }
    erewrite Rbar_FiniteExpectation_Rbar_Expectation.

    assert (isfe5: forall x : X, Rbar_IsFiniteExpectation (pullback_ps dom B prts rv_Y) (fun y : Y => rvmult rv_f (fun x0 : X * Y => g (fst x0)) (x, y))).
    {
      intros.
      apply IsFiniteExpectation_Rbar.
      apply IsFiniteExpectation_mult_bounded with (gmin := 0) (gmax := 1).
      - now apply prod_section_fst_rv.
      - intros.
        unfold g.
        unfold EventIndicator.
        match_destr; lra.
      - apply pullback_law_isfe.
        + now apply prod_section_fst_rv.
        + apply isfe2.
    }
    assert (isfe4: forall a,  Rbar_IsFiniteExpectation prts ((fun y : Y => Finite (rvmult rv_f (fun x : X * Y => g (fst x)) (rv_X a, y))) ∘ rv_Y)).
    {
      intros.
      specialize (isfe5 (rv_X a)).
      unfold Rbar_IsFiniteExpectation in isfe5.
      rewrite <- pullback_law in isfe5.
      apply isfe5.
      apply Real_Rbar_rv.
      apply rvmult_rv.
      - now apply prod_section_fst_rv.
      - unfold g.
        apply EventIndicator_pre_rv.
        unfold fst.
        apply sa_sigma_const_classic.
    }

    assert (RandomVariable 
              A borel_sa
              (fun x : X => Rbar_FiniteExpectation (pullback_ps dom B prts rv_Y) (fun y : Y => rvmult rv_f (fun x0 : X * Y => g (fst x0)) (x, y)))).
    {
      generalize (fubini_section_fst_rv (A := A) (pullback_ps dom A prts rv_X)  (pullback_ps dom B prts rv_Y) ); intros.
      specialize (H8 (rvmult rv_f (fun x0 : X * Y => g (fst x0)))).
      apply H8.
      - apply Real_Rbar_rv.
        apply rvmult_rv; trivial.
        unfold g.
        apply EventIndicator_pre_rv.
        apply fst_rv.
      - apply IsFiniteExpectation_Rbar.
        apply IsFiniteExpectation_mult_bounded with (gmin := 0) (gmax :=1); trivial.
        intros.
        unfold g.
        unfold EventIndicator.
        match_destr; lra.
    }
    assert (isfe6: Rbar_IsFiniteExpectation 
                     (pullback_ps dom A prts rv_X)
                     (fun x : X => Rbar_FiniteExpectation (pullback_ps dom B prts rv_Y) (fun y : Y => rvmult rv_f (fun x0 : X * Y => g (fst x0)) (x, y)))).
    {
      generalize (Rbar_isfe_fubini_section_fst 
                    (pullback_ps dom A prts rv_X) (pullback_ps dom B prts rv_Y)); intros.
      assert (Rbar_IsFiniteExpectation 
                (pullback_ps dom A prts rv_X)
                (fun x : X => Rbar_FiniteExpectation0 (pullback_ps dom B prts rv_Y) (fun y : Y => rvmult rv_f (fun x0 : X * Y => g (fst x0)) (x, y)))).
      {
        specialize (H9 (rvmult rv_f (fun x0 : X * Y => g (fst x0)))).
        apply H9; try easy.
        apply Real_Rbar_rv, rvmult_rv; trivial.
        unfold g.
        apply EventIndicator_pre_rv, fst_rv.
      }
      revert H10.
      apply Rbar_IsFiniteExpectation_proper.
      intros ?.
      now erewrite Rbar_FiniteExpectation0_finite.
    }
    erewrite fubini_section_fst.
    erewrite <- Rbar_FiniteExpectation_Rbar_Expectation.
    - erewrite <- pullback_law.
      + apply Rbar_Expectation_ext.
        intros ?.
        unfold compose.
        erewrite <- pullback_law_Rbar_fin.
        * unfold Rbar_rvmult.
          simpl.
          rewrite Rmult_comm, <- FiniteExpectation_scale.
          unfold compose.
          erewrite <- FinExp_Rbar_FinExp.
          -- apply Rbar_finite_eq, Rbar_FiniteExpectation_ext.
             intros ?.
             unfold compose, rvmult, rvscale.
             rewrite HH3.
             unfold compose, fst.
             now rewrite Rmult_comm.
          -- apply rvscale_rv.
             apply (compose_rv (dom2 := product_sa A B)); trivial.
             apply product_sa_rv; typeclasses eauto.
        * apply Real_Rbar_rv.
          apply rvmult_rv.
          -- apply (compose_rv (dom2 := product_sa A B)); trivial.
             apply product_sa_rv; typeclasses eauto.
          -- unfold fst.
             apply rvconst.
      + now apply Real_Rbar_rv.
    - apply Real_Rbar_rv, rvmult_rv; trivial.
      unfold g.
      apply EventIndicator_pre_rv, fst_rv.
  Qed.

  Lemma independent_sas_comm {Ts} {dom dom1 dom2 : SigmaAlgebra Ts} {prts : ProbSpace dom}
        (sub1 : sa_sub dom1 dom)
        (sub2 : sa_sub dom2 dom) :
    independent_sas prts sub1 sub2 <->
    independent_sas prts sub2 sub1.
  Proof.
    unfold independent_sas.
    split; intros; now apply symmetry.
  Qed.

  Lemma independent_sas_rv {Ts} {dom dom2: SigmaAlgebra Ts} {prts : ProbSpace dom}
      {sub : sa_sub dom2 dom}
      {rv_X : Ts -> X}
      {rv_Y : Ts -> Y}
        {rvX : RandomVariable dom A rv_X}
        {rvY : RandomVariable dom B rv_Y} 
        {rvX2 : RandomVariable dom2 A rv_X} :
    independent_sas prts (pullback_rv_sub dom B rv_Y rvY) sub ->  
    independent_rvs prts A B rv_X rv_Y.
  Proof.
    intros.
    apply independent_sas_comm in H.
    apply independent_rv_sas.
    revert H.
    apply independent_sas_sub_proper; try easy.
    now apply pullback_rv_sub.
  Qed.           

  Lemma freezing_rvce_sa {Ts} {dom dom2 : SigmaAlgebra Ts} {prts : ProbSpace dom}
      (sub : sa_sub dom2 dom)
        (rv_f : (X * Y) -> R) 
        (rv_X : Ts -> X)
        (rv_Y : Ts -> Y)
        {rvf : RandomVariable (product_sa A B) borel_sa rv_f}
        {rvf2 : RandomVariable dom borel_sa (fun ω : Ts => rv_f (rv_X ω, rv_Y ω))}
        {rvX : RandomVariable dom A rv_X}
        {rvX2 : RandomVariable dom2 A rv_X}
        {rvY : RandomVariable dom B rv_Y}
        {indep: independent_sas prts (pullback_rv_sub dom B rv_Y rvY) sub}
        {isfe:  IsFiniteExpectation prts (fun x : Ts => rv_f (rv_X x, rv_Y x)) }
        {isfe2 : forall x, IsFiniteExpectation prts (fun ω0 => rv_f (x, rv_Y ω0))} :
    RandomVariable dom2 Rbar_borel_sa
                   (fun ω : Ts => (fun x : X => FiniteExpectation prts (fun ω0 : Ts => rv_f (x, rv_Y ω0))) (rv_X ω)).
  Proof.
    generalize (freezing_rvce rv_f rv_X rv_Y (indep := independent_sas_rv indep)); intros.
    now apply (RandomVariable_sa_sub (pullback_rv_sub _ _ _ rvX2)).
  Qed.
    
End ps_product'.

Lemma freezing_prod_sa {Ts} {dom dom2: SigmaAlgebra Ts} {prts : ProbSpace dom}
      (sub : sa_sub dom2 dom)
      (X Z : Ts -> R) 
      {rvx1 : RandomVariable dom borel_sa X}
      {rvx2 : RandomVariable dom2 borel_sa X}      
      {rvz : RandomVariable dom borel_sa Z}  
      {isfex : IsFiniteExpectation prts X}
      {isfez : IsFiniteExpectation prts Z} :
  independent_sas prts (pullback_rv_sub dom borel_sa Z rvz) sub ->
  almostR2 (prob_space_sa_sub prts sub) eq (ConditionalExpectation prts sub (rvmult Z X))
           (rvscale (FiniteExpectation prts Z) X).
 Proof.
   intros.
   generalize (is_conditional_expectation_independent_sa prts sub Z H); intros.
   generalize (Condexp_cond_exp prts sub Z); intros.
   generalize (is_conditional_expectation_unique prts sub _ _ _ H0 H1); intros.

   assert (indepZX: independent_rvs prts borel_sa borel_sa Z X).
   {
     rewrite independent_rv_sas.
     apply independent_sas_sub_proper with (sub1 := pullback_rv_sub dom borel_sa Z rvz)
                                           (sub2 := sub); try easy.
     now apply pullback_rv_sub.
   }
   generalize (independent_expectation_prod_isfe prts Z X indepZX); intros isfexz.
   generalize (Condexp_factor_out prts sub Z X); intros.
   revert H3; apply almost_impl.
   revert H2; apply almost_impl.
   apply all_almost; intros ???.
   rewrite H3.
   unfold const in H2.
   unfold rvscale.
   unfold Rbar_rvmult.
   replace (Finite (Rmult (FiniteExpectation prts Z) (X x))) with
        (Rbar_mult (Finite (FiniteExpectation prts Z)) (X x)) by now simpl.
   rewrite H2.
   now rewrite Rbar_mult_comm.
 Qed.

 Instance freezing_rv {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (Psi : Ts2 * Ts -> R)
       {rvx : RandomVariable dom2 cod X}      
       {rvPsi : RandomVariable (product_sa cod dom3) borel_sa Psi} :
   RandomVariable dom borel_sa (fun ω : Ts => Psi (X ω, ω)).
 Proof.
   assert (RandomVariable dom (product_sa cod dom3) (fun ω : Ts => (X ω, ω))).
   {
     apply product_sa_rv; trivial.
     - now apply (RandomVariable_sa_sub sub2).
     - apply (RandomVariable_sa_sub sub3).
       typeclasses eauto.
   }
   apply (compose_rv (dom2 := product_sa cod dom3) (fun ω => (X ω, ω)) Psi).
 Qed.

 Lemma freezing_sa_rectangle {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (EPsi : pre_event (Ts2 * Ts))
       {sa_EPsi : sa_sigma (product_sa cod dom3) EPsi} 
       {rvx : RandomVariable dom2 cod X}
       {rve: RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe : IsFiniteExpectation prts (fun ω =>  EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe2: forall x, IsFiniteExpectation prts (fun ω : Ts => EventIndicator (classic_dec EPsi) (x, ω))}:
   independent_sas prts sub2 sub3 ->
   is_measurable_rectangle EPsi ->
   almostR2 (prob_space_sa_sub prts sub2) eq (ConditionalExpectation prts sub2 (fun ω => EventIndicator (classic_dec EPsi) (X ω, ω)))
            (fun ω => (fun x => FiniteExpectation prts (fun ω => EventIndicator (classic_dec EPsi) (x, ω))) (X ω)).
 Proof.
   intros.
   destruct H0 as [a [b ?]].
   assert (forall x,
              rv_eq
                (fun ω => EventIndicator (classic_dec EPsi) (X x, ω))
                (rvmult
                   (fun ω => EventIndicator (classic_dec a) (X x))
                   (EventIndicator (classic_dec b)))).
   {
     intros ??.
     unfold EventIndicator, rvmult.
     match_destr; match_destr; match_destr; try lra; try (rewrite H0 in e; now destruct e).
     rewrite H0 in n; now destruct n.
   }
   assert (rv_eq
             (fun ω => EventIndicator (classic_dec EPsi) (X ω, ω))
             (rvmult
                (fun ω => EventIndicator (classic_dec a) (X ω))
                (EventIndicator (classic_dec b)))).
   {
     intros ?.
     apply H1.
   }
   assert (rvx2 : RandomVariable dom2 borel_sa (fun ω : Ts => EventIndicator (classic_dec a) (X ω))).
   {
     apply (compose_rv X); trivial.
     apply EventIndicator_rv.       
   }
   assert (rvx1 : RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec a) (X ω))).
   {
     now apply (RandomVariable_sa_sub sub2).
   }
   assert (rvz : RandomVariable dom borel_sa (EventIndicator (classic_dec b))).
   {
     apply (RandomVariable_sa_sub sub3).
     apply EventIndicator_rv.
   }
   assert (isfex : IsFiniteExpectation prts (fun ω : Ts => EventIndicator (classic_dec a) (X ω))).
   {
     apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
     - apply IsFiniteExpectation_const.
     - apply IsFiniteExpectation_const.
     - apply EventIndicator_pos.
     - intros ?.
       unfold EventIndicator, const.
       match_destr; lra.
   }
   assert (isfez : IsFiniteExpectation prts (EventIndicator (classic_dec b))).
   {
     apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
     - apply IsFiniteExpectation_const.
     - apply IsFiniteExpectation_const.
     - apply EventIndicator_pos.
     - intros ?.
       unfold EventIndicator, const.
       match_destr; lra.
   }
   generalize (freezing_prod_sa sub2 (prts := prts)
                                (fun ω => EventIndicator (classic_dec a) (X ω))
                                (EventIndicator (classic_dec b))); intros.
   cut_to H3.
   - revert H3.
     apply almost_impl, all_almost; intros ??.
     etransitivity; [| etransitivity]; [|apply H3|].
     + apply ConditionalExpectation_ext.
       rewrite H2.
       now rewrite rvmult_comm.
     + rewrite (FiniteExpectation_ext_alt prts _ _ (H1 x)).
       unfold rvscale.
       rewrite Rmult_comm.
       rewrite <- FiniteExpectation_scale.
       unfold rvmult, rvscale.
       f_equal.
       now apply FiniteExpectation_ext.
   - rewrite independent_sas_comm in H.
     revert H.
     apply independent_sas_sub_proper; try easy.
     apply pullback_rv_sub.
     apply EventIndicator_rv.
 Qed.


 Section class_of_stuff.

   Context
     {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
         (sub2 : sa_sub dom2 dom)
         (sub3 : sa_sub dom3 dom)       
         (indep: independent_sas prts sub2 sub3)
         (X:Ts -> Ts2)
         {rvX:RandomVariable dom2 cod X}.

   Definition freezing_Vplus (ψ:Ts2 * Ts ->R) : Prop
     := NonnegativeFunction ψ /\
          (forall x, RandomVariable dom borel_sa (fun ω : Ts => ψ (x, ω))) /\
                   IsFiniteExpectation prts (fun ω : Ts => ψ (X ω, ω)) /\ 
          exists rvψ : RandomVariable dom borel_sa (fun ω : Ts => ψ (X ω, ω)),
            exists isfeψ : forall x, IsFiniteExpectation prts (fun ω : Ts => ψ (x, ω)),
                    almostR2 (prob_space_sa_sub prts sub2) eq
                    (ConditionalExpectation _ sub2 (fun ω => ψ (X ω,ω)))
                    (fun ω => ((fun x => FiniteExpectation prts (fun ω => ψ (x, ω))) (X ω))).

   Lemma freezing_Vplus_scale
     (ψ : (Ts2 * Ts -> R))
     (c : R)
     (ψ_Vplus : freezing_Vplus ψ) : 
     0 <= c ->
     freezing_Vplus (rvscale c ψ).
   Proof.
     intros.
     destruct ψ_Vplus as [? [? [? [? [? ?]]]]].
     split.
     - intros ?.
       unfold rvscale.
       now apply Rmult_le_pos.
     - assert (rvψ' : forall x : Ts2, RandomVariable dom borel_sa (fun ω : Ts => rvscale c ψ (x, ω))).
       {
         intros.
         now apply rvscale_rv.
       }
       assert (rvψ : RandomVariable dom borel_sa (fun ω => rvscale c ψ (X ω, ω))).
       {
         now apply rvscale_rv.
       }
       split; trivial.
       assert (IsFiniteExpectation prts (fun ω : Ts => rvscale c ψ (X ω, ω))).
       {
         now apply IsFiniteExpectation_scale.
       }
       split; trivial.
       exists rvψ.
       assert (isfeψ : forall x : Ts2,
                  IsFiniteExpectation prts (fun ω : Ts => rvscale c ψ (x, ω))).
       {
         intros.
         unfold rvscale.
         now apply IsFiniteExpectation_scale.
       }
       exists isfeψ.
       generalize (Condexp_scale prts sub2 c (fun ω : Ts => ψ (X ω, ω))); apply almost_impl.
       revert H3; apply almost_impl.
       apply all_almost; intros ???.
       apply (f_equal (Rbar_mult c)) in H3.
       etransitivity; [etransitivity |]; [| apply H3 |].
       + etransitivity; [etransitivity |]; [| apply H5 |];[|reflexivity].
         apply ConditionalExpectation_ext.
         intros ?; now unfold rvscale.
       + simpl.
         apply f_equal.
         rewrite <- FiniteExpectation_scale.
         apply FiniteExpectation_ext.
         intros ?; now unfold rvscale.
   Qed.

   Lemma freezing_Vplus_sum
     (ψ1 ψ2 : (Ts2 * Ts -> R))
     (ψ1_Vplus : freezing_Vplus ψ1) 
     (ψ2_Vplus : freezing_Vplus ψ2) :      
     freezing_Vplus (rvplus ψ1 ψ2).
   Proof.
     destruct ψ1_Vplus as [? [? [? [? [? ?]]]]].
     destruct ψ2_Vplus as [? [? [? [? [? ?]]]]].     
     split.
     - now apply rvplus_nnf.
     - assert (rvψ' : forall x : Ts2, RandomVariable dom borel_sa (fun ω : Ts => rvplus ψ1 ψ2 (x, ω))).
       {
         intros.
         now apply rvplus_rv.
       }
       assert (rvψ : RandomVariable dom borel_sa (fun ω : Ts => rvplus ψ1 ψ2 (X ω, ω))).
       {
         now apply rvplus_rv.
       }
       split; trivial.
       assert (isfe2: IsFiniteExpectation prts (fun ω : Ts => rvplus ψ1 ψ2 (X ω, ω))).
       {
         now apply IsFiniteExpectation_plus.
       }
       split; trivial.
       exists rvψ.
       assert (isfeψ : forall x : Ts2, IsFiniteExpectation prts (fun ω : Ts => rvplus ψ1 ψ2 (x, ω))).
       {
         intros.
         now apply IsFiniteExpectation_plus.
       }
       exists isfeψ.
       generalize (Condexp_plus prts sub2 (fun ω : Ts => ψ1 (X ω, ω)) (fun ω : Ts => ψ2 (X ω, ω))).
       apply almost_impl.
       revert H2; apply almost_impl.
       revert H6; apply almost_impl.
       apply all_almost; intros ????.
       unfold Rbar_rvplus in H7.
       rewrite H2 in H7.
       rewrite H6 in H7.
       etransitivity; [etransitivity |]; [| apply H7 |].
       + apply ConditionalExpectation_ext.
         reflexivity.
       + simpl.
         f_equal.
         generalize (FiniteExpectation_plus prts (fun ω : Ts => ψ1 (X x3, ω)) (fun ω : Ts => ψ2 (X x3, ω))); intros.
         symmetry in H8.
         etransitivity; [etransitivity |]; [| apply H8 |]; trivial.
         apply FiniteExpectation_ext.
         reflexivity.
   Qed.

   Lemma freezing_Vplus_const (c : R) :
     0 <= c ->
     freezing_Vplus (const c).
   Proof.
     intros.
     constructor.
     - now intros ?.
     - split.
       + intros.
         apply rvconst.
       + split.
         * apply IsFiniteExpectation_const.
         * assert (rvψ : RandomVariable dom borel_sa (const c))
             by apply rvconst.
           exists rvψ.
           assert (isfeψ : forall (x : Ts2), IsFiniteExpectation prts (const c)) 
             by (intros; apply IsFiniteExpectation_const).
           exists isfeψ.
           apply all_almost; intros ?.
           generalize (Condexp_const prts sub2 c); intros.
           generalize (FiniteExpectation_const prts c); intros.
           specialize (H0 x).
           unfold const in *.
           etransitivity; [etransitivity |]; [| apply H0 |].
           -- apply ConditionalExpectation_ext.
              reflexivity.
           -- f_equal.
              symmetry.
              etransitivity; [etransitivity |]; [| apply H1 |]; trivial.
              apply FiniteExpectation_ext.
              reflexivity.
    Qed.              

   Lemma freezing_Vplus_list_sum
     (lψ : (list (Ts2 * Ts -> R))):
     (forall (f : (Ts2 * Ts) -> R),
         In f lψ -> freezing_Vplus f) ->
     freezing_Vplus (fun ω => list_sum (map (fun f => f ω) lψ)).
   Proof.
     intros.
     induction lψ.
     - simpl.
       apply freezing_Vplus_const.
       lra.
     - simpl.
       apply freezing_Vplus_sum.
       + apply H.
         simpl; tauto.
       + apply IHlψ.
         intros.
         apply H.
         simpl; tauto.
   Qed.

  (* should replace rvlim_incr *)
   Lemma rvlim_incr_alt (f : nat -> Ts -> R)  :
        (forall (n:nat), NonnegativeFunction  (f n)) ->
        (forall (n:nat), rv_le (f n) (f (S n))) ->
        (forall (omega:Ts), ex_finite_lim_seq (fun n => f n omega)) ->
        (forall (n:nat), rv_le (f n) (rvlim f)).
      Proof.
        unfold rv_le, pointwise_relation, rvlim; intros.
        generalize (Lim_seq_le_loc (fun _ => f n a) (fun n0 => f n0 a)); intros.
        cut_to H2.
        rewrite Lim_seq_const in H2.
        generalize (isfin_Lim_seq _ H1); intros.
        now rewrite <- (H3 a) in H2.
        exists n; intros.
        now apply (incr_le_strong (fun n => f n a)).
      Qed.

   Lemma freezing_Vplus_has_increasing_limits
     (ψn : nat -> (Ts2 * Ts -> R))
     (ψn_Vplus : forall n, freezing_Vplus (ψn n)) : 
     (forall n, rv_le (ψn n) (ψn (S n))) ->
     (forall ω, ex_finite_lim_seq (fun n => ψn n ω)) ->
     IsFiniteExpectation prts (rvlim (fun n ω => ψn n (X ω, ω))) ->
     (forall x, IsFiniteExpectation prts (rvlim (fun n ω => ψn n (x, ω)))) ->     
     freezing_Vplus (rvlim ψn).
   Proof.
     intros incr fin isfe isfe2.
     split.
     - apply nnflim.
       intros.
       apply ψn_Vplus.
     - assert (rvψ' : forall x : Ts2, RandomVariable dom borel_sa (rvlim (fun n ω => ψn n (x, ω)))).
       {
         intros.
         apply rvlim_rv; trivial.
         intros.
         apply ψn_Vplus.
       }
       assert (rvψ : RandomVariable dom borel_sa (rvlim (fun n ω => ψn n (X ω, ω)))).
       {
         apply rvlim_rv; trivial.
         intros.
         apply ψn_Vplus.
       }
       split; trivial.
       split; trivial.
       exists rvψ.
       exists isfe2.
       assert (forall n : nat, RandomVariable dom borel_sa ((fun (n0 : nat) (ω : Ts) => ψn n0 (X ω, ω)) n)).
       {
         intros.
         apply (ψn_Vplus n).
       }
       assert (forall n ω, IsFiniteExpectation prts (fun ω0 : Ts => ψn n (X ω, ω0))).
       {
         intros.
         destruct (ψn_Vplus n) as [? [? [? [? [? ?]]]]].
         apply x0.
       }
       assert (forall n, almostR2 (prob_space_sa_sub prts sub2) eq
                           (ConditionalExpectation prts sub2 (fun ω : Ts => ψn n (X ω, ω)))
                           (fun ω : Ts => FiniteExpectation prts (fun ω0 : Ts => ψn n (X ω, ω0)))).
       {
         intros.
         destruct (ψn_Vplus n) as [? [? [? [? [? ?]]]]].
         revert H4; apply almost_impl.
         apply all_almost; intros ??.
         etransitivity; [etransitivity |]; [| apply H4 |].
         - apply ConditionalExpectation_ext; reflexivity.
         - f_equal; apply FiniteExpectation_ext; reflexivity.
       }
       assert (almost (prob_space_sa_sub prts sub2)
                      (fun ω =>
                         forall n, 
                           ((ConditionalExpectation prts sub2 (fun ω0 : Ts => ψn n (X ω0, ω0))) ω) = 
                             (FiniteExpectation prts (fun ω0 : Ts => ψn n (X ω, ω0))))).
       {
         apply almost_forall.
         intros.
         specialize (H1 n).
         revert H1; apply almost_impl.
         apply all_almost; intros ??.
         etransitivity; [etransitivity |]; [| apply H1 |]; reflexivity.
       }
       generalize (Condexp_monotone_convergence prts sub2 
                     (fun ω : Ts => rvlim ψn (X ω, ω))
                     (fun n ω => ψn n (X ω, ω)) 
                  ); intros.
       cut_to H3.
       + revert H3; apply almost_impl.
         revert H2; apply almost_impl.
         apply all_almost; intros ???.
         assert (forall n : nat, RandomVariable dom borel_sa (fun ω : Ts => ψn n (X x, ω))).
         {
           intros.
           apply (ψn_Vplus n).
         }
         assert (forall n : nat, NonnegativeFunction (fun ω : Ts => ψn n (X x, ω))).
         {
           intros.
           destruct (ψn_Vplus n) as [? [? [? [? [? ?]]]]].           
           intros ?.
           apply H5.
         }
         assert (RandomVariable dom borel_sa (rvlim (fun (n : nat) (ω : Ts) => ψn n (X x, ω)))).
         {
           now apply rvlim_rv.
         }
         assert (NonnegativeFunction (rvlim (fun (n : nat) (ω : Ts) => ψn n (X x, ω)))).
         {
           now apply nnflim.
         }
         generalize (monotone_convergence
                       (rvlim (fun n ω => ψn n (X x, ω)))
                       (fun n ω => ψn n (X x, ω))
                       H6 H7 H4 H5
                    ); intros.
         cut_to H8; try easy.
         * apply is_Elim_seq_unique in H3.
           rewrite <- H3.
           rewrite FiniteNonnegExpectation_alt with (posX := H7).
           rewrite <- H8.
           rewrite <- Elim_seq_fin.
           apply ELim_seq_ext.
           intros.
           rewrite H2.
           rewrite FiniteNonnegExpectation_alt with (posX := (H5 n)).
           now rewrite IsFiniteNonnegExpectation.
         * intros.
           apply (rvlim_incr_alt (fun n ω =>  ψn n (X x, ω))); try easy.
           intros ??.
           apply incr.
         * intros ??.
           apply incr.
         * intros.
           now apply IsFiniteNonnegExpectation.
         * intros.
           specialize (fin  (X x, omega)).
           apply ex_finite_lim_seq_correct in fin.
           destruct fin.
           unfold rvlim.
           rewrite H10.
           now apply Lim_seq_correct.
       + apply all_almost; intros ?.
         apply nnflim.
         intros.
         apply (ψn_Vplus n).
       + intros; apply all_almost; intros ?.
         apply (ψn_Vplus n).
       + intros; apply all_almost; intros.
         unfold rvlim.
         generalize (Lim_seq_increasing_le (fun n0 : nat => ψn n0 (X x, x))); intros.
         cut_to H4.
         * specialize (H4 n).
           specialize (fin (X x, x)).
           apply ex_finite_lim_seq_correct in fin.         
           destruct fin.
           rewrite <- H6 in H4.
           now simpl in H4.
         * intros.
           apply incr.
       + intros; apply all_almost; intros.         
         apply incr.
       + apply isfe.
       + intros.
         apply (ψn_Vplus n).
       + apply all_almost; intros ?.
         apply is_Elim_seq_fin.
         unfold rvlim.
         specialize (fin (X x, x)).
         apply ex_finite_lim_seq_correct in fin.
         destruct fin.
         rewrite H5.
         now apply Lim_seq_correct.
   Qed.
   
   Lemma EventIndicator_all {Ts'} : rv_eq (EventIndicator (Ts:=Ts') (classic_dec pre_Ω)) (const 1).
   Proof.
     intros ?.
     unfold EventIndicator.
     match_destr.
     now elim n.
   Qed.

   Instance freezing_Vplus_proper : Proper (rv_eq ==> iff) freezing_Vplus.
   Proof.
     cut (Proper (rv_eq ==> Basics.impl) (freezing_Vplus)).
     {
       intros ????.
       split; apply H; trivial.
       now symmetry.
     } 
     intros ???[?[?[?[??]]]].
     split.
     - revert H0.
       apply NonnegativeFunction_proper.
       now symmetry.
     - split.
       {
         intros.
         eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)); try apply H1.
         intros ?.
         symmetry; apply H.

       } 
       split.
       + eapply IsFiniteExpectation_proper.
         * intros ?.
           symmetry in H.
           apply H.
         * apply H2.
       + assert (rvψ : RandomVariable dom borel_sa
                      (fun ω : Ts => y (X ω, ω))).
         {
           eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _)); try apply x0.
           intros ?.
           symmetry; apply H.
         } 
         exists rvψ.
         destruct H3.
         assert (isfeψ : forall x2 : Ts2,
                    IsFiniteExpectation prts (fun ω : Ts => y (x2, ω))).
         {
           intros.
           eapply IsFiniteExpectation_proper; try apply x1.
           intros ?.
           symmetry; apply H.
         }
         exists isfeψ.
         etransitivity; [etransitivity |]; [| apply H3 |].
         * apply Condexp_proper.
           apply all_almost; intros ?.
           now rewrite <- H.
         * apply all_almost; intros ?.
           f_equal.
           apply FiniteExpectation_ext; intros ?.
           apply H.
    Qed.

   Lemma freezing_Vplus_all : freezing_Vplus (EventIndicator (classic_dec pre_Ω)).
   Proof.
     rewrite EventIndicator_all.
     split.
     - intros ?; unfold const; lra.
     - assert (rvψ : RandomVariable dom borel_sa
                        (fun ω : Ts => const 1 (X ω, ω))).
       {
         apply rvconst.
       }
       split.
       {
         intros.
         apply rvconst.
       }
       split.
       {
         apply IsFiniteExpectation_const.
       }
       exists rvψ.
       assert (isfeψ : forall x : Ts2,
                  IsFiniteExpectation prts (fun ω : Ts => const 1 (x, ω))).
       {
         intros.
         apply IsFiniteExpectation_const.
       }
       exists isfeψ.
       unfold const.
       transitivity (ConditionalExpectation prts sub2 (const 1)).
       + apply Condexp_proper.
         reflexivity.
       + rewrite Condexp_const.
         apply all_almost; intros ?.
         rewrite (FiniteExpectation_ext _ _ (const 1)).
         * now rewrite FiniteExpectation_const.
         * reflexivity.
   Qed.

   Definition freezing_M (e:pre_event (Ts2 * Ts))
     : Prop
     := sa_sigma (product_sa cod dom3) e /\
          freezing_Vplus (EventIndicator (classic_dec e)).

   Instance freezing_M_proper : Proper (pre_event_equiv ==> iff) (freezing_M).
   Proof.
     cut (Proper (pre_event_equiv ==> Basics.impl) (freezing_M)).
     {
       intros ????.
       split; apply H; trivial.
       now symmetry.
     } 

     intros ???[??].
     split.
     - revert H0.
       now apply sa_proper.
     - revert H1.
       apply freezing_Vplus_proper.
       intros ?.
       unfold EventIndicator.
       repeat match_destr.
       + now apply H in y0.
       + now apply H in x0.
   Qed.

   Lemma freezing_M_all : freezing_M pre_Ω.
   Proof.
     split.
     - apply sa_all.
     - apply freezing_Vplus_all.
   Qed.

   Lemma EventIndicator_pre_event_diff_eq {Ts'} (a b:pre_event Ts') :
     rv_eq (EventIndicator (classic_dec (pre_event_diff a b)))
       (pos_fun_part (rvminus (EventIndicator (classic_dec a))
                        (EventIndicator (classic_dec b)))).
   Proof.
     intros ?.
     unfold pre_event_diff, EventIndicator, pos_fun_part, rvminus, rvplus, rvopp, rvscale; simpl.
     unfold Rmax.
     repeat match_destr; try lra; firstorder.
     - repeat match_destr_in H1; try lra; firstorder.
     - repeat match_destr_in H1; try lra; firstorder.
   Qed.

   Lemma EventIndicator_pre_event_diff_sub_eq {Ts'} (a b:pre_event Ts') :
     pre_event_sub b a ->
     rv_eq (EventIndicator (classic_dec (pre_event_diff a b)))
       (rvminus (EventIndicator (classic_dec a))
          (EventIndicator (classic_dec b))).
   Proof.
     intros ??.
     unfold pre_event_diff, EventIndicator, pos_fun_part, rvminus, rvplus, rvopp, rvscale; simpl.
     repeat match_destr; try lra; try firstorder.
   Qed.

   Instance indicator_isfe {P} (dec:forall x, {P x} + {~ P x}) :
     IsFiniteExpectation prts (EventIndicator dec).
   Proof.
     eapply (IsFiniteExpectation_bounded _ (const 0) _ (const 1))
       ; intros ?; unfold const, EventIndicator; match_destr; lra.
   Qed.

   Lemma freezing_M_relative_complement (a b : pre_event (Ts2 * Ts)) :
     freezing_M a -> freezing_M b -> pre_event_sub a b -> freezing_M (pre_event_diff b a).
   Proof.
     intros [??] [??] subab.
     assert (rvb1:RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec b) (X ω, ω))).
     { 
       apply EventIndicator_pre_rv.
       destruct H2 as [? [?[?[? ?]]]].
       generalize (x (exist _ _ (borel_singleton 1))).
       apply sa_proper ; intros ?; simpl.
       unfold EventIndicator, pre_event_singleton.
       match_destr.
       - split; tauto.
       - split; try lra.
         tauto.
     }
     assert (rva1:RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec a) (X ω, ω))).
     { 
       apply EventIndicator_pre_rv.
       destruct H0 as [? [?[?[??]]]].
       generalize (x (exist _ _ (borel_singleton 1))).
       apply sa_proper ; intros ?; simpl.
       unfold EventIndicator, pre_event_singleton.
       match_destr.
       - split; tauto.
       - split; try lra.
         tauto.
     }

     assert (rv': (RandomVariable dom borel_sa
                     (fun ω : Ts =>
                        rvminus (EventIndicator (classic_dec b))
                          (EventIndicator (classic_dec a)) (X ω, ω)))).
     { 
       apply rvminus_rv; trivial.
     }

     assert (rvb1':forall x, RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec b) (x, ω))).
     {
       intros.
       apply EventIndicator_pre_rv.
       destruct H2 as [? [?[?[?[??]]]]].
       generalize (H3 x (exist _ _ (borel_singleton 1))).
       apply sa_proper ; intros ?; simpl.
       unfold EventIndicator, pre_event_singleton.
       match_destr.
       - split; tauto.
       - split; try lra.
         tauto.
     }
     assert (rva1':forall x, RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec a) (x, ω))).
     {
       intros.
       apply EventIndicator_pre_rv.
       destruct H0 as [? [?[?[?[??]]]]].
       generalize (H3 x (exist _ _ (borel_singleton 1))).
       apply sa_proper ; intros ?; simpl.
       unfold EventIndicator, pre_event_singleton.
       match_destr.
       - split; tauto.
       - split; try lra.
         tauto.
     }

     assert (rv'': forall x, (RandomVariable dom borel_sa
                     (fun ω : Ts =>
                        rvminus (EventIndicator (classic_dec b))
                          (EventIndicator (classic_dec a)) (x, ω)))).
     {
       intros.
       apply rvminus_rv; trivial.
     }
     
     assert (isfeψ: forall x, IsFiniteExpectation prts
                           (fun ω : Ts => EventIndicator (classic_dec (pre_event_diff b a)) (x, ω))).
     {
       intros.
       apply indicator_isfe.
     }
     split.
     - now apply sa_diff.
     - split.
       + typeclasses eauto.
       + assert (rvψ : RandomVariable dom borel_sa
                         (fun ω : Ts => EventIndicator (classic_dec (pre_event_diff b a)) (X ω, ω))).
         {
           eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _))
           ; try apply EventIndicator_pre_event_diff_sub_eq.
           - intros ?.
             apply subab.
           - apply rv'.
         }
         split.
         {
           intros.
           eapply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _))
           ; try apply EventIndicator_pre_event_diff_sub_eq.
           - intros ?.
             apply subab.
           - apply rv''.
         }
         split.
         {
           apply indicator_isfe.
         }
         exists rvψ.
         exists isfeψ.

         transitivity (ConditionalExpectation prts sub2
                         (rvminus  (fun ω => (EventIndicator (classic_dec b) (X ω, ω)))
                                         (fun ω => (EventIndicator (classic_dec a) (X ω, ω))))).
         {
           apply all_almost; intros ?.
           apply ConditionalExpectation_ext; intros ?.
           now rewrite EventIndicator_pre_event_diff_sub_eq.
         }

         assert (isfeb' : forall ω, IsFiniteExpectation prts (fun ω0 => EventIndicator (classic_dec b) (X ω, ω0))) by (intros; apply indicator_isfe).
         assert (isfea' : forall ω, IsFiniteExpectation prts (fun ω0 => EventIndicator (classic_dec a) (X ω, ω0))) by (intros; apply indicator_isfe).


         transitivity ((fun ω : Ts =>
                          FiniteExpectation prts (isfe:=IsFiniteExpectation_minus _ _ _)
                            (rvminus (fun ω0 : Ts => EventIndicator (classic_dec b)  (X ω, ω0))
                               (fun ω0 : Ts => EventIndicator (classic_dec a)  (X ω, ω0)))))
         ; cycle 1.
         {
           apply all_almost; intros ?.
           f_equal.
           apply FiniteExpectation_ext; intros ?.
           now rewrite EventIndicator_pre_event_diff_sub_eq.
         }

         destruct H0 as [?[?[?[? [? eqq1]]]]].
         destruct H2 as [?[?[?[? [? eqq2]]]]].

         revert eqq1; apply almost_impl.
         revert eqq2; apply almost_impl.
         generalize (Condexp_minus prts sub2
                       (fun ω => (EventIndicator (classic_dec b) (X ω, ω)))
                       (fun ω => (EventIndicator (classic_dec a) (X ω, ω))))
         ; apply almost_impl.
         apply all_almost; intros ????.
         etransitivity; [etransitivity |]; [| apply H7 |].
         * now apply ConditionalExpectation_ext; intros ?.
         * rewrite FiniteExpectation_minus.
           unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
           rewrite_condexp H8.
           rewrite_condexp H9.
           simpl.
           f_equal.
           unfold Rminus.
           f_equal.
           -- now apply FiniteExpectation_ext.
           -- f_equal.
              now apply FiniteExpectation_ext.
   Qed.

   Lemma Lim_seq_ascending_EventIndicator_union {Ts'} (collection: nat -> pre_event Ts') :
      (forall n : nat, pre_event_sub (collection n) (collection (S n))) ->
     rv_eq (fun x => Finite (EventIndicator (classic_dec (pre_union_of_collection collection)) x))
       (fun ω : Ts' => Lim_seq (fun n : nat => EventIndicator (classic_dec (collection n)) ω)).
   Proof.
     intros ??.
     unfold EventIndicator.
     match_destr.
     - destruct p.
       rewrite <- (Lim_seq_incr_n _ (S x)).
       rewrite <- (Lim_seq_const 1).
       apply Lim_seq_ext; intros ?.
       match_destr.
       elim n0.
       eapply pre_collection_increasing_trans; try apply H0; trivial.
       lia.
     - rewrite <- (Lim_seq_const 0).
       apply Lim_seq_ext; intros ?.
       match_destr.
       elim n.
       now exists n0.
   Qed.

   Lemma freezing_M_ascending_limit (collection : nat -> pre_event (Ts2 * Ts)) :
      (forall n : nat, freezing_M (collection n)) ->
      (forall n : nat, pre_event_sub (collection n) (collection (S n))) ->
      freezing_M (pre_union_of_collection collection).
    Proof.
      intros ??.
      split.
      - apply sa_countable_union; intros.
        apply (H n).
      - generalize (freezing_Vplus_has_increasing_limits
                      (fun n => EventIndicator (classic_dec (collection n)))); intros HH.
        assert (incr: forall n : nat, rv_le (EventIndicator (classic_dec (collection n))) (EventIndicator (classic_dec (collection (S n))))).
        {
          intros ??.
          unfold EventIndicator.
          repeat match_destr; try lra.
          elim n0.
          now apply H0.
        }
        assert (fin: forall ω : Ts2 * Ts, ex_finite_lim_seq (fun n : nat => EventIndicator (classic_dec (collection n)) ω)).
        {
          intros.
          apply ex_finite_lim_seq_incr with (M := 1).
          - intros.
            apply incr.
          - intros.
            unfold EventIndicator.
            match_destr; lra.
        }
        cut_to HH; trivial.
        + revert HH.
          apply freezing_Vplus_proper.
          intros ?.
          unfold rvlim.
          now rewrite <- Lim_seq_ascending_EventIndicator_union.
        + intro.
          apply (H n).
        + apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
          * apply IsFiniteExpectation_const.
          * apply IsFiniteExpectation_const.
          * intros ?.
            apply nnflim.
            intros.
            apply EventIndicator_pos.
          * unfold rvlim, const.
            intros ?.
            generalize (Lim_seq_le_loc  (fun n : nat => EventIndicator (classic_dec (collection n)) (X a, a)) (const 1)); intros.
            cut_to H1.
            -- unfold const in H1.
               rewrite Lim_seq_const in H1.
               case_eq ( Lim_seq (fun n : nat => EventIndicator (classic_dec (collection n)) (X a, a)));intros.
               ++ rewrite H2 in H1.
                  simpl.
                  now simpl in H1.
               ++ simpl; lra.
               ++ simpl; lra.
            -- exists (0%nat).
               intros.
               unfold EventIndicator, const.
               match_destr; lra.
        + intros.
          apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
          * apply IsFiniteExpectation_const.
          * apply IsFiniteExpectation_const.
          * intros ?.
            apply nnflim.
            intros.
            apply EventIndicator_pos.
          * unfold rvlim, const.
            intros ?.
            generalize (Lim_seq_le_loc  (fun n : nat => EventIndicator (classic_dec (collection n)) (x, a)) (const 1)); intros.
            cut_to H1.
            -- unfold const in H1.
               rewrite Lim_seq_const in H1.
               case_eq ( Lim_seq (fun n : nat => EventIndicator (classic_dec (collection n)) (x, a)));intros.
               ++ rewrite H2 in H1.
                  simpl.
                  now simpl in H1.
               ++ simpl; lra.
               ++ simpl; lra.
            -- exists (0%nat).
               intros.
               unfold EventIndicator, const.
               match_destr; lra.
    Qed.
   
   Instance freezing_M_monotone_class : monotone_class freezing_M.
   Proof.
     constructor.
     - apply freezing_M_all.
     - apply freezing_M_proper.
     - apply freezing_M_relative_complement.
     - apply freezing_M_ascending_limit.
   Qed.


 End class_of_stuff.

 Lemma freezing_M_rectangle {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (EPsi : pre_event (Ts2 * Ts))
       {sa_EPsi : sa_sigma (product_sa cod dom3) EPsi} 
       {rvx : RandomVariable dom2 cod X}
       {rve: RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe : IsFiniteExpectation prts (fun ω =>  EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe2: forall x, IsFiniteExpectation prts (fun ω : Ts => EventIndicator (classic_dec EPsi) (x, ω))}:
   independent_sas prts sub2 sub3 ->
   is_measurable_rectangle EPsi ->
   freezing_M sub2 X EPsi.
  Proof.
    intros.
    constructor; trivial.
    constructor.
    - apply EventIndicator_pos.
    - split.
      {
        intros.
        apply EventIndicator_pre_rv.
        apply sub3.
        generalize (product_section_fst (exist _ EPsi sa_EPsi) x); intros.
        revert H1.
        apply sa_proper.
        intros ?.
        reflexivity.
      }
      split.
      {
        apply indicator_isfe.
      }
      exists rve.
      exists isfe2.
      now apply freezing_sa_rectangle with (sub3 := sub3).
  Qed.

 Lemma freezing_M_product_sa {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (EPsi : pre_event (Ts2 * Ts))
       {sa_EPsi : sa_sigma (product_sa cod dom3) EPsi} 
       {rvx : RandomVariable dom2 cod X}
       {rve: RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe : IsFiniteExpectation prts (fun ω =>  EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe2: forall x, IsFiniteExpectation prts (fun ω : Ts => EventIndicator (classic_dec EPsi) (x, ω))}   :
   independent_sas prts sub2 sub3 ->
   freezing_M sub2 X EPsi.
 Proof.
   intros.
   generalize (monotone_class_theorem 
                 (pre_event_set_product (sa_sigma cod) (sa_sigma dom3))
              ); intros.
   specialize (H0 (freezing_M sub2 X)).
   cut_to H0.
   - apply H0.
     apply sa_EPsi.
   - apply pre_event_set_product_pi.
   - apply freezing_M_monotone_class.
   - intros ??.
     apply freezing_M_rectangle with (sub3 := sub3); try easy.
     + simpl.
       intros.
       now apply H2.
     + destruct H1 as [? [? [? [? ?]]]].
       apply EventIndicator_pre_rv.
       assert (sa_sigma dom (fun ω => (x0 (X ω)) /\ (x1 ω))).
       {
         apply sa_inter.
         - generalize (pullback_sa_pullback cod X x0 H1); intros.
           assert (sa_sub (pullback_sa cod X) dom).
           {
             apply pullback_rv_sub.
             now apply (RandomVariable_sa_sub sub2).
           }
           apply H5.
           apply H4.
         - now apply sub3.
       }
       revert H4.
       apply sa_proper.
       intros ?.
       specialize (H3 (X x2, x2)).
       now rewrite H3.
     + apply indicator_isfe.
     + intros.
       apply indicator_isfe.
     + unfold is_measurable_rectangle.
       destruct H1 as [? [? [? [? ?]]]].
       exists (exist _ x0 H1).
       exists (exist _ x1 H2).
       intros.
       split; intros.
       * now apply H3 in H4.
       * now apply H3.
   Qed.

 Lemma freezing_Vplus_indicator {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (EPsi : pre_event (Ts2 * Ts))
       {sa_EPsi : sa_sigma (product_sa cod dom3) EPsi} 
       {rvx : RandomVariable dom2 cod X}
       {rve: RandomVariable dom borel_sa (fun ω : Ts => EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe : IsFiniteExpectation prts (fun ω =>  EventIndicator (classic_dec EPsi) (X ω, ω))}
       {isfe2: forall x, IsFiniteExpectation prts (fun ω : Ts => EventIndicator (classic_dec EPsi) (x, ω))}   :
   independent_sas prts sub2 sub3 ->
   freezing_Vplus sub2 X (EventIndicator (classic_dec EPsi)).
  Proof.
    intros.
    now destruct (freezing_M_product_sa sub2 sub3 X EPsi (sa_EPsi := sa_EPsi) H); intros.
  Qed.

 Lemma freezing_Vplus_frf {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (Psi : Ts2 * Ts -> R)
       {frf : FiniteRangeFunction Psi}
       {nnf : NonnegativeFunction Psi}       
       {rvx : RandomVariable dom2 cod X}      
       {rvPsi : RandomVariable (product_sa cod dom3) borel_sa Psi}
       {rvPsi2: RandomVariable dom borel_sa (fun ω : Ts => Psi (X ω, ω))}
       {isfe : IsFiniteExpectation prts (fun ω => Psi (X ω, ω))}
       {isfe2: forall x, IsFiniteExpectation prts (fun ω : Ts => Psi (x, ω))}   :
   independent_sas prts sub2 sub3 ->
   freezing_Vplus sub2 X Psi.
  Proof.
    intros.
    generalize (Nonnegative_FiniteRangeFunction_nneg frf nnf); intros HH.
    generalize (frf_preimage_indicator Psi (frf:=(Nonnegative_FiniteRangeFunction Psi frf nnf)))
    ; intros.
    apply (freezing_Vplus_proper _ _ _ _ H0).
    generalize (freezing_Vplus_list_sum 
                  sub2 X
                  (map (fun c a => c * point_preimage_indicator Psi c a)
                     (nodup Req_EM_T (@frf_vals (prod Ts2 Ts) R Psi
                                        (Nonnegative_FiniteRangeFunction Psi frf nnf)) ))); intros.
    cut_to H1.
    - revert H1.
      simpl.
      apply freezing_Vplus_proper.
      intros ?.
      now rewrite map_map.
    - intros.
      apply in_map_iff in H2.
      destruct H2 as [? [??]].
      rewrite <- H2.
      apply freezing_Vplus_scale.
      + unfold point_preimage_indicator.
        generalize (freezing_Vplus_indicator sub2 sub3 X); intros.
        specialize (H4 (fun x0 : Ts2 * Ts => (Psi x0) = x)).
        cut_to H4; trivial.
        * revert H4.
          apply freezing_Vplus_proper.
          intros ?.
          unfold EventIndicator.
          match_destr; match_destr; tauto.
        * apply sa_le_pt.
          intros.
          now apply rv_measurable.
        * apply EventIndicator_pre_rv.
          apply sa_le_pt.
          intros.
          now apply rv_measurable.
        * apply indicator_isfe.
        * intros.
          apply indicator_isfe.
      + rewrite Forall_forall in HH.
        apply HH.
        now apply nodup_In in H3.
  Qed.

 Lemma freezing_Vplus_nnf {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (Psi : Ts2 * Ts -> R)
       {nnf : NonnegativeFunction Psi}       
       {rvx : RandomVariable dom2 cod X}      
       {rvPsi : RandomVariable (product_sa cod dom3) borel_sa Psi}
       {rvPsi2: RandomVariable dom borel_sa (fun ω : Ts => Psi (X ω, ω))}
       {isfe : IsFiniteExpectation prts (fun ω => Psi (X ω, ω))}
       {isfe2: forall x, IsFiniteExpectation prts (fun ω : Ts => Psi (x, ω))}   :
   independent_sas prts sub2 sub3 ->
   freezing_Vplus sub2 X Psi.
  Proof.
    intros.
    generalize (simple_approx_lim_seq Psi nnf); intro flim.
    generalize (simple_approx_frf Psi); intro apx_frf.
    generalize (simple_approx_pofrf Psi); intro apx_nnf.
    generalize (simple_approx_rv (dom := (product_sa cod dom3)) Psi); intros apx_rv.
    generalize (simple_approx_le Psi nnf); intro apx_le.
    generalize (simple_approx_increasing Psi nnf); intro apx_inc.
    generalize (freezing_Vplus_has_increasing_limits 
                  sub2 X
                  (fun n ω => simple_approx (fun x : Ts2 * Ts => Psi x) n ω)
               ); intros.
    cut_to H0.
    - revert H0.
      apply freezing_Vplus_proper.
      intros ?.
      unfold rvlim.
      specialize (flim a).
      apply is_lim_seq_unique in flim.
      assert (is_finite 
                (Lim_seq (fun n : nat => simple_approx (fun x : Ts2 * Ts => Psi x) n a))).
      {
        rewrite flim.
        now unfold is_finite.
      }
      rewrite <- H0 in flim.
      apply Rbar_finite_eq in flim.
      now rewrite flim.
    - intros.
      apply freezing_Vplus_frf with (sub3 := sub3); try easy.
      + apply (compose_rv (dom2 := product_sa cod dom3) (fun ω => (X ω, ω))); trivial.
        apply product_sa_rv.
        * now apply (RandomVariable_sa_sub sub2).
        * apply (RandomVariable_sa_sub sub3).
          apply id_rv.
      + apply IsFiniteExpectation_bounded with 
          (rv_X1 := const 0) 
          (rv_X3 := fun ω => Psi (X ω, ω)).
        * apply IsFiniteExpectation_const.
        * apply isfe.
        * intros ?.
          apply apx_nnf.
        * intros ?.
          specialize (apx_le n (X a, a)).
          now simpl in apx_le.
       + intros.
         apply IsFiniteExpectation_bounded with
          (rv_X1 := const 0) 
          (rv_X3 := fun ω => Psi (x, ω)).
         * apply IsFiniteExpectation_const.
         * apply isfe2.
         * intros ?.
           apply apx_nnf.
         * intros ?.
           apply apx_le.
    - intros ??.
      apply apx_inc.
    - intros.
      exists (Psi ω).
      apply flim.
    - revert isfe.
      apply IsFiniteExpectation_proper.
      intros ?.
      unfold rvlim.
      specialize (flim (X a, a)).
      apply is_lim_seq_unique in flim.
      assert (is_finite 
                (Lim_seq (fun n : nat => simple_approx (fun x : Ts2 * Ts => Psi x) n (X a, a)))).
      {
        rewrite flim.
        now unfold is_finite.
      }
      rewrite <- H1 in flim.
      apply Rbar_finite_eq in flim.
      now rewrite flim.
    - intros.
      specialize (isfe2 x).
      revert isfe2.
      apply IsFiniteExpectation_proper.
      intros ?.
      unfold rvlim.
      specialize (flim (x, a)).
      apply is_lim_seq_unique in flim.
      assert (is_finite 
                (Lim_seq (fun n : nat => simple_approx (fun x : Ts2 * Ts => Psi x) n (x, a)))).
      {
        rewrite flim.
        now unfold is_finite.
      }
      rewrite <- H1 in flim.
      apply Rbar_finite_eq in flim.
      now rewrite flim.
  Qed.

  Lemma rv_pos_neg_id' {Ts} (rv_X:Ts->R) : 
    rv_eq rv_X 
      (rvminus (pos_fun_part rv_X) (neg_fun_part rv_X)).
    Proof.
      intros x.
      unfold rvminus, rvplus, rvopp, pos_fun_part, neg_fun_part, rvscale; simpl.
      unfold Rmax, Rmin.
      repeat match_destr; lra.
    Qed.

 Lemma freezing_sa {Ts Ts2} {dom dom2 dom3: SigmaAlgebra Ts} {cod : SigmaAlgebra Ts2} {prts : ProbSpace dom}
       (sub2 : sa_sub dom2 dom)
       (sub3 : sa_sub dom3 dom)       
       (X : Ts -> Ts2) 
       (Psi : Ts2 * Ts -> R)
       {rvx : RandomVariable dom2 cod X}      
       {rvPsi : RandomVariable (product_sa cod dom3) borel_sa Psi}
       {rvPsi2: RandomVariable dom borel_sa (fun ω : Ts => Psi (X ω, ω))}
       {isfe : IsFiniteExpectation prts (fun ω => Psi (X ω, ω))}
       {isfe2: forall x, IsFiniteExpectation prts (fun ω : Ts => Psi (x, ω))}   :
  independent_sas prts sub2 sub3 ->
  almostR2 (prob_space_sa_sub prts sub2) eq (ConditionalExpectation prts sub2 (fun ω => Psi (X ω, ω)))
           (fun ω => ((fun x => FiniteExpectation prts (fun ω => Psi (x, ω))) (X ω))).
 Proof.
   intros.
   generalize (rv_pos_neg_id' Psi); intros HH.
   assert (freezing_Vplus sub2 X (pos_fun_part Psi)).
   {
     apply freezing_Vplus_nnf with (sub3 := sub3); trivial.
     - apply positive_part_nnf.
     - now apply positive_part_rv.
     - now apply positive_part_rv.
     - now apply (IsFiniteExpectation_parts prts (fun ω => Psi (X ω, ω))).
     - intros; now apply (IsFiniteExpectation_parts prts (fun ω => Psi (x, ω))).
   }
   assert (freezing_Vplus sub2 X (neg_fun_part Psi)).
   {
     apply freezing_Vplus_nnf with (sub3 := sub3); trivial.
     - apply negative_part_nnf.
     - now apply negative_part_rv.
     - now apply negative_part_rv.
     - now apply (IsFiniteExpectation_parts prts (fun ω => Psi (X ω, ω))).
     - intros; now apply (IsFiniteExpectation_parts prts (fun ω => Psi (x, ω))).
   }
   destruct H0 as [?[?[?[?[??]]]]].
   destruct H1 as [?[?[?[?[??]]]]].   
   generalize (Condexp_minus prts sub2
                 (fun ω : Ts => pos_fun_part Psi (X ω, ω))
                 (fun ω : Ts => neg_fun_part Psi (X ω, ω))                 
              ); intros.
   revert H8; apply almost_impl.
   revert H7; apply almost_impl.
   revert H4; apply almost_impl.
   apply all_almost; intros ????.
   unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp in H8.
   rewrite H4 in H8.
   rewrite H7 in H8.
   etransitivity; [etransitivity |]; [| apply H8 |].
   - apply ConditionalExpectation_ext.
     intros ?.
     now rewrite HH.
   - generalize (FiniteExpectation_minus prts
                   (fun ω : Ts => pos_fun_part Psi (X x3, ω))
                   (fun ω : Ts => neg_fun_part Psi (X x3, ω))); intros.
     simpl.
     apply Rbar_finite_eq.
     simpl in H9.
     ring_simplify.
     rewrite <- H9.
     apply FiniteExpectation_ext.
     intros ?.
     unfold rvminus, rvplus, rvopp, rvscale.
     unfold rvminus, rvplus, rvopp, rvscale in HH.
     specialize (HH (X x3, a)).
     simpl in HH.
     now symmetry.
  Qed.
       
Require Import Dynkin.
Section monotone_class.

  Lemma pre_event_indicator_disjoint_sum {Ts}
    (l : list (pre_event Ts))
    (union_dec:forall l (a:Ts), {pre_list_union l a} + {~ pre_list_union l a})
    (is_disj: ForallOrdPairs pre_event_disjoint l) :
    forall a, EventIndicator (union_dec l) a =
    (list_sum
       (map (fun ev => EventIndicator (classic_dec ev) a) l)).
  Proof.
    unfold EventIndicator; intros.
    induction l.
    - match_destr; simpl in *.
      destruct p; simpl in *; tauto.
    - invcs is_disj.
      specialize (IHl H2).
      simpl.
      rewrite Forall_forall in H1.
      rewrite <- IHl; clear IHl.
      unfold pre_list_union in *.
      repeat match_destr; try lra; firstorder congruence.
  Qed.

  Context {S:Type}.

  Lemma function_monotone_class_theorem_simple
    (H:(S->R)->Prop)
    (Hbounded:forall f, H f -> exists k, forall s, Rabs(f s) <= k)
    (Hplus: forall f g, H f -> H g -> H (rvplus f g))
    (Hscal: forall c f, H f -> H (rvscale c f))
    (Hone:H (const 1))
    (Hlim_closure:
      forall (fn:nat->(S->R)) (f:S->R) k,
        (forall n, H (fn n)) ->
        (forall n s, 0 <= (fn n s)) ->
        (forall n s, fn n s <= fn (Datatypes.S n) s) ->
        (forall s, f s <= k) ->
        (forall s, is_lim_seq (fun n => fn n s) (f s)) ->
       H f)
    (I:(S->Prop) -> Prop)
    {Ipi : Pi_system I}
    (HcontainsI:forall i, I i -> H (EventIndicator (classic_dec i)))
    (g:S->R)
    (gk:R)
    (gbounded:forall s, Rabs(g s) <= gk)
    (grv:RandomVariable (generated_sa I) borel_sa g)
    (gfrf:FiniteRangeFunction g)
    : H g.
  Proof.
    pose (D:=fun F => H (EventIndicator (classic_dec F))).
    assert (Hproper:Proper (pointwise_relation _ eq ==> iff) H).
    {
      intros ???.
      now apply functional_extensionality in H0; subst.
    }

    assert (Hconst : forall c, H (const c)).
    {
      intros.
      apply (Hproper _ (rvscale c (const 1))).
      - unfold rvscale, const.
        intros ?; lra.
      - apply Hscal.
        apply Hone.
    }

    assert (Hlist_sum : forall (l:list (S->R)),
               Forall H l -> H (fun s => (list_sum (map (fun x => x s) l)))).
    {
      induction l; intros; simpl.
      - apply Hconst.
      - invcs H0.
        apply Hplus; auto.
    }
    
    assert (Dlambda : Lambda_system D).
    {
      unfold D.
      constructor.
      - eapply Hproper; try apply Hone.
        intros ?.
        unfold EventIndicator, const, pre_Ω.
        match_destr.
        tauto.
      - intros ???.
        apply Hproper; intros ?.
        unfold EventIndicator.
        specialize (H0 a).
        repeat match_destr; tauto.
      - intros.
        generalize (Hplus _ _ Hone (Hscal (-1) _ H0)).
        apply Hproper; intros ?.
        unfold EventIndicator, rvplus, rvscale, const, pre_event_complement.
        repeat match_destr; try tauto; try lra.
      - intros.
        apply (Hlim_closure
                 (fun n => (EventIndicator (classic_dec
                                           (pre_list_union (collection_take an n))))) _ 1).
        + intros.
          apply (Hproper _
                         (fun a : S =>
                            list_sum
                              (map (fun x => x a)
                                 (map (fun ev : pre_event S => EventIndicator (classic_dec ev)) (collection_take an n))))
).
          * intros ?.
            rewrite (pre_event_indicator_disjoint_sum (collection_take an n)
                       (fun l => classic_dec (pre_list_union l))).
            -- now rewrite map_map.
            -- now apply pre_collection_take_preserves_disjoint.
          * apply Hlist_sum.
            apply Forall_map.
            apply Forall_forall; intros.
            apply In_collection_take in H2.
            now destruct H2 as [? [??]]; subst.
        + intros.
          apply EventIndicator_pos.
        + intros.
          unfold EventIndicator.
          repeat match_destr; try lra.
          elim n0.
          apply pre_list_union_take_Sn.
          now left.
        + intros.
          unfold EventIndicator.
          match_destr; try lra.
        + intros.
          apply is_lim_seq_spec.
          simpl; intros eps.
          destruct (classic_min_of_sumbool (fun n => an n s)).
          * destruct s0 as [N [anN _]].
            exists (Datatypes.S N).
            intros.
            assert (eqq:(EventIndicator (classic_dec (pre_list_union (collection_take an n))) s =
                       EventIndicator (classic_dec (pre_union_of_collection an)) s)).
            {
              unfold EventIndicator.
              repeat match_destr.
              - elim n0.
                revert p.
                apply pre_list_union_take_collection_sub.
              - elim n0.
                exists (an N).
                split; trivial.
                apply in_map.
                apply in_seq.
                lia.
            }
            rewrite eqq, Rminus_eq_0, Rabs_R0.
            apply cond_pos.
          * exists 0%nat; intros.
            assert (eqq:(EventIndicator (classic_dec (pre_list_union (collection_take an n0))) s =
                           EventIndicator (classic_dec (pre_union_of_collection an)) s)).
            {
              unfold EventIndicator.
              repeat match_destr.
              - destruct p as [? [inn ?]].
                apply In_collection_take in inn.
                destruct inn as [? [??]]; subst.
                elim (n _ H3).
              - destruct p.
                elim (n _ H3).
            }
            rewrite eqq, Rminus_eq_0, Rabs_R0.
            apply cond_pos.
    }

    assert (Dcontains_genI :
             pre_event_sub (sa_sigma (generated_sa I)) D).
    {
      now apply Dynkin.
    }
    assert (forall (e : pre_event S),
               (sa_sigma (generated_sa I) e) ->
               H (EventIndicator (classic_dec e))).
    {
      intros.
      assert (D e) by now apply Dcontains_genI.
      apply H1.
    }
    rewrite frf_preimage_indicator'.
    specialize (Hlist_sum 
                  (map (fun c a => c * point_preimage_indicator g c a) (nodup Req_EM_T frf_vals))).
    cut_to Hlist_sum.
    - revert Hlist_sum.
      apply Hproper; intros s.
      now rewrite map_map.
    - apply Forall_map.
      apply Forall_nodup.
      apply Forall_forall.
      intros.
      apply Hscal.
      unfold point_preimage_indicator.
      specialize (H0 (fun x0 => g x0 = x)).
      cut_to H0.
      + revert H0.
        apply Hproper.
        intros ?.
        unfold EventIndicator.
        repeat match_destr; congruence.
      + apply sa_le_pt.
        intros.
        now apply rv_measurable.
  Qed.
  
  Lemma function_monotone_class_theorem_nneg
    (H:(S->R)->Prop)
    (Hbounded:forall f, H f -> exists k, forall s, Rabs(f s) <= k)
    (Hplus: forall f g, H f -> H g -> H (rvplus f g))
    (Hscal: forall c f, H f -> H (rvscale c f))
    (Hone:H (const 1))
    (Hlim_closure:
      forall (fn:nat->(S->R)) (f:S->R) k,
        (forall n, H (fn n)) ->
        (forall n s, 0 <= (fn n s)) ->
        (forall n s, fn n s <= fn (Datatypes.S n) s) ->
        (forall s, f s <= k) ->
        (forall s, is_lim_seq (fun n => fn n s) (f s)) ->
       H f)
    (I:(S->Prop) -> Prop)
    {Ipi : Pi_system I}
    (HcontainsI:forall i, I i -> H (EventIndicator (classic_dec i)))
    (g:S->R)
    (gk:R)
    (gbounded:forall s, g s <= gk)
    (grv:RandomVariable (generated_sa I) borel_sa g)
    (nng:NonnegativeFunction g)
    : H g.
  Proof.
    generalize (simple_approx_lim_seq g nng); intro glim.
    generalize (simple_approx_frf g); intro apx_frf.
    generalize (simple_approx_pofrf g); intro apx_nnf.
    generalize (simple_approx_rv (dom := generated_sa I) g); intros apx_rv.
    generalize (simple_approx_le g nng); intro apx_le.
    generalize (simple_approx_increasing g nng); intro apx_inc.
    apply (Hlim_closure (fun n s => simple_approx g n s) _ gk); try easy.
    intros.
    apply function_monotone_class_theorem_simple with (I := I) (gk := gk); try easy.
    intros.
    specialize (apx_le n s).
    simpl in apx_le.
    rewrite Rabs_right.
    - eapply Rle_trans.
      apply apx_le.
      apply gbounded.
    - apply Rle_ge.
      apply apx_nnf.
  Qed.      
      
  Lemma function_monotone_class_theorem
    (H:(S->R)->Prop)
    (Hbounded:forall f, H f -> exists k, forall s, Rabs (f s) <= k)
    (Hplus: forall f g, H f -> H g -> H (rvplus f g))
    (Hscal: forall c f, H f -> H (rvscale c f))
    (Hone:H (const 1))
    (Hlim_closure:
      forall (fn:nat->(S->R)) (f:S->R) k,
        (forall n, H (fn n)) ->
        (forall n s, 0 <= (fn n s)) ->
        (forall n s, fn n s <= fn (Datatypes.S n) s) ->
        (forall s, f s <= k) ->
        (forall s, is_lim_seq (fun n => fn n s) (f s)) ->
       H f)
    (I:(S->Prop) -> Prop)
    {Ipi : Pi_system I}
    (HcontainsI:forall i, I i -> H (EventIndicator (classic_dec i)))
    (g:S->R)
    (gk:R)
    (gbounded:forall s, Rabs(g s) <= gk)
    (grv:RandomVariable (generated_sa I) borel_sa g)
    : H g.
  Proof.
    assert (Hproper:Proper (pointwise_relation _ eq ==> iff) H).
    {
      intros ???.
      now apply functional_extensionality in H0; subst.
    }
    rewrite rv_pos_neg_id.
    apply Hplus.
    - apply function_monotone_class_theorem_nneg with (I := I) (gk := gk); try easy.
      + intros.
        eapply Rle_trans.
        apply pos_fun_part_le.
        apply gbounded.
      + now apply positive_part_rv.
      + apply positive_part_nnf.
    - unfold rvopp.
      apply Hscal.
      apply function_monotone_class_theorem_nneg with (I := I) (gk := gk); try easy.
      + intros.
        eapply Rle_trans.
        apply neg_fun_part_le.
        apply gbounded.
      + now apply negative_part_rv.
      + apply negative_part_nnf.
  Qed.  

End monotone_class.
