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

  Context (α : event A -> Rbar) (meas_α : is_measure α).
  Context (β : event B -> Rbar) (meas_β : is_measure β).
  
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

Section ps_product.
  Context {X Y:Type}.
  Context {A:SigmaAlgebra X}.
  Context {B:SigmaAlgebra Y}.

  Context (ps1 : ProbSpace A).
  Context (ps2 : ProbSpace B).
  
  Lemma product_measure_Hyp_ps :
    measure_rectangle_pm_additive_Hyp (ps_P (σ:=A)) (ps_measure _) (ps_P (σ:=B)) (ps_measure _).
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
               (product_measure (ps_P (σ:=A)) (ps_measure _) (ps_P (σ:=B)) (ps_measure _)).
  Proof.
    apply product_measure_is_measurable.
    apply product_measure_Hyp_ps.
  Qed.

  Global Instance product_ps : ProbSpace (product_sa A B).
  Proof.
    apply (measure_all_one_ps (product_measure (ps_P (σ:=A)) (ps_measure _) (ps_P (σ:=B)) (ps_measure _))).
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
    apply (measure_proper (σ:=product_sa A B) (μ:=product_measure (fun x : event A => ps_P x) (ps_measure ps1) (fun x : event B => ps_P x) 
                                                                  (ps_measure ps2)) Ω (exist _ _ sa)).
    now red; simpl.
  Defined.

  Global Instance product_ps_proper : Proper (pre_event_equiv ==> eq)
                                                  (product_measure (ps_P (σ:=A)) (ps_measure _) (ps_P (σ:=B)) (ps_measure _)).
  Proof.
    apply product_measure_proper.
    apply product_measure_Hyp_ps.
  Qed.    
  
  Theorem product_sa_product (a:event A) (b:event B) :
    ps_P (ProbSpace:=product_ps) (product_sa_event a b) =
      ps_P a * ps_P b.
  Proof.
    simpl.
    rewrite product_measure_product; simpl; trivial.
    apply product_measure_Hyp_ps.
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
    assert (ps_P (rv_preimage fst A0) = ps_P A0).
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

End ps_product.

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
           
  Lemma ivector_nth_independent_rv_0 {n} {T} {σ:SigmaAlgebra T} 
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

  Lemma ivector_nth_independent_rv {n} {T} {σ:SigmaAlgebra T} 
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
      + apply (ivector_nth_independent_rv_0 (n:=S n) (p,i) idx2).
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
     
  Lemma ivector_take_rv {n} {T} (ivsa : ivector (SigmaAlgebra T) n) (idx : nat)
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

End ps_ivector_product.
Section ps_sequence_product.
  
  Fixpoint sequence_to_ivector {T} (x : nat -> T) j h : ivector T h
    := match h with
       | 0 => tt
       | S n => (x j, sequence_to_ivector x (S j) n)
       end.

  Definition sequence_cons {T} (x : T) (xs : nat -> T) : nat -> T :=
    fun n0 =>
      match n0 with
      | 0 => x
      | S n => xs n
      end.

  Definition inf_cylinder_event {T} {n} {σ:SigmaAlgebra T} 
             (e : pre_event (ivector T n)) : (pre_event (nat -> T)) :=
    fun (w : nat -> T) => e (sequence_to_ivector w 0%nat n).

  Definition inf_cylinder {T} {σ:SigmaAlgebra T} : (pre_event (nat -> T)) -> Prop :=
    fun (e : pre_event (nat -> T)) =>
      exists (n : nat),
        exists (ee : pre_event (ivector T (S n))),
          sa_sigma (ivector_sa (ivector_const (S n) σ)) ee /\ 
          e === inf_cylinder_event ee.

  Definition section_seq_event {T} {σ:SigmaAlgebra T} (x : T) 
             (e : pre_event (nat -> T)) : pre_event (nat -> T) :=
    fun (w : (nat -> T)) => e (sequence_cons x w).
      
  Definition ps_P_cylinder  {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) : R.
    unfold inf_cylinder in ecyl.
    apply constructive_indefinite_description in ecyl; destruct ecyl.
    apply constructive_indefinite_description in e0; destruct e0 as [? [? ?]].
    exact (ps_P (ProbSpace := ivector_ps (sequence_to_ivector ps 0%nat (S x)))
                (exist _ _ H)).
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
    exists n,
      let vps := sequence_to_ivector ps 0%nat (S n) in
      exists (ee : event (ivector_sa (ivector_const (S n) σ))),
          sa_sigma (ivector_sa (ivector_const (S n) σ)) ee /\ 
          e === inf_cylinder_event ee /\
          Finite  (ps_P_cylinder ps e ecyl) =
          NonnegExpectation 
            (Prts := (ivector_hd vps))
            (fun x => ps_P 
                        (ProbSpace := ivector_ps (ivector_tl vps))
                        (exist _ _ 
                               (ivector_product_section (ivector_const (S n) σ) 
                                                        ee x))).
  Proof.
    destruct ecyl as [? [? [? ?] ]].
    exists x.
    exists (exist _ _ s).
    split; try easy.
    split; try easy.
    
    unfold ps_P_cylinder.
    match_destr; intros.
    match_destr; intros.
    match_destr; intros.
    (* need that x = x2, x0 === x2, s == s0 *)
  Admitted.

  Instance nonneg_fun_nonnegreal {T} (g : T -> nonnegreal) :
    NonnegativeFunction g.
  Proof.
    intro x.
    apply cond_nonneg.
  Qed.

  Lemma ps_P_cylinder_expectation2 {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) : 
    exists (g : T -> nonnegreal),
      Finite (ps_P_cylinder ps e ecyl) =
      NonnegExpectation (Prts := ps 0%nat) g /\
      RandomVariable σ borel_sa g.
   Proof.
     generalize (ps_P_cylinder_expectation ps e ecyl); intros.
     destruct H as [? [? [? [? ?]]]].
     assert (forall (x1 : T),
                0 <=
                ps_P
                  (ProbSpace := (ivector_ps 
                                   (ivector_tl (sequence_to_ivector ps 0%nat (S x)))))
                  (exist (sa_sigma (ivector_sa (ivector_tl (ivector_const (S x) σ))))
                         (fun y : ivector T x => x0 (x1, y))
                         (ivector_product_section (ivector_const (S x) σ) x0 x1))).
     {
       intros.
       apply ps_pos.
     }
     exists (fun x1 : T => mknonnegreal _ (H2 x1)).
     split.
     - apply H1.
     - simpl.
       generalize (product_ps_section_measurable_fst (ivector_ps 
                                                        (ivector_tl (sequence_to_ivector ps 0%nat (S x)))) x0); intros.
       revert H3.
       apply RandomVariable_proper; try easy.
       intro x1.
       apply ps_proper.
       now intro xx.
   Qed.

  Lemma ps_P_cylinder_expectation3 {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ)
             (e : (pre_event (nat -> T))) 
             (ecyl : inf_cylinder e) : 
    {g : T -> nonnegreal |
      Finite (ps_P_cylinder ps e ecyl) =
      NonnegExpectation (Prts := ps 0%nat) g /\
      RandomVariable σ borel_sa g}.
  Proof.
    generalize (ps_P_cylinder_expectation2 ps e ecyl); intros.
    now apply constructive_indefinite_description in H.
  Qed.

  Lemma ps_P_cylinder_expectation4 {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ) :
    exists (g : {e : (pre_event (nat -> T)) | inf_cylinder e} -> T -> nonnegreal),
    forall (ee : {e : (pre_event (nat -> T)) | inf_cylinder e}),
      Finite (ps_P_cylinder ps (proj1_sig ee) (proj2_sig ee)) =
      NonnegExpectation (Prts := ps 0 %nat) (g ee)  /\
      RandomVariable σ borel_sa (g ee).
  Proof.
    exists (fun ee => proj1_sig (ps_P_cylinder_expectation3 ps (proj1_sig ee) (proj2_sig ee))).
    intros.
    unfold proj1_sig.
    match_destr.
    unfold proj2_sig.
    match_destr.
  Qed.

  Lemma ps_P_cylinder_expectation5 {T} {σ:SigmaAlgebra T} 
             (ps : nat -> ProbSpace σ) :
    {g : {e : (pre_event (nat -> T)) | inf_cylinder e} -> T -> nonnegreal |
      forall (ee : {e : (pre_event (nat -> T)) | inf_cylinder e}),
        Finite (ps_P_cylinder ps (proj1_sig ee) (proj2_sig ee)) =
        NonnegExpectation (Prts := ps 0 %nat) (g ee) /\
      RandomVariable σ borel_sa (g ee)}.
   Proof.
     generalize (ps_P_cylinder_expectation4 ps); intros.
    now apply constructive_indefinite_description in H.
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

  Lemma decreasing_cyl_nonempty_1  {T} {σ:SigmaAlgebra T}
             (ps : nat -> ProbSpace σ)        
             (es : nat -> (pre_event (nat -> T))) 
             (ecyl : forall n, inf_cylinder (es n)) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    Rbar_gt (Lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n))) 0 ->
    exists (x : T),
    forall n, 
      Rbar_gt (proj1_sig (ps_P_cylinder_expectation5 ps) (exist _ (es n) (ecyl n)) x) 0.
  Proof.
    intros.
    destruct (ps_P_cylinder_expectation5 ps).
    pose (f1 := rvlim (fun n x1 => x (exist _ (es n) (ecyl n)) x1)).
    assert (NonnegativeFunction f1).
    {
      apply nnflim.
      intros.
      intro z.
      simpl.
      apply cond_nonneg.
    }
    assert (decrx: forall n omega,
               x (exist _ (es (S n)) (ecyl (S n))) omega <= x (exist _ (es n) (ecyl n)) omega).
    {
      intros.
      
      admit.
    }
    assert (exfin: forall omega,  ex_finite_lim_seq (fun n : nat => x (exist _ (es n) (ecyl n)) omega)).
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
        now destruct (a (exist _ (es n) (ecyl n))) as [? ?].
      - intros.
        apply exfin.
    }
    generalize (NonnegExpectation_gt_val_nneg (Prts := ps 0%nat) f1 0); intros.
    cut_to H3; try lra.
    - destruct H3.
      exists x0.
      intros.
      simpl.
      apply (Lim_seq_decreasing_pos (fun n =>  x (exist _ (es n) (ecyl n)) x0)).
      + intros; apply decrx.
      + simpl in f1.
        unfold rvlim in f1.
        unfold f1 in H3.
        specialize (exfin x0).
        apply ex_finite_lim_seq_correct in exfin.
        destruct exfin.
        rewrite <- H5.
        simpl.
        apply H3.
    - generalize (monotone_convergence (Prts := ps 0%nat) f1  
                                       (fun (n : nat) (x1 : T) => x (exist inf_cylinder (es n) (ecyl n)) x1) H2); intros.
      erewrite <- H4.
      + rewrite Lim_seq_ext with
            (v := fun n => Finite (ps_P_cylinder ps (es n) (ecyl n))); trivial.
        intros.
        destruct (a (exist _ (es n) (ecyl n))).
        simpl in H5.
        now rewrite H5.
      + intros.
        now destruct (a (exist _ (es n) (ecyl n))).
      + (* need descending monontone convergence *) admit.
      + (* need descending monontone convergence *) admit.
      + intros.
        destruct (a (exist _ (es n) (ecyl n))).
        simpl in H5.
        now rewrite <- H5.
      + intros.
        now apply Lim_seq_correct'.
  Admitted.   
    
  
  Lemma decreasing_cyl_nonempty  {T} {σ:SigmaAlgebra T}
             (ps : nat -> ProbSpace σ)        
             (es : nat -> (pre_event (nat -> T))) 
             (ecyl : forall n, inf_cylinder (es n)) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    Lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n)) > 0 ->
    exists (z : nat -> T), (pre_inter_of_collection es) z.
  Proof.
    intros decr limpos.
    Admitted.


End ps_sequence_product.

