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

  Lemma ivector_take_const {T} (x:T) n m lt :
    ivector_take m n lt (ivector_const m x) = ivector_const n x.
  Proof.
    revert n lt.
    induction m; simpl; intros.
    - now destruct n; [| lia]; simpl.
    - destruct n; [simpl; trivial |].
      now rewrite IHm with (lt:=le_S_n n m lt); simpl.
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

    Lemma ivector_take_pullback_rectangle {n} {T} {σ:SigmaAlgebra T}
        (ivec_ps : ivector (ProbSpace σ) n) idx pf :
    forall (ve : ivector (event σ) idx),
      ps_P (ProbSpace := pullback_ps _ _  (ivector_ps ivec_ps) (ivector_take n idx pf)) (ivector_sa_event ve) =
      ps_P (ProbSpace:=ivector_ps (ivector_take n idx pf ivec_ps)) (ivector_sa_event ve).
    Proof.
      Admitted.

  Lemma ivector_take_pullback {n} {T} {σ:SigmaAlgebra T}
        (ivec_ps : ivector (ProbSpace σ) n) idx pf :
     forall (a : event (ivector_sa (ivector_const idx σ))),
       ps_P (ProbSpace := ivector_ps (ivector_take n idx pf ivec_ps)) a = 
       ps_P (ProbSpace := pullback_ps _ _  (ivector_ps ivec_ps) (ivector_take n idx pf)) a.
  Proof.
    intros.
    generalize product_ps_unique; intros.
    generalize (ivector_sa_product (ivector_take n idx pf ivec_ps)); intros.
    
  Admitted.

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

  Definition ivector_to_sequence {T} {n} (v : ivector T n) (default : T) 
    : nat -> T :=
    (fun i => 
       match lt_dec i n with
       | left pf => ivector_nth i pf v
       | right _ => default
       end).

   Lemma sequence_to_ivector_cons_shift {T} {n} (j : nat) (x : nat -> T) (val : T) :
     sequence_to_ivector (sequence_cons val x) (S j) n = sequence_to_ivector x j n.
   Proof.
     revert j.
     induction n.
     - intros.
       now simpl.
     - intros.
       simpl.
       f_equal.
       apply IHn.
   Qed.

   Lemma sequence_to_ivector_cons {T} {n} (x : nat -> T) (val : T) :
    sequence_to_ivector (sequence_cons val x) 0%nat (S n) =
    (val, sequence_to_ivector x 0%nat n).
  Proof.
    apply ivector_eq2.
    split.
    - now simpl.
    - apply sequence_to_ivector_cons_shift.
  Qed.

  Lemma ivec_nth_cons {T} {n} (x : ivector T n) (val : T) (x0 : nat) (l : (S x0 < S n)%nat) :
    ivector_nth (S x0) l (val, x) = ivector_nth x0 (le_S_n _ _ l) x.
  Proof.
    destruct n.
    - lia.
    - simpl.
      match_destr.
      match_destr.
      now apply ivector_nth_ext.
  Qed.

  Lemma ivec_sequence_cons {T} {n} (x : ivector T n) (val : T) (default : T) :
    ivector_to_sequence (n := S n) (val, x) default =
    sequence_cons val (ivector_to_sequence x default).
  Proof.
    apply functional_extensionality.
    destruct x0.
    - simpl.
      unfold ivector_to_sequence.
      match_destr.
      lia.
    - simpl.
      unfold ivector_to_sequence.
      match_destr; try lia.
      match_destr; try lia.
      + rewrite ivec_nth_cons.
        now apply ivector_nth_ext.
      + match_destr; try lia.
  Qed.

  Lemma ivec_to_seq_to_ivec {T} {n} (v : ivector T n) (default : T)  :
    v = sequence_to_ivector (ivector_to_sequence v default) 0%nat n.
  Proof.
    induction n.
    - simpl.
      now destruct v.
    - destruct v.
      rewrite ivec_sequence_cons.
      rewrite sequence_to_ivector_cons.
      specialize (IHn i).
      now rewrite <- IHn.
   Qed.

  Lemma ivector_take_cons {T} {N} (n : nat) (v : ivector T N)(val : T) 
        (le : (S n <= S N)%nat) :
    ivector_take (S N) (S n) le (val, v) = 
    (val, ivector_take N n (le_S_n _ _ le) v).
  Proof.
    apply ivector_eq2.
    now simpl.
  Qed.
  
  Definition inf_cylinder_event {T} {n} {σ:SigmaAlgebra T} 
             (e : pre_event (ivector T n)) : (pre_event (nat -> T)) :=
    fun (w : nat -> T) => e (sequence_to_ivector w 0%nat n).

  Definition inf_cylinder {T} {σ:SigmaAlgebra T} : (pre_event (nat -> T)) -> Prop :=
    fun (e : pre_event (nat -> T)) =>
      exists (n : nat),
        exists (ee : pre_event (ivector T (S n))),
          sa_sigma (ivector_sa (ivector_const (S n) σ)) ee /\ 
          e === inf_cylinder_event ee.


(*
  Lemma ivector_take_sequence {T} (x : nat -> T) (s n m : nat) 
        (lt : (S n <= S m)%nat) :
    sequence_to_ivector x s (S n) =
    ivector_take (S m) (S n) lt (sequence_to_ivector x s (S m)).
  Proof.
    revert n s lt.
    induction m; simpl; intros.
    - now destruct n; [| lia]; simpl.
    - destruct n; [simpl; trivial |].
      now rewrite IHm with (lt:=le_S_n (S n) (S m) lt); simpl.
  Qed.
 *)
  
  Lemma ivector_take_sequence {T} (x : nat -> T) (s n m : nat) 
        (lt : (n <= m)%nat) :
    sequence_to_ivector x s n =
    ivector_take m n lt (sequence_to_ivector x s m).
  Proof.
    revert n s lt.
    induction m; simpl; intros.
    - now destruct n; [| lia]; simpl.
    - destruct n; [simpl; trivial |].
      now rewrite <- IHm.
   Qed.

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
    now rewrite ivector_take_sequence with (m0 := m) (lt := pf).
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
       rewrite Expectation_pos_pofrf with (nnf0 := nncf) in H2.  
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
        (inh : NonEmpty T):
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
      apply rvlt_finexp_contra with (prts0 := prts) (isfe := H1); trivial.
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
             (inh : NonEmpty T)
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
    generalize (rvlt_nnexp_contra (ps 0%nat) f1 H2 H1 eps inh); intros.
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
   
   Lemma sequence_to_ivector_shift {T} (x : nat -> T) (j N : nat) :
     sequence_to_ivector x (S j) N = sequence_to_ivector (fun n0 : nat => x (S n0)) j N.
   Proof.
     revert j.
     induction N.
     - now simpl.
     - intros.
       simpl.
       f_equal.
       now rewrite IHN.
   Qed.

   Lemma cons_sequence_to_ivector {T} (w : nat -> T) (x2 : nat) :
     (w 0%nat, sequence_to_ivector w 1 x2) = sequence_to_ivector w 0 (S x2).
   Proof.
     reflexivity.
   Qed.

   Lemma sequence_to_ivector_ext {T} (f g : nat -> T) start len :
     pointwise_relation _ eq f g ->
     sequence_to_ivector f start len = sequence_to_ivector g start len.
   Proof.
     revert start.
     induction len; simpl; trivial; intros start eqq.
     now rewrite eqq, IHlen.
   Qed.
   
   Lemma decreasing_cyl_nonempty_2  {T}  {σ:SigmaAlgebra T}
         (inh : NonEmpty T)
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
    destruct (decreasing_cyl_nonempty_1_alt inh ps es ecyl eps H H0).
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

   Lemma decreasing_cyl_nonempty_2_alt  {T}  {σ:SigmaAlgebra T}
         (inh : NonEmpty T)
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
     generalize (decreasing_cyl_nonempty_2 inh ps es ecyl eps H H0); intros.
     now apply constructive_indefinite_description in H1.
  Qed.

   Fixpoint sequence_prefix {T} (pre w : nat -> T) (N : nat) : nat -> T :=
      match N with
      | 0 => w
      | S n => sequence_cons (pre 0%nat) (sequence_prefix (fun n => pre (S n)) w n)
      end.
   
   Fixpoint ivector_append {T} {n1 n2} : ivector T n1 -> ivector T n2 -> ivector T (n1 + n2) :=
     match n1 as n1' return ivector T n1' -> ivector T n2 -> ivector T (n1' + n2) with
     | 0%nat => fun _ v2 => v2
     | S n%nat => fun '(hd,tail) v2 => (hd, ivector_append tail v2)
     end.

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

   Lemma sequence_prefix_ivector_append {T} (x1 x2 : nat -> T) (n1 n2 : nat) :
     sequence_to_ivector (sequence_prefix x1 x2 n1) 0 (n1 + n2)%nat =
     ivector_append (sequence_to_ivector x1 0 n1) (sequence_to_ivector x2 0 n2).
   Proof.
     revert x1 n2.
     induction n1; trivial; intros; simpl.
     rewrite sequence_to_ivector_cons_shift.
     f_equal.
     rewrite IHn1.
     f_equal.
     now rewrite sequence_to_ivector_shift.
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

  Lemma sequence_to_ivector_Forall2 {T1 T2} (RR:T1->T2->Prop) (f:nat->T1) (g:nat->T2) s N :
    (forall n : nat, (s <= n <= N + s)%nat -> RR (f n) (g n)) ->
    ivector_Forall2 RR (sequence_to_ivector f s N) (sequence_to_ivector g s N).
  Proof.
    revert s.
    induction N; simpl; trivial; intros.
    split.
    - apply H; lia.
    - apply IHN.
      intros.
      apply H; lia.
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
  
  Definition decreasing_cyl_nonempty_2_seq  {T}  {σ:SigmaAlgebra T}
         (inh : NonEmpty T)
         (ps : nat -> ProbSpace σ)        
         (es : nat -> (pre_event (nat -> T))) 
         (ecyl : forall n, inf_cylinder (es n))
         (eps : posreal) 
         (decr:(forall n, pre_event_sub (es (S n)) (es n)))
         (epsbound:(forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps)) (n:nat) :
    {t : T & { tes : (nat -> (pre_event (nat -> T))) & { tecyl : forall n, inf_cylinder (tes n) |
       (forall i, 
           pre_event_sub
             (tes (S i))
             (tes i)) /\ 
       (forall i, 
           (ps_P_cylinder (fun j => ps (n + S j))%nat
                          (tes i)
                          (tecyl i)) >= eps)}}}.
  Proof.
    induction n.
    - destruct (decreasing_cyl_nonempty_2_alt inh ps es ecyl eps decr epsbound)
        as [t [tdecr tepsbound]].
      exists t.
      exists (fun i => section_seq_event t (es i)).
      exists (fun i => section_inf_cylinder t (es i) (ecyl i)).
      auto.
    - destruct IHn as [t [tes [tecyl [tdecr tepsbound]]]].
      destruct (decreasing_cyl_nonempty_2_alt
                  inh
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
          unfold ps_P_cylinder.
          repeat match_destr.
          replace (sequence_to_ivector 
                     (fun n0 : nat => ps (n + (S (S n0)))%nat) 0 (S x)) with
              (sequence_to_ivector 
                 (fun j : nat => ps ((S n) + (S j))%nat) O (S x)).
          - reflexivity.
          - apply sequence_to_ivector_ext.
            red; intros.
            f_equal.
            lia.
        }
        now rewrite <- H.
   Defined.
  
  Lemma iter_decreasing_cyl_eps {T} {σ:SigmaAlgebra T}
         (inh : NonEmpty T)
         (ps : nat -> ProbSpace σ)        
         (es : nat -> (pre_event (nat -> T))) 
         (ecyl : forall n, inf_cylinder (es n))
         (eps : posreal) :
     (forall n, pre_event_sub (es (S n)) (es n)) ->
     (forall n, ps_P_cylinder ps (es n) (ecyl n) >= eps) ->
     exists (x : nat -> T),
     forall n j,
       ps_P_cylinder (fun n => ps (n + j)%nat)
                     (iter_section_seq_event x j (es n))
                     (iter_section_inf_cylinder x (es n) (ecyl n) j) >= eps.
   Proof.
     intros decr epsbound.
     pose (xx := decreasing_cyl_nonempty_2_seq inh ps es ecyl eps decr epsbound).
     exists (fun n => projT1 (xx n)).
     intros.
     destruct (xx n) as [t [tes [tecyl [tdecr tepsbound]]]].
     
     Admitted.


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

  Lemma decreasing_cyl_nonempty  {T} {σ:SigmaAlgebra T}
             (inh : NonEmpty T)
             (ps : nat -> ProbSpace σ)        
             (es : nat -> (pre_event (nat -> T))) 
             (ecyl : forall n, inf_cylinder (es n)) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    Rbar_gt (Lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n))) 0 ->
    exists (z : nat -> T), (pre_inter_of_collection es) z.
  Proof.
    intros decr limpos.
    generalize (ps_P_cylinder_decreasing ps es ecyl decr); intros ps_decr.
    destruct (decreasing_lim_pos_eps (fun n => ps_P_cylinder ps (es n) (ecyl n)) ps_decr limpos) as [eps ?].
    pose (xx := decreasing_cyl_nonempty_2_seq inh ps es ecyl eps decr H).
    exists (fun n => projT1 (xx n)).
    intros ?.
    destruct (ecyl n) as [? [? [? ?]]].
    destruct (xx n) as [t [tes [tecyl [? ?]]]].
    specialize (H1  (fun n0 : nat => projT1 (xx n0))).
    rewrite H1.
    unfold inf_cylinder_event.
    specialize (H3 n).
    destruct (tecyl n) as [? [? [? ?]]].
    unfold ps_P_cylinder in H3.
    repeat match_destr_in H3.
    
    
  Admitted.

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

  Lemma decreasing_cyl_empty  {T} {σ:SigmaAlgebra T}
             (inh : NonEmpty T)
             (ps : nat -> ProbSpace σ)        
             (es : nat -> (pre_event (nat -> T))) 
             (ecyl : forall n, inf_cylinder (es n)) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    pre_event_equiv (pre_inter_of_collection es) pre_event_none ->
    Lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n)) = 0.
  Proof.
    intro decr.
    contrapose.
    intros.
    destruct (decreasing_cyl_nonempty inh ps es ecyl decr).
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

  Lemma decreasing_cyl_empty_alt  {T} {σ:SigmaAlgebra T}
             (inh : NonEmpty T)
             (ps : nat -> ProbSpace σ)        
             (es : nat -> (pre_event (nat -> T))) 
             (ecyl : forall n, inf_cylinder (es n)) :
    (forall n, pre_event_sub (es (S n)) (es n)) ->
    pre_event_equiv (pre_inter_of_collection es) pre_event_none ->
    is_lim_seq (fun n => ps_P_cylinder ps (es n) (ecyl n)) 0.
  Proof.
    intros.
    generalize (decreasing_cyl_empty inh ps es ecyl H H0); intros.
    rewrite <- H1.
    apply Lim_seq_correct.
    apply ex_lim_seq_decr.
    intros.
    apply ps_P_cylinder_decreasing.
    now intros.
  Qed.

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
          (inh : NonEmpty T)
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
        apply (decreasing_cyl_empty_alt inh ps B (fun n => proj2_sig (B n)) H H0).
  Qed.

  Definition ps_P_cylinder_measure {T} {σ:SigmaAlgebra T}
    (ps : nat -> ProbSpace σ) :=
    fun (x : pre_event (nat -> T)) =>
      outer_λ
        (fun (x : alg_set (inf_cylinder_algebra σ)) =>
           ps_P_cylinder ps (proj1_sig x) (proj2_sig x)).

End ps_sequence_product.

