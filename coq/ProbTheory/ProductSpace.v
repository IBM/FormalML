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

  Lemma sum_Rbar_n_finite_sum_n f n:
    sum_Rbar_n (fun x => Finite (f x)) (S n) = Finite (sum_n f n).
  Proof.
    rewrite sum_n_fold_right_seq.
    unfold sum_Rbar_n, list_Rbar_sum.
    generalize (0).
    induction n; trivial; intros.
    rewrite seq_Sn.
    repeat rewrite map_app.
    repeat rewrite fold_right_app.
    now rewrite <- IHn.
  Qed.

  Lemma Lim_seq_sum_Elim f :
    Lim_seq (sum_n f) = ELim_seq (sum_Rbar_n (fun x => Finite (f x))).
  Proof.
    rewrite <- ELim_seq_incr_1.
    rewrite <- Elim_seq_fin.
    apply ELim_seq_ext; intros.
    now rewrite sum_Rbar_n_finite_sum_n.
  Qed.    

  Lemma rbar_nneg_nneg x :
    Rbar_le 0 x ->
    0 <= x.
  Proof.
    destruct x; simpl; try lra.
  Qed.

  Lemma lim_seq_sum_singleton_is_one f :
    (forall n1 n2, n1 <> n2 -> f n1 = 0 \/ f n2 = 0) ->
    exists n, Lim_seq (sum_n f) = f n.
  Proof.
    intros.
    destruct (classic (exists m, f m <> 0)%type) as [[n ?]|].
    - rewrite <- (Lim_seq_incr_n _ n).
      assert (eqq:forall x,
                 sum_n f (x + n) =
                   f n).
      {
        intros.
        induction x; simpl.
        - destruct n.
          + now rewrite sum_O.
          + rewrite sum_Sn.
            erewrite sum_n_ext_loc; try rewrite sum_n_zero.
            * unfold plus; simpl; lra.
            * intros ??; simpl.
              destruct (H (S n) n0); try lra.
              lia.
        - rewrite sum_Sn, IHx.
          unfold plus; simpl.
          destruct (H n (S (x + n))); try lra.
          lia.
      }
      rewrite (Lim_seq_ext _ _ eqq).
      rewrite Lim_seq_const.
      eauto.
    - assert (eqq:forall x,
                 sum_n f x = 0).
      {
        intros.
        erewrite sum_n_ext; try eapply sum_n_zero.
        intros ?; simpl.
        destruct (Req_EM_T (f n) 0); trivial.
        elim H0; eauto.
      }
      rewrite (Lim_seq_ext _ _ eqq).
      rewrite Lim_seq_const.
      exists (0%nat).
      f_equal; symmetry.
      destruct (Req_EM_T (f 0%nat) 0); trivial.
      elim H0; eauto.
  Qed.

  Lemma lim_seq_sum_singleton_finite f :
    (forall n1 n2, n1 <> n2 -> f n1 = 0 \/ f n2 = 0) ->
    is_finite (Lim_seq (sum_n f)).
  Proof.
    intros.
    destruct (lim_seq_sum_singleton_is_one f H).
    now rewrite H0.
  Qed.

  Lemma Rbar_NonnegExpectation_const_pinfty {Ts} {dom: SigmaAlgebra Ts} (prts:ProbSpace dom)
        (pf:Rbar_NonnegativeFunction (const (B:=Ts) p_infty)) :
    Rbar_NonnegExpectation (const p_infty) = p_infty.
  Proof.
    generalize (Rbar_NonnegExpectation_pos (const p_infty)); intros HH.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup in *.
    unfold Lub_Rbar in *.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    simpl in *.
    unfold is_lub_Rbar in *.
    unfold is_ub_Rbar in *.
    destruct i.
    destruct x; simpl; try tauto.
    specialize (H (r+1)).
    simpl in H.
    cut_to H; try lra.
    exists (const (r+1)).
    exists (rvconst _ _ _).
    exists (frfconst _).
    repeat split.
    - apply nnfconst; lra.
    - now rewrite SimpleExpectation_const.
  Qed.      

  Lemma Rbar_NonnegExpectation_const' {Ts} {dom: SigmaAlgebra Ts} (prts:ProbSpace dom)
        (c : Rbar) (nneg:Rbar_le 0 c) (nnf:Rbar_NonnegativeFunction (const (B:=Ts) c)) :
    Rbar_NonnegExpectation (const c) = c.
  Proof.
    generalize (Rbar_NonnegExpectation_pos (const c)); intros HH.
    destruct c; simpl in *; try lra.
    - eapply Rbar_NonnegExpectation_const.
      Unshelve.
      trivial.
    - apply Rbar_NonnegExpectation_const_pinfty.
  Qed.

  Lemma Rbar_NonnegExpectation_inf_mult_indicator {Ts} {dom: SigmaAlgebra Ts} (prts:ProbSpace dom)
        {P : event dom}
        (dec : dec_event P)
        {pofrf:Rbar_NonnegativeFunction (Rbar_rvmult (const p_infty) (EventIndicator dec))} :
    ps_P P <> 0 ->
    Rbar_NonnegExpectation (Rbar_rvmult (const p_infty) (EventIndicator dec)) = p_infty.
  Proof.
    intros.
    generalize (Rbar_NonnegExpectation_pos (Rbar_rvmult (const p_infty) (EventIndicator dec))); intros HH.
    unfold Rbar_NonnegExpectation, SimpleExpectationSup in *.
    unfold Lub_Rbar in *.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    simpl in *.
    unfold is_lub_Rbar in *.
    unfold is_ub_Rbar in *.
    destruct i.
    destruct x; simpl; try tauto.
    specialize (H0 (r+1)).
    simpl in H0.
    cut_to H0; try lra.
    exists (rvscale ((r+1)/(ps_P P)) (EventIndicator dec)).
    exists _.
    exists _.
    repeat split.
    - intro x.
      unfold rvscale, EventIndicator.
      match_destr; try lra.
      rewrite Rmult_1_r.
      apply Rdiv_le_0_compat; try lra.
      generalize (ps_pos P); intros.
      lra.
    - intro x.
      unfold rvscale, const, Rbar_rvmult, EventIndicator.
      match_destr.
      + rewrite Rbar_mult_1_r.
        now simpl.
      + rewrite Rbar_mult_0_r.
        rewrite Rmult_0_r.
        now simpl.
    - rewrite <- scaleSimpleExpectation.
      rewrite (SimpleExpectation_EventIndicator dec).
      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite Rinv_l; lra.
  Qed.
    
  Lemma Rbar_NonnegExpectation_pinfty_prob {Ts} {dom: SigmaAlgebra Ts} (prts:ProbSpace dom)
        rv_X
        {rv:RandomVariable dom Rbar_borel_sa rv_X}
        {pofrf:Rbar_NonnegativeFunction rv_X} :
    ps_P (exist _ _ (sa_pinf_Rbar rv_X rv)) <> 0 ->
    Rbar_NonnegExpectation rv_X = p_infty.
Proof.
  intros.
  assert (Rbar_NonnegExpectation (Rbar_rvmult rv_X
                                              (EventIndicator (classic_dec (fun x => rv_X x = p_infty)))) = p_infty).
  {
    assert (rv_eq
               (Rbar_rvmult rv_X
                            (EventIndicator (classic_dec (proj1_sig (exist _ _ (sa_pinf_Rbar rv_X rv))))))
               (Rbar_rvmult (const p_infty)
                            (EventIndicator (classic_dec (proj1_sig (exist _ _ (sa_pinf_Rbar rv_X rv))))))).
    {
      intro x.
      unfold Rbar_rvmult, EventIndicator, proj1_sig.
      match_destr.
      - now rewrite e.
      - now do 2 rewrite Rbar_mult_0_r.
    }
    erewrite (Rbar_NonnegExpectation_ext _ _ H0).
    erewrite (Rbar_NonnegExpectation_inf_mult_indicator 
                  prts
                  (classic_dec (proj1_sig (exist _ _ (sa_pinf_Rbar rv_X rv))))); trivial.
    Unshelve.
    intros ?.
    apply Rbar_rvmult_nnf.
    - now unfold const; intros ?; simpl.
    - typeclasses eauto.
  }
  assert (Rbar_rv_le
             (Rbar_rvmult 
                rv_X
                (fun x : Ts =>
                   EventIndicator (classic_dec (fun x0 : Ts => rv_X x0 = p_infty)) x))
             rv_X).
  {
    intro x.
    unfold Rbar_rvmult, EventIndicator.
    match_destr.
    - rewrite Rbar_mult_1_r.
      apply Rbar_le_refl.
    - rewrite Rbar_mult_0_r.
      apply pofrf.
  }
  generalize (Rbar_NonnegExpectation_le _ _ H1); intros.
  rewrite H0 in H2.
  destruct (Rbar_NonnegExpectation rv_X); tauto.
Qed.

  
  Lemma Rbar_NonnegExpectation_scale' {Ts} {dom: SigmaAlgebra Ts} (prts:ProbSpace dom) c
        (rv_X : Ts -> Rbar)
        {rv:RandomVariable dom Rbar_borel_sa rv_X}
        {pofrf:Rbar_NonnegativeFunction rv_X}
        {pofrf2:Rbar_NonnegativeFunction (Rbar_rvmult (const c) rv_X)} :
    Rbar_le 0 c ->
    Rbar_NonnegExpectation (Rbar_rvmult (const c) rv_X) =
    Rbar_mult c (Rbar_NonnegExpectation rv_X).
  Proof.
    intros.
    destruct c; simpl in H; try lra.
    - destruct H.
      + apply (Rbar_NonnegExpectation_scale (mkposreal _ H)).
      + subst.
        rewrite Rbar_mult_0_l.
        rewrite <- Rbar_NonnegExpectation_const0.
        apply Rbar_NonnegExpectation_ext; intros ?.
        unfold const; simpl.
        unfold Rbar_rvmult.
        now rewrite Rbar_mult_0_l.
    - destruct (Rbar_eq_dec (Rbar_NonnegExpectation rv_X) 0).
      + rewrite e.
        apply (f_equal Some) in e.
        rewrite <- Rbar_Expectation_pos_pofrf in e.
        apply Rbar_Expectation_nonneg_zero_almost_zero in e; trivial.
        rewrite Rbar_mult_0_r.
        rewrite <- (Rbar_NonnegExpectation_const 0 (reflexivity _)).
        apply (Rbar_NonnegExpectation_almostR2_proper).
        * apply Rbar_rvmult_rv; typeclasses eauto.
        * typeclasses eauto.
        * revert e.
          apply almost_impl, all_almost; intros ??.
          unfold Rbar_rvmult, const in *.
          rewrite H0.
          now rewrite Rbar_mult_0_r.
      + transitivity p_infty.
        * assert (rvm:RandomVariable dom Rbar_borel_sa (Rbar_rvmult (const p_infty) rv_X)) 
            by (apply Rbar_rvmult_rv; typeclasses eauto).
          apply Rbar_NonnegExpectation_pinfty_prob with (rv0 := rvm).
          assert (pre_event_equiv
                    (fun x : Ts => Rbar_rvmult (const p_infty) rv_X x = p_infty)
                    (pre_event_complement (fun x : Ts => rv_X x = 0))).
          {
            intro x.
            unfold Rbar_rvmult, const, pre_event_complement.
            destruct (rv_X x); admit.
          }
          
          admit.
        * unfold Rbar_mult; simpl.
          generalize (Rbar_NonnegExpectation_pos rv_X); intros.
          destruct ( Rbar_NonnegExpectation rv_X ); simpl in *; rbar_prover.
          congruence.
  Admitted.

  Lemma sum_Rbar_n_rv {Ts} {dom: SigmaAlgebra Ts} 
        (Xn : nat -> Ts -> Rbar)
        (Xn_rv : forall n, RandomVariable dom Rbar_borel_sa (Xn n)) :
    forall n,
      RandomVariable dom Rbar_borel_sa (fun a : Ts => sum_Rbar_n (fun n=> Xn n a) n).
  Proof.
    unfold sum_Rbar_n.
    intros n.
    generalize 0%nat.
    induction n; intros.
    - apply rvconst.
    - apply Rbar_rvplus_rv; trivial.
Qed.     

  Lemma Rbar_NonnegExpectation_sum {Ts} {dom: SigmaAlgebra Ts} (prts:ProbSpace dom)
        (Xn : nat -> Ts -> Rbar)
        (Xn_rv : forall n, RandomVariable dom Rbar_borel_sa (Xn n))
        (Xn_pos : forall n, Rbar_NonnegativeFunction (Xn n))
        (Xlim_pos : forall n, Rbar_NonnegativeFunction (fun omega : Ts => sum_Rbar_n (fun n : nat => Xn n omega) n))
    : forall n,
    sum_Rbar_n (fun n => Rbar_NonnegExpectation (Xn n)) n =
      Rbar_NonnegExpectation (fun omega => sum_Rbar_n (fun n => (Xn n omega)) n).
  Proof.
    intros.
    unfold sum_Rbar_n.
    induction n.
    - simpl.
      erewrite <- Rbar_NonnegExpectation_const0 at 1; reflexivity.
    - symmetry.
        assert (Rbar_NonnegativeFunction
                  (fun a : Ts =>
                     Rbar_plus (list_Rbar_sum (map (fun n0 : nat => Xn n0 a) (seq 0 n)))
                               (list_Rbar_sum (map (fun n0 : nat => Xn n0 a) [(0 + n)%nat])))).
        {
          intros ?.
          apply Rbar_plus_nneg_compat; apply list_Rbar_sum_nneg_nneg; intros
          ; apply in_map_iff in H
          ; destruct H as [?[??]]; subst; apply Xn_pos.
        } 
          

      transitivity (Rbar_NonnegExpectation
                      (fun a => (Rbar_plus (list_Rbar_sum (map (fun n0 : nat => Xn n0 a) (seq 0 n)))
                                 (list_Rbar_sum (map (fun n0 : nat => Xn n0 a) [(0 + n)%nat]))))).
      + apply Rbar_NonnegExpectation_ext; intros ?.
        rewrite seq_Sn.
        rewrite map_app.
        rewrite list_Rbar_sum_nneg_plus.
        * reflexivity.
        * apply Forall_map; apply Forall_forall; intros; apply Xn_pos.
        * apply Forall_map; apply Forall_forall; intros; apply Xn_pos.
      + setoid_rewrite Rbar_NonnegExpectation_plus.
        * rewrite seq_Sn.
          rewrite map_app.
          rewrite list_Rbar_sum_nneg_plus.
          -- rewrite IHn.
             f_equal.
             simpl.
             rewrite Rbar_plus_0_r.
             apply Rbar_NonnegExpectation_ext.
             intros ?.
             now rewrite Rbar_plus_0_r.
          -- apply Forall_map; apply Forall_forall; intros; apply Rbar_NonnegExpectation_pos.
          -- apply Forall_map; apply Forall_forall; intros; apply Rbar_NonnegExpectation_pos.
        * apply sum_Rbar_n_rv; trivial.
        * simpl.
          apply Rbar_rvplus_rv; trivial.
          apply rvconst.
          Unshelve.
          simpl.
          intros ?.
          rewrite Rbar_plus_0_r.
          apply Xn_pos.
  Qed.

  Lemma Rbar_series_expectation {Ts} {dom: SigmaAlgebra Ts} (prts:ProbSpace dom)
        (Xn : nat -> Ts -> Rbar)
        (Xn_rv : forall n, RandomVariable dom Rbar_borel_sa (Xn n))
        (Xn_pos : forall n, Rbar_NonnegativeFunction (Xn n))
        (Xlim_pos : Rbar_NonnegativeFunction (fun omega : Ts => ELim_seq (sum_Rbar_n (fun n : nat => Xn n omega))))
    :
    ELim_seq
      (sum_Rbar_n
         (fun n : nat =>
            Rbar_NonnegExpectation (Xn n))) =
      Rbar_NonnegExpectation (fun omega => ELim_seq (sum_Rbar_n (fun n => (Xn n omega)))).
  Proof.
    assert (forall n, Rbar_NonnegativeFunction (fun omega : Ts => sum_Rbar_n (fun i : nat => Xn i omega) n)).
    {
      intros ??.
      apply sum_Rbar_n_nneg_nneg; intros.
      apply Xn_pos.
    } 

    transitivity (ELim_seq (fun n => Rbar_NonnegExpectation (fun omega => (sum_Rbar_n (fun i => Xn i omega) n)))).
    {
      apply ELim_seq_ext; intros.
      now apply Rbar_NonnegExpectation_sum.
    }
    rewrite monotone_convergence_Rbar_rvlim; trivial.
    - intros.
      now apply sum_Rbar_n_rv.
    - intros ??.
      apply sum_Rbar_n_pos_incr; intros.
      apply Xn_pos.
  Qed.
  
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

  Instance product_ps : ProbSpace (product_sa A B).
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
    assert (sa:sa_sigma (SigmaAlgebra:=product_sa A B) (fun '(x,y) => @pre_Ω X x /\ @pre_Ω Y y)).
    { 
      rewrite <- pre_eqq.
      apply sa_all.
    }
    apply (measure_proper (σ:=product_sa A B) (μ:=product_measure (fun x : event A => ps_P x) (ps_measure ps1) (fun x : event B => ps_P x) 
                                                                  (ps_measure ps2)) Ω (exist _ _ sa)).
    now red; simpl.
  Defined.

  Lemma product_sa_sa (a:event A) (b:event B) :
    sa_sigma (SigmaAlgebra:=product_sa A B) (fun '(x,y) => a x /\ b y).
  Proof.
    apply generated_sa_sub.
    red.
    destruct a; destruct b; simpl.
    exists x; exists x0.
    firstorder.
  Qed.

  Definition product_sa_event (a:event A) (b:event B) : event (product_sa A B)
    := exist _ _ (product_sa_sa a b).
  
  Theorem product_sa_product (a:event A) (b:event B) :
    ps_P (ProbSpace:=product_ps) (product_sa_event a b) =
      ps_P a * ps_P b.
  Proof.
    simpl.
    rewrite product_measure_product; simpl; trivial.
    apply product_measure_Hyp_ps.
  Qed.
  
End ps_product.
