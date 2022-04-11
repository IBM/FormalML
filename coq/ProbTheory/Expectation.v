Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq Coquelicot.Hierarchy.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Import NumberIso.
Require Export Almost SimpleExpectation.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section Expectation_sec.
  
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  (* should be p_infty if (is_empty (fun omega => rv_X omega > x)) *)

  Definition BoundedNonnegativeFunction
             (rv_X1 rv_X2 : Ts -> R) :=
    NonnegativeFunction rv_X2 /\ rv_le rv_X2 rv_X1.

  Definition SimpleExpectationSup 
             (E :  forall 
                 (rvx:Ts -> R)
                 (rv : RandomVariable dom borel_sa rvx)
                 (frf:FiniteRangeFunction rvx), Prop) : Rbar
    := Lub_Rbar (fun (x : R) => 
                   exists rvx rv frf, 
                     E rvx rv frf /\ (SimpleExpectation rvx) = x).
  
  Definition NonnegExpectation
             (rv_X : Ts -> R)
             {pofrf:NonnegativeFunction rv_X} :  Rbar   :=
    (SimpleExpectationSup
       (fun
           (rvx2: Ts -> R)
           (rv2 : RandomVariable dom borel_sa rvx2)
           (frf2:FiniteRangeFunction rvx2) =>
           (BoundedNonnegativeFunction rv_X rvx2))).

  Lemma frf_NonnegExpectation
        (rv_X : Ts -> R)
        {rvx_rv : RandomVariable dom borel_sa rv_X}
        {pofrf:NonnegativeFunction rv_X}
        {frf:FiniteRangeFunction rv_X} :
    NonnegExpectation rv_X = SimpleExpectation rv_X.
  Proof.
    unfold NonnegExpectation.
    unfold SimpleExpectationSup.
    unfold Lub_Rbar.
    match goal with
      [|- context [proj1_sig ?x]] => destruct x
    end; simpl.
    destruct i as [i0 i1].
    specialize (i1 (SimpleExpectation rv_X)).
    unfold is_ub_Rbar in *.
    specialize (i0 (SimpleExpectation rv_X)).
    cut_to i0.
    - cut_to i1.
      + now apply Rbar_le_antisym.
      + intros.
        destruct H as [rvx [? [? [? ?]]]].
        unfold BoundedNonnegativeFunction in H.
        destruct H.
        rewrite <- H0.
        apply SimpleExpectation_le; trivial.
    - exists rv_X.
      exists rvx_rv.
      exists frf.
      split; trivial.
      unfold BoundedNonnegativeFunction.
      split; trivial.
      intros ?; lra.
  Qed.

  Global Instance bnnf_eq_proper : Proper (rv_eq ==> rv_eq ==> iff) BoundedNonnegativeFunction.
  Proof.
    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold BoundedNonnegativeFunction.
    unfold NonnegativeFunction.
    repeat rewrite eqq1.
    rewrite eqq2.
    repeat red in eqq2.
    intuition.
    - now rewrite <- eqq2.
    - now rewrite eqq2.
  Qed.
  
  Lemma NonnegExpectation_ext 
        {rv_X1 rv_X2 : Ts -> R}
        (nnf1:NonnegativeFunction rv_X1) 
        (nnf2:NonnegativeFunction rv_X2):
    rv_eq rv_X1 rv_X2 ->
    NonnegExpectation rv_X1 = NonnegExpectation rv_X2.
  Proof.
    intros eqq.
    unfold NonnegExpectation, SimpleExpectationSup.
    apply Lub_Rbar_eqset; intros x.
    split; intros [y [ yrv [yfrf [??]]]].
    - exists y; exists yrv; exists yfrf.
      rewrite <- eqq.
      auto.
    - exists y; exists yrv; exists yfrf.
      rewrite eqq.
      auto.
  Qed.

  Lemma NonnegExpectation_re
        {rv_X1 rv_X2 : Ts -> R}
        (eqq:rv_eq rv_X1 rv_X2)
        {nnf1:NonnegativeFunction rv_X1} :
    NonnegExpectation rv_X1 = NonnegExpectation rv_X2 (pofrf:=((proj1 (NonnegativeFunction_proper _ _ eqq)) nnf1)).
  Proof.
    now apply NonnegExpectation_ext.
  Qed.

  Lemma NonnegExpectation_pf_irrel 
        {rv_X: Ts -> R}
        (nnf1 nnf2:NonnegativeFunction rv_X) :
    NonnegExpectation rv_X (pofrf:=nnf1) = NonnegExpectation rv_X (pofrf:=nnf2).
  Proof.
    apply NonnegExpectation_ext.
    reflexivity.
  Qed.

  Definition Rbar_minus' (x y : Rbar) : option Rbar :=
    Rbar_plus' x (Rbar_opp y).
  
  Definition Expectation (rv_X : Ts -> R) : option Rbar :=
    Rbar_minus' (NonnegExpectation (pos_fun_part rv_X))
                (NonnegExpectation (neg_fun_part rv_X)).
  
  Lemma pos_fun_part_pos (rv_X : Ts -> R) 
        {nnf : NonnegativeFunction rv_X} :
    rv_eq rv_X (pos_fun_part rv_X).
  Proof.
    unfold pos_fun_part.
    intro x.
    simpl.
    unfold NonnegativeFunction in nnf.
    now rewrite Rmax_left.
  Qed.

  Lemma neg_fun_part_pos (rv_X : Ts -> R) 
        {nnf : NonnegativeFunction rv_X} :
    rv_eq (const 0) (neg_fun_part rv_X).
  Proof.
    unfold neg_fun_part, const.
    intro x.
    simpl.
    specialize (nnf x).
    rewrite Rmax_right; lra.
  Qed.

  Lemma Expectation_ext {rv_X1 rv_X2 : Ts -> R} :
    rv_eq rv_X1 rv_X2 ->
    Expectation rv_X1 = Expectation rv_X2.
  Proof.
    intros eqq.
    unfold Expectation.
    f_equal.
    - apply NonnegExpectation_ext.
      intros x; simpl.
      now rewrite eqq.
    - f_equal.
      apply NonnegExpectation_ext.
      intros x; simpl.
      now rewrite eqq.
  Qed.

  Global Instance Expectation_proper : Proper (rv_eq ==> eq) Expectation.
  Proof.
    intros ???.
    now apply Expectation_ext.
  Qed.
  
  Definition rvmean (rv_X:Ts -> R) : option Rbar :=
    Expectation rv_X.

  Definition variance (rv_X : Ts -> R)  : option Rbar :=
    match rvmean rv_X with
    | Some (Finite m) => Expectation (rvsqr (rvminus rv_X (const m)))
    | _ => None
    end.

  Lemma lub_rbar_scale0 (c:posreal) (E : R -> Prop) (l:Rbar) :
    is_lub_Rbar E l -> is_lub_Rbar (fun x => E (x/c)) (Rbar_mult c l).
  Proof.
    assert (0 < c) as cpos by apply cond_pos.
    assert (0 <= c) as cnn by lra.
    unfold is_lub_Rbar, is_ub_Rbar.
    intros.
    destruct H.
    split.
    - intros.
      specialize (H (Rbar_div x c) H1).
      now apply rbar_le_scaled.
    - intros.
      specialize (H0 (Rbar_div b c)).
      cut_to H0.
      + now apply rbar_le_scaled2.
      + intros.
        specialize (H1 (c * x)).
        replace (c * x / c) with (x) in H1.
        apply rbar_le_scaled2.
        now apply H1.
        field.
        now apply Rgt_not_eq.
  Qed.
  
  Lemma lub_rbar_scale (c:posreal) (E : R -> Prop) :
    Lub_Rbar (fun x => E (x / c)) = Rbar_mult c (Lub_Rbar E).
  Proof.
    apply is_lub_Rbar_unique.
    apply lub_rbar_scale0.
    apply Lub_Rbar_correct.
  Qed.

  Global Instance rv_scale_le_proper (c:posreal) :
    Proper (rv_le ==> rv_le) (@rvscale Ts c).
  Proof.
    unfold rv_le, rvscale.
    intros x y xyle; intros ?.
    apply Rmult_le_compat_l; trivial.
    destruct c; simpl.
    lra.
  Qed.

  Lemma NonnegExpectation_scale (c: posreal) 
        (rv_X : Ts -> R)
        {pofrf:NonnegativeFunction rv_X} :
    NonnegExpectation (rvscale c rv_X) =
    Rbar_mult c (NonnegExpectation rv_X).
  Proof.
    unfold NonnegExpectation.
    unfold BoundedNonnegativeFunction.
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
        apply (Rmult_le_compat_l (/ c)) in H0.
        * rewrite <- Rmult_assoc in H0.
          rewrite Rinv_l in H0.
          -- lra.
          -- destruct c; simpl; lra.
        * destruct c; simpl.
          left.
          now apply Rinv_0_lt_compat.
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
      + now rewrite H0.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1.
        field; trivial.
        destruct c; simpl.
        lra.
  Qed.
  
  Lemma Expectation_scale_pos (c:posreal) (rv_X : Ts -> R) :
    NonnegExpectation (fun x : Ts => pos_fun_part (rvscale c rv_X) x) =
    Rbar_mult c (NonnegExpectation (pos_fun_part rv_X)).
  Proof.
    rewrite <- NonnegExpectation_scale.
    apply NonnegExpectation_ext.
    intros x.
    unfold pos_fun_part, rvscale.
    simpl.
    now rewrite scale_Rmax0.
  Qed.
  
  Lemma Expectation_scale_neg (c:posreal) (rv_X : Ts -> R) :
    NonnegExpectation (fun x : Ts => neg_fun_part (rvscale c rv_X) x) =
    Rbar_mult c (NonnegExpectation (neg_fun_part rv_X)).
  Proof.
    rewrite <- NonnegExpectation_scale.
    apply NonnegExpectation_ext.
    intros x.
    unfold neg_fun_part, rvscale.
    simpl.
    replace (-(c*rv_X x)) with (c * (-rv_X x)) by lra.
    now rewrite scale_Rmax0.
  Qed.

  Lemma Rbar_mult_pos_pinf (c : posreal):
    Rbar_mult c p_infty = p_infty.
  Proof.
    apply is_Rbar_mult_unique.
    apply (is_Rbar_mult_p_infty_pos c (cond_pos c)).
  Qed.

  Lemma Rbar_mult_pos_minf (c : posreal):
    Rbar_mult c m_infty = m_infty.
  Proof.
    apply is_Rbar_mult_unique.
    apply (is_Rbar_mult_m_infty_pos c (cond_pos c)).
  Qed.

  Lemma scale_Rbar_plus (c : posreal) (x y : Rbar) :
    Rbar_plus' (Rbar_mult c x) (Rbar_mult c y) =
    match (Rbar_plus' x y) with
    | Some x' => Some (Rbar_mult c x')
    | None => None
    end.
  Proof.
    assert (0 < c) by apply cond_pos.
    assert (0 <= c) by lra.
    match_case; intros.
    - destruct x; destruct y; simpl in H1; invcs H1.
      + simpl; f_equal.
        now rewrite <- Rmult_plus_distr_l.
      + replace (Rbar_mult c r0) with (Finite (c * r0)) by now simpl.
        unfold Rbar_plus'.
        match_case; intros.
        rewrite Rbar_mult_pos_pinf in H1.
        discriminate.
      + replace (Rbar_mult c r0) with (Finite (c * r0)) by now simpl.
        unfold Rbar_plus'.
        match_case; intros.
        rewrite Rbar_mult_pos_minf in H1.
        discriminate.
      + rewrite Rbar_mult_pos_pinf.
        replace (Rbar_mult c r0) with (Finite (c * r0)) by now simpl.
        now simpl.
      + rewrite Rbar_mult_pos_pinf; now simpl.
      + rewrite Rbar_mult_pos_minf; now simpl.
      + rewrite Rbar_mult_pos_minf; now simpl.
    - destruct x; destruct y; simpl in H1; try discriminate.
      + rewrite Rbar_mult_pos_pinf, Rbar_mult_pos_minf; now simpl.
      + rewrite Rbar_mult_pos_pinf, Rbar_mult_pos_minf; now simpl.
  Qed.

  Lemma scale_Rbar_diff (c : posreal) (x y : Rbar) :
    Rbar_plus' (Rbar_mult c x) (Rbar_opp (Rbar_mult c y)) =
    match (Rbar_plus' x (Rbar_opp y)) with
    | Some x' => Some (Rbar_mult c x')
    | None => None
    end.
  Proof.
    replace (Rbar_opp (Rbar_mult c y)) with (Rbar_mult c (Rbar_opp y)).
    - apply scale_Rbar_plus.
    - apply Rbar_mult_opp_r.
  Qed.

  Lemma Expectation_scale_posreal (c: posreal) 
        (rv_X : Ts -> R) :
    let Ex_rv := Expectation rv_X in
    let Ex_c_rv := Expectation (rvscale c rv_X) in
    Ex_c_rv = 
    match Ex_rv with
    | Some x => Some (Rbar_mult c x)
    | None => None
    end.
  Proof. 
    unfold Expectation.
    rewrite Expectation_scale_pos; trivial.
    rewrite Expectation_scale_neg; trivial.
    apply scale_Rbar_diff.
  Qed.
  
  Lemma Expectation_opp
        (rv_X : Ts -> R) :
    let Ex_rv := Expectation rv_X in
    let Ex_o_rv := Expectation (rvopp rv_X) in
    Ex_o_rv = 
    match Ex_rv with
    | Some x => Some (Rbar_opp x)
    | None => None
    end.
  Proof.
    unfold Expectation.
    rewrite NonnegExpectation_ext with (nnf2 := negative_part_nnf rv_X).
    - replace (NonnegExpectation (fun x : Ts => neg_fun_part (rvopp rv_X) x)) with
          (NonnegExpectation (fun x : Ts => pos_fun_part rv_X x)).
      + unfold Rbar_minus'.
        case_eq  (NonnegExpectation (fun x : Ts => pos_fun_part rv_X x)); intros.
        * case_eq  (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x)); intros; simpl; f_equal.
          rewrite Rbar_finite_eq; lra.
        * case_eq  (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x)); intros; simpl; f_equal.
        * case_eq  (NonnegExpectation (fun x : Ts => neg_fun_part rv_X x)); intros; simpl; f_equal.
      + symmetry.
        rewrite NonnegExpectation_ext with (nnf2 := positive_part_nnf rv_X).
        * reflexivity.
        * intro x.
          unfold neg_fun_part, rvopp, pos_fun_part, rvscale; simpl.
          now replace (- (-1 * rv_X x)) with (rv_X x) by lra.
    - intro x.
      unfold neg_fun_part, rvopp, pos_fun_part, rvscale; simpl.
      now replace (-1 * rv_X x) with (- rv_X x) by lra.
  Qed.

  Lemma lub_Rbar_witness (E : R -> Prop) (l : Rbar) (b:R):
    is_lub_Rbar E l -> Rbar_lt b l ->
    exists (x:R), E x /\ x > b.
  Proof.
    unfold is_lub_Rbar, is_ub_Rbar.
    intros.
    destruct H.
    specialize (H1 b).
    assert (~(forall x : R, E x -> x <= b)).
    - intros HH.
      specialize (H1 HH).
      apply Rbar_lt_not_le in H0.
      congruence.
    - apply not_all_ex_not in H2.
      destruct H2.
      apply imply_to_and in H2.
      destruct H2.
      exists x.
      split; trivial.
      lra.
  Qed.

  Lemma lub_rbar_inf_witness (E : R -> Prop) :
    is_lub_Rbar E p_infty -> forall (b:R), exists (x:R), E x /\ x>b.
  Proof.
    intros.
    apply (lub_Rbar_witness _ p_infty b H).
    now simpl.
  Qed.

  Lemma lub_bar_nonempty (E : R -> Prop) :
    (exists (x:R), E x) -> ~(Lub_Rbar E = m_infty).
  Proof.
    unfold Lub_Rbar.
    destruct (ex_lub_Rbar E); simpl.
    destruct i as [HH1 HH2].
    intros.
    destruct x.
    + discriminate.
    + discriminate.
    + destruct H.
      specialize (HH1 x H).
      now unfold Rbar_le in HH1.
  Qed.

  Lemma lub_rbar_sum_inf1  (E1 E2 : R -> Prop) :
    (exists (x:R), E1 x) -> Lub_Rbar E2 = p_infty ->
    Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = p_infty.
  Proof.
    intros nemptyE1 H.
    rewrite H.
    case_eq (Lub_Rbar E1); intros.
    - now simpl.
    - now simpl.
    - unfold Lub_Rbar in H0.
      destruct (ex_lub_Rbar E1); simpl in H0.
      destruct nemptyE1.
      destruct i.
      specialize (H2 x0 H1).
      rewrite H0 in H2.
      simpl in H2.
      tauto.
  Qed.

  Lemma lub_rbar_sum_inf2  (E1 E2 : R -> Prop) :
    (exists (x:R), E1 x) -> Lub_Rbar E2 = p_infty ->
    is_lub_Rbar (fun x => exists x1 x2, E1 x1 /\ E2 x2 /\ x = x1 + x2) p_infty.    
  Proof.
    intros nemptyE1 H.
    unfold is_lub_Rbar.
    split.
    - unfold is_ub_Rbar.
      intros.
      now simpl.
    - intros.
      unfold Lub_Rbar in H.
      destruct (ex_lub_Rbar E2); simpl in *.
      invcs H.
      generalize (lub_rbar_inf_witness _ i); intros.
      unfold is_lub_Rbar in i.
      destruct i.
      unfold is_ub_Rbar in *.
      destruct b.
      + destruct nemptyE1.
        specialize (H (r-x)).
        destruct H.
        specialize (H0 (x + x0)).
        cut_to H0.
        destruct H.
        simpl in H0; lra.
        exists x; exists x0.
        destruct H.
        tauto.
      + trivial.
      + destruct nemptyE1.
        specialize (H 0).
        destruct H.
        specialize (H0 (x + x0)).
        cut_to H0.
        now simpl in H0.
        exists x.
        exists x0.
        destruct H.
        tauto.
  Qed.

  Lemma lub_rbar_sum_inf3  (E1 E2 : R -> Prop) :
    (exists (x:R), E2 x) -> Lub_Rbar E1 = p_infty ->
    is_lub_Rbar (fun x => exists x1 x2, E1 x1 /\ E2 x2 /\ x = x1 + x2) p_infty.    
  Proof.
    intros nemptyE1 H.
    generalize (lub_rbar_sum_inf2 E2 E1 nemptyE1 H); intros.
    apply (is_lub_Rbar_eqset  
             (fun x : R => exists x1 x2 : R, E2 x1 /\ E1 x2 /\ x = x1 + x2)); 
      trivial; intros.
    split; intros; destruct H1; destruct H1; 
      exists x1; exists x0; rewrite Rplus_comm; tauto.
  Qed.

  Lemma lub_rbar_sum  (E1 E2 : R -> Prop) :
    (exists (x:R), E1 x) -> (exists (x:R), E2 x) ->
    Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = 
    Lub_Rbar (fun x => exists x1 x2, E1 x1 /\ E2 x2 /\ x = x1 + x2).
  Proof.
    intros nemptyE1 nemptyE2.
    symmetry.
    apply is_lub_Rbar_unique.
    split.
    - red; intros.
      destruct H as [y [z [Ey [Ez ?]]]].
      subst.
      red.
      unfold Lub_Rbar.
      destruct (ex_lub_Rbar E1); simpl.
      destruct (ex_lub_Rbar E2); simpl.
      destruct i as [HH11 HH12].
      specialize (HH11 _ Ey).
      destruct i0 as [HH21 HH22].
      specialize (HH21 _ Ez).
      red in HH11.
      red in HH21.
      destruct x; try tauto
      ; destruct x0; try tauto.
      simpl.
      lra.
    - intros.
      generalize (lub_rbar_sum_inf2 E1 E2 nemptyE1); intros.
      generalize (lub_rbar_sum_inf3 E1 E2 nemptyE2); intros.        

      generalize (lub_bar_nonempty E2 nemptyE2); intros.
      assert (Lub_Rbar E2 = p_infty -> 
              Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = p_infty).
      intros.
      apply lub_rbar_sum_inf1; trivial.        
      
      generalize (lub_bar_nonempty E1 nemptyE1); intros.
      assert (Lub_Rbar E1 = p_infty -> 
              Rbar_plus (Lub_Rbar E1) (Lub_Rbar E2) = p_infty).
      intros.
      rewrite Rbar_plus_comm.
      apply lub_rbar_sum_inf1; trivial.
      
      case_eq (Lub_Rbar E1); intros.
      + case_eq (Lub_Rbar E2); intros.
        * simpl.
          destruct b.
          -- clear H0 H1 H2 H3 H4 H5.
             unfold Lub_Rbar in *.
             destruct (ex_lub_Rbar E1) as [lubE1 ?]; simpl in *.
             destruct (ex_lub_Rbar E2) as [lubE2 ?]; simpl in *.
             invcs H6.
             generalize (lub_Rbar_witness E1 r (r - (r + r0 - r1)/2) i).
             generalize (lub_Rbar_witness E2 r0 (r0 - (r + r0 - r1)/2) i0); intros.
             assert (r + r0 > r1 -> False); intros.
             ++ cut_to H0; [|simpl; lra].
                cut_to H1; [|simpl; lra].
                destruct H0 as [x0 [H0 HH0]].
                destruct H1 as [x1 [H1 HH1]].
                unfold is_ub_Rbar in *.
                specialize (H (x0 + x1)).
                cut_to H.
                simpl in H.
                lra.
                exists x1; exists x0; rewrite Rplus_comm; tauto.
             ++ intros.
                lra.
          -- trivial.
          -- unfold is_ub_Rbar in H.
             destruct nemptyE1; destruct nemptyE2.
             specialize (H (x + x0)).
             cut_to H.
             now simpl in H.
             exists x; exists x0; tauto.
        * cut_to H0; trivial.
          unfold is_lub_Rbar in H0.
          destruct H0.
          now specialize (H8 b H).
        * congruence.
      + cut_to H1; trivial.
        unfold is_lub_Rbar in H1.
        destruct H1.
        specialize (H7 b H).
        rewrite <- H6.
        rewrite H5; trivial.
      + tauto.
  Qed.

  Lemma Expectation_witness (l: Rbar) (b : R)
        (rv_X: Ts -> R)
        {nnf:NonnegativeFunction rv_X} :
    Rbar_lt b l -> NonnegExpectation rv_X = l -> 
    exists (x:R), (exists (rvx : Ts -> R) (rv : RandomVariable dom borel_sa rvx)
                (frf : FiniteRangeFunction rvx),
                 BoundedNonnegativeFunction rv_X rvx /\ SimpleExpectation rvx = x) /\ x > b.
  Proof.
    unfold NonnegExpectation, SimpleExpectationSup.       
    unfold Lub_Rbar.
    match goal with
      [|- context [proj1_sig ?x]] => destruct x; simpl
    end.
    intros.
    invcs H0.
    apply lub_Rbar_witness with (l := l); trivial.
  Qed.

  Lemma NonnegExpectation_le 
        (rv_X1 rv_X2 : Ts -> R)
        {nnf1 : NonnegativeFunction rv_X1}
        {nnf2 : NonnegativeFunction rv_X2} :
    rv_le rv_X1 rv_X2 ->
    Rbar_le (NonnegExpectation rv_X1) (NonnegExpectation rv_X2).
  Proof.
    intros.
    unfold NonnegExpectation, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    refine (is_lub_Rbar_subset _ _ _ _ _ i0 i); intros.
    destruct H0 as [rvx [? [? [? ?]]]].
    exists rvx; exists x2; exists x3.
    split; trivial.
    unfold BoundedNonnegativeFunction in *.
    destruct H0.
    split; trivial.
    intros ?.
    specialize (H a); specialize (H2 a).
    lra.
  Qed.

  Lemma Lub_Rbar_const (c:R) :
    Lub_Rbar (fun x => x = c) = c.
  Proof.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    unfold is_lub_Rbar, is_ub_Rbar in i.
    destruct i.
    specialize (H c).
    cut_to H; trivial.
    specialize (H0 c).
    + cut_to H0.
      * apply Rbar_le_antisym; trivial.
      * intros.
        subst.
        apply Rbar_le_refl.
  Qed.

  Lemma NonnegExpectation_const (c : R) (nnc : 0 <= c) :
    (@NonnegExpectation (const c) (nnfconst _ nnc)) = c.
  Proof.
    unfold NonnegExpectation, SimpleExpectationSup.
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
      unfold BoundedNonnegativeFunction in H1.
      destruct H1.
      generalize (SimpleExpectation_le x1 (const c) H3); intros.
      rewrite H2 in H4.
      rewrite SimpleExpectation_const in H4.
      now simpl.
    - exists (const c).
      exists (rvconst _ _ c).
      exists (frfconst c).
      split; trivial; [| apply SimpleExpectation_const].
      unfold BoundedNonnegativeFunction.
      split; [ apply (nnfconst c nnc) |].
      unfold rv_le, const; intros ?.
      lra.
  Qed.
  
  Lemma NonnegExpectation_scale' c
        (rv_X : Ts -> R)
        {pofrf:NonnegativeFunction rv_X}
        {pofrf2:NonnegativeFunction (rvscale c rv_X)} :
    0 <= c ->
    NonnegExpectation (rvscale c rv_X) =
    Rbar_mult c (NonnegExpectation rv_X).
  Proof.
    intros [].
    - rewrite <- (NonnegExpectation_scale (mkposreal _ H)); simpl.
      apply NonnegExpectation_pf_irrel.
    - subst.
      rewrite Rbar_mult_0_l.
      rewrite (NonnegExpectation_ext _ (nnfconst 0 (reflexivity _))).
      + apply NonnegExpectation_const.
      + intros ?; unfold rvscale, const; lra.
  Qed.

  Lemma Expectation_scale (c: R) 
        (rv_X : Ts -> R) :
    c <> 0 ->
    let Ex_rv := Expectation rv_X in
    let Ex_c_rv := Expectation (rvscale c rv_X) in
    Ex_c_rv = 
    match Ex_rv with
    | Some x => Some (Rbar_mult c x)
    | None => None
    end.
  Proof. 
    intros.
    destruct (Rlt_dec 0 c).
    apply (Expectation_scale_posreal (mkposreal c r)).
    destruct (Rlt_dec 0 (- c)).
    - unfold Ex_c_rv.
      rewrite (@Expectation_ext _ (rvopp (rvscale (- c) rv_X))).
      + rewrite Expectation_opp.
        rewrite (Expectation_scale_posreal (mkposreal (-c) r)).
        unfold Ex_rv.
        case_eq (Expectation rv_X); intros; trivial.
        f_equal; simpl.
        rewrite <- Rbar_mult_opp_l.
        simpl.
        now replace (- - c) with (c) by lra.
      + intro x.
        unfold rvopp, rvscale.
        lra.
    - unfold Ex_c_rv, Ex_rv.
      lra.
  Qed.

  Lemma Expectation_pos_pofrf (rv_X : Ts -> R) 
        {nnf : NonnegativeFunction rv_X} :
    Expectation rv_X = Some (NonnegExpectation rv_X).
  Proof.
    unfold Expectation.
    replace (NonnegExpectation (pos_fun_part rv_X)) with (NonnegExpectation rv_X).
    - replace (NonnegExpectation (neg_fun_part rv_X)) with (Finite 0).
      + unfold Rbar_minus', Rbar_plus', Rbar_opp.
        match_destr.
        f_equal; apply Rbar_finite_eq; lra.
      + generalize (neg_fun_part_pos rv_X); intros.
        assert (0 <= 0) by lra.
        generalize (@nnfconst Ts 0 H0); intros.
        rewrite NonnegExpectation_ext with (nnf2 := H1).
        symmetry.
        apply (NonnegExpectation_const 0 H0).
        now symmetry.
    - apply NonnegExpectation_ext; trivial.
      now apply pos_fun_part_pos.
  Qed.

  Lemma Expectation_simple
        (rv_X : Ts -> R)
        {rvx_rv : RandomVariable dom borel_sa rv_X}
        {frf:FiniteRangeFunction rv_X} :
    Expectation rv_X = Some (Finite (SimpleExpectation rv_X)).
  Proof.
    unfold Expectation.
    repeat erewrite frf_NonnegExpectation.
    - simpl.
      f_equal.
      rewrite oppSimpleExpectation.
      rewrite sumSimpleExpectation; trivial.
      + f_equal.
        apply SimpleExpectation_ext.
        symmetry.
        apply rv_pos_neg_id.
  Qed.

  Lemma Expectation_const (c:R) :
    Expectation (const c) = Some (Finite c).
  Proof.
    now rewrite (Expectation_simple _ (frf:=frfconst c)), SimpleExpectation_const.
  Qed.

  Lemma z_le_z : 0 <= 0.
  Proof.
    lra.
  Qed.

  Lemma NonnegExpectation_const0 :
    (@NonnegExpectation (const 0) (nnfconst _ z_le_z)) = 0.
  Proof.
    apply NonnegExpectation_const.
  Qed.

  Lemma NonnegExpectation_pos
        (rv_X : Ts -> R)
        {nnf : NonnegativeFunction rv_X} :
    Rbar_le 0 (NonnegExpectation rv_X).
  Proof.
    rewrite <- NonnegExpectation_const0.
    apply NonnegExpectation_le; trivial.
  Qed.

  Lemma Finite_NonnegExpectation_le 
        (rv_X1 rv_X2 : Ts -> R)
        (nnf1 : NonnegativeFunction rv_X1)
        (nnf2 : NonnegativeFunction rv_X2) :
    rv_le rv_X1 rv_X2 ->
    is_finite (NonnegExpectation rv_X2) ->
    is_finite (NonnegExpectation rv_X1).
  Proof.
    intros.
    generalize (NonnegExpectation_le rv_X1 rv_X2 H); intros.
    assert (0 <= 0) by lra.
    generalize (@NonnegExpectation_le (const 0) rv_X1 (nnfconst _ H2) _); intros.
    cut_to H3.
    generalize (NonnegExpectation_const 0 H2); intros.
    rewrite H4 in H3.
    unfold is_finite in H0.
    apply (bounded_is_finite 0 (real (NonnegExpectation rv_X2))); trivial.
    now rewrite H0.
    unfold rv_le.
    now unfold NonnegativeFunction in nnf1.
  Qed.

  Lemma Expectation_abs_then_finite (rv_X:Ts->R)  
(*        {rv : RandomVariable dom borel_sa rv_X} *)
    :  match Expectation (rvabs rv_X) with
       | Some (Finite _) => True
       | _ => False
       end ->
       match Expectation rv_X with
       | Some (Finite _) => True
       | _ => False
       end.
  Proof.
    rewrite Expectation_pos_pofrf with (nnf := nnfabs _).
    unfold Expectation.
    intros HH.
    match_case_in HH
    ; [intros r eqq | intros eqq | intros eqq]
    ; rewrite eqq in HH
    ; try contradiction.

    unfold Rbar_minus', Rbar_plus'.
    assert (fin:is_finite (NonnegExpectation (rvabs rv_X)))
      by (rewrite eqq; reflexivity).

    generalize (pos_fun_part_le rv_X); intros le1.
    generalize (Finite_NonnegExpectation_le _ _ _ _ le1 fin)
    ; intros fin1.
    rewrite <- fin1.
    generalize (neg_fun_part_le rv_X); intros le2.
    generalize (Finite_NonnegExpectation_le _ _ _ _ le2 fin)
    ; intros fin2.
    rewrite <- fin2.
    simpl; trivial.
  Qed.

  Lemma pos_part_le 
        (rvp rvn : Ts -> R)
        (p : NonnegativeFunction rvp)
        (n : NonnegativeFunction rvn) :
    rv_le (fun x : Ts => pos_fun_part (rvminus rvp rvn) x) rvp.
  Proof.
    unfold rv_le, pos_fun_part, rvminus.
    intros x.
    simpl.
    unfold rvplus, rvopp, rvscale.
    unfold NonnegativeFunction in *.
    specialize (p x); specialize (n x).
    apply Rmax_lub; lra.
  Qed.

  Lemma neg_part_le 
        (rvp rvn : Ts -> R)
        (p : NonnegativeFunction rvp)
        (n : NonnegativeFunction rvn) :
    rv_le (fun x : Ts => neg_fun_part (rvminus rvp rvn) x) rvn.
  Proof.
    unfold rv_le, pos_fun_part, rvminus.
    intros x.
    simpl.
    unfold rvplus, rvopp, rvscale.
    unfold NonnegativeFunction in *.
    specialize (p x); specialize (n x).
    apply Rmax_lub; lra.
  Qed.


  Definition Rbar_ge_dec (x y : Rbar) := Rbar_le_dec y x.

  (* sequence of simple random variables monotonically converging to X>=0 *)
  Definition simple_approx (X:Ts->Rbar) (n:nat) : Ts -> R
    := fun ω : Ts =>
         let Xw := X ω in
         if Rbar_ge_dec Xw (INR n) then (INR n) else
           match find (fun start => if Rbar_ge_dec Xw (Finite start) then true else false) 
                      (rev (map (fun x => (INR x / (2^n))) 
                                (seq 0 (n*(2^n))))) with
           | Some r => r
           | None => (INR 0)
           end.

  Definition interval_dec : forall r r1 r2 :R, {r1 <= r < r2} + {~(r1 <= r < r2)}.
  Proof.
    intros.
    destruct (Rle_dec r1 r)
    ; destruct (Rlt_dec r r2)
    ; eauto 3
    ; right; lra.
  Defined.

  Lemma simple_approx_vals (X:Ts->Rbar) (n:nat) :
    forall (omega:Ts), 
      In (simple_approx X n omega)
         (map (fun x => INR x / (2^n)) (seq 0 (S (n*(2^n))))).          
  Proof.
    intros.
    unfold simple_approx.
    rewrite in_map_iff.
    match_destr.
    - exists (n * 2^n)%nat.
      split.
      + rewrite mult_INR.
        unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite pow_INR.
        rewrite INR_IZR_INZ.
        simpl.
        rewrite Rinv_r.
        * lra.
        * now apply pow_nzero.
      + apply in_seq.
        lia.
    - match_case; intros.
      + apply find_some in H.
        destruct H as [inn rge].
        match_destr_in rge.
        apply in_rev in inn.
        apply in_map_iff in inn.
        destruct inn as [x [eqq1 inn]]; subst.
        exists x.
        split; trivial.
        apply in_seq.
        apply in_seq in inn.
        lia.
      + exists 0%nat.
        split.
        * simpl.
          lra.
        * apply in_seq.
          lia.
  Qed.

  Program Instance simple_approx_frf (X:Ts->Rbar) (n:nat) : 
    FiniteRangeFunction (simple_approx X n) :=
    {frf_vals := map (fun x => INR x / (2^n)) (seq 0 (S (n*(2^n))))}.
  Next Obligation.
    apply simple_approx_vals.
  Qed.

  Lemma simple_approx_preimage_inf (X:Ts -> Rbar) (n:nat) :
    Rbar_NonnegativeFunction X ->
    forall (omega:Ts), simple_approx X n omega = INR n <-> Rbar_ge (X omega) (INR n).
  Proof.
    unfold Rbar_NonnegativeFunction; intro posX.
    intros.
    unfold simple_approx.
    match_case; intros.
    - tauto.
    - split; [| intros; now unfold Rbar_ge in H0].
      generalize (Rbar_not_le_lt _ _ n0); intros.
      match_case_in H1; intros.
      + rewrite H2 in H1.
        apply find_some in H2.
        destruct H2.
        match_case_in H3; intros.
        * invcs H1.
          unfold Rbar_ge.
          apply r0.
        * invcs H1.
          rewrite H4 in H3.
          congruence.
      + destruct (gt_dec n 0).
        * generalize (find_none _ _ H2); intros.
          specialize (H3 0).
          rewrite <- in_rev in H3.
          cut_to H3.
          specialize (posX omega).
          match_case_in H3; intros.
          -- rewrite H4 in H3.
             congruence.
          -- easy.
          -- apply in_map_iff.
             exists (0%nat).
             split.
             ++ simpl.
                lra.
             ++ apply in_seq.
                split; [lia|].
                simpl.
                generalize (pow_exp_gt 2 n); intros.
                cut_to H4.
                replace (0%nat) with (n*0)%nat at 1 by lia.
                apply mult_lt_compat_l; lia.
                lia.
        * assert (n = 0)%nat by lia.
          invcs H3.
          simpl.
          specialize (posX omega).
          match_destr.
  Qed.
  
  Lemma find_some_break {A} f (l:list A) r :
    find f l = Some r ->
    exists l1 l2, l = l1 ++ r::l2 /\ Forall (fun x => f x = false) l1.
  Proof.
    induction l; simpl; intros fs.
    - discriminate.
    - match_case_in fs; intros eqq1
      ; rewrite eqq1 in fs.
      + intros.
        exists nil, l.
        simpl.
        invcs fs.
        split; trivial.
      + destruct (IHl fs) as [l1 [l2 [eqq2 Fl]]]; subst.
        exists (a::l1), l2.
        simpl.
        split; trivial.
        constructor; trivial.
  Qed.

  Lemma simple_approx_preimage_fin0 (X:Ts -> Rbar) (n:nat) :
    Rbar_NonnegativeFunction X ->
    forall (omega:Ts) (k:nat),
      Rbar_lt (X omega) (INR n)->
      (simple_approx X n omega)*(2^n) = (INR k) <->
      Rbar_le (INR k) (Rbar_mult (X omega) (2^n)) /\
      Rbar_lt (Rbar_mult (X omega) (2^n)) (INR (S k)).
  Proof.
    unfold Rbar_NonnegativeFunction.
    intros posX.
    intros omega k.
    intros Xlt.
    unfold simple_approx.
    unfold Rbar_ge_dec.
    match_destr; [now apply Rbar_le_not_lt in r |].
    clear n0.
    assert (pos1:(n * 2 ^ n > 0)%nat).
    {
      apply NPeano.Nat.mul_pos_pos.
      - destruct n; try lia.
        simpl in Xlt.
        specialize (posX omega).
        now apply Rbar_le_not_lt in posX.
      - simpl.
        apply NPeano.Nat.Private_NZPow.pow_pos_nonneg
        ; lia.
    }
    match_case; intros.
    - destruct (find_some_break _ _ _ H) as [l1 [l2 [eqq1 Fl1]]].
      apply find_correct in H.
      simpl in H.
      match_destr_in H; clear H.
      apply (f_equal (@rev _)) in eqq1.
      rewrite rev_involutive in eqq1.
      rewrite rev_app_distr in eqq1.
      simpl in eqq1.
      apply map_app_break in eqq1.
      destruct eqq1 as [b [c [eqq2 [eqq3 eqq4]]]].
      symmetry in eqq3.
      apply map_app_break in eqq3.
      destruct eqq3 as [d [e [eqq5 [eqq6 eqq7]]]].
      subst.
      destruct e; simpl in eqq7.
      invcs eqq7.
      destruct e; simpl in eqq7; invcs eqq7.
      transitivity (n0 = k).
      + split; intros.
        * field_simplify in H.
          -- now apply INR_eq.
          -- revert H.
             now apply pow_nzero.
        * subst.
          field_simplify; trivial.
          apply pow_nzero; lra.
      + generalize (f_equal (fun x => nth (length d) x 0)%nat); intros HH.
        specialize (HH _ _ eqq2).
        rewrite seq_nth in HH.
        2: {
          apply (f_equal (@length _)) in eqq2.
          rewrite seq_length in eqq2.
          repeat rewrite app_length in eqq2.
          simpl in eqq2.
          lia.
        }
        simpl in HH.
        rewrite app_ass in HH.
        rewrite app_nth2 in HH by lia.
        rewrite NPeano.Nat.sub_diag in HH.
        simpl in HH.
        subst.
        split; intros.
        * subst.
          split.
          -- apply Rbar_le_div_l.
             apply pow2_pos.
             apply r0.
          -- apply Rbar_lt_div_r; trivial.
             ++ apply pow2_pos.
             ++ {
                 destruct c.
                 - rewrite app_nil_r in eqq2.
                   generalize (f_equal (fun x => last x 0)%nat eqq2); intros eqq0.
                   rewrite seq_last in eqq0; trivial.
                   rewrite last_app in eqq0 by congruence.
                   simpl in eqq0.
                   rewrite <- eqq0.
                   rewrite NPeano.Nat.sub_1_r.
                   rewrite Nat.succ_pred_pos by trivial.
                   rewrite mult_INR.
                   simpl.
                   unfold Rdiv.
                   rewrite Rmult_assoc.
                   rewrite pow_INR.
                   simpl.
                   rewrite Rinv_r.
                   + now rewrite Rmult_1_r.
                   + apply pow_nzero; lra.
                 - generalize (f_equal (fun x => nth (length d+1) x 0)%nat); intros HH.
                   specialize (HH _ _ eqq2).
                   {
                     rewrite seq_nth in HH.
                     - rewrite app_nth2 in HH.
                       + rewrite app_length in HH.
                         simpl in HH.
                         rewrite Nat.sub_diag in HH.
                         subst.
                         apply Internal.Forall_rev in Fl1.
                         rewrite eqq4 in Fl1.
                         invcs Fl1.
                         match_destr_in H1.
                         rewrite NPeano.Nat.add_1_r in n0.
                         rewrite Rbar_div_Rdiv.
                         now apply Rbar_not_le_lt in n0.
                       + rewrite app_length; simpl.
                         lia.
                     - apply (f_equal (@length _)) in eqq2.
                       rewrite seq_length in eqq2.
                       repeat rewrite app_length in eqq2.
                       simpl in eqq2.
                       rewrite eqq2.
                       lia.
                   }
               }
        * destruct H as [le1 lt2].
          rewrite <- Rbar_div_Rdiv in r0.
          rewrite Rbar_le_div_l in r0 ; [| apply pow2_pos].
          {
            destruct (lt_eq_lt_dec (length d) k) as [[lt1|]|lt1]; trivial
            ; elimtype False.
            - generalize (f_equal (fun x => nth k x 0)%nat); intros HH.
              specialize (HH _ _ eqq2).
              {
                rewrite seq_nth in HH.
                - rewrite app_nth2 in HH.
                  + rewrite app_length in HH.
                    simpl in HH.
                    destruct (nth_in_or_default (k - (length d + 1)) c 0%nat)
                    ; [| lia].
                    rewrite <- HH in i.
                    apply Internal.Forall_rev in Fl1.
                    rewrite eqq4 in Fl1.
                    rewrite Forall_map in Fl1.
                    rewrite Forall_forall in Fl1.
                    specialize (Fl1 _ i).
                    match_destr_in Fl1.
                    apply n0.
                    rewrite <- Rbar_div_Rdiv.
                    apply Rbar_le_div_l
                    ; [ apply pow2_pos |].
                    apply le1.
                  + rewrite app_length; simpl.
                    lia.
                - apply INR_lt.
                  rewrite <- Rbar_lt_Rlt.
                  eapply Rbar_le_lt_trans
                  ; try eapply le1.
                  apply Rbar_lt_div_r; [ apply pow2_pos |].
                  rewrite mult_INR.
                  rewrite pow_INR.
                  rewrite Rbar_div_Rdiv.
                  unfold Rdiv.
                  simpl.
                  rewrite Rmult_assoc.
                  rewrite Rinv_r.
                  + now rewrite Rmult_1_r.
                  + apply pow_nzero; lra.
              }
            - assert (le2:(S k <= length d)%nat) by lia.
              apply le_INR in le2.
              apply Rbar_le_Rle in le2.
              generalize (Rbar_lt_le_trans _ _ _ lt2 le2); intros.
              now apply Rbar_lt_not_le in H.
          }            
    - generalize (find_none _ _ H); intros HH.
      specialize (HH 0).
      cut_to HH.
      + match_destr_in HH.
        now specialize (posX omega).
      + apply -> in_rev.
        apply in_map_iff.
        exists 0%nat.
        split.
        * simpl; lra.
        * apply in_seq.
          simpl.
          split; trivial.
  Qed.

  Lemma simple_approx_preimage_fin (X:Ts -> Rbar) (n:nat) :
    Rbar_NonnegativeFunction X ->
    forall (omega:Ts), 
      Rbar_lt (X omega) (INR n) ->
      forall (k:nat),            
        simple_approx X n omega = (INR k)/2^n <->
        Rbar_le ((INR k)/2^n) (X omega) /\
        Rbar_lt (X omega) ((INR (S k))/2^n).
  Proof.
    intros.
    destruct (simple_approx_preimage_fin0 X n H omega k H0) as [HH1 HH2].
    split; intros HH.
    - cut_to HH1.
      + destruct HH1 as [le1 lt1].
        split; intros.
        * rewrite <- Rbar_div_Rdiv.
          apply  Rbar_le_div_l; [ apply pow2_pos |]; trivial.
        * rewrite <- Rbar_div_Rdiv.
          apply  Rbar_lt_div_r; [ apply pow2_pos |]; trivial.
      + rewrite HH.
        unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite Rinv_l.
        * now rewrite Rmult_1_r.
        * now apply pow_nzero.
    - cut_to HH2.
      + rewrite <- HH2.
        unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite Rinv_r.
        * now rewrite Rmult_1_r.
        * now apply pow_nzero.
      + destruct HH as [le1 lt1].
        split; intros.
        * apply  Rbar_le_div_l; [ apply pow2_pos |]; trivial.
        * apply  Rbar_lt_div_r; [ apply pow2_pos |]; trivial.
  Qed.       
  
  Lemma simple_approx_preimage_fin2 (X:Ts -> Rbar) (n:nat) :
    Rbar_NonnegativeFunction X ->
    forall (omega:Ts), 
    forall (k:nat), 
      (k < n*2^n)%nat ->
      simple_approx X n omega = (INR k)/2^n <->
      Rbar_le ((INR k)/2^n) (X omega) /\
      Rbar_lt (X omega) ((INR (S k))/2^n).
  Proof.
    unfold Rbar_NonnegativeFunction.
    intros posX.
    intros omega k.
    intros klt.
    assert (pos1:(n * 2 ^ n > 0)%nat).
    {
      apply NPeano.Nat.mul_pos_pos.
      - destruct n; try lia.
      - simpl.
        apply NPeano.Nat.Private_NZPow.pow_pos_nonneg
        ; lia.
    }
    unfold simple_approx.
    split; intros HH.
    - match_destr_in HH.
      + apply lt_INR in klt.
        rewrite mult_INR, pow_INR in klt.
        rewrite HH in klt.
        simpl in klt.
        unfold Rdiv in klt.
        rewrite Rmult_assoc in klt.
        rewrite Rinv_l in klt; [| apply pow_nzero; lra].
        lra.
      + apply Rbar_not_le_lt in n0.
        match_case_in HH; [intros x eqq1 | intros eqq1].
        * {
            rewrite eqq1 in HH.
            subst.
            rewrite <- map_rev in eqq1.
            rewrite find_over_map in eqq1.
            apply some_lift in eqq1.
            destruct eqq1 as [kk eqq1].
            apply Rmult_eq_reg_r in e.
            2: {apply Rinv_neq_0_compat.
                apply pow_nzero; lra.
            }
            apply INR_eq in e.
            subst kk.
            destruct (find_some_break _ _ _ eqq1) as [l1 [l2 [eqq2 Fl1]]].
            apply find_correct in eqq1.
            simpl in eqq1.
            match_destr_in eqq1; clear eqq1.
            split; [apply r | ].
            apply (f_equal (@rev _)) in eqq2.
            rewrite rev_involutive in eqq2.
            rewrite rev_app_distr in eqq2.
            simpl in eqq2.
            ++ {
                destruct l1.
                - rewrite app_nil_r in eqq2.
                  generalize (f_equal (fun x => last x 0%nat) eqq2); intros eqq0.
                  rewrite seq_last in eqq0; trivial.
                  rewrite last_app in eqq0 by congruence.
                  simpl in eqq0.
                  subst.
                  rewrite NPeano.Nat.sub_1_r.
                  rewrite Nat.succ_pred_pos by trivial.
                  rewrite mult_INR.
                  unfold Rdiv.
                  rewrite Rmult_assoc.
                  rewrite pow_INR.
                  simpl.
                  rewrite Rinv_r.
                  * now rewrite Rmult_1_r.
                  * apply pow_nzero; lra.
                - assert (k = length (rev l2)).
                  {
                    generalize (f_equal (fun x => nth (length (rev l2)) x 0%nat)); intros HH.
                    specialize (HH _ _ eqq2).
                    rewrite app_nth1 in HH
                    ; [| rewrite app_length; simpl; lia].
                    rewrite app_nth2 in HH by lia.
                    rewrite Nat.sub_diag in HH.
                    simpl in HH.
                    rewrite seq_nth in HH.
                    - lia.
                    - apply (f_equal (@length _)) in eqq2.
                      rewrite seq_length in eqq2.
                      repeat rewrite app_length in eqq2.
                      simpl in eqq2.
                      rewrite eqq2.
                      rewrite app_length.
                      simpl.
                      lia.
                  }
                  generalize (f_equal (fun x => nth (S k) x 0%nat)); intros HH.
                  specialize (HH _ _ eqq2).
                  rewrite seq_nth in HH.
                  + subst.
                    rewrite app_nth2 in HH
                    ; [| rewrite app_length; simpl; lia].
                    rewrite app_length in HH.
                    replace ((S (length (rev l2)) - (length (rev l2) + length [length (rev l2)])))%nat with 0%nat in HH.
                    * rewrite rev_nth in HH by (simpl; lia).
                      rewrite plus_0_l in HH.
                      rewrite HH.
                      rewrite Forall_forall in Fl1.
                      specialize (Fl1 (nth (length (n1 :: l1) - 1) (n1 :: l1) 0%nat)).
                      cut_to Fl1.
                      -- match_destr_in Fl1.
                         now apply Rbar_not_le_lt in n2.
                      -- apply nth_In.
                         simpl; lia.
                    * simpl length.
                      lia.
                  + apply (f_equal (@length _)) in eqq2.
                    rewrite seq_length in eqq2.
                    repeat rewrite app_length in eqq2.
                    simpl in eqq2.
                    rewrite eqq2.
                    rewrite app_length.
                    simpl.
                    lia.
              }
          } 
        * generalize (find_none _ _ eqq1); intros HH2.
          specialize (HH2 0).
          cut_to HH2.
          -- match_destr_in HH2.
             now specialize (posX omega).
          -- apply -> in_rev.
             apply in_map_iff.
             exists 0%nat.
             split.
             ++ simpl; lra.
             ++ apply in_seq.
                simpl.
                lia.
    - destruct HH as [le1 lt2].
      match_destr.
      + apply Rbar_le_not_lt in r.
        elim r.
        eapply Rbar_lt_le_trans; try eapply lt2.
        rewrite <- Rbar_div_Rdiv.
        apply Rbar_le_div_r.
        * apply Rinv_0_lt_compat.
          apply pow_lt; lra.
        * rewrite Rbar_div_Rdiv.
          unfold Rdiv.
          rewrite Rinv_involutive by (apply pow_nzero; lra).
          apply le_INR in klt.
          rewrite mult_INR in klt.
          rewrite pow_INR in klt.
          apply klt.
      + match_case; [intros x eqq1 | intros eqq1].
        * destruct (find_some_break _ _ _ eqq1) as [l1 [l2 [eqq2 Fl1]]].
          apply find_correct in eqq1.
          simpl in eqq1.
          match_destr_in eqq1; clear eqq1.
          apply (f_equal (@rev _)) in eqq2.
          rewrite rev_involutive in eqq2.
          rewrite rev_app_distr in eqq2.
          simpl in eqq2.
          { 
            assert (x = INR (length (rev l2)) / 2 ^ n).
            {
              generalize (f_equal (fun x => nth (length (rev l2)) x ((fun x : nat => INR x / 2 ^ n) 0%nat))); intros HH.
              specialize (HH _ _ eqq2).
              rewrite app_nth1 in HH
              ; [| rewrite app_length; simpl; lia].
              rewrite app_nth2 in HH by lia.
              rewrite Nat.sub_diag in HH.
              simpl in HH.
              rewrite (map_nth (fun x : nat => INR x / 2 ^ n) _ 0%nat) in HH.
              rewrite seq_nth in HH.
              - simpl in HH.
                auto.
              - apply (f_equal (@length _)) in eqq2.
                rewrite map_length in eqq2.
                rewrite seq_length in eqq2.
                repeat rewrite app_length in eqq2.
                simpl in eqq2.
                rewrite eqq2.
                lia.
            }
            subst.
            apply Rmult_eq_compat_r.
            f_equal.
            destruct (lt_eq_lt_dec (length (rev l2)) k) as [[lt1|]|lt1]; trivial
            ; elimtype False.
            - generalize (f_equal (fun x => nth k x ((fun x : nat => INR x / 2 ^ n) 0%nat))); intros HH.
              specialize (HH _ _ eqq2).
              {
                rewrite (map_nth (fun x : nat => INR x / 2 ^ n) _ 0%nat) in HH.
                rewrite seq_nth in HH by trivial.
                rewrite app_nth2 in HH.
                - rewrite app_length in HH.
                  simpl in HH.
                  destruct (nth_in_or_default (k - (length (rev l2) + 1)) (rev l1) (0 / 2 ^ n)).
                  + rewrite <- HH in i.
                    apply Internal.Forall_rev in Fl1.
                    rewrite Forall_forall in Fl1.
                    specialize (Fl1 _ i).
                    now match_destr_in Fl1.
                  + rewrite e in HH.
                    apply Rmult_eq_reg_r in HH.
                    2: {apply Rinv_neq_0_compat.
                        apply pow_nzero; lra.
                    }
                    replace 0 with (INR 0%nat) in HH by (simpl; trivial).
                    apply INR_eq in HH.
                    lia.
                - rewrite app_length; simpl.
                  lia.
              }
            - assert (le2:(S k <= length (rev l2))%nat) by lia.
              apply le_INR in le2.
              rewrite <- Rbar_div_Rdiv in lt2.
              apply Rbar_lt_div_r in lt2
              ; [| apply pow_lt; lra].
              rewrite <- Rbar_div_Rdiv in r.              
              apply  Rbar_le_div_l in r
              ; [| apply pow_lt; lra].
              rewrite <- Rbar_le_Rle in le2.
              generalize (Rbar_le_trans _ _ _ le2 r); intros.
              now apply Rbar_le_not_lt in H.
          }            
        * generalize (find_none _ _ eqq1); intros HH.
          specialize (HH 0).
          { cut_to HH.
            + match_destr_in HH.
              now specialize (posX omega).
            + apply -> in_rev.
              apply in_map_iff.
              exists 0%nat.
              split.
              * simpl; lra.
              * apply in_seq.
                simpl.
                split; trivial.
          } 
  Qed.
  
  Lemma simple_approx_le (X:Ts->Rbar) (posX : Rbar_NonnegativeFunction X) :
    forall n ω, Rbar_le (simple_approx X n ω) (X ω).
  Proof.
    unfold simple_approx; intros.
    match_case; intros.
    match_case; intros.
    apply find_some in H0.
    destruct H0.
    match_destr_in H1.
  Qed.

  Lemma simple_approx_exists (X:Ts -> Rbar) (n:nat) :
    forall (omega:Ts), 
    exists (k:nat), simple_approx X n omega = (INR k)/2^n.
  Proof.
    intros.
    generalize (simple_approx_vals X n omega); intros.
    apply in_map_iff in H.
    destruct H as [x [? ?]].
    exists x.
    now symmetry in H.
  Qed.

  Lemma simple_approx_pos (X:Ts->Rbar) (n:nat) (ω:Ts) :
    0 <= (simple_approx X n ω).
  Proof.
    generalize (simple_approx_exists X n ω); intros.
    destruct H.
    rewrite H.
    simpl.
    unfold Rdiv.
    apply Rmult_le_reg_r with (r:= 2^n).
    apply pow2_pos.
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    ring_simplify.
    apply pos_INR.
    apply pow2_nzero.
  Qed.

  Instance simple_approx_pofrf (X:Ts->Rbar) (n:nat) : 
    NonnegativeFunction (simple_approx X n).
  Proof.
    unfold NonnegativeFunction; intros.
    rewrite <- Rbar_le_Rle.
    apply simple_approx_pos.
  Qed.

  Lemma simple_approx_range_event (X : Ts -> Rbar) (n:nat) (r : R) :
    let rvals :=  filter (fun z => if Rle_dec z r then true else false)
                         (map (fun x : nat => INR x / 2 ^ n) (seq 0 (S (n * 2 ^ n)))) in
    pre_event_equiv (fun omega : Ts => Rbar_le (simple_approx X n omega) r)
                    (pre_list_union (map (fun z => (fun omega => simple_approx X n omega = z))
                                 rvals)).
  Proof.
    generalize (simple_approx_vals X n); intros.
    unfold pre_event_equiv; intros.
    subst rvals.
    specialize (H x).
    rewrite in_map_iff in H.
    destruct H as [k [? ?]].
    rewrite <- H.
    unfold list_union.
    split; intros.
    - exists (fun omega => simple_approx X n omega = INR k / 2^n).
      split.
      + rewrite in_map_iff.
        exists (INR k / 2^n).
        split; trivial.
        rewrite filter_In.
        split.
        * rewrite in_map_iff.
          exists k.
          tauto.
        * match_destr.
          now rewrite <- Rbar_le_Rle in n0.
      + now symmetry.
    - destruct H1 as [a [? ?]].
      rewrite in_map_iff in H1.
      destruct H1 as [x0 [? ?]].
      rewrite filter_In in H3.
      destruct H3.
      rewrite in_map_iff in H3.
      destruct H3 as [k0 [? ?]].
      rewrite <- H1 in H2.
      rewrite H2 in H.
      rewrite <- H in H4.
      match_destr_in H4.
  Qed.

  Lemma simple_approx_inf_event (X:Ts -> Rbar) (n:nat)
        (posx : Rbar_NonnegativeFunction X) :
    pre_event_equiv (pre_event_preimage (simple_approx X n) (pre_event_singleton (INR n)))
                (pre_event_preimage X (fun r => Rbar_ge r (INR n))).
  Proof.
    generalize (simple_approx_preimage_inf X n posx); intros.
    unfold pre_event_equiv, pre_event_preimage, pre_event_singleton.
    apply H.
  Qed.

  Lemma simple_approx_fin_event (X:Ts -> Rbar) (n:nat) 
        (posx : Rbar_NonnegativeFunction X) :
    forall (k : nat), 
      (k < n*2^n)%nat ->
      pre_event_equiv 
        (pre_event_preimage (simple_approx X n) (pre_event_singleton ((INR k)/2^n)))
        (pre_event_preimage X (fun z => Rbar_le ((INR k)/2^n) z /\
                                        Rbar_lt z  ((INR (S k))/2^n))).
  Proof.
    unfold pre_event_equiv, pre_event_preimage, pre_event_singleton.
    intros.
    now apply simple_approx_preimage_fin2.
  Qed.

  Lemma simple_approx_inf_measurable (X:Ts -> Rbar) (n:nat)
        (posx : Rbar_NonnegativeFunction X)
        (ranx : RandomVariable dom Rbar_borel_sa X) :
    sa_sigma (pre_event_preimage (simple_approx X n) (pre_event_singleton (INR n))).
  Proof.
    generalize (simple_approx_inf_event X n posx); intros.
    rewrite H.
    apply Rbar_sa_le_ge.
    apply Rbar_borel_sa_preimage2; intros.
    now apply rv_preimage_sa.
  Qed.

  Lemma simple_approx_fin_measurable (X:Ts -> Rbar) (n:nat)
        (posx : Rbar_NonnegativeFunction X)
        (ranx : RandomVariable dom Rbar_borel_sa X) :
    forall (k : nat), 
      (k < n*2^n)%nat ->
      sa_sigma (pre_event_preimage (simple_approx X n) (pre_event_singleton ((INR k)/2^n))).
  Proof.
    intros.
    generalize (simple_approx_fin_event X n posx k H); intros.
    rewrite H0.
    assert (pre_event_equiv 
              (fun z : Rbar => Rbar_le (INR k / 2 ^ n) z /\
                               Rbar_lt z  (INR (S k) / 2 ^ n))
              (pre_event_inter (fun z : Rbar => Rbar_ge z (INR k / 2 ^ n))
                               (fun z : Rbar => Rbar_lt z (INR (S k) / 2 ^ n)))).
    - intros x.
      unfold pre_event_inter.
      now unfold Rbar_ge.
    - rewrite H1.
      unfold pre_event_preimage.
      assert (pre_event_equiv  
                (fun omega : Ts =>
                   pre_event_inter (fun z : Rbar => Rbar_ge z (INR k / 2 ^ n) )
                                   (fun z : Rbar => Rbar_lt z (INR (S k) / 2 ^ n))
                                          (X omega))
                (pre_event_inter (fun omega => Rbar_ge (X omega) (INR k / 2^n))
                                 (fun omega => Rbar_lt (X omega) (INR (S k) / 2^n)))).
      + intros x.
        now unfold pre_event_inter.
      + rewrite H2.
        apply sa_inter.
        * apply Rbar_sa_le_ge.
          apply Rbar_borel_sa_preimage2; intros.
          now apply rv_preimage_sa.
        * apply Rbar_sa_le_lt.
          apply Rbar_borel_sa_preimage2; intros.
          now apply rv_preimage_sa.
  Qed.

  Instance simple_approx_rv (X : Ts -> Rbar)
           {posx : Rbar_NonnegativeFunction X} 
           {rvx : RandomVariable dom Rbar_borel_sa X} 
    : forall (n:nat), RandomVariable dom borel_sa (simple_approx X n).
  Proof.
    unfold RandomVariable.
    intros.
    apply borel_sa_preimage; trivial.
    intros.
    generalize (simple_approx_vals X n); intros.
    generalize (simple_approx_range_event X n r); intros.
    rewrite H0.
    apply sa_pre_list_union.
    intros.
    apply in_map_iff in H1.
    destruct H1 as [x0 [? ?]].
    subst.
    rewrite filter_In in H2.
    destruct H2.
    apply in_map_iff in H1.
    destruct H1 as [k [? ?]].
    subst.
    rewrite in_seq in H3.
    destruct H3.
    simpl in H3.
    rewrite Nat.lt_succ_r in H3.
    rewrite Nat.le_lteq in H3.
    destruct H3.
    - apply simple_approx_fin_measurable; trivial.
    - subst.
      replace (INR (n * 2 ^ n) / 2 ^ n) with (INR n).
      + apply simple_approx_inf_measurable; trivial.
      + rewrite mult_INR.
        rewrite pow_INR.
        unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite Rinv_r.
        * lra.
        * apply pow2_nzero.
  Qed.

  Lemma simple_approx_bound (X:Ts -> Rbar) (n:nat) :
    Rbar_NonnegativeFunction X ->
    forall (omega:Ts), 
      Rbar_lt (X omega) (INR n) ->
      forall (k:nat),  Rbar_le ((INR k)/2^n) (X omega) ->
                (INR k)/2^n <= simple_approx X n omega .
  Proof.
    intro posX.
    intros.
    induction k.
    - simpl.
      unfold Rdiv.
      rewrite Rmult_0_l.
      apply simple_approx_pos.
    - cut_to IHk.
      + generalize (simple_approx_preimage_fin X n posX omega H); intros.
        generalize (simple_approx_exists X n omega); intros.
        destruct H2.
        specialize (H1 k).
        destruct H1.
        apply imply_to_or in H1.
        destruct H1.
        {
        destruct IHk.
        * rewrite H2 in H4 |- *.
          unfold Rdiv in H4 |- *.
          apply Rmult_le_compat_r.
          -- left.
             apply Rinv_0_lt_compat.
             apply pow2_pos.
          -- apply Rmult_lt_reg_r in H4.
             ++ apply INR_lt in H4.
                apply le_INR.
                lia.
             ++ apply Rinv_0_lt_compat.
                apply pow2_pos.
        * congruence.
        }
        destruct H1.
        now apply Rbar_le_not_lt in H0.
      + eapply Rbar_le_trans; try eapply H0.
        rewrite S_INR.
        apply Rmult_le_compat_r.
        * left.
          apply Rinv_0_lt_compat.
          apply pow2_pos.
        * lra.
  Qed.

  Lemma simple_approx_increasing  (X:Ts->Rbar) (posX : Rbar_NonnegativeFunction X) 
        (n:nat) (ω : Ts) :
    simple_approx X n ω <= simple_approx X (S n) ω.
  Proof.
    intros.
    generalize (simple_approx_preimage_inf X n posX ω); intros.
    generalize (simple_approx_preimage_inf X (S n) posX ω); intros.
    destruct H; destruct H0.
    case (Rbar_ge_dec (X ω) (INR n)); intros.
    - specialize (H1 r).
      case (Rbar_ge_dec (X ω) (INR (S n))); intros.        
      + specialize (H2 r0).
        rewrite S_INR in H2.
        lra.
      + rewrite H1.
        apply Rbar_not_le_lt in n0.
        assert (INR n = INR (n*2^(S n))/2^(S n)).
        * rewrite mult_INR, pow_INR.
          replace (INR 2) with (2) by easy.
          field.
          apply pow2_nzero.
        * rewrite H3 in r.
          generalize (simple_approx_bound X (S n) posX ω n0 (n * 2 ^ S n) r); intros.
          lra.
    - apply Rbar_not_le_lt in n0.
      assert (Rbar_lt (X ω) (INR (S n))).
      apply Rbar_lt_trans with (y := INR n); trivial; apply lt_INR; lia.
      generalize (simple_approx_exists X n ω); intros.
      destruct H4.
      rewrite H4.
      generalize (simple_approx_le X posX n ω); intros.
      generalize (simple_approx_bound X (S n) posX ω H3); intros.
      rewrite H4 in H5.
      assert (INR x / 2^n = INR(2*x)/ 2^(S n)).
      + unfold Rdiv.
        rewrite mult_INR.
        simpl.
        field.
        apply pow2_nzero.
      + specialize (H6 (2*x)%nat).
        rewrite H7.
        apply H6.
        now rewrite H7 in H5.
  Qed.
  
  Lemma simple_approx_increasing2  (X:Ts->Rbar) (posX : Rbar_NonnegativeFunction X) 
        (k:nat) (ω : Ts) :
    forall (n:nat), simple_approx X n ω <= simple_approx X (n+k) ω.
  Proof.
    induction k.
    - intros.
      replace (n+0)%nat with (n); [| lia].
      now right.
    - intros.
      apply Rle_trans with (r2 := simple_approx X (S n) ω).
      apply simple_approx_increasing; trivial.
      specialize (IHk (S n)).
      now replace (n + S k)%nat with (S n + k)%nat by lia.
  Qed.

  Lemma Rbar_plus_lt_compat_r (a b : Rbar) (c : R) :
    Rbar_lt a b -> Rbar_lt (Rbar_plus a c) (Rbar_plus b c).
  Proof.
    intros.
    destruct a; destruct b; simpl; try tauto.
    simpl in H; lra.
  Qed.

  Lemma Rbar_minus_lt_compat_r (a b : Rbar) (c : R) :
    Rbar_lt a b -> Rbar_lt (Rbar_minus a c) (Rbar_minus b c).
  Proof.
    unfold Rbar_minus.
    now apply Rbar_plus_lt_compat_r.
  Qed.

  Lemma simple_approx_delta (X:Ts -> Rbar) (n:nat) (ω : Ts) (posX : Rbar_NonnegativeFunction X) :
    Rbar_lt (X ω) (INR n) -> Rbar_lt (Rbar_minus (X ω) (simple_approx X n ω)) (/ (2^n)).
  Proof.
    intros.
    generalize (simple_approx_preimage_fin X n posX ω H); intros.
    generalize (simple_approx_vals X n ω); intros.
    apply in_map_iff in H1.
    destruct H1 as [x [? ?]].
    symmetry in H1.
    specialize (H0 x).
    destruct H0.
    specialize (H0 H1).
    rewrite S_INR in H0.
    rewrite H1.
    destruct H0.
    replace (Finite (/ 2^n)) with (Rbar_minus ((INR x + 1) / 2^n) ((INR x) / 2^n)).
    now apply Rbar_minus_lt_compat_r.
    simpl.
    rewrite Rbar_finite_eq; lra.
  Qed.

  Lemma simple_approx_lim (X:Ts -> Rbar) (posX : Rbar_NonnegativeFunction X) (eps : posreal) :
    forall (ω : Ts), 
      is_finite (X ω) ->
      exists (n:nat), ((X ω) - (simple_approx X n ω)) <  eps.
  Proof.
    intro. intro isfin.
    assert (exists n, (2^n > Z.to_nat (up (/ eps))))%nat.
    - exists (S (Nat.log2 (Z.to_nat (up (/ eps))))).
      unfold NonnegativeFunction in posX.
      apply Nat.log2_spec.
      replace (0)%nat with (Z.to_nat (0%Z)) by apply Z2Nat.inj_0.
      apply Z2Nat.inj_lt.
      + lia.
      + apply Z.ge_le.
        apply up_nonneg.
        left.
        apply Rinv_0_lt_compat.
        apply cond_pos.
      + apply Z.gt_lt.
        apply up_pos.
        apply Rinv_0_lt_compat.
        apply cond_pos.
    - destruct H.
      exists (max x (Z.to_nat (up (X ω)))).
      generalize (simple_approx_delta X (Init.Nat.max x (Z.to_nat (up (X ω)))) ω posX); intros.
      cut_to H0.
      rewrite <- isfin in H0.
      simpl in H0.
      ring_simplify in H0.
      + apply Rlt_trans with (r2 := / 2 ^ Init.Nat.max x (Z.to_nat (up (X ω)))); trivial.
        replace (pos eps) with (/ (/ (pos eps))).
        * apply Rinv_lt_contravar.
          -- apply Rmult_lt_0_compat.
             ++ apply Rinv_0_lt_compat.
                apply cond_pos.
             ++ apply pow2_pos.
          -- apply Rlt_le_trans with (r2 := 2^x).
             ++ apply Rlt_trans with (r2 := IZR (up (/ eps))).
                ** apply archimed.
                ** apply lt_INR in H.
                   rewrite INR_up_pos in H.
                   --- replace (2^x) with (INR (2^x)); [apply H |].
                       rewrite pow_INR.
                       f_equal.
                   --- left.
                       apply Rinv_0_lt_compat.
                       apply cond_pos.
             ++ apply Rle_pow; [lra |].
                apply Max.le_max_l.
        * rewrite Rinv_involutive.
          reflexivity.
          apply Rgt_not_eq.
          apply cond_pos.
      + rewrite <- isfin; rewrite <- isfin in H0.
        simpl; simpl in H0.
        apply Rlt_le_trans with (r2 := INR (Z.to_nat (up (X  ω)))).
        * rewrite INR_up_pos.
          apply archimed.
          apply Rle_ge.
          unfold Rbar_NonnegativeFunction in posX.
          specialize (posX ω).
          now rewrite <- isfin in posX; simpl in posX.
        * apply le_INR.
          apply Max.le_max_r.
  Qed.

  Lemma simple_approx_lim_seq (X:Ts -> Rbar) (posX : Rbar_NonnegativeFunction X) :
    forall (ω : Ts), is_lim_seq(fun n => simple_approx X n ω) (X ω).
  Proof.
    intros.
    rewrite <- is_lim_seq_spec.
    unfold is_lim_seq'; intros.
    match_case; intros.
    - unfold Hierarchy.eventually; intros.
      generalize (simple_approx_lim X posX eps ω); intros.
      rewrite H in H0.
      unfold is_finite in H0.
      cut_to H0; try reflexivity.
      destruct H0.
      exists x.
      intros.
      generalize (simple_approx_le X posX n ω); intros. 
      rewrite H in H2.
      simpl in H2.
      rewrite Rabs_minus_sym.
      rewrite Rabs_right; [|lra].
      generalize (simple_approx_increasing2 X posX (n-x)%nat ω x); intros.
      replace (x + (n-x))%nat with (n) in H3 by lia.
      simpl in H0.
      lra.
    - destruct (Rle_dec 0 M).
      + exists (Z.to_nat (up M)).
        intros.
        unfold simple_approx.
        rewrite H.
        match_destr.
        * generalize (archimed M); intros.
          destruct H1.
          eapply Rlt_le_trans.
          apply H1.
          rewrite <- INR_up_pos; try lra.
          now apply le_INR.
        * match_destr.
          -- now simpl in n0.
          -- now simpl in n0.
      + assert (0 > M) by lra.
        exists (0%nat).
        intros.
        generalize (simple_approx_pos X n0); intros.
        specialize (H2 ω).
        lra.
   - unfold Rbar_NonnegativeFunction in posX.
     specialize (posX ω).
     rewrite H in posX.
     now simpl in posX.
  Qed.

  Lemma simple_NonnegExpectation
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {nnf : NonnegativeFunction rv_X} 
        {frf : FiniteRangeFunction rv_X} :
    Finite (SimpleExpectation rv_X) = NonnegExpectation rv_X.
  Proof.
    unfold NonnegExpectation.
    unfold SimpleExpectationSup.
    symmetry.
    apply is_lub_Rbar_unique.
    unfold is_lub_Rbar.
    unfold is_ub_Rbar.
    split; intros.
    - destruct H as [rvx2 [rv2 [frf2 [? ?]]]].
      unfold BoundedNonnegativeFunction in H.
      destruct H.
      simpl.
      rewrite <- H0.
      now apply SimpleExpectation_le.
    - apply H.
      unfold BoundedNonnegativeFunction.
      exists rv_X, rv, frf.
      split; now split.
  Qed.

  Lemma simple_expectation_real 
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {nnf : NonnegativeFunction rv_X} 
        {frf : FiniteRangeFunction rv_X} :
    is_finite (NonnegExpectation rv_X).
  Proof.
    rewrite <- (@simple_NonnegExpectation rv_X rv nnf frf).
    unfold is_finite.
    reflexivity.
  Qed.


  Lemma f_ge_g_le0_eq (f g : Ts -> R) :
    (pre_event_equiv (fun omega : Ts => f omega >= g omega)
                 (fun omega : Ts => (rvminus g f) omega <= 0)).
  Proof.
    intros x; unfold rvminus, rvplus, rvopp, rvscale; lra.
  Qed.
  
  Lemma sigma_f_ge_g 
        (f g : Ts -> R)
        (f_rv : RandomVariable dom borel_sa f)
        (g_rv : RandomVariable dom borel_sa g)  :
    sa_sigma (fun omega : Ts => f omega >= g omega).
  Proof.
    rewrite f_ge_g_le0_eq.
    apply minus_measurable; trivial
    ; now apply rv_measurable.
  Qed.

  Lemma monotone_convergence_Ec
        (X : Ts -> Rbar )
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : FiniteRangeFunction cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: NonnegativeFunction cphi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
    :

      (forall (n:nat), Rbar_rv_le (Xn n) X) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) (X omega) ) ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
      (forall (n:nat), sa_sigma (fun (omega:Ts) => (Xn n omega) >= cphi omega)) /\
      pre_event_equiv (pre_union_of_collection (fun n => fun (omega:Ts) => (Xn n omega) >= cphi omega)) 
                  pre_Ω.
  Proof.
    intros.
    split.
    - intros x.
      now apply sigma_f_ge_g. 
    - assert (pre_event_equiv (pre_event_union (fun (omega : Ts) => Rbar_lt (cphi omega) (X omega))
                                       (fun (omega : Ts) => cphi omega = 0))
                          pre_Ω).
      + intros x.
        unfold pre_Ω, pre_event_union.
        specialize (H0 x).
        tauto.
      + rewrite <- H2.
        intros x.
        specialize (H2 x).
        unfold pre_Ω in H2.
        split; [tauto | ].
        intros.
        unfold pre_union_of_collection; intros.
        specialize (H1 x).
        rewrite <- is_lim_seq_spec in H1.
        unfold is_lim_seq' in H1.
        specialize (H0 x).
        unfold NonnegativeFunction in posphi.
        destruct H0.
        * exists (0%nat).
          rewrite H0.
          unfold NonnegativeFunction in Xn_pos.
          specialize (Xn_pos 0%nat x).
          lra.
        * case_eq (X x); intros.
          -- rewrite H4 in H1.
             rewrite H4 in H0; simpl in H0.
             assert (0 < (r - cphi x)) by lra.
             specialize (H1 (mkposreal _ H5)).
             destruct H1.
             exists x0.
             specialize (H1 x0).
             simpl in H1.
             cut_to H1; [|lia].
             specialize (H x0 x).
             rewrite Rabs_left1 in H1; try lra.
             rewrite H4 in H; simpl in H; lra.
          -- rewrite H4 in H1.
             specialize (H1 (cphi x)).
             destruct H1.
             exists x0.
             specialize (H1 x0).
             cut_to H1; try lia.
             lra.
          -- now rewrite H4 in H0; simpl in H0.
  Qed.
  
  Lemma monotone_convergence_Ec2
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
    - assert (pre_event_equiv (pre_event_union (fun (omega : Ts) => Rbar_lt (cphi omega)  ((Rbar_rvlim Xn) omega))
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
        unfold Rbar_rvlim in H2.
        specialize (H0 x).
        destruct H0.
        * rewrite H0.
          exists (0%nat).
          apply Rle_ge, Xn_pos.
        * unfold Rbar_rvlim in H0.
          rewrite Elim_seq_fin in H0.
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

  Lemma lim_prob
        (En : nat -> event dom)
        (E : event dom) :
    (forall (n:nat), event_sub (En n) (En (S n))) ->
    event_equiv (union_of_collection En) E ->
    is_lim_seq (fun n => ps_P (En n)) (ps_P E).
  Proof.
    intros.
    apply (is_lim_seq_ext 
             (fun n => sum_f_R0' (fun j => ps_P (make_collection_disjoint En j)) (S n))).
    - intros.
      rewrite sum_f_R0'_as_fold_right.
      generalize (ps_list_disjoint_union Prts (collection_take (make_collection_disjoint En) (S n)))
      ; intros HH.
      cut_to HH.
      + rewrite fold_right_map in HH.
        rewrite ascending_make_disjoint_collection_take_union in HH by trivial.
        rewrite HH.
        unfold collection_take.
        rewrite fold_right_map.
        trivial.
      + apply collection_take_preserves_disjoint.
        apply make_collection_disjoint_disjoint.
    - apply (is_lim_seq_ext (fun n : nat => sum_f_R0 (fun j : nat => ps_P (make_collection_disjoint En j)) n)).
      + intros.
        now rewrite sum_f_R0_sum_f_R0'.
      + rewrite infinite_sum_is_lim_seq.
        rewrite infinite_sum_infinite_sum'.
        assert (event_equiv E (union_of_collection (make_collection_disjoint En))).
        * rewrite <- H0.
          apply make_collection_disjoint_union.
        * rewrite H1.
          apply ps_countable_disjoint_union.
          apply make_collection_disjoint_disjoint.
  Qed.

  Lemma lim_prob_descending
        (En : nat -> event dom)
        (E : event dom) :
    (forall (n:nat), event_sub (En (S n)) (En n)) ->
    event_equiv (inter_of_collection En) E ->
    is_lim_seq (fun n => ps_P (En n)) (ps_P E).
  Proof.
    intros.
    generalize (lim_prob (fun n => event_complement (En n)) (event_complement E)); intros.
    cut_to H1.
    - rewrite ps_complement in H1.
      setoid_rewrite ps_complement in H1.
      apply is_lim_seq_minus' with (u  := fun n => 1) (l1 := 1) in H1.
      + replace (1 - (1 - ps_P E)) with (ps_P E) in H1 by lra.
        apply is_lim_seq_ext with (v := fun n => ps_P (En n)) in H1; trivial.
        intros; lra.
      + apply is_lim_seq_const.
    - intros.
      apply event_complement_sub_proper.
      now unfold flip.
    - rewrite <- inter_of_collection_complement.
      now apply event_complement_proper.
  Qed.

  Lemma is_lim_seq_list_sum (l:list (nat->R)) (l2:list R) :
    Forall2 is_lim_seq l (map Finite l2) ->
    is_lim_seq (fun n => list_sum (map (fun x => x n) l)) (list_sum l2).
  Proof.
    intros F2.
    dependent induction F2.
    - destruct l2; simpl in x; try congruence.
      simpl.
      apply is_lim_seq_const.
    - destruct l2; simpl in x; try congruence.
      invcs x.
      specialize (IHF2 dom Prts l2 (eq_refl _)).
      simpl.
      eapply is_lim_seq_plus; eauto.
      reflexivity.
  Qed.

  Existing Instance nodup_perm.
  Existing Instance Permutation_map'.

  Lemma simpleFunEventIndicator
        (phi : Ts -> R)
        {rphi : RandomVariable dom borel_sa phi}
        (sphi : FiniteRangeFunction phi)
        {P : event dom}
        (dec:forall x, {P x} + {~ P x}) :
    SimpleExpectation (rvmult phi (EventIndicator dec)) =
    list_sum (map (fun v => v * (ps_P (event_inter
                                      (preimage_singleton phi v)
                                      P)))
                  (nodup Req_EM_T frf_vals)).
  Proof.
    unfold SimpleExpectation.
    simpl.
    transitivity (list_sum
                    (map (fun v : R => v * ps_P (preimage_singleton (rvmult phi (EventIndicator dec)) v)) (nodup Req_EM_T frf_vals))).
    - rewrite list_prod_swap.
      rewrite map_map; simpl.
      rewrite app_nil_r.
      rewrite map_app.
      repeat rewrite map_map; simpl.
      rewrite (map_ext (fun x : R => x * 0) (fun _ : R => 0))
        by (intros; lra).
      rewrite (map_ext (fun x : R => x * 1) (fun x : R => x))
        by (intros; lra).
      rewrite map_id.
      generalize frf_vals at 1.
      induction l; simpl; trivial.
      match_destr; simpl.
      rewrite IHl.
      lra.
    - f_equal.
      apply map_ext; intros.
      unfold preimage_singleton, pre_event_preimage.
      unfold event_inter, pre_event_inter.
      unfold rvmult, pre_event_singleton.
      unfold EventIndicator.
      destruct (Req_EM_T a 0).
      + subst; lra.
      + f_equal.
        apply ps_proper; intros x; simpl.
        match_destr.
        * split; intros.
          -- split; trivial.
             lra.
          -- destruct H; lra.
        * split; intros.
          -- lra.
          -- tauto.
  Qed.

  Lemma monotone_convergence_E_phi_lim
        (X : Ts -> Rbar )
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : FiniteRangeFunction cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: NonnegativeFunction cphi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
    :

      (forall (n:nat), Rbar_rv_le (Xn n) X) ->
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) (X omega)) ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
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
          unfold rv_le in H0.
          specialize (H0 n xx).
          simpl.
          lra.
        -- rewrite <- event_inter_countable_union_distr.
          assert (event_equiv (union_of_collection (fun (n : nat) => exist _ (fun (omega : Ts) => Xn n omega >= cphi omega) (sa1 n))) Ω).
          apply monotone_convergence_Ec with (X := X); trivial.
          ++ rewrite H4.
             apply event_inter_true_r.
  Qed.

  Lemma monotone_convergence_E_phi_lim2
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
          apply monotone_convergence_Ec2; trivial.
          ++ rewrite H2.
             apply event_inter_true_r.
  Qed.

  Lemma monotone_convergence0_cphi
        (X : Ts -> Rbar )
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (rvx : RandomVariable dom Rbar_borel_sa X)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : FiniteRangeFunction cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posX: Rbar_NonnegativeFunction X) 
        (posphi: NonnegativeFunction cphi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
    :

      (forall (n:nat), Rbar_rv_le (Xn n) X) ->
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ Rbar_lt (cphi omega) (X omega)) ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
      (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
      Rbar_le (NonnegExpectation cphi)
              (Lim_seq (fun n => real (NonnegExpectation (Xn n)))).
  Proof.
    intros.
    generalize (monotone_convergence_E_phi_lim X Xn cphi Xn_rv sphi phi_rv posphi Xn_pos H H0 H1 H2); intros.
    apply is_lim_seq_unique in H4.
    rewrite <- H4.
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
      cut_to H8.
      + rewrite <- H3 in H8.
        assert (is_finite (NonnegExpectation
                             (rvmult cphi
                                     (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega)))))).
        * assert (frf1:FiniteRangeFunction  (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
          {
            apply frfmult; trivial.
            apply EventIndicator_pre_frf.
          }
          rewrite <- simple_NonnegExpectation with (rv := H7) (frf := frf1).
          now unfold is_finite.
        * rewrite <- H9 in H8.
          now simpl in H8.
      + unfold rv_le; intros x.
        unfold rvmult, EventIndicator.
        destruct (Rge_dec (Xn n x) (cphi x)); [lra | ].
        unfold NonnegativeFunction in Xn_pos.
        generalize (Xn_pos n x); lra.
  Qed.

  Lemma monotone_convergence0_cphi2
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
    generalize (monotone_convergence_E_phi_lim2 Xn cphi Xn_rv sphi phi_rv posphi Xn_pos H H0); intros.
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

  Lemma monotone_convergence0_Rbar (c:R)
        (X : Ts -> Rbar )
        (Xn : nat -> Ts -> R)
        (phi : Ts -> R)

        (rvx : RandomVariable dom Rbar_borel_sa X)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : FiniteRangeFunction phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posX: Rbar_NonnegativeFunction X) 
        (posphi: NonnegativeFunction phi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
    :

      (forall (n:nat), Rbar_rv_le (Xn n) X) ->
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
      Rbar_rv_le phi X ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
      0 < c < 1 ->
      Rbar_le (Rbar_mult c (NonnegExpectation phi))
              (Lim_seq (fun n => (NonnegExpectation (Xn n)))).
  Proof.
    intros.
    pose (cphi := rvscale c phi).
    assert (NonnegativeFunction cphi).
    - unfold NonnegativeFunction, cphi, rvscale.
      unfold NonnegativeFunction in posphi.
      intros.
      destruct H4.
      apply Rmult_le_pos; trivial.
      lra.
    - generalize (monotone_convergence0_cphi X Xn cphi rvx Xn_rv 
                                             (frfscale c phi) (rvscale_rv _ c phi phi_rv) posX H5 Xn_pos).
      intros.
      cut_to H6; trivial.
      + destruct H4.
        rewrite <- (NonnegExpectation_scale (mkposreal c H4)); apply H6.
      + intros.
        unfold cphi, rvscale.
        destruct H4.
        unfold rv_le in H2.
        specialize (H2 omega).
        unfold NonnegativeFunction in posphi.
        specialize (posphi omega).
        unfold Rle in posphi.
        destruct posphi.
        * right.
          assert (c * phi omega < phi omega).
          {
            apply Rplus_lt_reg_l with (r := - (c * phi omega)).
            ring_simplify.
            replace (- c * phi omega + phi omega) with ((1-c)*phi omega) by lra.
            apply Rmult_lt_0_compat; [lra | trivial].
          }
          assert (Rbar_lt (c * phi omega) (phi omega)) by now simpl.
          eapply Rbar_lt_le_trans.
          apply H10.
          apply H2.
        * left.
          rewrite <- H8.
          lra.
  Qed.

  Lemma monotone_convergence0_Rbar2 (c:R)
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
              (Lim_seq (fun n => (NonnegExpectation (Xn n)))).
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
    - generalize (monotone_convergence0_cphi2 Xn cphi Xn_rv 
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
          {
            apply Rplus_lt_reg_l with (r := - (c * phi omega)).
            ring_simplify.
            replace (- c * phi omega + phi omega) with ((1-c)*phi omega) by lra.
            apply Rmult_lt_0_compat; [lra | trivial].
          }
          assert (Rbar_lt (c * phi omega) (phi omega)) by now simpl.
          eapply Rbar_lt_le_trans.
          apply H8.
          apply H1.
        * left.
          rewrite <- H6.
          lra.
  Qed.

  Lemma Lim_seq_NonnegExpectation_pos
        (rvxn : nat -> Ts -> R) 
        (posvn: forall n, NonnegativeFunction (rvxn n)) :
    Rbar_le 0 (Lim_seq (fun n : nat => NonnegExpectation (rvxn n))).
  Proof.
    replace (Finite 0) with (Lim_seq (fun _ => 0)) by apply Lim_seq_const.
    apply Lim_seq_le_loc.
    unfold Hierarchy.eventually.
    exists (0%nat); intros.
    generalize (NonnegExpectation_pos (rvxn n)); intros.
    case_eq (NonnegExpectation (rvxn n)); intros.
    - now rewrite H1 in H0.
    - simpl; lra.
    - simpl; lra.
  Qed.      

  Lemma Lim_seq_Expectation_m_infty
        (rvxn : nat -> Ts -> R) 
        (posvn: forall n, NonnegativeFunction (rvxn n)) :
    Lim_seq (fun n : nat => NonnegExpectation (rvxn n)) = m_infty -> False.
  Proof.
    generalize (Lim_seq_NonnegExpectation_pos rvxn posvn); intros.
    rewrite  H0 in H.
    now simpl in H.
  Qed.

  Lemma monotone_convergence00         
        (X : Ts -> Rbar )
        (Xn : nat -> Ts -> R)
        (phi : Ts -> R)

        (rvx : RandomVariable dom Rbar_borel_sa X)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : FiniteRangeFunction phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posX: Rbar_NonnegativeFunction X) 
        (posphi: NonnegativeFunction phi)
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :

    (forall (n:nat), Rbar_rv_le (Xn n) X) ->
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    Rbar_rv_le phi X ->
    (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
    Rbar_le 
      (NonnegExpectation phi)
      (Lim_seq (fun n =>  (NonnegExpectation (Xn n)))).
  Proof.
    assert (is_lim_seq (fun n => (1-/(2+INR n)) * (real (NonnegExpectation phi)))
                       (real (NonnegExpectation phi))).
    - replace (real (@NonnegExpectation phi posphi)) with 
          (1 * (real (@NonnegExpectation phi posphi))) at 1.
      + apply is_lim_seq_scal_r with (lu := Finite 1) (a := (@NonnegExpectation phi posphi)).
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
          -- apply Rplus_lt_reg_l with (r := /(2+INR n)).
             ring_simplify.
             apply Rmult_lt_reg_l with (r := (2 + INR n)).
             ++ generalize (pos_INR n); lra.
             ++ rewrite <- Rinv_r_sym.
                ** generalize (pos_INR n); lra.
                ** apply Rgt_not_eq.
                   generalize (pos_INR n); lra.
          -- generalize (monotone_convergence0_Rbar (mkposreal _ H6) X Xn phi rvx Xn_rv sphi phi_rv posX posphi Xn_pos); intros.
             cut_to H7; trivial.
             rewrite H5 in H7.
             assert (is_finite (NonnegExpectation phi)) by (now apply simple_expectation_real).
             ++ rewrite <- H8 in H7; now simpl in H7.
             ++ split; [trivial | simpl].
                apply Rplus_lt_reg_l with (r := -1).
                ring_simplify.
                apply Ropp_lt_gt_0_contravar.
                apply  Rinv_0_lt_compat.
                generalize (pos_INR n); lra.
        * assert (is_finite (NonnegExpectation phi))  by (now apply simple_expectation_real).
          rewrite <- H6.
          apply H.
        * apply is_lim_seq_const.
      + now destruct (NonnegExpectation phi).
      + now apply Lim_seq_Expectation_m_infty in H5.
  Qed.
(*
  Lemma monotone_convergence00_2
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
    - replace (real (@NonnegExpectation phi posphi)) with 
          (1 * (real (@NonnegExpectation phi posphi))) at 1.
      + apply is_lim_seq_scal_r with (lu := Finite 1) (a := (@NonnegExpectation phi posphi)).
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
          -- apply Rplus_lt_reg_l with (r := /(2+INR n)).
             ring_simplify.
             apply Rmult_lt_reg_l with (r := (2 + INR n)).
             ++ generalize (pos_INR n); lra.
             ++ rewrite <- Rinv_r_sym.
                ** generalize (pos_INR n); lra.
                ** apply Rgt_not_eq.
                   generalize (pos_INR n); lra.
          -- generalize (monotone_convergence0_Rbar2 (mkposreal _ H4) Xn phi Xn_rv sphi phi_rv posphi Xn_pos); intros.
             cut_to H5; trivial.
             rewrite H3 in H5.
             assert (is_finite (NonnegExpectation phi)) by (now apply simple_expectation_real).
             ++ rewrite <- H6 in H5; now simpl in H5.
             ++ split; [trivial | simpl].
                apply Rplus_lt_reg_l with (r := -1).
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
*)
  Lemma monotone_convergence
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (posX: NonnegativeFunction X) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    (forall (n:nat), rv_le (Xn n) X) ->
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
    Lim_seq (fun n => NonnegExpectation (Xn n)) =  (NonnegExpectation X).
  Proof.
    generalize NonnegExpectation_le; intros.
    assert (forall (n:nat), (Rbar_le (NonnegExpectation (Xn n)) (NonnegExpectation X))).
    - intros.
      apply H; trivial.
    - assert (forall (n:nat), (Rbar_le (NonnegExpectation (Xn n)) (NonnegExpectation (Xn (S n))))).
      + intros.
        apply H; trivial.
      + pose (a := (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
        generalize (Lim_seq_le_loc (fun n => NonnegExpectation (Xn n)) 
                                   (fun _ => NonnegExpectation X)); intros.
        rewrite Lim_seq_const in H6.
        assert (Rbar_le (NonnegExpectation X) (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
        * unfold NonnegExpectation at 1.
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
            apply monotone_convergence00 with (X := X); trivial.
            now apply borel_Rbar_borel.
          }
        * apply Rbar_le_antisym; trivial.
          case_eq (NonnegExpectation X); intros.
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
          ++ generalize (NonnegExpectation_pos X); intros.
             now rewrite H8 in H9.
  Qed.

  Lemma ex_monotone_convergence
        (Xn : nat -> Ts -> R)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    ex_lim_seq (fun n => NonnegExpectation (Xn n)).
  Proof.
    intros.
    apply ex_lim_seq_incr.
    intros.
    generalize (NonnegExpectation_le (Xn n) (Xn (S n)) (H n)); intros.
    rewrite <- (H0 n) in H1.
    rewrite <- (H0 (S n)) in H1.
    now simpl in H1.
 Qed.

(*
  Lemma monotone_convergence2
        (Xn : nat -> Ts -> R)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    (forall (n:nat), rv_le (Xn n) (rvlim Xn)) ->
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (NonnegExpectation (Xn n))) ->
    Lim_seq (fun n => NonnegExpectation (Xn n)) =  (NonnegExpectation (rvlim Xn)).
  Proof.
    generalize NonnegExpectation_le; intros.
    assert (forall (n:nat), (Rbar_le (NonnegExpectation (Xn n)) (NonnegExpectation (rvlim Xn)))).
    - intros.
      apply H; trivial.
    - assert (forall (n:nat), (Rbar_le (NonnegExpectation (Xn n)) (NonnegExpectation (Xn (S n))))).
      + intros.
        apply H; trivial.
      + pose (a := (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
        generalize (Lim_seq_le_loc (fun n => NonnegExpectation (Xn n)) 
                                   (fun _ => NonnegExpectation (rvlim Xn))); intros.
        rewrite Lim_seq_const in H5.
        assert (Rbar_le (NonnegExpectation (rvlim Xn)) (Lim_seq (fun n : nat => NonnegExpectation (Xn n)))).
        * unfold NonnegExpectation at 1.
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
            unfold BoundedNonnegativeFunction in H6.
            destruct H6.
            rewrite simple_NonnegExpectation with (nnf := H6); trivial.
            apply monotone_convergence00_2; trivial.
          }
        * apply Rbar_le_antisym; trivial.
          case_eq (NonnegExpectation (rvlim Xn)); intros.
          ++ rewrite H7 in H5; simpl in H5.
             apply H5.
             unfold Hierarchy.eventually.   
             exists (0%nat).
             intros.
             specialize (H (Xn n) (rvlim Xn) (Xn_pos n) (nnflim Xn Xn_pos) (H0 n)).
             rewrite <- (H2 n) in H.
             rewrite H7 in H.
             now simpl in H.
          ++ now destruct (Lim_seq (fun n : nat => NonnegExpectation (Xn n))).
          ++ generalize (NonnegExpectation_pos (rvlim Xn)); intros.
             now rewrite H7 in H8.
  Qed.
 *)
  
  Global Instance LimInf_seq_pos
         (Xn : nat -> Ts -> R)
         (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    NonnegativeFunction 
      (fun omega : Ts => (LimInf_seq (fun n : nat => Xn n omega))).
  Proof.
    unfold NonnegativeFunction.
    intros.
    generalize (LimInf_le (fun n : nat => 0) (fun n : nat => Xn n x)); intros.
    cut_to H.
    - rewrite LimInf_seq_const in H.
      destruct (LimInf_seq (fun n : nat => Xn n x)).
      + apply H.
      + simpl; lra.
      + simpl; lra.
    - exists (0%nat).
      intros.
      apply Xn_pos.
  Qed.

  Definition Fatou_Y (Xn : nat -> Ts -> R) (n:nat) :=
    fun (omega : Ts) => Inf_seq (fun (k:nat) => Xn (k+n)%nat omega).

  Lemma is_finite_Fatou_Y 
        (Xn : nat -> Ts -> R) 
        (Xn_pos : forall n, NonnegativeFunction (Xn n))
        (n : nat) :
    forall (omega:Ts), is_finite (Fatou_Y Xn n omega).
   Proof.
     intros.
     unfold Fatou_Y.
     generalize (Inf_seq_correct (fun k : nat => Xn (k + n)%nat omega)); intros.
     apply is_inf_seq_glb in H.
     unfold Rbar_is_glb in H.
     destruct H.
     unfold Rbar_is_lower_bound in *.
     apply bounded_is_finite with (a := 0) (b := (Xn (0+n)%nat omega)).
     - apply H0; intros.
       destruct H1.
       rewrite H1.
       apply Xn_pos.
     - apply H.
       now exists (0%nat).
  Qed.
   
  Instance Fatou_Y_pos
         (Xn : nat -> Ts -> R)
         (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
    forall (n:nat), NonnegativeFunction (Fatou_Y Xn n).
  Proof.
    unfold NonnegativeFunction.
    intros.
    unfold Fatou_Y.
    generalize (Inf_seq_le  (fun n : nat => 0) 
                            (fun k : nat => Finite (Xn (Init.Nat.add k n) x)))
    ; intros.
    replace  (Inf_seq (fun _ : nat => 0)) with (Finite 0) in H.
    - generalize (is_finite_Fatou_Y Xn Xn_pos n x); intros.
      rewrite <- H0 in H.
      apply H; simpl; intros.
      apply Xn_pos.
    - symmetry.
      apply is_inf_seq_unique.
      unfold is_inf_seq; intros.
      assert (0 < eps) by apply cond_pos.
      split.
      + simpl; intros; lra.
      + exists (0%nat); simpl;lra.
  Qed.

  Lemma Fatou_Y_incr_Rbar (Xn : nat -> Ts -> R) n omega :
    Rbar_le (Fatou_Y Xn n omega) (Fatou_Y Xn (S n) omega).
  Proof.
    unfold Fatou_Y.
    repeat rewrite Inf_eq_glb.
    apply Rbar_glb_subset.
    intros x [??]; subst.
    exists (S x0).
    now replace (x0 + S n)%nat with (S x0 + n)%nat by lia.
  Qed.
     
  Lemma Fatou_Y_incr (Xn : nat -> Ts -> R)
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) n omega:
    Fatou_Y Xn n omega <= Fatou_Y Xn (S n) omega.
  Proof.
    generalize (Fatou_Y_incr_Rbar Xn n omega).
    rewrite <- is_finite_Fatou_Y by trivial.
    simpl.
    now rewrite <-  is_finite_Fatou_Y by trivial.
  Qed.

    Instance Fatou_Y_meas
             (Xn : nat -> Ts -> R)
             (Xn_pos : forall n, NonnegativeFunction (Xn n))
             (Xn_rv : forall n, RealMeasurable dom (Xn n)) :
      forall (n:nat), RealMeasurable dom (Fatou_Y Xn n).
    Proof.
      intros; red.
      apply sa_ge_le.
      intros.
      assert (pre_event_equiv
              (fun omega : Ts => Inf_seq (fun k : nat => Xn (k + n)%nat omega) >= r)
              (pre_inter_of_collection (fun k:nat => (fun omega : Ts => Xn (k + n)%nat omega >= r)))).
      - unfold pre_inter_of_collection.
        intros omega.
        generalize (is_finite_Fatou_Y Xn Xn_pos n omega).
        unfold Fatou_Y.
        rewrite Inf_eq_glb.
        unfold Rbar_glb.
        match goal with
          [|- context [proj1_sig ?x]] => destruct x
        end; simpl.
        intros xisf.
        destruct r0 as [lb glb].
        split; intros HH.
        + red in lb.
          intros.
          eapply Rge_trans; try eapply HH.
          specialize (lb (Xn (n0 + n)%nat omega)).
          apply Rle_ge.
          cut_to lb; [| eauto].
          rewrite <- xisf in lb.
          simpl in lb.
          now simpl.
        + generalize (glb r); intros HH2.
          cut_to HH2.
          * rewrite <- xisf in HH2.
            apply Rle_ge.
            now simpl in HH2.
          * red; intros ? [??]; subst.
            simpl.
            apply Rge_le.
            auto.
      - rewrite H.
        apply sa_pre_countable_inter; intros.
        clear H.
        revert r.
        apply sa_le_ge.
        apply Xn_rv.
    Qed.
    
    Instance Fatou_Y_rv
         (Xn : nat -> Ts -> R)
         (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
         (Xn_pos : forall n, NonnegativeFunction (Xn n))
      :
    forall (n:nat), RandomVariable dom borel_sa (Fatou_Y Xn n).
    Proof.
      intros.
      apply measurable_rv.
      apply Fatou_Y_meas; intros; trivial.
      now apply rv_measurable.
    Qed.

  Lemma limInf_increasing
        (f : nat -> R) :
    (forall (n:nat), f n <= f (S n)) ->
    Lim_seq f = LimInf_seq f.
  Proof.
    intros.
    generalize (ex_lim_seq_incr f H); intros.
    rewrite ex_lim_LimSup_LimInf_seq in H0.
    unfold Lim_seq.
    rewrite H0.
    destruct (LimInf_seq f).
    - simpl.
      rewrite Rbar_finite_eq .
      lra.
    - now simpl.
    - now simpl.
  Qed.

  Lemma limInf_increasing2
        (f : nat -> R) :
    (forall (n:nat), f n <= f (S n)) ->
    forall (l:Rbar),
      is_lim_seq f l <-> is_LimInf_seq f l.
  Proof.
    intros.
    generalize (ex_lim_seq_incr f H); intros.
    generalize (limInf_increasing f H); intros.
    split; intros.
    now apply is_lim_LimInf_seq.
    apply Lim_seq_correct in H0.
    apply is_LimInf_seq_unique in H2.
    rewrite H2 in H1.
    now rewrite <- H1.
  Qed.

  Lemma inf_limInf
        (f : nat -> R) (n:nat) :
    Rbar_le (Inf_seq (fun k : nat => f (k + n)%nat))
            (LimInf_seq f).
  Proof.
    rewrite LimInf_SupInf_seq.
    rewrite Rbar_sup_eq_lub.
    unfold Rbar_lub.
    match goal with
      [|- context [proj1_sig ?x ]] => destruct x; simpl
    end.
    destruct r as [ub lub].
    apply ub; eauto.
  Qed.

  Lemma incr_le_strong f 
        (incr:forall (n:nat), f n <= f (S n)) a b :
    (a <= b)%nat -> f a <= f b.
  Proof.
    revert a.
    induction b; intros.
    - assert (a = 0%nat) by lia.
      subst.
      lra.
    - apply Nat.le_succ_r in H.
      destruct H.
      + eapply Rle_trans; [| eapply incr].
        auto.
      + subst.
        lra.
  Qed.

  Lemma is_LimInf_Sup_Seq (f: nat -> R) 
        (incr:forall (n:nat), f n <= f (S n)) :
    is_LimInf_seq f (Sup_seq f).
  Proof.
    intros.
    unfold Sup_seq.
    match goal with
      [|- context [proj1_sig ?x ]] => destruct x; simpl
    end.
    destruct x; simpl in *.
    - intros eps.
      split; intros.
      + exists N.
        split; try lia.
        destruct (i eps) as [HH _].
        auto.
      + destruct (i eps) as [_ [N HH]].
        exists N.
        intros.
        eapply Rlt_le_trans; try eapply HH.
        now apply incr_le_strong.
    - intros.
      destruct (i M) as [N HH].
      exists N.
      intros.
        eapply Rlt_le_trans; try eapply HH.
        now apply incr_le_strong.
    - intros.
      eauto.
  Qed.

  Lemma lim_seq_Inf_seq
        (f : nat -> R)
        (fin:forall n, is_finite (Inf_seq (fun n0 : nat => f (n0 + n)%nat)))
        (incr:forall (n:nat), 
            Inf_seq (fun k : nat => f (k + n)%nat) <=
            Inf_seq (fun k : nat => f (k + (S n))%nat)) :
    is_lim_seq
      (fun n : nat =>  Inf_seq (fun k : nat => f (k + n)%nat))
      (LimInf_seq f).
  Proof.
    generalize (ex_lim_seq_incr (fun n : nat =>  Inf_seq (fun k : nat => f (k + n)%nat)) incr); intros.
    rewrite limInf_increasing2; trivial.
    rewrite LimInf_SupInf_seq.
    rewrite (Sup_seq_ext _
    (fun m : nat => real (Inf_seq (fun n : nat => Finite (f (Init.Nat.add n m)))))).
    - now apply is_LimInf_Sup_Seq.
    - intros.
      now rewrite fin.
  Qed.

  Lemma Fatou
        (Xn : nat -> Ts -> R)
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (fin_exp : forall n, is_finite (NonnegExpectation (Xn n)))
        (isf:forall omega, is_finite (LimInf_seq (fun n : nat => Xn n omega)))

        (lim_rv : RandomVariable dom borel_sa 
                                 (fun omega => LimInf_seq (fun n => Xn n omega))) :
    Rbar_le (NonnegExpectation (fun omega => LimInf_seq (fun n => Xn n omega)))
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
              (NonnegExpectation (fun omega => LimInf_seq (fun n => Xn n omega)))).
      + apply monotone_convergence with (X:= (fun omega : Ts => LimInf_seq (fun n : nat => Xn n omega))); trivial.
        * assert (forall (n:nat), Rbar_le (NonnegExpectation (Fatou_Y Xn n))
                                          (NonnegExpectation (Xn n))); intros.
          -- now apply NonnegExpectation_le.
          -- now apply Fatou_Y_rv.
        * intros; intro x.
          generalize (inf_limInf (fun k => Xn k x) n); intros HH.
          rewrite <- isf in HH.
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
          rewrite isf.
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

  Lemma Expectation_zero_pos 
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {pofrf :NonnegativeFunction X} :
    Expectation X = Some (Finite 0) ->
    ps_P (preimage_singleton X 0) = 1.
  Proof.
    rewrite Expectation_pos_pofrf with (nnf := pofrf); intros.
    inversion H.

    generalize (simple_approx_lim_seq X pofrf); intros.
    generalize (simple_approx_rv X); intro apx_rv1.
    generalize (simple_approx_pofrf X); intro apx_nnf1.
    generalize (simple_approx_frf X); intro apx_frf1.
    generalize (simple_approx_le X pofrf); intro apx_le1.
    generalize (simple_approx_increasing X pofrf); intro apx_inc1.
    generalize (monotone_convergence X (simple_approx X) rv pofrf apx_rv1 apx_nnf1 apx_le1 apx_inc1 (fun n => simple_expectation_real (simple_approx X n)) H0); intros.

    assert (forall n:nat, NonnegExpectation (simple_approx X n) = 0).
    intros.
    generalize (NonnegExpectation_le (simple_approx X n) X (apx_le1 n)); intros.
    rewrite H1 in H3.
    generalize (NonnegExpectation_pos (simple_approx X n)); intros.
    apply Rbar_le_antisym; trivial.

    assert (forall n:nat, ps_P (preimage_singleton (simple_approx X n) 0) = 1).
    intros.
    apply SimplePosExpectation_zero_pos with (frf := apx_frf1 n); trivial.
    generalize (frf_NonnegExpectation (simple_approx X n)); intros.
    rewrite H3 in H4; symmetry in H4.
    now apply Rbar_finite_eq in H4.

    assert (forall n:nat, ps_P (event_complement (preimage_singleton (simple_approx X n) 0)) = 0).
    {
      intros.
      rewrite ps_complement.
      rewrite H4; lra.
    } 

    generalize (lim_prob (fun n => (event_complement (preimage_singleton (simple_approx X n) 0)))
                         (event_complement (preimage_singleton X 0))
               ); trivial; intros HH.
    cut_to HH; trivial.
    - apply is_lim_seq_ext with (v := (fun n => 0)) in HH.
      generalize (is_lim_seq_const 0); intros.
      apply is_lim_seq_unique in HH.    
      apply is_lim_seq_unique in H6.
      rewrite HH in H6.
      rewrite ps_complement in H6.
      apply Rbar_finite_eq in H6; lra.
      trivial.
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
        apply Rgt_not_eq.
        apply Rdichotomy in H6.
        destruct H6.
        generalize (apx_nnf1 x0 x); intros; lra.
        specialize (apx_le1 x0 x); simpl in apx_le1; lra.
      + specialize (H0 x).
        clear H H1 H2 H3 H4 H5 HH.
        apply Rdichotomy in H6.
        destruct H6.
        * specialize (pofrf x); lra.
        * apply is_lim_seq_spec in H0.
          unfold is_lim_seq' in H0.
          specialize (H0 (mkposreal _ H)).
          destruct H0.
          specialize (H0 x0).
          exists x0.
          apply Rgt_not_eq.
          cut_to H0; [|lia].
          simpl in H0.
          specialize (apx_le1 x0 x).
          rewrite <- Rabs_Ropp in H0.
          replace (Rabs (-(simple_approx X x0 x - X x))) with (X x - simple_approx X x0 x) in H0.
          lra.
          simpl in apx_le1.
          rewrite Rabs_pos_eq; lra.
  Qed.

  Lemma NonnegExpectation_simple_approx
        (rv_X1  : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {nnf1:NonnegativeFunction rv_X1} :
     Lim_seq
         (fun n : nat =>
          NonnegExpectation (simple_approx (fun x : Ts => rv_X1 x) n)) =
       NonnegExpectation rv_X1.
  Proof.
    generalize (simple_approx_lim_seq rv_X1 nnf1); intros.
    generalize (simple_approx_rv rv_X1); intro apx_rv1.
    generalize (simple_approx_pofrf rv_X1); intro apx_nnf1.
    generalize (simple_approx_frf rv_X1); intro apx_frf1.
    generalize (simple_approx_le rv_X1 nnf1); intro apx_le1.
    generalize (simple_approx_increasing rv_X1 nnf1); intro apx_inc1.
    generalize (monotone_convergence rv_X1 (simple_approx rv_X1) rv1 nnf1 apx_rv1 apx_nnf1 apx_le1 apx_inc1 (fun n => simple_expectation_real (simple_approx rv_X1 n))); intros.
    apply H0.
    apply H.
  Qed.        

  Lemma NonnegExpectation_sum 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        {nnf1:NonnegativeFunction rv_X1}
        {nnf2:NonnegativeFunction rv_X2} :     
    NonnegExpectation (rvplus rv_X1 rv_X2) =
    Rbar_plus (NonnegExpectation rv_X1) (NonnegExpectation rv_X2).
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
    
    generalize (monotone_convergence rv_X1 (simple_approx rv_X1) rv1 nnf1 apx_rv1 apx_nnf1 apx_le1 apx_inc1 (fun n => simple_expectation_real (simple_approx rv_X1 n))); intros.
    generalize (monotone_convergence rv_X2 (simple_approx rv_X2) rv2 nnf2 apx_rv2 apx_nnf2 apx_le2 apx_inc2 (fun n => simple_expectation_real (simple_approx rv_X2 n))); intros.
    cut_to H1; trivial.
    cut_to H2; trivial.
    generalize (fun n => rvplus_rv _ (simple_approx rv_X1 n) (simple_approx rv_X2 n)); intros.
    generalize (fun n => rvplus_nnf (simple_approx rv_X1 n) (simple_approx rv_X2 n)); intros.     
    generalize (fun n => simple_expectation_real (simple_approx rv_X1 n)); intros apx_fin1.
    generalize (fun n => simple_expectation_real (simple_approx rv_X2 n)); intros apx_fin2.     
    generalize (monotone_convergence (rvplus rv_X1 rv_X2) 
                                     (fun n => rvplus (simple_approx rv_X1 n)
                                                   (simple_approx rv_X2 n))
                                     (rvplus_rv _ rv_X1 rv_X2)
                                     (rvplus_nnf rv_X1 rv_X2) H3 H4); intros.
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
      simpl in apx_le1; simpl in apx_le2; lra.
    - unfold rv_le, rvplus.
      intros n x.
      specialize (apx_inc1 n x).
      specialize (apx_inc2 n x).       
      lra.
    - intros.
      apply simple_expectation_real; trivial.
      apply frfplus; trivial.
    - intros.
      unfold rvplus.
      now apply is_lim_seq_plus with (l1 := rv_X1 omega) (l2 := rv_X2 omega).
  Qed.

  Lemma Expectation_dif_pos_unique2 
        (rxp1 rxn1 rxp2 rxn2 : Ts -> R)
        (rp1 : RandomVariable dom borel_sa rxp1)
        (rn1 : RandomVariable dom borel_sa rxn1)
        (rp2 : RandomVariable dom borel_sa rxp2)
        (rn2 : RandomVariable dom borel_sa rxn2)        

        (pp1 : NonnegativeFunction rxp1)
        (pn1 : NonnegativeFunction rxn1)        
        (pp2 : NonnegativeFunction rxp2)
        (pn2 : NonnegativeFunction rxn2) :
    rv_eq (rvminus rxp1 rxn1) (rvminus rxp2 rxn2) ->
    is_finite (NonnegExpectation rxn1) ->
    is_finite (NonnegExpectation rxn2) ->    
    Rbar_minus (NonnegExpectation rxp1) (NonnegExpectation rxn1) =
    Rbar_minus (NonnegExpectation rxp2) (NonnegExpectation rxn2).
  Proof.
    intros.
    assert (rv_eq (rvplus rxp1 rxn2) (rvplus rxp2 rxn1)).
    - unfold rv_eq, pointwise_relation, rvminus, rvopp, rvplus, rvscale in *.
      intros.
      specialize (H a).
      lra.
    - generalize (NonnegExpectation_ext _ _ H2); intros.
      rewrite NonnegExpectation_sum in H3; trivial.
      rewrite NonnegExpectation_sum in H3; trivial.

      generalize (NonnegExpectation_pos rxp1); intros.
      generalize (NonnegExpectation_pos rxp2); intros.

      unfold is_finite in *.
      rewrite <- H0, <- H1 in H3; simpl in H3.
      rewrite <- H0, <- H1; simpl.

      destruct  (NonnegExpectation rxp1); destruct  (NonnegExpectation rxp2); try easy.

      + simpl in *.
        rewrite Rbar_finite_eq in H3.
        rewrite Rbar_finite_eq.
        lra.
  Qed.
  
  Lemma Expectation_dif_pos_unique 
        (rvp rvn : Ts -> R)
        (pr : RandomVariable dom borel_sa rvp)
        (nr : RandomVariable dom borel_sa rvn)        
        (p : NonnegativeFunction rvp)
        (n : NonnegativeFunction rvn) :
    is_finite (NonnegExpectation rvn) ->
    Expectation (rvminus rvp rvn) =
    Rbar_minus' (NonnegExpectation rvp)
                (NonnegExpectation rvn).
  Proof.
    intros.
    generalize (Expectation_dif_pos_unique2
                  rvp rvn 
                  (pos_fun_part (rvminus rvp rvn))
                  (neg_fun_part (rvminus rvp rvn))
                  _ _ _ _ _ _ _ _)
    ; intros.

    assert (is_finite (NonnegExpectation (fun x : Ts => neg_fun_part (rvminus rvp rvn) x))).
    - apply Finite_NonnegExpectation_le with (rv_X2 := rvn) (nnf2 := n); trivial.     
      apply neg_part_le; trivial.
    - cut_to H0; trivial.
      + unfold Expectation.
        unfold Rbar_minus'.
        unfold is_finite in H; rewrite <- H.
        unfold is_finite in H1; rewrite <- H1.
        rewrite <- H in H0.
        rewrite <- H1 in H0.
        unfold Rbar_minus in H0.

        generalize (NonnegExpectation_pos rvp); intros.
        generalize (NonnegExpectation_pos (pos_fun_part (rvminus rvp rvn))); intros.

        destruct  (NonnegExpectation rvp); destruct  (NonnegExpectation (pos_fun_part (rvminus rvp rvn))); try easy.

        * unfold Rbar_plus', Rbar_opp.
          simpl in H0.
          f_equal.
          rewrite Rbar_finite_eq.
          rewrite Rbar_finite_eq in H0.           
          simpl in *.
          lra.
      + apply rv_pos_neg_id.
  Qed.

  Lemma Expectation_sum 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} :
    
    is_finite (NonnegExpectation (neg_fun_part rv_X1)) ->
    is_finite (NonnegExpectation (neg_fun_part rv_X2)) ->    
    Expectation (rvplus rv_X1 rv_X2) =
    match Expectation rv_X1, Expectation rv_X2 with
    | Some exp1, Some exp2 => Some (Rbar_plus exp1 exp2)
    | _, _ => None
    end.
  Proof.
    intros.
    assert (eqq1:rv_eq (rvplus rv_X1 rv_X2) (rvminus (rvplus (pos_fun_part rv_X1) (pos_fun_part rv_X2)) (rvplus (neg_fun_part rv_X1) (neg_fun_part rv_X2)))).
    {
      rewrite (rv_pos_neg_id rv_X1) at 1.
      rewrite (rv_pos_neg_id rv_X2) at 1.
      intros x.
      unfold rvminus, rvplus, rvopp, rvscale.
      lra.
    }
    rewrite (Expectation_ext eqq1); clear eqq1.
    erewrite Expectation_dif_pos_unique.
    - repeat rewrite NonnegExpectation_sum by typeclasses eauto.
      unfold Expectation.
      unfold Rbar_minus'.
      generalize (NonnegExpectation_pos (pos_fun_part rv_X1)); intros.
      generalize (NonnegExpectation_pos (pos_fun_part rv_X2)); intros.      
      rewrite <- Rbar_plus_opp.
      destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X1 x))
      ; try solve[simpl; congruence].
      destruct (NonnegExpectation (fun x : Ts => neg_fun_part rv_X2 x))
      ; try solve[simpl; congruence].
      destruct (NonnegExpectation (fun x : Ts => pos_fun_part rv_X1 x)); try now simpl.
      + destruct (NonnegExpectation (fun x : Ts => pos_fun_part rv_X2 x)); try now simpl.
        simpl.
        f_equal.
        f_equal.
        lra.
      + destruct (NonnegExpectation (fun x : Ts => pos_fun_part rv_X2 x)); try now simpl.
    - typeclasses eauto.
    - typeclasses eauto.
    - rewrite NonnegExpectation_sum by typeclasses eauto.
      rewrite <- H, <- H0.
      simpl.
      reflexivity.
  Qed.

  Lemma Expectation_not_none 
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X} :
    match Expectation rv_X with
    | Some r => True
    | _ => False
    end ->
    is_finite (NonnegExpectation (pos_fun_part rv_X)) \/
    is_finite (NonnegExpectation (neg_fun_part rv_X)).
  Proof.
    match_case; intros; try tauto.
    unfold Expectation in H.
    unfold Rbar_minus', Rbar_plus' in H.
    match_case_in H; intros; rewrite H1 in H.
    - left; now simpl.
    - right.
      match_case_in H; intros; apply (f_equal Rbar_opp) in H2;
        rewrite Rbar_opp_involutive in H2.
      + rewrite H2.
        now simpl.
      + generalize (NonnegExpectation_pos (neg_fun_part rv_X)); intros.
        rewrite H2 in H3.
        now simpl in H3.
      + rewrite H2 in H.
        simpl in H.
        congruence.
    - right.
      generalize (NonnegExpectation_pos (pos_fun_part rv_X)); intros.
      rewrite H1 in H2.
      now simpl.
  Qed.

  Lemma neg_fun_opp (rv_X : Ts -> R) :
    rv_eq (fun x => nonneg ((neg_fun_part (rvopp rv_X)) x)) 
          (fun x => nonneg ((pos_fun_part rv_X) x)).
  Proof.
    intro x.
    unfold neg_fun_part, rvopp, pos_fun_part, rvscale.
    unfold FunctionsToReal.neg_fun_part_obligation_1.
    unfold FunctionsToReal.pos_fun_part_obligation_1.
    now replace (- (-1 * rv_X x)) with (rv_X x) by lra.
  Qed.

  Lemma Expectation_not_none_alt
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X} :
    match Expectation rv_X with
    | Some r => True
    | _ => False
    end ->
    is_finite (NonnegExpectation (neg_fun_part (rvopp rv_X))) \/
    is_finite (NonnegExpectation (neg_fun_part rv_X)).
  Proof.
    intros.
    generalize (Expectation_not_none _ H); intros.
    destruct H0.
    - left.
      generalize (neg_fun_opp rv_X); intros.
      now rewrite (NonnegExpectation_ext _ _ H1).
    - now right.
  Qed.

  Lemma Finite_Rbar_plus' (a b : Rbar) :
    forall (c:R),
      Rbar_plus' a b = Some (Finite c) ->
      is_finite a /\ is_finite b.
  Proof.
    intros.
    unfold Rbar_plus' in H.
    match_destr_in H; match_destr_in H.
    unfold is_finite.
    now rewrite Rbar_finite_eq.
  Qed.

  Lemma Finite_Rbar_opp (a : Rbar) :
    is_finite (Rbar_opp a) <-> is_finite a.
  Proof.
    unfold is_finite, Rbar_opp.
    split; match_destr.
  Qed.

  Lemma Finite_Rbar_minus' (a b : Rbar) :
    forall (c:R),
      Rbar_minus' a b = Some (Finite c) ->
      is_finite a /\ is_finite b.
  Proof.
    unfold Rbar_minus'.
    generalize (Finite_Rbar_plus' a (Rbar_opp b)); intros.
    specialize (H c H0).
    generalize (Finite_Rbar_opp b); intros.
    destruct H.
    rewrite <- H1.
    tauto.
  Qed.

  Lemma rvopp_opp (f : Ts -> R) :
    rv_eq (rvopp (rvopp f)) f.
  Proof.
    intro x.
    rv_unfold.
    lra.
  Qed.

  Lemma Expectation_sum_isfin_fun2
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} :
    forall (c:R), 
      Expectation rv_X2 = Some (Finite c) ->
      match Expectation rv_X1 with
      | Some exp1 => Expectation (rvplus rv_X1 rv_X2) = Some (Rbar_plus exp1 c)
      | _ => True
      end.
  Proof.
    intros.
    generalize (Expectation_not_none_alt rv_X1); intros.
    generalize (Finite_Rbar_minus' _ _ _ H); intro finparts.
    match_case; intros.
    rewrite H1 in H0.
    cut_to H0; trivial.
    destruct H0.
    - generalize (Expectation_sum (rvopp rv_X1) (rvopp rv_X2) H0); intros.
      cut_to H2.
      + assert (rv_eq (rvplus (rvopp rv_X1) (rvopp rv_X2))
                      (rvopp (rvplus rv_X1 rv_X2))) by (intro x; rv_unfold; lra).
        rewrite (Expectation_ext H3) in H2.
        generalize (Expectation_opp (rvopp (rvplus rv_X1 rv_X2))); intros.
        simpl in H4.
        generalize (Expectation_opp rv_X1); intros.
        rewrite H1 in H5; simpl in H5.
        generalize (Expectation_opp rv_X2); intros.
        rewrite H in H6; simpl in H6.
        rewrite H5, H6 in H2.
        generalize (rvopp_opp (rvplus rv_X1 rv_X2)); intros.
        rewrite (Expectation_ext H7) in H4.
        rewrite H2 in H4.
        rewrite <- Rbar_plus_opp in H4.
        rewrite Rbar_opp_involutive in H4.
        simpl in H4.
        now rewrite Ropp_involutive in H4.
      + generalize (Expectation_opp rv_X2); intros.
        rewrite H in H3; simpl in H3.
        generalize (Finite_Rbar_minus' _ _ _ H3); intros. 
        tauto.
    - destruct finparts.
      generalize (Expectation_sum rv_X1 rv_X2 H0 H3); intros.
      now rewrite H1, H in H4.
  Qed.

  Lemma Expectation_sum_finite 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} :
    forall (e1 e2:R), 
      Expectation rv_X1 = Some (Finite e1) ->
      Expectation rv_X2 = Some (Finite e2) ->
      Expectation (rvplus rv_X1 rv_X2) = Some (Finite (e1 + e2)).
  Proof.
    intros.
    generalize (Expectation_sum rv_X1 rv_X2); intros.
    rewrite H, H0 in H1.
    unfold Expectation in H.
    apply Finite_Rbar_minus' in H.
    unfold Expectation in H0.
    apply Finite_Rbar_minus' in H0.    
    destruct H; destruct H0.
    specialize (H1 H2 H3).
    rewrite H1.
    now simpl.
  Qed.

  Lemma Expectation_le 
        (rv_X1 rv_X2 : Ts -> R) :
    forall (e1 e2 : Rbar),
      Expectation rv_X1 = Some e1 ->
      Expectation rv_X2 = Some e2 ->
      rv_le rv_X1 rv_X2 ->
      Rbar_le e1 e2.
  Proof.
    unfold Expectation, rv_le; intros.
    assert (rv_le (pos_fun_part rv_X1) (pos_fun_part rv_X2)).
    - unfold rv_le, pos_fun_part.
      intros ?; simpl.
      now apply Rle_max_compat_r.
    - assert (rv_le (neg_fun_part rv_X2) (neg_fun_part rv_X1)).
      + unfold rv_le, neg_fun_part.
        intros x; simpl.
        apply Rle_max_compat_r.
        specialize (H1 x).
        lra.
      + apply NonnegExpectation_le with (nnf1 := positive_part_nnf rv_X1) 
                                        (nnf2 := positive_part_nnf rv_X2) in H2.
        apply NonnegExpectation_le with (nnf1 := negative_part_nnf rv_X2) 
                                        (nnf2 := negative_part_nnf rv_X1) in H3.
        apply Rbar_opp_le in H3.
        unfold Rbar_minus' in *.
        generalize (Rbar_plus_le_compat _ _ _ _ H2 H3).
        apply is_Rbar_plus_unique in H.
        apply is_Rbar_plus_unique in H0.
        rewrite H.
        now rewrite H0.
  Qed.
 
  Lemma Markov_ineq
        (X : Ts -> R)
        (rv : RandomVariable dom borel_sa X)
        (pofrf : NonnegativeFunction X)
        (a : posreal) :
    Rbar_le (a * (ps_P (event_ge dom X a))) (NonnegExpectation X).
  Proof.
    generalize (SimpleExpectation_pre_EventIndicator (sa_le_ge_rv dom X a) (fun x => Rge_dec (X x) a)); intros.
    unfold event_ge.
    rewrite <- H.
    generalize simple_NonnegExpectation; intros.
    rewrite scaleSimpleExpectation.
    erewrite H0.
    apply NonnegExpectation_le.
    unfold EventIndicator, rvscale; intros x.
    specialize (pofrf x).
    destruct (Rge_dec (X x) a); lra.
  Qed.    
      
  Lemma Markov_ineq_div 
        (X : Ts -> R)
        (rv : RandomVariable dom borel_sa X)
        (pofrf : NonnegativeFunction X)
        (a : posreal) :
    Rbar_le (ps_P (event_ge dom X a)) (Rbar_div_pos (NonnegExpectation X) a).
  Proof.
    generalize (Markov_ineq X rv pofrf a); intros.
    rewrite Rbar_div_pos_le with (z := a) in H.
    rewrite Rmult_comm in H.
    unfold Rbar_div_pos at 1 in H.
    unfold Rdiv in H.
    rewrite Rmult_assoc in H.
    rewrite <- Rinv_r_sym in H; [| apply Rgt_not_eq, cond_pos].
    now rewrite Rmult_1_r in H.
  Qed.

  Lemma rsqr_pos (a : posreal) : (0 < Rsqr a).
  Proof.
    apply Rlt_0_sqr.
    apply Rgt_not_eq.
    apply cond_pos.
  Qed.

  Lemma Rabs_Rsqr_ge (x : R) (a : posreal) :
    Rabs x >= a <-> Rsqr x >= Rsqr a.
  Proof.
    replace (pos a) with (Rabs a) at 1 by (apply Rabs_right; left; apply cond_pos).
    simpl.
    split; intros; apply Rle_ge; apply Rge_le in H.
    - now apply Rsqr_le_abs_1.
    - now apply Rsqr_le_abs_0.
  Qed.

  Lemma Chebyshev_ineq_div_mean0
        (X : Ts -> R)
        (rv : RandomVariable dom borel_sa X)
        (a : posreal) :
    Rbar_le (ps_P (event_ge dom (rvabs X) a))
            (Rbar_div_pos
               (NonnegExpectation (rvsqr X))
               (mkposreal _ (rsqr_pos a))).
  Proof.
    assert (event_equiv
              (event_ge dom (rvabs X) a)
              (event_ge dom (rvsqr X)
               {| pos := a²; cond_pos := rsqr_pos a |})).
    {
      intro x.
      unfold proj1_sig; simpl.
      unfold rvabs, const, rvsqr.
      now rewrite Rabs_Rsqr_ge.
    }
    rewrite H.
    apply Markov_ineq_div.
  Qed.

  Lemma Chebyshev_ineq_div_mean
        (X : Ts -> R)
        (rv : RandomVariable dom borel_sa X)
        (mean : R)
        (a : posreal) :
    Rbar_le (ps_P (event_ge dom (rvabs (rvminus X (const mean))) a))
            (Rbar_div_pos
               (NonnegExpectation (rvsqr (rvminus X (const mean))))
               (mkposreal _ (rsqr_pos a))).
  Proof.
    apply Chebyshev_ineq_div_mean0.
  Qed.

  Lemma Chebyshev_ineq_div
        (X : Ts -> R)
        (rv : RandomVariable dom borel_sa X)
        (a : posreal) :
    match (Expectation X) with
      | Some (Finite mean) => 
        Rbar_le (ps_P (event_ge dom (rvabs (rvminus X (const mean))) a))
                (Rbar_div_pos
                   (NonnegExpectation (rvsqr (rvminus X (const mean))))
                   (mkposreal _ (rsqr_pos a)))
      | _ => True
    end.
  Proof.
    case_eq (Expectation X); intros; trivial.
    match_destr.
    apply Chebyshev_ineq_div_mean.
  Qed.

  Lemma Expectation_sqr (rv_X :Ts->R)  :
    Expectation (rvsqr rv_X) = Some (NonnegExpectation (rvsqr rv_X)).
  Proof.
    apply Expectation_pos_pofrf.
  Qed.

End Expectation_sec.

Section almost_sec.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).
  
  Instance pos_fun_part_proper_almostR2 : Proper (almostR2 prts eq ==> almostR2 prts eq) 
                                            (fun x x0 => nonneg (pos_fun_part x x0)).
  Proof.
    intros x1 x2 eqq1.
    apply (almostR2_sub prts eq (fun x x0 => nonneg (pos_fun_part x x0))); trivial.
    intros.
    unfold pos_fun_part; simpl.
    now rewrite H.
  Qed.

  Instance neg_fun_part_proper_almostR2 : Proper (almostR2 prts eq ==> almostR2 prts eq) 
                                            (fun x x0 => nonneg (neg_fun_part x x0)).
  Proof.
    intros x1 x2 eqq1.
    apply (almostR2_sub prts eq (fun x x0 => nonneg (neg_fun_part x x0))); trivial.
    intros.
    unfold neg_fun_part; simpl.
    now rewrite H.
  Qed.

  Lemma NonnegExpectation_almostR2_0 x 
        {nnf:NonnegativeFunction x} :
    almostR2 prts eq x (const 0) ->
    NonnegExpectation x = 0.
  Proof.
    intros.
    unfold NonnegExpectation, SimpleExpectationSup.
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

    Lemma NonnegExpectation_EventIndicator_as x {P} (dec:dec_event P)
        {xrv:RandomVariable dom borel_sa x}                 
        {xnnf:NonnegativeFunction x}
    :
      ps_P P = 1 ->
    NonnegExpectation x = NonnegExpectation (rvmult x (EventIndicator dec)).
  Proof.
    intros pone.
    assert (eqq1:rv_eq x
                  (rvplus (rvmult x (EventIndicator dec))
                          (rvmult x (EventIndicator (classic_dec (pre_event_complement P)))))).
    {
      intros ?.
      rv_unfold.
      unfold pre_event_complement.
      repeat match_destr; try tauto; lra.
    }

    rewrite (NonnegExpectation_ext _ _ eqq1).
    rewrite NonnegExpectation_sum.
    - assert (eqq2:almostR2 prts eq (rvmult x (EventIndicator (classic_dec (pre_event_complement P)))) (const 0)).
      {
        exists P.
        split; trivial.
        intros.
        unfold pre_event_complement.
        rv_unfold.
        match_destr; try tauto; lra.
      }
      rewrite (NonnegExpectation_almostR2_0 _ eqq2).
      now rewrite Rbar_plus_0_r.
    - typeclasses eauto.
    - apply rvmult_rv; trivial.
      + apply EventIndicator_pre_rv.
        apply sa_complement.
        destruct P; trivial.
  Qed.
  
  Lemma NonnegExpectation_almostR2_proper x y
        {xrv:RandomVariable dom borel_sa x}
        {yrv:RandomVariable dom borel_sa y}
        {xnnf:NonnegativeFunction x}
        {ynnf:NonnegativeFunction y} :
    almostR2 prts eq x y ->
    NonnegExpectation x = NonnegExpectation y.
  Proof.
    intros [P [Pone Peqq]].
    rewrite (NonnegExpectation_EventIndicator_as x (classic_dec P) Pone).
    rewrite (NonnegExpectation_EventIndicator_as y (classic_dec P) Pone).
    apply NonnegExpectation_ext.
    intros ?.
    rv_unfold.
    match_destr; try lra.
    now rewrite Peqq.
  Qed.
  
  Lemma Expectation_almostR2_0 x :
    almostR2 prts eq x (const 0) ->
    Expectation x = Some (Finite 0).
  Proof.
    intros.
    unfold Expectation.
    assert (almostR2 prts eq (fun omega => nonneg(pos_fun_part x omega)) (const 0)).
    {
      rewrite (pos_fun_part_proper_almostR2 _ _ H).
      unfold const; simpl.
      unfold Rmax.
      match_destr; try lra.
      reflexivity.
    } 
    assert (almostR2 prts eq (fun omega => nonneg(neg_fun_part x omega)) (const 0)).
    {
      rewrite (neg_fun_part_proper_almostR2 _ _ H).
      unfold const; simpl.
      unfold Rmax.
      match_destr; try lra.
      reflexivity.
    }
    rewrite (NonnegExpectation_almostR2_0 _ H0).
    rewrite (NonnegExpectation_almostR2_0 _ H1).
    simpl; repeat f_equal.
    lra.
  Qed.

  Lemma Expectation_almostR2_proper x y
        {xrv:RandomVariable dom borel_sa x}
        {yrv:RandomVariable dom borel_sa y} :
    almostR2 prts eq x y ->
    Expectation x = Expectation y.
  Proof.
    intros eqq.
    unfold Expectation.
    rewrite (NonnegExpectation_almostR2_proper (fun x0 : Ts => pos_fun_part x x0) (fun x0 : Ts => pos_fun_part y x0))
      by now apply pos_fun_part_proper_almostR2.
    rewrite (NonnegExpectation_almostR2_proper (fun x0 : Ts => neg_fun_part x x0) (fun x0 : Ts => neg_fun_part y x0))
      by now apply neg_fun_part_proper_almostR2.
    reflexivity.
  Qed.

  Lemma pos_fun_mult_ind_ge (X:Ts->R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (fun omega => nonneg (pos_fun_part X omega))
          (rvmult X (EventIndicator (event_ge_dec dom X 0))).
  Proof.
    intros omega.
    unfold pos_fun_part, rvmult, EventIndicator; simpl.
    unfold Rmax.
    repeat match_destr; simpl in *; lra.
  Qed.

  Lemma event_le_dec (σ:SigmaAlgebra Ts) x1 n
        {rv1:RandomVariable σ borel_sa x1} :
    dec_event (event_le σ x1 n).
  Proof.
    unfold event_ge.
    intros x; simpl.
    apply Rle_dec.
  Qed.

  Lemma neg_fun_mult_ind_le (X:Ts->R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (rvopp (fun omega => nonneg (neg_fun_part X omega)))
          (rvmult X (EventIndicator (event_le_dec dom X 0))).
  Proof.
    intros omega.
    unfold neg_fun_part, rvmult, EventIndicator; simpl.
    unfold Rmax, rvopp, rvscale.
    repeat match_destr; simpl in *; try lra.      
  Qed.

  Lemma neg_fun_mult_ind_le' (X:Ts->R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (fun omega => nonneg (neg_fun_part X omega))
          (rvopp (rvmult X (EventIndicator (event_le_dec dom X 0)))).
  Proof.
    intros omega.
    unfold neg_fun_part, rvmult, EventIndicator; simpl.
    unfold Rmax, rvopp, rvscale.
    repeat match_destr; simpl in *; try lra.      
  Qed.

  Lemma Expectation_nonneg_zero_almost_zero
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {pofrf :NonnegativeFunction X} :
    Expectation X = Some (Finite 0) ->
    almostR2 prts eq X (const 0).
  Proof.
    exists (preimage_singleton X 0).
    split.
    - now apply Expectation_zero_pos.
    - intros.
      apply H0.
  Qed.

  Lemma Expectation_mult_indicator_almost_zero
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P), Expectation (rvmult X (EventIndicator dec))
                            = Some (Finite 0)) ->
    almostR2 prts eq X (const 0).
  Proof.
    intros HH.
    generalize (HH (event_ge _ X 0) (event_ge_dec _ X 0))
    ; intros HHpos.

    assert (pos_exp:Expectation (pos_fun_part X) = Some (Finite 0)).
    {
      rewrite <- HHpos.
      apply Expectation_proper.
      apply pos_fun_mult_ind_ge.
    } 

    generalize (HH (event_le _ X 0) (event_le_dec _ X 0))
    ; intros HHneg.

    assert (neg_exp':Expectation (rvopp (neg_fun_part X)) = Some (Finite 0)).
    {
      rewrite <- HHneg.
      apply Expectation_proper.
      apply neg_fun_mult_ind_le.
    }

    assert (neg_exp:Expectation (neg_fun_part X) = Some (Finite 0)).
    {
      generalize (Expectation_opp (neg_fun_part X))
      ; intros HH2.
      rewrite neg_exp' in HH2.
      simpl in *.
      match_destr_in HH2.
      invcs HH2.
      f_equal.
      apply (f_equal Rbar_opp) in H0.
      rewrite Rbar_opp_involutive in H0.
      simpl in H0.
      now rewrite Ropp_0 in H0.
    }

    apply Expectation_nonneg_zero_almost_zero in pos_exp; try typeclasses eauto.
    apply Expectation_nonneg_zero_almost_zero in neg_exp; try typeclasses eauto.
    assert (eqq:almostR2 prts eq
                         (rvplus (fun x : Ts => pos_fun_part X x) (rvopp (fun x : Ts => neg_fun_part X x))) (const 0)).
    {
      transitivity (rvplus (Ts:=Ts) (const 0) (rvopp (const 0)))
      ; [| apply almostR2_eq_subr; intros ?; rv_unfold; lra].
      apply almostR2_eq_plus_proper; trivial.
      now apply almostR2_eq_opp_proper.
    }
    rewrite <- eqq.
    apply almostR2_eq_subr.
    apply rv_pos_neg_id.
  Qed.

  Lemma Expectation_mult_indicator_almost_nonneg_zero'
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some (Finite r) => 0 <= r
        | _ => False
        end) ->
    almostR2 prts eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0).
  Proof.               
    intros.
    apply (Expectation_mult_indicator_almost_zero (neg_fun_part X)).
    - intros P dec.
      generalize (neg_fun_mult_ind_le' X)
      ; intros eqq1.
      assert (rv_eq (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))
                    (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        intros ?.
        rv_unfold; simpl.
        unfold Rmax.
        destruct (dec_event_inter (event_le_dec dom X 0) dec a); simpl in *.
        - destruct p.
          repeat match_destr; try lra; tauto.
        - repeat match_destr; try lra.
          elim n.
          split; trivial.
          lra.
      }
      transitivity (Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        now apply Expectation_proper.
      }

      specialize (H _ (dec_event_inter (event_le_dec dom X 0) dec)).
      match_option_in H; simpl in H; try tauto.
      destruct r; try tauto.
      assert (r = 0).
      { 
        assert (eqq2:Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec)))) =Some (Finite (- r))).
        {
          now rewrite Expectation_opp, eqq; simpl.
        }
        
        rewrite <- H0 in eqq2.
        assert (nnf:NonnegativeFunction (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))).
        {
          typeclasses eauto.
        } 
        rewrite (Expectation_pos_pofrf _ (nnf:=nnf)) in eqq2.
        invcs eqq2.
        generalize (NonnegExpectation_pos (rvmult (fun x : Ts => Rmax (- X x) 0) (EventIndicator dec)))
        ; intros HH2.
        simpl in HH2.
        match_destr_in HH2.
        invcs H2.
        lra.
      }
      rewrite Expectation_opp, eqq, H1.
      simpl.
      now rewrite Ropp_0.
  Qed.

  Lemma neg_fun_part_eq_0_nonneg
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    rv_eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0) ->
    NonnegativeFunction X.
  Proof.
    intros ??.
    rewrite (rv_pos_neg_id X x).
    unfold rvplus, rvopp, rvscale.
    rewrite H.
    rv_unfold; simpl.
    field_simplify.
    apply Rmax_r.
  Qed.

  Lemma neg_fun_part_eq_0_nonneg_almost
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    almostR2 prts eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0) ->
    almostR2 prts Rle (const 0) X.
  Proof.
    intros [ p[? pH]].
    exists p; split; trivial.
    intros x px.
    specialize (pH x px).
    rewrite (rv_pos_neg_id X x).

    unfold rvplus, rvopp, rvscale.
    rewrite pH.
    rv_unfold.
    simpl.
    field_simplify.
    apply Rmax_r.
  Qed.

  Lemma Expectation_mult_indicator_almost_nonneg'
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some (Finite r) => 0 <= r
        | _ => False
        end) ->
    almostR2 prts Rle (const 0) X.
  Proof.
    intros.
    apply neg_fun_part_eq_0_nonneg_almost; trivial.
    now apply Expectation_mult_indicator_almost_nonneg_zero'.
  Qed.      

  Lemma Expectation_mult_indicator_almost_nonneg_zero
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some r => Rbar_le 0 r
        | _ => False
        end) ->
    almostR2 prts eq (fun x : Ts => nonneg (neg_fun_part X x)) (const 0).
  Proof.
    intros.
    apply (Expectation_mult_indicator_almost_zero (neg_fun_part X)).
    - intros P dec.
      generalize (neg_fun_mult_ind_le' X)
      ; intros eqq1.
      assert (rv_eq (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))
                    (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        intros ?.
        rv_unfold; simpl.
        unfold Rmax.
        destruct (dec_event_inter (event_le_dec dom X 0) dec a); simpl in *.
        - destruct p.
          repeat match_destr; try lra; tauto.
        - repeat match_destr; try lra.
          elim n.
          split; trivial.
          lra.
      }
      transitivity (Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec))))).
      {
        now apply Expectation_proper.
      }

      specialize (H _ (dec_event_inter (event_le_dec dom X 0) dec)).
      match_option_in H; simpl in H; try tauto.
      destruct r; try tauto.
      + assert (r = 0).
        { 
          assert (eqq2:Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec)))) =Some (Finite (- r))).
          {
            now rewrite Expectation_opp, eqq; simpl.
          }
          
          rewrite <- H0 in eqq2.
          assert (nnf:NonnegativeFunction (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))).
          {
            typeclasses eauto.
          } 
          rewrite (Expectation_pos_pofrf _ (nnf:=nnf)) in eqq2.
          invcs eqq2.
          generalize (NonnegExpectation_pos (rvmult (fun x : Ts => Rmax (- X x) 0) (EventIndicator dec)))
          ; intros HH2.
          simpl in HH2.
          match_destr_in HH2.
          invcs H2.
          lra.
        }
        rewrite Expectation_opp, eqq, H1.
        simpl.
        now rewrite Ropp_0.
      + assert (eqq2:Expectation (rvopp (rvmult X (EventIndicator (dec_event_inter (event_le_dec dom X 0) dec)))) = Some (m_infty)).
        {
          now rewrite Expectation_opp, eqq; simpl.
        }
        rewrite <- H0 in eqq2.
        assert (nnf:NonnegativeFunction (rvmult (fun x : Ts => neg_fun_part X x) (EventIndicator dec))).
        {
          typeclasses eauto.
        } 
        rewrite (Expectation_pos_pofrf _ (nnf:=nnf)) in eqq2.
        invcs eqq2.
        generalize (NonnegExpectation_pos (rvmult (fun x : Ts => Rmax (- X x) 0) (EventIndicator dec)))
        ; intros HH2.
        simpl in HH2.
        match_destr_in HH2.
        invcs H2.
        lra.
  Qed.

  Lemma Expectation_mult_indicator_almost_nonneg
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X} :
    (forall P (dec:dec_event P),
        match Expectation (rvmult X (EventIndicator dec)) with
        | Some r => Rbar_le 0 r
        | _ => False
        end) ->
    almostR2 prts Rle (const 0) X.
  Proof.
    intros.
    apply neg_fun_part_eq_0_nonneg_almost; trivial.
    now apply Expectation_mult_indicator_almost_nonneg_zero.
  Qed.      


Lemma Expectation_EventIndicator:
  forall {Ts : Type} {dom : SigmaAlgebra Ts} {Prts : ProbSpace dom} {P : event dom}
    (dec : forall x : Ts, {P x} + {~ P x}), Expectation (EventIndicator dec) = Some (Finite (ps_P P)).
Proof.
  intros.
  erewrite Expectation_simple.
  now rewrite SimpleExpectation_EventIndicator.
Qed.

End almost_sec.

Section EventRestricted.
    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

      Lemma event_restricted_NonnegExpectation P (pf1 : ps_P P = 1) pf (f : Ts -> R) 
        (nnf : NonnegativeFunction f) :
    @NonnegExpectation Ts dom prts f nnf = 
    @NonnegExpectation _ _ (event_restricted_prob_space prts P pf) 
                       (event_restricted_function P f) _.
  Proof.
    unfold NonnegExpectation.
    unfold SimpleExpectationSup.
    unfold Lub_Rbar.
    destruct
      (ex_lub_Rbar
         (fun x : R =>
            exists
              (rvx : Ts -> R) (rv : RandomVariable dom borel_sa rvx) 
              (frf : FiniteRangeFunction rvx),
              BoundedNonnegativeFunction f rvx /\ SimpleExpectation rvx = x)).
    destruct
       (ex_lub_Rbar
       (fun x : R =>
        exists
          (rvx : event_restricted_domain P -> R) (rv : RandomVariable
                                                       (event_restricted_sigma P)
                                                       borel_sa rvx) 
        (frf : FiniteRangeFunction rvx),
          BoundedNonnegativeFunction (event_restricted_function P f) rvx /\
          SimpleExpectation rvx = x)).
    simpl.
    unfold is_lub_Rbar in *.
    destruct i; destruct i0.
    apply Rbar_le_antisym.
    - apply H0.
      unfold is_ub_Rbar.
      intros.
      destruct H3 as [? [? [? [? ?]]]].
      unfold BoundedNonnegativeFunction in H3.
      destruct H3.
      unfold is_ub_Rbar in H1.
      unfold is_ub_Rbar in H.
      apply H1.
      unfold BoundedNonnegativeFunction.
      exists (event_restricted_function P x2).
      exists (Restricted_RandomVariable P x2 x3).
      exists (Restricted_FiniteRangeFunction P x2 x4).
      split.
      + split.
        * now apply Restricted_NonnegativeFunction.
        * now apply event_restricted_rv_le.
      + now rewrite <- event_restricted_SimpleExpectation.
    - apply H2.
      unfold is_ub_Rbar.
      intros.
      destruct H3 as [? [? [? [? ?]]]].
      unfold BoundedNonnegativeFunction in H3.
      destruct H3.
      unfold is_ub_Rbar in H1.
      unfold is_ub_Rbar in H.
      apply H.
      unfold BoundedNonnegativeFunction.
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

  Lemma event_restricted_Expectation P (pf1 : ps_P P = 1) pf (f : Ts -> R) :
    @Expectation Ts dom prts f = 
    @Expectation _ _ (event_restricted_prob_space prts P pf) 
                       (event_restricted_function P f).
  Proof.
    unfold Expectation.
    generalize (event_restricted_NonnegExpectation 
                  P pf1 pf (pos_fun_part f) _); intros.
    rewrite H.
    generalize (event_restricted_NonnegExpectation 
                  P pf1 pf (neg_fun_part f) _); intros.
    now rewrite H0.
  Qed.
End EventRestricted.

Section sa_sub.

    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Lemma NonnegExpectation_prob_space_sa_sub
        (x:Ts -> R)
        {pofrf:NonnegativeFunction x}
        {rv:RandomVariable dom2 borel_sa x}
        
    :
      @NonnegExpectation Ts dom2 (prob_space_sa_sub prts sub)  x pofrf =
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
    @Expectation Ts dom2 (prob_space_sa_sub prts sub)  x =
    @Expectation Ts dom prts x.
  Proof.
    generalize ((RandomVariable_sa_sub sub x (rv_x:=rv)))
    ; intros rv1.

    unfold Expectation.
    repeat rewrite NonnegExpectation_prob_space_sa_sub by typeclasses eauto.
    reflexivity.
  Qed.

End sa_sub.

Lemma INR_eq_0 n : INR n = 0 -> n = 0%nat.
Proof.
  destruct (PeanoNat.Nat.eq_dec n 0); trivial; intros.
  now apply not_0_INR in n0.
Qed.  

Lemma find_ext_in {A} (f g : A -> bool) (l : list A) :
  (forall x : A, In x l -> f x = g x) -> find f l = find g l.
Proof.
  intros HH.
  induction l; simpl in *; trivial.
  rewrite HH by firstorder.
  now rewrite IHl by firstorder.
Qed.

Section indep.
    Context {Ts:Type}
            {dom: SigmaAlgebra Ts}
            (prts:ProbSpace dom).

    Existing Instance simple_approx_frf.
    Existing Instance simple_approx_rv.

    Instance simple_approx_borel_rv n :
        RandomVariable borel_sa borel_sa
                        (fun Xw : R =>
                           if Rbar_ge_dec (Finite Xw) (INR n)
                           then INR n
                           else
                             match
                               find (fun start : R => if Rbar_ge_dec Xw start then true else false)
                                    (rev (map (fun x : nat => INR x / 2 ^ n) (seq 0 (n * 2 ^ n))))
                             with
                             | Some r => r
                             | None => INR 0
                             end).
    Proof.
      pose (c := fun x => if Rle_dec 0 x then 1 else 0).
      assert (RandomVariable borel_sa borel_sa
                             (rvchoice (fun x => if Req_EM_T (c x) 0 then false else true)
                                       (fun x => x)
                                       (fun _ => 0))).
      {
        subst c.
        apply rvchoice_rv.
        - intros ?.
          apply borel_sa_preimage; trivial; intros.
          destruct (Rle_dec 1 r).
          {
            apply (sa_proper _ pre_Ω).
            - intros ?; unfold pre_Ω.
              match_destr; split; try tauto; lra.
            - apply sa_all.
          } 
          destruct (Rlt_dec r 0).
          {
            apply (sa_proper _ pre_event_none).
            - intros ?; unfold pre_event_none.
              match_destr; split; try tauto; lra.
            - apply sa_none.
          } 
          apply (sa_proper _ (fun omega => omega < 0)).
          {
            intros ?.
            match_destr; lra.
          }
          apply sa_ge_lt.
          apply sa_le_ge.
          intros ???.
          apply H.
          exists r0; tauto.
        - apply id_rv.
        - apply rvconst.
      }
      assert(Rbar_NonnegativeFunction
               (fun omega : R =>
                  rvchoice (fun x : R => if Req_EM_T (c x) 0 then false else true) 
                           (fun x : R => x) (fun _ : R => 0) omega)).
      {
        intros ?.
        unfold rvchoice.
        subst c; simpl.
        destruct (Rle_dec 0 x)
        ; destruct (Req_EM_T _ _)
        ; lra.
      } 

      generalize (simple_approx_rv
                    (rvchoice (fun x => if Req_EM_T (c x) 0 then false else true)
                                       (fun x => x)
                                       (fun _ => 0)) n).
      apply RandomVariable_proper; try reflexivity.
      intros ?.
      unfold simple_approx, rvchoice.
      subst c.

      case_eq (Rbar_ge_dec a (INR n)); intros; simpl in *.
      - destruct (Rle_dec 0 a)
        ; destruct (Req_EM_T _ _)
        ; try lra.
        + rewrite H1; trivial.
        + simpl in r.
          generalize (pos_INR n); lra.
      - destruct (Rle_dec 0 a)
        ; destruct (Req_EM_T _ _)
        ; try lra.
        + now rewrite H1.
        + generalize (pos_INR n); intros.

          destruct (Rbar_ge_dec 0 (INR n)); simpl in *.
          * assert (eqq:INR n = 0) by lra.
            apply INR_eq_0 in eqq; subst.
            now simpl.
          * assert (n <> 0%nat).
            {
              apply INR_not_0; lra.
            } 
            generalize (n * 2 ^ n)%nat
            ; intros nn.
            { induction nn; [now simpl |].
              rewrite seq_Sn.
              repeat rewrite map_app.
              repeat rewrite rev_app_distr; simpl.
              assert (0 <= INR nn / 2 ^ n).
              {
                apply Rcomplements.Rdiv_le_0_compat.
                - apply pos_INR.
                - apply pow_lt; lra.
              } 
              destruct (Rbar_ge_dec a (INR nn / 2 ^ n)); simpl in *; [lra |].
              destruct (Rbar_ge_dec 0 (INR nn / 2 ^ n)); simpl in *; trivial.
              assert (nn = 0%nat).
              {
                apply INR_eq_0.
                assert (INR nn / 2 ^ n = 0) by lra.
                destruct nn; simpl; trivial.
                cut (0 < INR (S nn) / 2 ^ n); [lra |].
                apply Rdiv_lt_0_compat.
                - rewrite S_INR.
                  generalize (pos_INR nn); lra.
                - apply pow_lt; lra.
              } 
              subst; simpl; lra.
            } 
    Qed.
          
    Lemma simple_approx_independent (X Y:Ts->R)
      {posx : Rbar_NonnegativeFunction X}
      {posy : Rbar_NonnegativeFunction Y}
      {rvx  : RandomVariable dom borel_sa X}
      {rvy  : RandomVariable dom borel_sa Y} :
      independent_rvs prts borel_sa borel_sa X Y ->
      forall n, independent_rvs prts borel_sa borel_sa (simple_approx X n) (simple_approx Y n).
    Proof.
      intros.

      assert (rv1:RandomVariable borel_sa borel_sa
                                 (fun Xw : R =>
            if Rbar_ge_dec (Finite Xw) (INR n)
            then INR n
            else
             match
               find (fun start : R => if Rbar_ge_dec Xw start then true else false)
                 (rev (map (fun x : nat => INR x / 2 ^ n) (seq 0 (n * 2 ^ n))))
             with
             | Some r => r
             | None => INR 0
             end)).
      {
        typeclasses eauto.
      }

      assert (rv1':RandomVariable dom borel_sa
          ((fun Xw : R =>
            if Rbar_ge_dec (Finite Xw) (INR n)
            then INR n
            else
             match
               find (fun start : R => if Rbar_ge_dec Xw start then true else false)
                 (rev (map (fun x : nat => INR x / 2 ^ n) (seq 0 (n * 2 ^ n))))
             with
             | Some r => r
             | None => INR 0
             end) ∘ (fun x : Ts => X x))).
      {
        unfold compose.
        apply simple_approx_rv; trivial.
        now apply Real_Rbar_rv.
      }

      assert (rv2:RandomVariable borel_sa borel_sa
          (fun Xw : R =>
            if Rbar_ge_dec (Finite Xw) (INR n)
            then INR n
            else
             match
               find (fun start : R => if Rbar_ge_dec Xw start then true else false)
                 (rev (map (fun x : nat => INR x / 2 ^ n) (seq 0 (n * 2 ^ n))))
             with
             | Some r => r
             | None => INR 0
             end)).
      {
        typeclasses eauto.
      } 

      assert (rv2':RandomVariable dom borel_sa
          ((fun Xw : R =>
            if Rbar_ge_dec (Finite Xw) (INR n)
            then INR n
            else
             match
               find (fun start : R => if Rbar_ge_dec Xw start then true else false)
                 (rev (map (fun x : nat => INR x / 2 ^ n) (seq 0 (n * 2 ^ n))))
             with
             | Some r => r
             | None => INR 0
             end) ∘ (fun x : Ts => Y x))).
      {
        unfold compose.
        apply simple_approx_rv; trivial.
        now apply Real_Rbar_rv.
      }

      generalize (independent_rv_compose prts _ _ _ _ 
                             X Y (fun Xw =>
                                if Rbar_ge_dec (Finite Xw) (INR n) then (INR n) else
                                  match find (fun start => if Rbar_ge_dec (Finite Xw) (Finite start) then true else false) 
                                             (rev (map (fun x => (INR x / (2^n))) 
                                                       (seq 0 (n*(2^n))))) with
                                  | Some r => r
                                  | None => (INR 0)
                                  end)
                             (fun Xw =>
                                if Rbar_ge_dec (Finite Xw) (INR n) then (INR n) else
                                  match find (fun start => if Rbar_ge_dec Xw (Finite start) then true else false) 
                                             (rev (map (fun x => (INR x / (2^n))) 
                                                       (seq 0 (n*(2^n))))) with
                                  | Some r => r
                                  | None => (INR 0)
                                  end)
                 H).
      apply independent_rvs_proper; reflexivity.
    Qed.

    Lemma simple_approx_independent' (X Y:Ts->R) n
      {posx : Rbar_NonnegativeFunction X}
      {posy : Rbar_NonnegativeFunction Y}
      {rvx  : RandomVariable dom borel_sa X}
      {rvy  : RandomVariable dom borel_sa Y}
      {rvsx  : RandomVariable dom borel_sa (simple_approx X n)}
      {rvsy  : RandomVariable dom borel_sa (simple_approx Y n)} :
      independent_rvs prts borel_sa borel_sa X Y ->
      independent_rvs prts borel_sa borel_sa (simple_approx X n) (simple_approx Y n).
    Proof.
      intros.
      generalize (simple_approx_independent X Y H n).
      apply independent_rvs_proper; reflexivity.
    Qed.

End indep.

Section ident.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom).

  Existing Instance simple_approx_frf.
  Existing Instance simple_approx_rv.

  Lemma ident_distr_simple_approx_eq (X Y:Ts->R)
        {posx : Rbar_NonnegativeFunction X}
        {posy : Rbar_NonnegativeFunction Y}
        {rvx  : RandomVariable dom borel_sa X}
        {rvy  : RandomVariable dom borel_sa Y} :
    identically_distributed_rvs prts borel_sa X Y ->
    forall n, SimpleExpectation (simple_approx X n) = SimpleExpectation (simple_approx Y n).
  Proof.
    intros.
    unfold simple_approx.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext; intros.
    f_equal.


    red in H.
    generalize (simple_approx_borel_rv n (exist sa_sigma _ (borel_singleton a))); intros HH.

    specialize (H (exist _ _ HH)).
    etransitivity; [etransitivity |]; [| apply H |]
    ; apply ps_proper; intros ?; simpl
    ; reflexivity.
  Qed.

End ident.
