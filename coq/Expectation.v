Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq Coquelicot.Hierarchy.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Import NumberIso.
Require Export SimpleExpectation.
Require Import AlmostEqual.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section Expectation.
  
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}.

  (* should be p_infty if (is_empty (fun omega => rv_X omega > x)) *)

  Definition BoundedPositiveRandomVariable
             (rv_X1 rv_X2 : Ts -> R) :=
    PositiveRandomVariable rv_X2 /\ rv_le rv_X2 rv_X1.

  Definition SimpleExpectationSup 
             (E :  forall 
                 (rvx:Ts -> R)
                 (rv : RandomVariable dom borel_sa rvx)
                 (srv:SimpleRandomVariable rvx), Prop) : Rbar
    := Lub_Rbar (fun (x : R) => 
                   exists rvx rv srv, 
                     E rvx rv srv /\ (SimpleExpectation rvx) = x).
  
  Definition Expectation_posRV
             (rv_X : Ts -> R)
             {posrv:PositiveRandomVariable rv_X} :  Rbar   :=
    (SimpleExpectationSup
       (fun
           (rvx2: Ts -> R)
           (rv2 : RandomVariable dom borel_sa rvx2)
           (srv2:SimpleRandomVariable rvx2) =>
           (BoundedPositiveRandomVariable rv_X rvx2))).

  Lemma srv_Expectation_posRV
        (rv_X : Ts -> R)
        {rvx_rv : RandomVariable dom borel_sa rv_X}
        {posrv:PositiveRandomVariable rv_X}
        {srv:SimpleRandomVariable rv_X} :
    Expectation_posRV rv_X = SimpleExpectation rv_X.
  Proof.
    unfold Expectation_posRV.
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
        unfold BoundedPositiveRandomVariable in H.
        destruct H.
        rewrite <- H0.
        apply SimpleExpectation_le; trivial.
    - exists rv_X.
      exists rvx_rv.
      exists srv.
      split; trivial.
      unfold BoundedPositiveRandomVariable.
      split; trivial.
      intros ?; lra.
  Qed.

  Global Instance bprv_eq_proper : Proper (rv_eq ==> rv_eq ==> iff) BoundedPositiveRandomVariable.
  Proof.
    intros x1 x2 eqq1 y1 y2 eqq2.
    unfold BoundedPositiveRandomVariable.
    unfold PositiveRandomVariable.
    repeat rewrite eqq1.
    rewrite eqq2.
    repeat red in eqq2.
    intuition.
    - now rewrite <- eqq2.
    - now rewrite eqq2.
  Qed.
  
  Lemma Expectation_posRV_ext 
        {rv_X1 rv_X2 : Ts -> R}
        (prv1:PositiveRandomVariable rv_X1) 
        (prv2:PositiveRandomVariable rv_X2):
    rv_eq rv_X1 rv_X2 ->
    Expectation_posRV rv_X1 = Expectation_posRV rv_X2.
  Proof.
    intros eqq.
    unfold Expectation_posRV, SimpleExpectationSup.
    apply Lub_Rbar_eqset; intros x.
    split; intros [y [ yrv [ysrv [??]]]].
    - exists y; exists yrv; exists ysrv.
      rewrite <- eqq.
      auto.
    - exists y; exists yrv; exists ysrv.
      rewrite eqq.
      auto.
  Qed.

  Lemma Expectation_posRV_re
        {rv_X1 rv_X2 : Ts -> R}
        (eqq:rv_eq rv_X1 rv_X2)
        {prv1:PositiveRandomVariable rv_X1} :
    Expectation_posRV rv_X1 = Expectation_posRV rv_X2 (posrv:=((proj1 (PositiveRandomVariable_proper _ _ eqq)) prv1)).
  Proof.
    now apply Expectation_posRV_ext.
  Qed.

  Lemma Expectation_posRV_pf_irrel 
        {rv_X: Ts -> R}
        (prv1 prv2:PositiveRandomVariable rv_X) :
    Expectation_posRV rv_X (posrv:=prv1) = Expectation_posRV rv_X (posrv:=prv2).
  Proof.
    apply Expectation_posRV_ext.
    reflexivity.
  Qed.

  Definition Rbar_minus' (x y : Rbar) : option Rbar :=
    Rbar_plus' x (Rbar_opp y).
  
  Definition Expectation (rv_X : Ts -> R) : option Rbar :=
    Rbar_minus' (Expectation_posRV (pos_fun_part rv_X))
                (Expectation_posRV (neg_fun_part rv_X)).
  
  Lemma pos_fun_part_pos (rv_X : Ts -> R) 
        {prv : PositiveRandomVariable rv_X} :
    rv_eq rv_X (pos_fun_part rv_X).
  Proof.
    unfold pos_fun_part.
    intro x.
    simpl.
    unfold PositiveRandomVariable in prv.
    now rewrite Rmax_left.
  Qed.

  Lemma neg_fun_part_pos (rv_X : Ts -> R) 
        {prv : PositiveRandomVariable rv_X} :
    rv_eq (const 0) (neg_fun_part rv_X).
  Proof.
    unfold neg_fun_part, const.
    intro x.
    simpl.
    specialize (prv x).
    rewrite Rmax_right; lra.
  Qed.

  Lemma Expectation_ext {rv_X1 rv_X2 : Ts -> R} :
    rv_eq rv_X1 rv_X2 ->
    Expectation rv_X1 = Expectation rv_X2.
  Proof.
    intros eqq.
    unfold Expectation.
    f_equal.
    - apply Expectation_posRV_ext.
      intros x; simpl.
      now rewrite eqq.
    - f_equal.
      apply Expectation_posRV_ext.
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

  Lemma Rbar_mult_mult_pos (c : posreal) (l : Rbar) :
    Rbar_mult_pos l c = Rbar_mult l c.
  Proof.
    assert (0 < c) as cpos by apply cond_pos.
    unfold Rbar_mult_pos.
    unfold Rbar_mult, Rbar_mult'.
    destruct l.
    - trivial.
    - match_case; intros; match_case_in H; intros; try lra; rewrite H0 in H; 
        match_case_in H; intros; try lra; rewrite H1 in H; [now invcs H| congruence].
    - match_case; intros; match_case_in H; intros; try lra; rewrite H0 in H; 
        match_case_in H; intros; try lra; rewrite H1 in H; [now invcs H| congruence].
  Qed.

  Lemma Rbar_div_mult_pos (c : posreal) (l : Rbar) :
    Rbar_mult_pos (Rbar_div l c) c = l.
  Proof.
    assert (c > 0) as cpos by apply cond_pos.
    assert ((pos c) <> 0) as cneq0 by lra.
    assert (/c > 0) by apply Rinv_0_lt_compat, cpos.
    unfold Rbar_div; simpl.
    unfold Rbar_mult, Rbar_mult', Rbar_mult_pos.
    destruct l.
    - f_equal; field; trivial.
    - case (Rle_dec 0 (/ c)) ; intros; try lra.
      match_case; intros; match_case_in H0; intros; match_case_in H1; intros; 
        try lra; rewrite H2 in H0; invcs H0.
    - case (Rle_dec 0 (/ c)) ; intros; try lra.
      match_case; intros; match_case_in H0; intros; match_case_in H1; intros; 
        try lra; rewrite H2 in H0; invcs H0.
  Qed.

  Lemma rbar_le_scaled (c : posreal) (x y :Rbar) :
    Rbar_le x (Rbar_mult c y) <-> Rbar_le (Rbar_div x c) y.
  Proof.
    symmetry.
    rewrite Rbar_mult_pos_le with (z := c).
    rewrite Rbar_mult_comm.
    rewrite Rbar_div_mult_pos.
    now rewrite Rbar_mult_mult_pos.
  Qed.
  
  Lemma rbar_le_scaled2 (c : posreal) (x y :Rbar) :
    Rbar_le (Rbar_mult c x) y <-> Rbar_le x (Rbar_div y c).
  Proof.
    symmetry.
    rewrite Rbar_mult_pos_le with (z := c).     
    rewrite Rbar_div_mult_pos.
    rewrite Rbar_mult_comm.
    now rewrite Rbar_mult_mult_pos.     
  Qed.

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

  Lemma Expectation_posRV_scale (c: posreal) 
        (rv_X : Ts -> R)
        {posrv:PositiveRandomVariable rv_X} :
    Expectation_posRV (rvscale c rv_X) =
    Rbar_mult c (Expectation_posRV rv_X).
  Proof.
    unfold Expectation_posRV.
    unfold BoundedPositiveRandomVariable.
    unfold SimpleExpectationSup.
    rewrite <- lub_rbar_scale.
    apply Lub_Rbar_eqset; intros.
    split; intros [? [? [? [[??]?]]]].
    - exists (rvscale (/ c) x0).
      exists (rvscale_rv _ _ _ _).
      exists (srvscale _ _).
      split; [split |].
      + assert (0 < / c).
        { destruct c; simpl.
          now apply Rinv_0_lt_compat.
        } 
        apply (positive_scale_prv (mkposreal _ H2) x0). 
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
      exists (srvscale c x0).
      split; [split |].
      + typeclasses eauto.
      + now rewrite H0.
      + rewrite <- scaleSimpleExpectation.
        rewrite H1.
        field; trivial.
        destruct c; simpl.
        lra.
  Qed.

  Lemma scale_Rmax0 (c:posreal) :
    forall (x:R),
      Rmax (c * x) 0 = c * Rmax x 0.
    intros.
    replace (0) with (c * 0) at 1 by lra.
    rewrite RmaxRmult; trivial.
    left.
    apply cond_pos.
  Qed.

  Lemma Expectation_scale_pos (c:posreal) (rv_X : Ts -> R) :
    Expectation_posRV (fun x : Ts => pos_fun_part (rvscale c rv_X) x) =
    Rbar_mult c (Expectation_posRV (pos_fun_part rv_X)).
  Proof.
    rewrite <- Expectation_posRV_scale.
    apply Expectation_posRV_ext.
    intros x.
    unfold pos_fun_part, rvscale.
    simpl.
    now rewrite scale_Rmax0.
  Qed.
  
  Lemma Expectation_scale_neg (c:posreal) (rv_X : Ts -> R) :
    Expectation_posRV (fun x : Ts => neg_fun_part (rvscale c rv_X) x) =
    Rbar_mult c (Expectation_posRV (neg_fun_part rv_X)).
  Proof.
    rewrite <- Expectation_posRV_scale.
    apply Expectation_posRV_ext.
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
    rewrite Expectation_posRV_ext with (prv2 := negative_part_prv rv_X).
    - replace (Expectation_posRV (fun x : Ts => neg_fun_part (rvopp rv_X) x)) with
          (Expectation_posRV (fun x : Ts => pos_fun_part rv_X x)).
      + unfold Rbar_minus'.
        case_eq  (Expectation_posRV (fun x : Ts => pos_fun_part rv_X x)); intros.
        * case_eq  (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x)); intros; simpl; f_equal.
          rewrite Rbar_finite_eq; lra.
        * case_eq  (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x)); intros; simpl; f_equal.
        * case_eq  (Expectation_posRV (fun x : Ts => neg_fun_part rv_X x)); intros; simpl; f_equal.
      + symmetry.
        rewrite Expectation_posRV_ext with (prv2 := positive_part_prv rv_X).
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
        {prv:PositiveRandomVariable rv_X} :
    Rbar_lt b l -> Expectation_posRV rv_X = l -> 
    exists (x:R), (exists (rvx : Ts -> R) (rv : RandomVariable dom borel_sa rvx)
                (srv : SimpleRandomVariable rvx),
                 BoundedPositiveRandomVariable rv_X rvx /\ SimpleExpectation rvx = x) /\ x > b.
  Proof.
    unfold Expectation_posRV, SimpleExpectationSup.       
    unfold Lub_Rbar.
    match goal with
      [|- context [proj1_sig ?x]] => destruct x; simpl
    end.
    intros.
    invcs H0.
    apply lub_Rbar_witness with (l := l); trivial.
  Qed.

  Lemma Expectation_posRV_le 
        (rv_X1 rv_X2 : Ts -> R)
        {prv1 : PositiveRandomVariable rv_X1}
        {prv2 : PositiveRandomVariable rv_X2} :
    rv_le rv_X1 rv_X2 ->
    Rbar_le (Expectation_posRV rv_X1) (Expectation_posRV rv_X2).
  Proof.
    intros.
    unfold Expectation_posRV, SimpleExpectationSup.
    unfold Lub_Rbar.
    repeat match goal with
             [|- context [proj1_sig ?x]] => destruct x; simpl
           end.
    refine (is_lub_Rbar_subset _ _ _ _ _ i0 i); intros.
    destruct H0 as [rvx [? [? [? ?]]]].
    exists rvx; exists x2; exists x3.
    split; trivial.
    unfold BoundedPositiveRandomVariable in *.
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

  Lemma Expectation_posRV_const (c : R) (nnc : 0 <= c) :
    (@Expectation_posRV (const c) (prvconst _ nnc)) = c.
  Proof.
    unfold Expectation_posRV, SimpleExpectationSup.
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
      unfold BoundedPositiveRandomVariable in H1.
      destruct H1.
      generalize (SimpleExpectation_le x1 (const c) H3); intros.
      rewrite H2 in H4.
      rewrite SimpleExpectation_const in H4.
      now simpl.
    - exists (const c).
      exists (rvconst _ _ c).
      exists (srvconst c).
      split; trivial; [| apply SimpleExpectation_const].
      unfold BoundedPositiveRandomVariable.
      split; [ apply (prvconst c nnc) |].
      unfold rv_le, const; intros ?.
      lra.
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

  Lemma Expectation_pos_posRV (rv_X : Ts -> R) 
        {prv : PositiveRandomVariable rv_X} :
    Expectation rv_X = Some (Expectation_posRV rv_X).
  Proof.
    unfold Expectation.
    replace (Expectation_posRV (pos_fun_part rv_X)) with (Expectation_posRV rv_X).
    - replace (Expectation_posRV (neg_fun_part rv_X)) with (Finite 0).
      + unfold Rbar_minus', Rbar_plus', Rbar_opp.
        match_destr.
        f_equal; apply Rbar_finite_eq; lra.
      + generalize (neg_fun_part_pos rv_X); intros.
        assert (0 <= 0) by lra.
        generalize (@prvconst Ts 0 H0); intros.
        rewrite Expectation_posRV_ext with (prv2 := H1).
        symmetry.
        apply (Expectation_posRV_const 0 H0).
        now symmetry.
    - apply Expectation_posRV_ext; trivial.
      now apply pos_fun_part_pos.
  Qed.

  Lemma Expectation_simple
        (rv_X : Ts -> R)
        {rvx_rv : RandomVariable dom borel_sa rv_X}
        {srv:SimpleRandomVariable rv_X} :
    Expectation rv_X = Some (Finite (SimpleExpectation rv_X)).
  Proof.
    unfold Expectation.
    repeat erewrite srv_Expectation_posRV.
    - simpl.
      f_equal.
      rewrite oppSimpleExpectation.
      rewrite sumSimpleExpectation; trivial.
      + f_equal.
        apply SimpleExpectation_ext.
        symmetry.
        apply rv_pos_neg_id.
      + now apply positive_part_rv.
      + apply rvopp_rv.
        now apply negative_part_rv.
    - now apply negative_part_rv.
    - now apply positive_part_rv.
  Qed.

  Lemma Expectation_const (c:R) :
    Expectation (const c) = Some (Finite c).
  Proof.
    now rewrite (Expectation_simple _ (srv:=srvconst c)), SimpleExpectation_const.
  Qed.

  Lemma z_le_z : 0 <= 0.
  Proof.
    lra.
  Qed.

  Lemma Expectation_posRV_const0 :
    (@Expectation_posRV (const 0) (prvconst _ z_le_z)) = 0.
  Proof.
    apply Expectation_posRV_const.
  Qed.

  Lemma Expectation_posRV_pos
        (rv_X : Ts -> R)
        {prv : PositiveRandomVariable rv_X} :
    Rbar_le 0 (Expectation_posRV rv_X).
  Proof.
    rewrite <- Expectation_posRV_const0.
    apply Expectation_posRV_le; trivial.
  Qed.

  Lemma Finite_Expectation_posRV_le 
        (rv_X1 rv_X2 : Ts -> R)
        (prv1 : PositiveRandomVariable rv_X1)
        (prv2 : PositiveRandomVariable rv_X2) :
    rv_le rv_X1 rv_X2 ->
    is_finite (Expectation_posRV rv_X2) ->
    is_finite (Expectation_posRV rv_X1).
  Proof.
    intros.
    generalize (Expectation_posRV_le rv_X1 rv_X2 H); intros.
    assert (0 <= 0) by lra.
    generalize (@Expectation_posRV_le (const 0) rv_X1 (prvconst _ H2) _); intros.
    cut_to H3.
    generalize (Expectation_posRV_const 0 H2); intros.
    rewrite H4 in H3.
    unfold is_finite in H0.
    apply (bounded_is_finite 0 (real (Expectation_posRV rv_X2))); trivial.
    now rewrite H0.
    unfold rv_le.
    now unfold PositiveRandomVariable in prv1.
  Qed.

  Lemma Expectation_abs_then_finite (rv_X:Ts->R)  
        {rv : RandomVariable dom borel_sa rv_X}
    :  match Expectation (rvabs rv_X) with
       | Some (Finite _) => True
       | _ => False
       end ->
       match Expectation rv_X with
       | Some (Finite _) => True
       | _ => False
       end.
  Proof.
    rewrite Expectation_pos_posRV with (prv := prvabs _).
    unfold Expectation.
    intros HH.
    match_case_in HH
    ; [intros r eqq | intros eqq | intros eqq]
    ; rewrite eqq in HH
    ; try contradiction.

    unfold Rbar_minus', Rbar_plus'.
    assert (fin:is_finite (Expectation_posRV (rvabs rv_X)))
      by (rewrite eqq; reflexivity).

    generalize (pos_fun_part_le rv_X); intros le1.
    generalize (Finite_Expectation_posRV_le _ _ _ _ le1 fin)
    ; intros fin1.
    rewrite <- fin1.
    generalize (neg_fun_part_le rv_X); intros le2.
    generalize (Finite_Expectation_posRV_le _ _ _ _ le2 fin)
    ; intros fin2.
    rewrite <- fin2.
    simpl; trivial.
  Qed.

  Lemma pos_part_le 
        (rvp rvn : Ts -> R)
        (p : PositiveRandomVariable rvp)
        (n : PositiveRandomVariable rvn) :
    rv_le (fun x : Ts => pos_fun_part (rvminus rvp rvn) x) rvp.
  Proof.
    unfold rv_le, pos_fun_part, rvminus.
    intros x.
    simpl.
    unfold rvplus, rvopp, rvscale.
    unfold PositiveRandomVariable in *.
    specialize (p x); specialize (n x).
    apply Rmax_lub; lra.
  Qed.

  Lemma neg_part_le 
        (rvp rvn : Ts -> R)
        (p : PositiveRandomVariable rvp)
        (n : PositiveRandomVariable rvn) :
    rv_le (fun x : Ts => neg_fun_part (rvminus rvp rvn) x) rvn.
  Proof.
    unfold rv_le, pos_fun_part, rvminus.
    intros x.
    simpl.
    unfold rvplus, rvopp, rvscale.
    unfold PositiveRandomVariable in *.
    specialize (p x); specialize (n x).
    apply Rmax_lub; lra.
  Qed.


  (* sequence of simple random variables monotonically converging to X>=0 *)
  Definition simple_approx (X:Ts->R) (n:nat) : Ts -> R
    := fun ω : Ts =>
         let Xw := X ω in
         if Rge_dec Xw (INR n) then (INR n) else
           match find (fun start => if Rge_dec Xw start then true else false) 
                      (rev (map (fun x => INR x / (2^n)) (seq 0 (n*(2^n))))) with
           | Some r => r
           | None => INR 0
           end.

  Definition interval_dec : forall r r1 r2 :R, {r1 <= r < r2} + {~(r1 <= r < r2)}.
  Proof.
    intros.
    destruct (Rle_dec r1 r)
    ; destruct (Rlt_dec r r2)
    ; eauto 3
    ; right; lra.
  Defined.

  Lemma pow2_pos n : 0 < pow 2 n.
  Proof.
    apply pow_lt.
    lra.
  Qed.

  Lemma pow_nzero a n : a <> 0 -> pow a n <> 0.
  Proof.
    intros.
    induction n; simpl.
    - lra.
    - intros eqq.
      apply Rmult_integral in eqq.
      intuition.
  Qed.

  Lemma pow2_nzero n : pow 2 n <> 0.
  Proof.
    apply pow_nzero.
    lra.
  Qed.

  Lemma simple_approx_vals (X:Ts->R) (n:nat) :
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

  Program Instance simple_approx_srv (X:Ts->R) (n:nat) : 
    SimpleRandomVariable (simple_approx X n) :=
    {srv_vals := map (fun x => INR x / (2^n)) (seq 0 (S (n*(2^n))))}.
  Next Obligation.
    apply simple_approx_vals.
  Qed.

  Lemma simple_approx_preimage_inf (X:Ts -> R) (n:nat) :
    PositiveRandomVariable X ->
    forall (omega:Ts), simple_approx X n omega = INR n <-> X omega >= INR n.
  Proof.
    unfold PositiveRandomVariable; intro posX.
    intros.
    unfold simple_approx.
    match_case; intros.
    - tauto.
    - split; [|lra].
      generalize (Rnot_ge_lt _ _ n0); intros.
      match_case_in H1; intros.
      + rewrite H2 in H1.
        apply find_some in H2.
        destruct H2.
        match_case_in H3; intros.
        * invcs H1.
          lra.
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
          -- lra.
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
          apply Rle_ge.
          apply posX.
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

  Lemma simple_approx_preimage_fin0 (X:Ts -> R) (n:nat) :
    PositiveRandomVariable X ->
    forall (omega:Ts) (k:nat),
      X omega < INR n ->
      (simple_approx X n omega)*(2^n) = (INR k) <->
      (INR k) <= (X omega)*(2^n) < (INR (S k)).
  Proof.
    unfold PositiveRandomVariable.
    intros posX.
    intros omega k.
    intros Xlt.
    unfold simple_approx.
    match_destr; [lra | ].
    clear n0.
    assert (pos1:(n * 2 ^ n > 0)%nat).
    {
      apply NPeano.Nat.mul_pos_pos.
      - destruct n; try lia.
        simpl in Xlt.
        specialize (posX omega).
        lra.
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
          -- apply Rge_le in r0.
             apply -> Rcomplements.Rle_div_l; trivial.
             apply pow2_pos.
          -- apply  Rcomplements.Rlt_div_r; trivial.
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
                   unfold Rdiv.
                   rewrite Rmult_assoc.
                   rewrite pow_INR.
                   simpl.
                   rewrite Rinv_r.
                   + lra.
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
                         lra.
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
          apply Rge_le in r0.
          apply Rcomplements.Rle_div_l in r0 ; [| apply pow2_pos].
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
                    apply Rle_ge.
                    apply  Rcomplements.Rle_div_l
                    ; [ apply pow2_pos |].
                    lra.
                  + rewrite app_length; simpl.
                    lia.
                - apply INR_lt.
                  eapply Rle_lt_trans
                  ; try eapply le1.
                  apply  Rcomplements.Rlt_div_r ; [ apply pow2_pos |].
                  rewrite mult_INR.
                  rewrite pow_INR.
                  unfold Rdiv.
                  simpl.
                  rewrite Rmult_assoc.
                  rewrite Rinv_r.
                  + now rewrite Rmult_1_r.
                  + apply pow_nzero; lra.
              }
            - assert (le2:(S k <= length d)%nat) by lia.
              apply le_INR in le2.
              lra.
          }            
    - generalize (find_none _ _ H); intros HH.
      specialize (HH 0).
      cut_to HH.
      + match_destr_in HH.
        specialize (posX omega).
        lra.
      + apply -> in_rev.
        apply in_map_iff.
        exists 0%nat.
        split.
        * simpl; lra.
        * apply in_seq.
          simpl.
          split; trivial.
  Qed.

  Lemma simple_approx_preimage_fin (X:Ts -> R) (n:nat) :
    PositiveRandomVariable X ->
    forall (omega:Ts), 
      X omega < INR n ->
      forall (k:nat),            
        simple_approx X n omega = (INR k)/2^n <->
        (INR k)/2^n <= X omega < (INR (S k))/2^n.
  Proof.
    intros.
    destruct (simple_approx_preimage_fin0 X n H omega k H0) as [HH1 HH2].
    split; intros HH.
    - cut_to HH1.
      + destruct HH1 as [le1 lt1].
        split; intros.
        * apply  Rcomplements.Rle_div_l; [ apply pow2_pos |]; trivial.
        * apply  Rcomplements.Rlt_div_r; [ apply pow2_pos |]; trivial.
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
        * apply  Rcomplements.Rle_div_l; [ apply pow2_pos |]; trivial.
        * apply  Rcomplements.Rlt_div_r; [ apply pow2_pos |]; trivial.
  Qed.       
  
  Lemma simple_approx_preimage_fin2 (X:Ts -> R) (n:nat) :
    PositiveRandomVariable X ->
    forall (omega:Ts), 
    forall (k:nat), (k < n*2^n)%nat ->
             simple_approx X n omega = (INR k)/2^n <->
             (INR k)/2^n <= X omega < (INR (S k))/2^n.
  Proof.
    unfold PositiveRandomVariable.
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
      + apply Rnot_ge_lt in n0.
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
            split; [lra | ].
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
                  * lra.
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
                         lra.
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
             specialize (posX omega).
             lra.
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
      + apply Rge_le in r.
        apply Rle_not_gt in r.
        elim r.
        apply Rlt_gt.
        eapply Rlt_le_trans; try eapply lt2.
        apply  Rcomplements.Rle_div_r.
        * apply Rinv_0_lt_compat.
          apply pow_lt; lra.
        * unfold Rdiv.
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
                    match_destr_in Fl1.
                    lra.
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
              apply  Rcomplements.Rlt_div_r in lt2
              ; [| apply pow_lt; lra].
              apply Rge_le in r.
              apply  Rcomplements.Rle_div_l in r
              ; [| apply pow_lt; lra].
              lra.
          }            
        * generalize (find_none _ _ eqq1); intros HH.
          specialize (HH 0).
          { cut_to HH.
            + match_destr_in HH.
              specialize (posX omega).
              lra.
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
  
  Lemma simple_approx_le (X:Ts->R) (posX : PositiveRandomVariable X) :
    forall n ω, simple_approx X n ω <= X ω.
  Proof.
    unfold simple_approx; intros.
    match_case; intros.
    - lra.
    - match_case; intros.
      apply find_some in H0.
      destruct H0.
      match_destr_in H1.
      lra.
  Qed.

  Lemma simple_approx_exists (X:Ts -> R) (n:nat) :
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

  Lemma simple_approx_pos (X:Ts->R) (n:nat) (ω:Ts) :
    simple_approx X n ω >= 0.
  Proof.
    generalize (simple_approx_exists X n ω); intros.
    destruct H.
    rewrite H.
    unfold Rdiv.
    apply Rle_ge.
    apply Rmult_le_reg_r with (r:= 2^n).
    apply pow2_pos.
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    ring_simplify.
    apply pos_INR.
    apply pow2_nzero.
  Qed.

  Instance simple_approx_posrv (X:Ts->R) (n:nat) : PositiveRandomVariable (simple_approx X n).
  Proof.
    unfold PositiveRandomVariable; intros.
    apply Rge_le.
    apply simple_approx_pos.
  Qed.

  Lemma simple_approx_inf_event (X:Ts -> R) (n:nat)
        (posx : PositiveRandomVariable X) :
    event_equiv (event_preimage (simple_approx X n) (event_singleton (INR n)))
                (event_preimage X (fun r => r >= INR n)).
  Proof.
    generalize (simple_approx_preimage_inf X n posx); intros.
    unfold event_equiv, event_preimage, event_singleton.
    apply H.
  Qed.

  Lemma simple_approx_fin_event (X:Ts -> R) (n:nat) 
        (posx : PositiveRandomVariable X) :
    forall (k : nat), 
      (k < n*2^n)%nat ->
      event_equiv (event_preimage (simple_approx X n) (event_singleton ((INR k)/2^n)))
                  (event_preimage X (fun z => (INR k)/2^n <= z < (INR (S k))/2^n)).
  Proof.
    unfold event_equiv, event_preimage, event_singleton.
    intros.
    now apply simple_approx_preimage_fin2.
  Qed.

  Lemma simple_approx_inf_measurable (X:Ts -> R) (n:nat)
        (posx : PositiveRandomVariable X)
        (ranx : RandomVariable dom borel_sa X) :
    sa_sigma (event_preimage (simple_approx X n) (event_singleton (INR n))).
  Proof.
    generalize (simple_approx_inf_event X n posx); intros.
    rewrite H.
    apply sa_le_ge.
    apply borel_sa_preimage2; intros.
    now apply rv_preimage.
  Qed.

  Lemma simple_approx_fin_measurable (X:Ts -> R) (n:nat)
        (posx : PositiveRandomVariable X)
        (ranx : RandomVariable dom borel_sa X) :
    forall (k : nat), 
      (k < n*2^n)%nat ->
      sa_sigma (event_preimage (simple_approx X n) (event_singleton ((INR k)/2^n))).
  Proof.
    intros.
    generalize (simple_approx_fin_event X n posx k H); intros.
    rewrite H0.
    assert (event_equiv (fun z : R => INR k / 2 ^ n <= z < INR (S k) / 2 ^ n)
                        (event_inter (fun z : R => z >= INR k / 2 ^ n)
                                     (fun z : R => z < INR (S k) / 2 ^ n))).
    - intros x.
      unfold event_inter.
      lra.
    - rewrite H1.
      unfold event_preimage.
      assert (event_equiv  (fun omega : Ts =>
                              event_inter (fun z : R => z >= INR k / 2 ^ n) 
                                          (fun z : R => z < INR (S k) / 2 ^ n)
                                          (X omega))
                           (event_inter (fun omega => X omega >= INR k / 2^n)
                                        (fun omega => X omega < INR (S k) / 2^n))).
      + intros x.
        unfold event_inter.
        lra.
      + rewrite H2.
        apply sa_inter.
        * apply sa_le_ge.
          apply borel_sa_preimage2; intros.
          now apply rv_preimage.
        * apply sa_le_lt.
          apply borel_sa_preimage2; intros.
          now apply rv_preimage.
  Qed.

  Lemma simple_approx_range_event (X : Ts -> R) (n:nat) (r : R) :
    let rvals :=  filter (fun z => if Rle_dec z r then true else false)
                         (map (fun x : nat => INR x / 2 ^ n) (seq 0 (S (n * 2 ^ n)))) in
    event_equiv (fun omega : Ts => simple_approx X n omega <= r)
                (list_union (map (fun z => (fun omega => simple_approx X n omega = z))
                                 rvals)).
  Proof.
    generalize (simple_approx_vals X n); intros.
    unfold event_equiv; intros.
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
        * match_destr; congruence.
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

  Instance simple_approx_rv (X : Ts -> R)
           {posx : PositiveRandomVariable X} 
           {rvx : RandomVariable dom borel_sa X} 
    : forall (n:nat), RandomVariable dom borel_sa (simple_approx X n).
  Proof.
    unfold RandomVariable.
    intros.
    apply borel_sa_preimage; trivial.
    intros.
    generalize (simple_approx_vals X n); intros.
    generalize (simple_approx_range_event X n r); intros.
    rewrite H1.
    apply sa_list_union.
    intros.
    apply in_map_iff in H2.
    destruct H2 as [x0 [? ?]].
    subst.
    rewrite filter_In in H3.
    destruct H3.
    apply in_map_iff in H2.
    destruct H2 as [k [? ?]].
    subst.
    rewrite in_seq in H4.
    destruct H4.
    simpl in H4.
    rewrite Nat.lt_succ_r in H4.
    rewrite Nat.le_lteq in H4.
    destruct H4.
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

  Lemma simple_approx_bound (X:Ts -> R) (n:nat) :
    PositiveRandomVariable X ->
    forall (omega:Ts), 
      X omega < INR n ->
      forall (k:nat),  (INR k)/2^n <= X omega ->
                (INR k)/2^n <= simple_approx X n omega .
  Proof.
    intro posX.
    intros.
    induction k.
    - simpl.
      unfold Rdiv.
      rewrite Rmult_0_l.
      apply Rge_le.
      apply simple_approx_pos.
    - cut_to IHk.
      + generalize (simple_approx_preimage_fin X n posX omega H); intros.
        generalize (simple_approx_exists X n omega); intros.
        destruct H2.
        specialize (H1 k).
        destruct H1.
        apply imply_to_or in H1.
        destruct H1; [|lra].
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
      + eapply Rle_trans; try eapply H0.
        rewrite S_INR.
        apply Rmult_le_compat_r.
        * left.
          apply Rinv_0_lt_compat.
          apply pow2_pos.
        * lra.
  Qed.

  Lemma simple_approx_increasing  (X:Ts->R) (posX : PositiveRandomVariable X) 
        (n:nat) (ω : Ts) :
    simple_approx X n ω <= simple_approx X (S n) ω.
  Proof.
    intros.
    generalize (simple_approx_preimage_inf X n posX ω); intros.
    generalize (simple_approx_preimage_inf X (S n) posX ω); intros.
    destruct H; destruct H0.
    case (Rge_dec (X ω) (INR n)); intros.
    - specialize (H1 r).
      case (Rge_dec (X ω) (INR (S n))); intros.        
      + specialize (H2 r0).
        rewrite S_INR in H2.
        lra.
      + rewrite H1.
        apply Rnot_ge_lt in n0.
        assert (INR n = INR (n*2^(S n))/2^(S n)).
        * rewrite mult_INR, pow_INR.
          replace (INR 2) with (2) by easy.
          field.
          apply pow2_nzero.
        * rewrite H3 in r.
          apply Rge_le in r.
          generalize (simple_approx_bound X (S n) posX ω n0 (n * 2 ^ S n) r); intros.
          lra.
    - apply Rnot_ge_lt in n0.
      assert (X ω < INR (S n)).
      apply Rlt_trans with (r2 := INR n); trivial; apply lt_INR; lia.
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
  
  Lemma simple_approx_increasing2  (X:Ts->R) (posX : PositiveRandomVariable X) 
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

  Lemma simple_approx_delta (X:Ts -> R) (n:nat) (ω : Ts) (posX : PositiveRandomVariable X) :
    (X ω < INR n) -> (X ω - simple_approx X n ω) < / (2^n).
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
    lra.
  Qed.

  Lemma simple_approx_lim (X:Ts -> R) (posX : PositiveRandomVariable X) (eps : posreal) :
    forall (ω : Ts), exists (n:nat), X ω - simple_approx X n ω < eps.
  Proof.
    intros.
    assert (exists n, (2^n > Z.to_nat (up (/ eps))))%nat.
    - exists (S (Nat.log2 (Z.to_nat (up (/ eps))))).
      unfold PositiveRandomVariable in posX.
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
      + apply Rlt_le_trans with (r2 := INR (Z.to_nat (up (X  ω)))).
        * rewrite INR_up_pos.
          apply archimed.
          apply Rle_ge.
          apply posX.
        * apply le_INR.
          apply Max.le_max_r.
  Qed.

  Lemma simple_approx_lim_seq (X:Ts -> R) (posX : PositiveRandomVariable X) :
    forall (ω : Ts), is_lim_seq(fun n => simple_approx X n ω) (X ω).
  Proof.
    intros.
    rewrite <- is_lim_seq_spec.
    unfold is_lim_seq'; intros.
    unfold Hierarchy.eventually.
    generalize (simple_approx_lim X posX eps ω); intros.
    destruct H.
    exists x.
    intros.
    generalize (simple_approx_le X posX n ω); intros. 
    rewrite Rabs_minus_sym.
    rewrite Rabs_right; [|lra].
    generalize (simple_approx_increasing2 X posX (n-x)%nat ω x); intros.
    replace (x + (n-x))%nat with (n) in H2 by lia.
    lra.
  Qed.

  Lemma simple_Expectation_posRV
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {prv : PositiveRandomVariable rv_X} 
        {srv : SimpleRandomVariable rv_X} :
    Finite (SimpleExpectation rv_X) = Expectation_posRV rv_X.
  Proof.
    unfold Expectation_posRV.
    unfold SimpleExpectationSup.
    symmetry.
    apply is_lub_Rbar_unique.
    unfold is_lub_Rbar.
    unfold is_ub_Rbar.
    split; intros.
    - destruct H as [rvx2 [rv2 [srv2 [? ?]]]].
      unfold BoundedPositiveRandomVariable in H.
      destruct H.
      simpl.
      rewrite <- H0.
      now apply SimpleExpectation_le.
    - apply H.
      unfold BoundedPositiveRandomVariable.
      exists rv_X, rv, srv.
      split; now split.
  Qed.

  Lemma simple_expectation_real 
        (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {prv : PositiveRandomVariable rv_X} 
        {srv : SimpleRandomVariable rv_X} :
    is_finite (Expectation_posRV rv_X).
  Proof.
    rewrite <- (@simple_Expectation_posRV rv_X rv prv srv).
    unfold is_finite.
    reflexivity.
  Qed.


  Lemma f_ge_g_le0_eq (f g : Ts -> R) :
    (event_equiv (fun omega : Ts => f omega >= g omega)
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
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: PositiveRandomVariable cphi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) X) ->
      (forall (omega:Ts), cphi omega = 0 \/ cphi omega < X omega) ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
      (forall (n:nat), sa_sigma (fun (omega:Ts) => (Xn n omega) >= cphi omega)) /\
      event_equiv (union_of_collection (fun n => fun (omega:Ts) => (Xn n omega) >= cphi omega)) 
                  Ω.
  Proof.
    intros.
    split.
    - intros x.
      now apply sigma_f_ge_g. 
    - assert (event_equiv (event_union (fun (omega : Ts) => cphi omega < X omega)
                                       (fun (omega : Ts) => cphi omega = 0))
                          Ω).
      + intros x.
        unfold Ω, event_union.
        specialize (H0 x).
        lra.
      + rewrite <- H2.
        intros x.
        specialize (H2 x).
        unfold Ω in H2.
        split; [tauto | ].
        intros.
        unfold union_of_collection; intros.
        specialize (H1 x).
        rewrite <- is_lim_seq_spec in H1.
        unfold is_lim_seq' in H1.
        specialize (H0 x).
        unfold PositiveRandomVariable in posphi.
        destruct H0.
        * exists (0%nat).
          rewrite H0.
          unfold PositiveRandomVariable in Xn_pos.
          specialize (Xn_pos 0%nat x).
          lra.
        * assert (0 < X x - cphi x) by lra.
          specialize (H1 (mkposreal _ H4)).
          destruct H1.
          exists x0.
          specialize (H1 x0).
          simpl in H1.
          cut_to H1; [|lia].
          specialize (H x0 x).
          rewrite Rabs_left1 in H1; lra.
  Qed.

  Lemma lim_prob
        (En : nat -> event Ts)
        (E : event Ts) :
    (forall (n:nat), sa_sigma (En n)) ->
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
      + intros ? inn.
        apply in_map_iff in inn.
        destruct inn as [?[??]]; subst.
        now apply sa_make_collection_disjoint.
      + apply collection_take_preserves_disjoint.
        apply make_collection_disjoint_disjoint.
    - apply (is_lim_seq_ext (fun n : nat => sum_f_R0 (fun j : nat => ps_P (make_collection_disjoint En j)) n)).
      + intros.
        now rewrite sum_f_R0_sum_f_R0'.
      + rewrite infinite_sum_is_lim_seq.
        rewrite infinite_sum_infinite_sum'.
        assert (event_equiv E (union_of_collection (make_collection_disjoint En))).
        * rewrite <- H1.
          apply make_collection_disjoint_union.
        * rewrite H2.
          apply ps_countable_disjoint_union.
          -- now apply sa_make_collection_disjoint.
          -- apply make_collection_disjoint_disjoint.
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
  
  Lemma simpleFunEventIndicator
        (phi : Ts -> R)
        (sphi : SimpleRandomVariable phi)
        {P : event Ts}
        (dec:forall x, {P x} + {~ P x}) :
    SimpleExpectation (rvmult phi (EventIndicator dec)) =
    list_sum (map (fun v => v * (ps_P (event_inter
                                      (event_preimage phi (event_singleton v))
                                      P)))
                  (nodup Req_EM_T srv_vals)).
  Proof.
    unfold SimpleExpectation.
    simpl.
    transitivity (list_sum
                    (map (fun v : R => v * ps_P (event_preimage (rvmult phi (EventIndicator dec)) (event_singleton v))) (nodup Req_EM_T srv_vals))).
    - rewrite list_prod_swap; simpl.
      rewrite map_map; simpl.
      rewrite app_nil_r.
      rewrite map_app.
      repeat rewrite map_map; simpl.
      rewrite (map_ext (fun x : R => x * 0) (fun _ : R => 0))
        by (intros; lra).
      rewrite (map_ext (fun x : R => x * 1) (fun x : R => x))
        by (intros; lra).
      rewrite map_id.
      generalize srv_vals at 1.
      induction l; simpl; trivial.
      match_destr; simpl.
      rewrite IHl.
      lra.
    - f_equal.
      apply map_ext; intros.
      unfold event_preimage.
      unfold event_inter.
      unfold rvmult, event_singleton.
      unfold EventIndicator.
      destruct (Req_EM_T a 0).
      + subst; lra.
      + f_equal.
        apply ps_proper; intros x.
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
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posphi: PositiveRandomVariable cphi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) X) ->
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ cphi omega < X omega) ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
      is_lim_seq (fun n => Expectation_posRV 
                          (rvmult cphi 
                                  (EventIndicator
                                     (fun omega => Rge_dec (Xn n omega) (cphi omega))))) 
                 (Expectation_posRV cphi).
  Proof.
    intros.
    rewrite <- (simple_Expectation_posRV cphi).
    assert (forall n,  sa_sigma (fun omega : Ts => Xn n omega >= cphi omega)).
    intros.
    now apply sigma_f_ge_g.
    apply (is_lim_seq_ext 
             (fun n => SimpleExpectation 
                      (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega)))))).
    - intros.
      rewrite <- simple_Expectation_posRV with (srv := (srvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))); trivial.
      apply rvmult_rv; trivial.
      now apply EventIndicator_rv.
    - apply (is_lim_seq_ext 
               (fun (n:nat) =>
                  (list_sum (map (fun v => v * (ps_P (event_inter
                                                     (event_preimage cphi (event_singleton v))
                                                     (fun omega => Xn n omega >= cphi omega))))
                                 (nodup Req_EM_T srv_vals))))).
      intros.
      symmetry.
      apply simpleFunEventIndicator.
      unfold SimpleExpectation.
      generalize (is_lim_seq_list_sum
                    (map
                       (fun v : R => fun n => 
                                    v *
                                    ps_P
                                      (event_inter (event_preimage cphi (event_singleton v))
                                                   (fun omega : Ts => Xn n omega >= cphi omega)))
                       (nodup Req_EM_T srv_vals))
                    (map (fun v : R => v * ps_P (event_preimage cphi (event_singleton v)))
                         (nodup Req_EM_T srv_vals)))
      ; intros HH.
      cut_to HH.
      + eapply is_lim_seq_ext; try eapply HH.
        intros; simpl.
        now rewrite map_map.
      + clear HH.
        rewrite map_map.
        rewrite <- Forall2_map.
        apply Forall2_refl_in.
        rewrite Forall_forall; intros.
        replace (Finite (x * ps_P (event_preimage cphi (event_singleton x)))) with
            (Rbar_mult x (ps_P (event_preimage cphi (event_singleton x))))
          by reflexivity.
        apply is_lim_seq_scal_l.
        apply lim_prob.
        * intros.
          apply sa_inter; [|trivial].
          now apply sa_singleton.
        * intros.
          apply event_inter_sub_proper; [reflexivity | ].
          intros xx.
          unfold rv_le in H0.
          specialize (H0 n xx).
          lra.
        * rewrite <- event_inter_countable_union_distr.
          assert (event_equiv (union_of_collection (fun (n : nat) (omega : Ts) => Xn n omega >= cphi omega)) Ω).
          apply monotone_convergence_Ec with (X := X); trivial.
          -- rewrite H5.
             apply event_inter_true_r.
  Qed.

  Lemma monotone_convergence0_cphi
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (cphi : Ts -> R)

        (rvx : RandomVariable dom borel_sa X)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable cphi)
        (phi_rv : RandomVariable dom borel_sa cphi)         

        (posX: PositiveRandomVariable X) 
        (posphi: PositiveRandomVariable cphi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) X) ->
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (omega:Ts), cphi omega = 0 \/ cphi omega < X omega) ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
      (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
      Rbar_le (Expectation_posRV cphi)
              (Lim_seq (fun n => real (Expectation_posRV (Xn n)))).
  Proof.
    intros.
    generalize (monotone_convergence_E_phi_lim X Xn cphi Xn_rv sphi phi_rv posphi Xn_pos H H0 H1 H2); intros.
    apply is_lim_seq_unique in H4.
    rewrite <- H4.
    apply Lim_seq_le_loc.
    unfold Hierarchy.eventually.
    exists (0%nat); intros.
    assert (PositiveRandomVariable
              (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
    now apply indicator_prod_pos.
    assert (RandomVariable _ borel_sa  (rvmult cphi
                                                  (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
    -  apply rvmult_rv; trivial.
      apply EventIndicator_rv.
      now apply sigma_f_ge_g.
    - generalize (Expectation_posRV_le
                    (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))
                    (Xn n)); intros.
      cut_to H8.
      + rewrite <- H3 in H8.
        assert (is_finite (Expectation_posRV
                             (rvmult cphi
                                     (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega)))))).
        * assert (SimpleRandomVariable  (rvmult cphi (EventIndicator (fun omega : Ts => Rge_dec (Xn n omega) (cphi omega))))).
          -- apply srvmult; trivial.
             apply EventIndicator_srv.
          -- rewrite <- simple_Expectation_posRV with (srv := X0).
             ++ now unfold is_finite.
             ++ apply rvmult_rv; trivial.
                apply EventIndicator_rv.
                now apply sigma_f_ge_g.
        * rewrite <- H9 in H8.
          now simpl in H8.
      + unfold rv_le; intros x.
        unfold rvmult, EventIndicator.
        destruct (Rge_dec (Xn n x) (cphi x)); [lra | ].
        unfold PositiveRandomVariable in Xn_pos.
        generalize (Xn_pos n x); lra.
  Qed.

  Lemma monotone_convergence0_Rbar (c:R)
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (phi : Ts -> R)

        (rvx : RandomVariable dom borel_sa X)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posX: PositiveRandomVariable X) 
        (posphi: PositiveRandomVariable phi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
    :

      (forall (n:nat), rv_le (Xn n) X) ->
      (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
      (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
      rv_le phi X ->
      (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
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
      destruct H4.
      apply Rmult_le_pos; trivial.
      lra.
    - generalize (monotone_convergence0_cphi X Xn cphi rvx Xn_rv 
                                             (srvscale c phi) (rvscale_rv _ c phi phi_rv) posX H5 Xn_pos).
      intros.
      cut_to H6; trivial.
      + destruct H4.
        rewrite <- (Expectation_posRV_scale (mkposreal c H4)); apply H6.
      + intros.
        unfold cphi, rvscale.
        destruct H4.
        unfold rv_le in H2.
        specialize (H2 omega).
        unfold PositiveRandomVariable in posphi.
        specialize (posphi omega).
        unfold Rle in posphi.
        destruct posphi.
        * right.
          assert (c * phi omega < phi omega); [|lra].
          apply Rplus_lt_reg_l with (r := - (c * phi omega)).
          ring_simplify.
          replace (- c * phi omega + phi omega) with ((1-c)*phi omega) by lra.
          apply Rmult_lt_0_compat; [lra | trivial].
        * left.
          rewrite <- H8.
          lra.
  Qed.

  Lemma Lim_seq_Expectation_posRV_pos
        (rvxn : nat -> Ts -> R) 
        (posvn: forall n, PositiveRandomVariable (rvxn n)) :
    Rbar_le 0 (Lim_seq (fun n : nat => Expectation_posRV (rvxn n))).
  Proof.
    replace (Finite 0) with (Lim_seq (fun _ => 0)) by apply Lim_seq_const.
    apply Lim_seq_le_loc.
    unfold Hierarchy.eventually.
    exists (0%nat); intros.
    generalize (Expectation_posRV_pos (rvxn n)); intros.
    case_eq (Expectation_posRV (rvxn n)); intros.
    - now rewrite H1 in H0.
    - simpl; lra.
    - simpl; lra.
  Qed.      

  Lemma Lim_seq_Expectation_m_infty
        (rvxn : nat -> Ts -> R) 
        (posvn: forall n, PositiveRandomVariable (rvxn n)) :
    Lim_seq (fun n : nat => Expectation_posRV (rvxn n)) = m_infty -> False.
  Proof.
    generalize (Lim_seq_Expectation_posRV_pos rvxn posvn); intros.
    rewrite  H0 in H.
    now simpl in H.
  Qed.

  Lemma monotone_convergence00         
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (phi : Ts -> R)

        (rvx : RandomVariable dom borel_sa X)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (sphi : SimpleRandomVariable phi)
        (phi_rv : RandomVariable dom borel_sa phi)         

        (posX: PositiveRandomVariable X) 
        (posphi: PositiveRandomVariable phi)
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :

    (forall (n:nat), rv_le (Xn n) X) ->
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
    rv_le phi X ->
    (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
    Rbar_le 
      (Expectation_posRV phi)
      (Lim_seq (fun n =>  real (Expectation_posRV (Xn n)))).
  Proof.
    assert (is_lim_seq (fun n => (1-/(2+INR n)) * (real (Expectation_posRV phi)))
                       (real (Expectation_posRV phi))).
    - replace (real (@Expectation_posRV phi posphi)) with 
          (1 * (real (@Expectation_posRV phi posphi))) at 1.
      + apply is_lim_seq_scal_r with (lu := Finite 1) (a := (@Expectation_posRV phi posphi)).
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
             assert (is_finite (Expectation_posRV phi)) by (now apply simple_expectation_real).
             ++ rewrite <- H8 in H7; now simpl in H7.
             ++ split; [trivial | simpl].
                apply Rplus_lt_reg_l with (r := -1).
                ring_simplify.
                apply Ropp_lt_gt_0_contravar.
                apply  Rinv_0_lt_compat.
                generalize (pos_INR n); lra.
        * assert (is_finite (Expectation_posRV phi))  by (now apply simple_expectation_real).
          rewrite <- H6.
          apply H.
        * apply is_lim_seq_const.
      + now destruct (Expectation_posRV phi).
      + now apply Lim_seq_Expectation_m_infty in H5.
  Qed.

  Lemma monotone_convergence
        (X : Ts -> R )
        (Xn : nat -> Ts -> R)
        (rvx : RandomVariable dom borel_sa X)
        (posX: PositiveRandomVariable X) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :
    (forall (n:nat), rv_le (Xn n) X) ->
    (forall (n:nat), rv_le (Xn n) (Xn (S n))) ->
    (forall (n:nat), is_finite (Expectation_posRV (Xn n))) ->
    (forall (omega:Ts), is_lim_seq (fun n => Xn n omega) (X omega)) ->
    Lim_seq (fun n => Expectation_posRV (Xn n)) =  (Expectation_posRV X).
  Proof.
    generalize Expectation_posRV_le; intros.
    assert (forall (n:nat), (Rbar_le (Expectation_posRV (Xn n)) (Expectation_posRV X))).
    - intros.
      apply H; trivial.
    - assert (forall (n:nat), (Rbar_le (Expectation_posRV (Xn n)) (Expectation_posRV (Xn (S n))))).
      + intros.
        apply H; trivial.
      + pose (a := (Lim_seq (fun n : nat => Expectation_posRV (Xn n)))).
        generalize (Lim_seq_le_loc (fun n => Expectation_posRV (Xn n)) 
                                   (fun _ => Expectation_posRV X)); intros.
        rewrite Lim_seq_const in H6.
        assert (Rbar_le (Expectation_posRV X) (Lim_seq (fun n : nat => Expectation_posRV (Xn n)))).
        * unfold Expectation_posRV at 1.
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
            unfold BoundedPositiveRandomVariable in H7.
            destruct H7.
            rewrite simple_Expectation_posRV with (prv := H7); trivial.
            apply monotone_convergence00 with (X := X); trivial.
          }
        * apply Rbar_le_antisym; trivial.
          case_eq (Expectation_posRV X); intros.
          ++ rewrite H8 in H6; simpl in H6.
             apply H6.
             unfold Hierarchy.eventually.   
             exists (0%nat).
             intros.
             specialize (H (Xn n) X (Xn_pos n) posX (H0 n)).
             rewrite <- (H2 n) in H.
             rewrite H8 in H.
             now simpl in H.
          ++ now destruct (Lim_seq (fun n : nat => Expectation_posRV (Xn n))).
          ++ generalize (Expectation_posRV_pos X); intros.
             now rewrite H8 in H9.
  Qed.

  Global Instance LimInf_seq_pos
         (Xn : nat -> Ts -> R)
         (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :
    PositiveRandomVariable 
      (fun omega : Ts => (LimInf_seq (fun n : nat => Xn n omega))).
  Proof.
    unfold PositiveRandomVariable.
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
        (Xn_pos : forall n, PositiveRandomVariable (Xn n))
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
         (Xn_pos : forall n, PositiveRandomVariable (Xn n)) :
    forall (n:nat), PositiveRandomVariable (Fatou_Y Xn n).
  Proof.
    unfold PositiveRandomVariable.
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
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) n omega:
    Fatou_Y Xn n omega <= Fatou_Y Xn (S n) omega.
  Proof.
    generalize (Fatou_Y_incr_Rbar Xn n omega).
    rewrite <- is_finite_Fatou_Y by trivial.
    simpl.
    now rewrite <-  is_finite_Fatou_Y by trivial.
  Qed.

    Instance Fatou_Y_meas
             (Xn : nat -> Ts -> R)
             (Xn_pos : forall n, PositiveRandomVariable (Xn n))
             (Xn_rv : forall n, RealMeasurable dom (Xn n)) :
      forall (n:nat), RealMeasurable dom (Fatou_Y Xn n).
    Proof.
      intros; red.
      apply sa_ge_le.
      intros.
      assert (event_equiv
              (fun omega : Ts => Inf_seq (fun k : nat => Xn (k + n)%nat omega) >= r)
              (inter_of_collection (fun k:nat => (fun omega : Ts => Xn (k + n)%nat omega >= r)))).
      - unfold inter_of_collection.
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
        apply sa_countable_inter; intros.
        clear H.
        revert r.
        apply sa_le_ge.
        apply Xn_rv.
    Qed.
    
    Instance Fatou_Y_rv
         (Xn : nat -> Ts -> R)
         (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
         (Xn_pos : forall n, PositiveRandomVariable (Xn n))
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
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) 
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (fin_exp : forall n, is_finite (Expectation_posRV (Xn n)))
        (isf:forall omega, is_finite (LimInf_seq (fun n : nat => Xn n omega)))

        (lim_rv : RandomVariable dom borel_sa 
                                 (fun omega => LimInf_seq (fun n => Xn n omega))) :
    Rbar_le (Expectation_posRV (fun omega => LimInf_seq (fun n => Xn n omega)))
            (LimInf_seq (fun n => Expectation_posRV (Xn n))).
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
    - assert (Lim_seq (fun n => Expectation_posRV (Fatou_Y Xn n)) =  
              (Expectation_posRV (fun omega => LimInf_seq (fun n => Xn n omega)))).
      + apply monotone_convergence with (X:= (fun omega : Ts => LimInf_seq (fun n : nat => Xn n omega))); trivial.
        * assert (forall (n:nat), Rbar_le (Expectation_posRV (Fatou_Y Xn n))
                                          (Expectation_posRV (Xn n))); intros.
          -- now apply Expectation_posRV_le.
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
        * intros; now apply Finite_Expectation_posRV_le with (rv_X2 := Xn n) (prv2 := Xn_pos n).
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
       (fun n : nat => Expectation_posRV (fun omega : Ts => Fatou_Y Xn n omega))) with
        (LimInf_seq
       (fun n : nat => Expectation_posRV (fun omega : Ts => Fatou_Y Xn n omega))).
        * apply LimInf_le.
          exists (0%nat); intros.
          generalize (Expectation_posRV_le (fun omega : Ts => Fatou_Y Xn n omega) (Xn n) (H1 n)); intros.
          generalize (Finite_Expectation_posRV_le (Fatou_Y Xn n) (Xn n) _ (Xn_pos n) (H1 n) (fin_exp n)); intros.
          rewrite <- H5 in H4.
          rewrite <- (fin_exp n) in H4.
          apply H4.
        * rewrite limInf_increasing; trivial.
          intros.
          generalize (Expectation_posRV_le 
                        (fun omega : Ts => Fatou_Y Xn n omega)
                        (fun omega : Ts => Fatou_Y Xn (S n) omega)); intros.
          generalize (Finite_Expectation_posRV_le (Fatou_Y Xn n) (Xn n) _ (Xn_pos n) (H1 n) (fin_exp n)); intros.
          generalize (Finite_Expectation_posRV_le (Fatou_Y Xn (S n)) (Xn (S n)) _ (Xn_pos (S n)) (H1 (S n)) (fin_exp (S n))); intros.                    
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

(*
  Lemma Riesz_Fischer
        (Xn : nat -> Ts -> R)
        (Xn_rv : forall n, RandomVariable dom borel_sa (Xn n))
        (Xn_pos : forall n, PositiveRandomVariable (Xn n)) 
        (norm : (Ts -> R) -> nonnegreal) :
    ex_lim_seq_cauchy (fun n => norm (Xn n)) ->
    exists (X : Ts -> R), 
    forall (omega:Ts), Lim_seq (fun n => norm (rvminus X (Xn n))) = 0.
    (* and is_finite (norm X) *)
    Proof.
  Admitted.
 *)
  
  Lemma Expectation_zero_pos 
        (X : Ts -> R)
        {rv : RandomVariable dom borel_sa X}
        {posrv :PositiveRandomVariable X} :
    Expectation X = Some (Finite 0) ->
    ps_P (fun omega => X omega = 0) = 1.
  Proof.
    rewrite Expectation_pos_posRV with (prv := posrv); intros.
    inversion H.

    generalize (simple_approx_lim_seq X posrv); intros.
    generalize (simple_approx_rv X); intro apx_rv1.
    generalize (simple_approx_posrv X); intro apx_prv1.
    generalize (simple_approx_srv X); intro apx_srv1.
    generalize (simple_approx_le X posrv); intro apx_le1.
    generalize (simple_approx_increasing X posrv); intro apx_inc1.
    generalize (monotone_convergence X (simple_approx X) rv posrv apx_rv1 apx_prv1 apx_le1 apx_inc1 (fun n => simple_expectation_real (simple_approx X n)) H0); intros.

    assert (forall n:nat, Expectation_posRV (simple_approx X n) = 0).
    intros.
    generalize (Expectation_posRV_le (simple_approx X n) X (apx_le1 n)); intros.
    rewrite H1 in H3.
    generalize (Expectation_posRV_pos (simple_approx X n)); intros.
    apply Rbar_le_antisym; trivial.

    assert (forall n:nat, ps_P (fun omega => (simple_approx X n) omega = 0) = 1).
    intros.
    apply SimplePosExpectation_zero_pos with (srv := apx_srv1 n); trivial.
    generalize (srv_Expectation_posRV (simple_approx X n)); intros.
    rewrite H3 in H4; symmetry in H4.
    now apply Rbar_finite_eq in H4.

    assert (forall n:nat, ps_P (event_complement (fun omega => (simple_approx X n omega = 0))) = 0).
    intros.
    rewrite ps_complement.
    rewrite H4; lra.
    apply sa_le_pt.
    unfold RandomVariable in apx_rv1.
    specialize (apx_rv1 n).
    now rewrite <- borel_sa_preimage2 in apx_rv1.

    generalize (lim_prob (fun n => (event_complement (fun omega => simple_approx X n omega = 0)))
                         (event_complement (fun omega => X omega = 0))
               ); trivial; intros.
    cut_to H6; trivial.
    apply is_lim_seq_ext with (v := (fun n => 0)) in H6.
    generalize (is_lim_seq_const 0); intros.
    apply is_lim_seq_unique in H6.
    apply is_lim_seq_unique in H7.    
    rewrite H6 in H7.
    rewrite ps_complement in H7.
    apply Rbar_finite_eq in H7; lra.
    apply sa_le_pt.
    unfold RandomVariable in rv.
    now rewrite <- borel_sa_preimage2 in rv.
    trivial.
    intros.
    apply sa_complement.
    apply sa_le_pt.
    specialize (apx_rv1 n).
    unfold RandomVariable in apx_rv1.
    now rewrite <- borel_sa_preimage2 in apx_rv1.
    unfold event_sub; intros.
    unfold event_complement.
    unfold event_complement in H7.
    unfold PositiveRandomVariable in apx_prv1.
    apply Rgt_not_eq.
    apply Rdichotomy in H7.
    destruct H7.
    generalize (apx_prv1 n); intros.
    specialize (H8 x); lra.
    specialize (apx_inc1 n x).
    lra.
    unfold event_complement.
    intro x.
    unfold union_of_collection.
    split; intros.
    destruct H7.
    apply Rgt_not_eq.
    apply Rdichotomy in H7.
    destruct H7.
    generalize (apx_prv1 x0 x); intros; lra.
    specialize (apx_le1 x0 x); lra.
    specialize (H0 x).
    clear H H1 H2 H3 H4 H5 H6.
    apply Rdichotomy in H7.
    destruct H7.
    specialize (posrv x); lra.
    apply is_lim_seq_spec in H0.
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
    rewrite Rabs_pos_eq; lra.
  Qed.

  Lemma Expectation_posRV_sum 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2}
        {prv1:PositiveRandomVariable rv_X1}
        {prv2:PositiveRandomVariable rv_X2} :     
    Expectation_posRV (rvplus rv_X1 rv_X2) =
    Rbar_plus (Expectation_posRV rv_X1) (Expectation_posRV rv_X2).
  Proof.
    generalize (simple_approx_lim_seq rv_X1 prv1); intros.
    generalize (simple_approx_lim_seq rv_X2 prv2); intros.
    generalize (simple_approx_rv rv_X1); intro apx_rv1.
    generalize (simple_approx_rv rv_X2); intro apx_rv2.
    generalize (simple_approx_posrv rv_X1); intro apx_prv1.
    generalize (simple_approx_posrv rv_X2); intro apx_prv2.     
    generalize (simple_approx_srv rv_X1); intro apx_srv1.
    generalize (simple_approx_srv rv_X2); intro apx_srv2.
    generalize (simple_approx_le rv_X1 prv1); intro apx_le1.
    generalize (simple_approx_le rv_X2 prv2); intro apx_le2. 
    generalize (simple_approx_increasing rv_X1 prv1); intro apx_inc1.
    generalize (simple_approx_increasing rv_X2 prv2); intro apx_inc2.
    
    generalize (monotone_convergence rv_X1 (simple_approx rv_X1) rv1 prv1 apx_rv1 apx_prv1 apx_le1 apx_inc1 (fun n => simple_expectation_real (simple_approx rv_X1 n))); intros.
    generalize (monotone_convergence rv_X2 (simple_approx rv_X2) rv2 prv2 apx_rv2 apx_prv2 apx_le2 apx_inc2 (fun n => simple_expectation_real (simple_approx rv_X2 n))); intros.
    cut_to H1; trivial.
    cut_to H2; trivial.
    generalize (fun n => rvplus_rv _ (simple_approx rv_X1 n) (simple_approx rv_X2 n)); intros.
    generalize (fun n => rvplus_prv (simple_approx rv_X1 n) (simple_approx rv_X2 n)); intros.     
    generalize (fun n => simple_expectation_real (simple_approx rv_X1 n)); intros apx_fin1.
    generalize (fun n => simple_expectation_real (simple_approx rv_X2 n)); intros apx_fin2.     
    generalize (monotone_convergence (rvplus rv_X1 rv_X2) 
                                     (fun n => rvplus (simple_approx rv_X1 n)
                                                   (simple_approx rv_X2 n))
                                     (rvplus_rv _ rv_X1 rv_X2)
                                     (rvplus_prv rv_X1 rv_X2) H3 H4); intros.
    cut_to H5; trivial.
    - rewrite Lim_seq_ext with (v := fun n => (Expectation_posRV (simple_approx rv_X1 n)) +
                                           (Expectation_posRV (simple_approx rv_X2 n)))
        in H5.
      + rewrite Lim_seq_plus in H5.
        * rewrite H1 in H5.
          rewrite H2 in H5.
          now symmetry.
        * apply ex_lim_seq_incr.
          intros.
          generalize (Expectation_posRV_le (simple_approx rv_X1 n) (simple_approx rv_X1 (S n)) (apx_inc1 n)); intros.
          rewrite <- apx_fin1 in H6; simpl in H6.
          now rewrite <- apx_fin1 in H6; simpl in H6.           
        * apply ex_lim_seq_incr.
          intros.
          generalize (Expectation_posRV_le (simple_approx rv_X2 n) (simple_approx rv_X2 (S n)) (apx_inc2 n)); intros.
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
        rewrite <- simple_Expectation_posRV with (srv := srvplus (simple_approx rv_X1 n) (simple_approx rv_X2 n)); trivial.
        rewrite <- sumSimpleExpectation; trivial.
        rewrite <- simple_Expectation_posRV with (srv := apx_srv1 n); trivial.
        rewrite <- simple_Expectation_posRV with (srv := apx_srv2 n); trivial.
    - unfold rv_le, rvplus.
      intros n x.
      specialize (apx_le1 n x).
      specialize (apx_le2 n x).       
      lra.
    - unfold rv_le, rvplus.
      intros n x.
      specialize (apx_inc1 n x).
      specialize (apx_inc2 n x).       
      lra.
    - intros.
      apply simple_expectation_real; trivial.
      apply srvplus; trivial.
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

        (pp1 : PositiveRandomVariable rxp1)
        (pn1 : PositiveRandomVariable rxn1)        
        (pp2 : PositiveRandomVariable rxp2)
        (pn2 : PositiveRandomVariable rxn2) :
    rv_eq (rvminus rxp1 rxn1) (rvminus rxp2 rxn2) ->
    is_finite (Expectation_posRV rxn1) ->
    is_finite (Expectation_posRV rxn2) ->    
    Rbar_minus (Expectation_posRV rxp1) (Expectation_posRV rxn1) =
    Rbar_minus (Expectation_posRV rxp2) (Expectation_posRV rxn2).
  Proof.
    intros.
    assert (rv_eq (rvplus rxp1 rxn2) (rvplus rxp2 rxn1)).
    - unfold rv_eq, pointwise_relation, rvminus, rvopp, rvplus, rvscale in *.
      intros.
      specialize (H a).
      lra.
    - generalize (Expectation_posRV_ext _ _ H2); intros.
      rewrite Expectation_posRV_sum in H3; trivial.
      rewrite Expectation_posRV_sum in H3; trivial.

      generalize (Expectation_posRV_pos rxp1); intros.
      generalize (Expectation_posRV_pos rxp2); intros.

      unfold is_finite in *.
      rewrite <- H0, <- H1 in H3; simpl in H3.
      rewrite <- H0, <- H1; simpl.

      destruct  (Expectation_posRV rxp1); destruct  (Expectation_posRV rxp2); try easy.

      + simpl in *.
        rewrite Rbar_finite_eq in H3.
        rewrite Rbar_finite_eq.
        lra.
  Qed.

  
  Lemma Expectation_dif_pos_unique 
        (rvp rvn : Ts -> R)
        (pr : RandomVariable dom borel_sa rvp)
        (nr : RandomVariable dom borel_sa rvn)        
        (p : PositiveRandomVariable rvp)
        (n : PositiveRandomVariable rvn) :
    is_finite (Expectation_posRV rvn) ->
    Expectation (rvminus rvp rvn) =
    Rbar_minus' (Expectation_posRV rvp)
                (Expectation_posRV rvn).
  Proof.
    intros.
    generalize (Expectation_dif_pos_unique2
                  rvp rvn 
                  (pos_fun_part (rvminus rvp rvn))
                  (neg_fun_part (rvminus rvp rvn))
                  _ _ _ _ _ _ _ _)
    ; intros.

    assert (is_finite (Expectation_posRV (fun x : Ts => neg_fun_part (rvminus rvp rvn) x))).
    - apply Finite_Expectation_posRV_le with (rv_X2 := rvn) (prv2 := n); trivial.     
      apply neg_part_le; trivial.
    - cut_to H0; trivial.
      + unfold Expectation.
        unfold Rbar_minus'.
        unfold is_finite in H; rewrite <- H.
        unfold is_finite in H1; rewrite <- H1.
        rewrite <- H in H0.
        rewrite <- H1 in H0.
        unfold Rbar_minus in H0.

        generalize (Expectation_posRV_pos rvp); intros.
        generalize (Expectation_posRV_pos (pos_fun_part (rvminus rvp rvn))); intros.

        destruct  (Expectation_posRV rvp); destruct  (Expectation_posRV (pos_fun_part (rvminus rvp rvn))); try easy.

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
    
    is_finite (Expectation_posRV (neg_fun_part rv_X1)) ->
    is_finite (Expectation_posRV (neg_fun_part rv_X2)) ->    
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
    - repeat rewrite Expectation_posRV_sum by typeclasses eauto.
      unfold Expectation.
      unfold Rbar_minus'.
      generalize (Expectation_posRV_pos (pos_fun_part rv_X1)); intros.
      generalize (Expectation_posRV_pos (pos_fun_part rv_X2)); intros.      
      rewrite <- Rbar_plus_opp.
      destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X1 x))
      ; try solve[simpl; congruence].
      destruct (Expectation_posRV (fun x : Ts => neg_fun_part rv_X2 x))
      ; try solve[simpl; congruence].
      destruct (Expectation_posRV (fun x : Ts => pos_fun_part rv_X1 x)); try now simpl.
      + destruct (Expectation_posRV (fun x : Ts => pos_fun_part rv_X2 x)); try now simpl.
        simpl.
        f_equal.
        f_equal.
        lra.
      + destruct (Expectation_posRV (fun x : Ts => pos_fun_part rv_X2 x)); try now simpl.
    - typeclasses eauto.
    - typeclasses eauto.
    - rewrite Expectation_posRV_sum by typeclasses eauto.
      rewrite <- H, <- H0.
      simpl.
      reflexivity.
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
    is_finite (Rbar_opp a) -> is_finite a.
  Proof.
    unfold is_finite, Rbar_opp.
    match_destr.
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
    specialize (H1 H2).
    tauto.
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
      + apply Expectation_posRV_le with (prv1 := positive_part_prv rv_X1) 
                                        (prv2 := positive_part_prv rv_X2) in H2.
        apply Expectation_posRV_le with (prv1 := negative_part_prv rv_X2) 
                                        (prv2 := negative_part_prv rv_X1) in H3.
        apply Rbar_opp_le in H3.
        unfold Rbar_minus' in *.
        generalize (Rbar_plus_le_compat _ _ _ _ H2 H3).
        apply is_Rbar_plus_unique in H.
        apply is_Rbar_plus_unique in H0.
        rewrite H.
        now rewrite H0.
  Qed.

End Expectation.
