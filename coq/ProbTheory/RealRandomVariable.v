Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program Equivalence.
Require Import Coquelicot.Coquelicot.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Import NumberIso.
Require Import SigmaAlgebras.
Require Export Almost.
Require Export FunctionsToReal ProbSpace BorelSigmaAlgebra.
Require Export RandomVariable.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section RealRandomVariables.

  Lemma borel_singleton (c:R) :
    sa_sigma (SigmaAlgebra:=borel_sa) (pre_event_singleton c).
  Proof.
    apply sa_le_pt.
    apply borel_sa_preimage2; intros.
    destruct B.
    unfold event_preimage.
    simpl.
    apply s.
  Qed.

  Global Instance borel_has_preimages : HasPreimageSingleton borel_sa.
  Proof.
    red; intros.
    apply sa_le_pt; intros.
    apply borel_sa_preimage2; intros.
    now apply rv_preimage_sa.
  Qed.

  Global Instance Rbar_borel_has_preimages : HasPreimageSingleton Rbar_borel_sa.
  Proof.
    red; intros.
    apply Rbar_sa_le_pt; intros.
    apply Rbar_borel_sa_preimage2; intros.
    now apply rv_preimage_sa.
  Qed.

  Context {Ts:Type}
          (dom: SigmaAlgebra Ts).

  Section measurable.

    (* For the borel_sa, this is an equivalent definition *)
    Class RealMeasurable (f: Ts -> R)
      := rmeasurable : forall (r:R), sa_sigma (fun omega : Ts => f omega <= r).

    Instance measurable_rv (rv_X:Ts->R)
             {rm:RealMeasurable rv_X}
      : RandomVariable dom borel_sa rv_X.
    Proof.
      intros ?.
      apply borel_sa_preimage2; trivial; intros.
    Qed.

    Instance rv_measurable (rv_X:Ts->R)
             {rrv:RandomVariable dom borel_sa rv_X}
      : RealMeasurable rv_X | 3.
    Proof.
      red.
      now rewrite borel_sa_preimage2.
    Qed.


    Global Instance RealMeasurable_proper :
      Proper (rv_eq ==> iff) RealMeasurable.
    Proof.
      intros ???.
      split; intros.
      - apply rv_measurable.
        setoid_rewrite <- H.
        now apply measurable_rv.
      - apply rv_measurable.
        rewrite H.
        now apply measurable_rv.
    Qed.
    
    Instance scale_measurable_pos (f : Ts -> R) (c:posreal) :
      RealMeasurable f ->
      RealMeasurable (rvscale c f).
    Proof.
      intros ? r.
      assert (pre_event_equiv (fun omega : Ts => (c * f omega <= r)%R)
                              (fun omega : Ts => (f omega <= r/c)%R)).
      - red; intros.
        assert (0 < c) by apply (cond_pos c).
        split; intros.
        + unfold Rdiv.
          rewrite Rmult_comm.
          replace (f x) with (/c * (c * f x)).
          * apply  Rmult_le_compat_l; trivial; left.
            now apply Rinv_0_lt_compat.
          * field_simplify; lra.
        + replace (r) with (c * (r / c)).
          * apply  Rmult_le_compat_l; trivial; now left.
          * field; lra.
      - rewrite H0.
        apply H.
    Qed.

    Instance scale_measurable_neg (f : Ts -> R) (c:posreal) :
      RealMeasurable f ->
      RealMeasurable (rvscale (- c) f).
    Proof.
      intros ? r.
      assert (pre_event_equiv (fun omega : Ts => ((-c) * f omega <= r)%R)
                              (fun omega : Ts => (c * f omega >= -r)%R)).
      - red; intros.
        assert (0 < c) by apply (cond_pos c).
        lra.
      - rewrite H0.
        apply sa_le_ge.
        now apply scale_measurable_pos.
    Qed.

    Instance constant_measurable (c:R) :
      RealMeasurable (const c).
    Proof.
      intros r.
      destruct (Rle_dec c r).
      - assert (pre_event_equiv (fun _ : Ts => c <= r)
                                (fun _ : Ts => True)).
        red; intros.
        intuition.
        rewrite H.
        apply sa_all.
      - assert (pre_event_equiv (fun _ : Ts => c <= r)
                                event_none).
        red; intros.
        intuition.
        rewrite H.
        apply sa_none.
    Qed.

    Instance scale_measurable (f : Ts -> R) (c:R) :
      RealMeasurable f ->
      RealMeasurable (rvscale c f).
    Proof.
      intros ?.
      destruct (Rtotal_order c 0) as [|[|]].
      - assert (pf:0 < - c) by lra.
        generalize (scale_measurable_neg f (mkposreal _ pf) H).
        simpl.
        apply RealMeasurable_proper.
        unfold rvscale; intros ?; lra.
      - subst.
        generalize (constant_measurable 0).
        apply RealMeasurable_proper.
        unfold rvscale, const; intros ?; lra.
      - generalize (scale_measurable_pos f (mkposreal _ H0) H).
        simpl.
        apply RealMeasurable_proper.
        unfold rvscale; intros ?; lra.
    Qed.

    Lemma sa_sigma_inter_pts
          (rv_X1 rv_X2 : Ts -> R)
          {rv1: RandomVariable dom borel_sa rv_X1}         
          {rv2: RandomVariable dom borel_sa rv_X2}         
          (c1 c2 : R) :
      sa_sigma (fun omega : Ts => rv_X1 omega = c1 /\ 
                                  rv_X2 omega = c2).
    Proof.
      apply sa_inter.
      - now apply sa_preimage_singleton.
      - now apply sa_preimage_singleton.
    Qed.

    
    Instance Ropp_measurable (f : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable (rvopp f).
    Proof.
      intros ??.
      assert (pre_event_equiv (fun omega : Ts => rvopp f omega <= r)
                              (fun omega : Ts => (f omega) >= -r)).
      unfold pre_event_equiv; intros.
      unfold rvopp, rvscale; lra.
      rewrite H0.
      now apply sa_le_ge.
    Qed.

    Instance plus_measurable (f g : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable g ->
      RealMeasurable (rvplus f g).
    Proof.
      intros ?? r.
      assert (pre_event_equiv (fun omega : Ts => rvplus f g omega <= r)
                              (pre_event_complement (fun omega : Ts => f omega + g omega > r))).
      - unfold pre_event_equiv, pre_event_complement, rvplus; intros.
        lra.
      - rewrite H1.
        assert (pre_event_equiv 
                  (fun omega : Ts => (f omega) + (g omega) > r)
                  (pre_union_of_collection
                     (fun (n:nat) => 
                        pre_event_inter
                          (fun omega : Ts => f omega > r - Qreals.Q2R (iso_b n))
                          (fun omega : Ts => g omega > Qreals.Q2R (iso_b n))))).
        + unfold pre_event_equiv, pre_union_of_collection, pre_event_inter; intros.
          split; intros.
          * assert (g x > r - f x) by lra.
            generalize (Q_dense (r - f x) (g x) H3); intros.
            destruct H4.
            exists (iso_f x0).
            rewrite iso_b_f.
            lra.
          * destruct H2.
            lra.
        + apply sa_complement.
          rewrite H2.
          apply sa_countable_union.
          intros.
          apply sa_inter.
          now apply sa_le_gt.
          now apply sa_le_gt.
    Qed.

    Instance rvsum_measurable 
             (Xn : nat -> Ts -> R)
             (Xn_rv : forall n, RealMeasurable (Xn n)) :
      forall (n:nat), RealMeasurable (rvsum Xn n).
    Proof.
      unfold RealMeasurable in *.
      induction n; intros.
      - assert (pre_event_equiv (fun omega : Ts => rvsum Xn 0 omega <= r)
                                (fun omega : Ts => Xn 0%nat omega <= r)).
        + intro x.
          unfold rvsum, Hierarchy.sum_n.
          now rewrite Hierarchy.sum_n_n.
        + now rewrite H.
      - assert (pre_event_equiv  (fun omega : Ts => rvsum Xn (S n) omega <= r)
                                 (fun omega => (rvplus (rvsum Xn n) (Xn (S n))) omega <= r)).
        + intro x.
          unfold rvsum, rvplus, Hierarchy.sum_n.
          rewrite Hierarchy.sum_n_Sm.
          now unfold plus; simpl.
          lia.
        + rewrite H.
          now apply plus_measurable.
    Qed.

    Instance minus_measurable (f g : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable g ->
      RealMeasurable (rvminus f g).
    Proof.
      intros.
      unfold Rminus.
      apply plus_measurable; trivial.
      now apply Ropp_measurable.
    Qed.
    
    Instance Rsqr_pos_measurable (f : Ts -> R) :
      (forall (x:Ts), (0 <= f x)%R) ->
      RealMeasurable f ->
      RealMeasurable (rvsqr f).
    Proof.
      intros ?? r.
      destruct (Rgt_dec 0 r).
      - assert (equiv (fun omega : Ts => rvsqr f omega <= r)
                      (fun _ => False)).
        + unfold equiv, pre_event_equiv; intros.
          generalize (Rle_0_sqr (f x)).
          unfold rvsqr.
          lra.
        + rewrite H1.
          apply sa_none.
      - assert (0 <= r) by lra.
        assert (pre_event_equiv (fun omega : Ts => rvsqr f omega <= r)
                                (fun omega : Ts => (f omega) <= Rsqrt (mknonnegreal _ H1)) ).
        + unfold pre_event_equiv, rvsqr; intros.
          specialize (H x).
          apply Rsqr_le_to_Rsqrt with (r := mknonnegreal _ H1) (x := mknonnegreal _ H).
        + rewrite H2.
          apply H0.
    Qed.

    Lemma measurable_open_continuous (f : Ts -> R) (g : R -> R) :
      continuity g ->
      (forall B: pre_event R, open_set B -> sa_sigma (pre_event_preimage f B)) ->
      (forall B: pre_event R, open_set B -> 
                              sa_sigma (pre_event_preimage (fun omega => g (f omega)) B)).
    Proof.
      intros.
      generalize (continuity_P3 g); intros.
      destruct H2.
      specialize (H2 H B H1).
      unfold image_rec in *.
      unfold event_preimage in *.
      now specialize (H0 (fun x : R => B (g x)) H2).
    Qed.

    Instance measurable_continuous (f : Ts -> R) (g : R -> R) :
      continuity g ->
      RealMeasurable f ->
      RealMeasurable (compose g f).
    Proof.
      intros ?? r.
      apply sa_open_set_le.
      apply measurable_open_continuous; trivial.
      now apply sa_le_open_set.
    Qed.

    Instance rvpow_measurable (f : Ts -> R) n :
      RealMeasurable f ->
      RealMeasurable (rvpow f n).
    Proof.
      intros.
      unfold rvpow.
      assert (rv_eq  (fun omega : Ts => f omega ^ n)
                     (fun omega : Ts => compose (fun x => pow x n) f omega))
        by reflexivity.
      rewrite H0.
      apply measurable_continuous; trivial.
      apply derivable_continuous.
      apply derivable_pow.
    Qed.

    Instance Rsqr_measurable (f : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable (rvsqr f).
    Proof.
      intros.
      unfold rvsqr.
      apply measurable_continuous; trivial.
      apply Rsqr_continuous.
    Qed.

    Instance mult_measurable (f g : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable g ->
      RealMeasurable (rvmult f g).
    Proof.
      intros.
      rewrite rvmult_unfold.
      typeclasses eauto.
    Qed.

    Instance Rabs_measurable f :
      RealMeasurable f ->
      RealMeasurable (rvabs f).
    Proof.
      intros.
      unfold rvabs.
      apply measurable_continuous.
      apply Rcontinuity_abs.
      apply H.
    Qed.

    Instance Rsqrt_measurable f :
      RealMeasurable f ->
      RealMeasurable (rvsqrt f).
    Proof.
      intros.
      unfold rvsqrt.
      apply measurable_continuous; trivial.
      generalize continuous_sqrt; intros.
      unfold continuity; intros.
      rewrite continuity_pt_filterlim.
      apply H0.
    Qed.

    Instance max_measurable (f g : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable g ->
      RealMeasurable (rvmax f g).
    Proof.
      intros ??.
      rewrite rvmax_unfold.
      typeclasses eauto.
    Qed.

    Instance min_measurable (f g : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable g ->
      RealMeasurable (rvmin f g).
    Proof.
      intros ??.
      rewrite rvmin_unfold.
      typeclasses eauto.
    Qed.

    Instance rvclip_measurable (f : Ts -> R) (c : nonnegreal) :
      RealMeasurable f ->
      RealMeasurable (rvclip f c).
    Proof.
      intros ??.
      generalize (rvclip_abs_bounded f c); intros.
      destruct (Rge_dec r c).
      - assert (pre_event_equiv (fun omega : Ts => rvclip f c omega <= r)
                                Ω ).
        + intro x.
          specialize (H0 x).
          generalize (Rle_abs (rvclip f c x)); intros.
          unfold Ω, pre_Ω; simpl.
          split; try tauto. red; lra.
        + rewrite H1.
          apply sa_all.
      - destruct (Rlt_dec r (-c)).
        + assert (pre_event_equiv (fun omega : Ts => rvclip f c omega <= r)
                                  event_none ).
          * intro x.
            specialize (H0 x).
            generalize (Rle_abs (- rvclip f c x)); intros.
            rewrite Rabs_Ropp in H1.
            split; intros.
            lra.
            now unfold event_none in H2.
          * rewrite H1.
            apply sa_none.
        + unfold RealMeasurable in H.
          assert (pre_event_equiv (fun omega : Ts => rvclip f c omega <= r)
                                  (fun omega : Ts => f omega <= r)).
          * intro x.
            unfold rvclip.
            match_destr.
            lra.
            match_destr; lra.
          * now rewrite H1.
    Qed.

    Instance pos_fun_part_measurable (f : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable (pos_fun_part f).
    Proof.
      intros.
      rewrite pos_fun_part_unfold.
      typeclasses eauto.
    Qed.

    Instance neg_fun_partmeasurable (f : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable (neg_fun_part f).
    Proof.
      intros.
      rewrite neg_fun_part_unfold.
      typeclasses eauto.
    Qed.

    Instance rvchoice_measurable (c f g : Ts -> R) :
      RealMeasurable c ->
      RealMeasurable f ->
      RealMeasurable g ->
      RealMeasurable (rvchoice (fun x => if Req_EM_T (c x) 0 then false else true)  f g).
    Proof.
      unfold RealMeasurable.
      intros.
      assert (pre_event_equiv
                (fun omega : Ts =>
                   rvchoice (fun x : Ts => if Req_EM_T (c x) 0 then false else true) 
                            f g omega <= r)
                (pre_event_union 
                   (pre_event_inter 
                      (fun omega : Ts => c omega = 0)
                      (fun omega : Ts => g omega <= r))
                   (pre_event_inter 
                      (pre_event_complement (fun omega : Ts => c omega = 0))
                      (fun omega : Ts => f omega <= r)))).
      intro x.
      unfold rvchoice, pre_event_union, pre_event_inter, pre_event_complement.
      destruct (Req_EM_T (c x) 0); lra.
      rewrite H2.
      apply sa_union; apply sa_inter; trivial.
      - now apply sa_le_pt.
      - apply sa_complement.
        now apply sa_le_pt.
    Qed.

    Definition Rbar_rvchoice (c:Ts -> bool) (rv_X1 rv_X2 : Ts -> Rbar)
      := fun omega => if c omega then rv_X1 omega else rv_X2 omega.

    Instance Rbar_rvchoice_measurable (c : Ts -> R) (f g : Ts -> Rbar) :
      RealMeasurable c ->
      RbarMeasurable f ->
      RbarMeasurable g ->
      RbarMeasurable (Rbar_rvchoice (fun x => if Req_EM_T (c x) 0 then false else true)  f g).
    Proof.
      unfold RealMeasurable, RbarMeasurable.
      intros.
      assert (pre_event_equiv
                (fun omega : Ts =>
                   Rbar_le
                     (Rbar_rvchoice (fun x : Ts => if Req_EM_T (c x) 0 then false else true) 
                                    f g omega )
                     r)
                (pre_event_union 
                   (pre_event_inter 
                      (fun omega : Ts => c omega = 0)
                      (fun omega : Ts => Rbar_le (g omega) r))
                   (pre_event_inter 
                      (pre_event_complement (fun omega : Ts => c omega = 0))
                      (fun omega : Ts => Rbar_le (f omega) r)))).
      - intro x.
        unfold Rbar_rvchoice, pre_event_union, pre_event_inter, pre_event_complement.
        destruct (Req_EM_T (c x) 0); intuition lra.
      - rewrite H2.
        apply sa_union; apply sa_inter; trivial.
        + now apply sa_le_pt.
        + apply sa_complement.
          now apply sa_le_pt.
    Qed.

    Instance ln_measurable (b : Ts -> R) :
      RealMeasurable b ->
      RealMeasurable (fun (x:Ts) => ln (b x)).
    Proof.
      unfold RealMeasurable.
      intros rb.
      intros.
      assert (pre_event_equiv (fun omega : Ts => ln (b omega) <= r)
                              (pre_event_union
                                 (pre_event_inter (fun omega : Ts => b omega <= 0)
                                                  (fun omega : Ts => 0 <= r))
                                 (pre_event_inter (fun omega : Ts => b omega > 0 )
                                                  (fun omega : Ts => b omega <= exp r)))).
      - intro x.
        unfold pre_event_union, pre_event_inter.
        split; intros.
        + destruct (Rle_dec (b x) 0).
          * left; unfold ln in H.
            match_destr_in H; lra.
          * right; split; [lra | ].
            rewrite <- (exp_ln (b x)); trivial.
            destruct H.
            -- left; now apply exp_increasing.
            -- rewrite H; lra.
            -- lra.
        + destruct H; destruct H.
          * unfold ln.
            match_destr.
            assert False by lra.
            tauto.
          * rewrite <- (ln_exp r).
            destruct H0.
            -- left; now apply ln_increasing.
            -- rewrite H0; lra.
      - rewrite H.
        apply sa_union.
        + apply sa_inter; trivial.
          apply constant_measurable.
        + apply sa_inter; trivial.
          now apply sa_le_gt.
    Qed.

    Instance exp_measurable (b : Ts -> R) :
      RealMeasurable b ->
      RealMeasurable (fun (x:Ts) => exp (b x)).
    Proof.
      apply measurable_continuous.
      apply derivable_continuous.
      apply derivable_exp.
    Qed.
    
    Instance Rpower_measurable (b e : Ts -> R) :
      RealMeasurable b ->
      RealMeasurable e ->
      RealMeasurable (fun (x:Ts) => Rpower (b x) (e x)).
    Proof.
      unfold rvpower, Rpower.
      intros bpos rb re.
      apply exp_measurable.
      apply mult_measurable; trivial.
      now apply ln_measurable.
    Qed.

    Instance rvpower_measurable (b e : Ts -> R) :
      (*      (forall (x:Ts), (0 <= b x)%R) -> *)
      RealMeasurable b ->
      RealMeasurable e ->
      RealMeasurable (rvpower b e).
    Proof.
      unfold rvpower, power, RealMeasurable.
      intros rb re r.
      assert (pre_event_equiv  (fun omega : Ts => (if Rle_dec (b omega) 0 
                                                   then 0 else Rpower (b omega) (e omega)) <= r)
                               (pre_event_union
                                  (pre_event_inter (fun omega => b omega <= 0)
                                                   (fun omega => 0 <= r))
                                  (pre_event_inter (fun omega => b omega > 0) 
                                                   (fun omega => Rpower (b omega) (e omega) <= r)))).
      - intro x.
        unfold pre_event_inter, pre_event_union.
        destruct (Rle_dec (b x) 0).
        + split; intros.
          * now left.
          * destruct H; destruct H; lra.
        + split; intros.
          * right; lra.
          * destruct H; destruct H; lra.
      - rewrite H.
        apply sa_union.
        + apply sa_inter; trivial.
          now apply constant_measurable.
        + apply sa_inter.
          * now apply sa_le_gt.
          * now apply Rpower_measurable.
    Qed.
    
    (* note this is zero at points where the limit is infinite *)
    Definition rvlim (f : nat -> Ts -> R) : (Ts -> R) :=
      (fun omega => real (Lim_seq (fun n => f n omega))).

    Instance LimSup_measurable (f : nat -> Ts -> R) : 
      (forall n, RealMeasurable (f n)) ->
      (forall omega, is_finite (LimSup_seq (fun n => f n omega))) ->
      RealMeasurable (fun omega => LimSup_seq (fun n => f n omega)).
    Proof.
      intros.
      unfold RealMeasurable; intros.
      apply sa_proper with
          (x := pre_inter_of_collection
                  (fun j => 
                     pre_union_of_collection
                       (fun m => 
                          pre_inter_of_collection
                            (fun n : nat => 
                               (fun omega => f (n + m)%nat omega <= r + / (INR (S j))))))).
      - intro x.
        specialize (H0 x).
        unfold pre_inter_of_collection, pre_union_of_collection, LimSup_seq; split; intros.
        + unfold proj1_sig.
          unfold LimSup_seq, proj1_sig in H0.
          match_destr.
          unfold is_LimSup_seq in i.
          match_destr_in i.
          destruct (Rle_dec r0 r); trivial.
          assert (0 < (r0 - r)/2) by lra.
          specialize (i (mkposreal _ H2)).
          simpl in i.
          destruct i.
          replace (r0 - (r0 - r)/2) with (r + (r0 - r)/2) in H3 by lra.
          specialize (H1 (Z.to_nat (up (2 / (r0 - r))))).
          destruct H1.
          specialize (H3 x0).
          destruct H3 as [? [? ?]].            
          specialize (H1 (x1 - x0)%nat).
          replace (x1 - x0 + x0)%nat with x1 in H1 by lia.
          generalize (Rlt_le_trans _ _ _ H5 H1); intros.
          apply Rplus_lt_reg_l in H6.
          replace ((r0 - r) / 2) with (/ (2 /(r0 - r))) in H6 by (field;lra).
          assert (0 < 2 / (r0 - r)).
          {
            replace (2 / (r0 - r)) with (/((r0-r)/2)) by (field; lra).
            now apply Rinv_0_lt_compat.
          }
          apply Rinv_lt_cancel in H6; trivial.
          rewrite S_INR in H6.
          rewrite INR_up_pos in H6; [|lra].
          generalize (archimed (2 / (r0 - r))); intros.
          destruct H8.
          lra.
        + unfold proj1_sig in H1.
          unfold LimSup_seq, proj1_sig in H0.
          match_destr_in H1.
          unfold is_LimSup_seq in i.
          match_destr_in i.
          assert (0 < / INR (S n)).
          { 
            apply Rinv_0_lt_compat.
            apply lt_0_INR; lia.
          }
          specialize (i (mkposreal _ H2)).
          destruct i.
          destruct H4.
          exists x0.
          intros.
          specialize (H4 (n0 + x0)%nat).
          cut_to H4; [|lia].
          replace (pos (mkposreal _ H2)) with (/ INR (S n)) in H4 by auto.
          left.
          apply (Rlt_le_trans _ _ _ H4).
          now apply Rplus_le_compat_r.
      - apply sa_pre_countable_inter; intros.
        apply sa_countable_union; intros.
        apply sa_pre_countable_inter; intros.
        apply H.
    Qed.

    Lemma x_plus_x_div_2 (x : Rbar) :
      (Rbar_div_pos (Rbar_plus x x ) (mkposreal 2 Rlt_R0_R2)) = x.
    Proof.
      case_eq x; intros; simpl; trivial.
      rewrite Rbar_finite_eq.
      field.
    Qed.

    Instance rvlim_measurable (f : nat -> Ts -> R) :
      (forall n, RealMeasurable (f n)) ->
      (forall (omega:Ts), ex_finite_lim_seq (fun n => f n omega)) ->
      RealMeasurable (rvlim f).
    Proof.
      intros.
      unfold rvlim.
      assert (forall omega, ex_lim_seq (fun n => f n omega)).
      {
        intros.
        now apply ex_finite_lim_seq_correct.
      }
      assert (forall omega, Lim_seq (fun n => f n omega) = 
                            LimSup_seq (fun n => f n omega)).
      {
        intros.
        specialize (H1 omega).
        rewrite ex_lim_LimSup_LimInf_seq in H1.
        unfold Lim_seq.
        rewrite H1.
        now rewrite x_plus_x_div_2.
      }
      apply RealMeasurable_proper with
          (x := fun omega => LimSup_seq (fun n => f n omega)).
      intro x; now rewrite H2.
      apply LimSup_measurable; trivial.
      intros.
      specialize (H0 omega).
      rewrite ex_finite_lim_seq_correct in H0.
      destruct H0.
      unfold is_finite.
      now rewrite <- H2.
    Qed.

    Section rvs.

      Global Instance rvlim_rv (f: nat -> Ts -> R)
             {rv : forall n, RandomVariable dom borel_sa (f n)} :
        (forall (omega:Ts), ex_finite_lim_seq (fun n => f n omega)) ->
        RandomVariable dom borel_sa (rvlim f).
      Proof.
        intros.
        apply measurable_rv.
        apply rvlim_measurable; intros.
        now apply rv_measurable.
        apply H.
      Qed.

      Global Instance rvscale_rv (c: R) (rv_X : Ts -> R) 
             (rv : RandomVariable dom borel_sa rv_X) 
        : RandomVariable dom borel_sa (rvscale c rv_X).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance rvopp_rv (rv_X : Ts -> R) 
             {rv : RandomVariable dom borel_sa rv_X}
        : RandomVariable dom borel_sa (rvopp rv_X).
      Proof.
        now apply rvscale_rv.
      Defined.

      Global Instance rvclip_rv (rv_X : Ts -> R) (c:nonnegreal)
             {rv : RandomVariable dom borel_sa rv_X}
        : RandomVariable dom borel_sa (rvclip rv_X c).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance rvplus_rv (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2} :
        RandomVariable dom borel_sa (rvplus rv_X1 rv_X2).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance rvsum_rv (Xn : nat -> Ts -> R)
             {rv : forall (n:nat), RandomVariable dom borel_sa (Xn n)} :
        forall (n:nat), RandomVariable dom borel_sa (rvsum Xn n).
      Proof.
        intros.
        apply measurable_rv.
        apply rvsum_measurable; intros.
        now apply rv_measurable.
      Qed.

      Global Instance rvminus_rv
             (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2}  :
        RandomVariable dom borel_sa (rvminus rv_X1 rv_X2) := 
        rvplus_rv rv_X1 (rvopp rv_X2).

      Global Instance rvmult_rv 
             (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2} :
        RandomVariable dom borel_sa (rvmult rv_X1 rv_X2).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance rvpow_rv (rv_X : Ts -> R) n :
        RandomVariable dom borel_sa rv_X ->
        RandomVariable dom borel_sa (rvpow rv_X n).
      Proof.
        typeclasses eauto.
      Qed.

      (* rvpower_rv declared below since it uses NonnegativeFunction *)
      
      Global Instance rvsqr_rv
             (rv_X : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X} :
        RandomVariable dom borel_sa (rvsqr rv_X).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance rvabs_rv
             (rv_X : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X} :
        RandomVariable dom borel_sa (rvabs rv_X).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance rvsqrt_rv
             (rv_X : Ts -> R)
             {rv : RandomVariable dom borel_sa rv_X} :
        RandomVariable dom borel_sa (rvsqrt rv_X).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance rvmax_rv
             (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2}  :
        RandomVariable dom borel_sa (rvmax rv_X1 rv_X2).
      Proof.
        typeclasses eauto.
      Qed.
      
      Global Instance rvmin_rv
             (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2}  :
        RandomVariable dom borel_sa (rvmin rv_X1 rv_X2).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance positive_part_rv 
             (rv_X : Ts -> R)
             (rv : RandomVariable dom borel_sa rv_X) :
        RandomVariable dom borel_sa (pos_fun_part rv_X).
      Proof.
        apply measurable_rv.
        apply pos_fun_part_measurable.
        apply rv_measurable.
        typeclasses eauto.
      Qed.

      Global Instance negative_part_rv
             (rv_X : Ts -> R)
             (rv : RandomVariable dom borel_sa rv_X) :
        RandomVariable dom borel_sa (neg_fun_part rv_X).
      Proof.
        apply measurable_rv.
        apply neg_fun_partmeasurable.
        now apply rv_measurable.
      Qed.

      Global Instance positive_part_rv'
             (rv_X : Ts -> R)
             (rv : RandomVariable dom borel_sa rv_X) :
        RandomVariable dom borel_sa (fun x => (pos_fun_part rv_X) x).
      Proof.
        typeclasses eauto.
      Qed.

      Global Instance negative_part_rv'
             (rv_X : Ts -> R)
             (rv : RandomVariable dom borel_sa rv_X) :
        RandomVariable dom borel_sa (fun x => neg_fun_part rv_X x).
      Proof.
        apply measurable_rv.
        apply neg_fun_partmeasurable.
        now apply rv_measurable.
      Qed.

      Global Instance rvchoice_rv
             (rv_C rv_X1 rv_X2 : Ts -> R)
             {rvc : RandomVariable dom borel_sa rv_C}
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2}  :
        RealMeasurable (rvchoice (fun x => if Req_EM_T (rv_C x) 0 then false else true) rv_X1 rv_X2).
      Proof.
        typeclasses eauto.
      Qed.


    End rvs.

  End measurable.

  Section Const.

    Global Program Instance scale_constant_random_variable (c: R)
           (rv_X : Ts -> R)
           {crv:ConstantRangeFunction rv_X} : ConstantRangeFunction (rvscale c rv_X)
      := { frf_val := Rmult c frf_val }.
    Next Obligation.
      destruct crv.
      unfold rvscale.
      now rewrite (frf_val_complete x).
    Qed.

  End Const.

  Section Simple.
    
    Global Program Instance frfscale (c: R)
           (rv_X : Ts -> R)
           {frf:FiniteRangeFunction rv_X} : FiniteRangeFunction (rvscale c rv_X)
      := { frf_vals := map (fun v => Rmult c v) frf_vals }.
    Next Obligation.
      destruct frf.
      rewrite in_map_iff.
      exists (rv_X x).
      split; trivial.
    Qed.

    Global Instance frfopp 
           {rv_X : Ts -> R}
           {frf:FiniteRangeFunction rv_X} : FiniteRangeFunction (rvopp rv_X)
      := frfscale (-1) rv_X.    

    Global Program Instance frfplus
           (rv_X1 rv_X2 : Ts -> R)
           {frf1:FiniteRangeFunction rv_X1}
           {frf2:FiniteRangeFunction rv_X2}
      : FiniteRangeFunction (rvplus rv_X1 rv_X2)
      := { frf_vals := map (fun ab => Rplus (fst ab) (snd ab)) 
                           (list_prod (frf_vals (FiniteRangeFunction:=frf1))
                                      (frf_vals (FiniteRangeFunction:=frf2))) }.
    Next Obligation.
      destruct frf1.
      destruct frf2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Instance frfminus 
           (rv_X1 rv_X2 : Ts -> R)
           {frf1 : FiniteRangeFunction rv_X1}
           {frf2 : FiniteRangeFunction rv_X2}  :
      FiniteRangeFunction (rvminus rv_X1 rv_X2) := 
      frfplus rv_X1 (rvopp rv_X2).

    Global Program Instance frfmult
           (rv_X1 rv_X2 : Ts -> R)
           {frf1:FiniteRangeFunction rv_X1}
           {frf2:FiniteRangeFunction rv_X2}
      : FiniteRangeFunction (rvmult rv_X1 rv_X2)
      := { frf_vals := map (fun ab => Rmult (fst ab) (snd ab)) 
                           (list_prod (frf_vals (FiniteRangeFunction:=frf1))
                                      (frf_vals (FiniteRangeFunction:=frf2))) }.
    Next Obligation.
      destruct frf1.
      destruct frf2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Program Instance frfsqr
           (rv_X : Ts -> R)
           {frf:FiniteRangeFunction rv_X} : FiniteRangeFunction (rvsqr rv_X)
      := { frf_vals := map Rsqr frf_vals }.
    Next Obligation.
      destruct frf.
      unfold rvsqr.
      now apply in_map.
    Qed.

    Global Program Instance frfsqrt
           (rv_X : Ts -> R)
           {frf:FiniteRangeFunction rv_X} : FiniteRangeFunction (rvsqrt rv_X)
      := { frf_vals := map sqrt frf_vals }.
    Next Obligation.
      destruct frf.
      unfold rvsqrt.
      now apply in_map.
    Qed.

    Global Program Instance frfpow
           (rv_X : Ts -> R) n
           {frf:FiniteRangeFunction rv_X} : FiniteRangeFunction (rvpow rv_X n)
      := { frf_vals := map (fun x => pow x n) frf_vals }.
    Next Obligation.
      destruct frf.
      unfold rvpow.
      simpl.
      apply in_map_iff.
      eauto.
    Qed.

    Global Program Instance frfabs
           (rv_X : Ts -> R)
           {frf:FiniteRangeFunction rv_X} : FiniteRangeFunction (rvabs rv_X)
      := { frf_vals := map Rabs frf_vals }.
    Next Obligation.
      destruct frf.
      unfold rvabs.
      now apply in_map.
    Qed.


    Global Instance frfchoice (c:Ts->bool) x y
           {frfx:FiniteRangeFunction x}
           {frfy:FiniteRangeFunction y}
      : FiniteRangeFunction (rvchoice c x y).
    Proof.
      destruct frfx; destruct frfy.
      exists (frf_vals ++ frf_vals0).
      intros.
      rewrite in_app_iff.
      unfold rvchoice.
      match_destr; auto.
    Qed.
    
    Global Program Instance frfmax
           (rv_X1 rv_X2 : Ts -> R)
           {frf1:FiniteRangeFunction rv_X1}
           {frf2:FiniteRangeFunction rv_X2}
      : FiniteRangeFunction (rvmax rv_X1 rv_X2)
      := { frf_vals := map (fun ab => Rmax (fst ab) (snd ab)) 
                           (list_prod (frf_vals (FiniteRangeFunction:=frf1))
                                      (frf_vals (FiniteRangeFunction:=frf2))) }.
    Next Obligation.
      destruct frf1.
      destruct frf2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Program Instance frfmin
           (rv_X1 rv_X2 : Ts -> R)
           {frf1:FiniteRangeFunction rv_X1}
           {frf2:FiniteRangeFunction rv_X2}
      : FiniteRangeFunction (rvmin rv_X1 rv_X2)
      := { frf_vals := map (fun ab => Rmin (fst ab) (snd ab)) 
                           (list_prod (frf_vals (FiniteRangeFunction:=frf1))
                                      (frf_vals (FiniteRangeFunction:=frf2))) }.
    Next Obligation.
      destruct frf1.
      destruct frf2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Instance frfsum (X : nat -> Ts -> R) 
           {rv : forall (n:nat), FiniteRangeFunction (X n)} (n : nat) :
      FiniteRangeFunction (rvsum X n).
    Proof.
      induction n.
      - assert (rv_eq  (rvsum X 0) (X 0%nat)).
        + intro x.
          unfold rvsum. cbn.
          lra.
        + eapply FiniteRangeFunction_ext.
          * symmetry; apply H.
          * apply rv.
      - assert (rv_eq (rvsum X (S n)) (rvplus (X (S n)) (rvsum X n))).
        + intro x.
          unfold rvplus, rvsum.
          rewrite sum_Sn; unfold plus; simpl.
          lra.
        + eapply FiniteRangeFunction_ext.
          * rewrite H; reflexivity.
          * apply frfplus; trivial.
    Qed.
    
    Global Program Instance positive_part_frf'
           (rv_X : Ts -> R) 
           {frf: FiniteRangeFunction rv_X } : FiniteRangeFunction (pos_fun_part rv_X)
      :=  { frf_vals := map (fun x => mknonnegreal (Rmax x 0) _) frf_vals}.
    Next Obligation.
      apply Rmax_r.
    Defined.
    Next Obligation.
      destruct frf.
      apply in_map_iff.
      unfold RandomVariable.frf_vals.
      exists (rv_X x).
      split; trivial.
    Qed.
    
    Global Program Instance positive_part_frf
           (rv_X : Ts -> R) 
           {frf: FiniteRangeFunction rv_X } : FiniteRangeFunction (fun x => nonneg (pos_fun_part rv_X x))
      :=  { frf_vals := map (fun x => (Rmax x 0)) frf_vals}.
    Next Obligation.
      destruct frf.
      apply in_map_iff.
      unfold RandomVariable.frf_vals.
      exists (rv_X x).
      split; trivial.
    Qed.    

    Global Program Instance negative_part_frf'
           (rv_X : Ts -> R) 
           {frf: FiniteRangeFunction rv_X } : FiniteRangeFunction (neg_fun_part rv_X)
      :=  { frf_vals := map (fun x => mknonnegreal (Rmax (- x) 0) _) frf_vals}.
    Next Obligation.
      apply Rmax_r.
    Defined.
    Next Obligation.
      destruct frf.
      apply in_map_iff.
      unfold RandomVariable.frf_vals.
      unfold neg_fun_part.
      exists (rv_X x).
      split; trivial.
    Qed.

    Global Program Instance negative_part_frf
           (rv_X : Ts -> R) 
           {frf: FiniteRangeFunction rv_X } : FiniteRangeFunction (fun x => nonneg (neg_fun_part rv_X x))
      :=  { frf_vals := map (fun x => (Rmax (- x) 0)) frf_vals}.
    Next Obligation.
      destruct frf.
      apply in_map_iff.
      unfold RandomVariable.frf_vals.
      exists (rv_X x).
      split; trivial.
    Qed.

    Program Instance FiniteRangeFunction_enlarged
            {rv_X : Ts -> R}
            (frf:FiniteRangeFunction rv_X)
            (l:list R)
            (lincl : incl frf_vals l)
      : FiniteRangeFunction rv_X :=
      {
      frf_vals := l
      }.
    Next Obligation.
      apply lincl.
      apply frf_vals_complete.
    Qed.


  End Simple.

  
  Section Indicator.
    
    Class IndicatorRandomVariable
          (rv_X : Ts -> R) :=
      irv_binary : forall x, In (rv_X x) [0;1] .
    

    Global Program Instance IndicatorRandomVariableSimpl
           rv_X
           {irv: IndicatorRandomVariable rv_X} : FiniteRangeFunction rv_X
      := {frf_vals := [0;1]}.
    Next Obligation.
      apply irv.
    Qed.

    Global Instance EventIndicator_pre_rv {P : pre_event Ts} (dec:forall x, {P x} + {~ P x}) :
      sa_sigma P ->
      RandomVariable dom borel_sa (EventIndicator dec).
    Proof.
      red; intros.
      apply borel_sa_preimage; trivial; intros.
      destruct (Rlt_dec r 0).
      - unfold EventIndicator.
        simpl.
        assert (pre_event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                                event_none).
        + unfold pre_event_equiv, event_none, pre_event_none; intros; simpl.
          destruct (dec x); lra.
        + rewrite H0; apply sa_none.
      - destruct (Rlt_dec r 1).
        + assert (pre_event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                                  (fun omega : Ts => ~ P omega)).
          * unfold pre_event_equiv; intros.
            destruct (dec x).
            -- split; [lra | congruence].
            -- split; [congruence | lra].
          * rewrite H0.
            now apply sa_complement.
        + assert (pre_event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                                  (fun omega : Ts => True)).
          * unfold pre_event_equiv; intros.
            destruct (dec x); lra.
          * rewrite H0.
            apply sa_all.
    Qed.

    Global Instance EventIndicator_pre_indicator (P : pre_event Ts) (dec:forall x, {P x} + {~ P x})
      : IndicatorRandomVariable (EventIndicator dec).
    Proof.
      unfold EventIndicator.
      intros x.
      simpl.
      match_destr; tauto.
    Qed.

    Global Program Instance EventIndicator_pre_frf {P : pre_event Ts} (dec:forall x, {P x} + {~ P x})
      : FiniteRangeFunction (EventIndicator dec) :=
      IndicatorRandomVariableSimpl (EventIndicator dec).

    Global Program Instance EventIndicator_frf {P : event dom} (dec:forall x, {P x} + {~ P x})
      : FiniteRangeFunction (EventIndicator dec) :=
      IndicatorRandomVariableSimpl (EventIndicator dec).

    Global Instance EventIndicator_rv {P : event dom} (dec:forall x, {P x} + {~ P x}) :
      RandomVariable dom borel_sa (EventIndicator dec).
    Proof.
      apply EventIndicator_pre_rv.
      now destruct P.
    Qed.
    
    Definition point_preimage_indicator
               (rv_X:Ts -> R)
               (c:R) :=
      EventIndicator (fun x => Req_EM_T (rv_X x) c).

    Global Instance point_preimage_indicator_rv
           {rv_X:Ts -> R}
           (rv: RandomVariable dom borel_sa rv_X)
           (c:R) : RandomVariable dom borel_sa (point_preimage_indicator rv_X c).
    Proof.
      unfold point_preimage_indicator.
      apply EventIndicator_pre_rv.
      now apply sa_preimage_singleton.
    Qed.    
    
    Global Instance point_preimage_indicator_frf
           {rv_X:Ts -> R}
           (rv: RandomVariable dom borel_sa rv_X)
           (c:R) : FiniteRangeFunction (point_preimage_indicator rv_X c)
      := IndicatorRandomVariableSimpl _.

    Lemma preimage_indicator_notin (rv_X : Ts -> R) l :
      forall a:Ts,
        ~ In (rv_X a) l ->
        list_sum 
          (map 
             (fun c => c * (point_preimage_indicator rv_X c a))
             (nodup Req_EM_T l)) = 0.
    Proof.
      intros.
      erewrite map_ext_in.
      - apply list_sum_map_zero.
      - intros.
        apply nodup_In in H0.
        unfold point_preimage_indicator, EventIndicator.
        match_destr.
        + congruence.
        + lra.
    Qed.


    Lemma frf_preimage_indicator (rv_X : Ts -> R) {frf:FiniteRangeFunction rv_X} :
      forall a:Ts, rv_X a =
                   list_sum 
                     (map 
                        (fun c => c * (point_preimage_indicator rv_X c a))
                        (nodup Req_EM_T frf_vals)).
    Proof.
      intros.
      destruct frf; simpl.
      specialize (frf_vals_complete a).
      induction frf_vals; simpl in frf_vals_complete; [tauto |].
      simpl.
      match_destr.
      - apply IHfrf_vals.
        intuition congruence.
      - simpl.
        destruct frf_vals_complete.
        + subst.
          rewrite preimage_indicator_notin; trivial.
          unfold point_preimage_indicator, EventIndicator.
          match_destr; lra.
        + rewrite IHfrf_vals; trivial.
          unfold point_preimage_indicator, EventIndicator.
          match_destr.
          * subst.
            tauto.
          * lra.
    Qed.

    Lemma frf_preimage_indicator' (rv_X : Ts -> R) {frf:FiniteRangeFunction rv_X} :
      pointwise_relation Ts eq rv_X
                         (fun a => list_sum 
                                     (map 
                                        (fun c => c * (point_preimage_indicator rv_X c a))
                                        (nodup Req_EM_T frf_vals))).
    Proof.
      repeat red; intros.
      apply frf_preimage_indicator.
    Qed.

  End Indicator.

  Section Pos.
    
    Class NonnegativeFunction
          (rv_X:Ts->R) : Prop :=
      nnf : forall (x:Ts), (0 <= rv_X x)%R.

    Class Rbar_NonnegativeFunction
          (rv_X:Ts->Rbar) : Prop :=
      Rbar_nnf : forall (x:Ts), (Rbar_le 0 (rv_X x)).

    Global Instance positive_Rbar_positive
           (rv_X:Ts->R) 
           {nnf : NonnegativeFunction rv_X} :
      Rbar_NonnegativeFunction rv_X.
    Proof.
      easy.
    Qed.

    Global Instance NonnegativeFunction_proper : Proper (rv_eq ==> iff) NonnegativeFunction.
    Proof.
      unfold NonnegativeFunction, rv_eq, pointwise_relation.
      intros x y eqq.
      split; intros lle z.
      - rewrite <- eqq; auto.
      - rewrite eqq; auto.
    Qed.

    Global Instance NonnegativeFunction_le_proper : Proper (rv_le ==> impl) NonnegativeFunction.
    Proof.
      unfold NonnegativeFunction, rv_le.
      intros x y eqq lle z.
      eapply Rle_trans; eauto.
    Qed.

    Global Instance nnfconst c (cpos:0<=c) : NonnegativeFunction (const c).
    Proof.
      intros x.
      unfold const; trivial.
    Qed.
    
    Global Instance nnfconstinr (c : nat) : NonnegativeFunction (const (INR c)).
    Proof.
      apply nnfconst.
      apply pos_INR.
    Qed.

    Global Instance IndicatorRandomVariable_positive (rv_X:Ts->R)
           {irvx:IndicatorRandomVariable rv_X} :
      NonnegativeFunction rv_X.
    Proof.
      red in irvx; simpl in irvx.
      intros x.
      destruct (irvx x) as [|[|]]
      ; try rewrite <- H; try lra.
    Qed.

    Global Instance positive_scale_nnf (c:posreal) 
           (rv_X : Ts -> R)
           {nnf : NonnegativeFunction rv_X} :
      NonnegativeFunction (rvscale c rv_X).
    Proof.
      red; intros.
      red in nnf.
      assert (0 < c) by apply (cond_pos c).
      unfold rvscale.
      specialize (nnf x).
      replace (0) with (c*0) by lra.    
      apply Rmult_le_compat_l; trivial.
      now left.
    Qed.

    Global Instance rvplus_nnf (rv_X1 rv_X2 : Ts -> R)
           {rv1 : NonnegativeFunction rv_X1}
           {rv2 : NonnegativeFunction rv_X2} :
      NonnegativeFunction (rvplus rv_X1 rv_X2).
    Proof.
      unfold NonnegativeFunction in *.
      unfold rvplus.
      intros.
      specialize (rv1 x); specialize (rv2 x).
      lra.
    Qed.

    Global Instance rvsum_pos (Xn : nat -> Ts -> R)
           {Xn_pos : forall n, NonnegativeFunction (Xn n)} :
      forall (n:nat), NonnegativeFunction (rvsum Xn n).
    Proof.
      intros.
      unfold NonnegativeFunction in Xn_pos.
      unfold NonnegativeFunction, rvsum; intros.
      induction n.
      - unfold Hierarchy.sum_n.
        now rewrite Hierarchy.sum_n_n.
      - unfold Hierarchy.sum_n.
        rewrite Hierarchy.sum_n_Sm.
        apply Rplus_le_le_0_compat ; trivial.
        lia.
    Qed.

    Global Instance indicator_prod_pos 
           (rv_X : Ts -> R) 
           (pofrf : NonnegativeFunction rv_X)
           {P : pre_event Ts} 
           (dec:forall x, {P x} + {~ P x}) : 
      NonnegativeFunction (rvmult rv_X (EventIndicator dec)).
    Proof.
      intros x.
      unfold rvmult, EventIndicator.
      unfold NonnegativeFunction in pofrf.
      apply Rmult_le_pos; trivial.
      match_destr; lra.
    Qed.

    Global Instance NonNegMult (f g : Ts -> R)
             {nnf : NonnegativeFunction f}
             {nng : NonnegativeFunction g} :
      NonnegativeFunction (rvmult g f).
    Proof.
      intro x.
      unfold rvmult.
      now apply Rmult_le_pos.
    Qed.

    Global Instance EventIndicator_pos {P : pre_event Ts} (dec:forall x, {P x} + {~ P x})
      : NonnegativeFunction (EventIndicator dec).
    Proof.
      typeclasses eauto.
    Qed.


    Global Instance rvscale_nnf (phival : posreal)
           (rv_X : Ts -> R) 
           (pofrf : NonnegativeFunction rv_X) :
      NonnegativeFunction (rvscale phival rv_X).
    Proof.
      intro x.
      unfold rvscale.
      apply Rmult_le_pos; trivial.
      left; apply cond_pos.
    Qed.

    Global Instance nnfabs
           (rv_X : Ts -> R) :
      NonnegativeFunction (rvabs rv_X).
    Proof.
      unfold NonnegativeFunction, rvabs.
      intros; apply Rabs_pos.
    Qed.

    Lemma rvabs_pos_eq (rv_X:Ts->R) {nnf:NonnegativeFunction rv_X} :
      rv_eq (rvabs rv_X) rv_X.
    Proof.
      intros a.
      unfold rvabs.
      now rewrite Rabs_pos_eq.
    Qed.


    Global Instance nnfsqr
           (rv_X : Ts -> R) :
      NonnegativeFunction (rvsqr rv_X).
    Proof.
      unfold NonnegativeFunction, rvsqr.
      intros.
      apply Rle_0_sqr.
    Qed.


    Global Instance nnflim
           (Xn : nat -> Ts -> R) 
           (pofrf : forall n, NonnegativeFunction (Xn n)) :
      NonnegativeFunction (rvlim Xn).
    Proof.
      unfold NonnegativeFunction, rvlim.
      unfold NonnegativeFunction in pofrf.
      intros.
      generalize (Lim_seq_le_loc (fun _ => 0) (fun n => Xn n x)); intros.
      rewrite Lim_seq_const in H.
      cut_to H.
      - destruct (classic (is_finite (Lim_seq (fun n : nat => Xn n x)))).
        + rewrite <- H0 in H.
          now simpl in H.
        + unfold real.
          match_destr; lra.
      - exists 0%nat.
        intros; try lia.
        apply pofrf.
    Qed.

    Global Instance rvpow_nnf
           (rv_X : Ts -> R) 
           (k : nat) 
           (nnf : NonnegativeFunction rv_X) :
      NonnegativeFunction (rvpow rv_X k).
    Proof.
      unfold NonnegativeFunction, rvpow.
      unfold NonnegativeFunction in nnf.
      intros.
      now apply pow_le.
    Qed.

    Global Instance rvpower_nnf
           (rv_X1 rv_X2 : Ts -> R) :
      NonnegativeFunction (rvpower rv_X1 rv_X2).
    Proof.
      unfold NonnegativeFunction, rvpower in *.
      intros.
      apply power_nonneg.
    Qed.

    (* Here so that we can state the positivity constraint nicely *)
    Global Instance rvpower_rv 
           (rv_X1 rv_X2 : Ts -> R)
           {rv1 : RandomVariable dom borel_sa rv_X1}
           {rv2 : RandomVariable dom borel_sa rv_X2}
           {nnf1: NonnegativeFunction rv_X1}:
      RandomVariable dom borel_sa (rvpower rv_X1 rv_X2).
    Proof.
      apply measurable_rv.
      apply rvpower_measurable; trivial
      ; apply rv_measurable; trivial.
    Qed.
    
    (*
    Definition rvsqrt (rv_X : Ts -> R)
                      (nnf : NonnegativeFunction rv_X) := 
      fun omega => Rsqrt (mknonnegreal (rv_X omega) (nnf omega)).

    Instance rvsqrt_measurable (rv_X : Ts -> R) 
             (xpos: NonnegativeFunction rv_X) :
      RealMeasurable rv_X ->
      RealMeasurable (rvsqrt rv_X xpos).
    Proof.
      intros.
      apply RealMeasurable_proper with
          (x := rvpower (fun x => mknonnegreal (rv_X x) (xpos x)) (fun _ => / 2)).
      intro x.
      unfold rvpower.
      now rewrite power_2_sqrt.
      apply rvpower_measurable; trivial.
      apply constant_measurable.
    Qed.

    Global Instance rvsqrt_rv 
           (rv_X : Ts -> R)
           {rv : RandomVariable dom borel_sa rv_X}
           {nnf: NonnegativeFunction rv_X}:
      RandomVariable dom borel_sa (rvsqrt rv_X nnf).
    Proof.
      apply measurable_rv.
      apply rvsqrt_measurable; trivial
      ; apply rv_measurable; trivial.
    Qed.

    Definition frfsqrt_simplemapping l :=
      map (fun x =>
             match Rle_dec 0 x with
             | left pf => Rsqrt (mknonnegreal _ pf)
             | right _ => 0
             end) l.

    Global Program Instance frfsqrt
           (rv_X : Ts -> R)
           {nnf: NonnegativeFunction rv_X}
           {frf:FiniteRangeFunction rv_X} : FiniteRangeFunction (rvsqrt rv_X nnf)
      := { frf_vals := frfsqrt_simplemapping frf_vals }.
    Next Obligation.
      unfold frfsqrt_simplemapping.
      apply in_map_iff.
      unfold rvsqrt; simpl.
      exists (rv_X x); simpl.
      destruct frf.
      red in nnf0.
      match_destr.
      - split; trivial.
        now apply Rsqrt_ext.
      - generalize (nnf0 x).
        congruence.
    Qed.
     *)
    Global Instance nnfchoice (c:Ts->bool) (rv_X1 rv_X2 : Ts -> R)
           {nnf1:NonnegativeFunction rv_X1}
           {nnf2:NonnegativeFunction rv_X2} :
      NonnegativeFunction (rvchoice c rv_X1 rv_X2).
    Proof.
      unfold NonnegativeFunction in *.
      intros x.
      unfold rvchoice.
      match_destr.
    Qed.

    Global Instance nnfmin (rv_X1 rv_X2 : Ts -> R)
           {nnf1:NonnegativeFunction rv_X1}
           {nnf2:NonnegativeFunction rv_X2} :
      NonnegativeFunction (rvmin rv_X1 rv_X2).
    Proof.
      unfold NonnegativeFunction in *.
      intros x.
      unfold rvmin.
      eapply Rmin_glb; eauto.
    Qed.

    Global Instance nnfmax_l  (rv_X1 rv_X2 : Ts -> R)
           {nnf1:NonnegativeFunction rv_X1} : NonnegativeFunction (rvmax rv_X1 rv_X2).
    Proof.
      intros x.
      unfold rvmax.
      eapply Rle_trans; try eapply (nnf1 x).
      eapply Rmax_l.
    Qed.

    Global Instance nnfmax_r  (rv_X1 rv_X2 : Ts -> R)
           {nnf1:NonnegativeFunction rv_X2} : NonnegativeFunction (rvmax rv_X1 rv_X2).
    Proof.
      intros x.
      unfold rvmax.
      eapply Rle_trans; try eapply (nnf1 x).
      eapply Rmax_r.
    Qed.

    Global Instance positive_part_nnf 
           (rv_X : Ts -> R) :
      NonnegativeFunction (pos_fun_part rv_X).
    Proof.
      unfold NonnegativeFunction.
      unfold pos_fun_part; simpl.
      intros.
      apply Rmax_r.
    Qed.

    
    Global Instance negative_part_nnf
           (rv_X : Ts -> R) :
      NonnegativeFunction (neg_fun_part rv_X).
    Proof.
      unfold NonnegativeFunction.
      unfold neg_fun_part.
      intros.
      apply cond_nonneg.
    Qed.
    
  End Pos.

  Instance rv_fun_simple_R (x : Ts -> R) (f : R -> R)
           (rvx : RandomVariable dom borel_sa x) 
           (frfx : FiniteRangeFunction x) :
    RandomVariable dom borel_sa (fun u => f (x u)).    
  Proof.
    eapply rv_fun_simple; eauto.
    intros.
    now apply sa_preimage_singleton.
  Qed.

  Lemma sa_le_ge_rv 
        (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : sa_sigma (fun omega => rv_X omega >= x).
  Proof.
    apply sa_le_ge.
    now apply rv_measurable.
  Qed.

  Definition event_ge 
             (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : event dom
    := @exist (pre_event Ts) _ _ (sa_le_ge_rv rv_X x).

  Lemma sa_le_le_rv 
        (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : sa_sigma (fun omega => rv_X omega <= x).
  Proof.
    now apply rv_measurable.
  Qed.

  Definition event_le
             (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : event dom
    := @exist (pre_event Ts) _ _ (sa_le_le_rv rv_X x).

  Lemma sa_le_lt_rv 
        (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : sa_sigma (fun omega => rv_X omega < x).
  Proof.
    apply sa_le_lt.
    now apply rv_measurable.
  Qed.

  Definition event_lt
             (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : event dom
    := @exist (pre_event Ts) _ _ (sa_le_lt_rv rv_X x).
  
  Lemma sa_le_gt_rv 
        (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : sa_sigma (fun omega => rv_X omega > x).
  Proof.
    apply sa_le_gt.
    now apply rv_measurable.
  Qed.

  Definition event_gt
             (rv_X : Ts -> R) {rv : RandomVariable dom borel_sa rv_X} x
    : event dom
    := @exist (pre_event Ts) _ _ (sa_le_gt_rv rv_X x).

End RealRandomVariables.

Section MoreRealRandomVariable.

  Context {Ts:Type}.

  Lemma event_Rgt_sa (σ:SigmaAlgebra Ts) x1 x2
        {rv1:RandomVariable σ borel_sa x1}
        {rv2:RandomVariable σ borel_sa x2}
    : sa_sigma (fun x => x1 x > x2 x).
  Proof.
    apply (sa_proper _ (fun x => (rvminus x1 x2) x > 0)).
    -  red; intros.
       rv_unfold.
       intuition lra.
    - apply sa_le_gt; intros.
      apply rv_measurable.
      typeclasses eauto.
  Qed.

  Definition event_Rgt (σ:SigmaAlgebra Ts) x1 x2
             {rv1:RandomVariable σ borel_sa x1}
             {rv2:RandomVariable σ borel_sa x2} : event σ
    := exist _ _ (event_Rgt_sa σ x1 x2).

  Lemma event_Rgt_dec (σ:SigmaAlgebra Ts) x1 x2
        {rv1:RandomVariable σ borel_sa x1}
        {rv2:RandomVariable σ borel_sa x2} :
    dec_event (event_Rgt σ x1 x2).
  Proof.
    unfold event_Rgt.
    intros x; simpl.
    apply Rgt_dec.
  Qed.

  Definition dec_sa_event_Rgt (σ:SigmaAlgebra Ts) x1 x2
             {rv1:RandomVariable σ borel_sa x1}
             {rv2:RandomVariable σ borel_sa x2}
    : dec_sa_event (σ:=σ)
    := {| dsa_event := event_Rgt σ x1 x2
          ; dsa_dec := event_Rgt_dec σ x1 x2
       |}.

  Lemma event_ge_dec (σ:SigmaAlgebra Ts) x1 n
        {rv1:RandomVariable σ borel_sa x1} :
    dec_event (event_ge σ x1 n).
  Proof.
    unfold event_ge.
    intros x; simpl.
    apply Rge_dec.
  Qed.

  Lemma event_ge_pre_dec (σ:SigmaAlgebra Ts) x1 n
        {rv1:RandomVariable σ borel_sa x1} :
    dec_pre_event (event_ge σ x1 n).
  Proof.
    unfold event_ge.
    intros x; simpl.
    apply Rge_dec.
  Qed.

  Definition dec_sa_event_ge (σ:SigmaAlgebra Ts) x1 n
             {rv1:RandomVariable σ borel_sa x1}
    : dec_sa_event (σ:=σ)
    := {| dsa_event := event_ge σ x1 n
          ; dsa_dec := event_ge_dec σ x1 n
       |}.

End MoreRealRandomVariable.

Section RbarRandomVariables.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}.

  Lemma RealMeasurable_RbarMeasurable (f : Ts -> R) :
    RealMeasurable dom f <-> RbarMeasurable f.
  Proof.
    unfold RealMeasurable, RbarMeasurable.
    split; intros.
    - destruct r.
      + apply H.
      + apply sa_all.
      + apply sa_none.      
    - specialize (H r).
      apply H.
  Qed.

  Lemma borel_Rbar_borel (f : Ts -> R) :
    RandomVariable dom borel_sa f <-> RandomVariable dom Rbar_borel_sa f.
  Proof.
    unfold RandomVariable.
    generalize (RealMeasurable_RbarMeasurable f); intros.
    unfold RealMeasurable, RbarMeasurable in H.
    destruct H.
    split; intros.
    - apply Rbar_borel_sa_preimage2.
      apply H.
      now apply borel_sa_preimage2.
    - apply borel_sa_preimage2.
      apply H0.
      now apply Rbar_borel_sa_preimage2.
  Qed.

  Global Instance Rbar_measurable_rv (rv_X:Ts->Rbar)
         {rm:RbarMeasurable rv_X}
    : RandomVariable dom Rbar_borel_sa rv_X.
  Proof.
    intros ?.
    apply Rbar_borel_sa_preimage2; trivial; intros.
  Qed.

  Global Instance rv_Rbar_measurable (rv_X : Ts -> Rbar)
         {rrv:RandomVariable dom Rbar_borel_sa rv_X}
    : RbarMeasurable rv_X.
  Proof.
    red.
    now rewrite Rbar_borel_sa_preimage2.
  Qed.

  Global Instance RbarMeasurable_proper :
    Proper (rv_eq ==> iff) RbarMeasurable.
  Proof.
    intros ???.
    split; intros.
    - apply rv_Rbar_measurable.
      rewrite <- H.
      now apply Rbar_measurable_rv.
    - apply rv_Rbar_measurable.
      rewrite H.
      now apply Rbar_measurable_rv.
  Qed.

  Global Instance Rbar_rvchoice_rv
         (rv_C : Ts -> R) (rv_X1 rv_X2 : Ts -> Rbar)
         {rvc : RandomVariable dom borel_sa rv_C}
         {rv1 : RandomVariable dom Rbar_borel_sa rv_X1}
         {rv2 : RandomVariable dom Rbar_borel_sa rv_X2}  :
    RbarMeasurable (Rbar_rvchoice (fun x => if Req_EM_T (rv_C x) 0 then false else true) rv_X1 rv_X2).
  Proof.
    apply Rbar_rvchoice_measurable.
    - now apply rv_measurable.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

  Definition Rbar_finite_part (rv_X : Ts -> Rbar) : (Ts -> R) :=
    (fun x => real (rv_X x)).

  Instance Rbar_finite_part_meas (rv_X : Ts -> Rbar) 
           (rv : RandomVariable dom Rbar_borel_sa rv_X) :
    RealMeasurable dom (Rbar_finite_part rv_X).
  Proof.
    unfold RealMeasurable.
    intros.
    apply rv_Rbar_measurable in rv.
    unfold RbarMeasurable in rv.
    destruct (Rle_dec 0 r).
    - assert (pre_event_equiv
                (fun omega : Ts =>
                   (Rbar_finite_part rv_X) omega <= r)
                (pre_event_union 
                   (fun omega : Ts => rv_X omega = p_infty)
                   (fun omega : Ts => Rbar_le (rv_X omega) r))).
      + intro x.
        unfold pre_event_union, Rbar_finite_part.
        destruct (rv_X x); split; intros; simpl; trivial; try tauto.
        destruct H; trivial; now simpl.
      + rewrite H.
        apply sa_union.
        * now apply Rbar_sa_le_pt.
        * apply rv.
    - assert (0 > r) by lra.
      assert (pre_event_equiv
                (fun omega : Ts =>
                   (Rbar_finite_part rv_X) omega <= r)
                (pre_event_inter
                   (pre_event_complement
                      (fun omega : Ts => (rv_X omega) = m_infty ))
                   (fun omega : Ts => Rbar_le (rv_X omega) r))).
      + intro x.
        unfold pre_event_inter, pre_event_complement, Rbar_finite_part.
        destruct (rv_X x); split; intros; simpl; trivial; try tauto.
        split; trivial; discriminate.
      + rewrite H0.
        apply sa_inter.
        * apply sa_complement.
          now apply Rbar_sa_le_pt.
        * apply rv.
  Qed.

  Lemma sa_pinf_Rbar
        (f : Ts -> Rbar) 
        (rv : RandomVariable dom Rbar_borel_sa f) :
    sa_sigma (fun x => (f x) = p_infty).
  Proof.
    apply Rbar_sa_le_pt.
    now rewrite Rbar_borel_sa_preimage2.
  Qed.

  Lemma sa_minf_Rbar
        (f : Ts -> Rbar) 
        (rv : RandomVariable dom Rbar_borel_sa f) :
    sa_sigma (fun x => (f x) = m_infty).
  Proof.
    apply Rbar_sa_le_pt.
    now rewrite Rbar_borel_sa_preimage2.
  Qed.

  Lemma sa_finite_Rbar
        (f : Ts -> Rbar) 
        (rv : RandomVariable dom Rbar_borel_sa f) :
    sa_sigma (fun x => is_finite (f x)).
  Proof.
    assert (pre_event_equiv (fun x => is_finite (f x))
                            (pre_event_complement
                               (pre_event_union
                                  (fun omega => (f omega) = p_infty)
                                  (fun omega => (f omega) = m_infty)
           ))).
    intro z.
    unfold is_finite, pre_event_complement, pre_event_union.
    destruct (f z); intuition discriminate.
    rewrite H.
    apply sa_complement.
    apply sa_union.
    + now apply sa_pinf_Rbar.
    + now apply sa_minf_Rbar.
  Qed.

  Global Instance Real_Rbar_rv (rv_X:Ts->R)
         {rv : RandomVariable dom borel_sa rv_X} :
    RandomVariable dom Rbar_borel_sa rv_X.
  Proof.
    apply Rbar_measurable_rv.
    apply rv_measurable in rv.
    unfold RealMeasurable in rv.
    unfold RbarMeasurable.
    intros.
    destruct r.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (rv_X omega) r)
                (fun omega : Ts => rv_X omega <= r)) by easy.
      now rewrite H.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (rv_X omega) p_infty)
                (fun omega => True)) by easy.
      rewrite H.
      apply sa_all.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (rv_X omega) m_infty)
                (fun omega => False)) by easy.
      rewrite H.
      apply sa_none.
  Qed.                

  Definition Rbar_rvlim (f : nat -> Ts -> R) : (Ts -> Rbar) :=
    (fun omega => Lim_seq (fun n => f n omega)).

  Global Instance Rbar_rvlim_nnf
         (Xn : nat -> Ts -> R) 
         (pofrf : forall n, NonnegativeFunction (Xn n)) :
    Rbar_NonnegativeFunction (Rbar_rvlim Xn).
  Proof.
    unfold Rbar_NonnegativeFunction, Rbar_rvlim.
    unfold NonnegativeFunction in pofrf.
    intros.
    generalize (Lim_seq_le_loc (fun _ => 0) (fun n => Xn n x)); intros.
    rewrite Lim_seq_const in H.
    apply H.
    now exists 0%nat.
  Qed.

  Lemma Rbar_rvlim_pos_ge
        (Xn : nat -> Ts -> R)          
        (Xn_pos : forall n, NonnegativeFunction (Xn n)) :
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
        unfold NonnegativeFunction in Xn_pos.
        assert (forall n, 0 <= Xn n x); intros.
        apply Xn_pos.
        generalize (is_lim_seq_le _ _ _ _ H2 H1 H0); intros.
        now simpl in H3.
    - apply ex_lim_seq_incr.
      intros.
      apply H.
  Qed.

  Lemma rvlim_rvmin (f : Ts -> R) :
    rv_eq (Rbar_rvlim (fun n => rvmin f (const (INR n)))) f.
  Proof.
    intro x.
    unfold Rbar_rvlim, rvmin, const.
    now rewrite Lim_seq_min.
  Qed.

  Definition Rbar_rvplus (rv_X1 rv_X2 : Ts -> Rbar) :=
    (fun omega =>  Rbar_plus (rv_X1 omega) (rv_X2 omega)).

  Definition Rbar_rvopp (rv_X : Ts -> Rbar) :=
    (fun omega =>  Rbar_opp (rv_X omega)).

  Definition Rbar_rvminus (rv_X1 rv_X2 : Ts -> Rbar) :=
    Rbar_rvplus rv_X1 (Rbar_rvopp rv_X2).

  Definition Rbar_sqr (x:Rbar)
    := match x with
       | Finite x' => Finite (Rsqr x')
       | p_infty => p_infty
       | m_infty => m_infty
       end.
  
  Definition Rbar_rvsqr (rv_X : Ts -> Rbar) :=
    (fun omega =>  Rbar_sqr (rv_X omega)).

  Definition Rbar_rvmult (x y:Ts->Rbar) omega :=
    Rbar_mult (x omega) (y omega).

  Global Instance pos_Rbar_plus (f g : Ts -> Rbar) 
         {fpos : Rbar_NonnegativeFunction f}
         {gpos: Rbar_NonnegativeFunction g} :
    Rbar_NonnegativeFunction (Rbar_rvplus f g).
  Proof.
    unfold Rbar_NonnegativeFunction in *.
    unfold Rbar_rvplus.
    intro.
    replace (Finite 0) with (Rbar_plus 0 0).
    apply Rbar_plus_le_compat; trivial.
    simpl.
    now rewrite Rplus_0_r.
  Qed.

  
  Instance Rbar_div_pos_measurable (f : Ts -> Rbar) (c : posreal) :
    RbarMeasurable f ->
    RbarMeasurable (fun omega => Rbar_div_pos (f omega) c).
  Proof.
    unfold RbarMeasurable.
    intros.
    assert (pre_event_equiv
              (fun omega : Ts => Rbar_le (Rbar_div_pos (f omega) c) r)
              (fun omega : Ts => Rbar_le (f omega) (Rbar_mult_pos r c))).
    {
      intros x.
      replace (r) with (Rbar_div_pos (Rbar_mult_pos r c) c) at 1.
      now rewrite <- Rbar_div_pos_le.
      unfold Rbar_div_pos, Rbar_mult_pos.
      destruct r; trivial.
      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite Rinv_r.
      - rewrite Rmult_1_r.
        reflexivity.
      - apply Rgt_not_eq, cond_pos.
    }
    now rewrite H0.
  Qed.

  Instance Rbar_inf_measurable (f : nat -> Ts -> Rbar) :
    (forall n, RbarMeasurable (f n)) ->
    RbarMeasurable (fun omega => Inf_seq (fun n => f n omega)).
  Proof.
    unfold RbarMeasurable; intros.
    apply Rbar_sa_ge_le; intros.
    assert (forall (n:nat) (r:Rbar), sa_sigma (fun omega : Ts => Rbar_ge (f n omega) r)) by
        (intros; now apply Rbar_sa_le_ge).
    assert (pre_event_equiv
              (fun omega : Ts => Rbar_ge (Inf_seq (fun n : nat => f n omega)) r0)
              (pre_inter_of_collection
                 (fun n => 
                    fun omega => Rbar_ge (f n omega) r0))).
    {
      intro x.
      unfold pre_inter_of_collection.
      unfold Inf_seq, proj1_sig.
      match_destr.
      generalize (is_inf_seq_glb _ _ i); intros.
      unfold Rbar_is_glb, Rbar_is_lower_bound in H1.
      destruct H1.
      unfold Rbar_ge in *.
      split; intros.
      - specialize (H1 (f n x)).
        eapply Rbar_le_trans.
        apply H3.
        apply H1.
        now exists n.
                   - specialize (H2 r0).
                     apply H2.
                     intros.
                     destruct H4.
                     rewrite H4.
                     apply H3.
    }
    rewrite H1.
    now apply sa_pre_countable_inter.
  Qed.


  Instance Rbar_sup_measurable (f : nat -> Ts -> Rbar) :
    (forall n, RbarMeasurable (f n)) ->
    RbarMeasurable (fun omega => Sup_seq (fun n => f n omega)).
  Proof.
    unfold RbarMeasurable; intros.
    assert (pre_event_equiv
              (fun omega : Ts => Rbar_le (Sup_seq (fun n : nat => f n omega)) r)
              (pre_inter_of_collection
                 (fun n => 
                    fun omega => Rbar_le (f n omega) r))).
    {
      intro x.
      unfold pre_inter_of_collection.
      unfold Sup_seq, proj1_sig.
      match_destr.
      generalize (is_sup_seq_lub _ _ i); intros.
      unfold Rbar_is_lub, Rbar_is_upper_bound in H0.
      destruct H0.
      split; intros.
      - specialize (H0 (f n x)).
        eapply Rbar_le_trans.
        apply H0.
        now exists n.
                   apply H2.
                   - specialize (H1 r).
                     apply H1.
                     intros.
                     destruct H3.
                     rewrite H3.
                     apply H2.
    }
    rewrite H0.
    now apply sa_pre_countable_inter.
  Qed.

  Instance Rbar_lim_sup_measurable (f : nat -> Ts -> R) :
    (forall n, RbarMeasurable (f n)) ->
    RbarMeasurable (fun omega => LimSup_seq (fun n => f n omega)).
  Proof.
    intros.
    assert (rv_eq (fun omega => LimSup_seq (fun n => f n omega))
                  (fun omega => Inf_seq (fun m : nat => 
                                           Sup_seq (fun n : nat => f (n + m)%nat omega)))) 
      by (intro x; now rewrite LimSup_InfSup_seq).
    apply (RbarMeasurable_proper _ _ H0).
    apply Rbar_inf_measurable.
    intros.
    now apply Rbar_sup_measurable.
  Qed.
  
  Instance Rbar_lim_inf_measurable (f : nat -> Ts -> R) :
    (forall n, RbarMeasurable (f n)) ->
    RbarMeasurable (fun omega => LimInf_seq (fun n => f n omega)).
  Proof.
    intros.
    assert (rv_eq (fun omega : Ts => LimInf_seq (fun n : nat => f n omega))
                  (fun omega =>
                     Sup_seq (fun m : nat => Inf_seq (fun n : nat => f (n + m)%nat omega))))
      by (intro x; now rewrite LimInf_SupInf_seq).
    apply (RbarMeasurable_proper _ _ H0).
    apply Rbar_sup_measurable.
    intros.
    now apply Rbar_inf_measurable.
  Qed.

  Instance Rbar_rvlim_measurable (f : nat -> Ts -> R) :
    (forall n, RealMeasurable dom (f n)) ->
    (forall (omega:Ts), ex_lim_seq (fun n => f n omega)) -> 
    RbarMeasurable (Rbar_rvlim f).
  Proof.
    intros.
    unfold Rbar_rvlim.
    assert (forall omega, Lim_seq (fun n => f n omega) = 
                          LimSup_seq (fun n => f n omega)).
    {
      intros.
      specialize (H0 omega).
      rewrite ex_lim_LimSup_LimInf_seq in H0.
      unfold Lim_seq.
      rewrite H0.
      now rewrite x_plus_x_div_2.
    }
    apply RbarMeasurable_proper with
        (x := fun omega => LimSup_seq (fun n => f n omega)).
    intro x; now rewrite H1.
    apply Rbar_lim_sup_measurable; trivial.
    intros.
    now apply RealMeasurable_RbarMeasurable.
  Qed.

  Global Instance Rbar_rvlim_rv (f: nat -> Ts -> R)
         {rv : forall n, RandomVariable dom borel_sa (f n)} :
    (forall (omega:Ts), ex_lim_seq (fun n => f n omega)) ->     
    RandomVariable dom Rbar_borel_sa (Rbar_rvlim f).
  Proof.
    intros.
    apply Rbar_measurable_rv.
    apply Rbar_rvlim_measurable; trivial.
    intros n.
    specialize (rv n).
    now apply rv_measurable.
  Qed.


  Instance Rbar_lim_inf_rv (f : nat -> Ts -> R) :
    (forall n, RandomVariable dom borel_sa (f n)) ->
    RandomVariable dom Rbar_borel_sa (fun omega => LimInf_seq (fun n => f n omega)).
  Proof.
    intros.
    apply Rbar_measurable_rv.
    apply Rbar_lim_inf_measurable.
    intros.
    apply rv_Rbar_measurable.
    now rewrite <- borel_Rbar_borel.
  Qed.

  Instance Rbar_real_measurable (f : Ts -> Rbar) :
    RbarMeasurable f ->
    RealMeasurable dom (fun x => real (f x)).
  Proof.
    unfold RbarMeasurable, RealMeasurable; intros.
    destruct (Rle_dec 0 r).
    - assert (pre_event_equiv
                (fun omega => real (f omega ) <= r)
                (pre_event_union
                   (pre_event_inter
                      (fun omega => is_finite (f omega))
                      (fun omega => Rbar_le (f omega) r))
                   (pre_event_union
                      (fun omega => f omega = p_infty)
                      (fun omega => f omega = m_infty)))).
      {
        intro x.
        unfold pre_event_inter, pre_event_union, is_finite.
        destruct (f x); simpl.
        - intuition congruence.
        - intuition congruence.
        - intuition congruence.
      }
      rewrite H0.
      apply sa_union.
      + apply sa_inter.
        * apply sa_finite_Rbar.
          now apply Rbar_measurable_rv.
        * apply H.
      + apply sa_union.
        * now apply Rbar_sa_le_pt.
        * now apply Rbar_sa_le_pt.
    - assert (r < 0) by lra.
      assert (pre_event_equiv
                (fun omega : Ts => f omega <= r)
                (pre_event_inter
                   (fun omega => is_finite (f omega))
                   (fun omega => Rbar_le (f omega) r))).
      {
        intro x.
        unfold pre_event_inter, is_finite.
        destruct (f x).
        - simpl.
          intuition discriminate.
        - simpl.
          intuition discriminate.
        - simpl.
          intuition discriminate.
      }
      rewrite H1.
      apply sa_inter.
      + apply sa_finite_Rbar.
        now apply Rbar_measurable_rv.
      + apply H.
  Qed.

  (*
  (* assume Rbar_plus is well defined everywhere *)
  Instance Rbar_plus_measurable (f g : Ts -> Rbar) :
    RbarMeasurable f -> RbarMeasurable g ->
    (forall x, ex_Rbar_plus (f x) (g x)) ->
    RbarMeasurable (Rbar_rvplus f g).
  Proof.
    intros.
    unfold RbarMeasurable.
    destruct r.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_plus (f omega) (g omega)) r)
                (pre_event_union
                   (fun omega => (Rbar_plus (f omega) (g omega)) = m_infty)
                   (pre_event_inter
                      (pre_event_inter
                         (fun omega => is_finite (f omega))
                         (fun omega => is_finite (g omega)))
                      (fun omega => (f omega) + (g omega) <= r)))).
      {
        intro x.
        unfold pre_event_union, pre_event_inter.
        specialize (H1 x).
        destruct (f x); destruct (g x); simpl; split; intros; try tauto.
        - right.
          unfold is_finite.
          tauto.
        - destruct H2.
          + discriminate.
          + now destruct H2 as [[? ?] ?].
        - destruct H2.
          + discriminate.
          + destruct H2 as [[? ?] ?].
            discriminate.
        - destruct H2.
          + discriminate.
          + destruct H2 as [[? ?] ?].
            discriminate.
        - destruct H2.
          + discriminate.
          + destruct H2 as [[? ?] ?].
            discriminate.
      }
      rewrite H2.
      apply sa_union.
      + assert (pre_event_equiv
                  (fun omega : Ts => Rbar_plus (f omega) (g omega) = m_infty)
                  (pre_event_union
                     (fun omega => f omega = m_infty)
                     (fun omega => g omega = m_infty))).
        {
          intro x.
          unfold pre_event_union.
          specialize (H1 x).
          destruct (f x); destruct (g x); simpl; split; intros; try tauto.
          - discriminate.
          - destruct H3; discriminate.
          - destruct H3; discriminate.
          - destruct H3; discriminate.
        }
        rewrite H3.
        apply sa_union.
        * now apply Rbar_sa_le_pt.
        * now apply Rbar_sa_le_pt.        
      + apply sa_inter.
        * apply sa_inter.
          -- apply sa_finite_Rbar.
             now apply Rbar_measurable_rv.
          -- apply sa_finite_Rbar.
             now apply Rbar_measurable_rv.
        * generalize (@plus_measurable Ts dom (fun omega => real (f omega)) (fun omega => real (g omega))); intros.
          apply Rbar_real_measurable in H.
          apply Rbar_real_measurable in H0.
          specialize (H3 H H0).
          apply H3.
    - assert (pre_event_equiv 
                (fun omega : Ts => Rbar_le (Rbar_plus (f omega) (g omega)) p_infty)
                (fun _ => True)).
      {
        intro x.
        unfold Rbar_le.
        match_destr; tauto.
      }
      rewrite H2.
      apply sa_all.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_plus (f omega) (g omega)) m_infty)
                (pre_event_union
                   (fun omega => (f omega) = m_infty)
                   (fun omega => (g omega) = m_infty))).
      { 
        intro x.
        unfold Rbar_le, pre_event_union.
        unfold ex_Rbar_plus in H1.
        unfold Rbar_plus.
        specialize (H1 x).
        match_case_in H1; intros.
        - match_destr.
          split; intros.
          + tauto.
          + destruct H3.
            * rewrite H3 in H2.
              simpl in H2.
              match_destr_in H2.
            * rewrite H3 in H2.
              unfold Rbar_plus' in H2.
              match_destr_in H2.
          + split; intros.
            * tauto.
            * destruct H3.
              -- rewrite H3 in H2.
                 simpl in H2.
                 match_destr_in H2.
              -- rewrite H3 in H2.
                 unfold Rbar_plus' in H2.
                 match_destr_in H2.
          + split; intros.
            * unfold Rbar_plus' in H2.
              repeat match_destr_in H2; tauto.
            * destruct H3.
              -- rewrite H3 in H2.
                 unfold Rbar_plus' in H2.
                 match_destr_in H2.
              -- rewrite H3 in H2.
                 unfold Rbar_plus' in H2.
                 match_destr_in H2.
        - split; intros.
          + tauto.
          + destruct H3.
            * now rewrite H2 in H1.
            * now rewrite H2 in H1.
      }
      rewrite H2.
      apply sa_union.
      + now apply Rbar_sa_le_pt.
      + now apply Rbar_sa_le_pt.
    Qed.
   *)

  Lemma Rbar_rvplus_minf (f g : Ts -> Rbar) :
    pre_event_equiv
      (fun omega : Ts => Rbar_plus (f omega) (g omega) = m_infty)
      (pre_event_union
         (pre_event_inter
            (fun omega => f omega = m_infty)
            (fun omega => g omega = m_infty))
         (pre_event_union
            (pre_event_inter
               (fun omega => f omega = m_infty)
               (fun omega => is_finite (g omega)))
            (pre_event_inter
               (fun omega => is_finite (f omega))
               (fun omega => g omega = m_infty) ))).
  Proof.
    intro x.
    unfold pre_event_union, pre_event_inter.
    destruct (f x); destruct (g x); simpl; split; intros; try tauto; try discriminate.
    - destruct H; destruct H.
      + discriminate.
      + destruct H; discriminate.
      + destruct H; discriminate.
    - destruct H; destruct H.
      + discriminate.
      + destruct H; discriminate.
      + destruct H; discriminate.
    - right; right; now split.
    - destruct H; destruct H.
      + discriminate.
      + destruct H; discriminate.
      + destruct H; discriminate.
    - destruct H; destruct H.
      + discriminate.
      + destruct H; discriminate.
      + destruct H; discriminate.
    - right; left; now split.
    - destruct H; destruct H.
      + discriminate.
      + destruct H; discriminate.
      + destruct H; discriminate.
  Qed.

  Instance Rbar_plus_measurable (f g : Ts -> Rbar) :
    RbarMeasurable f -> RbarMeasurable g ->
    RbarMeasurable (Rbar_rvplus f g).
  Proof.
    intros fmeas gmeas.
    assert (plusnoneequiv :
              (pre_event_equiv
                 (fun omega => Rbar_plus' (f omega) (g omega) = None)
                 (pre_event_union
                    (pre_event_inter
                       (fun omega => f omega = p_infty)
                       (fun omega => g omega = m_infty))
                    (pre_event_inter
                       (fun omega => f omega = m_infty)
                       (fun omega => g omega = p_infty))
           ))).
    {
      intro x.
      unfold Rbar_plus'.
      unfold pre_event_union, pre_event_inter.
      destruct (f x); destruct (g x); try intuition congruence.
    }
    assert (saplusnone :
              sa_sigma (fun omega => Rbar_plus' (f omega) (g omega) = None)).
    {
      rewrite plusnoneequiv.
      apply sa_union; apply sa_inter; now apply Rbar_sa_le_pt.
    }
    unfold RbarMeasurable; intros.
    
    destruct r.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_plus (f omega) (g omega)) r)
                (pre_event_union
                   (fun omega => (Rbar_plus (f omega) (g omega)) = m_infty)
                   (pre_event_union
                      (pre_event_inter
                         (fun omega => Rbar_plus' (f omega) (g omega) = None)
                         (fun omega => (f omega) + (g omega) <= r))
                      (pre_event_inter
                         (pre_event_inter
                            (fun omega => is_finite (f omega))
                            (fun omega => is_finite (g omega)))
                         (fun omega => (f omega) + (g omega) <= r))))).
      {
        intro x.
        unfold pre_event_union, pre_event_inter.
        destruct (f x); destruct (g x); simpl; split; intros; try intuition congruence.
        - right.
          unfold is_finite.
          tauto.
        - right; left.
          split; trivial; lra.
        - destruct H; try discriminate.
          destruct H; destruct H; try lra.
        - right; left.
          split; trivial; lra.          
        - destruct H; try discriminate.
          destruct H; destruct H; try lra.
      }
      rewrite H.
      apply sa_union.
      + rewrite  Rbar_rvplus_minf.
        apply sa_union.
        * apply sa_inter; now apply Rbar_sa_le_pt.
        * apply sa_union.
          -- apply sa_inter.
             ++ now apply Rbar_sa_le_pt.
             ++ apply sa_finite_Rbar.
                now apply Rbar_measurable_rv.
          -- apply sa_inter.
             ++ apply sa_finite_Rbar.
                now apply Rbar_measurable_rv.
             ++ now apply Rbar_sa_le_pt.
      + apply sa_union.
        * apply sa_inter; trivial.
          generalize (@plus_measurable Ts dom (fun omega => real (f omega)) (fun omega => real (g omega))); intros.
          apply Rbar_real_measurable in fmeas.
          apply Rbar_real_measurable in gmeas.
          specialize (H0 fmeas gmeas).
          apply H0.
        * apply sa_inter.
          -- apply sa_inter; apply sa_finite_Rbar; now apply Rbar_measurable_rv.
          -- generalize (@plus_measurable Ts dom (fun omega => real (f omega)) (fun omega => real (g omega))); intros.
             apply Rbar_real_measurable in fmeas.
             apply Rbar_real_measurable in gmeas.
             specialize (H0 fmeas gmeas).
             apply H0.
    - assert (pre_event_equiv 
                (fun omega : Ts => Rbar_le (Rbar_plus (f omega) (g omega)) p_infty)
                (fun _ => True)).
      {
        intro x.
        unfold Rbar_le.
        match_destr; tauto.
      }
      rewrite H.
      apply sa_all.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_plus (f omega) (g omega)) m_infty)
                (fun omega : Ts => Rbar_plus (f omega) (g omega) = m_infty)).
      {
        intro x.
        now destruct (Rbar_plus (f x) (g x)).
      }
      rewrite H.
      rewrite  Rbar_rvplus_minf.
      apply sa_union.
      + apply sa_inter; now apply Rbar_sa_le_pt.
      + apply sa_union.
        * apply sa_inter.
          -- now apply Rbar_sa_le_pt.
          -- apply sa_finite_Rbar; now apply Rbar_measurable_rv.
        * apply sa_inter.
          -- apply sa_finite_Rbar; now apply Rbar_measurable_rv.
          -- now apply Rbar_sa_le_pt.
  Qed.

  Instance Rbar_lim_seq_measurable_pos (f : nat -> Ts -> R) :
    (forall n, RbarMeasurable (f n)) ->
    (forall n, Rbar_NonnegativeFunction (f n)) ->
    RbarMeasurable (fun omega => Lim_seq (fun n => f n omega)).
  Proof.
    intros.
    unfold Lim_seq.
    apply Rbar_div_pos_measurable.
    apply Rbar_plus_measurable.
    - now apply Rbar_lim_sup_measurable.
    - now apply Rbar_lim_inf_measurable.
  Qed.

  Definition Rbar_rvabs  (rv_X : Ts -> Rbar) := fun omega => Rbar_abs (rv_X omega).

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


  Global Instance power_abs_pos (rv_X : Ts -> Rbar) (p:R) :
    Rbar_NonnegativeFunction
      (fun omega => Rbar_power (Rbar_abs (rv_X omega)) p ).
  Proof.
    intros x.
    apply Rbar_power_nonneg.
  Qed.

  Definition Rbar_rvpower (rv_X1 : Ts -> Rbar) (n : R) := 
    fun omega => Rbar_power (rv_X1 omega) n.

  Instance Rbar_power_measurable (f : Ts -> Rbar) (n : R) :
    RbarMeasurable f ->
    RbarMeasurable (Rbar_rvpower f n).
  Proof.
    intros.
    unfold Rbar_rvpower, RbarMeasurable.
    destruct r.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_power (f omega) n) r)
                (pre_event_union
                   (pre_event_inter
                      (fun omega => is_finite (f omega))
                      (fun omega => power (f omega) n <= r))
                   (pre_event_union
                      (pre_event_inter
                         (fun omega => f omega = p_infty)
                         (fun omega => False))
                      (pre_event_inter
                         (fun omega => f omega = m_infty)
                         (fun omega => 0 <= r))))).
      {
        intro x.
        unfold pre_event_union, pre_event_inter, is_finite.
        destruct (f x); simpl; intuition discriminate.
      }
      rewrite H0.
      apply sa_union.
      + apply sa_inter.
        * apply sa_finite_Rbar.
          now apply Rbar_measurable_rv.
        * apply rvpower_measurable.
          -- now apply Rbar_real_measurable.
          -- now apply constant_measurable.
      + apply sa_union.
        * apply sa_inter.
          -- apply Rbar_sa_le_pt.
             apply H.
          -- apply sa_none.
        * apply sa_inter.
          -- apply Rbar_sa_le_pt.
             apply H.
          -- apply constant_measurable.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_power (f omega) n) p_infty)
                (fun omega => True)).
      {
        intro x.
        unfold Rbar_le.
        now match_destr.
      }
      rewrite H0.
      apply sa_all.
    - assert (pre_event_equiv
                (fun omega : Ts => Rbar_le (Rbar_power (f omega) n) m_infty)
                (fun omega => False)).
      {
        intro x.
        unfold Rbar_power.
        match_destr; now simpl.
      }
      rewrite H0.
      apply sa_none.
  Qed.
  
  (*
  Lemma Rbar_rvmult_unfold (f g:Ts->Rbar) :
    (forall omega, ex_Rbar_mult (f omega) (g omega)) ->
    rv_eq (Rbar_rvmult f g) (fun omega => Rbar_div_pos (Rbar_rvminus (Rbar_rvsqr (Rbar_rvplus f g))
                                            (Rbar_rvsqr (Rbar_rvminus f g)) omega) (mkposreal 4 ltac:(lra))).
    Proof.
      intros mex omega.
      specialize (mex omega).
      unfold Rbar_rvmult, Rbar_rvminus, Rbar_rvplus, Rbar_rvsqr, Rbar_rvopp, Rbar_div_pos; simpl.
      destruct (f omega); destruct (g omega); simpl.
      - f_equal.
        unfold Rsqr.
        lra. 
      - destruct (Rle_dec 0 r).
        + destruct (Rle_lt_or_eq_dec 0 r r0); trivial.
          simpl in mex.
          lra.
        + 
        Show 2.
    Qed.
   *)
  Global Instance Rbar_rvmult_meas (x y : Ts -> Rbar)
         {xrv:RbarMeasurable x} 
         {yrv:RbarMeasurable y} :
    RbarMeasurable (Rbar_rvmult x y).
  Proof.
    intros r.

    pose (efin := pre_list_inter [(fun omega => is_finite (x omega))
                                  ; (fun omega => is_finite (y omega))
                                  ; fun omega => Rbar_le (rvmult (Rbar_finite_part x) (Rbar_finite_part y) omega) r]).
    pose (e0 := pre_event_inter (pre_event_union (fun omega => (x omega) = 0) (fun omega => (y omega) = 0)) ((fun omega => Rbar_le 0 r))).
    pose (epinf := pre_event_inter (
                       pre_list_union [
                           (pre_event_inter (fun omega => x omega = p_infty)  (fun omega => Rbar_gt (y omega) 0))
                           ; (pre_event_inter (fun omega => y omega = p_infty) (fun omega => Rbar_gt (x omega) 0))
                           ; (pre_event_inter (fun omega => x omega = m_infty)  (fun omega => Rbar_lt (y omega) 0))
                           ; (pre_event_inter (fun omega => y omega = m_infty)  (fun omega => Rbar_lt (x omega) 0))])
                                   (fun omega => Rbar_le p_infty r)).

    pose (eminf := 
            pre_list_union [
                (pre_event_inter (fun omega => x omega = m_infty) (fun omega => Rbar_gt (y omega) 0))
                ; (pre_event_inter (fun omega => y omega = m_infty) (fun omega => Rbar_gt (x omega) 0))
                ; (pre_event_inter (fun omega => x omega = p_infty) (fun omega => Rbar_lt (y omega) 0))
                ; (pre_event_inter (fun omega => y omega = p_infty) (fun omega => Rbar_lt (x omega) 0))])
    .
    
    assert (eqq:pre_event_equiv (fun omega : Ts => Rbar_le (Rbar_rvmult x y omega) r)
                                (pre_list_union [efin; e0; epinf; eminf])).
    {
      intro z.
      unfold pre_list_union, Rbar_rvmult.
      split; intros.
      - case_eq (x z); case_eq (y z); intros.
        exists efin.
        + split; [apply in_eq | ].
          subst efin.
          unfold pre_list_inter; intros.
          destruct H2.
          * rewrite <- H2.
            unfold is_finite; rewrite H1; now simpl.
          * destruct H2.
            -- rewrite <- H2.
               unfold is_finite; rewrite H0; now simpl.
            -- destruct H2.
               ++ rewrite <- H2.
                  rewrite H0, H1 in H.
                  unfold rvmult, Rbar_finite_part.
                  rewrite H0, H1.
                  apply H.
               ++ now apply in_nil in H2.
        + destruct (Req_EM_T r0 0).
          * exists e0.
            split; [apply in_cons, in_eq |].
            subst e0.
            split.
            -- unfold pre_event_union.
               rewrite e in H1; tauto.
            -- subst.
               rewrite H0, H1 in H.
               now rewrite Rbar_mult_0_l in H.
          * destruct (Rlt_dec 0 r0).
            -- exists epinf.
               split; [apply in_cons, in_cons, in_eq |].
               subst epinf.
               unfold pre_list_union, pre_event_inter.
               split.
               ++ exists (fun x0 : Ts => y x0 = p_infty /\ Rbar_gt (x x0) 0).
                  split; [apply in_cons, in_eq |].
                  ** split; trivial.
                     rewrite H1.
                     now simpl.
               ++ rewrite H0, H1 in H.
                  rewrite Rbar_mult_comm in H.
                  now rewrite Rbar_mult_p_infty_pos in H by trivial.
            -- exists eminf.
               split; [apply in_cons, in_cons, in_cons, in_eq |].
               subst eminf.
               unfold pre_list_union, pre_event_inter.
               ++ exists (fun x0 : Ts => y x0 = p_infty /\ Rbar_lt (x x0) 0).
                  split; [apply in_cons, in_cons, in_cons, in_eq |].
                  split; trivial.
                  rewrite H1; simpl; lra.
        + destruct (Req_EM_T r0 0).
          * exists e0.
            split; [apply in_cons, in_eq |].
            subst e0.
            unfold pre_event_union.
            split.
            -- rewrite e in H1; tauto.
            -- subst.
               rewrite H0, H1 in H.
               now rewrite Rbar_mult_0_l in H.              
          * destruct (Rlt_dec 0 r0).
            -- exists eminf.
               split; [apply in_cons, in_cons, in_cons, in_eq |].
               subst eminf.
               unfold pre_list_union, pre_event_inter.
               exists (fun x0 : Ts => y x0 = m_infty /\ Rbar_gt (x x0) 0).
               split; [apply in_cons, in_eq |].
               ++ split; trivial.
                  rewrite H1.
                  now simpl.
            -- exists epinf.
               split; [apply in_cons, in_cons, in_eq |].
               subst epinf.
               unfold pre_list_union, pre_event_inter.
               split.
               ++ exists (fun x0 : Ts => y x0 = m_infty /\ Rbar_lt (x x0) 0).
                  split; [apply in_cons, in_cons, in_cons, in_eq |].
                  split; trivial.
                  rewrite H1; simpl; lra.
               ++ rewrite H0, H1 in H.
                  rewrite Rbar_mult_comm in H.
                  now rewrite Rbar_mult_m_infty_neg in H by lra.
        + destruct (Req_EM_T r0 0).
          * exists e0.
            split; [apply in_cons, in_eq |].
            subst e0.
            unfold pre_event_union.
            split.
            -- rewrite e in H0; tauto.
            -- subst.
               rewrite H0, H1 in H.
               now rewrite Rbar_mult_0_r in H.
          * destruct (Rlt_dec 0 r0).
            -- exists epinf.
               split; [apply in_cons, in_cons, in_eq |].
               subst epinf.
               unfold pre_list_union, pre_event_inter.
               split.
               ++ exists (fun x0 : Ts => x x0 = p_infty /\ Rbar_gt (y x0) 0).
                  split; [apply in_eq |].
                  split; trivial.
                  rewrite H0.
                  now simpl.
               ++ rewrite H0, H1 in H.
                  now rewrite Rbar_mult_p_infty_pos in H by trivial.
            -- exists eminf.
               split; [apply in_cons, in_cons, in_cons, in_eq |].
               subst eminf.
               unfold pre_list_union, pre_event_inter.
               exists (fun x0 : Ts => x x0 = p_infty /\ Rbar_lt (y x0) 0).
               split; [apply in_cons, in_cons, in_eq | ].
               split; trivial.
               rewrite H0; simpl; lra.       
        + exists epinf.
          split; [apply in_cons, in_cons, in_eq |].
          subst epinf.
          unfold pre_list_union, pre_event_inter.
          split.
          ++ exists (fun x0 : Ts => x x0 = p_infty /\ Rbar_gt (y x0) 0).
             split; [apply in_eq |].
             split; trivial.
             rewrite H0.
             now simpl.
          ++ rewrite H0, H1 in H.
             apply H.
        + exists eminf.
          split; [apply in_cons, in_cons, in_cons, in_eq |].
          subst eminf.
          unfold pre_list_union, pre_event_inter.
          exists (fun x0 : Ts => x x0 = p_infty /\ Rbar_lt (y x0) 0).
          split; [apply in_cons, in_cons, in_eq |].
          ++ split; trivial.
             rewrite H0.
             now simpl.
        + destruct (Req_EM_T r0 0).
          * exists e0.
            split; [apply in_cons, in_eq |].
            subst e0.
            unfold pre_event_union.
            split.
            -- rewrite e in H0; tauto.
            -- subst.
               rewrite H0, H1 in H.
               now rewrite Rbar_mult_0_r in H.
          * destruct (Rlt_dec 0 r0).
            -- exists eminf.
               split; [apply in_cons, in_cons, in_cons, in_eq |].
               subst eminf.
               unfold pre_list_union, pre_event_inter.
               exists (fun x0 : Ts => x x0 = m_infty /\ Rbar_gt (y x0) 0).
               split; [apply in_eq |].
               ++ split; trivial.
                  rewrite H0.
                  now simpl.
            -- exists epinf.
               split; [apply in_cons, in_cons, in_eq |].
               subst epinf.
               unfold pre_list_union, pre_event_inter.
               split.
               ++ exists (fun x0 : Ts => x x0 = m_infty /\ Rbar_lt (y x0) 0).
                  split; [apply in_cons, in_cons, in_eq | ].
                  split; trivial.
                  rewrite H0; simpl; lra.
               ++ rewrite H0, H1 in H.
                  now rewrite Rbar_mult_m_infty_neg in H by lra.
        + exists eminf.
          split; [apply in_cons, in_cons, in_cons, in_eq |].
          subst eminf.
          unfold pre_list_union, pre_event_inter.
          exists (fun x0 : Ts => x x0 = m_infty /\ Rbar_gt (y x0) 0).
          split; [apply in_eq |].
          ++ split; trivial.
             rewrite H0.
             now simpl.
        + exists epinf.
          split; [apply in_cons, in_cons, in_eq |].
          subst epinf.
          unfold pre_list_union, pre_event_inter.
          split.
          ++ exists (fun x0 : Ts => x x0 = m_infty /\ Rbar_lt (y x0) 0).
             split; [apply in_cons, in_cons, in_eq |].
             split; trivial.
             rewrite H0.
             now simpl.
          ++ rewrite H0, H1 in H.
             apply H.
      - destruct H as [a [inn az]].
        unfold efin, e0, epinf, eminf in inn.
        simpl in inn.
        destruct inn as [?|[?|[?|[?|?]]]]; subst.
        + unfold pre_list_inter in az; simpl in az.
          generalize (az (fun omega : Ts => is_finite (x omega)))
          ; intros HH1.
          cut_to HH1; [| tauto].
          generalize (az (fun omega : Ts => is_finite (y omega)))
          ; intros HH2.
          cut_to HH2; [| tauto].
          rewrite <- HH1, <- HH2; simpl.
          generalize (az (fun omega : Ts =>
                            match r with
                            | Finite y0 => rvmult (Rbar_finite_part x) (Rbar_finite_part y) omega <= y0
                            | p_infty => True
                            | m_infty => False
                            end)); intros HH3.
          cut_to HH3; [| tauto].
          apply HH3.
        + destruct az.
          destruct H
          ; rewrite H.
          * now rewrite Rbar_mult_0_l.
          * now rewrite Rbar_mult_0_r.
        + destruct az as [[?[??]]?].
          simpl in H.
          repeat destruct H.
          * destruct H0.
            rewrite H; simpl.
            match_destr_in H0.
            -- now rewrite Rbar_mult_p_infty_pos by trivial.
            -- now simpl.
          * destruct H0.
            rewrite H.
            match_destr_in H0; try tauto.
            rewrite Rbar_mult_comm.
            rewrite Rbar_mult_p_infty_pos; trivial.
          * destruct r; try tauto.
            unfold Rbar_le.
            match_destr.
          * destruct r; try tauto.
            unfold Rbar_le.
            match_destr.
        + destruct az as [?[??]].
          simpl in H.
          (repeat destruct H)
          ; try solve [destruct H0
                       ; rewrite H; simpl
                       ; match_destr_in H0
                       ; [unfold Rbar_mult, Rbar_mult'
                          ; destruct (Rle_dec 0 r0); try lra
                          ; destruct (Rle_lt_or_eq_dec 0 r0 r1); try lra
                          ; now simpl
                         | tauto]].
          * destruct H0.
            rewrite H; simpl.
            unfold Rbar_lt in H0.
            match_destr_in H0.
            -- unfold Rbar_mult, Rbar_mult'.
               destruct (Rle_dec 0 r0); try lra.
               destruct (Rle_lt_or_eq_dec 0 r0 r1); try lra.
               now simpl.
            -- tauto.
          * destruct H0.
            rewrite H; simpl.
            unfold Rbar_lt in H0.
            match_destr_in H0.
            -- unfold Rbar_mult, Rbar_mult'.
               destruct (Rle_dec 0 r0); try lra.
               destruct (Rle_lt_or_eq_dec 0 r0 r1); try lra.
               now simpl.
            -- tauto.
        + tauto.
    }
    rewrite eqq.
    apply sa_pre_list_union; intros ?.
    simpl.
    intros [?|[?|[?|[?|?]]]]; subst.
    - unfold efin.
      apply sa_pre_list_inter; intros ?.
      intros [?|[?|[?|?]]]; subst.
      + apply sa_finite_Rbar.
        now apply Rbar_measurable_rv.
      + apply sa_finite_Rbar.
        now apply Rbar_measurable_rv.
      + assert (RbarMeasurable (fun omega => (rvmult (Rbar_finite_part x) (Rbar_finite_part y) omega))).
        {
          apply RealMeasurable_RbarMeasurable.
          apply mult_measurable.
          - apply Rbar_finite_part_meas.
            now apply Rbar_measurable_rv.
          - apply Rbar_finite_part_meas.
            now apply Rbar_measurable_rv.
        }
        apply H.
      + tauto.
    - unfold e0.
      apply sa_inter.
      + apply sa_union.
        * now apply Rbar_sa_le_pt.
        * now apply Rbar_sa_le_pt.
      + apply RealMeasurable_RbarMeasurable.
        apply constant_measurable.
    - unfold epinf.
      apply sa_inter.
      + apply sa_pre_list_union; intros ?.
        intros [?|[?|[?|[?|?]]]]; subst
        ; (try tauto; try apply sa_inter
           ; try apply sa_pre_event_union
           ; try now apply Rbar_sa_le_pt).
        * now apply Rbar_sa_le_gt.
        * now apply Rbar_sa_le_gt.
        * now apply Rbar_sa_le_lt.
        * now apply Rbar_sa_le_lt.
      + destruct (Rbar_le_dec p_infty r).
        * eapply sa_proper; try eapply sa_all.
          red; unfold pre_Ω; tauto.
        * eapply sa_proper; try eapply sa_none.
          red; unfold pre_event_none; tauto.
    - unfold eminf.
      apply sa_pre_list_union; intros ?.
      intros [?|[?|[?|[?|?]]]]; subst
      ; (try tauto; try apply sa_inter
         ; try apply sa_pre_event_union
         ; try now apply Rbar_sa_le_pt).
      * now apply Rbar_sa_le_gt.
      * now apply Rbar_sa_le_gt.
      * now apply Rbar_sa_le_lt.
      * now apply Rbar_sa_le_lt.
    - tauto.
  Qed.
  
  Global Instance Rbar_rvmult_rv (x y : Ts -> Rbar)
         {xrv:RandomVariable dom Rbar_borel_sa x} 
         {yrv:RandomVariable dom Rbar_borel_sa y} :
    RandomVariable dom Rbar_borel_sa (Rbar_rvmult x y).
  Proof.
    intros.
    apply Rbar_measurable_rv.
    now apply Rbar_rvmult_meas; apply rv_Rbar_measurable.
  Qed.

  Global Instance Rbar_rvmult_nnf (x y : Ts -> Rbar)
         {xnnf:Rbar_NonnegativeFunction x}
         {ynnf:Rbar_NonnegativeFunction y} :
    Rbar_NonnegativeFunction (Rbar_rvmult x y).
  Proof.
    intros omega; simpl.
    specialize (xnnf omega).
    specialize (ynnf omega).
    unfold Rbar_rvmult.
    destruct x; simpl in *; try tauto
    ; destruct y; simpl in *; try tauto.
    - now apply Rmult_le_pos.
    - destruct (Rle_dec 0 r); try tauto.
      destruct (Rle_lt_or_eq_dec 0 r r0); lra.
    - destruct (Rle_dec 0 r); try tauto.
      destruct (Rle_lt_or_eq_dec 0 r r0); lra.
  Qed.

End RbarRandomVariables.  

Section rv_almost.

  Lemma almost_map_R_split
        {Ts:Type}
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        {f:Ts->R} {P:R->Prop} :
    almost prts (fun x => P (f x)) ->
    exists f', almostR2 prts eq f f' /\
          (forall x, P (f' x)) /\
          (RandomVariable dom borel_sa f -> RandomVariable dom borel_sa f').
  Proof.
    intros aP.
    destruct (almost_witness _ aP) as [x Px].
    destruct aP as [p [pone ph]].
    exists (rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec p))) x) 0 then false else true)

                f
                (const (f x))
      ).
    repeat split.
    - exists p.
      split; trivial.
      intros.
      rv_unfold.
      destruct (classic_dec p x0); try tauto.
      destruct (Req_EM_T 1 0); try lra; tauto.
    - intros.
      rv_unfold.
      destruct (classic_dec p x0); try tauto.
      + destruct (Req_EM_T 1 0); try lra; auto.
      + destruct (Req_EM_T 0 0); try lra; auto.
    - intros.
      apply measurable_rv.
      eapply rvchoice_rv; trivial.
      + apply EventIndicator_rv.
      + typeclasses eauto.
  Qed.

  Lemma almost_map_Rbar_split
        {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        {f:Ts->Rbar} {P:Rbar->Prop} :
    almost prts (fun x => P (f x)) ->
    exists f', almostR2 prts eq f f' /\
          (forall x, P (f' x)) /\
          (RandomVariable dom Rbar_borel_sa f -> RandomVariable dom Rbar_borel_sa f').
  Proof.
    intros aP.
    destruct (almost_witness _ aP) as [x Px].
    destruct aP as [p [pone ph]].
    exists (Rbar_rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec p))) x) 0 then false else true)

                     f
                     (const (f x))
      ).
    repeat split.
    - exists p.
      split; trivial.
      intros.
      rv_unfold; unfold Rbar_rvchoice.
      destruct (classic_dec p x0); try tauto.
      destruct (Req_EM_T 1 0); try lra; try tauto.
    - intros.
      rv_unfold; unfold Rbar_rvchoice.
      destruct (classic_dec p x0); try tauto.
      + destruct (Req_EM_T 1 0); try lra; auto.
      + destruct (Req_EM_T 0 0); try lra; auto.
    - intros.
      apply Rbar_measurable_rv.
      eapply Rbar_rvchoice_rv; trivial.
      + apply EventIndicator_rv.
      + typeclasses eauto.

  Qed.

  Open Scope prob.
  Global Instance almostR2_eq_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvplus.
  Proof.
    intros ??????.
    eapply almost_impl; [| eapply almost_and; [exact H | exact H0]].
    apply all_almost; intros ? [??].
    unfold rvplus; congruence.
  Qed.

  Global Instance almostR2_eq_scale_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (eq ==> almostR2 prts eq ==> almostR2 prts eq) rvscale.
  Proof.
    unfold almostR2 in *.
    intros ? c ? x1 x2 [Px [Pxall eq_onx]]; subst.
    exists Px.
    split; trivial.
    intros.
    unfold rvscale.
    now rewrite eq_onx.
  Qed.

  Global Instance almostR2_eq_opp_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq) rvopp.
  Proof.
    now apply almostR2_eq_scale_proper.
  Qed.

  Global Instance almostR2_eq_minus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvminus.
  Proof.
    intros ??????.
    unfold rvminus.
    now rewrite H, H0.
  Qed.  

  Lemma almostR2_eq_plus_inv {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         {x y z} :
    almostR2 prts eq z (rvplus x y) ->
    exists x' y',
      almostR2 prts eq x x' /\
      almostR2 prts eq y y' /\ 
      rv_eq z (rvplus x' y').
  Proof.
    intros [p [pone px]].
    exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then x a else 0).
    exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then y a else z a).
    split; [| split].
    - exists p.
      split; trivial.
      intros ??.
      match_destr.
      tauto.
    - exists p.
      split; trivial.
      intros ??.
      match_destr.
      tauto.
    - intros a; simpl.
      rv_unfold.
      match_destr.
      + auto.
      + lra.
  Qed.

  Lemma almostR2_eq_opp_inv{Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         {x z} :
    almostR2 prts eq z (rvopp x) ->
    exists x',
      almostR2 prts eq x x' /\
      rv_eq z (rvopp x').
  Proof.
    intros [p [pone px]].

    exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then x a else - z a).
    split.
    - exists p.
      split; trivial.
      intros ??.
      match_destr.
      tauto.
    - intros ?.
      rv_unfold.
      match_destr.
      + auto.
      + lra.
  Qed.

  Global Instance almostR2_le_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts Rle ==> almostR2 prts Rle ==> almostR2 prts Rle) rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvplus.
      apply Rplus_le_compat; auto.
  Qed.

  Global Instance almostR2_le_lt_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts Rle ==> almostR2 prts Rlt ==> almostR2 prts Rlt) rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvplus.
      apply Rplus_le_lt_compat; auto.
  Qed.

  Global Instance almostR2_lt_le_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts Rlt ==> almostR2 prts Rle ==> almostR2 prts Rlt) rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvplus.
      apply Rplus_lt_le_compat; auto.
  Qed.

  Global Instance almostR2_eq_mult_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvmult.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvmult.
      now rewrite eq_onx, eq_ony.
  Qed.

  Global Instance almostR2_eq_Rbar_mult_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) Rbar_rvmult.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold Rbar_rvmult.
      now rewrite eq_onx, eq_ony.
  Qed.

  Global Instance almostR2_sub
         {Ts Td:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         (R:Td->Td->Prop)
         (f:(Ts->Td)->Ts->Td)
         (fpres: forall x y a, R (x a) (y a) -> R (f x a) (f y a))
    : Proper (almostR2 prts R ==> almostR2 prts R) f.
  Proof.
    intros x1 x2 [Px [Pxall eq_onx]].
    exists Px.
    split; trivial.
    intros; auto.
  Qed.

  Lemma almostR2_eq_pow_abs_proper
        {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom) 
        (x1 x2: Ts -> R)
        n
        (eqqx : almostR2 prts eq (rvabs x1) (rvabs x2)) :
    almostR2 prts eq (rvpow (rvabs x1) n) (rvpow (rvabs x2) n).
  Proof.
    apply (almostR2_sub prts eq (fun x => rvpow x n)); trivial.
    intros.
    now unfold rvpow; rewrite H.
  Qed.

  Global Instance almostR2_eq_power_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) :
    Proper (almostR2 prts eq ==> eq ==> almostR2 prts eq) rvpower.
  Proof.
    intros x1 x2 eqq1 ? n ?; subst.
    apply (almostR2_sub prts eq (fun x => rvpower x n)); trivial.
    intros.
    unfold rvpower, RealAdd.power.
    now rewrite H.
  Qed.

  Global Instance almostR2_eq_abs_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : 
    Proper (almostR2 prts eq ==> almostR2 prts eq) rvabs.
  Proof.
    eapply almostR2_sub; eauto; try typeclasses eauto.
    intros.
    unfold rvabs.
    now rewrite H.
  Qed.

  Global Instance almostR2_eq_subr {Ts Td:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) :
    subrelation (@rv_eq Ts Td) (almostR2 prts eq).
  Proof.
    intros ???.
    exists Ω.
    split; auto with prob.
  Qed.

  Global Instance almostR2_le_subr {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) :
    subrelation (@rv_le Ts) (almostR2 prts Rle).
  Proof.
    intros ???.
    exists Ω.
    split; auto with prob.
  Qed.

  Global Instance rv_le_sub_eq {Ts:Type}: subrelation (@rv_eq Ts R) rv_le.
  Proof.
    unfold rv_eq, rv_le.
    intros ????.
    rewrite H.
    lra.
  Qed.

  Lemma almostR2_le_split {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         x y :
    almostR2 prts Rle x y ->
    exists x', almostR2 prts eq x x' /\
          rv_le x' y.
  Proof.
    intros [p [pone ph]].
    generalize (fun ts => sa_dec p ts).
    exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then x ts else y ts).
    split.
    - exists p.
      split; trivial; intros.
      now match_destr.
    - intros ?.
      match_destr.
      + auto.
      + reflexivity.
  Qed.

  Lemma almostR2_le_split_r {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         x y :
    almostR2 prts Rle x y ->
    exists y', almostR2 prts eq y y' /\
          rv_le x y'.
  Proof.
    intros [p [pone ph]].
    generalize (fun ts => sa_dec p ts).
    exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then y ts else x ts).
    split.
    - exists p.
      split; trivial; intros.
      now match_destr.
    - intros ?.
      match_destr.
      + auto.
      + reflexivity.
  Qed.

  Local Existing Instance Rbar_le_pre.
  
  Lemma almostR2_Rbar_le_split {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         x y :
    almostR2 prts Rbar_le x y ->
    exists x', almostR2 prts eq x x' /\
          Rbar_rv_le x' y.
  Proof.
    intros [p [pone ph]].
    generalize (fun ts => sa_dec p ts).
    exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then x ts else y ts).
    split.
    - exists p.
      split; trivial; intros.
      now match_destr.
    - intros ?.
      match_destr.
      + auto.
      + reflexivity.
  Qed.

  Lemma almostR2_Rbar_le_split_r {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         x y :
    almostR2 prts Rbar_le x y ->
    exists y', almostR2 prts eq y y' /\
          Rbar_rv_le x y'.
  Proof.
    intros [p [pone ph]].
    generalize (fun ts => sa_dec p ts).
    exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then y ts else x ts).
    split.
    - exists p.
      split; trivial; intros.
      now match_destr.
    - intros ?.
      match_destr.
      + auto.
      + reflexivity.
  Qed.

End rv_almost.

Section EventRestricted.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}.

  Global Instance Restricted_NonnegativeFunction
         (e:event dom) (f : Ts -> R)
         (nnf: NonnegativeFunction f) :
    NonnegativeFunction (event_restricted_function e f).
  Proof.
    unfold NonnegativeFunction in *.
    intros.
    apply nnf.
  Qed.

  Global Instance Restricted_Rbar_NonnegativeFunction P (f : Ts -> Rbar)
         (nnf : Rbar_NonnegativeFunction f) :
    Rbar_NonnegativeFunction (event_restricted_function P f).
  Proof.
    unfold Rbar_NonnegativeFunction in *.
    intros.
    unfold event_restricted_function.
    unfold event_restricted_domain in x.
    destruct x.
    now unfold proj1_sig.
  Qed.

  Global Instance event_restricted_rv_le P : Proper (rv_le ==> rv_le) (event_restricted_function P).
  Proof.
    intros f g rel x.
    unfold event_restricted_function.
    unfold event_restricted_domain in x.
    destruct x.
    unfold proj1_sig.
    apply rel.
  Qed.

  Global Instance event_restricted_Rbar_rv_le P : Proper (Rbar_rv_le ==> Rbar_rv_le) (event_restricted_function P).
  Proof.
    intros f g rel x.
    unfold event_restricted_function.
    unfold event_restricted_domain in x.
    destruct x.
    unfold proj1_sig.
    apply rel.
  Qed.



  Global Instance lift_event_restricted_domain_fun_nnf {P} (f:event_restricted_domain P -> R) :
    NonnegativeFunction f -> 
    NonnegativeFunction (lift_event_restricted_domain_fun 0 f).
  Proof.
    unfold NonnegativeFunction, lift_event_restricted_domain_fun.
    intros nnf x.
    match_destr.
    lra.
  Qed.

  Global Instance lift_event_restricted_domain_fun_Rbar_nnf {P} (f:event_restricted_domain P -> Rbar) :
    Rbar_NonnegativeFunction f -> 
    Rbar_NonnegativeFunction (lift_event_restricted_domain_fun (Finite 0) f).
  Proof.
    unfold Rbar_NonnegativeFunction, lift_event_restricted_domain_fun.
    intros nnf x.
    match_destr.
    simpl; lra.
  Qed.

  Lemma restrict_lift {P} (f:event_restricted_domain P -> R) :
    rv_eq (event_restricted_function P (lift_event_restricted_domain_fun 0 f)) f.
  Proof.
    intro x.
    destruct x.
    unfold event_restricted_function, lift_event_restricted_domain_fun.
    match_destr; try easy.
    do 2 f_equal.
    apply proof_irrelevance.
  Qed.


  Lemma restrict_lift_Rbar {P} (f:event_restricted_domain P -> Rbar) :
    rv_eq (event_restricted_function P (lift_event_restricted_domain_fun (Finite 0) f)) f.
  Proof.
    intro x.
    destruct x.
    unfold event_restricted_function, lift_event_restricted_domain_fun.
    match_destr; try easy.
    do 2 f_equal.
    apply proof_irrelevance.
  Qed.

End EventRestricted.

(*
Section prob.
  Local Open Scope R.
  Local Open Scope prob.

  Context {Ts:Type} {Td:Type}
          {dom: SigmaAlgebra Ts}
          {prts: ProbSpace dom}
          {cod: SigmaAlgebra Td}
          {rv_X: Ts -> Td}.

  Definition Pr 
             (S:Td->Prop)
    := ps_P (fun x:Ts => S (rv_X x)).

  Definition independent (A B:Td->Prop) :=
    Pr (A ∩ B) = (Pr A * Pr B).

  Notation "a ⊥ b" := (independent a b) (at level 50) : prob. (* \perp *)

  Lemma pr_all : Pr Ω = R1.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_proper _ Ω) by firstorder. 
    apply ps_all.
  Qed.
  
  Lemma pr_none : Pr ∅ = R0.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_proper _ ∅) by firstorder.
    apply ps_none.
  Qed.


End prob.


Section lebesgueintegration.
  

  Class MeasurableFunction {Ts: Type} (dom: SigmaAlgebra Ts) :=
    {
    measure_mu: event Ts -> R;

    measure_none : measure_mu event_none = R0 ;
    measure_ge_zero: forall A : event Ts, sa_sigma A -> 0 <= measure_mu A;
    
    measure_coutably_additive: forall collection: nat -> event Ts,
        (forall n : nat, sa_sigma (collection n)) ->
        collection_is_pairwise_disjoint collection ->
        sum_of_probs_equals measure_mu collection (measure_mu (union_of_collection collection))

    }.


  (* See https://en.wikipedia.org/wiki/Lebesgue_integration#Towards_a_formal_definition *)
  Definition F_star {dom:SigmaAlgebra R} (measure: MeasurableFunction dom) (f: R -> R) (t: R) :=
    measure_mu (fun (x: R) => (f x) > t).

  (* The integral $\int f d\mu defined in terms of the Riemann integral.
   * note that this definition assumes that f : R -> R+
   * Again, see https://en.wikipedia.org/wiki/Lebesgue_integration#Towards_a_formal_definition *)
  Definition Lebesgue_integrable_pos {dom: SigmaAlgebra R}
             (f : R -> R)
             (f_nonneg : forall x:R, f x > 0)
             (measure: MeasurableFunction dom)
             (a b : R) :=
    (Riemann_integrable (F_star measure f) a b).
End lebesgueintegration.

Instance ProbSpace_Measurable {T:Type} {sa: SigmaAlgebra T} (ps:ProbSpace sa) : MeasurableFunction sa
  := {
  measure_mu := ps_P ;
  measure_none := (ps_none ps) ;
  measure_ge_zero := ps_pos ;
  measure_coutably_additive := ps_countable_disjoint_union ; 
    }.

Section zmBoundedVariance.
  (* TODO finish this definition *)
  Class ZeroMeanVoundedVariance (t: nat -> R) :=
    {
    has_zero_mean: Prop;
    has_bounded_variance: Prop;
    }.
End zmBoundedVariance.
 *)
