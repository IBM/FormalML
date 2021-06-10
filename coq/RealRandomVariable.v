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
        rewrite <- H.
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

      (* rvpower_rv declared below since it uses PositiveRandomvariable *)
      
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
           {crv:ConstantRandomVariable rv_X} : ConstantRandomVariable (rvscale c rv_X)
      := { srv_val := Rmult c srv_val }.
    Next Obligation.
      destruct crv.
      unfold rvscale.
      now rewrite (srv_val_complete x).
    Qed.

  End Const.

  Section Simple.
    
    Global Program Instance srvscale (c: R)
           (rv_X : Ts -> R)
           {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvscale c rv_X)
      := { srv_vals := map (fun v => Rmult c v) srv_vals }.
    Next Obligation.
      destruct srv.
      rewrite in_map_iff.
      exists (rv_X x).
      split; trivial.
    Qed.

    Global Instance srvopp 
           {rv_X : Ts -> R}
           {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvopp rv_X)
      := srvscale (-1) rv_X.    

    Global Program Instance srvplus
           (rv_X1 rv_X2 : Ts -> R)
           {srv1:SimpleRandomVariable rv_X1}
           {srv2:SimpleRandomVariable rv_X2}
      : SimpleRandomVariable (rvplus rv_X1 rv_X2)
      := { srv_vals := map (fun ab => Rplus (fst ab) (snd ab)) 
                           (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                      (srv_vals (SimpleRandomVariable:=srv2))) }.
    Next Obligation.
      destruct srv1.
      destruct srv2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Instance srvminus 
           (rv_X1 rv_X2 : Ts -> R)
           {srv1 : SimpleRandomVariable rv_X1}
           {srv2 : SimpleRandomVariable rv_X2}  :
      SimpleRandomVariable (rvminus rv_X1 rv_X2) := 
      srvplus rv_X1 (rvopp rv_X2).

    Global Program Instance srvmult
           (rv_X1 rv_X2 : Ts -> R)
           {srv1:SimpleRandomVariable rv_X1}
           {srv2:SimpleRandomVariable rv_X2}
      : SimpleRandomVariable (rvmult rv_X1 rv_X2)
      := { srv_vals := map (fun ab => Rmult (fst ab) (snd ab)) 
                           (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                      (srv_vals (SimpleRandomVariable:=srv2))) }.
    Next Obligation.
      destruct srv1.
      destruct srv2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Program Instance srvsqr
           (rv_X : Ts -> R)
           {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvsqr rv_X)
      := { srv_vals := map Rsqr srv_vals }.
    Next Obligation.
      destruct srv.
      unfold rvsqr.
      now apply in_map.
    Qed.

    Global Program Instance srvpow
           (rv_X : Ts -> R) n
           {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvpow rv_X n)
      := { srv_vals := map (fun x => pow x n) srv_vals }.
    Next Obligation.
      destruct srv.
      unfold rvpow.
      simpl.
      apply in_map_iff.
      eauto.
    Qed.

    Global Program Instance srvabs
           (rv_X : Ts -> R)
           {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvabs rv_X)
      := { srv_vals := map Rabs srv_vals }.
    Next Obligation.
      destruct srv.
      unfold rvabs.
      now apply in_map.
    Qed.

    Global Program Instance srvmax
           (rv_X1 rv_X2 : Ts -> R)
           {srv1:SimpleRandomVariable rv_X1}
           {srv2:SimpleRandomVariable rv_X2}
      : SimpleRandomVariable (rvmax rv_X1 rv_X2)
      := { srv_vals := map (fun ab => Rmax (fst ab) (snd ab)) 
                           (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                      (srv_vals (SimpleRandomVariable:=srv2))) }.
    Next Obligation.
      destruct srv1.
      destruct srv2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Program Instance srvmin
           (rv_X1 rv_X2 : Ts -> R)
           {srv1:SimpleRandomVariable rv_X1}
           {srv2:SimpleRandomVariable rv_X2}
      : SimpleRandomVariable (rvmin rv_X1 rv_X2)
      := { srv_vals := map (fun ab => Rmin (fst ab) (snd ab)) 
                           (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                      (srv_vals (SimpleRandomVariable:=srv2))) }.
    Next Obligation.
      destruct srv1.
      destruct srv2.
      rewrite in_map_iff.
      exists (rv_X1 x, rv_X2 x).
      split.
      now simpl.
      apply in_prod; trivial.
    Qed.

    Global Program Instance positive_part_srv'
           (rv_X : Ts -> R) 
           {srv: SimpleRandomVariable rv_X } : SimpleRandomVariable (pos_fun_part rv_X)
      :=  { srv_vals := map (fun x => mknonnegreal (Rmax x 0) _) srv_vals}.
    Next Obligation.
      apply Rmax_r.
    Defined.
    Next Obligation.
      destruct srv.
      apply in_map_iff.
      unfold RandomVariable.srv_vals.
      exists (rv_X x).
      split; trivial.
    Qed.
    
    Global Program Instance positive_part_srv
           (rv_X : Ts -> R) 
           {srv: SimpleRandomVariable rv_X } : SimpleRandomVariable (fun x => nonneg (pos_fun_part rv_X x))
      :=  { srv_vals := map (fun x => (Rmax x 0)) srv_vals}.
    Next Obligation.
      destruct srv.
      apply in_map_iff.
      unfold RandomVariable.srv_vals.
      exists (rv_X x).
      split; trivial.
    Qed.    

    Global Program Instance negative_part_srv'
           (rv_X : Ts -> R) 
           {srv: SimpleRandomVariable rv_X } : SimpleRandomVariable (neg_fun_part rv_X)
      :=  { srv_vals := map (fun x => mknonnegreal (Rmax (- x) 0) _) srv_vals}.
    Next Obligation.
      apply Rmax_r.
    Defined.
    Next Obligation.
      destruct srv.
      apply in_map_iff.
      unfold RandomVariable.srv_vals.
      unfold neg_fun_part.
      exists (rv_X x).
      split; trivial.
    Qed.

    Global Program Instance negative_part_srv
           (rv_X : Ts -> R) 
           {srv: SimpleRandomVariable rv_X } : SimpleRandomVariable (fun x => nonneg (neg_fun_part rv_X x))
      :=  { srv_vals := map (fun x => (Rmax (- x) 0)) srv_vals}.
    Next Obligation.
      destruct srv.
      apply in_map_iff.
      unfold RandomVariable.srv_vals.
      exists (rv_X x).
      split; trivial.
    Qed.

    Program Instance SimpleRandomVariable_enlarged
            {rv_X : Ts -> R}
            (srv:SimpleRandomVariable rv_X)
            (l:list R)
            (lincl : incl srv_vals l)
      : SimpleRandomVariable rv_X :=
      {
      srv_vals := l
      }.
    Next Obligation.
      apply lincl.
      apply srv_vals_complete.
    Qed.


  End Simple.

  
  Section Indicator.
    
    Class IndicatorRandomVariable
          (rv_X : Ts -> R) :=
      irv_binary : forall x, In (rv_X x) [0;1] .
    

    Global Program Instance IndicatorRandomVariableSimpl
           rv_X
           {irv: IndicatorRandomVariable rv_X} : SimpleRandomVariable rv_X
      := {srv_vals := [0;1]}.
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

    Global Program Instance EventIndicator_pre_srv {P : pre_event Ts} (dec:forall x, {P x} + {~ P x})
      : SimpleRandomVariable (EventIndicator dec) :=
      IndicatorRandomVariableSimpl (EventIndicator dec).

    Global Program Instance EventIndicator_srv {P : event dom} (dec:forall x, {P x} + {~ P x})
      : SimpleRandomVariable (EventIndicator dec) :=
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
    
    Global Instance point_preimage_indicator_srv
             {rv_X:Ts -> R}
             (rv: RandomVariable dom borel_sa rv_X)
             (c:R) : SimpleRandomVariable (point_preimage_indicator rv_X c)
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


 Lemma srv_preimage_indicator (rv_X : Ts -> R) {srv:SimpleRandomVariable rv_X} :
   forall a:Ts, rv_X a =
               list_sum 
                 (map 
                    (fun c => c * (point_preimage_indicator rv_X c a))
                    (nodup Req_EM_T srv_vals)).
  Proof.
    intros.
    destruct srv; simpl.
    specialize (srv_vals_complete a).
    induction srv_vals; simpl in srv_vals_complete; [tauto |].
    simpl.
    match_destr.
    - apply IHsrv_vals.
      intuition congruence.
    - simpl.
      destruct srv_vals_complete.
      + subst.
        rewrite preimage_indicator_notin; trivial.
        unfold point_preimage_indicator, EventIndicator.
        match_destr; lra.
      + rewrite IHsrv_vals; trivial.
        unfold point_preimage_indicator, EventIndicator.
        match_destr.
        * subst.
          tauto.
        * lra.
  Qed.

  Lemma srv_preimage_indicator' (rv_X : Ts -> R) {srv:SimpleRandomVariable rv_X} :
    pointwise_relation Ts eq rv_X
               (fun a => list_sum 
                 (map 
                    (fun c => c * (point_preimage_indicator rv_X c a))
                    (nodup Req_EM_T srv_vals))).
  Proof.
    repeat red; intros.
    apply srv_preimage_indicator.
  Qed.

  End Indicator.

  Section Pos.
    
    Class PositiveRandomVariable
          (rv_X:Ts->R) : Prop :=
      prv : forall (x:Ts), (0 <= rv_X x)%R.

    Global Instance PositiveRandomVariable_proper : Proper (rv_eq ==> iff) PositiveRandomVariable.
    Proof.
      unfold PositiveRandomVariable, rv_eq, pointwise_relation.
      intros x y eqq.
      split; intros lle z.
      - rewrite <- eqq; auto.
      - rewrite eqq; auto.
    Qed.

    Global Instance PositiveRandomVariable_le_proper : Proper (rv_le ==> impl) PositiveRandomVariable.
    Proof.
      unfold PositiveRandomVariable, rv_le.
      intros x y eqq lle z.
      eapply Rle_trans; eauto.
    Qed.

    Global Instance prvconst c (cpos:0<=c) : PositiveRandomVariable (const c).
    Proof.
      intros x.
      unfold const; trivial.
    Qed.

    Global Instance IndicatorRandomVariable_positive (rv_X:Ts->R)
           {irvx:IndicatorRandomVariable rv_X} :
      PositiveRandomVariable rv_X.
    Proof.
      red in irvx; simpl in irvx.
      intros x.
      destruct (irvx x) as [|[|]]
      ; try rewrite <- H; try lra.
    Qed.

    Global Instance positive_scale_prv (c:posreal) 
           (rv_X : Ts -> R)
           {prv : PositiveRandomVariable rv_X} :
      PositiveRandomVariable (rvscale c rv_X).
    Proof.
      red; intros.
      red in prv.
      assert (0 < c) by apply (cond_pos c).
      unfold rvscale.
      specialize (prv x).
      replace (0) with (c*0) by lra.    
      apply Rmult_le_compat_l; trivial.
      now left.
    Qed.

    Global Instance rvplus_prv (rv_X1 rv_X2 : Ts -> R)
           {rv1 : PositiveRandomVariable rv_X1}
           {rv2 : PositiveRandomVariable rv_X2} :
      PositiveRandomVariable (rvplus rv_X1 rv_X2).
    Proof.
      unfold PositiveRandomVariable in *.
      unfold rvplus.
      intros.
      specialize (rv1 x); specialize (rv2 x).
      lra.
    Qed.

    Global Instance rvsum_pos (Xn : nat -> Ts -> R)
           {Xn_pos : forall n, PositiveRandomVariable (Xn n)} :
      forall (n:nat), PositiveRandomVariable (rvsum Xn n).
    Proof.
      intros.
      unfold PositiveRandomVariable in Xn_pos.
      unfold PositiveRandomVariable, rvsum; intros.
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
           (posrv : PositiveRandomVariable rv_X)
           {P : pre_event Ts} 
           (dec:forall x, {P x} + {~ P x}) : 
      PositiveRandomVariable (rvmult rv_X (EventIndicator dec)).
    Proof.
      intros x.
      unfold rvmult, EventIndicator.
      unfold PositiveRandomVariable in posrv.
      apply Rmult_le_pos; trivial.
      match_destr; lra.
    Qed.


    Global Instance EventIndicator_pos {P : pre_event Ts} (dec:forall x, {P x} + {~ P x})
      : PositiveRandomVariable (EventIndicator dec).
    Proof.
      typeclasses eauto.
    Qed.


    Global Instance rvscale_prv (phival : posreal)
           (rv_X : Ts -> R) 
           (posrv : PositiveRandomVariable rv_X) :
      PositiveRandomVariable (rvscale phival rv_X).
    Proof.
      intro x.
      unfold rvscale.
      apply Rmult_le_pos; trivial.
      left; apply cond_pos.
    Qed.

    Global Instance prvabs
           (rv_X : Ts -> R) :
      PositiveRandomVariable (rvabs rv_X).
    Proof.
      unfold PositiveRandomVariable, rvabs.
      intros; apply Rabs_pos.
    Qed.

    Global Instance prvsqr
           (rv_X : Ts -> R) :
      PositiveRandomVariable (rvsqr rv_X).
    Proof.
      unfold PositiveRandomVariable, rvsqr.
      intros.
      apply Rle_0_sqr.
    Qed.

    Global Instance prvlim
           (Xn : nat -> Ts -> R) 
           (posrv : forall n, PositiveRandomVariable (Xn n)) :
      PositiveRandomVariable (rvlim Xn).
    Proof.
      unfold PositiveRandomVariable, rvlim.
      unfold PositiveRandomVariable in posrv.
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
        apply posrv.
      Qed.

    Global Instance rvpow_prv
           (rv_X : Ts -> R) 
           (k : nat) 
           (prv : PositiveRandomVariable rv_X) :
      PositiveRandomVariable (rvpow rv_X k).
    Proof.
      unfold PositiveRandomVariable, rvpow.
      unfold PositiveRandomVariable in prv.
      intros.
      now apply pow_le.
    Qed.

    Global Instance rvpower_prv
           (rv_X1 rv_X2 : Ts -> R) :
      PositiveRandomVariable (rvpower rv_X1 rv_X2).
    Proof.
      unfold PositiveRandomVariable, rvpower in *.
      intros.
      apply power_nonneg.
    Qed.

    (* Here so that we can state the positivity constraint nicely *)
    Global Instance rvpower_rv 
           (rv_X1 rv_X2 : Ts -> R)
           {rv1 : RandomVariable dom borel_sa rv_X1}
           {rv2 : RandomVariable dom borel_sa rv_X2}
           {prv1: PositiveRandomVariable rv_X1}:
      RandomVariable dom borel_sa (rvpower rv_X1 rv_X2).
    Proof.
      apply measurable_rv.
      apply rvpower_measurable; trivial
      ; apply rv_measurable; trivial.
    Qed.
    
    Definition rvsqrt (rv_X : Ts -> R)
                      (prv : PositiveRandomVariable rv_X) := 
      fun omega => Rsqrt (mknonnegreal (rv_X omega) (prv omega)).

    Instance rvsqrt_measurable (rv_X : Ts -> R) 
             (xpos: PositiveRandomVariable rv_X) :
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
           {prv: PositiveRandomVariable rv_X}:
      RandomVariable dom borel_sa (rvsqrt rv_X prv).
    Proof.
      apply measurable_rv.
      apply rvsqrt_measurable; trivial
      ; apply rv_measurable; trivial.
    Qed.

    Definition srvsqrt_simplemapping l :=
      map (fun x =>
             match Rle_dec 0 x with
             | left pf => Rsqrt (mknonnegreal _ pf)
             | right _ => 0
             end) l.

    Global Program Instance srvsqrt
           (rv_X : Ts -> R)
           {prv: PositiveRandomVariable rv_X}
           {srv:SimpleRandomVariable rv_X} : SimpleRandomVariable (rvsqrt rv_X prv)
      := { srv_vals := srvsqrt_simplemapping srv_vals }.
    Next Obligation.
      unfold srvsqrt_simplemapping.
      apply in_map_iff.
      unfold rvsqrt; simpl.
      exists (rv_X x); simpl.
      destruct srv.
      red in prv0.
      match_destr.
      - split; trivial.
        now apply Rsqrt_ext.
      - generalize (prv0 x).
        congruence.
    Qed.

    Global Instance prvchoice (c:Ts->bool) (rv_X1 rv_X2 : Ts -> R)
           {prv1:PositiveRandomVariable rv_X1}
           {prv2:PositiveRandomVariable rv_X2} :
      PositiveRandomVariable (rvchoice c rv_X1 rv_X2).
    Proof.
      unfold PositiveRandomVariable in *.
      intros x.
      unfold rvchoice.
      match_destr.
    Qed.

    Global Instance prvmin (rv_X1 rv_X2 : Ts -> R)
           {prv1:PositiveRandomVariable rv_X1}
           {prv2:PositiveRandomVariable rv_X2} :
      PositiveRandomVariable (rvmin rv_X1 rv_X2).
    Proof.
      unfold PositiveRandomVariable in *.
      intros x.
      unfold rvmin.
      eapply Rmin_glb; eauto.
    Qed.

    Global Instance prvmax_l  (rv_X1 rv_X2 : Ts -> R)
           {prv1:PositiveRandomVariable rv_X1} : PositiveRandomVariable (rvmax rv_X1 rv_X2).
    Proof.
      intros x.
      unfold rvmax.
      eapply Rle_trans; try eapply (prv1 x).
      eapply Rmax_l.
    Qed.

    Global Instance prvmax_r  (rv_X1 rv_X2 : Ts -> R)
           {prv1:PositiveRandomVariable rv_X2} : PositiveRandomVariable (rvmax rv_X1 rv_X2).
    Proof.
      intros x.
      unfold rvmax.
      eapply Rle_trans; try eapply (prv1 x).
      eapply Rmax_r.
    Qed.

    Global Instance positive_part_prv 
           (rv_X : Ts -> R) :
      PositiveRandomVariable (pos_fun_part rv_X).
    Proof.
      unfold PositiveRandomVariable.
      unfold pos_fun_part; simpl.
      intros.
      apply Rmax_r.
    Qed.

    
    Global Instance negative_part_prv
           (rv_X : Ts -> R) :
      PositiveRandomVariable (neg_fun_part rv_X).
    Proof.
      unfold PositiveRandomVariable.
      unfold neg_fun_part.
      intros.
      apply cond_nonneg.
    Qed.
    
  End Pos.

  Instance rv_fun_simple_R (x : Ts -> R) (f : R -> R)
            (rvx : RandomVariable dom borel_sa x) 
            (srvx : SimpleRandomVariable x) :
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

Instance Restricted_PositiveRandomVariable {Ts:Type} {dom : SigmaAlgebra Ts}
         (e:event dom) (f : Ts -> R)
         (prv: PositiveRandomVariable f) :
  PositiveRandomVariable (event_restricted_function e f).
Proof.
  unfold PositiveRandomVariable in *.
  intros.
  apply prv.
Qed.

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
