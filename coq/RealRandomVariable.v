Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq.
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
      intros ??.
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

    Lemma sa_singleton (c:R) (rv_X:Ts->R)
          {rv : RandomVariable dom borel_sa rv_X} :
      sa_sigma (event_preimage rv_X (event_singleton c)).
    Proof.
      apply sa_le_pt; intros.
      apply borel_sa_preimage2; intros.
      now apply rv_preimage.
    Qed.

    Instance scale_measurable_pos (f : Ts -> R) (c:posreal) :
      RealMeasurable f ->
      RealMeasurable (rvscale c f).
    Proof.
      intros ? r.
      assert (event_equiv (fun omega : Ts => (c * f omega <= r)%R)
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
      assert (event_equiv (fun omega : Ts => ((-c) * f omega <= r)%R)
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
      - assert (event_equiv (fun _ : Ts => c <= r)
                            (fun _ : Ts => True)).
        red; intros.
        intuition.
        rewrite H.
        apply sa_all.
      - assert (event_equiv (fun _ : Ts => c <= r)
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
      - now apply sa_singleton.
      - now apply sa_singleton.
    Qed.

    
    Instance Ropp_measurable (f : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable (rvopp f).
    Proof.
      intros ??.
      assert (event_equiv (fun omega : Ts => rvopp f omega <= r)
                          (fun omega : Ts => (f omega) >= -r)).
      unfold event_equiv; intros.
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
      assert (event_equiv (fun omega : Ts => rvplus f g omega <= r)
                          (event_complement (fun omega : Ts => f omega + g omega > r))).
      - unfold event_equiv, event_complement, rvplus; intros.
        lra.
      - rewrite H1.
        assert (event_equiv 
                  (fun omega : Ts => (f omega) + (g omega) > r)
                  (union_of_collection
                     (fun (n:nat) => 
                        event_inter
                          (fun omega : Ts => f omega > r - Qreals.Q2R (iso_b n))
                          (fun omega : Ts => g omega > Qreals.Q2R (iso_b n))))).
        + unfold event_equiv, union_of_collection, event_inter; intros.
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
      - assert (event_equiv (fun omega : Ts => rvsqr f omega <= r)
                            (fun _ => False)).
        + unfold event_equiv; intros.
          generalize (Rle_0_sqr (f x)).
          unfold rvsqr.
          lra.
        + rewrite H1.
          apply sa_none.
      - assert (0 <= r) by lra.
        assert (event_equiv (fun omega : Ts => rvsqr f omega <= r)
                            (fun omega : Ts => (f omega) <= Rsqrt (mknonnegreal _ H1)) ).
        + unfold event_equiv, rvsqr; intros.
          specialize (H x).
          apply Rsqr_le_to_Rsqrt with (r := mknonnegreal _ H1) (x := mknonnegreal _ H).
        + rewrite H2.
          apply H0.
    Qed.
    
    Lemma measurable_open_continuous (f : Ts -> R) (g : R -> R) :
      continuity g ->
      (forall B: event R, open_set B -> sa_sigma (event_preimage f B)) ->
      (forall B: event R, open_set B -> 
                     sa_sigma (event_preimage (fun omega => g (f omega)) B)).
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

    Instance Rsqr_measurable (f : Ts -> R) :
      RealMeasurable f ->
      RealMeasurable (rvsqr f).
    Proof.
      intros.
      unfold rvsqr.
      apply measurable_continuous; trivial.
      apply Rsqr_continuous.
    Qed.

    Instance product_measurable (f g : Ts -> R) :
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

    Section rvs.

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
        typeclasses eauto.
      Qed.

      Global Instance rvplus_rv (rv_X1 rv_X2 : Ts -> R)
             {rv1 : RandomVariable dom borel_sa rv_X1}
             {rv2 : RandomVariable dom borel_sa rv_X2} :
        RandomVariable dom borel_sa (rvplus rv_X1 rv_X2).
      Proof.
        typeclasses eauto.
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

    Global Instance EventIndicator_rv {P : event Ts} (dec:forall x, {P x} + {~ P x})
           (sap: sa_sigma P) : RandomVariable dom borel_sa (EventIndicator dec).
    Proof.
      red; intros.
      apply borel_sa_preimage; trivial; intros.
      destruct (Rlt_dec r 0).
      - unfold EventIndicator.
        simpl.
        assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                            event_none).
        + unfold event_equiv, event_none; intros.
          destruct (dec x); lra.
        + rewrite H0; apply sa_none.
      - destruct (Rlt_dec r 1).
        + assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                              (fun omega : Ts => ~ P omega)).
          * unfold event_equiv; intros.
            destruct (dec x).
            -- split; [lra | congruence].
            -- split; [congruence | lra].
          * rewrite H0.
            now apply sa_complement.
        + assert (event_equiv (fun omega : Ts => (if dec omega then 1 else 0) <= r)
                              (fun omega : Ts => True)).
          * unfold event_equiv; intros.
            destruct (dec x); lra.
          * rewrite H0.
            apply sa_all.
    Qed.

    Global Instance EventIndicator_indicator (P : event Ts) (dec:forall x, {P x} + {~ P x})
      : IndicatorRandomVariable (EventIndicator dec).
    Proof.
      unfold EventIndicator.
      intros x.
      simpl.
      match_destr; tauto.
    Qed.

    Global Program Instance EventIndicator_srv {P : event Ts} (dec:forall x, {P x} + {~ P x})
      : SimpleRandomVariable (EventIndicator dec) :=
      IndicatorRandomVariableSimpl (EventIndicator dec).
    
    Definition point_preimage_indicator
               (rv_X:Ts -> R)
               (c:R) :=
      EventIndicator (fun x => Req_EM_T (rv_X x) c).

    Instance point_preimage_indicator_rv
             {rv_X:Ts -> R}
             (rv: RandomVariable dom borel_sa rv_X)
             (c:R) : RandomVariable dom borel_sa (point_preimage_indicator rv_X c).
    Proof.
      apply EventIndicator_rv.
      now apply sa_singleton.
    Qed.    
    
    Instance point_preimage_indicator_srv
             {rv_X:Ts -> R}
             (rv: RandomVariable dom borel_sa rv_X)
             (c:R) : SimpleRandomVariable (point_preimage_indicator rv_X c)
      := IndicatorRandomVariableSimpl _.

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

    Global Instance indicator_prod_pos 
           (rv_X : Ts -> R) 
           (posrv : PositiveRandomVariable rv_X)
           {P : event Ts} 
           (dec:forall x, {P x} + {~ P x}) : 
      PositiveRandomVariable (rvmult rv_X (EventIndicator dec)).
    Proof.
      intros x.
      unfold rvmult, EventIndicator.
      unfold PositiveRandomVariable in posrv.
      apply Rmult_le_pos; trivial.
      match_destr; lra.
    Qed.


    Global Instance EventIndicator_pos {P : event Ts} (dec:forall x, {P x} + {~ P x})
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


End RealRandomVariables.

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

