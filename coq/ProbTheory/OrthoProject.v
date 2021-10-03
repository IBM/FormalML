Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Export RandomVariableLpR RandomVariableL2.
Require Import quotient_space.

Require Import Event.
Require Import Almost.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section ortho_project.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  (* the conditional expectation of x over the sub-algebra dom2 *)

  Definition ortho_phi (dom2 : SigmaAlgebra Ts)
    : LpRRVq prts 2 -> Prop
    := (fun y:LpRRVq prts 2 =>
          exists z, Quot _ z = y /\
               RandomVariable dom2 borel_sa (LpRRV_rv_X prts z)).

  Definition LpRRV_filter_from_seq {dom2:SigmaAlgebra Ts} {prts2 : ProbSpace dom2}
             (f : nat -> LpRRV prts2 2) : ((LpRRV_UniformSpace prts2 big2 -> Prop) -> Prop) :=
    fun (P : (LpRRV_UniformSpace prts2 big2 -> Prop)) => exists (N:nat), forall (n:nat), (n >= N)%nat -> P (f n).

  Lemma cauchy_filterlim_almost_unique_eps (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
    (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
    forall (eps:posreal), LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) < eps.
  Proof.
    intros.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/2) by lra.
    specialize (H (mkposreal _ H2)).
    specialize (H0 (mkposreal _ H2)).     
    generalize (Hierarchy.filter_and _ _ H H0); intros.
    apply filter_ex in H3.
    unfold LpRRVball in H3.
    destruct H3 as [? [? ?]].
    generalize (LpRRV_dist_triang prts big2 x x0 y); intros.
    unfold LpRRV_dist in H5.
    eapply Rle_lt_trans.
    apply H5.
    rewrite LpRRVnorm_minus_sym in H4.
    simpl in H3; simpl in H4; simpl.
    lra.
  Qed.     

  Lemma cauchy_filterlim_almost_unique_eps_alt (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
    (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
    forall (eps:posreal), LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) < eps.
  Proof.
    intros.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/4) by lra.
    destruct (H (mkposreal _ H2)) as [x0 [? ?]].
    destruct (H0 (mkposreal _ H2)) as [y0 [? ?]].
    generalize (Hierarchy.filter_and _ _ H3 H5); intros.
    apply filter_ex in H7.
    unfold LpRRVball in H7.
    destruct H7 as [? [? ?]].
    generalize (LpRRV_dist_triang prts big2 x x0 x1); intros.
    generalize (LpRRV_dist_triang prts big2 x1 y0 y); intros.
    unfold LpRRV_dist in H9.
    unfold LpRRV_dist in H10.
    generalize (LpRRV_dist_triang prts big2 x x1 y); intros.
    unfold LpRRV_dist in H11.
    apply LpRRV_ball_sym in H4; unfold LpRRVball in H4; simpl in H4.
    simpl in H7.
    rewrite LpRRVnorm_minus_sym in H8; simpl in H8.
    unfold LpRRVball in H6; simpl in H6.
    eapply Rle_lt_trans.
    apply H11.
    assert (LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x x1) < eps/2).
    {
      eapply Rle_lt_trans.
      apply H9.
      simpl; lra.
    }
    assert (LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x1 y) < eps/2).
    {
      eapply Rle_lt_trans.
      apply H10.
      simpl; lra.
    }
    lra.
  Qed.     

  Lemma cauchy_filterlim_almost_unique_0 (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
    (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
    LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) = 0.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_eps _ _ _ _ H H0); intros.
    apply nneg_lt_eps_zero; trivial.
    apply power_nonneg.
  Qed.

  Lemma cauchy_filterlim_almost_unique_alt_0 (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
    (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
    LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) = 0.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_eps_alt _ _ _ _ H H0); intros.
    apply nneg_lt_eps_zero; trivial.
    apply power_nonneg.
  Qed.

  Lemma cauchy_filterlim_almost_unique (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
    (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
    almostR2 prts eq x y.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_0 _ _ _ _ H H0); intros.
    apply LpRRV_norm0 in H1.
    now apply LpRRValmost_sub_zero_eq in H1.
  Qed.

  Lemma cauchy_filterlim_almost_unique_alt (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
        (PF : ProperFilter F)
        (x y : LpRRV prts 2) :
    (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
    (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
    almostR2 prts eq x y.
  Proof.
    intros.
    generalize (cauchy_filterlim_almost_unique_alt_0 _ _ _ _ H H0); intros.
    apply LpRRV_norm0 in H1.
    now apply LpRRValmost_sub_zero_eq in H1.
  Qed.
  
  Definition subset_to_sa_sub
             {dom2 : SigmaAlgebra Ts}
             (sub : sa_sub dom2 dom)
             (set:LpRRV_UniformSpace (prob_space_sa_sub prts sub) big2 -> Prop) :
    {x : LpRRV_UniformSpace prts big2 | RandomVariable dom2 borel_sa x} -> Prop.
  Proof.
    intros [x pfx].
    apply set.
    simpl.
    destruct x; simpl in *.
    exists LpRRV_rv_X; trivial.
    apply IsLp_prob_space_sa_sub; trivial.
  Defined.

  Definition subset_filter_to_sa_sub_filter
             {dom2 : SigmaAlgebra Ts}
             (sub : sa_sub dom2 dom)
             (F:({x : LpRRV_UniformSpace prts big2 | RandomVariable dom2 borel_sa x} -> Prop) -> Prop) :
    (LpRRV_UniformSpace (prob_space_sa_sub prts sub) big2 -> Prop) -> Prop.
  Proof.
    intros sa.
    apply F.
    eapply subset_to_sa_sub; eauto.
  Defined.

  Lemma subset_filter_to_sa_sub_filter_Filter {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) F :
    Filter F ->
    Filter (subset_filter_to_sa_sub_filter sub F).
  Proof.
    intros [FF1 FF2 FF3].
    unfold subset_filter_to_sa_sub_filter, subset_to_sa_sub.
    split.
    - eapply FF3; try eapply FF1; intros.
      destruct x; trivial.
    - intros.
      eapply FF3; try eapply FF2; [| eapply H | eapply H0].
      intros [??]; simpl; intros.
      tauto.
    - intros.
      eapply FF3; [| eapply H0].
      intros [??].
      eapply H.
  Qed.

  Lemma subset_filter_to_sa_sub_filter_proper {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) F :
    ProperFilter F ->
    ProperFilter (subset_filter_to_sa_sub_filter sub F).
  Proof.
    intros pf.
    unfold subset_filter_to_sa_sub_filter; simpl.
    constructor.
    - intros.
      destruct pf.
      destruct (filter_ex _ H).
      destruct x; simpl in *.
      eexists; eapply H0.
    - destruct pf.
      now apply subset_filter_to_sa_sub_filter_Filter.
  Qed.

  Definition prob_space_sa_sub_set_lift
             {dom2} (sub:sa_sub dom2 dom)
             (s:LpRRV (prob_space_sa_sub prts sub) 2 -> Prop)
             (x:LpRRV prts 2) : Prop.
  Proof.
    destruct x.
    destruct (ClassicalDescription.excluded_middle_informative (RandomVariable dom2 borel_sa LpRRV_rv_X)).
    - apply s.
      exists LpRRV_rv_X; trivial.
      now apply IsLp_prob_space_sa_sub.
    - exact False.
  Defined.

  Definition prob_space_sa_sub_LpRRV_lift
             {dom2} (sub:sa_sub dom2 dom)
             (s:LpRRV (prob_space_sa_sub prts sub) 2)
    : LpRRV prts 2.
  Proof.
    destruct s.
    exists LpRRV_rv_X.
    - eapply RandomVariable_sa_sub; eauto.
    - eapply IsLp_prob_space_sa_sub; eauto.
  Defined.

  Instance prob_space_sa_sub_LpRRV_lift_rv {dom2} (sub:sa_sub dom2 dom) (X:LpRRV (prob_space_sa_sub prts sub) 2)
           {rvx:RandomVariable dom2 borel_sa X} :
    RandomVariable dom2 borel_sa (prob_space_sa_sub_LpRRV_lift sub X).
  Proof.
    now destruct X; simpl in *.
  Qed.

  Lemma ortho_phi_closed 
        {dom2 : SigmaAlgebra Ts} 
        (sub : sa_sub dom2 dom) :
    @closed (LpRRVq_UniformSpace prts 2 big2) (ortho_phi dom2).
  Proof.
    unfold closed, ortho_phi, locally.
    intros.
    destruct (Quot_inv x); subst.
    generalize (not_ex_all_not _ _ H)
    ; intros HH1; clear H.
    generalize (fun n => not_all_ex_not _ _ (HH1 n))
    ; intros HH2; clear HH1.

    assert (HH3: forall n : posreal,
               exists n0 : LpRRVq_UniformSpace prts 2 big2,
                 @Hierarchy.ball  (LpRRVq_UniformSpace prts 2 big2) (Quot (LpRRV_eq prts) x0) n n0 /\
                 (exists z : LpRRV prts 2,
                     Quot (LpRRV_eq prts) z = n0 /\ RandomVariable dom2 borel_sa z)).
    {
      intros n.
      destruct (HH2 n).
      exists x.
      apply not_all_not_ex in H.
      destruct H.
      tauto.
    }
    clear HH2.
    
    assert (HH4: forall eps : posreal,
               exists z : LpRRV prts 2,
                 (@Hierarchy.ball (LpRRVq_UniformSpace prts 2 big2)
                                  (Quot (LpRRV_eq prts) x0) eps
                                  (Quot (LpRRV_eq prts) z)) /\
                 (RandomVariable dom2 borel_sa z)).
    {
      intros eps.
      destruct (HH3 eps) as [x [xH1 [z [xH2 xH3]]]]; subst.
      eauto.
    }
    clear HH3.
    assert (HH5: forall eps : posreal,
               exists z : LpRRV prts 2,
                 (@Hierarchy.ball (LpRRV_UniformSpace prts big2)
                                  x0 eps z) /\
                 (RandomVariable dom2 borel_sa z)).
    {
      intros eps.
      destruct (HH4 eps) as [x [? ?]].
      red in H; simpl in H.
      rewrite LpRRVq_ballE in H.
      eauto.
    }
    assert (forall (n : nat), 0 < (/ (INR (S n)))).
    {
      intros.
      apply Rinv_0_lt_compat.
      apply lt_0_INR.
      lia.
    }
    assert (forall (n:nat),
               {z:LpRRV prts 2 |
                 (LpRRVball prts big2 x0 (mkposreal _ (H n)) z) /\
                 (RandomVariable dom2 borel_sa z)}).
    {
      intros.
      destruct (constructive_indefinite_description _ (HH5 (mkposreal _ (H n))))
        as [x Fx].
      now exists x.
    }
    pose (f := fun (n : nat) => proj1_sig (X n)).
    assert (is_lim_seq (fun n => LpRRV_dist prts (p:=bignneg _ big2) (f n) x0) 0).
    {
      apply is_lim_seq_spec.
      unfold is_lim_seq'.
      intros.
      assert (0 < eps) by apply cond_pos.
      generalize (archimed_cor1 eps H0); intros.
      destruct H1 as [? [? ?]].
      exists x.
      intros.
      rewrite Rminus_0_r, Rabs_pos_eq.
      - unfold f.
        destruct (X n) as [? [? ?]].
        simpl.
        apply LpRRV_ball_sym in l.
        unfold LpRRVball in l.
        eapply Rlt_trans.
        apply l.
        apply Rlt_trans with (r2 := / INR x); trivial.
        apply Rinv_lt_contravar.
        apply Rmult_lt_0_compat.
        + now apply lt_0_INR.
        + apply lt_0_INR; lia.
        + apply lt_INR; lia.
      - unfold LpRRVnorm.
        apply power_nonneg.
    }
    pose (prts2 := prob_space_sa_sub prts sub).

    pose (F :=  LpRRV_filter_from_seq f).
    pose (dom2pred := fun v => RandomVariable dom2 borel_sa v).
    pose (F2 := subset_filter F dom2pred ).
    pose (F3:=subset_filter_to_sa_sub_filter sub F2).

    generalize (L2RRV_lim_complete prts2 big2 F3); intros HH1.

    
    assert (ProperFilter F).
    {
      subst F f.
      unfold LpRRV_filter_from_seq; simpl.
      split.
      - intros P [N HP].
        exists (proj1_sig (X N)).
        apply HP.
        lia.
      - split.
        + exists 0%nat; trivial.
        + intros P Q [NP HP] [NQ HQ].
          exists (max NP NQ); intros n nN.
          split.
          * apply HP.
            generalize (Max.le_max_l NP NQ); lia.
          * apply HQ.
            generalize (Max.le_max_r NP NQ); lia.
        + intros P Q Himp [N HP].
          exists N; intros n nN.
          auto.
    }

    assert (pfsub:ProperFilter (subset_filter F (fun v : LpRRV prts 2 => dom2pred v))).
    {
      apply subset_filter_proper; intros.
      subst F.
      subst f.
      unfold LpRRV_filter_from_seq in H2.
      destruct H2 as [? HH2].
      unfold dom2pred.
      exists (proj1_sig (X x)).
      split.
      - destruct (X x); simpl.
        tauto.
      - apply HH2; lia.
    } 
    
    assert (F3proper:ProperFilter F3).
    {
      unfold F3, F2.
      now apply subset_filter_to_sa_sub_filter_proper.
    }

    assert (F3cauchy:cauchy F3).
    {
      unfold F3, F2.
      unfold subset_filter_to_sa_sub_filter.
      intros eps; simpl.
      unfold F, f.
      unfold LpRRV_filter_from_seq; simpl.
      unfold dom2pred.
      assert (eps2pos:0 < eps / 2).
      {
        destruct eps; simpl.
        lra.
      } 

      destruct (archimed_cor1 (eps/2) eps2pos) as [N [Nlt Npos]].

      destruct (X N)
        as [x [XH XR]].
      assert (xlp:IsLp (prob_space_sa_sub prts sub) 2 x).
      {
        apply IsLp_prob_space_sa_sub; typeclasses eauto.
      } 
      exists (pack_LpRRV (prob_space_sa_sub prts sub) x).
      red.
      exists N.
      simpl.
      intros n nN ?.
      destruct (X n) as [Xn [XnH XnRv]]; simpl in *.
      unfold pack_LpRRV; simpl.
      generalize (LpRRV_dist_triang prts big2 x x0 Xn)
      ; intros triag.
      unfold LpRRV_dist in triag.
      unfold Hierarchy.ball; simpl.
      unfold LpRRVball; simpl.
      simpl in *.

      destruct Xn as [Xn ??]; simpl in *.
      apply LpRRV_ball_sym in XH.
      LpRRV_simpl.
      simpl in *.
      unfold LpRRVball in XnH, XH, triag.
      simpl in XnH, XH, triag.
      unfold LpRRVminus in XnH, XH, triag; simpl in XnH, XH, triag.
      
      unfold LpRRVnorm in *.
      erewrite FiniteExpectation_prob_space_sa_sub; try typeclasses eauto.
      unfold pack_LpRRV, prob_space_sa_sub in XnH, XH, triag |- *; simpl in *.
      eapply Rle_lt_trans; try eapply triag.
      replace (pos eps) with ((eps/2) + (eps/2)) by lra.
      assert (sNeps2:/ INR (S N) < eps /2).
      {
        apply Rle_lt_trans with (r2 := / INR N); trivial.
        apply Rinv_le_contravar.
        - apply lt_0_INR; lia.
        - apply le_INR; lia.
      }
      assert (sneps2:/ INR (S n) < eps /2).
      {
        apply Rle_lt_trans with (r2 := / INR (S N)); trivial.
        apply Rinv_le_contravar.
        - apply lt_0_INR; lia.
        - apply le_INR; lia.
      }
      apply Rplus_lt_compat.
      - rewrite <- sNeps2; trivial.
      - rewrite <- sneps2; trivial.
    } 
    cut_to HH1; trivial.
    exists (prob_space_sa_sub_LpRRV_lift sub (LpRRV_lim prts2 big2 F3)).
    split; [|typeclasses eauto].
    LpRRVq_simpl.
    unfold LpRRV_eq.
    apply (LpRRValmost_sub_zero_eq prts (p := bignneg 2 big2)).
    apply LpRRV_norm0.
    apply nneg_lt_eps_zero; [apply power_nonneg |].
    assert (forall (eps:posreal),
               exists (N:nat),
                 forall (n:nat), (n>=N)%nat ->
                          LpRRV_dist prts (p:=bignneg _ big2) (f n) x0 < eps).
    {
      intros.
      apply is_lim_seq_spec in H0.
      destruct (H0 eps).
      exists x; intros.
      specialize (H2 n H3).
      rewrite Rminus_0_r in H2.
      now rewrite Rabs_pos_eq in H2 by apply power_nonneg.
    }

    assert (F3limball:forall (eps:posreal),
               (LpRRV_dist prts  (p:=bignneg _ big2) (prob_space_sa_sub_LpRRV_lift sub (LpRRV_lim prts2 big2 F3)) x0) < eps).
    {
      intros.
      assert (0 < eps) by apply cond_pos.
      assert (0 < eps/2) by lra.
      destruct (HH1 (mkposreal _ H4)).
      destruct (H2 (mkposreal _ H4)).
      specialize (H6 (max x x1)).
      specialize (H5 (max x x1)).
      cut_to H5; try lia.
      cut_to H6; try lia.
      unfold F3, F2, F in H5.
      unfold LpRRV_filter_from_seq in H5.
      generalize (LpRRV_dist_triang prts big2 (prob_space_sa_sub_LpRRV_lift sub (LpRRV_lim prts2 big2 F3)) (f (max x x1)) x0); intros.
      rewrite Rplus_comm in H7.
      eapply Rle_lt_trans.
      apply H7.
      replace (pos eps) with ((eps/2) + (eps/2)) by lra.
      apply Rplus_lt_compat.
      apply H6.
      unfold dom2pred in H5.
      assert (frv:RandomVariable dom2 borel_sa (f (Init.Nat.max x x1))).
      {
        unfold f.
        unfold proj1_sig.
        match_destr; tauto.
      } 
      specialize (H5 frv).
      unfold subset_to_sa_sub, Hierarchy.ball in H5.
      simpl in H5.
      unfold LpRRVball, LpRRVnorm in H5.
      simpl in H5.
      unfold prts2 in H5.
      assert (isfe2:IsFiniteExpectation prts
                                        (rvpower
                                           (rvabs
                                              (rvminus
                                                 (LpRRV_lim (prob_space_sa_sub prts sub) big2
                                                            (subset_filter_to_sa_sub_filter sub
                                                                                            (subset_filter
                                                                                               (fun P : LpRRV prts 2 -> Prop =>
                                                                                                  exists N : nat, forall n : nat, (n >= N)%nat -> P (f n))
                                                                                               (fun v : LpRRV prts 2 => RandomVariable dom2 borel_sa v))))
                                                 (match
                                                     f (Init.Nat.max x x1) as l
                                                     return (RandomVariable dom2 borel_sa l -> LpRRV (prob_space_sa_sub prts sub) 2)
                                                   with
                                                   | {| LpRRV_rv_X := LpRRV_rv_X; LpRRV_lp := LpRRV_lp |} =>
                                                     fun pfx : RandomVariable dom2 borel_sa LpRRV_rv_X =>
                                                       {|
                                                         LpRRV_rv_X := LpRRV_rv_X;
                                                         LpRRV_rv := pfx;
                                                         LpRRV_lp := match IsLp_prob_space_sa_sub prts sub 2 LpRRV_rv_X with
                                                                     | conj x _ => x
                                                                     end LpRRV_lp |}
                                                   end frv))) (const 2))).
      {
        eapply (IsFiniteExpectation_prob_space_sa_sub prts sub); try typeclasses eauto.
        unfold FiniteExpectation, proj1_sig in H5.
        match_destr_in H5.
        red.
        now rewrite e.
      }       
      rewrite (FiniteExpectation_prob_space_sa_sub _ _ _ (isfe2:=isfe2)) in H5.
      unfold LpRRV_dist, LpRRVnorm.
      simpl.
      unfold f in *.
      eapply Rle_lt_trans; try eapply H5.
      right.
      f_equal.
      apply FiniteExpectation_ext; intros ?.
      rv_unfold.
      f_equal.
      f_equal.
      f_equal.
      - unfold prob_space_sa_sub_LpRRV_lift; simpl.
        unfold F3, F2, F.
        unfold LpRRV_filter_from_seq.
        simpl.
        unfold prts2, dom2pred.
        match_destr.
      - f_equal.
        clear H6.

        destruct (X (Init.Nat.max x x1)); simpl.
        match_destr.
    } 
    apply F3limball.
  Qed.

  Lemma ortho_phi_complete
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) :
    @complete_subset (@PreHilbert_NormedModule (@L2RRVq_PreHilbert Ts dom prts)) (ortho_phi dom2).
  Proof.
    unfold complete_subset.
    exists (LpRRVq_lim prts big2).
    intros F PF cF HH.
    assert (HHclassic: forall P : PreHilbert_NormedModule -> Prop,
               F P -> (exists x : PreHilbert_NormedModule, P x /\ ortho_phi dom2 x)).
    {
      intros P FP.
      specialize (HH P FP).
      now apply NNPP in HH.
    }
    clear HH.
    match goal with
      [|- _ /\ ?x ] => cut x; [split; trivial |]
    end.
    - apply ortho_phi_closed; trivial.
      simpl.
      unfold locally.
      intros [eps HH].
      specialize (H eps).
      destruct (HHclassic _ H) as [? [? ?]].
      specialize (HH x).
      elim HH; trivial.
      now rewrite <- hball_pre_uniform_eq.
    - intros.
      assert (cF':@cauchy (@LpRRVq_UniformSpace Ts dom prts (IZR (Zpos (xO xH))) big2) F).
      {
        now apply cauchy_pre_uniform.
      } 
      generalize (LpRRVq_lim_complete prts big2 F PF); intros.
      eapply filter_imp; try eapply (H cF' eps).
      + intros.
        unfold Hierarchy.ball; simpl.
        now apply L2RRVq_ball_ball.
  Qed.

  Program Definition ortho_projection_hilbert (E:PreHilbert) 
          (phi: E -> Prop) (phi_mod: compatible_m phi) (phi_compl: complete_subset phi)
          (u : E) : {v:E |
                      unique (fun v => phi v /\ norm (minus u v) = Glb_Rbar (fun r : R => exists w : E, phi w /\ r = norm (minus u w))) v}.
  generalize (ortho_projection_subspace phi phi_mod phi_compl u);intros.
  cut_to H.
  - destruct (constructive_definite_description _ H) as [x xH].
    exists x.
    split; trivial.
    destruct H as [y [yH1 yH2]].
    intros.
    transitivity y; [| eauto].
    symmetry; eauto.
  - intro; apply classic.
  Qed.

  Lemma ortho_phi_compatible_m
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
    : compatible_m (E:=(L2RRVq_PreHilbert prts)) (ortho_phi dom2).
  Proof.
    split; [split | ]; intros.
    - destruct H as [a [eqqa rv_a]]; subst.
      destruct H0 as [b [eqqb rv_b]]; subst.
      unfold plus, opp; simpl.
      rewrite LpRRVq_oppE, LpRRVq_plusE.
      eexists.
      split.
      + reflexivity.
      + typeclasses eauto.
    - exists (LpRRVq_zero prts).
      exists (LpRRVzero prts).
      simpl.
      split.
      + reflexivity.
      + typeclasses eauto.
    - destruct H as [a [eqqa Ha]]; subst.
      exists (LpRRVscale prts l a).
      simpl.
      split.
      + unfold scal; simpl.
        rewrite LpRRVq_scaleE.
        reflexivity.
      + typeclasses eauto.
  Qed.

End ortho_project.
