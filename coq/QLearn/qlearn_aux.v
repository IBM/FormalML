Require Import Qreals.
Require Import List.
Require Import mdp qvalues fixed_point.
Require Import RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import Expectation RandomVariableFinite RbarExpectation.
Require Import SigmaAlgebras ProbSpace.
Require Import ConditionalExpectation.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import DiscreteProbSpace ProductSpace.

Set Bullet Behavior "Strict Subproofs".

Section qlearn_aux.

Context {Ts : Type} {dom: SigmaAlgebra Ts}.

  Lemma inter_coll_le_sup {prts: ProbSpace dom} (f : nat -> Ts -> R) (eps:R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
    forall n,
      event_equiv
        (inter_of_collection (fun t : nat => event_le dom (rvabs (f (n + t)%nat)) eps))
        (event_Rbar_le (fun x0 : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x0))) (const eps)).
    Proof.
      intros n z.
      simpl.
      unfold rvabs, const, pre_event_complement.
      split; intros.
      - replace (Finite eps) with (Sup_seq (fun n => eps)).
        + apply Sup_seq_le.
          intros.
          simpl.
          apply H.
        + apply Sup_seq_const.
          - rewrite Rbar_sup_eq_lub in H.
            unfold Rbar_lub, proj1_sig in H.
            match_destr_in H.
            unfold Rbar_is_lub, Rbar_is_upper_bound in r.
            destruct r.
            generalize (Rbar_le_trans  (Rabs (f (n + n0)%nat z)) x eps); intros.
            simpl in H2.
            apply H2; trivial.
            destruct x.
            + specialize (H0 ( Rabs (f (n + n0)%nat z))).
              simpl in H0.
              apply H0.
              now exists n0.
            + trivial.
            + specialize (H0 (Rabs (f (n + 0)%nat z))).
              simpl in H0.
              apply H0.
              now exists (0%nat).
    Qed.                         

    Lemma event_Rbar_gt_complement (f : Ts -> Rbar) (eps:R)
          {rv : RandomVariable dom Rbar_borel_sa f} :
      event_equiv
        (event_Rbar_gt f (const eps))
        (event_complement (event_Rbar_le f (const eps))).
    Proof.
      intros ?.
      unfold event_Rbar_gt, event_Rbar_le, event_complement, pre_event_complement, proj1_sig.
      unfold Rbar_gt.
      split; intros.
      - now apply Rbar_lt_not_le.
      - now apply Rbar_not_le_lt.
    Qed.

  Lemma union_coll_gt_sup {prts: ProbSpace dom} (f : nat -> Ts -> R) (eps:posreal)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
    forall n,
      event_equiv
        (union_of_collection (fun t : nat => event_gt dom (rvabs (f (n + t)%nat)) eps))
        (event_Rbar_gt (fun x0 : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x0))) (const (pos eps))).
    Proof.
      intros n.
      generalize (inter_coll_le_sup f eps); intros.
      assert (event_equiv
                (union_of_collection (fun t : nat => event_gt dom (rvabs (f (n + t)%nat)) eps))
                (event_complement (inter_of_collection (fun t : nat => event_le dom (rvabs (f (n + t)%nat)) eps)))).
      {
        rewrite inter_of_collection_complement.
        intros ?.
        simpl.
        unfold pre_event_complement.
        split; intros; destruct H0; exists x0; lra.
     }
      rewrite H0.
      rewrite event_Rbar_gt_complement.
      apply event_complement_proper.
      apply inter_coll_le_sup.
  Qed.

Lemma sa_sigma_not_convergent (X : nat -> Ts -> R) (X0 : Ts -> R) (eps : posreal) (N : nat)
      {rv : forall n, RandomVariable dom borel_sa (X n)}
      {rv0 : RandomVariable dom borel_sa X0} :
  sa_sigma _ (fun omega => exists n : nat, (n >= N)%nat /\ Rabs (X n omega - X0 omega) >= eps).
Proof.
  apply sa_countable_union; intros n.
  apply sa_inter; try apply sa_sigma_const_classic.
  apply sa_le_ge; intros r.
  apply Rabs_measurable.
  generalize (minus_measurable dom (X n) (X0)); intros.
  rewrite rvminus_unfold in H.
  apply H.
  -- apply rv_measurable; try apply rv.
  -- apply rv_measurable; try apply rv0.
Qed.

Lemma sa_sigma_not_full_convergent (X : nat -> Ts -> R) X0
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
  {rv0 : RandomVariable dom borel_sa X0}:
  sa_sigma _ (fun omega => exists (eps : posreal), forall N:nat,
                  exists (n : nat),
                    (n >= N)%nat /\
                    Rabs ((X n omega) - (X0 omega)) >= eps).
Proof.
   assert (eqq1:pre_event_equiv
                 (fun omega => exists (eps : posreal), forall N:nat,
                        exists (n : nat),
                          (n >= N)%nat /\
                          Rabs ((X n omega) - (X0 omega)) >= eps)
                 (fun omega => exists (eps : QArith_base.Q),
                      (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} eps) /\
                      forall N:nat,
                      exists (n : nat),
                        (n >= N)%nat /\
                        Rabs ((X n omega) - (X0 omega)) >= Q2R eps)).
  {
    intros x.
    split.
    - intros [eps HH].
      destruct (Q_dense 0 eps) as [q [ql qr]].
      + apply cond_pos.
      + exists q.
        split.
        * apply Qreals.Rlt_Qlt.
          unfold QArith_base.inject_Z.
          unfold Q2R.
          simpl.
          rewrite Rmult_0_l.
          apply ql.
        * intros N.
          destruct (HH N) as [n [Hn1 Hn2]].
          exists n.
          intuition lra.
    - intros [eps [epos HH]].
      assert (qepspos: 0 < Q2R eps).
      {
        apply Qreals.Qlt_Rlt in epos.
        now rewrite RMicromega.Q2R_0 in epos.
      }
      exists (mkposreal (Q2R eps) qepspos).
      intros N.
      destruct (HH N) as [n [Hn1 Hn2]].
      exists n. intuition lra.
  }
  rewrite eqq1.
  apply sa_countable_union_iso; try typeclasses eauto.
  intros.
  destruct (Rlt_dec 0 (Q2R i)).
  - assert (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
    {
      apply Qreals.Rlt_Qlt.
      now rewrite RMicromega.Q2R_0.
    }
    eapply (sa_proper _  (fun omega => (forall N : nat,
      exists n : nat,
        (n >= N)%nat /\ Rabs (X n omega - X0 omega) >= Q2R i))).
    + firstorder.
    + apply sa_pre_countable_inter; intros N.
      now apply (sa_sigma_not_convergent X X0 (mkposreal _ r)).
  - eapply sa_proper; try apply sa_none.
    assert (~ QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
    {
      intros qlt.
      apply Qreals.Qlt_Rlt in qlt.
      now rewrite RMicromega.Q2R_0 in qlt.
    }
    firstorder.
Qed.

  Lemma recip_pos (m : nat) : 0 < /(1 + INR m).
  Proof.
    apply Rinv_pos.
    generalize (pos_INR m). generalize (INR m) as x; intros.
    lra.
  Qed.

Lemma almost_convergent_iff (X : nat -> Ts -> R) X0
       {rv : forall n, RandomVariable dom borel_sa (X n)}
   {rv0 : RandomVariable dom borel_sa X0}:
   event_equiv ((exist (sa_sigma _) _ (sa_sigma_not_full_convergent X X0)))
               (union_of_collection
                  (fun m => inter_of_collection
                           (fun k => exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 (mkposreal (/(1 + INR m)) (recip_pos _)) k)))).
 Proof.
    simpl.
   intros omega. simpl.
   split; intros.
   + destruct H as [eps Heps].
     generalize (archimed_cor1 eps (cond_pos eps)); intros.
     destruct H as [N [HN1 HN2]].
     assert (/(1 + INR N) < eps).
     {
       eapply Rlt_trans; eauto.
       apply Rinv_lt_contravar; try lra.
       apply Rmult_lt_0_compat; try (now apply lt_0_INR).
       generalize (pos_INR N). generalize (INR N) as x; intros.
       lra.
     }
     exists N.
     intros n1.
     specialize (Heps n1).
     destruct Heps as [n0 [Hn1 Hn2]].
     exists n0.
     repeat split; try trivial.
     eapply Rge_trans; eauto.
     lra.
   + destruct H as [N HN].
     exists (mkposreal (/(1 + INR N)) (recip_pos _)).
     simpl. intros N0.
     specialize (HN N0).
     assumption.
 Qed.


Lemma almost_is_lim_seq_iff {prts : ProbSpace dom} (X : nat -> Ts -> R) X0
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
  {rv0 : RandomVariable dom borel_sa X0}:
  almost _ (fun omega => is_lim_seq (fun n => X n omega) (X0 omega)) <->
  (forall (eps:posreal),
      is_lim_seq (fun N =>
                    ps_P (exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 eps N))) 0).
Proof.
  assert (H1 : forall (eps: posreal),let E := fun n => exist (sa_sigma _) _
                                                     (sa_sigma_not_convergent X X0 eps n) in
                                is_lim_seq (fun k => ps_P (E k)) (ps_P (inter_of_collection E))).
  {
    intros eps E.
    apply is_lim_descending.
    intros n. repeat red. intros omega H.
    red in H. destruct H as [n0 [m0 H]].
    exists n0. repeat split; try lia; trivial.
  }
  split; intros.
  + rewrite almost_alt_eq in H.
    unfold almost_alt in H.
    destruct H as [E [HE Heps]].
    specialize (H1 eps). simpl in H1.
    enough (Hpsp : ps_P (
                    inter_of_collection(
                        fun n => (exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 eps n)))) = 0).
    - now rewrite <-Hpsp.
    - apply ps_P_sub_zero with E; trivial.
      intros omega.
      simpl; specialize (Heps omega).
      intros. apply Heps. push_neg.
      setoid_rewrite is_lim_seq_Reals.
      unfold Un_cv. push_neg. exists eps.
      split; try apply cond_pos.
      now unfold R_dist.
  + (* forall 0<δ, P(B_δ) = 0*)
    assert (Hinter : forall eps:posreal, let E :=
         fun n : nat => exist (sa_sigma _) _ (sa_sigma_not_convergent X X0 eps n) in
                                    (ps_P (inter_of_collection E)) = 0).
    {
      intros eps E.
      rewrite <-Rbar_finite_eq.
      rewrite <-(is_lim_seq_unique _ _ (H eps)). symmetry.
      apply is_lim_seq_unique. apply H1.
    }
    clear H.
    rewrite almost_alt_eq.
    unfold almost_alt.
    exists (exist (sa_sigma _) _ (sa_sigma_not_full_convergent X X0)).
    split.
    ++ rewrite almost_convergent_iff.
       rewrite <-ps_union_countable_union_iff.
       intros n; apply (Hinter ({| pos := /(1 + INR n); cond_pos := recip_pos n|})).
    ++ intros omega Hnot.
       simpl. setoid_rewrite is_lim_seq_Reals in Hnot.
       unfold Un_cv in Hnot. push_neg_in Hnot.
       destruct Hnot as [eps [Heps Hx]].
       now exists (mkposreal eps Heps).
Qed.

  Lemma conv_prob_sup_0_as {prts: ProbSpace dom} (f : nat -> Ts -> R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
      (forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_Rbar_gt (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) (const (pos eps)))) 0) ->
      almost prts (fun x => is_lim_seq (fun n => f n x) 0).
    Proof.
      intros.
      rewrite  almost_is_lim_seq_iff.
      intros.
      assert (0 < eps) by apply cond_pos.
      assert (0 < eps/2) by lra.
      specialize (H (mkposreal _ H1)).
      apply is_lim_seq_le_le with (u := fun n => 0)
                                  (w :=  (fun n : nat =>
         ps_P
           (event_Rbar_gt (fun x : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x)))
                          (const (pos (mkposreal _ H1)))))); trivial.
      - intros.
        split.
        + apply ps_pos.
        + apply ps_sub.
          rewrite <- union_coll_gt_sup.
          intros ? ?.
          simpl.
          simpl in H2.
          destruct H2 as [? [? ?]].
          exists (x0 - n)%nat.
          rewrite Rminus_0_r in H3.
          unfold rvabs.
          replace (n + (x0 - n))%nat with x0  by lia.
          lra.
        - apply is_lim_seq_const.
          Unshelve.
          + apply rv.
          + apply rvconst.
          + apply rv.
    Qed.

    Lemma conv_as_prob_sup_0 {prts: ProbSpace dom} (f : nat -> Ts -> R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
      almost prts (fun x => is_lim_seq (fun n => f n x) 0) ->
      (forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_Rbar_gt (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) (const (pos eps)))) 0).
   Proof.
     intros.
     rewrite almost_is_lim_seq_iff in H.
     intros.
     specialize (H eps).
     assert (RandomVariable dom borel_sa (fun _ : Ts => 0)) by apply rvconst.
     apply is_lim_seq_le_le with (u := fun n => 0)
                                 (w :=  (fun N : nat =>
         ps_P (ProbSpace := prts)
           (exist (sa_sigma dom)
                  (fun omega : Ts =>
                     exists n : nat, (n >= N)%nat /\ Rabs (f n omega - 0) >= eps)
                  (sa_sigma_not_convergent f (fun _ : Ts => 0) eps N)))).
     intros.
     - split.
       + apply ps_pos.
       + apply ps_sub.
         rewrite <- union_coll_gt_sup.
         intros ? ?.
         simpl.
         simpl in H1.
         destruct H1.
         exists (n + x0)%nat.
         split; try lia.
         unfold rvabs in H1.
         rewrite Rminus_0_r.
         lra.
    - apply is_lim_seq_const.
    - revert H.
      apply is_lim_seq_ext.
      intros.
      apply ps_proper.
      intros ?.
      simpl.
      reflexivity.
      Unshelve.
      + apply rv.
      + apply rvconst.
      + apply rv.
  Qed.

  Lemma lim_ps_sub_1_0 {prts: ProbSpace dom} (f : nat -> Ts -> R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
    forall (eps:posreal),
      is_lim_seq (fun n => ps_P (event_Rbar_le (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) (const (pos eps)))) 1 <->
      is_lim_seq (fun n => ps_P (event_Rbar_gt (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) (const (pos eps)))) 0.
    Proof.
      intros.
      split; intros.
      - apply is_lim_seq_ext with
         (u := (fun n : nat =>
                  1 - ps_P
                        (event_Rbar_le
                           (fun x : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x))) (const (pos eps))))).
        + intros.
          rewrite <- ps_complement.
          apply ps_proper.
          intros ?.
          simpl.
          unfold pre_event_complement.
          match_destr; simpl; lra.
        + apply is_lim_seq_minus with (l1 := 1) (l2 := 1); trivial.
          * apply is_lim_seq_const.
          * unfold is_Rbar_minus, is_Rbar_plus; simpl.
            f_equal.
            apply Rbar_finite_eq.
            lra. 
      - apply is_lim_seq_ext with
            (u := (fun n => 
                     1 - 
                     ps_P (event_Rbar_gt
                             (fun x : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x))) (const (pos eps))))).
        + intros.
          rewrite <- ps_complement.
          apply ps_proper.
          intros ?.
          simpl.
          unfold pre_event_complement.
          match_destr; simpl; lra.
        + apply is_lim_seq_minus with (l1 := 1) (l2 := 0); trivial.
          * apply is_lim_seq_const.
          * unfold is_Rbar_minus, is_Rbar_plus; simpl.
            f_equal.
            apply Rbar_finite_eq.
            lra. 
  Qed.

  Lemma conv_prob_sup_1_as {prts: ProbSpace dom} (f : nat -> Ts -> R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
      (forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_Rbar_le (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) (const (pos eps)))) 1) ->
      almost prts (fun x => is_lim_seq (fun n => f n x) 0).
   Proof.
     intros.
     apply conv_prob_sup_0_as with (rv3 := rv2); trivial.
     intros.
     now rewrite <- lim_ps_sub_1_0.
  Qed.

  Lemma conv_as_prob_sup_1  {prts: ProbSpace dom} (f : nat -> Ts -> R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
      almost prts (fun x => is_lim_seq (fun n => f n x) 0) ->
      forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_Rbar_le (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) (const (pos eps)))) 1.
    Proof.
      intros.
      rewrite lim_ps_sub_1_0; trivial.
      now apply  conv_as_prob_sup_0.
    Qed.

    Lemma nneg_expec_inf_sum {prts : ProbSpace dom} (f : nat -> Ts -> Rbar) 
          {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} 
          {nnf : forall n, Rbar_NonnegativeFunction (f n)} 
          {pofrf : Rbar_NonnegativeFunction
            (fun omega : Ts => ELim_seq (sum_Rbar_n (fun k : nat => f k omega)))} :
      ELim_seq (sum_Rbar_n (fun k => Rbar_NonnegExpectation (f k))) =
      Rbar_NonnegExpectation (fun omega => ELim_seq (sum_Rbar_n (fun k => f k omega))).
    Proof.
      assert (forall k, 
                 Rbar_NonnegativeFunction
                   (fun omega : Ts => sum_Rbar_n (fun j : nat => f j omega) k)).
      {
        unfold Rbar_NonnegativeFunction; intros.
        apply sum_Rbar_n_nneg_nneg; intros.
        apply nnf.
      }
      rewrite ELim_seq_ext with
          (v := (fun k => Rbar_NonnegExpectation 
                            (fun omega => sum_Rbar_n (fun j => f j omega) k))).
      rewrite monotone_convergence_Rbar_rvlim.
      - now unfold Rbar_rvlim.
      - intros.
        apply sum_Rbar_n_rv.
        intros.
        apply rv.
      - intros.
        unfold Rbar_rv_le.
        intros ?.
        apply sum_Rbar_n_pos_incr.
        intros.
        apply nnf.
      - intros.
        generalize Rbar_NonnegExpectation_sum; intros.
        now rewrite Rbar_NonnegExpectation_sum with (Xlim_pos := H).
   Qed.

    Lemma Injective_iso {A A' B} (f:A->B) {iso:Isomorphism A A'} :
      FinFun.Injective f -> FinFun.Injective (fun a' => f (iso_b a')).
    Proof.
      intros inj a1 a2 eqq.
      apply inj in eqq.
      apply (f_equal (iso_f (Isomorphism := iso))) in eqq.
      now repeat rewrite iso_f_b in eqq.
    Qed.

    Program Instance countable_iso {A B} {count:Countable A} {iso:Isomorphism A B} : Countable B
      := {| countable_index b := countable_index (iso_b b) |}.
    Next Obligation.
      apply Injective_iso.
      apply countable_index_inj.
    Qed.      

    Context {T:Type} {countableT:Countable T}.

    Instance countable_ivector {n:nat} : Countable (ivector T n).
    Proof.
      induction n; simpl.
      - apply unit_countable.
      - apply prod_countable; trivial.
    Qed.
    
    Instance countable_vector {n:nat} : Countable (vector T n).
    Proof.
      apply (@countable_iso (ivector T n)).
      - apply countable_ivector.
      - apply Isomorphism_symm.
        apply vec_to_ivec_encoder.
    Qed.

    Definition vec_pmf {n} (p0 : ProbSpace (discrete_sa T)) : (vector T n) -> R :=
      fun v =>
        vector_fold_left Rmult (vector_map ps_P (vector_map discrete_singleton v)) 1.

    Definition ivec_pmf {n} (p0 : ProbSpace (discrete_sa T)) : (ivector T n) -> R :=
      fun v =>
        ivector_fold_left Rmult (ivector_map ps_P (ivector_map discrete_singleton v)) 1.

    Lemma vec_to_ivec_pmf {n} (p0 : ProbSpace (discrete_sa T)) (v:vector T n) :
      vec_pmf p0 v = ivec_pmf p0 (iso_f (Isomorphism := vec_to_ivec_encoder) v).
    Proof.
      unfold vec_pmf, ivec_pmf, vector_fold_left.
      destruct v as [x []].
      generalize 1.
      now induction x; simpl in *.
    Qed.      
    
    Lemma vec_pmf_pos {n} (p0 : ProbSpace (discrete_sa T)):
      forall v,
        0 <= vec_pmf (n:=n) p0 v.
    Proof.
      intros.
      unfold vec_pmf, vector_fold_left, vector_map.
      destruct v; simpl.
      assert (forall (e:R), 
                 forall (l : list R),
                   0 <= e ->
                   (forall f, In f l -> 0<=f) ->
                   0 <= fold_left Rmult l e).
      {
        intros.
        revert H.
        revert e0.
        induction l.
        - intros.
          now simpl.
        - intros.
          simpl.
          apply IHl.
          + intros.
            apply H0.
            now apply in_cons.
          + apply Rmult_le_pos; trivial.
            apply H0.
            simpl.
            tauto.
      }
      apply H; try lra.
      intros.
      apply in_map_iff in H0.
      destruct H0 as [? [? ?]].
      rewrite <- H0.
      apply ps_pos.
    Qed.

    Lemma vec_pmf_sum1 {n} (p0 : ProbSpace (discrete_sa T)):
      countable_sum (vec_pmf (n:=n) p0) 1.
    Proof.
      Admitted.

    Program Definition vectorPMF {n} (p0 : ProbSpace (discrete_sa T)) : prob_mass_fun (vector T n) := {| pmf_pmf := vec_pmf p0 |}.
    Next Obligation.
      apply vec_pmf_pos.
    Qed.
    Next Obligation.    
      apply vec_pmf_sum1.
    Qed.

    Global Instance vector_discrete_ps {n} (p0 : ProbSpace (discrete_sa T)): ProbSpace (discrete_sa (vector T n)) := discrete_ps (vectorPMF p0).
    
    
End qlearn_aux.      


    
