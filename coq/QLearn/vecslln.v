Require Import QArith.Qreals.
Require Import Lra Lia Reals RealAdd RandomVariableL2 Coquelicot.Coquelicot.
Require Import Morphisms Finite List ListAdd Permutation infprod Almost NumberIso.
Require Import Sums SimpleExpectation PushNeg.
Require Import EquivDec.
Require Import Classical.
Require Import ClassicalChoice.
Require Import IndefiniteDescription ClassicalDescription.
Require Import BorelSigmaAlgebra.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import VectorConditionalExpectation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Import ListNotations.

Section vec_cauchy.

  Definition cauchy_seq_at {A : Type}(omega : A) (X : nat -> A -> R) := forall (eps:posreal),
    exists (N:nat), forall (n m : nat),  (n >= N)%nat -> (m >= N)%nat -> Rabs ((X n omega) - (X m omega)) < eps.

  Definition vec_cauchy_seq_at {A : Type} {size:nat} (omega : A) (X : nat -> A -> vector R size)
    := forall (eps:posreal),
      exists (N:nat), forall (n m : nat),  (n >= N)%nat -> (m >= N)%nat ->
                             hilbert.Hnorm (minus (X n omega) (X m omega)) < eps.

  Lemma nth_exist_join_aux {T} {size:nat} {P} (f:forall (i:nat) (pf:(i < size)%nat), exists (t:T), P i pf t) :
    forall bound, (bound <= size)%nat ->
             exists (ts:list T), length ts = bound /\ forall i pf d, (i < bound)%nat -> P i pf (nth i ts d).
  Proof.
    induction bound; simpl.
    - exists nil; simpl.
      split; trivial; lia.
    - intros bpf.
      destruct IHbound as [ts [tslen tspf]]; [lia |].
      destruct (f _ bpf) as [t tpf].
      exists (ts ++ [t]).
      split.
      + rewrite app_length; simpl; lia.
      + intros i pf d ipf.
        destruct (i == bound); unfold equiv, complement in *.
        * subst.
          rewrite app_nth2 by lia.
          rewrite Nat.sub_diag; simpl.
          replace pf with bpf; trivial.
          apply digit_pf_irrel.
        * rewrite app_nth1 by lia.
          apply tspf.
          lia.
  Qed.

  Lemma nth_exist_join {T} {size:nat} {P} (f:forall (i:nat) (pf:(i < size)%nat), exists (t:T), P i pf t) :
    exists (ts:list T), length ts = size /\ forall i pf d, P i pf (nth i ts d).
  Proof.
    destruct (nth_exist_join_aux f _ (le_refl _)) as [??]; firstorder.
  Qed.

  Lemma Hnorm_vector0 (x : vector R 0) : hilbert.Hnorm x = 0.
  Proof.
    destruct x.
    destruct x; simpl in *; [| lia].
    vm_compute.
    repeat match_destr.
    destruct a.
    symmetry in H0.
    apply Rsqr_eq_0 in H0.
    apply H0.
  Qed.

  Lemma In_le_list_sum (ts : list nat): forall i, In i ts -> (i <= list_sum ts)%nat.
  Proof.
    intros i Hi.
    induction ts.
    + simpl in Hi; lia.
    + simpl in Hi. destruct Hi.
      -- rewrite H. simpl; lia.
      -- specialize (IHts H). simpl; lia.
  Qed.


  Lemma vec_cauchy_seq_at_iff {A : Type} (n : nat) (omega : A) (X : nat -> A -> vector R n):
    vec_cauchy_seq_at omega X <->
    (forall (i:nat) (pf: (i < n)%nat), cauchy_seq_at omega (fun k a => vector_nth _ pf (X k a))).
  Proof.
    split; intros.
    + unfold vec_cauchy_seq_at in H.
      intros eps.
      specialize (H eps).
      destruct H as [N HN].
      exists N; intros n1 m1 Hn1 Hm1.
      specialize (HN n1 m1 Hn1 Hm1).
      generalize (Hnorm_nth1 _ eps i pf HN); intros HK.
      rewrite <-minus_nth in HK.
      apply HK.
    + destruct (n == 0%nat).
      {
        red in e; subst.
        red; intros.
        exists 0%nat; intros.
        rewrite Hnorm_vector0.
        apply cond_pos.
      } 
      unfold equiv, complement in c.
      intros eps.
      unfold cauchy_seq_at in H.
      assert (eps_div_pos:0 < (eps / INR n)).
      {
        apply Rdiv_lt_0_compat; try (apply cond_pos).
        apply lt_0_INR; lia.
      }
      destruct (nth_exist_join (fun i pf => H i pf (mkposreal _ eps_div_pos)))
        as [ts [Hsize tspfs]].
      exists (list_sum ts).
      intros n1 n2 n1big n2big.
      apply (@Nth_Hnorm n); [ lia | ].
      intros i pf.
      specialize (tspfs i pf 0%nat n1 n2).
      cut_to tspfs.
      * rewrite Rabs_minus_sym in tspfs.
        apply tspfs.
      * apply Nat.le_trans with (list_sum ts); auto.
        apply In_le_list_sum; apply nth_In.
        now rewrite Hsize.
      * apply Nat.le_trans with (list_sum ts); auto.
        apply In_le_list_sum; apply nth_In.
        now rewrite Hsize.
  Qed.

End vec_cauchy.

Section ash.
  Lemma ash_6_1_1_a {x : nat -> R}{a : nat -> nat -> R} (ha : forall j, is_lim_seq (fun n => (a n j)) 0)
        (hb1 : forall n, ex_series(fun j => Rabs(a n j)))
        (hb2 : exists c, forall n, Series (fun j => Rabs (a n j)) < c)
        (hx1 : bounded x) (hx2 : is_lim_seq x 0) :
    let y := fun n => Series (fun j => (a n j)*(x j)) in is_lim_seq y 0.
  Proof.
    intros y. destruct hx1 as [M HMx].
    destruct hb2 as [c Hc].
    assert (hy1 : forall n j, Rabs (a n j * x j) <= M*Rabs(a n j))
      by (intros ; rewrite Rabs_mult, Rmult_comm ;
          apply Rmult_le_compat_r; auto; apply Rabs_pos).
    assert (hy2 : forall n M, ex_series(fun j => M*Rabs(a n j)))
      by (intros; now apply (ex_series_scal_l) with (a0 := fun j => Rabs(a n j))).
    assert (hy3 : forall n, ex_series (fun j : nat => Rabs(a n j * x j))).
    {
      intros n.
      apply (ex_series_le (fun j => Rabs (a n j * x j)) (fun j => M*Rabs(a n j))); trivial.
      intros. rewrite Rabs_Rabsolu; auto.
    }
    assert (hy6 : forall n N, (0 < N)%nat -> Rabs(y n) <= sum_f_R0 (fun j => Rabs (a n j * x j)) (pred N)
                                                 + Series (fun j => Rabs (a n (N + j)%nat * x (N +j)%nat)))
      by (intros; unfold y; eapply Rle_trans; try (apply Series_Rabs; trivial);
          right; apply Series_incr_n with (a := fun j => Rabs ( a n j * x j)); trivial).
    rewrite is_lim_seq_Reals; unfold Un_cv, R_dist; simpl.
    intros eps Heps.
    setoid_rewrite Rminus_0_r.
    assert (Hcc : c > 0).
    {
      specialize (Hc 0%nat). eapply Rle_lt_trans; try (apply Hc).
      eapply Rle_trans; try (apply sum_f_R0_nonneg_le_Series; eauto).
      + apply sum_f_R0_Rabs_pos. Unshelve. exact 0%nat.
      + intros; apply Rabs_pos.
    }
    assert (hy7 : exists N, forall j, (j >= N)%nat -> Rabs(x j) < eps/(2*c)).
    {
      rewrite is_lim_seq_Reals in hx2.
      assert (Heps' : eps/(2*c) > 0).
      {
        apply Rlt_gt. apply RIneq.Rdiv_lt_0_compat;lra.
      }
      specialize (hx2 (eps/(2*c)) Heps'). unfold R_dist in hx2.
      setoid_rewrite Rminus_0_r in hx2. exact hx2.
    }
    assert (hy8 : forall N, is_lim_seq (fun n => sum_f_R0 (fun j => Rabs (a n j * x j)) N) 0).
    { intros N.
      apply (is_lim_seq_le_le (fun _ => 0) _ (fun n => M*sum_f_R0 (fun j => Rabs(a n j)) N)).
      - intros n.
        split ; try (apply sum_f_R0_Rabs_pos).
        rewrite <-sum_f_R0_mult_const.
        apply sum_f_R0_le; intros.
        rewrite Rmult_comm.
        rewrite Rabs_mult.
        apply Rmult_le_compat_r; auto; try (apply Rabs_pos).
      - apply is_lim_seq_const.
      - replace (0:Rbar) with (Rbar_mult M 0) by (apply Rbar_mult_0_r).
        apply is_lim_seq_scal_l.
        apply is_lim_seq_sum_f_R0; intros; auto.
        replace 0 with (Rabs 0) by (apply Rabs_R0).
        apply is_lim_seq_continuous; auto.
        rewrite continuity_pt_filterlim; apply (continuous_Rabs 0).
    }
    setoid_rewrite is_lim_seq_Reals in hy8.
    destruct hy7 as [N0 HN0].
    assert (Heps' : eps/2 > 0) by (apply RIneq.Rdiv_lt_0_compat;lra).
    specialize (hy8 (N0) (eps/2) Heps').
    unfold R_dist in hy8. setoid_rewrite Rminus_0_r in hy8.
    destruct hy8 as [N1 HN1].
    exists N1; intros. specialize (hy6 n (N0 + 1)%nat).
    eapply Rle_lt_trans; try (apply hy6).
    ** lia.
    ** replace (eps) with ((eps/2) + c*(eps/(2*c))) by (field;lra).
       apply Rplus_le_lt_compat.
    -- replace (Init.Nat.pred (N0 + 1)) with N0 by lia.
       eapply Rle_trans; try (apply Rle_abs); left; eauto.
    -- assert
         (hy7 : Series (fun j => Rabs (a n (N0 + 1 + j)%nat * x(N0 + 1 + j)%nat))
                <= Series(fun j => (eps/(2*c))*Rabs (a n (N0+1+j)%nat))).
       {
         apply Series_le; intros.
         + split; try (apply Rabs_pos).
           rewrite Rabs_mult, Rmult_comm.
           apply Rmult_le_compat_r; try(apply Rabs_pos).
           left. apply HN0; lia.
         + apply (ex_series_scal_l) with (c0 := eps/(2*c))(a0 := fun j => Rabs(a n (N0+1+j)%nat)).
           now rewrite <-(ex_series_incr_n) with (n0 := (N0 + 1)%nat)(a0:=fun j => Rabs (a n j)).
       }
       eapply Rle_lt_trans; eauto.
       rewrite Series_scal_l. rewrite Rmult_comm.
       apply Rmult_lt_compat_r; eauto; try(apply RIneq.Rdiv_lt_0_compat;lra).
       generalize (Series_shift_le (fun n0 => Rabs_pos _) (hb1 n) (N0 + 1)); intros.
       eapply Rle_lt_trans; eauto.
  Qed.

  Lemma ash_6_1_1_b {x : nat -> R}{a : nat -> nat -> R} (ha1 : forall j, is_lim_seq (fun n => (a n j)) 0)
        (hb1 : forall n, ex_series(fun j => Rabs(a n j)))
        (hb2 : exists c, forall n, Series (fun j => Rabs (a n j)) < c)
        (hx1 : bounded x) (x0 : R) (hx2 : is_lim_seq x x0)
        (ha2 : is_lim_seq (fun n => Series (fun j => a n j)) 1) :
    let y := fun n => Series (fun j => (a n j)*(x j)) in is_lim_seq y x0.
  Proof.
    intros y. unfold y.
    destruct hx1 as [M HM].
    assert (hy1 : forall n j, Rabs (a n j * x j) <= M*Rabs(a n j))
      by (intros ; rewrite Rabs_mult, Rmult_comm ;
          apply Rmult_le_compat_r; auto; apply Rabs_pos).
    assert (hy2 : forall n M, ex_series(fun j => M*Rabs(a n j)))
      by (intros; now apply (ex_series_scal_l) with (a0 := fun j => Rabs(a n j))).
    assert (hy3 : forall n, ex_series (fun j : nat => Rabs(a n j * x j))).
    {
      intros n.
      apply (ex_series_le (fun j => Rabs (a n j * x j)) (fun j => M*Rabs(a n j))); trivial.
      intros. rewrite Rabs_Rabsolu; auto.
    }
    assert (hxx : is_lim_seq (fun j => x j - x0) 0).
    {
      replace 0 with (x0 - x0) by lra.
      apply is_lim_seq_minus'; auto.
      apply is_lim_seq_const.
    }
    generalize (ash_6_1_1_a ha1 hb1 hb2 (is_lim_seq_bounded _ 0 hxx) hxx); intros.
    unfold y in H.
    setoid_rewrite Rmult_minus_distr_l in H.
    apply is_lim_seq_ext with (v := fun n => Series(fun j => a n j * x j) - Series(fun j => a n j * x0)) in H.
    + setoid_rewrite Series_scal_r in H.
      apply is_lim_seq_plus with (l := x0) (l1 := x0) (u := fun n => Series (a n)*x0) in H.
      -- setoid_rewrite Rplus_comm in H.
         setoid_rewrite Rplus_assoc in H.
         setoid_rewrite Rplus_opp_l in H.
         now setoid_rewrite Rplus_0_r in H.
      -- generalize (is_lim_seq_scal_r _ x0 _ ha2); intros.
         simpl in H0. now rewrite Rmult_1_l in H0.
      -- unfold is_Rbar_plus.
         simpl. f_equal. rewrite Rbar_finite_eq.
         lra.
    + intros n.
      apply Series_minus.
      ** now apply ex_series_Rabs.
      ** apply ex_series_scal_r. now apply ex_series_Rabs.
  Qed.

  (* Toeplitz lemma. *)
  Lemma ash_6_1_2  {a x : nat -> R} {x0 : R}(ha : forall n, 0 <= a n)
        (hb1 : forall n, 0 < sum_f_R0 a n)(hb2 : is_lim_seq (sum_f_R0 a) p_infty)  (hx : is_lim_seq x x0):
    is_lim_seq (fun n => (sum_f_R0 (fun j => a j * x j) n)/(sum_f_R0 a n)) x0.
  Proof.
    pose (A := fun (n j : nat) => if (le_dec j  n) then (a j)/(sum_f_R0 a n) else 0).
    assert (Apos: forall n j, 0 <= A n j).
    {
      intros.
      unfold A.
      match_destr; [|lra].
      unfold Rdiv.
      apply Rmult_le_pos; trivial.
      left.
      now apply Rinv_0_lt_compat.
    }
    assert (Aser: forall n, is_series (fun j => A n j) 1).
    {
      intros.
      unfold A.
      rewrite <-series_is_lim_seq.
      apply is_lim_seq_ext_loc with (u := fun n => 1); [|apply is_lim_seq_const].
      exists n.
      intros.
      rewrite <- sum_n_sum_f_clipped with (N := n); try lia.
      rewrite sum_n_Reals.
      unfold Rdiv.
      rewrite <- scal_sum.
      apply Rinv_l_sym.
      apply Rgt_not_eq.
      apply hb1.
    }
    apply is_lim_seq_ext with 
        (u := fun n => Series (fun j => (A n j) * x j)).
    - intros.
      unfold Series.
      unfold A.
      rewrite Lim_seq_ext_loc with
          (v := fun _ => sum_f_R0 (fun j : nat => a j * x j) n / sum_f_R0 a n).
      + now rewrite Lim_seq_const.
      + exists n; intros.
        rewrite sum_n_ext with
            (b := (fun j : nat => (if le_dec j n then (((a j)*(x j)) / sum_f_R0 a n) else 0))).
        * rewrite <- sum_n_sum_f_clipped with (N := n); try lia.
          rewrite sum_n_Reals.
          unfold Rdiv.
          rewrite <- scal_sum.
          now rewrite Rmult_comm at 1.
        * intros.
          match_destr; lra.
    - apply ash_6_1_1_b; trivial.
      + intros.
        unfold A.
        apply is_lim_seq_ext_loc with (u := fun n => a j / sum_f_R0 a n).
        * exists j.
          intros.
          match_destr; tauto.
        * apply is_lim_seq_div with (l1 := a j) (l2 := p_infty); trivial.
          -- apply is_lim_seq_const.
          -- discriminate.
          -- unfold is_Rbar_div; simpl.
             unfold is_Rbar_mult; simpl.
             now rewrite Rmult_0_r.
      + intros.
        apply ex_series_ext with (a0 := fun j => A n j).
        * intros.
          rewrite Rabs_right; trivial.
          specialize (Apos n n0); lra.
        * now exists 1.
                + exists 2.
                  intros.
                  specialize (Aser n).
                  apply is_series_unique in Aser.
                  rewrite Series_ext with (b := (fun j => A n j)); [rewrite Aser;lra|].
                  intros.
                  rewrite Rabs_right; trivial.
                  specialize (Apos n n0); lra.
                + now apply is_lim_seq_bounded with (c := x0).
                + apply is_lim_seq_ext with ( u := fun n => 1); [|apply is_lim_seq_const].
                  intros.
                  specialize (Aser n).
                  apply is_series_unique in Aser; now symmetry.
  Qed.

  (* Kronecker Lemma *)
  Lemma ash_6_1_3 {b x : nat -> R} (hb0: b (0%nat) = 0) (hb1 : forall n, 0 < b (S n) <= b (S (S n))) (hb2 : is_lim_seq b p_infty)
        (hx : ex_series x):
    is_lim_seq (fun n => (sum_f_R0 (fun j => b j * x j) (S n))/(b (S n))) 0.
  Proof.
    pose (s := sum_f_R0 x).
    assert (forall n, sum_f_R0 (fun j => b j * x j) (S n) = 
                      (b (S n))*(s (S n)) - sum_f_R0 (fun j => (s j) * ((b (S j)) - (b j))) n).
    {
      intros.
      induction n.
      - unfold s; simpl.
        ring_simplify; lra.
      - replace (S (S n)) with (S (n+1)) by lia.
        simpl.
        replace (n+1)%nat with (S n) by lia.
        rewrite IHn.
        apply Rplus_eq_reg_r with (r := sum_f_R0 (fun j : nat => s j * (b (S j) - b j)) n).
        ring_simplify.
        apply Rplus_eq_reg_r with (r := - (b (S n) * s (S n))).
        ring_simplify.
        unfold s.
        replace (S n) with (n+1)%nat by lia.
        simpl.
        now ring_simplify.
    }
    assert (forall n, b (S n) <> 0).
    {
      intros.
      apply Rgt_not_eq.
      apply hb1.
    }
    assert (forall n,
               (s (S n)) - (sum_f_R0 (fun j : nat => s j * (b (S j) - b j)) n)/(b (S n)) = 
               (sum_f_R0 (fun j : nat => b j * x j) (S n))/(b (S n))).

    {
      intros.
      symmetry.
      unfold Rdiv.
      replace (s (S n)) with ((b (S n) * s (S n)) * / b (S n)).
      - rewrite <- Rmult_minus_distr_r.
        now apply Rmult_eq_compat_r.
      - now field_simplify.
    }
    assert (bser: forall n, b (S n) - b (0%nat) = sum_f_R0 (fun j : nat => b (S j) - b j) n).
    {
      induction n.
      - now simpl.
      - simpl.
        rewrite <- IHn.
        lra.
    }
    destruct hx.
    apply (is_lim_seq_ext _ _ _ H1).
    rewrite <- series_is_lim_seq in H2.
    apply is_lim_seq_ext with (v := s) in H2.
    - apply is_lim_seq_minus with (l1 := x0) (l2 := x0).
      + now rewrite is_lim_seq_incr_1 in H2.
      + generalize (@ash_6_1_2 (fun j => b (S j) - b j) s x0); intros.
        cut_to H3; trivial.
        * eapply (is_lim_seq_ext _ _ x0 _ H3).
        * intros.
          destruct (lt_dec 0 n).
          -- specialize (hb1 (n-1)%nat).
             replace (S (n-1)) with (n) in hb1 by lia.
             lra.
          -- assert (n = 0%nat) by lia.
             rewrite H4.
             rewrite hb0.
             rewrite Rminus_0_r.
             left; apply hb1.
        * intros.
          induction n.
          -- simpl.
             specialize (hb1 0%nat).
             lra.
          -- rewrite sum_f_R0_peel.
             eapply Rlt_le_trans.
             ++ apply IHn.
             ++ assert (b (S (S n)) - b (S n) >= 0).
                ** specialize (hb1 n); lra.
                ** lra.
        * apply (is_lim_seq_ext _ _ _ bser).
          apply is_lim_seq_minus with (l1 := p_infty) (l2 := b (0%nat)).
          -- now apply is_lim_seq_incr_1 in hb2.
          -- apply is_lim_seq_const.
          -- red; simpl.
             now red; simpl.
      + red; simpl.
        red; simpl.
        now rewrite Rplus_opp_r.
    - unfold s.
      intros.
      now rewrite sum_n_Reals.
      Unshelve.
      intros.
      simpl.
      specialize (bser n).
      rewrite <- bser.
      rewrite hb0.
      rewrite Rminus_0_r.
      f_equal.
      apply sum_f_R0_ext.
      intros.
      now rewrite Rmult_comm.
  Qed.

  Lemma sum_n_zeroval (f : nat -> R)  (n:nat) :
    f 0%nat = 0 ->
    sum_n_m f 0%nat n = sum_n_m f 1%nat n.
  Proof.
    intros.
    induction n.
    - rewrite sum_n_n.
      rewrite H.
      rewrite sum_n_m_zero; try lia.
      reflexivity.
    - rewrite sum_n_Sm; try lia.
      rewrite sum_n_Sm; try lia.
      unfold plus; simpl.
      now rewrite IHn.
  Qed.

  Lemma ash_6_1_3_strong1 {b x : nat -> R} (hb1 : forall n, 0 < b n <= b (S n)) (hb2 : is_lim_seq b p_infty)
        (hx : ex_series x):
    is_lim_seq (fun n => (sum_n_m (fun j => b j * x j) 1 n)/(b n)) 0.
  Proof.
    pose (bb  := fun n => if (lt_dec 0 n) then (b n) else 0).
    generalize (@ash_6_1_3 bb x); intros.
    cut_to H; trivial.
    - apply is_lim_seq_ext with (v := fun n => sum_n_m (fun j => b j * x j) 1 (S n) / (b (S n))) in H.
      + apply is_lim_seq_incr_1.
        apply H.
      + intros.
        rewrite <- sum_n_Reals.
        unfold sum_n.
        replace (bb (S n)) with (b (S n)).
        * f_equal.
          rewrite sum_n_zeroval.
          -- rewrite sum_n_m_ext_loc with (b0 :=  (fun j : nat => b j * x j)); [easy | ].
             intros.
             unfold bb.
             match_destr.
             lia.
          -- unfold bb.
             simpl.
             lra.
        * unfold bb.
          match_destr.
          lia.
    - unfold bb.
      now simpl.
    - unfold bb.
      apply is_lim_seq_incr_1.
      apply is_lim_seq_ext with (u := (fun n => b (S n))).
      + intros.
        match_destr.
        lia.
      + now apply is_lim_seq_incr_1 in hb2.
  Qed.

  Lemma ash_6_1_3_strong {b x : nat -> R} (hb1 : forall n, 0 < b n <= b (S n)) (hb2 : is_lim_seq b p_infty)
        (hx : ex_series x):
    is_lim_seq (fun n => (sum_n (fun j => b j * x j) n)/(b n)) 0.
  Proof.
    apply is_lim_seq_incr_1.
    apply is_lim_seq_ext with (u := fun n => ((b 0%nat)*(x 0%nat) + sum_n_m (fun j : nat => b j * x j) 1 (S n))/(b (S n))).
    - intros.
      f_equal.
    - apply is_lim_seq_ext with (u := fun n => (b 0%nat)*(x 0%nat)/(b (S n)) + (sum_n_m (fun j : nat => b j * x j) 1 (S n))/(b (S n))).
      + intros.
        field.
        apply Rgt_not_eq.
        apply (hb1 (S n)).
      + apply is_lim_seq_plus with (l1 := 0) (l2 := 0).
        * unfold Rdiv.
          replace (Rbar.Finite 0) with (Rbar_mult (Rmult (b 0%nat) (x 0%nat)) 0).
          -- apply is_lim_seq_scal_l.
             replace (Rbar.Finite 0) with (Rbar_inv p_infty).
             ++ apply is_lim_seq_inv.
                ** now apply is_lim_seq_incr_1 in hb2.
                ** discriminate.
             ++ now simpl.
          -- now rewrite Rbar_mult_0_r.
        * generalize (ash_6_1_3_strong1 hb1 hb2 hx); intros.
          now apply is_lim_seq_incr_1 in H.
        * red; simpl.
          f_equal.
          now rewrite Rplus_0_r.
  Qed.

  Context {Ts:Type} {dom: SigmaAlgebra Ts}{Prts: ProbSpace dom}.

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
  Defined.

  Global Instance frfite (X Y : Ts -> R){p : Prop}(dec : {p} + {~ p})
         {rv_X : FiniteRangeFunction X} {rv_Y : FiniteRangeFunction Y} :
    FiniteRangeFunction (if dec then X else Y).
  Proof.
    match_destr.
  Qed.

  Definition rvmaxlist (X : nat -> Ts -> R) (N : nat) : Ts -> R :=
    fun (omega : Ts) => Rmax_list (List.map (fun n => X n omega) (List.seq 0 (S N))).

  Lemma rvmaxlist_monotone (X : nat -> Ts -> R) :
    forall n omega, rvmaxlist X n omega <= rvmaxlist X (S n) omega.
  Proof.
    intros n omega.
    unfold rvmaxlist.
    assert (seq 0 (S (S n)) = seq 0 (S n) ++ [S n]).
    {
      generalize (S n); intros n0.
      rewrite seq_S.
      f_equal.
    }
    rewrite H.
    rewrite Rmax_list_app.
    + apply Rmax_l.
    + apply seq_not_nil; lia.
  Qed.


  Global Instance frfrvmaxlist (X : nat -> Ts -> R)
         {rv : forall n, FiniteRangeFunction (X n)} (N : nat):
    FiniteRangeFunction (rvmaxlist X N).
  Proof.
    unfold rvmaxlist.
    generalize (0%nat).
    induction N; simpl; intros s.
    - apply rv.
    - assert (frf:FiniteRangeFunction (fun omega => Rmax (X s omega) (Rmax_list (map (fun n : nat => X n omega) (seq (S s) (S N)))))).
      {
        apply frfmax; auto.
      }
      destruct N.
      + simpl; auto.
      + eapply FiniteRangeFunction_ext; try eapply frf.
        intros ?.
        reflexivity.
  Qed.

  Global Instance rvmaxlist_rv (X : nat -> Ts -> R)
         {rv : forall n, RandomVariable dom borel_sa (X n)} (N : nat):
    RandomVariable dom borel_sa (rvmaxlist X N).
  Proof.
    unfold rvmaxlist.
    generalize (0%nat).
    induction N; simpl; intros s.
    - apply rv.
    - assert (frf:RandomVariable dom borel_sa (fun omega => Rmax (X s omega) (Rmax_list (map (fun n : nat => X n omega) (seq (S s) (S N)))))).
      {
        apply rvmax_rv; auto.
      }
      destruct N.
      + simpl; auto.
      + eapply RandomVariable_proper; try reflexivity; try eapply frf.
        intros ?.
        reflexivity.
  Qed.

  Fixpoint vec_filtration_history {size:nat} (n : nat) (X : nat -> Ts -> vector R size)
           {frf : forall n, FiniteRangeFunction (X n)}
           {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
    : list dec_sa_event :=
    match n with
    | 0%nat => [dsa_Ω]
    | S k => refine_dec_sa_partitions (vec_induced_sigma_generators (frf k)) (vec_filtration_history k X)
    end.

  Lemma rvmult_zero (f : Ts -> R) :
    rv_eq (rvmult f (const 0)) (const 0).
  Proof.
    intro x.
    unfold rvmult, const.
    lra.
  Qed.

  Lemma vec_part_list_history {size:nat} (n : nat) (X : nat -> Ts -> vector R size)
        {frf : forall n, FiniteRangeFunction (X n)}
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)} :
    is_partition_list (map dsa_event (vec_filtration_history n X)).
  Proof.
    induction n.
    - simpl.
      unfold is_partition_list.
      split.
      + apply FOP_cons.
        * apply Forall_nil.
        * apply FOP_nil.
      + apply list_union_singleton.
    - simpl.
      apply is_partition_refine.
      + apply is_partition_vec_induced_gen.
      + apply IHn.
  Qed.

  Lemma vec_part_meas_induced {size:nat} (f : Ts -> vector R size) 
        {frf : FiniteRangeFunction f}
        {rv : RandomVariable dom (Rvector_borel_sa size) f} :
    partition_measurable (cod:=Rvector_borel_sa size) f 
                         (map dsa_event (vec_induced_sigma_generators frf)).
  Proof.
    unfold partition_measurable, vec_induced_sigma_generators.
    intros.
    rewrite in_map_iff in H0.  
    destruct H0 as [? [? ?]].
    rewrite in_map_iff in H1.
    destruct H1 as [? [? ?]].
    rewrite <- H1 in H0; simpl in H0.
    destruct frf.
    exists x0.
    rewrite H0.
    easy.
  Qed.

  Global Instance vec_partition_measurable_perm {size:nat} (f : Ts -> vector R size)
         {frf : FiniteRangeFunction f}
         {rvf : RandomVariable dom (Rvector_borel_sa size) f} :
    Proper (@Permutation _ ==> iff) (partition_measurable (cod:=Rvector_borel_sa size) f).
  Proof.
    cut (Proper (Permutation (A:=event dom) ==> impl) (partition_measurable  (cod:=Rvector_borel_sa size) f)).
    {
      unfold Proper, respectful, impl; intros HH x y perm.
      split; intros.
      - eauto.
      - symmetry in perm.
        eauto.
    }
    unfold partition_measurable.
    unfold Proper, respectful, impl; intros x y perm HH isp e ein.
    rewrite <- perm in isp.
    rewrite <- perm in ein.
    now apply HH.
  Qed.

  Instance vec_partition_measurable_event_equiv {size:nat} (f : Ts -> vector R size)
           {frf : FiniteRangeFunction f}
           {rvf : RandomVariable dom (Rvector_borel_sa size) f} :
    Proper (Forall2 event_equiv ==> iff) (partition_measurable (cod:=Rvector_borel_sa size) f).
  Proof.
    cut (Proper (Forall2 event_equiv ==> impl) (partition_measurable (cod:=Rvector_borel_sa size) f)).
    {
      unfold Proper, respectful, impl; intros HH x y perm.
      split; intros.
      - eauto.
      - symmetry in perm.
        eauto.
    }
    unfold partition_measurable, impl.
    intros x y F2 HH isp p inp.
    rewrite <- F2 in isp.
    destruct (Forall2_In_r F2 inp) as [p' [??]].
    destruct (HH isp p') as [c csub]; trivial.
    exists c.
    now rewrite <- H0.
  Qed.  

  Lemma vec_part_meas_refine_commute {size:nat}
        (f : Ts -> vector R size) 
        (l1 l2 : list dec_sa_event)
        {frf : FiniteRangeFunction f}
        {rvf : RandomVariable dom (Rvector_borel_sa size) f} :
    partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event
                                                             (refine_dec_sa_partitions l1 l2)) <->
    partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event
                                                             (refine_dec_sa_partitions l2 l1)).
  Proof.
    destruct (refine_dec_sa_partitions_symm l1 l2) as [l' [perm F2]].
    transitivity (partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event l')).
    - apply vec_partition_measurable_perm.
      now apply Permutation_map.
    - apply vec_partition_measurable_event_equiv.
      apply Forall2_map_f.
      apply F2.
  Qed.
  
  Lemma vec_part_meas_refine_l {size:nat} (f : Ts -> vector R size) 
        (l1 l2 : list dec_sa_event)
        {frf : FiniteRangeFunction f}
        {rvf : RandomVariable dom (Rvector_borel_sa size) f} :
    (is_partition_list (map dsa_event l1)) ->
    (is_partition_list (map dsa_event l2)) ->  
    (partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event l1)) ->
    partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event
                                                             (refine_dec_sa_partitions l1 l2)).
  Proof.
    intros ispartl1 ispartl2; intros.
    unfold partition_measurable, refine_dec_sa_partitions.
    intros.
    rewrite in_map_iff in H1.
    destruct H1 as [? [? ?]].
    rewrite flat_map_concat_map in H2.
    rewrite concat_In in H2.
    destruct H2 as [? [? ?]].
    rewrite in_map_iff in H2.
    destruct H2 as [? [? ?]].
    unfold partition_measurable in H.    
    destruct frf.
    rewrite <- H2 in H3.
    cut_to H; trivial.
    specialize (H (dsa_event x1)).
    cut_to H.
    - destruct H as [? ?].
      exists x2.
      unfold refine_dec_sa_event in H3.
      rewrite in_map_iff in H3.
      destruct H3 as [? [? ?]].
      rewrite <- H1.
      transitivity (dsa_event x1); trivial.
      rewrite <- H3.
      simpl.
      apply Event.event_inter_sub_l.
    - now apply in_map.
  Qed.

  Lemma vec_part_meas_refine {size:nat} (f : Ts -> vector R size) 
        (l1 l2 : list dec_sa_event)
        {frf : FiniteRangeFunction f}
        {rvf : RandomVariable dom (Rvector_borel_sa size) f} :
    (is_partition_list (map dsa_event l1)) ->
    (is_partition_list (map dsa_event l2)) ->  
    (partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event l1)) \/ 
    (partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event l2)) ->  
    partition_measurable (cod:=Rvector_borel_sa size) f (map dsa_event
                                                             (refine_dec_sa_partitions l1 l2)).
  Proof.
    intros.
    destruct H1.
    - now apply vec_part_meas_refine_l.
    - rewrite vec_part_meas_refine_commute.
      now apply vec_part_meas_refine_l.
  Qed.

  Lemma vec_induced_gen_ispart {size:nat}
        {rv_X : Ts -> vector R size}
        {rv:RandomVariable dom (Rvector_borel_sa size) rv_X}
        (frf : FiniteRangeFunction rv_X) :
    is_partition_list (map dsa_event (vec_induced_sigma_generators frf)).
  Proof. 
    unfold is_partition_list.
    unfold vec_induced_sigma_generators, event_preimage, event_singleton.
    rewrite map_map; simpl.
    split.
    - apply event_disjoint_preimage_disj.
      apply NoDup_nodup.
    - destruct frf.
      unfold RandomVariable.frf_vals.
      unfold event_equiv; intros.
      unfold list_union.
      split.
      + intros.
        now unfold Ω, pre_Ω; simpl.
      + intros.
        eexists.
        split.
        * rewrite in_map_iff.
          exists (rv_X x).
          split; try easy.
          now rewrite nodup_In.
        * now simpl.
  Qed.

  Lemma vec_part_meas_hist {size:nat} (j k : nat) (X : nat -> Ts -> vector R size)
        {frf : forall n, FiniteRangeFunction (X n)}
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)} :
    partition_measurable (cod:=Rvector_borel_sa size) (X j) (map dsa_event (vec_filtration_history ((S j) + k)%nat X)).
  Proof.
    induction k.
    - replace (S j + 0)%nat with (S j) by lia.
      simpl.
      apply vec_part_meas_refine.
      + apply vec_induced_gen_ispart.
      + apply vec_part_list_history.
      + left.
        apply vec_part_meas_induced.
    - replace (S j + S k)%nat with (S (S j + k))%nat by lia.
      simpl.
      apply vec_part_meas_refine.
      + apply vec_induced_gen_ispart.
      + apply is_partition_refine.
        * apply vec_induced_gen_ispart.
        * apply vec_part_list_history.
      + right.
        apply IHk.
  Qed.

Lemma vec_expec_cross_zero {size:nat} (X : nat -> Ts -> vector R size)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)}
        {isfe_in : forall (j k:nat), IsFiniteExpectation Prts (rvinner (X j) (X k))}
        {isfe_mult : forall (j k:nat), vector_IsFiniteExpectation Prts (vecrvmult (X j) (X k))}
        {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}   
        (HC : forall (n:nat), 
          almostR2 Prts eq
              (vector_FiniteConditionalExpectation 
                 Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
              (const Rvector_zero)) :
    forall (j k : nat), 
      (j < k)%nat ->
      FiniteExpectation Prts (rvinner (X j) (X k)) = 0.
  Proof.
    intros j k jltk.
    destruct k; try lia.
    generalize (vector_FiniteCondexp_factor_out_inner_zero_swapped); intros.
    specialize (H Prts _ (filtration_history_sa_sub (cod := Rvector_borel_sa size) X k)).
    specialize (H size (X (S k)) (X j) _ _).
    cut_to H.
    - rewrite <- (H _ _).
      + apply FiniteExpectation_ext.
        reflexivity.
      + apply HC.
    - apply filtration_history_sa_le_rv; lia.
  Qed.

  Lemma SimpleExpectation_rvsum {n}  
        (X : nat -> Ts -> R)
        {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
        {frf : forall (n:nat), FiniteRangeFunction (X n)} :
    SimpleExpectation (rvsum X n) =
    sum_n (fun m => SimpleExpectation (X m)) n.
  Proof.
    induction n.
    - rewrite sum_O.
      assert (rv_eq (rvsum X 0%nat) (X 0%nat)).
      {
        unfold rvsum.
        intro x.
        now rewrite sum_O.
      }
      now erewrite SimpleExpectation_ext; [|apply H].
    - replace (SimpleExpectation (rvsum X (S n))) with
          (SimpleExpectation (rvplus (rvsum X n) (X (S n)))).
      + rewrite <- sumSimpleExpectation.
        rewrite IHn.
        rewrite sum_Sn.
        now unfold plus; simpl.
      + apply SimpleExpectation_ext.
        intro x.
        unfold rvplus, rvsum.
        now rewrite sum_Sn.
  Qed.

  Lemma vec_expec_cross_zero_sum_shift {size:nat} (X : nat -> Ts -> vector R size) (m:nat)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)}
        {isfe_in : forall (j k:nat), IsFiniteExpectation Prts (rvinner (X j) (X k))}
        {isfe_mult : forall (j k:nat), vector_IsFiniteExpectation Prts (vecrvmult (X j) (X k))}
        {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
        (HC : forall (n:nat), 
          almostR2 Prts eq
              (vector_FiniteConditionalExpectation 
                 Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
              (const Rvector_zero)) :
    forall (j k : nat), 
      (j < k)%nat ->
      FiniteExpectation Prts (rvsum (fun n => rvinner (X (n+m)%nat) (X (k+m)%nat)) j) = 0.
  Proof.
    intros.
    rewrite <- sum_expectation.
    rewrite sum_n_ext_loc with (b := fun _ => 0).
    - rewrite sum_n_const.
      lra.
    - intros.
      apply vec_expec_cross_zero with (rv0 := rv) (isfe0 := isfe) ; trivial.
      lia.
  Qed.

  Definition rvsumvec {size:nat} (Xn : nat -> Ts -> vector R size) (n : nat) : Ts -> vector R size
    := fun ts => sum_n (fun n => Xn n ts) n.

  Lemma vec_rvsum_distr_r {size:nat} {n} (X : nat -> Ts -> vector R size) (f : Ts -> vector R size) :
    rv_eq (rvsum (fun j => rvinner (X j) f) n) (rvinner (rvsumvec X n) f).
  Proof.
    intros ?.
    unfold rvsum, rvinner, rvsumvec.
    induction n; simpl.
    - now repeat rewrite sum_O.
    - repeat rewrite sum_Sn.
      rewrite IHn.
      unfold plus; simpl.
      now rewrite Rvector_inner_plus.
  Qed.
  
  Global Instance rvsumvec_rv {n} (f : nat -> Ts -> vector R n) (m:nat)
         {rv:forall k, (k <= m)%nat -> RandomVariable dom (Rvector_borel_sa n) (f k)} :
    RandomVariable dom (Rvector_borel_sa n) (rvsumvec f m).
  Proof.
    unfold rvsumvec.
    induction m.
    - apply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _) (f 0%nat)).
      + intro x.
        now rewrite sum_O.
      + apply rv; lia.
    - apply (RandomVariable_proper _ _ (reflexivity _) _ _ (reflexivity _) (fun ts : Ts => plus (sum_n (fun n : nat => f n ts) m) (f (S m) ts))).
      + intro x.
        now rewrite sum_Sn.
      + apply Rvector_plus_rv.
        * apply IHm.
          intros.
          apply rv; lia.
        * apply rv; lia.
  Qed.

  Global Instance rvsumvec_frf {n} (f : nat -> Ts -> vector R n) (m:nat)
         {rv:forall k, FiniteRangeFunction (f k)} :
    FiniteRangeFunction (rvsumvec f m).
  Proof.
    unfold rvsumvec.
    induction m.
    - eapply FiniteRangeFunction_ext; try eapply (rv 0%nat).
      intros ?.
      now rewrite sum_O; simpl.
    - destruct IHm as [l1 pf1].
      destruct (rv (S m)) as [l2 pf2].
      exists (map (fun '(x,y) => plus x y) (list_prod l1 l2)).
      intros.
      rewrite sum_Sn.
      change (In ((fun '(x0, y) => plus x0 y) ((sum_n (fun n0 : nat => f n0 x) m), (f (S m) x)))
                 (map (fun '(x0, y) => plus x0 y) (list_prod l1 l2))).
      apply in_map.
      apply in_prod_iff.
      split; trivial.
  Qed.

  Lemma vec_expec_cross_zero_sum2_shift {size:nat} (X : nat -> Ts -> vector R size) (m : nat)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)}
        {isfe_in : forall (j k:nat), IsFiniteExpectation Prts (rvinner (X j) (X k))}
        {isfe_mult : forall (j k:nat), vector_IsFiniteExpectation Prts (vecrvmult (X j) (X k))}
        {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
        {isfe_sum : forall (j k : nat),
            IsFiniteExpectation 
              Prts
              (rvinner (rvsumvec (fun n : nat => X (n + m)%nat) j) (X (k + m)%nat))}
        (HC : forall (n:nat), 
          almostR2 Prts eq
              (vector_FiniteConditionalExpectation 
                 Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
              (const Rvector_zero)) :
    forall (j k : nat), 
      (j < k)%nat -> 
      FiniteExpectation Prts (rvinner (rvsumvec (fun n => X (n + m)%nat) j) (X (k+m)%nat)) = 0.
  Proof.
    intros.
    generalize (vec_expec_cross_zero_sum_shift X m HC j k H); intros.
    rewrite <- H0.
    apply FiniteExpectation_ext.
    symmetry.
    apply vec_rvsum_distr_r.
  Qed.

  (* Few properties about cutoff sequences. Move to RealAdd. *)
  Fixpoint vec_cutoff_eps {size:nat} (n : nat) (eps : R) (X : nat -> vector R size) :=
    match n with
    | 0%nat => X 0%nat
    | S k => if (Rlt_dec (Rmax_list_map (seq 0 (S k)) (fun n => hilbert.Hnorm(X n))) eps) then X (S k)
             else (vec_cutoff_eps k eps X)
    end.

  Lemma vec_cutoff_eps_lt_eps {size:nat} eps n (X : nat -> vector R size) :
    (forall k, (k <= n)%nat -> hilbert.Hnorm (X k) < eps) -> (vec_cutoff_eps n eps X = X n).
  Proof.
    intros H.
    induction n.
    + now simpl.
    + simpl.
      match_destr.
      assert (H1 : Rmax_list_map (seq 0 (S n)) (fun n => hilbert.Hnorm(X n)) < eps).
      {
        unfold Rmax_list_map.
        rewrite Rmax_list_lt_iff; try (apply map_not_nil; apply seq_not_nil; lia).
        intros.
        rewrite in_map_iff in H0.
        destruct H0 as [x0 [Hx0 Hx1]].
        subst; auto. apply H.
        rewrite in_seq in Hx1. destruct Hx1.
        intuition.
      }
      exfalso; firstorder.
  Qed.

  Lemma vec_cutoff_eps_ge_eps {size:nat} eps (X : nat -> vector R size) :
    (forall k:nat, eps <= hilbert.Hnorm(X k)) -> (forall n, vec_cutoff_eps n eps X = X 0%nat).
  Proof.
    intros H n.
    simpl.
    induction n.
    ++ now simpl in H.
    ++ simpl. match_destr.
       assert (hilbert.Hnorm(X n) <= Rmax_list_map (0%nat :: seq 1 n) 
                                                   (fun n => hilbert.Hnorm(X n))).
       {
         unfold Rmax_list_map.
         apply Rmax_spec.
         rewrite in_map_iff.
         exists n; split; trivial.
         replace (0%nat :: seq 1 (n)) with (seq 0%nat (S n)) by (now simpl).
         rewrite in_seq; lia.
       }
       specialize (H n).
       lra.
  Qed.

  Lemma ne_le_succ {k n : nat} (hk1 : k <> S n) (hk2 : (k <= S n)%nat) : (k <= n)%nat.
  Proof.
    lia.
  Qed.

  Lemma vec_cutoff_ge_eps_exists {size:nat} (n : nat) (eps : R) ( X : nat -> vector R size ):
    (eps <= hilbert.Hnorm(vec_cutoff_eps n eps X)) -> 
    exists k, (k <= n)%nat /\ eps <= hilbert.Hnorm(X k).
  Proof.
    intros Hn.
    induction n.
    -- simpl in Hn. exists 0%nat.
       split; trivial.
    -- simpl in Hn.
       match_destr_in Hn.
       ++  exists (S n). split; trivial; lra.
       ++ apply Rnot_lt_ge in n0.
          specialize (IHn Hn).
          destruct IHn as [k Hk].
          exists k. destruct Hk. split; trivial.
          etransitivity; eauto; lia.
  Qed.

  Lemma vec_cutoff_ge_eps_exists_contrapose {size:nat} (n : nat) (eps : R) (X : nat -> vector R size):
    (hilbert.Hnorm(vec_cutoff_eps n eps X) < eps) -> 
    (forall k, (k <= n)%nat -> hilbert.Hnorm(X k) < eps).
  Proof.
    intros Heps.
    induction n.
    + simpl in Heps. intros.
      assert (k = 0%nat) by lia; subst; trivial.
    + simpl in Heps.
      match_destr_in Heps.
      ++ intros. destruct (k == S n).
      -- now rewrite e.
      -- apply IHn; try(apply ne_le_succ; eauto).
         unfold Rmax_list_map in r.
         replace (0%nat :: seq 1 n) with (seq 0%nat (S n)) in r by (now simpl).
         rewrite Rmax_list_lt_iff in r; try (apply map_not_nil; apply seq_not_nil; lia).
         rewrite vec_cutoff_eps_lt_eps; intros; try (apply r; rewrite in_map_iff).
         ** exists n; split; trivial. rewrite in_seq; lia.
         ** exists k0; split; trivial. rewrite in_seq; lia.
         ++ intros. specialize (IHn Heps).
            apply Rnot_lt_ge in n0.
            replace (0%nat :: seq 1 n) with (seq 0%nat (S n)) in n0 by (now simpl).
            unfold Rmax_list_map in n0.
            assert ((0 < S n)%nat) by lia.
            apply Rge_le in n0.
            rewrite (Rmax_list_map_seq_ge eps (fun n => hilbert.Hnorm (X n)) H0) in n0.
            destruct n0 as [k1 [Hk1 Heps1]].
            assert (k1 <= n)%nat by lia.
            specialize (IHn k1 H1).
            exfalso; lra.
  Qed.

  Lemma vec_cutoff_ge_eps_exists_iff {size:nat} (n : nat) (eps : R) (X : nat -> vector R size):
    (eps <= hilbert.Hnorm(vec_cutoff_eps n eps X)) <-> 
    exists k, (k <= n)%nat /\ eps <= hilbert.Hnorm(X k).
  Proof.
    split.
    + apply vec_cutoff_ge_eps_exists.
    + intro H. apply ROrderedType.ROrder.not_gt_le.
      revert H. apply ssrbool.contraPnot.
      intro H. generalize (vec_cutoff_ge_eps_exists_contrapose n eps X H); intros.
      apply Classical_Pred_Type.all_not_not_ex.
      intros k. specialize (H0 k).
      apply Classical_Prop.or_not_and.
      apply Classical_Prop.imply_to_or; intros.
      specialize (H0 H1).  apply Rgt_not_le; trivial.
  Qed.

  Lemma vec_cutoff_ge_eps_Rmax_list_iff {size:nat} (n : nat) (eps : R) (X : nat -> vector R size):
    (eps <= hilbert.Hnorm(vec_cutoff_eps n eps X)) <-> eps <= Rmax_list_map (seq 0 (S n)) (fun n => hilbert.Hnorm (X n)).
  Proof.
    assert (Hn : (0 < S n)%nat) by lia.
    rewrite (Rmax_list_map_seq_ge eps (fun n => hilbert.Hnorm (X n)) Hn).
    rewrite vec_cutoff_ge_eps_exists_iff.
    split; intros; destruct H as [x [Hx1 Hx2]]; exists x; split; trivial; lia.
  Qed.

  Definition vec_cutoff_eps_rv {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size) :=
    fun omega => vec_cutoff_eps n eps (fun k => X k omega).


  Lemma rvmaxlist_ge (X : nat -> Ts -> R): forall n omega, X n omega <= rvmaxlist X n omega.
  Proof.
    intros.
    unfold rvmaxlist.
    apply Rmax_spec.
    rewrite in_map_iff.
    exists n; split; trivial.
    rewrite in_seq; lia.
  Qed.

  Lemma vec_cutoff_eps_rv_lt_eps eps {size:nat} (X : nat -> Ts -> vector R size) : forall omega,
      (forall k, hilbert.Hnorm(X k omega) < eps) ->
      (forall n, vec_cutoff_eps_rv n eps X omega = X n omega).
  Proof.
    intros omega H n.
    unfold vec_cutoff_eps_rv.
    now apply (vec_cutoff_eps_lt_eps eps n (fun k => X k omega)).
  Qed.

  Lemma vec_cutoff_eps_rv_ge_eps eps {size:nat} (X : nat -> Ts -> vector R size) : forall omega,
      (forall k:nat, eps <= hilbert.Hnorm(X k omega)) ->
      (forall n, vec_cutoff_eps_rv n eps X omega = X 0%nat omega).
  Proof.
    intros omega H n.
    unfold vec_cutoff_eps_rv.
    now apply (vec_cutoff_eps_ge_eps eps (fun k => X k omega)).
  Qed.

  Lemma vec_cutoff_ge_eps_rv_rvmaxlist_iff {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size): forall omega,
      eps <= hilbert.Hnorm(vec_cutoff_eps_rv n eps X omega) <->
      eps <= rvmaxlist (fun k => fun omega => hilbert.Hnorm (X k omega)) n omega.
  Proof.
    intros omega.
    unfold rvmaxlist, vec_cutoff_eps_rv.
    now rewrite vec_cutoff_ge_eps_Rmax_list_iff.
  Qed.

  Lemma Rle_Rmax : forall r1 r2 r : R, Rmax r1 r2 <= r <-> r1 <= r /\ r2 <= r.
  Proof.
    split; intros.
    + split.
      -- eapply Rle_trans; try (apply H); apply Rmax_l.
      -- eapply Rle_trans; try (apply H); apply Rmax_r.
    + destruct H; apply Rmax_lub; trivial.
  Qed.

  Instance max_list_measurable (k : nat) (X : nat -> Ts -> R)
           {rm: forall n, (n <= k)%nat -> RealMeasurable dom (X n)} :
    RealMeasurable dom (fun omega => Rmax_list_map (seq 0 (S k)) (fun n => X n omega)).
  Proof.
    unfold Rmax_list_map.
    induction k.
    - simpl.
      apply rm; lia.
    - unfold RealMeasurable in *; intros.
      assert (pre_event_equiv
                (fun omega : Ts =>
                   Rmax_list (map (fun n : nat => X n omega) (seq 0 (S (S k)))) <= r)
                (pre_event_inter
                   (fun omega : Ts =>
                      Rmax_list (map (fun n : nat => X n omega) (seq 0 (S k))) <= r)
                   (fun omega => X (S k) omega <= r))).
      {
        intro x; unfold pre_event_inter.
        replace (seq 0 (S(S k))) with (seq 0 (S k) ++ [S k]) by
            (do 3 rewrite seq_S; f_equal; lra).
        rewrite Rmax_list_app; try (apply seq_not_nil; lia).
        apply Rle_Rmax.
      }
      rewrite H.
      apply sa_inter.
      + apply IHk.
        intros.
        apply rm; lia.
      + apply rm; lia.
  Qed.

  Global Instance vec_rv_cutoff_eps_rv {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size) 
           {rv: forall k, (k <= n)%nat -> RandomVariable dom (Rvector_borel_sa size) (X k)} :
    RandomVariable dom (Rvector_borel_sa size) (vec_cutoff_eps_rv n eps X).
  Proof.
    unfold vec_cutoff_eps_rv.
    apply RealVectorMeasurableRandomVariable.
    assert (mrv : forall k, (k <= n)%nat ->  RealVectorMeasurable (X k)).
    {
      intros.
      apply RandomVariableRealVectorMeasurable.
      apply rv; lia.
    }
    unfold RealVectorMeasurable in *.
    intros.
    intro.
    induction n.
    - simpl; apply mrv; lia.
    - simpl in *.
      unfold RealMeasurable in mrv.
      rewrite vector_nth_fun_to_vector.
      rewrite vector_nth_fun_to_vector in IHn.
      assert (mrv_le: (S n <= S n)%nat) by lia.
      specialize (mrv (S n) mrv_le i pf).
      rewrite vector_nth_fun_to_vector in mrv.
      assert (sa1 : sa_sigma (fun omega : Ts => Rmax_list_map (0%nat :: seq 1 n) (fun n0 : nat => hilbert.Hnorm (X n0 omega)) < eps)).
      {
        apply sa_le_lt.
        apply (max_list_measurable n); intros.
        unfold hilbert.Hnorm.
        apply Rsqrt_measurable.
        unfold hilbert.inner; simpl.
        apply Rvector_inner_measurable; apply RandomVariableRealVectorMeasurable; apply rv; lia.
      } 
      rewrite (sa_proper _ _
                         (pre_event_union 
                            (pre_event_inter 
                               (fun omega : Ts => (Rmax_list_map (0%nat :: seq 1 n) (fun n0 : nat => hilbert.Hnorm (X n0 omega))) < eps)
                               (fun omega => vector_nth i pf (X (S n) omega) <= r))
                            (pre_event_inter 
                               (pre_event_complement (fun omega : Ts => (Rmax_list_map (0%nat :: seq 1 n) (fun n0 : nat => hilbert.Hnorm (X n0 omega))) < eps))
                               (fun omega => (vector_nth i pf (vec_cutoff_eps n eps (fun k : nat => X k omega))) <= r)))).
      + apply sa_union.
        * apply sa_inter; trivial.
        * apply sa_inter; trivial.
          -- apply sa_complement; trivial.
          -- apply IHn.
             ++ intros.
                apply rv; lia.
             ++ intros.
                rewrite vector_nth_fun_to_vector.
                apply rv_measurable.
                apply vecrvnth_rv.
                apply rv; lia.
      + red; intros.
        match_destr.
        * split; intros.
          -- left.
             split; trivial.
          -- destruct H.
             ++ destruct H; trivial.
             ++ destruct H.
                now elim H.
        * split; intros.
          -- right.
             split; trivial.
          -- destruct H.
             ++ destruct H.
                tauto.
             ++ destruct H; trivial.
  Qed.

  (*
Instance vec_nnf_cutoff_eps_rv {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size) 
         {nnf: forall n, NonnegativeFunction (X n)} :
  NonnegativeFunction (cutoff_eps_rv n eps X).
Proof.
  unfold cutoff_eps_rv.
  induction n.
  - now simpl.
  - simpl.
    intro x.
    specialize (IHn x).
    simpl in IHn.
    match_destr.
    apply nnf.
Qed.
   *)

  Lemma vec_cutoff_eps_values {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size) :
    forall (x:Ts),
    exists (k : nat), 
      (k <= n)%nat /\
      vec_cutoff_eps_rv n eps X x = X k x.
  Proof.
    intros.
    unfold vec_cutoff_eps_rv.
    induction n.
    - exists (0%nat); simpl.
      now split; try lia.
    - simpl.
      match_destr.
      + exists (S n).
        now split; try lia.
      + destruct IHn as [k [? ?]].
        exists k.
        now split; try lia.
  Qed.

  Local Obligation Tactic := idtac.

  Global Program Instance vec_frf_cutoff_eps_rv {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size) 
          {frf: forall n, FiniteRangeFunction (X n)} :
    FiniteRangeFunction (vec_cutoff_eps_rv n eps X) := {
    frf_vals := flat_map (fun k => frf_vals (FiniteRangeFunction := frf k)) (seq 0 (S n))
                                                      }.
  Next Obligation.
    intros.
    apply in_flat_map.
    destruct (vec_cutoff_eps_values n eps X x) as [k [kle ck]].
    exists k.
    split.
    - apply in_seq; lia.
    - rewrite ck.
      apply frf.
  Qed.

  Local Obligation Tactic := unfold complement, equiv; Tactics.program_simpl.

  Lemma vec_cutoff_eps_succ_minus {size:nat} eps (X : nat -> vector R size) :
    forall n, minus (vec_cutoff_eps (S n) eps X) (vec_cutoff_eps n eps X) =
              if (Rlt_dec (Rmax_list_map (seq 0 (S n)) (fun n => hilbert.Hnorm (X n))) eps) then
                minus (X (S n)) (X n) else (vector_const 0 size).
  Proof.
    intros n.
    simpl.
    match_destr; intuition; try lra.
    - f_equal.
      replace (0%nat :: seq 1 n) with (seq 0 (S n)) in r by (now simpl).
      induction n; try (now simpl).
      assert (0 < S n)%nat by lia.
      generalize (Rmax_list_map_succ eps (fun n => hilbert.Hnorm (X n)) (S n) H r); intros.
      specialize (IHn H0).
      simpl. match_destr; intuition; try lra.
    - now rewrite minus_eq_zero.
  Qed.

  Definition vec_pre_cutoff_event {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size) : pre_event Ts :=
    fun x => Rmax_list_map (seq 0 n) (fun n => hilbert.Hnorm (X n x)) < eps.

  Program Definition vec_cutoff_indicator {size:nat} (n : nat) (eps : R) (X : nat -> Ts -> vector R size) :=
    EventIndicator (P := vec_pre_cutoff_event n eps X) _.
  Next Obligation.
    apply ClassicalDescription.excluded_middle_informative.
  Defined.

  Global Instance vec_cutoff_ind_rv {size:nat} (j:nat) (eps:R) (X: nat -> Ts -> vector R size) 
           {rv : forall n, (n <= j)%nat -> RandomVariable dom (Rvector_borel_sa size) (X n)}
           {fsf : forall n, FiniteRangeFunction (X n)} :
    RandomVariable dom borel_sa
                   (vec_cutoff_indicator (S j) eps (rvsumvec X)).
  Proof.
    unfold vec_cutoff_indicator.
    apply EventIndicator_pre_rv.
    unfold vec_pre_cutoff_event.
    apply sa_le_lt.
    intros.
    apply max_list_measurable.        
    intros.
    unfold hilbert.Hnorm, hilbert.inner; simpl.
    apply Rsqrt_measurable.
    apply Rvector_inner_measurable.
    - apply RandomVariableRealVectorMeasurable.
      apply rvsumvec_rv.
      intros.
      apply rv; lia.
    - apply RandomVariableRealVectorMeasurable.
      apply rvsumvec_rv.
      intros.
      apply rv; lia.
  Qed.

  Lemma partition_measurable_rvplus (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2}         
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable  rv_X1 l ->
    partition_measurable  rv_X2 l ->     
    partition_measurable  (rvplus rv_X1 rv_X2) l.
  Proof.
    unfold partition_measurable. intros.
    specialize (H0 H p H3).
    specialize (H1 H p H3).
    destruct H0 as [c1 ?].
    destruct H1 as [c2 ?].     
    exists (Rplus c1 c2).
    intros ?.
    simpl.
    unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
    unfold rvplus; simpl; intros.
    now rewrite (H0 x), (H1 x).
  Qed.

  Lemma partition_measurable_rvsumvec {size:nat} (j : nat) (X : nat -> Ts -> vector R size)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)}
        (l : list (event dom)) :
    is_partition_list l ->
    (forall k, (k <= j)%nat -> partition_measurable (cod:=Rvector_borel_sa size) (X k) l) ->
    partition_measurable (cod:=Rvector_borel_sa size)  (rvsumvec X j) l.
  Proof.
    unfold partition_measurable; intros.
    induction j.
    - specialize (H0 0%nat).
      cut_to H0; try lia; trivial.
      destruct (H0 p H2) as [c ?].
      exists c.
      unfold rvsumvec.
      rewrite H3.
      intros ?; simpl.
      unfold pre_event_preimage; simpl.
      now rewrite sum_O.
    - unfold rvsumvec.
      generalize H0; intros HH0.
      specialize (H0 (S j)).
      cut_to H0; try lia; trivial.
      cut_to IHj.
      + specialize (H0 p H2).
        destruct IHj as [c0 ?].
        destruct H0 as [c1 ?].
        exists (plus c1 c0).
        intros x; simpl.
        repeat red in H0, H3.
        unfold pre_event_preimage, pre_event_singleton in *; simpl in *; intros px.
        rewrite sum_Sn.
        rewrite (plus_comm c1 c0).
        unfold plus; simpl.
        f_equal; auto.
        now apply H3.
      + intros.
        apply HH0; trivial.
        lia.
  Qed.

  Lemma partition_measurable_rvinner {size:nat} (rv_X1 rv_X2 : Ts -> vector R size)
        {rv1 : RandomVariable dom (Rvector_borel_sa size) rv_X1}
        {rv2 : RandomVariable dom (Rvector_borel_sa size) rv_X2} 
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2}         
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable (cod:=Rvector_borel_sa size) rv_X1 l ->
    partition_measurable (cod:=Rvector_borel_sa size) rv_X2 l ->     
    partition_measurable (rvinner rv_X1 rv_X2) l.
  Proof.
    unfold partition_measurable. intros.
    specialize (H0 H p H3).
    specialize (H1 H p H3).
    destruct H0 as [c1 ?].
    destruct H1 as [c2 ?].     
    exists (Rvector_inner c1 c2).
    intros ?.
    simpl.
    unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
    unfold rvinner; simpl; intros.
    now rewrite (H0 x), (H1 x).
  Qed.

  Lemma partition_measurable_indicator 
        {P : event dom} 
        (dec:forall x, {P x} + {~ P x}) 
        (l : list (event dom)) :
    (forall (Q : event dom), 
        In Q l ->
        (event_sub Q P) \/ (event_sub Q (event_complement P))) ->
    partition_measurable (EventIndicator dec) l.
  Proof.
    intros.
    unfold partition_measurable; intros.
    unfold frf_vals, EventIndicator_frf, IndicatorRandomVariableSimpl.
    unfold preimage_singleton, EventIndicator, event_sub.
    unfold pre_event_sub, pre_event_preimage, pre_event_singleton.
    destruct (H p H1).
    - exists 1.
      simpl; intros.
      match_destr.
      now specialize (H2 x H3).
    - exists 0.
      simpl; intros.
      match_destr.
      now specialize (H2 x H3).
  Qed.    

  Lemma partition_measurable_indicator_pre
        {P : pre_event Ts} 
        (dec:forall x, {P x} + {~ P x}) 
        {rv : RandomVariable dom borel_sa (EventIndicator dec)}
        (l : list (event dom)) :
    (forall (Q : event dom), 
        In Q l ->
        (pre_event_sub Q P) \/ (pre_event_sub Q (pre_event_complement P))) ->
    partition_measurable (EventIndicator dec) l.
  Proof.
    intros.
    unfold partition_measurable; intros.
    unfold frf_vals, EventIndicator_frf, IndicatorRandomVariableSimpl.
    unfold preimage_singleton, EventIndicator, event_sub.
    unfold pre_event_sub, pre_event_preimage, pre_event_singleton.
    destruct (H p H1).
    - exists 1.
      simpl; intros.
      match_destr.
      now specialize (H2 x H3).
    - exists 0.
      simpl; intros.
      match_destr.
      now specialize (H2 x H3).
  Qed.

  Lemma vec_Chebyshev_ineq_div_mean0 {size:nat}
        (X : Ts -> vector R size )
        (rv : RandomVariable dom (Rvector_borel_sa size) X)
        (a : posreal) :
    Rbar_le (ps_P (event_ge dom (rvinner X X) (mkposreal _ (rsqr_pos a))))
            (Rbar_div_pos
               (NonnegExpectation (rvinner X X))
               (mkposreal _ (rsqr_pos a))).
  Proof.
    apply Markov_ineq_div.
  Qed.

  Lemma vec_filtration_history_var_const {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (j:nat) 
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom),
      In Q (map dsa_event (vec_filtration_history (S j) X)) ->
      forall (k:nat), 
        (k <= j)%nat ->
        exists (c:vector R size),
        forall x, Q x -> X k x = c.
  Proof.
    intros.
    generalize (vec_part_meas_hist k (j - k)%nat X); intros.
    unfold partition_measurable in H1.
    generalize (vec_part_list_history (S j) X); intros.
    replace (S k + (j - k))%nat with (S j) in H1 by lia.
    cut_to H1; trivial.
    specialize (H1 Q).
    cut_to H1; trivial.
  Qed.

  Lemma vec_filtration_history_rvsum_var_const_shift {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (m j:nat)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom),
      In Q (map dsa_event (vec_filtration_history (S j + m)%nat X)) ->
      forall (k:nat),
        (k <= j)%nat ->
        exists (c:vector R size),
        forall x, Q x -> rvsumvec (fun n => X(n+m)%nat) k x = c.
  Proof.
    intros.
    generalize (partition_measurable_rvsumvec k (fun n => X (n+m)%nat)
                                              (map dsa_event (vec_filtration_history (S j + m)%nat X))); intros.
    generalize (vec_part_list_history (S j + m)%nat X); intros.
    cut_to H1; trivial.
    - unfold partition_measurable in H1.
      cut_to H1; trivial.
      specialize (H1 Q).
      cut_to H1; trivial.
    - intros.
      generalize (vec_part_meas_hist (k0+m) (j - k0)%nat X); intros.
      now replace (S (k0 + m) + (j - k0))%nat with (S j + m)%nat in H4 by lia.
  Qed.

  Lemma vec_filtration_history_rvsum_var_const_ex_shift {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (m j:nat)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom),
      In Q (map dsa_event (vec_filtration_history (S j + m)%nat X)) ->
      forall (k:nat),
        (k <= j)%nat ->
        {c:vector R size |
          forall x, Q x -> rvsumvec (fun n => X (n+m)%nat) k x = c}.
  Proof.
    intros.
    generalize (vec_filtration_history_rvsum_var_const_shift X eps m j Q H k H0); intros.
    now apply constructive_indefinite_description in H1.
  Qed.

  Lemma vec_filtration_history_rvsum_var_const_fun_shift {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (m j:nat)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom),
      In Q (map dsa_event (vec_filtration_history (S j + m)%nat X)) ->
      exists (f :  {n':nat | n' <= j}%nat -> vector R size),
      forall (k:  {n':nat | n' <= j}%nat),
      forall x, Q x -> rvsumvec (fun n => X(n+m)%nat) (proj1_sig k) x = f k.
  Proof.
    intros.
    generalize (vec_filtration_history_rvsum_var_const_ex_shift X eps m j Q H); intros.
    exists (fun k => (proj1_sig (X0 (proj1_sig k) (proj2_sig k)))).
    intros.
    destruct k; simpl.
    generalize (X0 x0 l); intros.
    destruct s.
    simpl.
    now apply e.
  Qed.

  Lemma vec_pre_cutoff_event_const_history_shift {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (j m:nat)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom),
      In Q (map dsa_event (vec_filtration_history (S j + m)%nat X)) ->
      exists (c:R),
      forall x, Q x -> Rmax_list_map (seq 0 (S j)) 
                                     (fun n : nat => hilbert.Hnorm (rvsumvec (fun k => X (k + m)%nat) n x)) = c.
  Proof.
    intros.
    generalize (vec_filtration_history_rvsum_var_const_fun_shift X eps m j Q H); intros.
    destruct H0 as [f ?].
    setoid_rewrite Rmax_list_seq_bounded_nat.
    exists (Rmax_list_map (bounded_nat_finite_list (S j))
                          (fun x0 => hilbert.Hnorm (f (bounded_nat_lt_succ_le j x0)))).
    intros.
    apply Rmax_list_map_ext_in; intros.
    f_equal. specialize (H0 (bounded_nat_lt_succ_le j x0) x H1).
    rewrite <-H0. f_equal.
  Qed.

  Lemma vec_partition_measurable_cutoff_ind_shift {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (m:nat)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall j, partition_measurable (vec_cutoff_indicator (S j) eps (rvsumvec (fun n => X (n + m)%nat))) (map dsa_event (vec_filtration_history (S j + m)%nat X)).
  Proof.
    intros.
    apply partition_measurable_indicator_pre; intros.
    - generalize (vec_pre_cutoff_event_const_history_shift X eps j m Q H); intros.
      unfold pre_event_sub, vec_pre_cutoff_event, pre_event_complement.
      destruct H0 as [c ?].
      destruct (Rlt_dec c eps).
      + left.
        intros.
        now rewrite H0.
      + apply Rnot_lt_ge in n.
        right; intros.
        apply Rge_not_lt.
        rewrite H0; trivial.
  Qed.

  Lemma partition_measurable_rvsqrt (rv_X : Ts -> R)
        {rv : RandomVariable dom borel_sa rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable   rv_X l ->
    partition_measurable  (rvsqrt rv_X) l.
  Proof.
    intros.
    unfold partition_measurable. intros.
    specialize (H0 H p H2).
    destruct H0 as [c1 ?].
    exists (sqrt c1).
    intros ?.
    simpl.
    unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
    unfold rvsqrt; simpl; intros.
    now rewrite (H0 x).
  Qed.

  Definition rvnorm {size:nat} (X : Ts -> vector R size) :=
    rvsqrt (rvinner X X).

  Lemma vec_partition_measurable_Rmax_list_map {size:nat} (j : nat) (X : nat -> Ts -> vector R size)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)}
        (l : list (event dom)) :
    is_partition_list l ->
    (forall k, (k <= j)%nat -> partition_measurable (cod := Rvector_borel_sa size) (X k) l) ->
    partition_measurable (fun x =>
                            (Rmax_list_map (seq 0 (S j))
                                           (fun n : nat => hilbert.Hnorm (X n x)))) l.
  Proof.
    unfold partition_measurable; intros.
    assert (Hr : forall k, (k <= j)%nat -> is_partition_list l -> partition_measurable (rvnorm (X k)) l).
    {
      intros. apply partition_measurable_rvsqrt; eauto.
      apply partition_measurable_rvinner; eauto.
      - unfold partition_measurable; eauto.
      - unfold partition_measurable; eauto.        
    }
    induction j.
    - assert (Hz : (0 <= 0)%nat) by lia.
      specialize (Hr 0%nat Hz). clear Hz.
      cut_to Hr; try lia; trivial.
      destruct (Hr H p H2) as [c ?].
      unfold frf_vals in H3.
      exists c.
      rewrite H3.
      intros ?; simpl.
      unfold pre_event_preimage; simpl.
      unfold Rmax_list_map. simpl.
      unfold rvabs. trivial.
    - generalize (Hr); intros HHr.
      specialize (Hr (S j)).
      cut_to Hr; try lia; trivial.
      cut_to IHj.
      + specialize (Hr H p H2).
        destruct IHj as [c0 ?].
        destruct Hr as [c1 ?].
        exists (Rmax (c0) (c1)).
        intros x; simpl.
        repeat red in H4, H6.
        unfold pre_event_preimage, pre_event_singleton in *; simpl in *; intros px.
        replace (0%nat :: 1%nat :: seq 2%nat j) with (seq 0%nat (S j) ++ [S j]).
        -- unfold Rmax_list_map.
           rewrite Rmax_list_app; try (apply seq_not_nil; lia).
           unfold Rmax_list_map in H3.
           specialize (H3 x px).
           specialize (H4 x px).
           unfold preimage_singleton, pre_event_preimage, pre_event_preimage, pre_event_singleton, proj1_sig in H3, H4.
           subst.
           reflexivity.
        -- simpl.
           now rewrite <- seq_S; simpl.
      + intros.
        apply H0; trivial.
        lia.
      + intros; apply HHr; trivial; try lia.
  Qed.
  
  Lemma vec_partition_measurable_Rmax_list_map_rvsumvec {size:nat} (j : nat) (X : nat -> Ts -> vector R size)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)}
        (l : list (event dom)) :
    is_partition_list l ->
    (forall k, (k <= j)%nat -> partition_measurable (cod := Rvector_borel_sa size) (X k) l) ->
    partition_measurable (fun x => 
                            (Rmax_list_map (seq 0 (S j)) 
                                           (fun n : nat => hilbert.Hnorm (rvsumvec X n x)))) l.
  Proof.
    intros.
    assert (forall n, FiniteRangeFunction (rvsumvec X n)).
    {
      intros.
      typeclasses eauto.
    }
    generalize (vec_partition_measurable_Rmax_list_map j (rvsumvec X) l H); intros.
    apply H1.
    intros.
    apply (partition_measurable_rvsumvec k X l H).
    intros.
    apply H0.
    lia.
  Qed.
  
  Lemma vec_cutoff_eps_const_history_shift {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (j m:nat)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall (Q : event dom), 
      In Q (map dsa_event (vec_filtration_history (S j + m)%nat X)) ->
      exists (c:vector R size),
      forall x, Q x -> (vec_cutoff_eps_rv j eps (rvsumvec (fun n => X (n + m)%nat))) x = c.
  Proof.
    unfold vec_cutoff_eps_rv.
    induction j; intros.
    - simpl.
      unfold rvsum.
      setoid_rewrite sum_O.
      replace (1 + m)%nat with (S m) in H by lia.
      generalize (vec_filtration_history_var_const X eps m Q H m); intros.
      cut_to H0; try lia.
      destruct H0 as [c ?].
      exists c.
      now apply H0.
    - assert (exists (QQ: event dom), (event_sub Q QQ) /\
                                      (In QQ (map dsa_event (vec_filtration_history (S j + m)%nat X)))).
      {
        replace (S j) with (j+1)%nat in H by lia.
        simpl in H.
        replace (j+1)%nat with (S j) in H by lia.
        unfold refine_dec_sa_partitions in H.
        rewrite in_map_iff in H.
        destruct H as [? [? ?]].
        unfold refine_dec_sa_event in H0.
        rewrite in_flat_map in H0.
        destruct H0 as [? [? ?]].
        rewrite in_map_iff in H1.
        destruct H1 as [? [? ?]].
        exists (dsa_event x1).
        split; [|now apply in_map].
        unfold dec_sa_event_inter in H1.
        assert (event_inter (dsa_event x0) (dsa_event x1) = dsa_event x).
        - rewrite <- H1.
          now simpl.
        - rewrite H in H3.
          rewrite <- H3.
          apply event_inter_sub_r.
      }
      destruct H0 as [QQ [? ?]].
      generalize (vec_filtration_history_rvsum_var_const_fun_shift X eps m (S j)%nat Q H); intros.
      simpl.
      generalize (vec_pre_cutoff_event_const_history_shift X eps j m QQ H1); intros.
      destruct H3 as [c1 ?].
      specialize (IHj QQ H1).
      destruct IHj as [c2 ?].
      destruct H2 as [f ?].
      assert (S j <= S j)%nat by lia.
      exists (if Rlt_dec c1 eps then (f (exist _ _ H5)) else c2).
      intros.
      specialize (H0 x H6).
      specialize (H4 x H0).
      rewrite H4.
      specialize (H3 x H0).
      replace (0%nat :: seq 1 j) with (seq 0%nat (S j)) by now simpl.
      rewrite H3.
      rewrite <- (H2 (exist _ _ H5) x H6).
      now unfold proj1_sig; simpl.
  Qed.

  Lemma event_sub_preimage_singleton (f : Ts -> R) c
        (rv : RandomVariable dom borel_sa f):
    forall (p : event dom), event_sub p (preimage_singleton f c) <->
                            (forall x, p x -> f x = c).
  Proof.
    intros; split; intros.
    + repeat red in H.
      apply H. unfold proj1_sig.
      apply H0.
    + repeat red.
      apply H.
  Qed.
  
  Lemma partition_constant_measurable 
        (f : Ts -> R)
        (rv : RandomVariable dom borel_sa f)
        (frf : FiniteRangeFunction f)
        (l : list (event dom)) :
    is_partition_list l ->
    (forall (p : event dom),
        In p l ->
        exists c, forall x, p x -> f x = c) <->
    partition_measurable f l.
  Proof.
    unfold partition_measurable.
    intros.
    split; intros.
    - destruct (H0 p H2) as [c ?].
      exists c.
      now repeat red.
    - now apply H0.
  Qed.

  Lemma vec_partition_constant_measurable {size:nat}
        (f : Ts -> vector R size)
        (rv : RandomVariable dom (Rvector_borel_sa size) f)
        (frf : FiniteRangeFunction f)
        (l : list (event dom)) :
    is_partition_list l ->
    (forall (p : event dom),
        In p l ->
        exists c, forall x, p x -> f x = c) <->
    partition_measurable (cod := Rvector_borel_sa size) f l.
  Proof.
    unfold partition_measurable.
    intros.
    split; intros.
    - destruct (H0 p H2) as [c ?].
      exists c.
      now repeat red.
    - now apply H0.
  Qed.

  Lemma vec_partition_measurable_cutoff_eps_shift {size:nat} (X : nat -> Ts -> vector R size) (eps : R) (m:nat)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)} :
    forall j, partition_measurable (cod := Rvector_borel_sa size)
                                   (vec_cutoff_eps_rv j eps (rvsumvec (fun n => X (n+m)%nat)))
                                   (map dsa_event (vec_filtration_history ((S j)+m)%nat X)).
  Proof.
    intros.
    apply vec_partition_constant_measurable.
    - apply vec_part_list_history.
    - intros.
      apply (vec_cutoff_eps_const_history_shift X eps j m p H).
  Qed.

End ash.


 Section ash2.

   Context {Ts:Type} {dom: SigmaAlgebra Ts}{Prts: ProbSpace dom}.
   
  Lemma vec_indicator_prod_cross_shift {size:nat} (j m:nat) (eps:R) (X: nat -> Ts -> vector R size) 
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall n, FiniteRangeFunction (X n)}
        {isfe_in : let Xm := fun n => X (n + m)%nat in 
                   IsFiniteExpectation 
                     Prts
                     (rvinner
                        (vecrvscalerv (vec_cutoff_indicator (S j) eps (rvsumvec Xm))
                                      (vec_cutoff_eps_rv j eps (rvsumvec Xm))) (Xm (S j)))}
        {isfe_mult : let Xm := fun n => X (n + m)%nat in
            vector_IsFiniteExpectation 
              Prts 
              (vecrvmult 
                 (vecrvscalerv (vec_cutoff_indicator (S j) eps (rvsumvec Xm))
                               (vec_cutoff_eps_rv j eps (rvsumvec Xm))) (Xm (S j)))}
        {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
        (HC : forall (n:nat), 
          almostR2 Prts eq
              (vector_FiniteConditionalExpectation 
                 Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
              (const Rvector_zero)) :
    let Xm := fun n => X (n + m)%nat in 
    FiniteExpectation Prts
      (rvinner (vecrvscalerv (vec_cutoff_indicator (S j) eps (rvsumvec Xm))
                             (vec_cutoff_eps_rv j eps (rvsumvec Xm)))
               (Xm (S j))) = 0.
  Proof.
    intros.
    generalize (vector_FiniteCondexp_factor_out_inner_zero_swapped); intros.
    specialize (H Prts _ (filtration_history_sa_sub (cod := Rvector_borel_sa size) X (j + m)%nat)).
    specialize (H size (Xm (S j))  (vecrvscalerv (vec_cutoff_indicator (S j) eps (rvsumvec Xm))
          (vec_cutoff_eps_rv j eps (rvsumvec Xm))) _ _).
    cut_to H.
    - simpl in isfe_in.
      simpl in isfe_mult.
      rewrite <- (H _ _).
      + apply FiniteExpectation_ext.
        reflexivity.
      + apply HC.
    - unfold Xm.
      apply Rvector_scale_rv_rv.
      + apply vec_cutoff_ind_rv.
        * intros.
          apply filtration_history_sa_le_rv.
          lia.
        * easy.
      + apply vec_rv_cutoff_eps_rv; intros.
        apply rvsumvec_rv; intros.
        apply filtration_history_sa_le_rv.
        lia.
     Qed.
  
  Lemma rvnorm_hnorm {size:nat} (X : Ts -> vector R size) :
    forall omega,
      (rvnorm X) omega = hilbert.Hnorm (X omega).
  Proof.
    auto.
  Qed.

  Lemma Rvector_inner_plus_r {n:nat} (x y z:vector R n)  : 
    Rvector_inner x (Rvector_plus y z) = Rplus (Rvector_inner x y) (Rvector_inner x z).
  Proof.
    rewrite Rvector_inner_comm.
    rewrite (Rvector_inner_comm x y).
    rewrite (Rvector_inner_comm x z).    
    apply Rvector_inner_plus.
  Qed.

  Lemma Rvector_inner_sum {size:nat} (X Y : vector R size) :
    (Rvector_inner (Rvector_plus X Y) (Rvector_plus X Y)) = 
    (Rplus (Rvector_inner X X) 
           (Rplus (Rmult 2 (Rvector_inner X Y))
                  (Rvector_inner Y Y))).
  Proof.
    rewrite Rvector_inner_plus.
    do 2 rewrite Rvector_inner_plus_r.
    rewrite (Rvector_inner_comm Y X).
    ring.
  Qed.

  Lemma rvinner_sum {size:nat} (X Y : Ts -> vector R size) :
    rv_eq (rvinner (vecrvplus X Y) (vecrvplus X Y))
          (rvplus (rvinner X X) 
                  (rvplus (rvscale 2 (rvinner X Y))
                          (rvinner Y Y))).
  Proof.
    intros x.
    unfold rvinner, vecrvplus, rvplus, rvscale.
    now rewrite Rvector_inner_sum.
  Qed.

  Lemma vecrvplus_minus {size:nat} (X Y : Ts -> vector R size) (z:Ts) :
    (X z) = (vecrvplus Y 
                       (vecrvminus X Y)) z.
  Proof.
    unfold vecrvminus, vecrvplus.
    rewrite Rvector_plus_assoc.
    rewrite Rvector_plus_comm.
    rewrite Rvector_plus_assoc.
    rewrite (Rvector_plus_comm (vecrvopp Y z) (Y z)).
    replace (vecrvopp Y z) with (Rvector_opp (Y z)).
    - rewrite Rvector_plus_inv.
      rewrite Rvector_plus_comm.
      now rewrite Rvector_plus_zero.
    - now unfold Rvector_opp, vecrvopp, vecrvscale.
  Qed.

  Lemma rvmaxlist_rvnorm_hnorm {size:nat} (n : nat) (X : nat -> Ts -> vector R size) :
    forall omega,
      rvmaxlist (fun k : nat => rvnorm (X k)) n omega =
      rvmaxlist (fun k : nat => (fun omega => hilbert.Hnorm ((X k) omega))) n omega.
  Proof.
    intros.
    unfold rvmaxlist.
    now setoid_rewrite rvnorm_hnorm.
  Qed.

  Lemma Rvector_opp_scale {size:nat} (X : vector R size) :
    Rvector_opp X = Rvector_scale (-1) X.
  Proof.
    easy.
  Qed.

  Lemma vec_ash_6_1_4 {size:nat} (X: nat -> Ts -> vector R size) (eps:posreal) (m:nat)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall (n:nat), FiniteRangeFunction (X n)}
        {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}        
        (HC : forall (n:nat), 
          almostR2 Prts eq
              (vector_FiniteConditionalExpectation 
                 Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
              (const Rvector_zero)) :
    let Sum := fun j => (rvsumvec (fun n => X (n + m)%nat) j) in
    forall (n:nat), ps_P (event_ge dom (rvmaxlist (fun k => rvnorm(Sum k)) n) eps) <=
                    (SimpleExpectation (rvinner (Sum n) (Sum n)))/eps^2.
  Proof.
    intros.
    assert (H1 : event_equiv (event_ge dom (rvmaxlist (fun k => rvnorm(Sum k)) n) eps)
                             (event_ge dom (rvnorm(vec_cutoff_eps_rv n eps Sum)) eps)).
    {
      intro omega.
      unfold proj1_sig; simpl.
      split; intros H; try (apply Rle_ge; apply Rge_le in H).
      + rewrite rvnorm_hnorm.
        now rewrite vec_cutoff_ge_eps_rv_rvmaxlist_iff.
      + rewrite rvmaxlist_rvnorm_hnorm.
        now rewrite <- vec_cutoff_ge_eps_rv_rvmaxlist_iff.
    }
    rewrite H1.
    generalize (vec_Chebyshev_ineq_div_mean0 (vec_cutoff_eps_rv n eps Sum) _ eps); intros H3.
    erewrite <- simple_NonnegExpectation in H3.  
    simpl in H3.
    rewrite <- Rsqr_pow2.
    unfold rvnorm.
    assert (H3eq: event_equiv
                    (event_ge dom
                              (rvsqrt
                                 (rvinner (vec_cutoff_eps_rv n eps Sum) 
                                          (vec_cutoff_eps_rv n eps Sum)))
                              eps)
                    (event_ge dom
                              (rvinner (vec_cutoff_eps_rv n eps Sum) 
                                       (vec_cutoff_eps_rv n eps Sum))
                              eps²)).
    {
      intro x.
      simpl.
      unfold rvsqrt.
      replace (pos eps) with (sqrt (Rsqr eps)) at 3.
      - split; intros.
        + apply Rle_ge.
          apply sqrt_le_0.
          * apply Rle_0_sqr.
          * unfold rvinner.
            generalize (hilbert.inner_ge_0 (vec_cutoff_eps_rv n eps Sum x)); intros.
            unfold hilbert.inner in H0; simpl in H0.
            apply H0.
          * apply Rge_le.
            apply H.
        + apply Rle_ge.
          apply sqrt_le_1.
          * apply Rle_0_sqr.
          * unfold rvinner.
            generalize (hilbert.inner_ge_0 (vec_cutoff_eps_rv n eps Sum x)); intros.
            unfold hilbert.inner in H0; simpl in H0.
            apply H0.
          * apply Rge_le.
            apply H.
      - apply sqrt_Rsqr.
        left.
        apply cond_pos.
    }
    rewrite H3eq.
    eapply Rle_trans; [apply H3 |].
    unfold Rdiv.
    apply Rmult_le_compat_r; 
      [left; apply Rinv_0_lt_compat, Rlt_0_sqr, Rgt_not_eq, cond_pos |].
    assert (Srel:forall j, SimpleExpectation(rvinner (Sum (S j)) (Sum (S j))) =
                           SimpleExpectation(rvinner (Sum j) (Sum j)) + 
                           SimpleExpectation(rvinner (X ((S j)+m)%nat) (X ((S j)+m)%nat))).
    {
      intros.
      assert (rv_eq (Sum (S j)) (vecrvplus (Sum j) (X (S j + m)%nat))).
      - intro x.
        unfold vecrvplus.
        unfold Sum, rvsumvec.
        now rewrite sum_Sn.
      - generalize (rvinner_sum (Sum j) (X (S j + m)%nat)); intros.
        rewrite <- H in H0.
        rewrite (SimpleExpectation_ext H0).
        rewrite <- sumSimpleExpectation.
        rewrite <- sumSimpleExpectation.
        rewrite <- Rplus_assoc.
        rewrite <- scaleSimpleExpectation.

        assert (isfe_in : forall j k : nat, IsFiniteExpectation Prts (rvinner (X j) (X k))).
        {
          intros.
          apply IsFiniteExpectation_simple; typeclasses eauto.
        }
        assert (isfe_mult : forall j k : nat, vector_IsFiniteExpectation Prts (vecrvmult (X j) (X k))).
        {
          intros.
          apply vector_IsFiniteExpectation_simple.
          - typeclasses eauto.
          - now apply frf_vecrvmult.
       }
        assert(isfe_sum : forall j k : nat,
             IsFiniteExpectation 
               Prts
               (rvinner (rvsumvec (fun n : nat => X (n + m)%nat) j) (X (k + m)%nat))).
       {
         intros.
         apply IsFiniteExpectation_simple; typeclasses eauto.         
        }
        generalize (vec_expec_cross_zero_sum2_shift X m HC); intros.
        specialize (H2 j (S j)).
        cut_to H2; try lia.
        replace  (SimpleExpectation (rvinner (Sum j) (X (S j + m)%nat))) with 0.
        + ring.
        + rewrite simple_FiniteExpectation.
          unfold Sum.
          rewrite <- H2.
          apply FiniteExpectation_pf_irrel.
    }
    assert (Zrel: forall j,
               SimpleExpectation (rvinner (vec_cutoff_eps_rv (S j) eps Sum)
                                         (vec_cutoff_eps_rv (S j) eps Sum)) =
               SimpleExpectation (rvinner (vec_cutoff_eps_rv j eps Sum)
                                         (vec_cutoff_eps_rv j eps Sum)) + 
               SimpleExpectation  (rvinner (vecrvminus (vec_cutoff_eps_rv (S j) eps Sum) 
                                                     (vec_cutoff_eps_rv j eps Sum))
                                         (vecrvminus (vec_cutoff_eps_rv (S j) eps Sum) 
                                                     (vec_cutoff_eps_rv j eps Sum)))).
    {
      intros.
      assert (rv_eq (rvinner (vec_cutoff_eps_rv (S j) eps Sum)
                             (vec_cutoff_eps_rv (S j) eps Sum)) 
                    (rvplus (rvinner (vec_cutoff_eps_rv j eps Sum)
                                     (vec_cutoff_eps_rv j eps Sum))
                            (rvplus
                               (rvscale 2
                                        (rvinner (vec_cutoff_eps_rv j eps Sum)
                                                 (vecrvminus 
                                                    (vec_cutoff_eps_rv (S j) eps Sum) 
                                                    (vec_cutoff_eps_rv j eps Sum))))
                               (rvinner (vecrvminus (vec_cutoff_eps_rv (S j) eps Sum) 
                                                    (vec_cutoff_eps_rv j eps Sum))
                                        (vecrvminus (vec_cutoff_eps_rv (S j) eps Sum) 
                                                    (vec_cutoff_eps_rv j eps Sum)))))).
      - intro x.
        assert (rv_eq (rvinner (vec_cutoff_eps_rv (S j) eps Sum) (vec_cutoff_eps_rv (S j) eps Sum))
                      (rvinner (vecrvplus (vec_cutoff_eps_rv j eps Sum)
                                          (vecrvminus 
                                             (vec_cutoff_eps_rv (S j) eps Sum) 
                                             (vec_cutoff_eps_rv j eps Sum)))
                               (vecrvplus (vec_cutoff_eps_rv j eps Sum)
                                          (vecrvminus 
                                             (vec_cutoff_eps_rv (S j) eps Sum) 
                                             (vec_cutoff_eps_rv j eps Sum))))).
        + unfold rvinner.
          intro z; simpl.
          now rewrite <- vecrvplus_minus.
        + rewrite H.
          now rewrite rvinner_sum.         
      - rewrite (SimpleExpectation_ext H).
        rewrite <- sumSimpleExpectation.
        rewrite <- sumSimpleExpectation.
        rewrite <- Rplus_assoc.
        f_equal.
        rewrite <- scaleSimpleExpectation.
        assert (SimpleExpectation (rvinner (vec_cutoff_eps_rv j eps Sum) 
                                           (vecrvminus (vec_cutoff_eps_rv (S j) eps Sum) 
                                                       (vec_cutoff_eps_rv j eps Sum))) = 0).
        + assert (Heq :rv_eq
                         (rvinner 
                            (vec_cutoff_eps_rv j eps Sum) 
                            (vecrvscalerv 
                               (vec_cutoff_indicator (S j) eps Sum)
                               (X ((S j)+m)%nat)))
                         (rvinner 
                            (vec_cutoff_eps_rv j eps Sum) 
                            (vecrvminus (vec_cutoff_eps_rv (S j) eps Sum) 
                                        (vec_cutoff_eps_rv j eps Sum)))).
          {
            intros w.
            unfold rvinner, vecrvminus, vecrvopp, vecrvplus, vecrvscale, vecrvscalerv.
            f_equal.
            unfold vec_cutoff_eps_rv, vec_cutoff_indicator, EventIndicator.
            unfold vec_cutoff_indicator_obligation_1.
            generalize (vec_cutoff_eps_succ_minus eps (fun k => Sum k w) j); intros.
            unfold minus, plus, opp in H0; simpl in H0.
            simpl.
            rewrite <- Rvector_opp_scale.
            rewrite H0.
            unfold vec_pre_cutoff_event.
            match_destr.
            - match_destr.
              + rewrite Rvector_scale1.
                unfold Sum, rvsumvec.
                rewrite sum_Sn.
                unfold plus; simpl.
                rewrite <- Rvector_plus_assoc.
                rewrite (Rvector_plus_comm (X (S (j + m)%nat) w) _).
                rewrite Rvector_plus_assoc.
                rewrite Rvector_plus_inv.
                rewrite Rvector_plus_comm.
                now rewrite Rvector_plus_zero.
              + tauto.
            - match_destr.
              + tauto.
              + now rewrite Rvector_scale0.
          }
          erewrite <-(SimpleExpectation_ext Heq).
          assert (rv_eq
                    (rvinner (vec_cutoff_eps_rv j eps Sum)
                             (vecrvscalerv (vec_cutoff_indicator (S j) eps Sum) (X ((S j)+m)%nat)))
                    (rvinner
                       (vecrvscalerv (vec_cutoff_indicator (S j) eps (rvsumvec (fun n => X (n +  m)%nat)))
                                     (vec_cutoff_eps_rv j eps (rvsumvec (fun n => X (n +  m)%nat))) )
                       (X (S j + m)%nat))).
          {
            unfold rvinner, vecrvscalerv.
            intro x.
            rewrite Rvector_inner_scal.
            rewrite Rvector_inner_comm.
            rewrite Rvector_inner_scal.
            rewrite Rvector_inner_comm.
            now unfold Sum, rvsumvec.
          }
          erewrite (SimpleExpectation_ext H0).
          rewrite simple_FiniteExpectation.
          apply vec_indicator_prod_cross_shift with (isfe0 := isfe) (rv0 := rv); trivial.
          simpl.
          apply vector_IsFiniteExpectation_simple.
          * typeclasses eauto.
          * apply frf_vecrvmult; trivial.
            apply frf_vecrvscalerv; typeclasses eauto.
        + rewrite H0.
          lra.
    }
    clear H1 H3 H3eq.
    induction n.
    + simpl.
      right.
      apply SimpleExpectation_ext.
      intro x.
      now unfold Sum.
    + rewrite Srel.
      rewrite Zrel.
      apply Rplus_le_compat; trivial.
      apply SimpleExpectation_le.
      intro x.
      unfold rvinner, vecrvminus, vecrvplus, vecrvopp, vecrvscale.
      unfold vec_cutoff_eps_rv.
      generalize (vec_cutoff_eps_succ_minus eps (fun j => Sum j x) n); intros Hcut.
      replace ( minus (vec_cutoff_eps (S n) eps (fun j : nat => Sum j x))
                      (vec_cutoff_eps n eps (fun j : nat => Sum j x))) with
          (Rvector_plus (vec_cutoff_eps (S n) eps (fun k : nat => Sum k x))
                        (Rvector_scale (-1) (vec_cutoff_eps n eps (fun k : nat => Sum k x)))) in Hcut by reflexivity.
      rewrite Hcut.
      match_destr.
      * right.
        unfold Sum, rvsumvec, minus, plus, opp; simpl.
        rewrite sum_Sn.
        unfold plus; simpl.
        rewrite <- Rvector_plus_assoc.
        rewrite (Rvector_plus_comm (X (S (n + m)%nat) x) _).
        rewrite Rvector_plus_assoc.
        rewrite Rvector_plus_inv.
        rewrite Rvector_plus_comm.
        now rewrite Rvector_plus_zero.
      * rewrite Rvector_inner_zero.
        apply Rvector_inner_pos.
    Qed.

  Lemma vec_var_sum_cross_0_offset {size:nat} (X : nat -> Ts -> vector R size) (m : nat)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)}
        {frf : forall (n:nat), FiniteRangeFunction (X n)}
        {isfe : forall n, vector_IsFiniteExpectation Prts (X n)}
        (HC : forall (n:nat), 
          almostR2 Prts eq
              (vector_FiniteConditionalExpectation 
                 Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
              (const Rvector_zero)) :
    let Xm := fun n => X (n + m)%nat in
    forall j, SimpleExpectation(rvinner (rvsumvec Xm j) (rvsumvec Xm j)) =
              sum_n (fun n => SimpleExpectation (rvinner (X (n + m)%nat) (X (n + m)%nat))) j.
  Proof.
    intros.
    induction j.
    - assert (rv_eq (rvinner (rvsumvec Xm 0%nat) (rvsumvec Xm 0%nat)) (rvinner (X m) (X m))). 
      + intro x.
        unfold Xm, rvinner, rvsumvec; simpl.
        now rewrite sum_O.
      + rewrite (SimpleExpectation_ext H).
        now rewrite sum_O.
    - rewrite sum_Sn.
      unfold plus; simpl.
      assert (rv_eq (rvinner (rvsumvec Xm (S j)) (rvsumvec Xm (S j)))
                    (rvplus (rvinner (rvsumvec Xm j) (rvsumvec Xm j))
                            (rvplus
                               (rvscale 2
                                        (rvinner (rvsumvec Xm j) (X ((S j)+m)%nat)))
                               (rvinner (X ((S j)+m)%nat) (X ((S j)+m)%nat) )))).
      + intro x.
        unfold Xm, rvinner, vecrvplus, rvsumvec.
        rewrite sum_Sn.
        unfold plus; simpl.
        rewrite Rvector_inner_sum.
        now unfold rvplus, rvscale; simpl.
      + rewrite (SimpleExpectation_ext H).
        rewrite <- sumSimpleExpectation.
        rewrite <- sumSimpleExpectation.
        rewrite <- scaleSimpleExpectation.
        assert (isfe_in : forall j k : nat, IsFiniteExpectation Prts (rvinner (X j) (X k))).
        {
          intros.
          apply IsFiniteExpectation_simple; typeclasses eauto.
        }
        assert (isfe_mult : forall j k : nat, vector_IsFiniteExpectation Prts (vecrvmult (X j) (X k))).
        {
          intros.
          apply vector_IsFiniteExpectation_simple.
          - typeclasses eauto.
          - now apply frf_vecrvmult.
       }
        assert(isfe_sum : forall j k : nat,
             IsFiniteExpectation 
               Prts
               (rvinner (rvsumvec (fun n : nat => X (n + m)%nat) j) (X (k + m)%nat))).
       {
         intros.
         apply IsFiniteExpectation_simple; typeclasses eauto.         
        }
        generalize (vec_expec_cross_zero_sum2_shift X m HC); intros.
        specialize (H0 j (S j)).
        cut_to H0; try lia.
        replace (SimpleExpectation (rvinner (rvsumvec Xm j) (X (S j + m)%nat))) with 0.
        * rewrite <- IHj.
          ring_simplify.
          reflexivity.
        * rewrite simple_FiniteExpectation.
          unfold Xm.
          rewrite <- H0.
          apply FiniteExpectation_pf_irrel.
   Qed.

  Lemma vec_sa_sigma_not_cauchy {size:nat} (X : nat -> Ts -> vector R size) (eps:posreal) (N : nat)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)} :
    sa_sigma (fun omega =>
                exists (n m : nat),
                  (n >= N)%nat /\ (m >= N)%nat /\
                  hilbert.Hnorm (minus (X n omega) (X m omega)) >= eps) .
  Proof.
    apply sa_countable_union; intros n.
    apply sa_countable_union; intros m.
    apply sa_inter.
    - apply sa_sigma_const_classic.
    - apply sa_inter.
      + apply sa_sigma_const_classic.
      + apply sa_le_ge; intros.
        apply Rsqrt_measurable.
        apply Rvector_inner_measurable.
        * apply Rvector_plus_measurable.
          -- now apply RandomVariableRealVectorMeasurable.
          -- apply Rvector_opp_measurable.
             now apply RandomVariableRealVectorMeasurable.
        * apply Rvector_plus_measurable.
          -- now apply RandomVariableRealVectorMeasurable.
          -- apply Rvector_opp_measurable.
             now apply RandomVariableRealVectorMeasurable.
  Qed.

  Lemma vec_sa_sigma_not_full_cauchy {size:nat} (X : nat -> Ts -> vector R size)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)} :
    sa_sigma (fun omega => exists (eps : posreal), forall N:nat,
                    exists (n m : nat),
                      (n >= N)%nat /\ (m >= N)%nat /\
                      hilbert.Hnorm (minus (X n omega) (X m omega)) >= eps).
  Proof.
    assert (eqq1:pre_event_equiv
                   (fun omega => exists (eps : posreal), forall N:nat,
                          exists (n m : nat),
                            (n >= N)%nat /\ (m >= N)%nat /\
                            hilbert.Hnorm (minus (X n omega) (X m omega)) >= eps)
                   (fun omega => exists (eps : QArith_base.Q),
                        (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} eps) /\
                        forall N:nat,
                        exists (n m : nat),
                          (n >= N)%nat /\ (m >= N)%nat /\
                          hilbert.Hnorm (minus (X n omega) (X m omega)) >= Q2R eps)).
    {
      intros x.
      split.
      - intros [eps HH].
        destruct (Q_dense 0 eps) as [q [ql qr]].
        + apply cond_pos.
        + exists q.
          split.
          * apply Rlt_Qlt.
            unfold QArith_base.inject_Z.
            unfold Q2R.
            simpl.
            rewrite Rmult_0_l.
            apply ql.
          * intros N.
            destruct (HH N) as [n [m [? [? HH3]]]].
            exists n; exists m.
            intuition lra.
      - intros [eps [epos HH]].
        assert (qepspos: 0 < Q2R eps).
        {
          apply Qlt_Rlt in epos.
          now rewrite RMicromega.Q2R_0 in epos.
        }
        exists (mkposreal (Q2R eps) qepspos).
        intros N.
        destruct (HH N) as [n [m [? [HH3]]]].
        exists n; exists m.
        intuition lra.
    }
    rewrite eqq1.
    apply sa_countable_union_iso; try typeclasses eauto.
    intros.
    destruct (Rlt_dec 0 (Q2R i)).
    - assert (QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
      {
        apply Rlt_Qlt.
        now rewrite RMicromega.Q2R_0.
      } 
      eapply (sa_proper _  (fun omega => (forall N : nat,
                                             exists n m : nat,
                                               (n >= N)%nat /\ (m >= N)%nat /\ hilbert.Hnorm (minus (X n omega) (X m omega)) >= Q2R i))).
      + firstorder.
      + apply sa_pre_countable_inter; intros N.
        now apply (vec_sa_sigma_not_cauchy X (mkposreal _ r)).
    - eapply sa_proper; try apply sa_none.
      assert (~ QArith_base.Qlt {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} i).
      {
        intros qlt.
        apply Qlt_Rlt in qlt.
        now rewrite RMicromega.Q2R_0 in qlt.
      } 
      firstorder.
  Qed.

  Lemma vec_sa_sigma_cauchy_descending {size:nat} (X : nat -> Ts -> vector R size )(eps : posreal)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}:
    forall n, let E := fun n => exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps n) in
              event_sub (E (S n)) (E n).
  Proof.
    intros n E.
    repeat red. intros omega H.
    red in H. destruct H as [n0 [m0 [H1 [H2 H3]]]].
    exists n0; exists m0.
    repeat split; try lia; trivial.
  Qed.

  Lemma vec_sa_sigma_cauchy_inter_event_sub {size:nat} (X : nat -> Ts -> vector R size) {eps1 eps2 : posreal}
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)} (Heps : eps2 < eps1) (n : nat):
    event_sub (inter_of_collection (fun n => exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps1 n)))
              (inter_of_collection (fun n => exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps2 n))).
  Proof.
    repeat red. intros omega H.
    repeat red in H. intros m.
    specialize (H m).
    destruct H as [n0 [m0 [H1 [H2 H3]]]].
    exists n0; exists m0.
    repeat split; try lia; try lra.
  Qed.

  (* Move to ProbSpace.v *)
  Lemma ps_union_countable_union_iff (coll : nat -> event dom):
    (forall n, ps_P (coll n) = 0) <-> (ps_P (union_of_collection coll) = 0).
  Proof.
    split; intros H.
    + now apply ps_zero_countable_union.
    + intros n.
      assert (H1 : 0 <= ps_P (coll n)) by (apply ps_pos).
      assert (H2 : ps_P (coll n) <= ps_P (union_of_collection coll)).
      {
        apply ps_sub.
        apply union_of_collection_sup.
      }
      rewrite H in H2.
      lra.
  Qed.

  Lemma recip_pos (m : nat) : 0 < /(1 + INR m).
  Proof.
    apply Rinv_pos.
    generalize (pos_INR m). generalize (INR m) as x; intros.
    lra.
  Qed.

  Lemma vec_almost_cauchy_iff {size:nat} (X : nat -> Ts -> vector R size)
        {rv : forall n, RandomVariable dom (Rvector_borel_sa size) (X n)}:
    event_equiv ((exist sa_sigma _ (vec_sa_sigma_not_full_cauchy X)))
                (union_of_collection
                   (fun m => inter_of_collection
                               (fun k => exist sa_sigma _ (vec_sa_sigma_not_cauchy X (mkposreal (/(1 + INR m)) (recip_pos _)) k)))).
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
      destruct Heps as [n0 [m0 [Hn0 [Hm0 Hnm]]]].
      exists n0. exists m0.
      repeat split; try trivial.
      eapply Rge_trans; eauto.
      lra.
    + destruct H as [N HN].
      exists (mkposreal (/(1 + INR N)) (recip_pos _)).
      simpl. intros N0.
      specialize (HN N0).
      assumption.
  Qed.

  Lemma ps_P_sub_zero (E1 E2 : event dom) :
    event_sub E1 E2 -> ps_P E2 = 0 -> ps_P E1 = 0.
  Proof.
    intros.
    generalize (ps_sub _ E1 E2 H); intros.
    rewrite H0 in H1.
    generalize (ps_pos E1); intros.
    lra.
  Qed.

  (* ash prob 2.5.4 *)
  Lemma vec_almost_cauchy_seq_at_iff {size:nat} (X : nat -> Ts -> vector R size)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)} :
    almost _ (fun omega => vec_cauchy_seq_at omega X) <->
    (forall (eps:posreal),
        Lim_seq (fun N =>
                   ps_P (exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps N))) = 0).
  Proof.
    assert (H1 : forall (eps: posreal),let E := fun n => exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps n) in
                                       is_lim_seq (fun k => ps_P (E k)) (ps_P (inter_of_collection E))).
    {
      intros eps E.
      apply is_lim_descending.
      apply vec_sa_sigma_cauchy_descending.
    }
    unfold vec_cauchy_seq_at.
    split; intros.
    + rewrite almost_alt_eq in H.
      unfold almost_alt in H.
      destruct H as [E [HE Heps]].
      specialize (H1 eps). simpl in H1.
      apply is_lim_seq_unique in H1. rewrite H1.
      rewrite Rbar_finite_eq.
      apply ps_P_sub_zero with E; trivial.
      intros omega.
      simpl; specialize (Heps omega).
      intros. apply Heps. push_neg.
      push_neg_in Heps.
      now exists eps.
                 + (* forall 0<δ, P(B_δ) = 0*)
                   assert (Hinter : forall eps:posreal, let E :=
                                                            fun n : nat => exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps n) in
                                                        (ps_P (inter_of_collection E)) = 0).
                   {
                     intros eps E.
                     rewrite <-Rbar_finite_eq.
                     rewrite <-H with eps. symmetry.
                     apply is_lim_seq_unique. apply H1.
                   }
                   clear H.
                   rewrite almost_alt_eq.
                   unfold almost_alt.
                   exists (exist sa_sigma _ (vec_sa_sigma_not_full_cauchy X)).
                   split.
                   ++ rewrite vec_almost_cauchy_iff.
                      rewrite <-ps_union_countable_union_iff.
                      intros n; apply (Hinter ({| pos := /(1 + INR n); cond_pos := recip_pos n|})).
                   ++ intros omega Hnot.
                      simpl. now push_neg_in Hnot.
  Qed.


  (*TODO(Kody): Simplify this proof using the above.*)
  Lemma vec_almost_cauchy_is_lim_seq_iff {size:nat} (X : nat -> Ts -> vector R size)
        {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X n)} :
    almost _ (fun omega => vec_cauchy_seq_at omega X) <->
    (forall (eps:posreal),
        is_lim_seq (fun N =>
                      ps_P (exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps N))) 0).
  Proof.
    assert (H1 : forall (eps: posreal),let E := fun n => exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps n) in
                                       is_lim_seq (fun k => ps_P (E k)) (ps_P (inter_of_collection E))).
    {
      intros eps E.
      apply is_lim_descending.
      apply vec_sa_sigma_cauchy_descending.
    }
    unfold vec_cauchy_seq_at.
    split; intros.
    + rewrite almost_alt_eq in H.
      unfold almost_alt in H.
      destruct H as [E [HE Heps]].
      specialize (H1 eps). simpl in H1.
      enough (Hpsp : ps_P (
                         inter_of_collection(
                             fun n => (exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps n)))) = 0).
    - now rewrite <-Hpsp.
    - apply ps_P_sub_zero with E; trivial.
      intros omega.
      simpl; specialize (Heps omega).
      intros. apply Heps. push_neg.
      push_neg_in Heps.
      now exists eps.
                 + (* forall 0<δ, P(B_δ) = 0*)
                   assert (Hinter : forall eps:posreal, let E :=
                                                            fun n : nat => exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps n) in
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
                   exists (exist sa_sigma _ (vec_sa_sigma_not_full_cauchy X)).
                   split.
                   ++ rewrite vec_almost_cauchy_iff.
                      rewrite <-ps_union_countable_union_iff.
                      intros n; apply (Hinter ({| pos := /(1 + INR n); cond_pos := recip_pos n|})).
                   ++ intros omega Hnot.
                      simpl. now push_neg_in Hnot.
  Qed.

  Lemma Lim_seq_le (u v : nat -> R):
    (forall n, u n <= v n) -> Rbar_le (Lim_seq u) (Lim_seq v).
  Proof.
    intros.
    apply Lim_seq_le_loc.
    exists (0%nat); intros.
    apply H.
  Qed.

  Lemma event_ge_pf_irrel {x}
        {rv_X : Ts -> R}
        {rv1 : RandomVariable dom borel_sa rv_X}
        {rv2 : RandomVariable dom borel_sa rv_X} :
    event_equiv (event_ge dom rv_X (rv:=rv1) x)
                (event_ge dom rv_X (rv:=rv2) x).
  Proof.
    repeat red; intros.
    split; intros; trivial.
  Qed.
  
  Lemma sqr_pos (eps : posreal) :
    0 < Rsqr eps.
  Proof.
    apply Rsqr_pos_lt.
    apply Rgt_not_eq.
    apply cond_pos.
  Qed.
  
    (*ash 6.2.1 *)
    Lemma vec_Ash_6_2_1_helper {size:nat} (X : nat -> Ts -> vector R size) (eps : posreal) (m : nat)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))}
          (HC : forall (n:nat), 
              almostR2 Prts eq
                       (vector_FiniteConditionalExpectation 
                          Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
                       (const Rvector_zero)) :

      let Sum := fun j => rvsumvec (fun k => X (k+m)%nat) j in
      Rbar_le (Lim_seq (fun n => ps_P (event_ge dom (rvmaxlist (fun k => rvnorm (Sum k)) n) eps)))
              (Rbar_div_pos (LimSup_seq (sum_n (fun n => SimpleExpectation (rvinner (X (n + m)%nat) (X (n + m)%nat))))) (mkposreal _ (sqr_pos eps))).
    Proof.
      intros.
      generalize (vec_ash_6_1_4 X); intros.
      specialize (H eps m _ _ isfe HC).
      simpl in H.
      generalize (Lim_seq_le _ _ H); intros.
      unfold Sum.
      eapply Rbar_le_trans.
      - apply H0.
      - replace (eps * (eps * 1)) with (Rsqr eps) by (unfold Rsqr; lra).
        unfold Rdiv.
        rewrite Lim_seq_scal_r.
        replace (Rbar.Finite (/ (Rsqr (pos eps)))) with (Rbar.Finite (/ (pos (mkposreal _ (sqr_pos eps))))) by now simpl.
        rewrite Rbar_mult_div_pos.
        apply Rbar_div_pos_le.
        generalize (vec_var_sum_cross_0_offset X m HC); intros.
        simpl in H1.
        rewrite Lim_seq_ext with (v := sum_n (fun n : nat => SimpleExpectation (rvinner (X (n + m)%nat)  (X (n + m)%nat)))).
        + apply Lim_seq_sup_le.
        + apply H1.
    Qed.

    Lemma vec_Ash_6_2_1_helper2 {size:nat} (X : nat -> Ts -> vector R size) (eps : posreal)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))}:
      ex_series (fun n => SimpleExpectation (rvinner (X n) (X n))) ->
      is_lim_seq (fun m =>
                    (Rbar_div_pos (LimSup_seq (sum_n (fun n => SimpleExpectation (rvinner (X (n + (S m))%nat) (X (n + (S m))%nat))))) 
                                  (mkposreal _ (sqr_pos eps)))) 0.
    Proof.
      intros.
      apply is_lim_seq_ext with
          (u := fun m => (Rbar_div_pos (Series (fun n => SimpleExpectation (rvinner (X (n + (S m))%nat) (X (n + (S m))%nat))))
                                       (mkposreal _ (sqr_pos eps)))).
      {
        intros.
        generalize (LimSup_seq_series H); intros.
        now rewrite H0.
      }
      simpl.
      unfold Rdiv.
      replace (Rbar.Finite 0) with (Rbar_mult 0 (/ (mkposreal _ (sqr_pos eps)))).
      - apply is_lim_seq_scal_r.
        generalize (zerotails _ H); intros.
        apply is_lim_seq_ext with
            (u :=  (fun n : nat =>
                      Series (fun k : nat => SimpleExpectation (rvinner (X (S (n + k))) (X (S (n + k))))))).
        + intros.
          apply Series_ext.
          intros.
          apply SimpleExpectation_ext.
          intro x.
          now replace (n0 + S n)%nat with (S (n + n0))%nat by lia.
        + apply H0.
      - simpl.
        now rewrite Rmult_0_l.
    Qed.

    Lemma list_union_rvmaxlist (f : nat -> Ts -> R) (eps : posreal) (n : nat) 
          (rv: forall n, RandomVariable dom borel_sa (f n)) :
      event_equiv
        (list_union
           (collection_take (fun k => event_ge dom (f k) eps) (S n)))
        (event_ge dom (rvmaxlist f n) eps).
    Proof.
      split.
      - intros [a [inn ax]].
        apply In_collection_take in inn.
        destruct inn as [m [mlt ?]]; subst.
        simpl in ax.
        simpl.
        unfold rvmaxlist.
        apply Rle_ge.
        apply Rge_le in ax.
        eapply Rmax_list_ge; eauto.
        apply in_map_iff.
        eexists; split; eauto.
        apply in_seq.
        lia.
      - intros rvm.
        simpl in rvm.
        unfold rvmaxlist in rvm.
        generalize (Rmax_list_In (map (fun n : nat => f n x) (seq 0 (S n))))
        ; intros HH.
        cut_to HH; [| simpl; congruence].
        apply in_map_iff in HH.
        destruct HH as [m [fm mini]].
        exists (event_ge dom (f m) eps).
        split.
        + unfold collection_take.
          apply in_map_iff.
          eexists; split; eauto.
        + simpl.
          congruence.
    Qed.

    Lemma vec_Ash_6_2_1_helper3 {size:nat} (X : nat -> Ts -> vector R size) (eps : posreal) (m : nat) 
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))} :
      let Sum := fun j => rvsumvec X j in
      Rbar.Finite (ps_P (union_of_collection (fun k =>  event_ge dom (rvnorm (vecrvminus (Sum (k+(S m))%nat) (Sum m))) eps))) =
      Lim_seq (fun n => ps_P (event_ge dom (rvmaxlist (fun k => rvnorm (vecrvminus (Sum (k + (S m))%nat) (Sum m))) n) eps)).
    Proof.
      intros.
      assert (Rbar.Finite (ps_P
                             (union_of_collection (fun k : nat => event_ge dom (rvnorm (vecrvminus (Sum (k + (S m))%nat) (Sum m))) eps))) =
              Lim_seq (fun n => ps_P (list_union (collection_take (fun k : nat => event_ge dom (rvnorm (vecrvminus (Sum (k + (S m))%nat) (Sum m))) eps) (S n))))).
      {
        rewrite lim_ascending.
        - now rewrite event_union_list_union.
        - unfold ascending_collection.
          intros.
          replace (S n) with (n+1)%nat by lia.
          rewrite collection_take_Sn.
          rewrite list_union_app.
          apply event_sub_union_l.
      }
      rewrite H.
      apply Lim_seq_ext.
      intros.
      apply ps_proper.
      apply list_union_rvmaxlist.
    Qed.

    Lemma vec_sum_n_m_shift {size:nat} (α : nat -> vector R size) (k n0 : nat) :
      sum_n_m α k (n0 + k)%nat = sum_n (fun n1 : nat => α (n1 + k)%nat) n0.
    Proof.
      unfold sum_n.
      induction n0.
      - replace (0 + k)%nat with (k) by lia.
        do 2 rewrite sum_n_n.
        f_equal; lia.
      - replace (S n0 + k)%nat with (S (n0 + k)%nat) by lia.
        rewrite sum_n_Sm; try lia.
        rewrite sum_n_Sm; try lia.
        replace (S n0 + k)%nat with (S (n0 + k)%nat) by lia.
        now rewrite IHn0.
    Qed.

    Lemma vec_sum_shift_diff {size:nat} (X : nat -> vector R size) (m a : nat) :
      minus (sum_n X (a + S m)) (sum_n X m) =
      sum_n (fun n0 : nat => X (n0 + S m)%nat) a.
    Proof.
      rewrite <- vec_sum_n_m_shift.
      unfold sum_n.
      rewrite sum_split with (m0 := m); try lia.
      unfold minus,plus,opp; simpl.
      generalize (sum_n_m X 0 m) as k.
      generalize (sum_n_m X (S m) (a + S m)).
      intros s k.
      rewrite Rvector_plus_comm.
      rewrite Rvector_plus_assoc.
      rewrite Rvector_inv_plus.
      rewrite Rvector_plus_comm.
      apply Rvector_plus_zero.
    Qed.
    
    Lemma vec_Ash_6_2_1_helper4 {size:nat} (X : nat -> Ts -> vector R size) (eps : posreal) (m : nat) 
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))}
          (HC : forall (n:nat), 
              almostR2 Prts eq
                       (vector_FiniteConditionalExpectation 
                          Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
                       (const Rvector_zero)) :

      let Sum := fun j => rvsumvec X j in
      Rbar_le (ps_P (union_of_collection (fun k =>  event_ge dom (rvnorm (vecrvminus (Sum (k + (S m))%nat) (Sum m))) eps)))
              (Rbar_div_pos (LimSup_seq (sum_n (fun n => SimpleExpectation (rvinner (X (n + (S m))%nat)  (X (n + (S m))%nat))))) (mkposreal _ (sqr_pos eps))).
    Proof.
      intros.
      unfold Sum.
      rewrite vec_Ash_6_2_1_helper3; trivial.
      generalize (vec_Ash_6_2_1_helper X eps (S m) HC); intros.
      simpl in H.
      rewrite Lim_seq_ext with
          (v :=  fun n : nat =>
                   ps_P
                     (event_ge dom
                               (rvmaxlist
                                  (fun k : nat => rvnorm (rvsumvec (fun k0 : nat => X (k0 + (S m))%nat) k))
                                  n) eps)).
      - apply H.
      - intros.
        apply ps_proper.
        assert (rv_eq
                  (rvmaxlist
                     (fun k : nat =>
                        rvnorm
                          (vecrvminus (rvsumvec (fun k0 : nat => X k0) (k + (S m)))
                                      (rvsumvec (fun k0 : nat => X k0) m))) n)
                  (rvmaxlist (fun k : nat => rvnorm (rvsumvec (fun k0 : nat => X (k0 + (S m))%nat) k))
                             n)).
        + intro x.
          unfold rvmaxlist.
          apply Rmax_list_Proper, refl_refl, map_ext.
          intros.
          unfold vecrvminus, rvsumvec, vecrvopp, vecrvplus, vecrvscale, rvnorm, rvsqrt, rvinner.
          f_equal.
          f_equal.
          * apply vec_sum_shift_diff.
          * apply vec_sum_shift_diff.            
        + intro x.
          simpl.
          now rewrite H0.
    Qed.

    Lemma vec_Ash_6_2_1_helper5 {size:nat} (X : nat -> Ts -> vector R size)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))}
          {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
          (HC : forall (n:nat), 
              almostR2 Prts eq
                       (vector_FiniteConditionalExpectation 
                          Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
                       (const Rvector_zero)) :

      ex_series (fun n => SimpleExpectation (rvinner (X n) (X n))) ->
      let Sum := fun j => rvsumvec X j in
      forall (eps : posreal),
        is_lim_seq (fun m => ps_P (union_of_collection (fun k => event_ge dom (rvnorm (vecrvminus (Sum (k + (S m))%nat) (Sum m))) eps))) 0. 
    Proof.
      intros.
      generalize (vec_Ash_6_2_1_helper2 X eps H); intros.
      assert (forall m, 
                 0 <= (fun m : nat =>
                         ps_P
                           (union_of_collection
                              (fun k : nat =>
                                 event_ge dom (rvnorm (vecrvminus (Sum (k + S m)%nat) (Sum m))) eps))) m <=
                 (fun m : nat =>
                    Rbar_div_pos
                      (LimSup_seq
                         (sum_n (fun n : nat => SimpleExpectation (rvinner  (X (n + (S m))%nat)  (X (n + (S m))%nat)))))
                      {| pos := eps²; cond_pos := sqr_pos eps |}) m).
      {
        intros.
        split.
        - apply ps_pos.
        - generalize (vec_Ash_6_2_1_helper4 X eps m HC); intros.
          unfold Sum in H1.
          generalize (LimSup_seq_series H); intros.
          rewrite H2 in H1.
          simpl in H1.
          rewrite H2.
          simpl.
          unfold Sum.
          apply H1.
      }
      apply (is_lim_seq_le_le _ _ _ 0 H1); trivial.
      apply is_lim_seq_const.
    Qed.

    Lemma vec_Ash_6_2_1_helper6a {size:nat} (X : nat -> Ts -> vector R size) (eps : posreal) (N : nat) 
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))} :
      event_sub
        (exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps N))
        (union_of_collection (fun k => event_ge dom (rvnorm (vecrvminus (X (k + (S N))%nat) (X N))) (eps/2))).
    Proof.
      unfold rvabs.
      intro x; simpl; intros.
      destruct H as [n [m [? [? ?]]]].
      destruct (Rge_dec (hilbert.Hnorm (minus (X n x) (X N x))) (eps/2)).
      - destruct (n == N).
        + rewrite e in r.
          rewrite minus_eq_zero in r.
          rewrite (@hilbert.norm_zero) in r.
          generalize (is_pos_div_2 eps); intros; lra.
        + assert (n > N)%nat by (destruct H; try lia;firstorder).
          exists (n - (S N))%nat.
          unfold vecrvminus.
          now replace (n - S N + S N)%nat with (n) by lia.
      - generalize (@norm_triangle R_AbsRing (@hilbert.PreHilbert_NormedModule (@Rvector_PreHilbert size)) (minus (X n x) (X N x)) (minus (X N x) (X m x)));intros.
        unfold norm in H2; simpl in H2.
        unfold minus, plus, opp in H2; simpl in H2.
        replace (Rvector_plus (Rvector_plus (X n x) (Rvector_opp (X N x)))
                              (Rvector_plus (X N x) (Rvector_opp (X m x)))) with
            (Rvector_plus (X n x) (Rvector_opp (X m x))) in H2.
        + unfold minus, plus, opp in H1; simpl in H1.
          unfold minus, plus, opp in n0; simpl in n0.
          assert (hilbert.Hnorm (Rvector_plus (X N x) (Rvector_opp (X m x))) >= eps/2) by lra.
          destruct (m == N).
          * rewrite e in H3.
            rewrite Rvector_plus_inv in H3.
            rewrite (@hilbert.norm_zero) in H3.
            assert (0 < eps) by apply cond_pos.
            lra.
          * assert (m > N)%nat by (destruct H0; try lia; firstorder).
            exists (m - (S N))%nat.
            replace (m - S N + S N)%nat with (m) by lia.
            replace (Rvector_plus (X N x) (Rvector_opp (X m x))) with 
                (minus (X N x) (X m x)) in H3.
            -- rewrite (@Hnorm_minus_opp) in H3.
               apply H3.
            -- reflexivity.
        + rewrite <- Rvector_plus_assoc. 
          f_equal.
          rewrite Rvector_plus_assoc.
          rewrite Rvector_inv_plus.
          rewrite Rvector_plus_comm.
          now rewrite Rvector_plus_zero.
    Qed.
    
    Lemma vec_Ash_6_2_1_helper6b {size:nat} (X : nat -> Ts -> vector R size) (eps : posreal) (N : nat) 
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))} :
      event_sub
        (union_of_collection (fun k => event_ge dom (rvnorm (fun omega => minus (X (k + (S N))%nat omega) (X N omega))) eps))
        (exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps N)).
    Proof.
      unfold rvnorm.
      intro x; simpl; intros.
      destruct H.
      exists (x0 + S N)%nat.
      exists N.
      split; try lia.
      split; try lia; trivial.
    Qed.

    Lemma vec_Ash_6_2_1_helper6 {size:nat} (X : nat -> Ts -> vector R size) 
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))} :
      (forall (eps:posreal), 
          is_lim_seq (fun m => ps_P (union_of_collection (fun k => event_ge dom (rvnorm (vecrvminus (X (k + (S m))%nat) (X m))) eps))) 0) <->
      (forall (eps:posreal), 
          is_lim_seq (fun N => ps_P (exist sa_sigma _ (vec_sa_sigma_not_cauchy X eps N))) 0).
    Proof.
      split; intros.
      - generalize (is_pos_div_2 eps); intros.
        specialize (H (mkposreal _ H0)).
        apply is_lim_seq_le_le with 
            (u := const 0) 
            (w :=  (fun m : nat =>
                      ps_P
                        (union_of_collection
                           (fun k : nat =>
                              event_ge dom (rvnorm (vecrvminus (X (k + S m)%nat) (X m)))
                                       {| pos := eps / 2; cond_pos := H0 |})))).
        + intros; split.
          * apply ps_pos.
          * apply ps_sub.
            apply vec_Ash_6_2_1_helper6a.
        + apply is_lim_seq_const.
        + apply H.
      - specialize (H eps).
        apply is_lim_seq_le_le with
            (u := const 0)
            (w :=  (fun N : nat =>
                      ps_P
                        (exist sa_sigma
                               (fun omega : Ts =>
                                  exists n m : nat,
                                    (n >= N)%nat /\ (m >= N)%nat /\ hilbert.Hnorm (minus (X n omega) (X m omega)) >= eps)
                               (vec_sa_sigma_not_cauchy X eps N)))).
        + intros; split.
          * apply ps_pos.
          * apply ps_sub.
            apply vec_Ash_6_2_1_helper6b.
        + apply is_lim_seq_const.
        + apply H.
    Qed.            

    Lemma cauchy_seq_at_ex_series {A : Type} (X : nat -> A -> R)
      : forall x:A,
        cauchy_seq_at x (fun (n : nat) (omega : A) => sum_n (fun n0 : nat => X n0 omega) n)
        -> ex_series (fun n => X n x).
    Proof.
      intros x Hx.
      generalize (ex_series_Cauchy (fun n => X n x)); intros.
      apply H. clear H. unfold cauchy_seq_at in Hx.
      rewrite Cauchy_series_Reals.
      unfold Cauchy_crit_series.
      unfold Cauchy_crit.
      setoid_rewrite sum_n_Reals in Hx.
      intros. unfold R_dist.
      specialize (Hx (mkposreal eps H)); eauto.
    Qed.

    Global Instance cauchy_seq_at_proper {A}: Proper (eq ==> (pointwise_relation _ (pointwise_relation _ eq)) ==> iff) (@cauchy_seq_at A).
    Proof.
      intros ??????; subst.
      unfold cauchy_seq_at.
      repeat red in H0.
      split; intros HH eps
      ; destruct (HH eps) as [N HH1]
      ; exists N
      ; intros n m HH2 HH3
      ; specialize (HH1 _ _ HH2 HH3)
      ; congruence.
    Qed.

    Lemma vec_Ash_6_2_1 {size:nat} (X : nat -> Ts -> vector R size)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))}
          {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
          (HC : forall (n:nat), 
              almostR2 Prts eq
                       (vector_FiniteConditionalExpectation 
                          Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
                       (const Rvector_zero)) :
      ex_series (fun n => SimpleExpectation (rvinner (X n) (X n))) ->
      almost Prts (fun (x : Ts) => 
                     (forall (i:nat) (pf : (i<size)%nat),
                         ex_series (fun k => (vecrvnth i pf (X k)) x))).
    Proof.
      intros.
      generalize (vec_almost_cauchy_is_lim_seq_iff (rvsumvec X)); intros.
      generalize (vec_Ash_6_2_1_helper6 (rvsumvec X)); intros.
      rewrite <- H1 in H0.
      clear H1.
      generalize (vec_Ash_6_2_1_helper5 X HC H); intros.
      simpl in H1.
      rewrite <- H0 in H1.
      unfold almost.
      destruct H1 as [E HE].
      exists E. destruct HE. split; trivial.
      intros.  specialize (H2 x H3).
      apply (cauchy_seq_at_ex_series (fun k => fun x => vecrvnth i pf (X k) x)).
      rewrite vec_cauchy_seq_at_iff in H2.
      unfold vecrvnth.
      unfold rvsumvec in H2.
      specialize (H2 i pf).
      eapply cauchy_seq_at_proper; try eapply H2; trivial.
      repeat red; intros.
      now rewrite vector_nth_sum_n.
    Qed.    

    Lemma nodup_vecscaled {size:nat} (c : R) (frf_vals : list (vector R size)) :
      c <> 0 -> map (fun v : vector R size => Rvector_scale c v) (nodup vec_Req_EM_T frf_vals) =
                nodup vec_Req_EM_T (map (fun v : vector R size => Rvector_scale c v) frf_vals).
    Proof.
      intros.
      symmetry.
      apply nodup_map_inj; intros.
      now apply Rvector_scale_inj in H2.
    Qed.

    Lemma vec_induced_sigma_scale {size:nat} (X : nat -> Ts -> vector R size) (b : nat -> R)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))} :
      (forall n, b n <> 0) ->
      forall n, Forall2 dsa_equiv (vec_induced_sigma_generators (frf n)) (vec_induced_sigma_generators (frf_vecrvscale (/ b n) (X n))).
    Proof.
      intros.
      unfold vec_induced_sigma_generators.
      unfold VectorRandomVariable.vec_induced_sigma_generators_obligation_1.
      simpl.
      assert (forall n, / b n <> 0) by (intros; now apply Rinv_neq_0_compat).
      rewrite <- nodup_vecscaled, map_map; trivial.
      unfold rvscale, preimage_singleton.
      unfold pre_event_preimage, pre_event_singleton.
      rewrite <- Forall2_map.
      apply Forall2_refl.
      intros ??; simpl.
      unfold vecrvscale.
      split; intros.
      - now subst.
      - now apply Rvector_scale_inj in H1.
    Qed.

    Lemma vec_filtration_history_scale {size:nat} (X : nat -> Ts -> vector R size) (b : nat -> R)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))} :
      (forall n, b n <> 0) ->
      forall n, Forall2 dsa_equiv (vec_filtration_history n X) (vec_filtration_history n (fun n0 : nat => vecrvscale (/ b n0) (X n0))).
    Proof.
      induction n.
      - now simpl.
      - simpl.
        apply refine_dec_sa_partitions_proper.
        + now apply vec_induced_sigma_scale.
        + apply IHn.
    Qed.
    

    Lemma vec_SCESA_scale {size:nat} (X : nat -> Ts -> vector R size) (b : nat -> R)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
(*          {frf : forall (n:nat), FiniteRangeFunction (X (n))} *)
          {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
          (HC : forall (n:nat), 
              almostR2 Prts eq
                       (vector_FiniteConditionalExpectation 
                          Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
                       (const Rvector_zero)) :
      (forall n, b n <> 0) ->
      forall n, almostR2 Prts eq 
                         (vector_FiniteConditionalExpectation Prts
                            (filtration_history_sa_sub (cod := Rvector_borel_sa size) 
                                                       (fun n0 : nat => vecrvscale (/ b n0) (X n0)) n)
                            (vecrvscale (/ (b (S n))) (X (S n))))
                         (const Rvector_zero).
    Proof.
      intros bneq n.
      assert (forall n,
                 sa_equiv (filtration_history_sa (cod := Rvector_borel_sa size) X n)
                          (filtration_history_sa (cod := Rvector_borel_sa size)
                                                 (fun n0 => (vecrvscale (/ b n0) (X n0))) n)).
    {
      intros.
      apply filtrate_sa_proper.
      intros ??.
      apply pullback_sa_vecrvscale_equiv.
      now apply Rinv_neq_0_compat.
    }
    generalize (vector_FiniteCondexp_scale 
                  Prts 
                  (filtration_history_sa_sub (cod := Rvector_borel_sa size)
                                             (fun n0 => (vecrvscale (/ b n0) (X n0))) n)
                              (/ b (S n)) (X (S n))); intros.
    specialize (HC n).
    apply almostR2_prob_space_sa_sub_lift in H0.
    revert HC; apply almost_impl.
    revert H0; apply almost_impl.

    generalize (vector_FiniteCondexp_all_proper
                  Prts
                  (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n)
                  (filtration_history_sa_sub (cod := Rvector_borel_sa size)
                                             (fun n0 : nat => vecrvscale (/ b n0) (X n0)) n)
                  (H n) (X (S n)) (X (S n))); intros HH.
    cut_to HH.
    - apply almostR2_prob_space_sa_sub_lift in HH.
      revert HH; apply almost_impl.
      apply all_almost; intros ????.
      rewrite H1.
      rewrite H0 in H2.
      
      unfold vecrvscale.
      apply (f_equal (fun z => Rvector_scale (/ b (S n)) z)) in H2.
      unfold const in H2.
      rewrite Rvector_scale_zero in H2.
      unfold const.
      unfold vecrvscale.
      rewrite <- H2.
      reflexivity.
    - apply all_almost.
      now intros.
   Qed.
    
    Lemma vec_Ash_6_2_2 {size:nat} (X : nat -> Ts -> vector R size) (b : nat -> R)
          {rv : forall (n:nat), RandomVariable dom (Rvector_borel_sa size) (X (n))}
          {frf : forall (n:nat), FiniteRangeFunction (X (n))}
          {isfe : forall (n:nat), vector_IsFiniteExpectation Prts (X n)}
          (HC : forall (n:nat), 
              almostR2 Prts eq
                       (vector_FiniteConditionalExpectation 
                          Prts (filtration_history_sa_sub (cod := Rvector_borel_sa size) X n) (X (S n))) 
                       (const Rvector_zero)) :
      (forall n, 0 < b n <= b (S n)) ->
      is_lim_seq b p_infty ->
      ex_series (fun n => SimpleExpectation (rvinner (vecrvscale (/ (b n)) (X n))
                                                  (vecrvscale (/ (b n)) (X n)))) ->
      almost Prts 
             (fun (x : Ts) => 
                (forall (i:nat) (pf : (i<size)%nat),
                    is_lim_seq (fun n => (rvscale (/ (b n)) (rvsum (fun k => (vecrvnth i pf (X k))) n)) x) 0)). 
    Proof.
      intros.
      assert (bneq0:forall n, b n <> 0).
      {
        intros.
        apply Rgt_not_eq.
        apply H.
      }
      generalize (vec_SCESA_scale X b HC bneq0); intros.
      generalize (vec_Ash_6_2_1 (fun n => vecrvscale (/ (b n)) (X n)) H2 H1); intros.
      destruct H3 as [? [? ?]].
      exists x.
      split; trivial.
      intros.
      generalize (ash_6_1_3_strong H H0 (H4 x0 H5 i pf)); intros.
      eapply is_lim_seq_ext; try (apply H6).
      intros; simpl.
      unfold rvsum, rvscale, Rdiv, vecrvnth, vecrvscale.
      rewrite Rmult_comm.
      f_equal.
      apply sum_n_ext.
      intros.
      unfold Rvector_scale.
      rewrite vector_nth_map.
      simpl; field.
      apply Rgt_not_eq.
      apply H.
    Qed.

  Lemma gen_simple_conditional_expectation_scale_zero P dec :
    rv_eq (gen_simple_conditional_expectation_scale P (const 0) dec) (const 0).
  Proof.
    unfold gen_simple_conditional_expectation_scale.
    match_destr; unfold EventIndicator; intros ?; unfold rvscale, const.
    - lra.
    - unfold rvmult.
      assert (eqq1:rv_eq (fun omega : Ts => 0 * (if dec omega then 1 else 0)) (const 0)).
      {
        intros ?; unfold const; lra.
      }
      rewrite (SimpleExpectation_ext eqq1).
      rewrite SimpleExpectation_const.
      lra.
  Qed.
    
  Lemma SimpleConditionalExpectationSA_zero (n : nat) (l : list dec_sa_event) :
    rv_eq (SimpleConditionalExpectationSA (const 0) l) (const 0).
  Proof.
    intros ?.
    unfold SimpleConditionalExpectationSA.
    induction l; simpl; trivial.
    unfold rvplus; simpl.
    rewrite gen_simple_conditional_expectation_scale_zero.
    unfold const.
    field_simplify.
    apply IHl.
  Qed.      
                                    
  Lemma vec_SimpCondexpSA_zero (n : nat) (l : list dec_sa_event) :
    rv_eq
      (vector_SimpleConditionalExpectationSA (const (@Rvector_zero n)) l)
      (const zero).
  Proof.
    unfold vector_SimpleConditionalExpectationSA; simpl; intros ?.
    apply vector_nth_eq; intros.
    rewrite vector_of_funs_vector_nth, vector_nth_create.
    simpl.
    unfold const, zero; simpl.
    rewrite Rvector_nth_zero; simpl.
    replace 0 with (const 0 a) by reflexivity.
    rewrite <- (SimpleConditionalExpectationSA_zero n l a).
    apply SimpleConditionalExpectationSA_ext; try reflexivity.
    intros ?.
    rewrite vector_nth_fun_to_vector.
    unfold const, zero; simpl.
    now rewrite Rvector_nth_zero; simpl.
  Qed.

End ash2.


