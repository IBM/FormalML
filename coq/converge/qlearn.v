Require Import List.
Require Import converge.mdp fixed_point.
Require Import RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia.
Require Import infprod Dvoretzky Expectation RandomVariableFinite.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import RandomVariableL2.
Require hilbert.

Set Bullet Behavior "Strict Subproofs".

(*
****************************************************************************************
This file is a work-in-progress proof of convergence of the classical Q-learning
algorithm.
****************************************************************************************
*)

  Section qlearn.

    Context {X : NormedModule R_AbsRing} {F : X -> X}
            (hF : is_contraction F) (α : nat -> R) (x0 : X).

    Definition f_alpha (f : X -> X) a : (X -> X)  :=
      fun (x:X) => plus (scal (1-a) x) (scal a (f x)).

    Definition g_alpha (gamma a : R) :=
      1 - (1 - gamma) * a.

    Fixpoint RMsync (n : nat) : X :=
      match n with
      | 0 => x0
      | (S k) => plus (scal (1 - α k) (RMsync k)) (scal (α k) (F (RMsync k)))
      end.

    Lemma plus_minus_scal_distr (r : R) (x1 x2 y1 y2 : X) :
      minus (plus (scal (1 - r) x1) (scal r y1) ) (plus (scal (1-r) x2) (scal r y2)) =
      plus (scal (1-r) (minus x1 x2)) (scal r (minus y1 y2)).
    Proof.
      generalize (scal_minus_distr_l (1 - r) x1 x2); intros H1.
      generalize (scal_minus_distr_l r y1 y2); intros H2.
      setoid_rewrite H1.
      setoid_rewrite H2.
      generalize (scal (1-r) x1) as a.
      generalize (scal r y1) as b.
      generalize (scal (1-r) x2) as c.
      generalize (scal r y2) as d.
      intros.
      unfold minus.
      rewrite opp_plus.
      rewrite plus_assoc.
      rewrite plus_assoc.
      f_equal.
      rewrite <-plus_assoc.
      rewrite <-plus_assoc.
      f_equal. apply plus_comm.
    Qed.

    (* Proof of Lemma 1. *)
    Lemma is_contraction_falpha (r : R) :
      (0<r<1) -> (@norm_factor R_AbsRing X <= 1) ->
      is_contraction (f_alpha F r).
    Proof.
      intros Hr Hnf.
      unfold is_contraction.
      destruct hF as [γ [Hγ [Hγ0 HF]]].
      exists (1 - r + r*γ).
      split.
      + rewrite <-(Rplus_0_r).
        replace (1 -r + r*γ) with (1 + r*(γ-1)) by lra.
        apply Rplus_lt_compat_l.
        replace 0 with (r*0) by lra.
        apply Rmult_lt_compat_l ; lra.
      + unfold is_Lipschitz in *.
        split; intros.
        ++ replace 0 with  (0+0) by lra.
          apply Rplus_le_compat.
          --- lra.
          --- replace 0 with (r*0) by lra.
              apply Rmult_le_compat_l ; lra.
        ++ apply (@norm_compat1 R_AbsRing).
           rewrite Rmult_plus_distr_r.
           unfold f_alpha.
           rewrite plus_minus_scal_distr.
           generalize (norm_triangle (scal (1-r) (minus x2 x1)) (scal r (minus (F x2) (F x1)))) ; intros.
           eapply Rle_lt_trans ; eauto.
           apply Rplus_lt_le_compat.
          --  generalize (norm_scal (1-r) (minus x2 x1)) ; intros.
              eapply Rle_lt_trans ; eauto.
              unfold abs ; simpl.
              replace (Rabs (1-r)) with (1-r) by (symmetry; try apply Rabs_pos_eq;
                                                  try (lra)).
              apply Rmult_lt_compat_l ; try lra.
              unfold ball_x in H0.
              simpl in H0.
              generalize (norm_compat2 x1 x2 (mkposreal r0 H)) ; intros.
              replace r0 with (1*r0) by lra.
              eapply Rlt_le_trans ; eauto ; try lra.
              simpl. apply Rmult_le_compat_r ; lra; trivial.
          --  generalize (norm_scal r (minus (F x2) (F x1))); intros.
              eapply Rle_trans; eauto.
              unfold abs ; simpl.
              rewrite Rabs_pos_eq ; try (left ; lra).
              rewrite Rmult_assoc.
              apply Rmult_le_compat_l; try lra.
              generalize (norm_compat2 x1 x2 (mkposreal r0 H) H0) ; intros.
              simpl in H3.
              specialize (HF x1 x2 r0 H H0).
              destruct Hγ0.
              +++ assert (0 < γ*r0) by (apply Rmult_lt_0_compat; trivial).
                  generalize (norm_compat2 (F x1) (F x2) (mkposreal (γ*r0) H5) HF); intros.
                  replace (γ*r0) with (1*(γ*r0)) by lra.
                  simpl in H5.
                  left.
                  eapply Rlt_le_trans; eauto.
                  apply Rmult_le_compat_r; trivial.
                  now left.
              +++ subst.
                  replace (0*r0) with 0 in * by lra.
                  assert (F x1 = F x2) by (now apply ball_zero_eq).
                  rewrite H4.
                  rewrite minus_eq_zero.
                  right.
                  apply (@norm_zero R_AbsRing).
    Qed.

    (*TODO(Kody): Use this to simplify the proof above. *)
    Lemma is_contraction_falpha' (γ r : R) :
      0<=r<=1 -> (forall x y, norm(minus (F x) (F y)) <= γ*(norm (minus x y)))
      -> (forall x y,
      norm (minus (f_alpha F r x) (f_alpha F r y)) <=  (1-r+ γ*r)*norm(minus x y)).
    Proof.
      intros Hr HL x y.
      rewrite Rmult_plus_distr_r.
      unfold f_alpha.
      rewrite plus_minus_scal_distr.
      generalize (norm_triangle (scal (1-r) (minus x y)) (scal r (minus (F x) (F y)))) ; intros.
      eapply Rle_trans ; eauto.
      apply Rplus_le_compat.
      --  generalize (norm_scal (1-r) (minus x y)) ; intros.
          eapply Rle_trans ; eauto.
          unfold abs ; simpl.
          replace (Rabs (1-r)) with (1-r) by (symmetry; try apply Rabs_pos_eq;
                                              try (lra)).
          apply Rmult_le_compat_l ; try lra.
      --  generalize (norm_scal r (minus (F x) (F y))); intros.
          eapply Rle_trans; eauto.
          unfold abs ; simpl.
          rewrite Rabs_pos_eq ; try (left ; lra).
          replace (γ*r) with (r*γ) by lra.
          rewrite Rmult_assoc.
          apply Rmult_le_compat_l; try lra.
          apply HL.
          lra.
    Qed.

    (* The next few lemmas are in preparation for proving Theorem 2. *)

    (* Equation (9). *)
    Lemma xstar_fixpoint xstar :
      xstar = F xstar ->
      forall n, xstar = f_alpha F (α n) xstar.
    Proof.
      intros.
      unfold f_alpha.
      rewrite <- H.
      rewrite <- scal_distr_r.
      unfold plus; simpl.
      replace (1 - α n + α n) with 1 by lra.
      replace 1 with (@one R_AbsRing).
      now rewrite scal_one.
      reflexivity.
    Qed.

    Lemma prod_f_R0_Sn f n :
      prod_f_R0 f (S n) = prod_f_R0 f n * (f (S n)).
    Proof.
      now simpl.
    Qed.

    Lemma gamma_alpha_pos gamma :
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) ->
      forall n, 0 <= g_alpha gamma (α n).
    Proof.
      intros.
      apply Rge_le.
      apply Rge_minus.
      replace (1) with (1*1) at 1 by lra.
      specialize (H0 n).
      apply Rmult_ge_compat; lra.
    Qed.

    Lemma gamma_alpha_le_1 gamma :
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) ->
      forall n, g_alpha gamma (α n) <= 1.
    Proof.
      intros.
      assert (0 <= (1 - gamma) * α n).
      specialize (H0 n).
      apply Rmult_le_pos; lra.
      unfold g_alpha; lra.
    Qed.

    (* Lemma 1 *)
    Lemma f_alpha_contraction gamma a :
      0 <= gamma < 1 ->
      0 <= a <= 1 ->
      (forall x y, norm(minus (F x) (F y)) <= gamma * norm (minus x y)) ->
      forall x y, norm(minus (f_alpha F a x) (f_alpha F a y)) <= (g_alpha gamma a) * norm (minus x y).
    Proof.
      intros.
      unfold f_alpha, g_alpha.
      rewrite plus_minus_scal_distr.
      rewrite norm_triangle.
      rewrite (@norm_scal_R X).
      rewrite (@norm_scal_R X).
      unfold abs; simpl.
      repeat rewrite Rabs_right by lra.
      specialize (H1 x y).      
      apply Rmult_le_compat_l with (r := a) in H1; lra.
    Qed.
      
    Lemma RMsync_f_alpha n :
      RMsync (S n) = f_alpha F (α n) (RMsync n).
    Proof.
      now simpl.
    Qed.

    Lemma gamma_alpha_RMsync_ratio gamma xstar :
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) ->
      xstar = F xstar ->
      (forall x y, norm(minus (F x) (F y)) <= gamma * norm (minus x y)) ->
      forall n,
        norm (minus (RMsync (S n)) xstar) <= 
        (g_alpha gamma (α n)) * norm (minus (RMsync n) xstar).
      Proof.
        intros.
        replace (RMsync (S n)) with (f_alpha F (α n) (RMsync n)).
        replace (xstar) with (f_alpha F (α n) xstar) at 1.
        apply f_alpha_contraction; trivial.
        symmetry.
        now apply xstar_fixpoint.
        now simpl.
    Qed.

      (* Theorem 2, part a. *)

    Theorem Deterministic_RM_2a gamma xstar :
      0 <= gamma < 1 ->
      xstar = F xstar ->
      (forall n, 0 <= α n <= 1) ->
      (forall x y, norm(minus (F x) (F y)) <= gamma * norm (minus x y)) ->
      forall n, 
        norm (minus (RMsync (S n)) xstar) <= 
        norm (minus x0 xstar) * prod_f_R0 (fun k => g_alpha gamma (α k)) n.
      Proof.
        intros.
        generalize (gamma_alpha_RMsync_ratio gamma xstar H H1 H0 H2); intros.
        induction n.
        - unfold prod_f_R0.
          rewrite Rmult_comm.
          now apply H3.
        - specialize (H3 (S n)).
          rewrite Rmult_comm in H3.
          apply Rle_trans with (r2 := norm (minus (RMsync (S n)) xstar) * (g_alpha gamma (α (S n)))); trivial.
          rewrite prod_f_R0_Sn.
          rewrite <- Rmult_assoc.
          apply Rmult_le_compat_r.
          now apply gamma_alpha_pos.
          apply IHn.
      Qed.

      (* Theorem 2, part b. *)
    Theorem Deterministic_RM_2b gamma xstar :
      0 <= gamma < 1 ->
      xstar = F xstar ->
      (forall n, 0 <= α n <= 1) ->
      is_lim_seq (fun n => prod_f_R0 (fun k => g_alpha gamma (α k)) n) 0 ->
      (forall x y, norm(minus (F x) (F y)) <= gamma * norm (minus x y)) ->
      is_lim_seq (fun n => norm (minus (RMsync n) xstar)) 0.
    Proof.
      intros.
      generalize (Deterministic_RM_2a gamma xstar H H0 H1 H3); intros.
      rewrite is_lim_seq_incr_1.
      eapply is_lim_seq_le_le; intros.
      - split.
        + eapply norm_ge_0.
        + eapply H4.
      - apply is_lim_seq_const.
      - replace (Finite 0) with (Rbar_mult (norm (minus x0 xstar)) 0).
        now apply is_lim_seq_scal_l.
        apply Rbar_mult_0_r.
    Qed.

    Fixpoint list_product (l : list R) : R :=
      match l with
      | nil => 1
      | cons x xs => x*list_product xs
      end.

    (* Lemma 4.*)
    Lemma product_sum_helper (l : list R):
      List.Forall (fun r => 0 <= r <= 1) l -> 1 - list_sum l <= list_product (List.map (fun x => 1 - x) l).
    Proof.
      revert l.
      induction l.
      * simpl ; lra.
      * simpl. intros Hl.
        eapply Rle_trans with ((1-list_sum l)*(1-a)).
        ++ ring_simplify.
           apply Rplus_le_compat_r.
           do 2 rewrite Rle_minus_r.
           ring_simplify.
           inversion Hl ; subst.
           specialize (IHl H2). destruct H1.
           apply Rmult_le_pos ; trivial.
           apply list_sum_pos_pos'; trivial.
           generalize (List.Forall_and_inv _ _ H2); intros.
           destruct H1; trivial.
        ++ inversion Hl; subst.
           specialize (IHl H2).
           rewrite Rmult_comm.
           apply Rmult_le_compat_l ; trivial.
           lra.
    Qed.

  End qlearn.

  Section qlearn2.

    Context {X : CompleteNormedModule R_AbsRing}.

    Lemma product_sum_assumption_a_lt_1 (α : nat -> R) (gamma:R) (k:nat):
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) ->
      (forall n, 0 <= (1-gamma)* α (n+k)%nat < 1) ->
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      is_lim_seq (fun n => prod_f_R0 (fun m => g_alpha gamma (α (m + k)%nat)) n) 0.
      Proof.
        intros.
        assert (forall n, 0 <= (1-gamma)* α (n+k)%nat < 1) by (intros; apply H1).
        generalize (Fprod_0 (fun n => (1-gamma)* α (n+k)%nat) H4); intros.
        apply is_lim_seq_ext with (v := (fun n : nat => prod_f_R0 (fun m : nat => g_alpha gamma (α (m + k)%nat)) n)) in H5.
        apply H5.
        induction n.
        - unfold part_prod, part_prod_n, g_alpha.
          simpl; lra.
        - simpl.
          unfold part_prod, g_alpha.
          simpl.
          rewrite part_prod_n_S; [|lia].
          unfold part_prod in IHn.
          rewrite IHn.
          reflexivity.
        - unfold l1_divergent.
          apply is_lim_seq_ext with 
              (u := (fun m => (1-gamma) * (sum_n  (fun n => α (n + k)%nat) m))).
          + intros.
            generalize (sum_n_mult_l (1-gamma) (fun n => α (n + k)%nat) n); intros.
            unfold Hierarchy.mult in H6; simpl in H6.
            symmetry.
            apply H6.
          + replace (p_infty) with (Rbar_mult (1-gamma) p_infty).
            * apply is_lim_seq_scal_l.
              destruct (Nat.eq_dec k 0).
              -- subst.
                 apply is_lim_seq_ext with (u := (sum_n α)); trivial.
                 intros; apply sum_n_ext.
                 intros; f_equal.
                 lia.
              -- assert (k > 0)%nat by lia.
                 apply is_lim_seq_ext with
                     (u := fun m => minus (sum_n α (m + k)%nat) (sum_n α (k-1)%nat)).
                 ++ intros.
                    rewrite <- sum_n_m_sum_n; trivial; try lia.
                    replace (S (k-1)%nat) with (k) by lia.
                    apply sum_n_m_shift.
                 ++ apply is_lim_seq_minus with 
                        (l1 := p_infty) (l2 := sum_n α (k - 1)).
                    ** eapply is_lim_seq_incr_n in H3.
                       apply H3.
                    ** apply is_lim_seq_const.
                    ** unfold is_Rbar_minus, is_Rbar_plus, Rbar_opp.
                       now simpl.
            * rewrite Rbar_mult_comm.
              rewrite Rbar_mult_p_infty_pos; trivial.
              lra.
      Qed.

      Lemma prod_f_R0_n (f : nat -> R) (n : nat) :
        f n = 0 ->
        prod_f_R0 f n = 0.
      Proof.
        intros.
        destruct (Nat.eq_dec n 0).
        - subst.
          now simpl.
        - replace (n) with (S (n-1)) by lia.
          rewrite prod_f_R0_Sn.
          replace (S (n - 1)) with n by lia.
          rewrite H.
          apply Rmult_0_r.
       Qed.

      Lemma prod_f_R0_n1_n2 (f : nat -> R) (n1 n2 : nat) :
        (n1 <= n2)%nat ->
        f n1 = 0 ->
        prod_f_R0 f n2 = 0.
      Proof.
        intros.
        destruct (lt_dec n1 n2).
        - rewrite prod_SO_split with (k := n1) (n := n2); trivial.
          rewrite prod_f_R0_n; trivial.
          apply Rmult_0_l.
        - assert (n1 = n2) by lia.
          rewrite H1 in H0.
          now apply prod_f_R0_n.
      Qed.

      (* Lemma 3, part a *)
      Lemma product_sum_assumption_a (α : nat -> R) gamma :
        0 <= gamma < 1 ->
        (forall n, 0 <= α n <= 1) ->
        is_lim_seq α 0 ->
        is_lim_seq (sum_n α) p_infty ->
        forall k, is_lim_seq (fun n => prod_f_R0 (fun m => g_alpha gamma (α (m + k)%nat)) n) 0.
      Proof.
        intros.
        assert (abounds: forall n, 0 <= (1-gamma)* α (n + k)%nat <= 1).
        {
          intros n.
          split.
          - apply Rmult_le_pos; [lra | ].
            apply H0.
          - assert (0 < 1-gamma <= 1) by lra.
            destruct H3.
            apply Rmult_le_compat_r with (r :=  α (n + k)%nat) in H4; [|apply H0].
            rewrite Rmult_1_l in H4.
            apply Rle_trans with (r2 := α (n + k)%nat); trivial.
            apply H0.
        }
        
        destruct (classic (exists n,  (1-gamma) * α (n+k)%nat = 1)) as [[n an1] | Hnex].
        - unfold g_alpha.
          apply is_lim_seq_le_le_loc with (u := fun _ => 0) (w := fun _ => 0)
             ; [| apply is_lim_seq_const | apply is_lim_seq_const].
          exists n; intros.
          replace (prod_f_R0 (fun m : nat => 1 - (1 - gamma) * α (m + k)%nat) n0) with 0.
          lra.
          rewrite prod_f_R0_n1_n2 with (n1 := n); trivial.
          rewrite an1.
          lra.
        - assert (abounds':forall n, 0 <= (1-gamma)* α (n + k)%nat < 1).
          {
            intros n.
            destruct (abounds n).
            split; trivial.
            destruct H4; trivial.
            elim Hnex; eauto.
          }
          apply product_sum_assumption_a_lt_1; trivial.
      Qed.

    Lemma product_sum_assumption_b_helper (g_α : nat -> R) :
      (forall n, 0 <= g_α n <= 1) ->
      ex_series g_α ->
      exists N, Lim_seq (sum_n_m g_α N) < 1.
    Proof.
      intros.
      generalize (Cauchy_ex_series _ H0); intros.
      unfold Cauchy_series in H1.
      specialize (H1 posreal_half).
      destruct H1 as [N H1].
      unfold norm in H1; simpl in H1.
      unfold abs in H1; simpl in H1.
      assert (Lim_seq (fun n => sum_n_m g_α (S N) n) < 1).
      generalize (Lim_seq_le_loc (fun n => sum_n_m g_α (S N) n) (fun _ => /2)); intros.
      rewrite Lim_seq_const in H2.
      unfold ex_series in H0.
      destruct H0.
      unfold is_series in H0.
      assert (is_lim_seq (sum_n g_α) x).
      unfold is_lim_seq.
      apply H0.
      assert (ex_finite_lim_seq (fun n : nat => sum_n_m g_α (S N) n)).
      unfold ex_finite_lim_seq.
      exists (x - (sum_n g_α N)).
      apply is_lim_seq_ext_loc with 
        (u := (fun n => minus (sum_n g_α n) (sum_n g_α N))).
      exists N.
      intros.
      rewrite sum_n_m_sum_n; trivial.
      apply is_lim_seq_minus'; trivial.
      apply is_lim_seq_const.
      unfold ex_finite_lim_seq in H4.
      destruct H4.
      apply is_lim_seq_unique in H4.
      rewrite H4.
      rewrite H4 in H2.
      simpl in H2.
      apply Rle_lt_trans with (r2 := /2); try lra.
      apply H2.
      exists (S N).
      intros.
      specialize (H1 (S N) n).
      left.
      rewrite Rabs_right in H1.
      apply H1.
      lia.
      lia.
      replace 0 with (sum_n_m (fun _ => 0) (S N) n).
      apply Rle_ge.
      apply sum_n_m_le.
      apply H.
      generalize (@sum_n_m_const_zero R_AbsRing (S N) n).
      now unfold zero; simpl.
      eexists.
      apply H2.
    Qed.

    Lemma sum_f_bound (f : nat -> R) (N : nat) (C : R) :
      (forall n, (n<=N)%nat -> 0 <= f n) ->
      sum_n f N < C ->
      (forall n, (n<=N)%nat -> f n < C).
    Proof.
      intros.
      induction N.
      - unfold sum_n in H0; simpl in H0.
        rewrite sum_n_n in H0.
        assert (n = 0%nat ) by lia.
        rewrite H2.
        apply H0.
      - destruct (le_dec n N).
        + apply IHN; trivial.
          intros; apply H; lia.
          rewrite sum_S in H0.
          apply Rle_lt_trans with (r2 := sum_n f N + f (S N)); trivial.
          replace (sum_n f N) with ((sum_n f N) + 0) at 1 by lra.
          apply Rplus_le_compat_l.
          apply H; lia.
        + assert (n = S N) by lia.
          rewrite H2.
          apply Rle_lt_trans with (r2 := sum_n f (S N)); trivial.
          rewrite sum_S.
          replace (f (S N)) with (0 + (f (S N))) at 1 by lra.
          apply Rplus_le_compat_r.
          apply sum_n_nneg.
          intros; apply H; lia.
    Qed.

    Lemma product_sum_helper_fun (x : nat -> R) (N : nat) :
      (forall n, (n<=N)%nat -> 0 <= x n <= 1) ->
      prod_f_R0 (fun n => 1 - x n) N >= 1 - sum_n x N.
    Proof.
      intros.
      induction N.
      - simpl.
        rewrite sum_O.
        lra.
      - simpl.
        rewrite sum_S.
        cut_to IHN.
        + apply Rge_trans with (r2 := (1-sum_n x N) * (1 - x (S N))).
          * apply Rmult_ge_compat_r; trivial.
            specialize (H (S N)).
            cut_to H; try lia.
            lra.
          * rewrite Rmult_minus_distr_r.
            rewrite Rmult_1_l.
            rewrite Rmult_minus_distr_l.
            rewrite Rmult_1_r.
            apply Rge_trans with (r2 := 1 - x (S N) - sum_n x N); [ | lra].
            unfold Rminus.
            apply Rplus_ge_compat_l.
            ring_simplify.
            replace (- sum_n x N) with (0 - sum_n x N) by lra.
            unfold Rminus.
            apply Rplus_ge_compat_r.
            apply Rle_ge.
            apply Rmult_le_pos.
            -- apply sum_n_nneg.
               intros; apply H; lia.
            -- apply H; lia.
        + intros; apply H; lia.
     Qed.

    Lemma product_sum_helper_lim (α : nat -> R) (N:nat) :
        (forall n, 0 <= α n <= 1) ->
        ex_finite_lim_seq (fun n => sum_n_m α N (n + N)%nat) ->
        Lim_seq (sum_n_m α N) < 1 ->
        Rbar_lt 0 (Lim_seq (fun m => prod_f_R0 (fun n => 1 - (α (n + N)%nat)) m)).
      Proof.
        generalize (Lim_seq_le_loc (fun n => 1 - sum_n_m α N (n+N)%nat) (fun n => prod_f_R0 (fun k => 1 - α (k + N)%nat) n)); intros.
        apply ex_finite_lim_seq_correct in H1.
        destruct H1.
        generalize (Lim_seq_incr_n (sum_n_m α N) N); intros.
        rewrite <- H4 in H2.
        cut_to H.
        - rewrite Lim_seq_minus, Lim_seq_const in H; trivial.
          + apply Rbar_lt_le_trans with (y := (Rbar_minus 1 (Lim_seq (fun n : nat => sum_n_m α N (n + N))))); trivial.
            rewrite <- H3.
            simpl.
            simpl; lra.
          + apply ex_lim_seq_const.
          + rewrite Lim_seq_const.
            rewrite <- H3.
            now simpl.
        - exists (0%nat); intros.
          apply Rge_le.
          generalize (product_sum_helper_fun (fun n => α (n + N)%nat)); intros.
          replace (sum_n_m α N (n + N)) with (sum_n (fun n => α (n + N)%nat) n).
          apply H6.
          intros; apply H0.
          symmetry.
          apply sum_n_m_shift.
     Qed.

      Lemma series_finite_sum (a : nat -> R) :
        ex_series a ->
        ex_finite_lim_seq (sum_n a).
      Proof.
        unfold ex_series, is_series, ex_finite_lim_seq, is_lim_seq; intros.
        apply H.
      Qed.

      Lemma series_finite_sum_shift (a : nat -> R) (N:nat) :
        ex_series a ->
        ex_finite_lim_seq (fun n => sum_n_m a N (n + N)).
      Proof.
        intros.
        assert (ex_series (fun n => a (n + N)%nat)).
        apply ex_series_incr_n with (n := N) in H.
        apply ex_series_ext with (a0 := (fun k : nat => a (N + k)%nat)); trivial.
        intros; f_equal; lia.
        generalize (series_finite_sum _ H0); intros.
        unfold ex_finite_lim_seq in H1.
        destruct H1.
        apply is_lim_seq_ext with (v := (fun n : nat => sum_n_m a N (n + N)) ) in H1.
        exists x.
        apply H1.
        intros.
        now rewrite sum_n_m_shift.
     Qed.

    (* Lemma 3, part b *)
    Lemma product_sum_assumption_b (α : nat -> R) gamma :
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) ->
      is_lim_seq α 0 ->
      (forall k, is_lim_seq (fun n => prod_f_R0 (fun m => g_alpha gamma (α (m + k)%nat)) n) 0) ->
      is_lim_seq (sum_n α) p_infty.
    Proof.
      intros gbounds abounds alim.
      rewrite <- Decidable.contrapositive; [|apply classic].
      intros.
      assert (asum: ex_series (fun n => α n)).
      {
        rewrite <- is_lim_seq_spec in H.
        unfold is_lim_seq' in H.
        apply not_all_ex_not in H.
        destruct H as [M H].
        unfold eventually in H.
        generalize (not_ex_all_not _ _ H); intros HH.
        assert (HH1:forall n : nat, exists n0 : nat, (n <= n0)%nat /\ sum_n α n0 <= M).
        {
          intros n; specialize (HH n).
          apply not_all_ex_not in HH.
          destruct HH as [x HH2].
          apply imply_to_and in HH2.
          destruct HH2.
          exists x.
          split; trivial.
          lra.
        }
        assert (HH2: forall n : nat, sum_n α n <= M).
        {
          intros n.
          destruct (HH1 n) as [n0 [nle nbound]].
          generalize (sum_n_pos_incr α n n0); intros.
          apply Rle_trans with (r2 := sum_n α n0); trivial.
          apply H1; trivial.
          intros.
          apply abounds.
        }
        unfold ex_series.
        unfold is_series.
        generalize (ex_lim_seq_incr (sum_n α)); intros.
        unfold ex_lim_seq in H1.
        cut_to H1.
        - destruct H1.
          generalize (is_lim_seq_le (sum_n α) (fun _ => M) x M HH2 H1); intros.
          generalize (is_lim_seq_le (fun _ => 0) (sum_n α) 0 x); intros.
          cut_to H2; [|apply is_lim_seq_const].
          cut_to H3.
          + generalize (bounded_is_finite 0 M x H3 H2); intros.
            rewrite <- H4 in H1.
            exists (real x).
            apply H1.
          + intros.
            rewrite <- sum_n_zero with (n := n).
            unfold sum_n.
            apply sum_n_m_le.
            apply abounds.
          + apply is_lim_seq_const.
          + apply H1.
        - intros.
          rewrite sum_Sn.
          replace (sum_n α n) with ((sum_n α n) + 0) at 1 by lra.
          apply Rplus_le_compat_l.
          apply abounds.
      }
      assert (gasum: ex_series (fun n => (1-gamma)* (α n))).
      now apply ex_series_scal with (c := 1-gamma) (a := α).
      assert (ga_pos: forall n, 0 <= (1 - gamma) * α n).
      {
        intros.
        apply Rmult_le_pos; [lra|].
        apply abounds.
      }
      assert (ga_bounds : (forall n : nat, 0 <= (1 - gamma) * α n <= 1)).
      {
        intros; split; [apply ga_pos|].
        assert (0 < 1-gamma <= 1) by lra.
        destruct H1.
        apply Rmult_le_compat_r with (r :=  α n) in H2; [|apply abounds].
        rewrite Rmult_1_l in H2.
        apply Rle_trans with (r2 := α n); trivial.
        apply abounds.
      }
      generalize (product_sum_assumption_b_helper (fun n => (1-gamma) * α n) ga_bounds gasum); intros.
      destruct H1.
      generalize (product_sum_helper_lim (fun n => (1-gamma) * α n) x ga_bounds); intros.
      specialize (H0 x).
      apply is_lim_seq_unique in H0.
      unfold g_alpha in H0.
      rewrite H0 in H2.
      simpl in H2.
      cut_to H2; trivial.
      lra.
      now apply series_finite_sum_shift.
    Qed.

    Fixpoint RMseq (α : nat -> R) (s : nat -> R) (init : R) (n : nat) : R :=
      match n with
      | 0 => init
      | (S k) => plus (scal (1 - α k) (RMseq α s init k)) (scal (α k) (s k))
      end.

    (* Lemma 5.*)
    Lemma helper_bounding_5 (α : nat -> R) (s1 s2 : nat -> R) (init1 init2 : R) :
      0 <= init1 <= init2 ->
      (forall n, 0 <= (α n) <= 1) ->
      (forall n, 0 <= s1 n <= s2 n) ->
      forall n, 0 <= RMseq α s1 init1 n <= RMseq α s2 init2 n.
    Proof.
      intros.
      induction n.
      - now unfold RMseq.
      - simpl.
        unfold plus, scal; simpl.
        unfold mult; simpl.
        specialize (H0 n).
        specialize (H1 n).
        split.
        + apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra.
        + apply Rplus_le_compat; apply Rmult_le_compat_l; lra.
     Qed.

    Fixpoint RMseqX (α : nat -> R) (f : nat -> X -> X) (init : X) (n : nat) : X :=
      match n with
      | 0 => init
      | (S k) => plus (scal (1 - α k) (RMseqX α f init k)) (scal (α k) (f k (RMseqX α f init k)))
      end.
      
    Fixpoint RMseqG (α : nat -> R) (init gamma C : R) (n : nat) : R :=
      match n with
      | 0 => init
      | (S k) => plus (scal (g_alpha gamma (α k)) (RMseqG α init gamma C k)) (scal (α k) C)
      end.

    Lemma RMseq_shift (α : nat -> R) (delta : nat -> R) (init : R) (N n : nat) :
      RMseq (fun n =>  α (N + n)%nat) 
            (fun n : nat => delta (N + n)%nat) (RMseq α delta init N) n  = 
      RMseq α delta init (N + n)%nat.
    Proof.
      induction n.
      - simpl.
        f_equal.
        lia.
      - replace (N + S n)%nat with (S (N + n)%nat) by lia.
        simpl.
        rewrite IHn.
        reflexivity.
      Qed.

    (* Lemma 6. *)
    Lemma helper_convergence_6 (α : nat -> R) (delta : nat -> R) (init:R) :
      0 <= init ->
      (forall n, 0 <= (α n) <= 1) ->
      (forall n, 0 <= delta n) ->
      is_lim_seq α 0 ->
      is_lim_seq delta 0 ->
      (forall k, is_lim_seq (fun n => prod_f_R0 (fun m => 1 - (α (m + k)%nat)) n) 0) ->
      is_lim_seq (RMseq α delta init) 0.
    Proof.
      intros.
      rewrite <- is_lim_seq_spec in H3.
      unfold is_lim_seq' in H3.
      rewrite <- is_lim_seq_spec.
      unfold is_lim_seq'.
      intros.
      generalize (cond_pos eps); intros.
      assert (0 < eps/2) by lra.
      specialize (H3 (mkposreal _ H6)).
      destruct H3 as [N H3].
      simpl in H3.
      generalize (helper_bounding_5 (fun n => α (N+n)%nat)
                                    (fun n => delta (N+n)%nat) 
                                    (fun _ => eps/2) 
                                    (RMseq α delta init N) (RMseq α delta init N)); intros.
      generalize (@Deterministic_RM_2b R_CompleteNormedModule (fun _ => eps/2) (fun n => α (N+n)%nat) (RMseq α delta init N) 0 (eps/2)); intros.
      assert (is_lim_seq (fun n : nat => (RMseq (fun n => α (N+n)%nat) (fun _ => eps/2) 
                                                (RMseq α delta init N) n)) (eps / 2)).
      {
        rewrite <- is_lim_seq_abs_0 in H8.
        generalize (is_lim_seq_const (eps/2)); intros.
        cut_to H8; trivial.
        - generalize (is_lim_seq_plus' _ _ _ _ H8 H9); intros.
          rewrite Rplus_0_l in H10.
          apply is_lim_seq_ext with 
              (v := (fun n => (@RMsync R_CompleteNormedModule (fun _ => eps/2) (fun n => α (N+n)%nat) 
                                       (RMseq α delta init N) n)) ) in H10.
          + apply is_lim_seq_ext with (v :=  (RMseq (fun n => α (N+n)%nat) (fun _ => eps/2)
                                                    (RMseq α delta init N))) in H10.
            * apply H10.
            * induction n.
              -- now unfold RMsync, RMseq.
              -- simpl.
                 unfold plus, scal, mult; simpl.
                 unfold Hierarchy.mult; simpl.
                 rewrite <- IHn.
                 reflexivity.
          + intro.
            unfold minus; simpl.
            unfold plus, opp; simpl.
            lra.
        - lra.
        - unfold g_alpha.
          specialize (H4 N).
          apply is_lim_seq_ext with (u := (fun n : nat => prod_f_R0 (fun m : nat => 1 - α (m + N)%nat) n)).
          intro n.
          apply prod_f_R0_proper; trivial.
          intro x.
          ring_simplify.
          do 3 f_equal.
          lia.
          apply H4.
        - intros.
          unfold minus, norm; simpl.
          unfold abs, plus, opp; simpl.
          ring_simplify.
          replace (eps / 2 + - (eps / 2)) with (0) by lra.
          right.
          apply Rabs_R0.
      }
      rewrite <- is_lim_seq_spec in H9.
      unfold is_lim_seq' in H9.
      specialize (H9 (mkposreal _ H6)).
      destruct H9 as [Neps H9]; simpl in H9.
      exists (N + Neps)%nat; intros.
      rewrite Rminus_0_r.
      assert (Neps <= (n - N))%nat by lia.
      specialize (H9 (n-N)%nat H11); simpl in H9.
      generalize (Rabs_triang_inv (RMseq (fun n : nat => α (N + n)%nat) (fun _ : nat => eps / 2) (RMseq α delta init N) (n-N)) (eps/2)); intros.
      generalize (Rle_lt_trans _ _ _ H12 H9); intros.
      rewrite Rabs_right with (r := eps/2) in H13; [| lra].
      apply Rplus_lt_compat_r with (r := eps/2) in H13.
      ring_simplify in H13.
      replace (2 * (eps/2)) with (pos eps) in H13 by lra.
      cut_to H7; trivial.
      - specialize (H7 (n-N)%nat).
        destruct H7.
        generalize (RMseq_shift α delta init N (n-N)); intros.
        replace (N + (n -N))%nat with n in H15 by lia.
        generalize (Rle_trans _ _ _ H7 H14); intros.
        rewrite H15 in H14.
        rewrite Rabs_right in H13.
        generalize (Rle_lt_trans _ _ _ H14 H13); intros.
        rewrite Rabs_right.
        apply H17.
        generalize (helper_bounding_5  α delta delta init init); intros.
        cut_to H18; trivial; try lra.
        intros.
        split; [| lra].
        apply H1.
        now apply Rle_ge.
      - apply helper_bounding_5; trivial; try lra.
        split; try lra.
        apply H1.
      - intros; split.
        + apply H1.
        + specialize (H3 (N + n0)%nat).
          rewrite Rabs_right in H3.
          * rewrite Rminus_0_r in H3.
            left.
            apply H3.
            lia.
          * rewrite Rminus_0_r.
            apply Rle_ge.
            apply H1.
     Qed.

    Lemma finite_lim_bound (f : nat -> R) (lim : R) :
      is_lim_seq f lim ->
      exists (B:R), forall n, f n <= B.
    Proof.
      generalize (filterlim_bounded f); intros.
      cut_to H.
      - destruct H.
        exists x; intros.
        unfold norm in r; simpl in r.
        unfold abs in r; simpl in r.
        eapply Rle_trans.
        + apply Rle_abs.
        + apply r.
      - exists lim.
        apply H0.
    Qed.

    (* Lemma 7. *)
    Lemma bounding_7  (α : nat -> R) (gamma C : R) (f : nat -> X -> X) (init : X) :
      0 <= gamma < 1 -> 0 <= C ->
      (forall n, 0 <= (α n) <= 1) ->
      (forall n x, norm (f n x) <= gamma * norm x + C) ->
      is_lim_seq α 0 ->
      (forall k, is_lim_seq (fun n => prod_f_R0 (fun m => g_alpha gamma (α (m+k)%nat)) n) 0) ->
      exists B, forall n, norm ( RMseqX α f init n) <= B.
    Proof.
      intros.
      assert (forall n, norm(RMseqX α f init (S n)) <= (1 - α n)*norm(RMseqX α f init n) + (α n)*(gamma * norm (RMseqX α f init n) + C)).
      {
        intros.
        simpl.
        specialize (H1 n).
        eapply Rle_trans.
        generalize (@norm_triangle R_AbsRing X); intros.
        apply H5.
        do 2 rewrite (@norm_scal_R X).
        unfold abs; simpl.
        rewrite Rabs_right; try lra.
        rewrite Rabs_right; try lra.
        apply Rplus_le_compat_l.
        apply Rmult_le_compat_l; try lra.
        apply H2.
      }

      assert (forall n,  norm(RMseqX α f init (S n)) <= (g_alpha gamma  (α n)) * norm(RMseqX α f init n) + (α n)*C).
      {
        intros.
        eapply Rle_trans.
        apply H5.
        unfold g_alpha.
        lra.
     }

      assert (forall n, norm(RMseqX α f init n) <= RMseqG α (norm init) gamma C n).
      { 
        induction n.
        - unfold RMseqX, RMseqG; lra.
        - simpl.
          unfold g_alpha.
          eapply Rle_trans.
          apply H5.
          unfold scal; simpl.
          unfold mult; simpl.
          rewrite Rmult_plus_distr_l. 
          rewrite <- Rmult_assoc.
          rewrite <- Rplus_assoc.
          rewrite <- Rmult_plus_distr_r. 
          unfold plus; simpl.
          apply Rplus_le_compat_r.
          replace (1 - α n + α n * gamma) with (1 - (1 - gamma) * α n) by lra.
          apply Rmult_le_compat_l.
          apply  gamma_alpha_pos; trivial.
          apply IHn.
      }
      
      generalize (@Deterministic_RM_2b R_CompleteNormedModule (fun s => gamma * s + C) α (norm init) gamma (C/(1-gamma)) H); intros.
      assert (exists B2, forall n, RMseqG α (norm init) gamma C n <= B2).
      {
        cut_to H8; trivial.
        - apply finite_lim_bound with (lim := C / (1 - gamma)).
          rewrite <- is_lim_seq_abs_0 in H8.
          generalize (is_lim_seq_const (C / (1 - gamma))); intros.
          generalize (is_lim_seq_plus' _ _ _ _ H8 H9); intros.
          rewrite Rplus_0_l in H10.
          apply is_lim_seq_ext with (v := (fun n => (@RMsync R_CompleteNormedModule (fun s => gamma * s + C) α (norm init) n)) ) in H10.
          + apply is_lim_seq_ext with (v :=  (RMseqG α (norm init) gamma C)) in H10.
            * apply H10.
            * induction n.
              -- now unfold RMsync, RMseqG.
              -- simpl.
                 unfold g_alpha.
                 unfold plus, scal, mult; simpl.
                 unfold Hierarchy.mult; simpl.
                 rewrite <- IHn.
                 ring_simplify.
                 apply Rplus_eq_compat_r.
                 rewrite Rmult_assoc.
                 rewrite Rmult_comm with (r2 := gamma).
                 rewrite <- Rmult_assoc.
                 unfold Rminus.
                 do 2 rewrite Rplus_assoc.
                 apply Rplus_eq_compat_l.
                 now rewrite Rplus_comm.
          + intros.
            unfold minus; simpl.
            unfold plus; simpl.
            unfold opp; simpl.
            now ring_simplify.
        - simpl; field; lra.
        - specialize (H4 0%nat).
          apply is_lim_seq_ext with (u := (fun n : nat => prod_f_R0 (fun k : nat => g_alpha gamma (α (k + 0)%nat)) n)); intros.
          apply prod_f_R0_proper; trivial; intro x.
          f_equal; f_equal; lia.
          apply H4.
        - intros.
          unfold minus, plus, opp; simpl.
          right.
          unfold norm; simpl.
          unfold abs; simpl.
          replace (gamma * x + C + - (gamma * y + C)) with (gamma * (x + - y)) by lra.
          rewrite Rabs_mult, Rabs_right; lra.
      }
      destruct H9.
      exists x.
      intros.
      eapply Rle_trans.
      apply H7.
      apply H9.
    Qed.

  End qlearn2.

  Section qlearn3.
    
  Import hilbert.
  Context {I : nat}.
  Canonical Rvector_UniformSpace := @PreHilbert_UniformSpace (@Rvector_PreHilbert I).
  Canonical Rvector_NormedModule := @PreHilbert_NormedModule (@Rvector_PreHilbert I).
  Canonical Rvector_CompleteNormedModule :=
       @Hilbert_CompleteNormedModule (@Rvector_Hilbert I).

  Context (gamma : R) (α : nat -> R) {F : vector R I -> vector R I} {Ts : Type}
          {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

    Global Instance positive_inner (f : Ts -> vector R I) :
      PositiveRandomVariable (fun v => inner (f v) (f v) ).
    Proof.
      unfold PositiveRandomVariable.
      intros.
      apply inner_ge_0.
    Qed.

    Lemma forall_expectation_ext {rv1 rv2 : nat -> Ts -> R} :
      (forall n, rv_eq (rv1 n) (rv2 n)) ->
      forall n, Expectation (rv1 n) = Expectation (rv2 n).
    Proof.
      intros.
      now apply Expectation_ext.
    Qed.

    Lemma forall_SimpleRandomVariable_ext {rv1 rv2 : nat -> Ts -> R} 
          {srv1 : forall n, SimpleRandomVariable (rv1 n)} :
      (forall n, rv_eq (rv1 n) (rv2 n)) ->
      forall n, SimpleRandomVariable (rv2 n).
    Proof.
      intros.
      specialize (srv1 n).
      specialize (H n).
      generalize (SimpleRandomVariable_ext _ _ H srv1).
      trivial.
    Qed.

    Lemma forall_SimpleExpectation_ext {rv1 rv2 : nat -> Ts -> R}
          {rrv1 : forall n, RandomVariable dom borel_sa (rv1 n)}
          {srv1 : forall n, SimpleRandomVariable (rv1 n)}
          {rrv2 : forall n, RandomVariable dom borel_sa (rv2 n)}
          {srv2 : forall n, SimpleRandomVariable (rv2 n)} :
      (forall n, rv_eq (rv1 n) (rv2 n)) ->
      forall n, SimpleExpectation (rv1 n) = SimpleExpectation (rv2 n).
    Proof.
      intros.
      now apply SimpleExpectation_ext.
    Qed.

    Lemma isfinexp_finite_neg_part (rv_X : Ts -> R)
          {rv : RandomVariable dom borel_sa rv_X} :
      IsFiniteExpectation prts rv_X ->
      is_finite (Expectation_posRV (neg_fun_part rv_X)).
    Proof.
      intros.
      apply IsFiniteExpectation_Finite in H.
      destruct H.
      unfold neg_fun_part, is_finite; simpl.
      unfold Expectation in e.
      unfold Rbar_minus' in e.
      simpl in e.
      unfold Rbar_plus', Rbar_opp in e.
      match_destr_in e.
      - match_case_in e; intros; match_case_in H; intros; rewrite H0 in H
        ; try discriminate.
        + rewrite H0 in e; inversion e.
        + rewrite H0 in e; inversion e.          
      - match_case_in e; intros; match_case_in H; intros; rewrite H0 in H
        ; try discriminate.
        + rewrite H0 in e; inversion e.
        + rewrite H0 in e; inversion e.          
      - match_case_in e; intros; match_case_in H; intros; rewrite H0 in H
        ; try discriminate.
        + rewrite H0 in e; inversion e.
        + rewrite H0 in e; inversion e.          
   Qed.

  Lemma Expectation_pos_finite_neg_part (rv_X : Ts -> R) 
        {prv : PositiveRandomVariable rv_X} :
    is_finite (Expectation_posRV (neg_fun_part rv_X)).
  Proof.
    unfold neg_fun_part; simpl.
    unfold PositiveRandomVariable in prv.
    assert (rv_eq (fun x : Ts => Rmax (- rv_X x) 0) (const 0)).
    intro x.
    specialize (prv x).
    unfold const.
    rewrite Rmax_right; lra.
    rewrite (Expectation_posRV_re H).
    assert (0 <= 0) by lra.
    generalize (Expectation_posRV_const 0 H0); intros.
    erewrite Expectation_posRV_pf_irrel.
    rewrite H1.
    reflexivity.
  Qed.

  Lemma Expectation_sum_first_finite_snd_pos 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {prv2 : PositiveRandomVariable rv_X2} :
    forall (e1:R) (e2 : Rbar), 
      Expectation rv_X1 = Some (Finite e1) ->
      Expectation rv_X2 = Some e2 ->
      Expectation (rvplus rv_X1 rv_X2) = Some (Rbar_plus e1 e2).
  Proof.
    intros.
    generalize (isfinexp_finite_neg_part rv_X1); intros.
    cut_to H1.
    generalize (Expectation_pos_finite_neg_part rv_X2); intros.
    generalize (Expectation_sum rv_X1 rv_X2 H1 H2); intros.
    rewrite H in H3.
    rewrite H0 in H3.
    apply H3.
    unfold IsFiniteExpectation.
    now rewrite H.
 Qed.


   Lemma rv_inner_plus_l (x y z : vector R I) :
     Rvector_inner (Rvector_plus x y) z = 
     (Rvector_inner x z) + (Rvector_inner y z).
   Proof.
     apply (inner_plus_l x y z).
   Qed.

   Lemma rv_inner_plus_r (x y z : vector R I) :
     Rvector_inner x (Rvector_plus y z) = 
     (Rvector_inner x y) + (Rvector_inner x z).
    Proof.
      apply (inner_plus_r x y z).
    Qed.
   
   Lemma rv_inner_scal_l (x y : vector R I) (l : R) :
     Rvector_inner (Rvector_scale l x) y = l * Rvector_inner x y.
   Proof.
     apply (inner_scal_l x y l).
   Qed.

   Lemma rv_inner_scal_r (x y : vector R I) (l : R) :
     Rvector_inner x (Rvector_scale l y) = l * Rvector_inner x y.
   Proof.
     apply (inner_scal_r x y l).
   Qed.

   Lemma rv_inner_sym (x y : vector R I) :
     Rvector_inner x y = Rvector_inner y x.
   Proof.
     apply (inner_sym x y).
   Qed.

   Lemma rv_inner_ge_0 (x : vector R I) :
      0 <= Rvector_inner x x.
   Proof.
     apply (inner_ge_0 x).
   Qed.

   Existing Instance rv_fun_simple_Rvector.

   Definition F_alpha (a : R) (x : Ts -> vector R I) :=
     vecrvplus (vecrvscale (1-a) x) (vecrvscale a (fun v => F (x v))).


   Instance rv_Fa (a:R) (x: Ts -> vector R I) 
            (rvx : RandomVariable dom (Rvector_borel_sa I) x) 
            (srvx : SimpleRandomVariable x) :
     RandomVariable dom (Rvector_borel_sa I) (F_alpha a x).
   Proof.
     eapply srv_singleton_rv; intros.
     apply (sa_preimage_singleton (σ:=Rvector_borel_sa I)).
     unfold F_alpha.
     typeclasses eauto.
  Qed.
   
   Lemma L2_convergent_helper (C : R) (w x : nat -> Ts -> vector R I) (xstar : vector R I) (n:nat)
         (rx : forall n, RandomVariable dom (Rvector_borel_sa I) (x n))
         (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n))
         (srw : forall n, SimpleRandomVariable  (w n)) 
         (srx : forall n, SimpleRandomVariable  (x n)) :
     (forall k, (x (S k)) = 
                 vecrvplus (F_alpha (α k) (x k))
                           (vecrvscale (α k) (w k))) ->
     SimpleExpectation
       (rvinner
          (vecrvminus (F_alpha (α n) (x n)) 
                      (const xstar))
          (w n)) = zero ->
     
     rv_le (rvinner (vecrvminus (F_alpha (α n) (x n))
                                (const xstar))
                    (vecrvminus (F_alpha (α n) (x n))
                                (const xstar)))
           (rvscale ((g_alpha gamma (α n))^2)
                    (rvinner (vecrvminus (x n) (const xstar))
                             (vecrvminus (x n) (const xstar)))) ->
           
     SimpleExpectation (rvinner (w n) (w n)) < C  ->
      
     SimpleExpectation (rvinner (vecrvminus (x (S n)) (const xstar))
                                (vecrvminus (x (S n)) (const xstar))) <=
     ((g_alpha gamma (α n))^2) *
     (SimpleExpectation
        (rvinner (vecrvminus (x n) (const xstar))
                 (vecrvminus (x n) (const xstar))))
       + (α n)^2 * C.
    Proof.
      intros.
      assert (rv_eq (rvinner (vecrvminus (x (S n)) (const xstar))
                     (vecrvminus (x (S n)) (const xstar)))
            (rvplus
               (rvscale 
                  (2 * (α n))
                  (rvinner
                     (vecrvminus (F_alpha (α n) (x n))
                                 (const xstar))
                     (w n)))
               (rvplus
                  (rvinner (vecrvminus 
                              (F_alpha (α n) (x n))
                              (const xstar))
                           (vecrvminus 
                              (F_alpha (α n) (x n)) 
                              (const xstar)))
                  (rvscale ((α n)^2)
                           (rvinner (w n) (w n)))))).
      {
        intros v.
        unfold rvplus, rvscale.
        simpl.
        rewrite H.
        unfold rvinner, vecrvminus, vecrvplus, vecrvopp, vecrvscale.
        Check inner_plus_l.
        repeat rewrite (rv_inner_plus_l).
        repeat rewrite (rv_inner_plus_r).
        repeat rewrite (rv_inner_scal_l).
        repeat rewrite (rv_inner_scal_r).
        ring_simplify.
        repeat rewrite Rplus_assoc.
        repeat apply Rplus_eq_compat_l.
        replace (Rvector_inner (w n v) (F_alpha (α n) (x n) v)) with 
            (Rvector_inner (F_alpha (α n) (x n) v) (w n v)) by apply rv_inner_sym.
        replace (Rvector_inner (w n v) (const xstar v)) with
                (Rvector_inner (const xstar v) (w n v)) by apply rv_inner_sym.
        now ring_simplify.
     }
      rewrite (SimpleExpectation_ext H3).
      repeat rewrite <- sumSimpleExpectation.
      repeat rewrite <- scaleSimpleExpectation.
      rewrite H0.
      rewrite Rmult_0_r.
      ring_simplify.
      generalize (SimpleExpectation_le _ _ H1); intros.
      rewrite <- scaleSimpleExpectation in H4.
      rewrite Rplus_comm.
      apply Rplus_le_compat; trivial.
      apply Rmult_le_compat_l.
      - apply pow2_ge_0.
      - now left.
    Qed.

    Lemma SimpleExpectation_pos (f : Ts -> R)
          (rx : RandomVariable dom borel_sa f)
          (srv: SimpleRandomVariable f) :
      (forall omega, 0 <= f omega) ->
      0 <= SimpleExpectation f.
    Proof.
      intros.
      replace (0) with (SimpleExpectation (const 0)).
      - apply SimpleExpectation_le.
        now unfold const.
      - apply SimpleExpectation_const.
    Qed.

    Lemma SimpleExpectation_rvinner_pos (f : Ts -> vector R I) 
          (rx : RandomVariable dom (Rvector_borel_sa I) f)
          (srv: SimpleRandomVariable f) :
      0 <= SimpleExpectation (rvinner f f).
    Proof.
      apply SimpleExpectation_pos.
      intro v.
      now generalize (inner_ge_0 (f v)).
   Qed.

    Lemma SimpleExpectation_rvmaxabs_pos (f : Ts -> vector R I) 
          (rx : RandomVariable dom (Rvector_borel_sa I) f)
          (srv: SimpleRandomVariable f) :
      0 <= SimpleExpectation (rvmaxabs f).
    Proof.
      apply SimpleExpectation_pos.
      intro v.
      unfold const, rvmaxabs.
      unfold Rvector_max_abs.
      unfold vector_fold_left.
      apply fold_left_Rmax_init_le.
   Qed.

    Lemma aux_seq (C: R) (x : nat -> Ts -> vector R I) (v : nat -> R) (xstar : vector R I)
         (rx : forall n, RandomVariable dom (Rvector_borel_sa I) (x n))
         (srx : forall n, SimpleRandomVariable  (x n)) :
      v (0%nat) = SimpleExpectation 
                    (rvinner 
                       (vecrvminus (x (0%nat)) (const xstar))
                       (vecrvminus (x (0%nat)) (const xstar))) ->
      (forall n, v (S n) = (g_alpha gamma (α n))^2 * (v n) +
                                                  (α n)^2 * C) ->
      (forall n,
          SimpleExpectation (rvinner (vecrvminus (x (S n)) (const xstar))
                                     (vecrvminus (x (S n)) (const xstar))) <=
          ((g_alpha gamma (α n))^2) *
          (SimpleExpectation
             (rvinner (vecrvminus (x n) (const xstar))
                      (vecrvminus (x n) (const xstar))))
          + (α n)^2 * C) ->
      forall n, 0 <= 
          SimpleExpectation (rvinner (vecrvminus (x n) (const xstar))
                                     (vecrvminus (x n) (const xstar))) <=
          (v n).
    Proof.
      intros.
      split.
      apply SimpleExpectation_rvinner_pos.
      induction n.
      - rewrite H.
        lra.
      - eapply Rle_trans.
        apply H1.
        rewrite H0.
        apply Rplus_le_compat_r.
        apply Rmult_le_compat_l.
        apply pow2_ge_0.
        apply IHn.
     Qed.
    
    Lemma aux_seq_lim (C: R) (x : nat -> Ts -> vector R I) (v : nat -> R) (xstar : vector R I)
         (rx : forall n, RandomVariable dom (Rvector_borel_sa I) (x n))
         (srx : forall n, SimpleRandomVariable  (x n)) :
      0 <= C ->
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) -> 
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      v (0%nat) = SimpleExpectation 
                    (rvinner 
                       (vecrvminus (x (0%nat)) (const xstar))
                       (vecrvminus (x (0%nat)) (const xstar))) ->
      (forall n, v (S n) = (g_alpha gamma (α n))^2 * (v n) +
                                                 (α n)^2 * C) ->
      is_lim_seq v 0.
    Proof.
      intros Cpos grel arel alim aser v0rel vrel.
      generalize (helper_convergence_6); intros.
      specialize (H (fun n => 2*(1-gamma)*(α n)-(1-gamma)^2*(α n)^2)).
      specialize (H (fun n => C*(α n)/(2*(1-gamma)-(1-gamma)^2*(α n)))).
      specialize (H (v (0%nat))).
      assert (0 <= v 0%nat).
      rewrite v0rel.
      apply SimpleExpectation_rvinner_pos; typeclasses eauto.
      specialize (H H0).
      cut_to H; trivial.
      apply is_lim_seq_ext with (u :=  (RMseq
            (fun n : nat => 2 * (1 - gamma) * α n - (1 - gamma) ^ 2 * α n ^ 2)
            (fun n : nat => C * α n / (2 * (1 - gamma) - (1 - gamma) ^ 2 * α n))
            (v 0%nat))).
      intros.
      induction n.
      - now unfold RMseq.
      - rewrite vrel.
        simpl.
        simpl in IHn.
        rewrite IHn.
        unfold g_alpha.
        unfold plus, scal; simpl.
        unfold mult; simpl.
        apply Rminus_diag_uniq.
        field_simplify; trivial.
        unfold Rdiv.
        now rewrite Rmult_0_l.
        rewrite Rmult_comm.
        rewrite Rmult_assoc.
        rewrite <- Rmult_minus_distr_l.
        apply Rmult_integral_contrapositive.
        split; [lra | ].
        assert ((1-gamma) *  α n <= 1).
        apply Rmult_le_1; [lra |].
        apply arel.
        lra.
      - apply H.
      - intros.
        replace ( 2 * (1 - gamma) * α n - (1 - gamma) ^ 2 * α n ^ 2 ) with
            (1 -  (g_alpha gamma (α n))^2).
        generalize (gamma_alpha_pos α gamma grel arel n); intros.
        generalize (gamma_alpha_le_1 α gamma grel arel n); intros.        
        generalize (Rmult_le_1 (g_alpha gamma (α n)) (g_alpha gamma (α n))); try lra.
        unfold g_alpha.
        ring.
      - intros.
        apply Rmult_le_pos.
        apply Rmult_le_pos; trivial; apply arel.
        left.
        apply Rinv_0_lt_compat.
        rewrite Rmult_comm.
        simpl.
        rewrite Rmult_assoc.
        rewrite <- Rmult_minus_distr_l.
        apply Rmult_lt_0_compat; [lra |].
        rewrite Rmult_1_r.
        assert ((1 - gamma) * α n <= 1).
        replace (1) with (1 * 1) by lra.
        apply Rmult_le_compat; try lra; apply arel.
        lra.
      - apply is_lim_seq_minus with (l1 := 0) (l2 := 0).
        replace (Finite 0) with (Rbar_mult (2 * (1 - gamma)) 0).
        now apply is_lim_seq_scal_l.
        simpl; rewrite Rmult_0_r; reflexivity.
        replace (Finite 0) with (Rbar_mult ((1-gamma)^2) 0).
        apply is_lim_seq_scal_l.
        unfold pow.
        apply is_lim_seq_mult with (l1 := 0) (l2 := 0); trivial.
        replace (Finite 0) with (Rbar_mult 0 1).
        now apply is_lim_seq_scal_r.
        simpl; rewrite Rmult_0_l; reflexivity.
        unfold is_Rbar_mult; simpl.
        f_equal; rewrite Rmult_0_l; reflexivity.
        simpl; rewrite Rmult_0_r; reflexivity.
        unfold is_Rbar_minus; simpl.
        unfold is_Rbar_plus; simpl.
        f_equal; rewrite Rplus_0_l, Ropp_0; reflexivity.
      - apply is_lim_seq_div with (l1 := 0) (l2 := (2 * (1 - gamma))).
        replace (Finite 0) with (Rbar_mult C 0).
        now apply is_lim_seq_scal_l.
        simpl; rewrite Rmult_0_r; reflexivity.
        apply is_lim_seq_minus with (l1 := 2 * (1-gamma)) (l2 := 0).
        apply is_lim_seq_const.
        replace (Finite 0) with (Rbar_mult ((1-gamma)^2) 0).
        now apply is_lim_seq_scal_l.
        simpl; rewrite Rmult_0_r; reflexivity.
        unfold is_Rbar_minus; simpl.
        unfold is_Rbar_plus; simpl.
        f_equal; rewrite Ropp_0, Rplus_0_r; reflexivity.
        rewrite Rbar_finite_neq.
        apply Rmult_integral_contrapositive.
        split; lra.
        unfold is_Rbar_div; simpl.
        unfold is_Rbar_mult; simpl.
        f_equal; rewrite Rmult_0_l; reflexivity.
      - generalize (product_sum_assumption_a α gamma grel arel alim aser); intros.
        assert (forall k, 
                    is_lim_seq
                      (fun n : nat => prod_f_R0 (fun m : nat => (g_alpha gamma (α (m + k)))^2) n) 0).
        intros.
        apply is_lim_seq_ext with
            (u := (fun n => (prod_f_R0 (fun m : nat => g_alpha gamma (α (m + k0))) n) * 
                            (prod_f_R0 (fun m : nat => g_alpha gamma (α (m + k0))) n))).
        intros.
        induction n.
        + simpl; ring.
        + simpl.
          simpl in IHn.
          rewrite <- IHn.
          ring.
        + apply is_lim_seq_mult with (l1 := 0) (l2 := 0).
          apply H1.
          apply H1.
          unfold is_Rbar_mult; simpl.
          f_equal; rewrite Rmult_0_l; reflexivity.
        + apply is_lim_seq_ext with 
              (u := (fun n : nat =>
                       prod_f_R0 (fun m : nat => g_alpha gamma (α (m + k)) ^ 2) n)).
          intros.
          apply prod_f_R0_proper; trivial.
          intro m.
          unfold g_alpha.
          simpl; ring.
          apply H2.
     Qed.

    Fixpoint RMseq_gen (a b : nat -> R) (init : R) (n : nat) : R :=
      match n with
      | 0 => init
      | (S k) => (a k) * (RMseq_gen a b init k) + (b k)
      end.

   (* following depends on is_contraction hypothesis in context *)
(*
  Context (hF : (@is_contraction Rvector_UniformSpace Rvector_UniformSpace F)).


          (lF : (@is_Lipschitz Rvector_UniformSpace Rvector_UniformSpace F gamma)).
*)
   Lemma f_contract_fixedpoint :
      0 <= gamma < 1 ->
      (forall x1 y : vector R I, Hnorm (minus (F x1) (F y)) <= gamma * Hnorm (minus x1 y)) -> 
     exists (xstar : vector R I), F xstar = xstar.
   Proof.
     intros.
     destruct (Req_dec gamma 0).
     - exists (F zero).
       rewrite H1 in H0.
       apply (@is_Lipschitz_le_zero_const R_AbsRing R_AbsRing 
                                          Rvector_NormedModule
                                          Rvector_NormedModule).
       intros.
       specialize (H0 y x).
       now rewrite Rmult_0_l in H0.
    - generalize (@FixedPoint R_AbsRing Rvector_CompleteNormedModule F (fun _ => True)); intros.
     cut_to H2; trivial.
     destruct H2 as [x [? [? [? ?]]]].
     now exists x.
     now exists (zero).
     apply closed_my_complete ; apply closed_true.                
     unfold is_contraction.
     exists gamma.
     split; [lra | ].
     unfold is_Lipschitz.
     unfold ball_x, ball_y; simpl.
     unfold ball; simpl.
     split; [lra | ].
     intros.
     specialize (H0 x1 x2).
     eapply Rle_lt_trans.
     apply H0.
     assert (0 < gamma) by lra.
     now apply Rmult_lt_compat_l.
  Qed.

   Lemma partition_measurable_vecrvminus_F_alpha_const (x : Ts -> vector R I)
         {rv : RandomVariable dom (Rvector_borel_sa I) x}
         {srv : SimpleRandomVariable x}
         (a : R) (xstar : vector R I) 
         (l : list (event dom)) :
     is_partition_list l ->
     partition_measurable (cod:=Rvector_borel_sa I) x l ->
     partition_measurable (cod:=Rvector_borel_sa I) (vecrvminus (F_alpha a x) (const xstar)) l.
   Proof.
     unfold F_alpha; intros.
     apply partition_measurable_vecrvminus; trivial.
     eapply partition_measurable_vecrvplus; trivial.
     apply partition_measurable_vecrvscale; trivial.
     apply partition_measurable_vecrvscale; trivial.
     apply partition_measurable_comp; trivial.
     apply partition_measurable_const; trivial.
   Qed.

  Definition update_sa_dec_history (l : list dec_sa_event)
          {rv_X : Ts -> vector R I}
          {rv:RandomVariable dom (Rvector_borel_sa I) rv_X}
          (srv : SimpleRandomVariable rv_X) : list dec_sa_event
    :=                                                   
      refine_dec_sa_partitions (vec_induced_sigma_generators srv) l.

  Lemma update_partition_list
          (l : list dec_sa_event)
          {rv_X : Ts -> vector R I}
          {rv:RandomVariable dom (Rvector_borel_sa I) rv_X}
          (srv : SimpleRandomVariable rv_X) :
    is_partition_list (map dsa_event l) ->
    is_partition_list (map dsa_event (update_sa_dec_history l srv)).
  Proof.
    intros.
    unfold update_sa_dec_history.
    apply is_partition_refine; trivial.
    apply is_partition_vec_induced_gen.
  Qed.

  Lemma update_partition_measurable
          (l : list dec_sa_event)
          {rv_X : Ts -> vector R I}
          {rv:RandomVariable dom (Rvector_borel_sa I) rv_X}
          (srv : SimpleRandomVariable rv_X) :
    partition_measurable (cod:=Rvector_borel_sa I) rv_X (map dsa_event (update_sa_dec_history l srv)).
  Proof.
    unfold partition_measurable, update_sa_dec_history.
    unfold refine_dec_sa_partitions.
    intros.
    rewrite in_map_iff in H0.
    destruct H0 as [? [? ?]].
    rewrite flat_map_concat_map in H1.
    rewrite concat_In in H1.
    destruct H1 as [? [? ?]].
    rewrite in_map_iff in H1.
    destruct H1 as [? [? ?]].
    rewrite <- H1 in H2.
    destruct srv.
    unfold vec_induced_sigma_generators in H3.
    rewrite in_map_iff in H3.
    destruct H3 as [? [? ?]].
    unfold RandomVariable.srv_vals in *.
    exists x2.
    split.
    now rewrite nodup_In in H4.
    unfold refine_dec_sa_event in H2.
    rewrite in_map_iff in H2.
    destruct H2 as [? [? ?]].
    rewrite <- H0.
    rewrite <- H2.
    rewrite <- H3.
    simpl.
    vm_compute.
    tauto.
  Qed.
  
    Lemma L2_convergent_helper2 (C : R) (w x : nat -> Ts -> vector R I) (xstar : vector R I)
         (hist : nat -> list dec_sa_event) 
         (rx : forall n, RandomVariable dom (Rvector_borel_sa I) (x n))
         (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n))
         (srw : forall n, SimpleRandomVariable  (w n)) 
         (srx : forall n, SimpleRandomVariable  (x n)) :
      0 <= C ->
      0 <= gamma < 1 ->
      xstar = F xstar ->
      (forall n, 0 <= α n <= 1) -> 
      (forall n, is_partition_list (map dsa_event (hist n))) ->
      (forall n, partition_measurable (cod:=Rvector_borel_sa I) (x n) (map dsa_event (hist n))) ->
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      (forall k, (x (S k)) = 
                 vecrvplus (F_alpha (α k) (x k))
                           (vecrvscale (α k) (w k))) ->
      (forall n, rv_eq (vector_gen_SimpleConditionalExpectation (w n) (hist n)) (const zero)) ->
      (forall n, SimpleExpectation (rvinner (w n) (w n)) < C)  ->
      (forall x1 y : vector R I, Hnorm (minus (F x1) (F y)) <= gamma * Hnorm (minus x1 y)) -> 
      is_lim_seq 
        (fun n => SimpleExpectation
                    (rvinner (vecrvminus (x n) (const xstar))
                             (vecrvminus (x n) (const xstar)))) 0.
    Proof.
      intros Cpos grel xfix arel ispart part_meas alim aser xrel xterm wbound Fcontract.
      assert (forall n,
                 SimpleExpectation (rvinner (vecrvminus (x (S n)) (const xstar))
                                (vecrvminus (x (S n)) (const xstar))) <=
                 ((g_alpha gamma (α n))^2) *
                 (SimpleExpectation
                    (rvinner (vecrvminus (x n) (const xstar))
                             (vecrvminus (x n) (const xstar))))
                 + (α n)^2 * C).
      {
        intros.
        eapply L2_convergent_helper with (w := w) (srw := srw); trivial.
        generalize (partition_measurable_vecrvminus_F_alpha_const (x n) (α n)
                   xstar (map dsa_event (hist n)) (ispart n) (part_meas n)); intros.
        generalize (simple_expection_rvinner_measurable_zero 
                      (vecrvminus (F_alpha (α n) (x n)) (const xstar))
                      (w n) (hist n) (xterm n) (ispart n) H); intros.
        erewrite SimpleExpectation_pf_irrel in H0.
        now rewrite H0.
        generalize (@is_contraction_falpha' (@PreHilbert_NormedModule
                                               (@Rvector_PreHilbert I))
                                            F gamma (α n) (arel n)); intros.
        intro v.
        cut_to H.
        - specialize (H (x n v) xstar).
          unfold norm, minus, f_alpha in H; simpl in H.
          unfold Hnorm, plus, opp in H; simpl in H.
          unfold inner, scal in H; simpl in H.
          unfold rvinner, vecrvminus, F_alpha, const.
          unfold vecrvplus, vecrvopp, vecrvscale, rvscale.
          unfold Rvector_opp in H.
          replace (1 - α n + gamma * α n) with (sqrt( (1 - α n + gamma * α n)^2)) in H.
          + rewrite <- sqrt_mult_alt in H.
            * apply sqrt_le_0 in H.
              -- unfold g_alpha.
                 rewrite <- xfix in H.
                 replace  (Rvector_plus (Rvector_scale (1 - α n) xstar)
                                        (Rvector_scale (α n) xstar)) with
                     (xstar) in H.
                 ++ replace (1 - (1 - gamma) * α n) with (1 - α n + gamma * α n) by lra.
                    apply H.
                 ++ assert (xstar = plus (scal (1 - (α n)) xstar) (scal (α n) xstar)).
                    ** rewrite scal_minus_distr_r with (x0 := 1).
                       unfold minus.
                       rewrite <- plus_assoc.
                       rewrite plus_opp_l.
                       rewrite plus_zero_r.
                       now generalize (scal_one xstar).
                    ** apply H0.
              -- apply rv_inner_ge_0.
              -- apply Rmult_le_pos.
                 ++ apply pow2_ge_0.
                 ++ apply rv_inner_ge_0.      
            * apply pow2_ge_0.
          + rewrite sqrt_pow2; trivial.
            generalize (gamma_alpha_pos α gamma grel arel n).
            unfold g_alpha; lra.
            (*
             destruct lF.
             unfold ball_x in H1.
             repeat red in H1.
             unfold UniformSpace.ball in H1.
             simpl in H1.
             unfold ball in H1.
             unfold PreHilbert_NormedModule. simpl.
             intros. specialize (H1 x1 y).
            *)
        - apply Fcontract.
       }
      generalize 
        (aux_seq_lim C x 
                     (fun n => RMseq_gen (fun k => (g_alpha gamma (α k))^2)
                                         (fun k => ((α k)^2)* C) 
                                         (SimpleExpectation
                                            (rvinner (vecrvminus (x 0%nat) 
                                                                 (const xstar))
                                                     (vecrvminus (x 0%nat) 
                                                                 (const xstar))))
                                         n   )
                     xstar rx srx Cpos grel arel alim aser
        ); intros; cut_to H0; try (now simpl).
      generalize
        (aux_seq C x 
                 (fun n => RMseq_gen (fun k => (g_alpha gamma (α k))^2)
                                     (fun k => ((α k)^2)* C) 
                                     (SimpleExpectation
                                        (rvinner (vecrvminus (x 0%nat) 
                                                             (const xstar))
                                                 (vecrvminus (x 0%nat) 
                                                             (const xstar))))
                                     n   )
                 xstar rx srx
        ); intros; cut_to H1; try (now simpl).
      apply (is_lim_seq_le_le _ _ _ 0 H1); trivial.
      apply is_lim_seq_const.
    Qed.


    Fixpoint L2_convergent_x (xinit:Ts->vector R I) (w: nat -> Ts -> vector R I) (n:nat) : Ts -> vector R I
      := match n with
         | 0 => xinit
         | S k => vecrvplus (F_alpha (α k) (L2_convergent_x xinit w k))
                           (vecrvscale (α k) (w k))
         end.
    
    Global Instance L2_convergent_x_srv (xinit:Ts->vector R I) (w: nat -> Ts -> vector R I) (n:nat)
          (srx : SimpleRandomVariable xinit)
          (srw : forall n, SimpleRandomVariable (w n)) :
      SimpleRandomVariable (L2_convergent_x xinit w n).
    Proof.
      induction n.
      - now simpl.
      - typeclasses eauto.
    Qed.

    Global Instance L2_convergent_x_rv (xinit:Ts->vector R I) (w: nat -> Ts -> vector R I) (n:nat)
          (rx : RandomVariable dom (Rvector_borel_sa I) xinit)
          (srx : SimpleRandomVariable xinit)
          (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n)) 
          (srw : forall n, SimpleRandomVariable (w n)) :
      RandomVariable dom (Rvector_borel_sa I) (L2_convergent_x xinit w n). 
    Proof.
      induction n.
      - now simpl.
      - generalize (L2_convergent_x_srv xinit w n srx srw); intros.
        typeclasses eauto.
    Qed.

    Section hist.
      Context (x:nat->Ts->vector R I).
      Context (rvx:forall n, RandomVariable dom (Rvector_borel_sa I) (x n)).
      Context (srvx: forall n, SimpleRandomVariable (x n)).
      
      Fixpoint L2_convergent_hist (n:nat) : list dec_sa_event
        := match n with
           | 0 => 
             @vec_induced_sigma_generators Ts dom I
                                   (x 0%nat)
                                   (rvx 0%nat)
                                   (srvx 0%nat)
           | S k =>
             @update_sa_dec_history (L2_convergent_hist k)
                                   (x (S k))
                                   (rvx (S k))
                                   (srvx (S k))
           end.

    End hist.

    Lemma L2_convergent_hist_is_partition_list x rx srx n:
      is_partition_list (map dsa_event (L2_convergent_hist x rx srx n)).
    Proof.
      induction n; simpl.
      - apply is_partition_vec_induced_gen.
      - now apply update_partition_list.
    Qed.

    Lemma L2_convergent_hist_partition_measurable x rx srx (n:nat):
      partition_measurable (cod:=Rvector_borel_sa I) (x n) (map dsa_event (L2_convergent_hist x rx srx n)).
    Proof.
      induction n; simpl.
      - apply vec_induced_partition_measurable.
      - apply update_partition_measurable.
    Qed.

    (* Theorem 8 *)
    Theorem L2_convergent (C : R) (xinit:Ts->vector R I) (w : nat -> Ts -> vector R I)
          (rxinit : RandomVariable dom (Rvector_borel_sa I) xinit)
          (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n))
          (srvxinit : SimpleRandomVariable xinit)
          (srw : forall n, SimpleRandomVariable  (w n)) :
      0 <= C ->
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) -> 
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      (forall n, rv_eq (vector_gen_SimpleConditionalExpectation 
                          (w n) 
                          (L2_convergent_hist (L2_convergent_x xinit w) _ _ n)) 
                       (const zero)) ->
      (forall n, SimpleExpectation (rvinner (w n) (w n)) < C)  ->
      (forall x1 y : vector R I, Hnorm (minus (F x1) (F y)) <= gamma * Hnorm (minus x1 y)) ->
      exists xstar,
        F xstar = xstar /\
        is_lim_seq 
          (fun n => SimpleExpectation
                   (rvinner (vecrvminus (L2_convergent_x xinit w n) (const xstar))
                            (vecrvminus (L2_convergent_x xinit w n) (const xstar)))) 0.
    Proof.
      intros.
      destruct (f_contract_fixedpoint) as [xstar Fxstar]; trivial.
      exists xstar.
      split; trivial.
      eapply L2_convergent_helper2; eauto.
      - intros.
        apply L2_convergent_hist_is_partition_list.
      - intros.
        apply L2_convergent_hist_partition_measurable.
    Qed.

  End qlearn3.

  Section qlearn4.

  Context (gamma : R) {Ts : Type}
          {dom: SigmaAlgebra Ts}.
(*          {prts: ProbSpace dom}. *)

    Fixpoint RMseqTs (α : nat -> R) (f : nat -> Ts -> R) (init : Ts -> R) (n : nat) (omega : Ts) : R :=
      match n with
      | 0 => init omega
      | (S k) => plus (scal (1 - α k) (RMseqTs α f init k omega)) (scal (α k) (f k omega))
      end.
   
(*
    Lemma eq86 {n} (F : vector R n -> vector R n) (x w : nat -> Ts -> vector R n) (xstar : vector R n) (C : R)
          (i : nat) (pf : (i < n)%nat) :
      (forall n, forall omega, Rabs (vector_nth i pf (minus (x n omega) xstar)) <= C) ->
      (forall n, forall omega, x (S n) omega = 
      (forall x y : vector R n, hilbert.Hnorm (minus (F x) (F y)) <= gamma * hilbert.Hnorm (minus x y)) ->
      (forall n, forall omega, 
            (- α n)*gamma*C <= (vector_nth i pf (minus (x (S n) omega) xstar)) -  (1 - α n)*(vector_nth i pf (minus (x n omega) xstar)) -  (α n)*(vector_nth i pf (w n omega)) <= (α n)*gamma*C).
    Proof.
      intros.
      induction n.
      - simpl.
      
*)
    Lemma Induction_I2_15 (α : nat -> R) (xtilde : nat -> Ts -> R) (xstar : R) (w : nat -> Ts -> R) (C:R) :
      (forall n, 0 <= α n <= 1) -> 
      (forall n, forall omega, Rabs (xtilde n omega) <= C) ->
      (forall n, forall omega, 
            (- α n)*gamma*C <= (xtilde (S n) omega) -  (1 - α n)*(xtilde n omega) -  (α n)*(w n omega) <= (α n)*gamma*C) ->
      forall n, forall omega, 
          - (RMseq α (fun n => gamma * C) C n) <= (xtilde n omega) - (RMseqTs α w (const 0) n omega) 
          <= RMseq α (fun n => gamma * C) C n.
    Proof.
      intros.
      induction n.
      - unfold const; simpl.
        rewrite Rminus_0_r.
        specialize (H0 0%nat omega).
        now apply Rabs_le_between.
      - simpl.
        specialize (H1 n omega).
        unfold plus, scal; simpl.
        unfold Hierarchy.mult; simpl.
        destruct IHn.
        specialize (H n).
        split.
        + apply Rmult_le_compat_l with (r := 1 - α n) in H2; lra.
        + apply Rmult_le_compat_l with (r := 1 - α n) in H3; lra.
     Qed.

    Lemma RMseq_const_lim (α : nat -> R) (C : R) (init : R):
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) ->       
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      is_lim_seq (RMseq α (fun n => gamma * C) init) (gamma * C).
    Proof.
      intros.
      generalize (product_sum_assumption_a α gamma H H0 H1 H2 0); intros.
      apply is_lim_seq_ext with (v := fun n : nat => prod_f_R0 (fun m : nat => g_alpha gamma (α m)) n) in H3.
      generalize (@Deterministic_RM_2b R_NormedModule (fun n => gamma * C) α init gamma (gamma * C) H); intros.
      cut_to H4; trivial.
      - apply is_lim_seq_abs_0 in H4.
        unfold minus in H4.
        unfold opp in H4; simpl in H4.
        apply is_lim_seq_plus' with (u := (fun _ => gamma * C)) (l1 := gamma * C) in H4.
        + rewrite Rplus_0_r in H4.
          apply is_lim_seq_ext with (v := (RMseq α (fun _ : nat => gamma * C) init)) in H4.
          apply H4.
          intros.
          unfold plus; simpl.
          ring_simplify.
          clear H1 H2 H3 H4.
          induction n.
          * now simpl.
          * simpl.
            now rewrite IHn.
        + apply is_lim_seq_const.
      - intros.
        rewrite minus_eq_zero, norm_zero.
        apply Rmult_le_pos; try lra.
        apply norm_ge_0.
      - intros; apply prod_f_R0_proper; [|trivial].
        unfold Morphisms.pointwise_relation; intros.
        do 2 f_equal; lia.
      Qed.

    Lemma Rsqr_le_rvinner {n} (v : vector R n) (i: nat) (pf : (i < n)%nat) :
      (vector_nth i pf v)² <= Rvector_sum (Rvector_mult v v).
    Proof.
      eapply Rle_trans
      ; [| 
         apply (vector_nth_pos_le_pos (Rvector_mult v v) i pf)].
      - rewrite Rvector_mult_explode, vector_nth_create'.
        unfold Rsqr.
        now right.
      - intros.
        apply In_vector_nth_ex in H.
        destruct H as [?[? HH]].
        rewrite Rvector_mult_explode, vector_nth_create' in HH.
        assert (HH2:a = Rsqr (vector_nth x x0 v))
          by (symmetry; apply HH).
        rewrite HH2.
        apply Rle_0_sqr.
    Qed.

    Lemma SimpleExpectation_rvsqr_pos (f : Ts -> R)
          {prts: ProbSpace dom}
          {rx : RandomVariable dom borel_sa f}
          {srv: SimpleRandomVariable f}       :
      0 <= SimpleExpectation (rvsqr f).
    Proof.
      apply SimpleExpectation_pos.
      intro v.
      unfold const, rvsqr.
      apply Rle_0_sqr.
   Qed.

    Lemma lim_rvinner_0 {n:nat}
        (i : nat)
        (pf : (i < n)%nat)
        {prts: ProbSpace dom}
        (Xn: nat -> Ts -> vector R n) 
        (srvxn : forall n0, SimpleRandomVariable (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :

        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq 
          (fun n0 => 
              SimpleExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0))))) 0.
    Proof.
      apply is_lim_seq_le_le with (u := fun n0 => 0); [| apply is_lim_seq_const].
      intros.
      split.
      apply SimpleExpectation_rvsqr_pos.
      apply SimpleExpectation_le.
      intro x.
      unfold rvsqr, rvinner.
      unfold Rvector_inner, rvabs.
      rewrite <- Rsqr_abs.
      unfold vecrvnth.
      apply Rsqr_le_rvinner.
    Qed.

    Lemma Induction_I1_15_helper {n}
          {prts: ProbSpace dom}
          (α : nat -> R)
          (eps : posreal) (C : R) (w : nat -> Ts -> vector R n)
          (rw : forall n0, RandomVariable dom (Rvector_borel_sa n) (w n0))
          (srw : forall n0, SimpleRandomVariable  (w n0)) (i : nat) (pf : (i < n)%nat) :
      0 <= C ->
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) ->       
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      (forall n0 : nat,
          rv_eq
            (vector_gen_SimpleConditionalExpectation 
               (w n0)
               (L2_convergent_hist 
                  (@L2_convergent_x n α (vecrvconst n 0) Ts (vecrvconst n 0) w) _ _ n0)) 
            (const zero)) ->
      (forall n0 : nat, SimpleExpectation (rvinner (w n0) (w n0)) < C) ->
    is_lim_seq (fun n0 => ps_P (event_ge dom (rvabs (vecrvnth i pf (@L2_convergent_x n α (vecrvconst n 0) Ts (vecrvconst n 0) w n0))) eps)) 0.
    Proof.
      intros.
      generalize (@L2_convergent n gamma α (fun _ => vector_const 0 n) Ts dom prts C (vecrvconst n 0) w (Rvector_const_rv n 0) rw (srv_vecrvconst n 0) srw H H0 H1 H2 H3); intros.
      cut_to H6; trivial.
      - destruct H6 as [? [? ?]].
        rewrite <- H6 in H7.
        apply is_lim_seq_ext with 
            (v := fun n0 : nat =>
                    SimpleExpectation
                      (rvinner (@L2_convergent_x n α (vecrvconst n 0) Ts (vecrvconst n 0) w n0)
                               (@L2_convergent_x n α (vecrvconst n 0) Ts (vecrvconst n 0) w n0))) in H7.
        + apply conv_l2_prob1; intros.
          * erewrite srv_Expectation_posRV.
            now unfold is_finite.
          * apply is_lim_seq_ext with 
                (u := fun n0 : nat =>
                        SimpleExpectation (rvsqr (rvabs (vecrvnth i pf (@L2_convergent_x n α (vecrvconst n 0) Ts (vecrvconst n 0) w n0))))).
            -- intros.
               erewrite srv_Expectation_posRV.
               reflexivity.
            -- now apply lim_rvinner_0.
        + intros.
          apply SimpleExpectation_ext.
          intro z.
          assert (rv_eq (vecrvminus (@L2_convergent_x n α (fun v => vector_const 0 n) Ts (vecrvconst n 0) w n0) (const (vector_const 0 n)))
                        (@L2_convergent_x n α (fun v => vector_const 0 n) Ts (vecrvconst n 0) w n0)).
          intro zz.
          unfold vecrvminus, vecrvconst.
          unfold vecrvplus, vecrvopp.
          unfold vecrvscale, const.
          rewrite Rvector_scale_zero.
          now rewrite Rvector_plus_zero.
          now apply rvinner_proper.
      - intros.
        rewrite minus_eq_zero.
        generalize (@hilbert.norm_zero (@Rvector_PreHilbert n)); intros.
        replace (@zero (@Rvector_AbelianGroup n)) with (@zero (hilbert.PreHilbert.AbelianGroup (@Rvector_PreHilbert n))).
        rewrite H7.
        apply Rmult_le_pos; try lra.
        now apply hilbert.norm_ge_0.
        reflexivity.
    Qed.

    Lemma conv_l2_vector_prob_i {n:nat}
        (eps : posreal) 
        (i : nat)
        (pf : (i < n)%nat)
        {prts: ProbSpace dom}
        (Xn: nat -> Ts -> vector R n) 
        (srvxn : forall n0, SimpleRandomVariable (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq (fun n0 => ps_P (event_ge dom (rvabs (vecrvnth i pf (Xn n0))) eps)) 0.
    Proof.
      intros.
      apply conv_l2_prob1.
      intros.
      replace (Expectation_posRV (rvsqr (rvabs (vecrvnth i pf (Xn n0)))))
        with (Finite (SimpleExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0)))))).
      now simpl.
      generalize (srv_Expectation_posRV (rvsqr (rvabs (vecrvnth i pf (Xn n0))))).      
      intros.
      symmetry.
      apply H0.
      apply is_lim_seq_ext with
          (u :=  (fun n0 : nat => SimpleExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0)))))).  
      intros.
      symmetry.
      generalize (srv_Expectation_posRV (rvsqr (rvabs (vecrvnth i pf (Xn n0))))); intros.
      now rewrite H0.
      now apply lim_rvinner_0 with (srvxn0 := srvxn).
   Qed.

    Lemma conv_l2_vector_prob {n:nat}
          (eps : posreal)
        {prts: ProbSpace dom}          
        (Xn: nat -> Ts -> vector R n) 
        (srvxn : forall n0, SimpleRandomVariable (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        forall i (pf: (i<n)%nat),
          is_lim_seq (fun n0 => ps_P (event_ge dom (rvabs (vecrvnth i pf (Xn n0))) eps)) 0.
    Proof.
      intros.
      now apply conv_l2_vector_prob_i with (srvxn0 := srvxn).
    Qed.

    Lemma conv_l2_conv_linf_sqr {n:nat}
        {prts: ProbSpace dom}                    
        (Xn: nat -> Ts -> vector R n) 
        (srvxn : forall n0, SimpleRandomVariable (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvsqr (rvmaxabs (Xn n0)))) 0.
    Proof.
      intros.
      apply is_lim_seq_le_le with
          (u := fun _ => 0) (w := fun n0 => 
                                    SimpleExpectation (rvinner (Xn n0) (Xn n0)));
        [ | apply is_lim_seq_const | trivial].
      intros; split.
      - apply SimpleExpectation_pos.
        intros.
        unfold rvsqr.
        apply Rle_0_sqr.
      - apply SimpleExpectation_le.
        intro x.
        unfold rvmaxabs, rvinner, rvsqr.
        apply sqr_max_abs_le_inner.
    Qed.

    Instance IsFiniteExpectation_simple
        (X:  Ts -> R)
        {prts: ProbSpace dom}                    
        {rv : RandomVariable dom borel_sa X} 
        {srv: SimpleRandomVariable X}  :       
      IsFiniteExpectation prts X.
    Proof.
      generalize (Expectation_simple X); intros.
      generalize (Expectation_IsFiniteExpectation prts X); intros.
      now specialize (H0 _ H).
    Qed.

    Program Instance srvpower
           (rv_X : Ts -> R) (r:R)
           {prts: ProbSpace dom}                    
           {srv:SimpleRandomVariable rv_X} : 
      SimpleRandomVariable (rvpower (rvabs rv_X) (const r)) :=
      {srv_vals := map (fun x => power (Rabs x) r) srv_vals }.
    Next Obligation.
      unfold rvpower, rvabs, const.
      apply in_map_iff.
      destruct srv.
      exists (rv_X x).
      split; trivial.
    Qed.

    Instance IsLp_simple
        (X:  Ts -> R)
        {prts: ProbSpace dom}                    
        (rv : RandomVariable dom borel_sa X) 
        (srv: SimpleRandomVariable X)  :       
      IsLp prts 2 X.
    Proof.
      unfold IsLp.
      apply IsFiniteExpectation_simple.
      typeclasses eauto.
      typeclasses eauto.      
    Qed.

    Lemma finite_expectation_simple
        (X: Ts -> R)
        {prts: ProbSpace dom}                    
        {rv : RandomVariable dom borel_sa X} 
        {srv : SimpleRandomVariable X} :
      SimpleExpectation X = FiniteExpectation prts X.
      generalize (Expectation_simple X); intros.
      generalize (FiniteExpectation_Expectation prts X); intros.
      rewrite H in H0.
      now inversion H0.
   Qed.

    Lemma conv_l2_l1_simple
          (Xn: nat -> Ts -> R)
        {prts: ProbSpace dom}                              
        (rvxn : forall n, RandomVariable dom borel_sa (Xn n)) 
        (srvxn : forall n, SimpleRandomVariable (Xn n))  :       
    is_lim_seq (fun n => SimpleExpectation (rvsqr (Xn n))) 0 ->
    is_lim_seq (fun n => SimpleExpectation (rvabs (Xn n))) 0.
    Proof.
      intros.
      generalize (conv_l2_l1 prts Xn rvxn _); intros.
      cut_to H0.
      - apply is_lim_seq_ext with 
            (v := fun n : nat => SimpleExpectation (rvabs (Xn n))) in H0.
        apply H0.
        intros; symmetry.
        generalize (finite_expectation_simple (rvabs (Xn n))); intros.
        rewrite H1.
        apply FiniteExpectation_pf_irrel.
      - apply is_lim_seq_ext with
            (u := fun n => SimpleExpectation (rvsqr (rvabs (Xn n)))).
        intros.
        generalize (finite_expectation_simple (rvsqr (rvabs (Xn n)))); intros.
        rewrite H1.
        apply FiniteExpectation_pf_irrel.
        apply is_lim_seq_ext with
            (u := (fun n : nat => SimpleExpectation (rvsqr (Xn n)))); trivial.
        intros.
        apply SimpleExpectation_ext.
        intro x.
        unfold rvsqr, rvabs.
        now rewrite Rsqr_abs.
     Qed.

    Lemma conv_l2_conv_linf {n:nat}
        (Xn: nat -> Ts -> vector R n) 
        {prts: ProbSpace dom}                              
        {srvxn : forall n0, SimpleRandomVariable (Xn n0)}
        {rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)} :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq
          (fun n0 : nat =>
             SimpleExpectation (rvmaxabs (Xn n0))) 0.
     Proof.
       intros.
       generalize (conv_l2_conv_linf_sqr Xn srvxn rvxn H); intros.
       apply conv_l2_l1_simple in H0.
       apply is_lim_seq_ext with
           (v := (fun n0 => SimpleExpectation (rvmaxabs (Xn n0)))) in H0; trivial.
       intros.
       apply SimpleExpectation_ext.
       intro x.
       unfold rvabs, rvmaxabs.
       apply Rabs_right.
       apply Rle_ge.
       apply Rvector_max_abs_nonneg.
    Qed.

    Lemma equiv_le_rvmaxabs_inter_rvabs {n}
          (eps : posreal)
          {prts: ProbSpace dom}                              
          (X : Ts -> vector R n)
          (srv : SimpleRandomVariable X)
          (rv :  RandomVariable dom (Rvector_borel_sa n) X) :
      pre_event_equiv
        (fun omega => rvmaxabs X omega <= eps)
        (pre_list_inter
           (proj1_sig (vector_map (fun f => fun omega => rvabs f omega <= eps)
                                  (fun_to_vector_to_vector_of_funs X)))).
    Proof.
      unfold rvmaxabs, rvabs.
      intro x.
      split; intros HH.
      - intros ? inn.
        apply In_vector_nth_ex in inn.
        destruct inn as [?[? inn]].
        subst.
        rewrite vector_nth_map, vector_nth_fun_to_vector.
        eapply Rle_trans; try eapply HH.
        apply Rvector_max_abs_nth_le.
      - red in HH.
        apply fold_left_lub.
        + intros ? inn.
          apply In_vector_nth_ex in inn.
          destruct inn as [?[? inn]].
          subst.
          unfold Rvector_abs.
          rewrite vector_nth_map.
          apply HH.
          generalize (vector_nth_In (vector_map (fun (f : Ts -> R) (omega : Ts) => Rabs (f omega) <= eps)
                                                (fun_to_vector_to_vector_of_funs X)) x1 x2)
          ; intros inn.
          rewrite vector_nth_map in inn.
          rewrite vector_nth_fun_to_vector in inn.
          apply inn.
        + destruct eps; simpl.
          lra.
    Qed.

    Lemma equiv_ge_rvmaxabs_inter_rvabs_aux {n}
          (eps : posreal)
          {prts: ProbSpace dom}                              
          (X : Ts -> vector R (S n))
          (srv : SimpleRandomVariable X)
          (rv :  RandomVariable dom (Rvector_borel_sa (S n)) X) :
      pre_event_equiv
        (fun omega => rvmaxabs X omega >= eps)
        (pre_list_union
           (proj1_sig (vector_map (fun f => fun omega => rvabs f omega >= eps)
                                  (fun_to_vector_to_vector_of_funs X)))).
    Proof.
      unfold rvmaxabs, rvabs.
      intro x.
      split; intros HH.
      - red.
        destruct (Rvector_max_abs_nth_in (X x)) as [i [pf inn]].

        assert (
             exists i pf,
               vector_nth i pf
                          (vector_map (fun (f : Ts -> R) (omega : Ts) => Rabs (f omega) >= eps)
                                      (fun_to_vector_to_vector_of_funs X)) x).
        + eexists. eexists.
          rewrite vector_nth_map.
          rewrite vector_nth_fun_to_vector.
          rewrite inn in HH.
          eapply HH.
        + destruct H as [?[??]].
          eexists.
          split; [| eapply H].
          apply vector_nth_In.
      - destruct HH as [e [inn HH]].
        apply In_vector_nth_ex in inn.
        destruct inn as [i[pf eqq]].
        subst.
        rewrite vector_nth_map in HH.
        rewrite vector_nth_fun_to_vector in HH.
        eapply Rge_trans; try eapply HH.
        eapply Rle_ge.
        apply Rvector_max_abs_nth_le.
    Qed.

    Lemma equiv_ge_rvmaxabs_inter_rvabs {n}
          (eps : posreal)
          {prts: ProbSpace dom}                              
          (X : Ts -> vector R n)
          (srv : SimpleRandomVariable X)
          (rv :  RandomVariable dom (Rvector_borel_sa n) X) :
      pre_event_equiv
        (fun omega => rvmaxabs X omega >= eps)
        (pre_list_union
           (proj1_sig (vector_map (fun f => fun omega => rvabs f omega >= eps)
                                  (fun_to_vector_to_vector_of_funs X)))).
    Proof.
      destruct n.
      - simpl.
        rewrite pre_list_union_nil.
        unfold pre_event_none.
        intros ?.
        split; try tauto.
        unfold rvmaxabs, Rvector_max_abs, vector_fold_left.
        destruct (X x); simpl.
        destruct x0; try discriminate.
        simpl.
        destruct eps; simpl.
        lra.
      - now apply equiv_ge_rvmaxabs_inter_rvabs_aux.
    Qed.

    Instance rvmaxabs_pos {n}
             (X : Ts -> vector R n) :
      PositiveRandomVariable (rvmaxabs X).
    Proof.
      unfold PositiveRandomVariable, rvmaxabs.
      intros.
      apply Rvector_max_abs_nonneg.
    Qed.

    Lemma conv_l2_vector_prob_max_abs {n:nat}
        (eps : posreal)
          {prts: ProbSpace dom}                              
        (Xn: nat -> Ts -> vector R n) 
        (srvxn : forall n0, SimpleRandomVariable (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq (fun n0 => ps_P (event_ge dom (rvmaxabs (Xn n0)) eps)) 0.
    Proof.
      intros.
      apply conv_l2_conv_linf in H.
      apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                      (w := (fun n => (Expectation_posRV (rvmaxabs (Xn n))) / eps)).
      - exists (0%nat); intros.
        split.
        + apply ps_pos.
        + generalize (conv_l1_prob_le prts eps (rvmaxabs (Xn n0))); intros.
          rewrite Expectation_posRV_ext with (prv2 := prvabs (rvmaxabs (Xn n0))).
          * assert (event_equiv
                      (event_ge dom (rvmaxabs (Xn n0)) eps)
                      (event_ge dom (rvabs (rvmaxabs (Xn n0))) eps)).
            {
              intro x.
              simpl.
              unfold rvmaxabs, rvabs.
              replace (Rabs (Rvector_max_abs (Xn n0 x))) with
                  (Rvector_max_abs (Xn n0 x)); try lra.
              rewrite Rabs_right; trivial.
              apply Rle_ge.
              apply Rvector_max_abs_nonneg.
            }
            rewrite (ps_proper _ _ H2).
            apply H1.
            generalize (simple_Expectation_posRV (rvabs (rvmaxabs (Xn n0)))); intros.
            unfold is_finite.
            rewrite <- H3.
            simpl.
            reflexivity.
          * intro x.
            unfold rvmaxabs, rvabs.
            rewrite Rabs_right; trivial.
            apply Rle_ge.
            apply Rvector_max_abs_nonneg.
      - apply is_lim_seq_const.
      - apply is_lim_seq_ext with
            (u := fun n0 => (/ eps) * SimpleExpectation (rvmaxabs (Xn n0))).
        + intros.
          unfold Rdiv.
          rewrite Rmult_comm.
          apply Rmult_eq_compat_r.
          generalize (simple_Expectation_posRV (rvmaxabs (Xn n0))); intros.
          rewrite <- H0.
          reflexivity.
        + replace (Finite 0) with (Rbar_mult (Finite (/ eps)) (Finite 0)).
          * now apply is_lim_seq_scal_l.
          * simpl.
            rewrite Rbar_finite_eq.
            lra.
    Qed.

    Lemma vecrvminus_zero {n} (rvx : Ts -> vector R n) :
          rv_eq (vecrvminus rvx (const (vector_const 0 n))) rvx.
    Proof.
      intro x.
      unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, const.
      rewrite Rvector_scale_zero.
      now rewrite Rvector_plus_zero.
    Qed.

    Definition Rvector_minus {n} (x y:vector R n) : vector R n
      := Rvector_plus x (Rvector_opp y).

    Lemma Rabs_le_both (a b : R) :
      Rabs a <= b <-> -b <= a <= b.
    Proof.
      unfold Rabs.
      destruct (Rcase_abs a); lra.
    Qed.
   
    Lemma Rabs_lt_both (a b : R) :
      Rabs a < b <-> -b < a < b.
    Proof.
      unfold Rabs.
      destruct (Rcase_abs a); lra.
    Qed.

    Lemma plus_nth {n} (v1 v2 : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_plus v1 v2) = 
      (vector_nth i pf v1) + (vector_nth i pf v2).
    Proof.
      rewrite Rvector_plus_explode.
      now rewrite vector_nth_create'.
    Qed.

    Lemma scale_nth {n} (c : R) (v : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_scale c v) = c * vector_nth i pf v.
    Proof.
      apply vector_nth_map.
    Qed.

    Lemma opp_nth {n} (v : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_opp v) = -1 * vector_nth i pf v.
    Proof.
      apply vector_nth_map.
    Qed.

    Lemma minus_nth {n} (v1 v2 : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_minus v1 v2) = 
      (vector_nth i pf v1) - (vector_nth i pf v2).
    Proof.
      unfold Rvector_minus.
      rewrite plus_nth, opp_nth.
      lra.
    Qed.


    Declare Scope Rvector_scope.
    Delimit Scope Rvector_scope with Rvector.
    Bind Scope Rvector_scope with vector R.
    Local Open Scope Rvector_scope.

    Notation "c .* v" := (Rvector_scale (c%R) v) (at level 41, right associativity) : Rvector_scope.
    Notation "x + y" := (Rvector_plus x y) (at level 50, left associativity) : Rvector_scope.

    Lemma Rvector_plus_eq_compat_l {n} (v v1 v2 : vector R n) :
      v1 = v2 -> Rvector_plus v v1 = Rvector_plus v v2.
    Proof.
      congruence.
    Qed.

    Hint Rewrite @plus_nth @scale_nth @mult_nth @minus_nth @opp_nth : vector.

    Lemma eq_vector_nths {T} {n} (v1 v2:vector T n) :
      v1 = v2 ->
      (forall i pf, vector_nth i pf v1 = vector_nth i pf v2).
    Proof.
      congruence.
    Qed.

    Lemma L2_convergent_x_nth_RMseqTs (i n:nat) (pf : (i < S n)%nat) (α : nat -> R) 
          (w : nat -> Ts -> vector R (S n)) (omega:Ts) :
      forall n0, 
        vector_nth i pf (@L2_convergent_x 
                           (S n) α 
                           (vecrvconst (S n) 0) Ts
                           (vecrvconst (S n) 0) w n0 omega) =
        RMseqTs (fun n0 : nat => α (n0)%nat)
                (fun n0 : nat => vecrvnth i pf (w (n0)%nat)) 
                (const 0) n0 omega.
    Proof.
      unfold vecrvconst, const, vecrvnth.
      induction n0.
      - simpl.
        now rewrite vector_nth_const.
      - simpl.
        unfold F_alpha, vecrvplus, vecrvscale.
        autorewrite with vector.
        rewrite IHn0, vector_nth_const.
        unfold plus, scal; simpl.
        unfold Hierarchy.mult; simpl.
        ring.
     Qed.

    Lemma minus_half (r:R) :
      r - r/2 = r/2.
    Proof.
      lra.
    Qed.

    Lemma seq_sum_shift (α : nat -> R) (nk:nat):
      is_lim_seq (sum_n α) p_infty ->
      is_lim_seq (sum_n (fun n0 => α (n0 + nk)%nat)) p_infty.
    Proof.
      intros.
      destruct (Nat.eq_dec nk 0).
      - subst.
        eapply (is_lim_seq_ext _ _ _ _ H).
        Unshelve.
        intros.
        apply sum_n_ext.
        intros.
        f_equal; lia.
     -  apply is_lim_seq_incr_n with (N := nk) in H.
        assert (0 < nk)%nat by lia.
        apply is_lim_seq_ext 
              with (v := (fun n => ((sum_n α (nk-1)%nat) + 
                                    (sum_n (fun n1 : nat => α (n1 + nk)%nat) n))%R ))
                   in H.
        + eapply is_lim_seq_minus with (v := fun _ => sum_n α (nk-1)) in H.
          * eapply is_lim_seq_ext in H.
            -- apply H.
            -- intros; lra.
          * apply is_lim_seq_const.
          * unfold is_Rbar_minus, is_Rbar_plus.
            now simpl.
        + intros.
          unfold sum_n.
          rewrite sum_split with (m := (nk-1)%nat); try lia.
          apply Rplus_eq_compat_l.
          replace (S (nk - 1)) with (nk) by lia.
          apply sum_n_m_shift.
    Qed.

    (*
    Instance indexed_srv_shifted {Td} (w : nat -> Ts -> Td) (nk : nat) :
      (forall n, SimpleRandomVariable (w n)) ->
      forall n, SimpleRandomVariable (w (n + nk)%nat).
    Proof.
      easy.
    Qed.

    Instance indexed_rv_shifted {Td} (sa : SigmaAlgebra Td) (w : nat -> Ts -> Td) (nk : nat) :
      (forall n0, RandomVariable dom sa (w n0)) ->
      forall n0, RandomVariable dom sa (w (n0 + nk)%nat).
    Proof.
      easy.
    Qed.
     *)

    Lemma Induction_stepk_I1_15 {n} (k:nat) (eps P C0: posreal) (α : nat -> R)
          (C : R) (w x : nat -> Ts -> vector R (S n)) (xstar : vector R (S n))
          (F : (vector R (S n)) -> (vector R (S n)))
          {prts: ProbSpace dom}                              
          (rx : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (x n0))
          (rw : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (w n0))
          (srw : forall n0, SimpleRandomVariable  (w n0)) :
      P < 1 ->
      0 <= C ->
      0 <= gamma < 1 ->
      gamma + eps < 1 ->
      (forall n, 0 <= α n <= 1) ->       
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      (forall (x y : vector R (S n)),
          Rvector_max_abs (Rvector_minus (F x) (F y)) <= 
          gamma * Rvector_max_abs (Rvector_minus x y)) ->
      F xstar = xstar ->
      (forall n,
          (rv_eq (x (S n))
                 (vecrvplus
                    (vecrvscale (1 - α n) (x n)) 
                    (vecrvscale (α n)
                                (vecrvplus (fun v => F (x n v)) (w n)))))) ->
      (forall n, forall omega, 
            rvmaxabs (vecrvminus (x n) (const xstar)) omega <= C0) ->
      (forall n0 : nat, SimpleExpectation (rvinner (w n0) (w n0)) < C) ->
      (forall nk, forall n0,
          rv_eq
            (vector_gen_SimpleConditionalExpectation 
               (w (n0 + nk)%nat)
               (L2_convergent_hist 
                  (@L2_convergent_x (S n) (fun k => α (k + nk)%nat) 
                                    (vecrvconst (S n) 0) Ts 
                                    (vecrvconst (S n) 0) 
                                    (fun k => w (k + nk)%nat)) _ _ n0)) 
               (const zero)) ->
       (exists nk : nat,
           forall n0 : nat,
             rv_le (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar)))
             (const (C0 * (gamma + eps) ^ k))) ->
      exists (nk : nat),
      forall n0, 
        ps_P 
          (event_le dom
             (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar)))
             (C0 * (gamma + eps)^(S k)))
        >= P .
    Proof.
      intros Plim Clim glim geps alim aseq sumaseq Fcont Fxstar xrel xlim wexp condexp normbound.
      destruct normbound as [nk IHk].
      assert (alimshift : (forall n, 0 <= α (n + nk)%nat <= 1)) by (intros; apply alim).
      assert (aseqshift: is_lim_seq (fun n0 => α (n0 + nk)%nat) 0) by now apply is_lim_seq_incr_n.
      assert (sumaseqshift: is_lim_seq (sum_n (fun n0 => α (n0 + nk)%nat)) p_infty) 
        by    (apply seq_sum_shift; trivial).
      generalize (RMseq_const_lim (fun n0 => α (n0 + nk)%nat)  (C0 * (gamma + eps)^k) (C0 * (gamma + eps)^k) glim alimshift aseqshift sumaseqshift); intros.
      generalize (@L2_convergent (S n) gamma (fun n0 => α (n0 + nk)%nat) (fun _ => vector_const 0 (S n)) Ts dom prts C (vecrvconst (S n) 0) (fun n => w (n + nk)%nat) (Rvector_const_rv (S n) 0) _ (srv_vecrvconst (S n) 0) _ Clim glim alimshift aseqshift sumaseqshift); intros.
      cut_to H0; trivial.
      + destruct H0 as [? [? ?]].
        rewrite <- H0 in H1.
        rewrite <- is_lim_seq_spec in H.
        unfold is_lim_seq' in H.
        generalize (cond_pos eps); intros.
        assert (0 < C0 * (gamma + eps)^k * eps/2).
        { 
          apply Rmult_lt_0_compat; [|lra].
          apply Rmult_lt_0_compat; trivial.
          apply Rmult_lt_0_compat; [apply cond_pos|].
          apply pow_lt.
          lra.
        }
        specialize (H (mkposreal _ H3)).
        destruct H; simpl in H.
        apply is_lim_seq_ext with
            (v :=  fun n0 : nat =>
                     SimpleExpectation
                       (rvinner (@L2_convergent_x (S n) (fun n => α (n + nk)%nat) (vecrvconst (S n) 0) Ts (vecrvconst (S n) 0) (fun n => w (n + nk)%nat) n0)
                                (@L2_convergent_x (S n) (fun n => α (n + nk)%nat) (vecrvconst (S n) 0) Ts (vecrvconst (S n) 0) (fun n => w (n + nk)%nat) n0))) in H1.
        * generalize (conv_l2_vector_prob_max_abs 
                        (mkposreal _ H3)
                        (fun n0 => @L2_convergent_x (S n) (fun n => α (n + nk)%nat) (vecrvconst (S n) 0) Ts (vecrvconst (S n) 0) (fun n => w (n + nk)%nat) n0) _ _ H1); intros.
            apply is_lim_seq_spec in H4.
            unfold is_lim_seq' in H4.
            assert (0 < 1-P) by lra.
            destruct (H4 (mkposreal _ H5)); simpl in H6.
            assert (gamma * C0 * (gamma+eps)^k = gamma * C0 * (gamma+eps)^k); trivial.
            generalize (product_sum_assumption_a α gamma glim alim aseq sumaseq 0%nat); intros.
            apply is_lim_seq_ext with
                (v := fun n : nat => prod_f_R0 (fun m : nat => g_alpha gamma (α m)) n)
              in H8; [|(intros;
                       apply prod_f_R0_proper; trivial;
                       intro m; f_equal; f_equal; lia)].
            generalize (@Deterministic_RM_2b 
                          R_NormedModule
                          (fun n0 => gamma * C0 * (gamma+eps)^k)
                          α 
                          (gamma * C0 * (gamma+eps)^k)
                          gamma
                          (gamma * C0 * (gamma+eps)^k)
                          glim
                          H7
                          alim
                          H8
                       ); intros.
            rewrite minus_eq_zero in H9.
            rewrite norm_zero in H9.
            cut_to H9; [|(intros; apply Rmult_le_pos; [lra | apply norm_ge_0])].
            apply is_lim_seq_spec in H9.
            unfold is_lim_seq' in H9.
            destruct (H9 (mkposreal _ H3)); simpl in H10.

            assert (forall n, 
                       (x1 <= n)%nat -> (x2 <= n)%nat ->
                       ps_P (event_ge dom
                                      (rvmaxabs (vecrvminus (x (n + nk)%nat) (const xstar)))
                                      (C0 * (gamma + eps)^(S k))) < 1-P).
            {
              intros.
              specialize (H n0 H11).
              specialize (H6 n0 H12).
              assert (event_sub 
                          (event_ge dom (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar)))
                                  (C0 * (gamma + eps) ^ S k))
                        (event_ge dom 
                                  (rvmaxabs (@L2_convergent_x (S n) (fun n => α (n + nk)%nat) (vecrvconst (S n) 0) Ts (vecrvconst (S n) 0) (fun n => w (n + nk)%nat) n0))
                                  (C0 * (gamma + eps) ^ k * (eps / 2)))).
              - intro omega. simpl.
                unfold rvmaxabs; intros.
                generalize (Rvector_max_abs_nth_in  (vecrvminus (x (n0 + nk)%nat) (const xstar) omega) ); intros.
                destruct H14 as [i [pf ?]].
                rewrite H14 in H13.
                apply Rge_trans with 
                    (r2 := Rabs (vector_nth i pf 
                                            (@L2_convergent_x 
                                               (S n) (fun n => α (n + nk)%nat)
                                               (vecrvconst (S n) 0) Ts 
                                               (vecrvconst (S n) 0) 
                                               (fun n => w (n + nk)%nat) n0 omega))).
                + apply Rle_ge.
                  apply Rvector_max_abs_nth_le.
                + rewrite L2_convergent_x_nth_RMseqTs.
                  generalize (Induction_I2_15 
                                (fun n0 => α (n0 + nk)%nat) 
                                (fun n0 => vecrvnth i pf (vecrvminus (x (n0+nk)%nat) (const xstar))) 
                                (vector_nth i pf xstar) 
                                (fun n0 => vecrvnth i pf (w (n0 + nk)%nat))
                                (C0 * (gamma + eps) ^ k) 
                       ); intros.
                  cut_to H15.
                  * specialize (H15 n0 omega).
                    apply Rabs_le_both in H15.
                    clear H0.
                    rewrite  Rabs_lt_both in H; destruct H.
                    apply Rlt_minus_l in H0.
                    generalize (Rle_lt_trans _ _ _ H15 H0); intros.
                    generalize (Rabs_triang_inv
                                  (vecrvnth i pf (vecrvminus (x (n0 + nk)%nat) (const xstar)) omega)
                                  (RMseqTs (fun n0 : nat => α (n0 + nk)%nat)
                                           (fun n0 : nat => vecrvnth i pf (w (n0 + nk)%nat)) 
                                           (const 0) n0 omega)); intros.
                    generalize (Rle_lt_trans _ _ _ H17 H16); intros.
                    apply Rlt_minus_r in H18.
                    unfold Rminus in H18.
                    rewrite Ropp_involutive in H18.
                    rewrite Rplus_comm in H18.
                    apply Rlt_gt in H18.
                    generalize (Rgt_ge_trans _ _ _ H18 H13); intros.
                    apply Rplus_gt_compat_r 
                      with (r := - (C0 * (gamma + eps) ^ k * eps / 2 + gamma * (C0 * (gamma + eps) ^ k))) in H19.
                    ring_simplify in H19.
                    rewrite Rplus_comm in H19.
                    ring_simplify in H19.
                    left.
                    rewrite minus_half in H19.
                    now field_simplify.
                  * intros; apply alim.
                  * intros.
                    specialize (IHk n1 omega0).
                    unfold rvmaxabs in IHk.
                    eapply Rle_trans.
                    apply Rvector_max_abs_nth_le.
                    apply IHk.
                  * intros.
                    assert 
                      (forall n0 : nat,
                          rv_le (rvmaxabs (vecrvminus 
                                             (fun v => F ((x (n0 + nk)%nat) v))
                                             (const (F xstar))))
                                (const  (gamma * C0 * (gamma + eps) ^ k))).
                    -- intros.
                       intro v.
                       unfold rvmaxabs, const, vecrvminus, vecrvplus, vecrvopp, vecrvscale.
                       unfold Rvector_minus, Rvector_opp in Fcont.
                       eapply Rle_trans.
                       apply Fcont.
                       rewrite Rmult_assoc.
                       apply Rmult_le_compat_l; try lra.
                       apply IHk.
                    -- rewrite <- Ropp_mult_distr_l.
                       rewrite <- Ropp_mult_distr_l.
                       apply Rabs_le_both.
                       replace (S n1 + nk)%nat with (S (n1 + nk)) by lia.
                       specialize (xrel (n1 + nk)%nat).
                       assert (rv_eq
                                 (vecrvminus
                                    (vecrvminus (vecrvminus (x (S (n1 + nk))) (const xstar))
                                                (vecrvscale  (1 - α (n1+nk)%nat) (vecrvminus (x (n1 + nk)%nat) (const xstar))))
                                    (vecrvscale (α (n1+nk)%nat) (w (n1 + nk)%nat)))
                                 (vecrvscale (α (n1+nk)%nat) (vecrvminus (fun v => F (x (n1 + nk)%nat v))
                                                                      (const (F xstar))))).
                       ++ intro z.
                          unfold vecrvminus, const, vecrvplus, vecrvopp, vecrvscale.
                          specialize (xrel z).
                          unfold vecrvminus, const, vecrvplus, vecrvopp, vecrvscale in xrel.
                          rewrite xrel.
                          f_equal.
                          apply vector_nth_eq; intros.
                          autorewrite with vector.
                          rewrite Fxstar.
                          ring.
                       ++ specialize (H17 omega0).
                          unfold rvmaxabs, vecrvminus, const, vecrvplus, vecrvopp, vecrvscale in H17.
                          generalize (eq_vector_nths _ _ H17 i pf); intros.
                          specialize (H16 n1 omega0).
                          unfold rvmaxabs, vecrvminus, const, vecrvplus, vecrvopp, vecrvscale in H16.
                          generalize (Rvector_max_abs_nth_le (F (x (n1 + nk)%nat omega0) + -1 .* F xstar) i pf); intros.
                          generalize (Rle_trans _ _ _ H19 H16); intros.
                          apply Rmult_le_compat_l with (r := Rabs (α (n1 + nk)%nat)) in H20; [|apply Rabs_pos].
                          rewrite <- Rabs_mult, <- scale_nth, <- H18 in H20.
                          rewrite Rabs_right with (r := (α (n1 + nk)%nat)) in H20.
                          unfold vecrvnth, vecrvminus, const, vecrvplus, vecrvopp, vecrvscale.
                          unfold vecrvminus, const, vecrvplus, vecrvopp, vecrvscale in H18.                          
                          autorewrite with vector in H20.
                          autorewrite with vector.
                          rewrite Rmult_assoc.
                          rewrite Rmult_assoc in H20.
                          eapply Rle_trans.
                          shelve.
                          apply H20.
                          apply Rle_ge, alim.
                          Unshelve.
                          right.
                          f_equal.
                          unfold Rminus.
                          ring.
              - apply (ps_sub prts) in H13.
                rewrite Rabs_right in H6.
                + eapply Rle_lt_trans.
                  
                  apply H13.
                  replace (C0 * (gamma + eps) ^ k * (eps / 2)) with
                      (C0 * (gamma + eps) ^ k * eps / 2) by lra.
                  rewrite Rminus_0_r in H6.
                  apply H6.
                + rewrite Rminus_0_r.
                  apply Rle_ge.
                  apply ps_pos.
            }
            exists ((max x1 x2) + nk)%nat.
            intros.
            specialize (H11 (n0 + (max x1 x2))%nat).
            cut_to H11; try lia.
            assert (event_sub 
                      (event_complement
                         (event_ge 
                            dom
                            (rvmaxabs (vecrvminus (x (n0 + (max x1 x2 + nk))%nat) 
                                                  (const xstar)))
                            (C0 * (gamma + eps) ^ S k)))
                      (event_le 
                         dom
                         (rvmaxabs (vecrvminus (x (n0 + (max x1 x2 + nk))%nat)
                                               (const xstar)))
                         (C0 * (gamma + eps) ^ S k))) by
                (intro z; simpl; unfold pre_event_complement; lra).
            apply (ps_sub prts) in H12.
            apply Rle_ge in H12. 
            eapply Rge_trans.
            apply H12.
            rewrite ps_complement.
            replace (n0 + (Init.Nat.max x1 x2 + nk))%nat with
                (n0 + Init.Nat.max x1 x2 + nk)%nat by lia.
            lra.
        * intros.
          apply SimpleExpectation_ext.
          intro z.
          unfold rvinner.
          now rewrite vecrvminus_zero.
      + intros.
        generalize (condexp nk n0); intros.
        rewrite <- H1.
        intros ?.
        f_equal.
        repeat f_equal.
        exact H1.
        apply H1.
        (* apply H1. n1 vs n0 ?? *)
        admit.
      + intros.
        generalize (wexp (n0 + nk)%nat); intros.
        admit.
      + intros.
        rewrite minus_eq_zero.
        generalize (@hilbert.norm_zero (@Rvector_PreHilbert (S n))); intros.
        replace (@zero (@Rvector_AbelianGroup (S n))) with (@zero (hilbert.PreHilbert.AbelianGroup (@Rvector_PreHilbert (S n)))); trivial.
        rewrite H1.
        apply Rmult_le_pos; try lra.
        now apply hilbert.norm_ge_0.
    Admitted.
    
    Lemma Induction_I1_15 {n} (eps P C0: posreal) (α : nat -> R) (C : R) (w x : nat -> Ts -> vector R (S n)) (xstar : vector R (S n))
          (F : (vector R (S n)) -> (vector R (S n)))
          {prts: ProbSpace dom}                              
          (rx : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (x n0))
          (rw : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (w n0))
          (srw : forall n0, SimpleRandomVariable  (w n0)) :
      P < 1 ->
      0 <= C ->
      0 <= gamma < 1 ->
      gamma + eps < 1 ->
      (forall n, 0 <= α n <= 1) ->       
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
       (forall (x y : vector R (S n)),
          Rvector_max_abs (Rvector_minus (F x) (F y)) <= 
          gamma * Rvector_max_abs (Rvector_minus x y)) ->
       F xstar = xstar ->
       (forall n,
           (rv_eq (x (S n))
                  (vecrvplus
                     (vecrvscale (1 - α n) (x n)) 
                    (vecrvscale (α n)
                                (vecrvplus (fun v => F (x n v)) (w n)))))) ->
       (forall n, forall omega, 
            rvmaxabs (vecrvminus (x n) (const xstar)) omega <= C0) ->
      (forall n0 : nat, SimpleExpectation (rvinner (w n0) (w n0)) < C) ->
      (forall nk, forall n0,
          rv_eq
            (vector_gen_SimpleConditionalExpectation 
               (w ( n0 + nk)%nat)
               (L2_convergent_hist 
                  (@L2_convergent_x (S n) (fun k => α (k + nk)%nat) 
                                    (vecrvconst (S n) 0) Ts 
                                    (vecrvconst (S n) 0) 
                                    (fun k => w (k + nk)%nat)) _ _ n0)) 
               (const zero)) ->
      forall (k:nat),
      exists (nk : nat),
      forall n0, 
        ps_P 
          (event_le dom
             (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar)))
             (C0 * (gamma + eps)^k))
        >= P^k .
    Proof.
      intros Plim Clim glim geps alim aseq sumaseq Fcont Fxstar xrel xlim wexp condexp k.
       induction k.
      - exists (0%nat).
        intros.
        replace (n0 + 0)%nat with n0 by lia.
        rewrite pow_O.
        rewrite Rmult_1_r.
        rewrite pow_O; right.
        assert (event_equiv 
                   (event_le dom
                      (rvmaxabs (vecrvminus (x (n0 + 0)%nat) (const xstar)))
                      C0)
                    Ω).
        {
          intro omega.
          unfold  Ω, pre_Ω, sa_all; simpl.
          specialize (xlim n0 omega).
          replace (n0 + 0)%nat with (n0) by lia.
          tauto.
        }
        replace (n0 + 0)%nat with n0 in H by lia.
        rewrite H.
        apply ps_one.
      - generalize (Induction_stepk_I1_15 k eps P C0 α C w x xstar F rx rw srw Plim Clim glim geps alim aseq sumaseq Fcont Fxstar xrel xlim wexp condexp); intros.
        Admitted.

    Lemma log_power_base (e b : R ) :
      0 < e -> 0 < b ->
      b <> 1 -> Rpower b (ln e / ln b) = e.
    Proof.
      intros.
      assert (exp (ln (Rpower b (ln e / ln b))) = exp (ln e)).
      { 
        f_equal.
        rewrite Rpower_ln.
        field.
        destruct (Rlt_dec b 1).
        - apply Rlt_not_eq.
          rewrite <- ln_1.
          apply ln_increasing; lra.
        - apply Rgt_not_eq.
          rewrite <- ln_1.
          apply ln_increasing; lra.
      }
      rewrite exp_ln in H2; [|apply Rpower_pos].
      now rewrite exp_ln in H2.
    Qed.
      
    Lemma Rpower_lt1 (b y z : R ) :
      0 < b < 1 -> y < z -> Rpower b y > Rpower b z.
    Proof.
      intros.
      unfold Rpower.
      apply exp_increasing.
      assert (ln b < 0).
      - destruct H.
        rewrite <- ln_1.
        apply ln_increasing; lra.
      - rewrite Rmult_comm with (r1 := z).
        rewrite Rmult_comm with (r1 := y).
        now apply Rmult_lt_gt_compat_neg_l.
    Qed.

    Lemma qlearn_15 {n} (eps C0: posreal) (α : nat -> R) (C : R) (w x : nat -> Ts -> vector R (S n)) (xstar : vector R (S n))
          (F : (vector R (S n)) -> (vector R (S n)))
          {prts: ProbSpace dom}                              
          (rx : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (x n0))
          (rw : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (w n0))
          (srw : forall n0, SimpleRandomVariable  (w n0)) :
      0 <= gamma < 1 ->
      gamma + eps < 1 -> 
      (forall n, 0 <= α n <= 1) ->       
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      F xstar = xstar ->
       (forall n,
           (rv_eq (x (S n))
                  (vecrvplus
                     (vecrvscale (1 - α n) (x n)) 
                    (vecrvscale (α n)
                                (vecrvplus (fun v => F (x n v)) (w n)))))) ->
       (forall n, forall omega, 
            rvmaxabs (vecrvminus (x n) (const xstar)) omega <= C0) ->
      (forall P,
        0 < P < 1 ->
        forall (k:nat),
        exists (nk : nat),
        forall n0, 
          ps_P 
            (event_le dom
                      (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar)))
                      (C0 * (gamma + eps)^k))
          >= P^k) ->
      forall (E : posreal),
        is_lim_seq (fun n => 
                      ps_P 
                        (event_le dom 
                                  (rvmaxabs (vecrvminus (x n) 
                                                        (const xstar)))
                                  E)) 1.
    Proof.
      intros.
      destruct (Rge_dec E C0).
      { 
        apply is_lim_seq_ext with (u := fun _ => 1).
        - intros.
          assert 
            (event_equiv
               (event_le 
                  dom
                  (rvmaxabs (vecrvminus (x n0) (const xstar)))
                  E)
               Ω ).
          + intro z; simpl.
            unfold  pre_Ω.
            split; intros; trivial.
            specialize (H6 n0 z).
            lra.
          + rewrite H8.
            now rewrite ps_all.
        - apply is_lim_seq_const.
      }
      assert (Elim: E < C0) by lra.      
      rewrite <- is_lim_seq_spec.
      unfold is_lim_seq'.
      pose (kstar := (ln(E/C0)/ln((gamma+eps)%R))).
      assert (geps_pos: 0 < gamma + eps).
      {
        rewrite Rplus_comm.
        apply Rplus_lt_le_0_compat; try lra.
        apply cond_pos.
      }
      assert (pos E = C0 * (Rpower (gamma+eps)%R kstar)).
      { 
        assert (pos C0 <> 0) by apply Rgt_not_eq, cond_pos.
        assert (/ C0 <> 0) by now apply Rinv_neq_0_compat.
        rewrite Rmult_comm; trivial.
        apply Rmult_eq_reg_r with (r := /C0); trivial.
        field_simplify; trivial.
        subst kstar.
        rewrite log_power_base; try lra.
        unfold Rdiv.
        apply Rmult_lt_0_compat; [apply cond_pos|].
        apply Rinv_pos, cond_pos.
      }
      pose (kkstar := Z.to_nat (up kstar)).
      intros.
      assert (kstar_pos: kstar > 0).
      {
        subst kstar.
        unfold Rdiv.
        replace (0) with (ln (E * / C0) * 0) by lra.
        apply Rmult_lt_gt_compat_neg_l.
        - replace (0) with (ln 1) by apply ln_1.
          apply ln_increasing.
          apply Rmult_lt_0_compat.
          + apply cond_pos.
          + apply Rinv_0_lt_compat.
            apply cond_pos.
          + rewrite Rmult_comm.
            apply Rmult_lt_reg_l with (r := C0).
            * apply cond_pos.
            * rewrite <- Rmult_assoc.   
              rewrite <- Rinv_r_sym.
              -- lra.
              -- apply Rgt_not_eq.
                 apply cond_pos.
        - apply Rinv_lt_0_compat.
          replace (0) with (ln 1) by apply ln_1.
          apply ln_increasing; lra.
      }
      assert (pos E > C0 * (gamma+eps)%R ^ kkstar).
      {
        rewrite <- Rpower_pow; trivial.
        rewrite H8.
        apply Rmult_gt_compat_l; [apply cond_pos|].
        apply Rpower_lt1.
        - split; trivial.
        - subst kkstar.
          rewrite INR_up_pos; try lra.
          apply archimed.
      }
      pose (pstar := Rmax (1 - eps0/2) (/2)).     
      pose (P := Rpower pstar (/ INR kkstar)).
      specialize (H7 P).
      assert (0 < P < 1).
      {
        subst P.
        split.
        - apply Rpower_pos.
        - rewrite <- Rpower_base_1 with (x := (/ INR kkstar)).
          apply Rlt_Rpower_l.
          + apply Rinv_pos.
            subst kkstar.
            rewrite INR_up_pos; try lra.
            generalize (archimed kstar); lra.
          + subst pstar.
            unfold Rmax.
            assert (0 < eps0) by apply cond_pos.
            match_destr; split; try lra.
      }
      specialize (H7 H10 kkstar).
      destruct H7.
      exists x0; intros.
      specialize (H7 (n1-x0)%nat).
      replace (n1 - x0 + x0)%nat with (n1) in H7 by lia.
      rewrite Rabs_left1.
      - replace (pos eps0) with (- - (pos eps0)) by lra.
        apply Ropp_lt_contravar.
        apply Rplus_lt_reg_r with (x := 1).
        ring_simplify.
        apply Rgt_lt.
        replace (- (pos eps0) + 1)%R with (1 - (pos eps0))%R by lra.
        assert 
          (event_sub
             (event_le 
                dom 
                (rvmaxabs (vecrvminus (x n1) (const xstar))) 
                (C0 * (gamma + eps) ^ kkstar))
             (event_le 
                dom 
                (rvmaxabs (vecrvminus (x n1) (const xstar))) 
                E)).
        {
          intro z; simpl.
          intros.
          apply Rgt_lt in H9.
          left.
          eapply Rle_lt_trans.
          apply H12.
          apply H9.
        }
        apply (ps_sub prts) in H12.
        apply Rle_ge in H12.
        subst P.
        rewrite <- Rpower_pow with 
            (x := Rpower pstar (/ INR kkstar)) in H7 by apply Rpower_pos.
        rewrite Rpower_mult in H7.
        rewrite <- Rinv_l_sym in H7.
        + rewrite Rpower_1 in H7.
          * assert (pstar > 1-eps0).
            -- subst pstar.
               unfold Rmax.
               assert (0 < eps0) by apply cond_pos.
               match_destr; lra.
            -- generalize (Rge_trans _ _ _ H12 H7); intros.
               eapply Rge_gt_trans.
               apply H14.
               apply H13.
          * subst pstar.
            unfold Rmax.
            assert (0 < eps0) by apply cond_pos.
            match_destr; lra.
        + subst kkstar.
          rewrite INR_up_pos; try lra.
          generalize (archimed kstar); intros.
          lra.
      - apply Rplus_le_reg_r with (r := 1).
        ring_simplify.
        apply ps_le1.
   Qed.

  End qlearn4.    
