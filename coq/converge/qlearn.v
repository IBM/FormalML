Require Import List.
Require Import converge.mdp fixed_point.
Require Import RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia.
Require Import infprod Dvoretzky Expectation RandomVariableFinite.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace.
Require Import DVector RealVectorHilbert VectorRandomVariable.
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
    
    Lemma Rmult_lt_1 (a b :R) :
      0 <= a <= 1 ->
      b < 1 ->
      a*b < 1.
   Proof.
     intros.
     destruct H.
     destruct (Rlt_dec 0 a).
     - apply Rmult_lt_compat_l with (r := a) in H0; trivial.
       rewrite Rmult_1_r in H0.
       now generalize (Rlt_le_trans _ _ _ H0 H1).
     - assert (a = 0) by lra.
       subst.
       lra.
   Qed.

   Lemma sum_n_m_shift (α : nat -> R) (k n0 : nat) :
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

      Lemma sum_n_m_pos a n1 n2 :
         (forall n, (n1 <= n <= n2)%nat -> 0 <= a n) ->
         0 <= (sum_n_m a n1 n2).
      Proof.
        intros.
        rewrite sum_n_m_fold_right_seq.
        cut (forall x, List.In x ((List.seq n1 (S n2 - n1))) -> 0 <= a x).
        - generalize ( (List.seq n1 (S n2 - n1))); intros l.
          induction l; simpl; intros.
          + lra.
          + apply Rplus_le_le_0_compat; auto.
        - intros ? inn.
          apply List.in_seq in inn.
          apply H.
          lia.
      Qed.
                                   
    Lemma sum_n_pos_incr a n1 n2 : (forall n, (n1 < n <= n2)%nat -> 0 <= a n) -> 
                                     (n1 <= n2)%nat -> sum_n a n1 <= sum_n a n2.
      Proof.
        intros.
        destruct (Nat.eq_dec n1 n2); [rewrite e; lra|].
        assert (n1 < n2)%nat by lia.
        unfold sum_n.
        rewrite sum_n_m_Chasles with (k:=n2) (m:=n1); try lia.
        replace (sum_n_m a 0 n1) with ((sum_n_m a 0 n1) + 0) at 1 by lra.
        unfold plus; simpl.
        apply Rplus_le_compat_l.
        apply sum_n_m_pos; intros.
        apply H.
        lia.
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

  Definition X := (vector R I).

  Context (gamma : R) (α : nat -> R) {F : X -> X}
          {dom: SigmaAlgebra X} {prts: ProbSpace dom} (x0 : X).

  Context (hF : (@is_contraction Rvector_UniformSpace Rvector_UniformSpace F))
          (lF : (@is_Lipschitz Rvector_UniformSpace Rvector_UniformSpace F gamma)).

    (* Theorem 8 *)

    Global Instance positive_inner (f : X -> X) :
      PositiveRandomVariable (fun v => inner (f v) (f v) ).
    Proof.
      unfold PositiveRandomVariable.
      intros.
      apply inner_ge_0.
    Qed.

    Lemma forall_expectation_ext {rv1 rv2 : nat -> X -> R} :
      (forall n, rv_eq (rv1 n) (rv2 n)) ->
      forall n, Expectation (rv1 n) = Expectation (rv2 n).
    Proof.
      intros.
      now apply Expectation_ext.
    Qed.

    Lemma forall_SimpleRandomVariable_ext {rv1 rv2 : nat -> X -> R} 
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

    Lemma forall_SimpleExpectation_ext {rv1 rv2 : nat -> X -> R} 
          {srv1 : forall n, SimpleRandomVariable (rv1 n)}
          {srv2 : forall n, SimpleRandomVariable (rv2 n)} :
      (forall n, rv_eq (rv1 n) (rv2 n)) ->
      forall n, SimpleExpectation (rv1 n) = SimpleExpectation (rv2 n).
    Proof.
      intros.
      now apply SimpleExpectation_ext.
    Qed.

    Lemma isfinexp_finite_neg_part (rv_X : X -> R)
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

  Lemma Expectation_pos_finite_neg_part (rv_X : X -> R) 
        {prv : PositiveRandomVariable rv_X} :
    is_finite (Expectation_posRV (neg_fun_part rv_X)).
  Proof.
    unfold neg_fun_part; simpl.
    unfold PositiveRandomVariable in prv.
    assert (rv_eq (fun x : X => Rmax (- rv_X x) 0) (const 0)).
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
        (rv_X1 rv_X2 : X -> R)
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


   Lemma rv_inner_plus_l (x y z : X) :
     Rvector_inner (Rvector_plus x y) z = 
     (Rvector_inner x z) + (Rvector_inner y z).
   Proof.
     now generalize (inner_plus_l x y z).
   Qed.

   Lemma rv_inner_plus_r (x y z : X) :
     Rvector_inner x (Rvector_plus y z) = 
     (Rvector_inner x y) + (Rvector_inner x z).
    Proof.
      now generalize (inner_plus_r x y z).
    Qed.
   
   Lemma rv_inner_scal_l (x y : X) (l : R) :
     Rvector_inner (Rvector_scale l x) y = l * Rvector_inner x y.
   Proof.
     now generalize (inner_scal_l x y l).
   Qed.

   Lemma rv_inner_scal_r (x y : X) (l : R) :
     Rvector_inner x (Rvector_scale l y) = l * Rvector_inner x y.
   Proof.
     now generalize (inner_scal_r x y l).
   Qed.

   Lemma rv_inner_sym (x y : X) :
     Rvector_inner x y = Rvector_inner y x.
   Proof.
     now generalize (inner_sym x y).
   Qed.

   Lemma rv_inner_ge_0 (x : X) :
      0 <= Rvector_inner x x.
   Proof.
     now generalize (inner_ge_0 x).
   Qed.
(*
   Definition F_alpha (a : R)  :=
     (@f_alpha Rvector_NormedModule F a).

    Definition f_alpha (f : X -> X) a : (X -> X)  :=
      fun (x:X) => plus (scal (1-a) x) (scal a (f x)).
*)

   Definition F_alpha (a : R) (x : X -> X) :=
     vecrvplus (vecrvscale (1-a) x) (vecrvscale a (fun v => F (x v))).

  Instance srv_Fa (a:R) (x: X -> X)
           (srvx : SimpleRandomVariable x) :
    SimpleRandomVariable (F_alpha a x).
  Proof.
    unfold F_alpha.
    apply srv_vecrvplus.
    typeclasses eauto.
    typeclasses eauto.
  Qed.

  Lemma vec_sa_singleton {n} (rv_X : X -> vector R n)
        {rv : RandomVariable dom (Rvector_borel_sa n) rv_X} :
    forall c, sa_sigma (event_preimage rv_X (event_singleton c)).
  Proof.

    intros.
    generalize  (RandomVariableRealVectorMeasurable rv_X); intros.
    unfold RealVectorMeasurable in H.
    unfold event_preimage, event_singleton.
    unfold X in *.
    simpl in H.
    
    assert (event_equiv 
              (fun omega : X => rv_X omega = c)
              (inter_of_collection
                 (fun i => match lt_dec i n with
                        | left pf => fun omega => vector_nth i pf (rv_X omega) = vector_nth i pf c
                        | right _ => Ω
                        end))).
    {
      intros e.
      split; intros HH.
      - intros i.
        match_destr.
        + congruence.
        + now red.
      - apply vector_nth_eq; intros.
        specialize (HH i); simpl in HH.
        match_destr_in HH; try lia.
        now replace pf with l by apply le_uniqueness_proof.
    }
    rewrite H0.
    apply sa_countable_inter; intros.
    match_destr.
    - specialize (H _ l).
      apply measurable_rv in H.
      rewrite vector_nth_fun_to_vector in H.
      now apply sa_singleton.
    - apply sa_all.
  Qed.                 

  Instance rv_fun_simple (x f : X -> X)
            (rvx : RandomVariable dom (Rvector_borel_sa I) x) 
            (srvx : SimpleRandomVariable x) :
     RandomVariable dom (Rvector_borel_sa I) (fun u => f (x u)).    
  Proof.
    apply RealVectorMeasurableRandomVariable.
    intros i pf.
    apply rv_measurable.
    simpl.
    rewrite vector_nth_fun_to_vector.
    generalize (vec_srv _ i pf srvx); intros srv.
    simpl in srv.
    rewrite vector_nth_fun_to_vector in srv.
    apply RandomVariableRealVectorMeasurable in rvx.
    specialize (rvx i pf).
    apply measurable_rv in rvx.
    simpl in rvx.
    rewrite vector_nth_fun_to_vector in rvx.

    (*

    
    
    generalize (srv_fun x f srvx); intros.

    apply srv_singleton_rv with (srv:=X0); trivial.
    destruct X0.
    destruct srvx.
    intros c cinn.
    generalize (vec_sa_singleton x); intros.
    unfold event_preimage, event_singleton.
    assert (event_equiv (fun omega : X => f (x omega) = c)
                        (list_union
                           (map (fun sval =>
                                   (fun omega =>
                                      (x omega = sval) /\ (f sval = c)))
                                srv_vals0))).
    admit.
    rewrite H0.
    apply sa_list_union.
    intros.
    rewrite in_map_iff in H1.
    destruct H1.
    destruct H1.
    rewrite <- H1.
    assert (event_equiv (fun omega : X => x omega = x2 /\ f x2 = c)
                        (event_inter (fun omega => x omega = x2)
                                     (fun _ => f x2 = c))).
    intro u.
    now unfold event_inter.
    rewrite H3.
    apply sa_inter.
    apply H.
    apply sa_sigma_const.
    apply classic_event_lem.

    Admitted.
     *)
   Instance rv_Fa (a:R) (x: X -> X) 
            (rvx : RandomVariable dom (Rvector_borel_sa I) x) 
            (srvx : SimpleRandomVariable x) :
     RandomVariable dom (Rvector_borel_sa I) (F_alpha a x).
   Proof.
     eapply srv_singleton_rv with (srv:=srv_Fa _ _ _).
     intros.
     apply vec_sa_singleton.
     unfold F_alpha.
     typeclasses eauto.
  Qed.
   
   Lemma L2_convergent_helper (C : R) (w x : nat -> X -> X) (xstar : X) (n:nat)
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
        repeat rewrite rv_inner_plus_l.
        repeat rewrite rv_inner_plus_r.        
        repeat rewrite rv_inner_scal_l.
        repeat rewrite rv_inner_scal_r.
        ring_simplify.
        repeat rewrite Rplus_assoc.
        repeat apply Rplus_eq_compat_l.
        replace (Rvector_inner (w n v) (F_alpha (α n) (x n) v)) with 
            (Rvector_inner (F_alpha (α n) (x n) v) (w n v)) by apply rv_inner_sym.
        replace (Rvector_inner (w n v) (const xstar v)) with
                (Rvector_inner (const xstar v) (w n v)) by apply rv_inner_sym.
        now ring_simplify.
     }
      generalize (SimpleExpectation_ext _ _ H3); intros.
      rewrite <- sumSimpleExpectation in H4; [|typeclasses eauto | typeclasses eauto].
      rewrite <- sumSimpleExpectation in H4; [|typeclasses eauto | typeclasses eauto].
      rewrite <- scaleSimpleExpectation in H4.
      rewrite <- scaleSimpleExpectation in H4.      
      rewrite H0 in H4.
      rewrite Rmult_0_r in H4.
      ring_simplify in H4.
      generalize (SimpleExpectation_le _ _ H1); intros.
      rewrite H4.      
      rewrite <- scaleSimpleExpectation in H5.
      apply Rplus_le_compat.
      apply H5.
      apply Rmult_le_compat_l.
      apply pow2_ge_0.
      now left.
    Qed.

    Lemma SimpleExpectation_rvinner_pos (f : X -> X) 
          (rx : RandomVariable dom (Rvector_borel_sa I) f)
          (srv: SimpleRandomVariable f) :
      0 <= SimpleExpectation (rvinner f f).
    Proof.
      replace (0) with (SimpleExpectation (const 0)).
      apply SimpleExpectation_le.
      apply rvconst.
      now apply Rvector_inner_rv.
      intro v.
      now generalize (inner_ge_0 (f v)).
      apply SimpleExpectation_const.
   Qed.

    Lemma aux_seq (C: R) (x : nat -> X -> X) (v : nat -> R) (xstar : X)
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
      typeclasses eauto.
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

    Lemma Rmult_le_1 (a b :R) :
      0 <= a <= 1 ->
      0 <= b <= 1 ->
      0 <= a*b <= 1.
    Proof.
      intros.
      split.
      now apply Rmult_le_pos.
      replace (1) with (1 * 1) by lra.
      now apply Rmult_le_compat.
    Qed.

    Lemma aux_seq_lim (C: R) (x : nat -> X -> X) (v : nat -> R) (xstar : X)
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

    Theorem L2_convergent (C : R) (w x : nat -> X -> X) (xstar : X)
         (rx : forall n, RandomVariable dom (Rvector_borel_sa I) (x n))
         (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n))
         (srw : forall n, SimpleRandomVariable  (w n)) 
         (srx : forall n, SimpleRandomVariable  (x n)) :
      0 <= C ->
      0 <= gamma < 1 ->
      xstar = F xstar ->
      (forall n, 0 <= α n <= 1) -> 
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      (forall k, (x (S k)) = 
                 vecrvplus (F_alpha (α k) (x k))
                           (vecrvscale (α k) (w k))) ->
      (forall n, SimpleExpectation
                   (rvinner
                      (vecrvminus (F_alpha (α n) (x n)) 
                                  (const xstar))
                      (w n)) = zero) ->
      (forall n, SimpleExpectation (rvinner (w n) (w n)) < C)  ->
      (forall x1 y : vector R I, Hnorm (minus (F x1) (F y)) <= gamma * Hnorm (minus x1 y)) -> 
      is_lim_seq 
        (fun n => SimpleExpectation
                    (rvinner (vecrvminus (x n) (const xstar))
                             (vecrvminus (x n) (const xstar)))) 0.
    Proof.
      intros Cpos grel xfix arel alim aser xrel xterm wbound Fcontract.
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
        apply L2_convergent_helper with (w := w) (srw := srw); trivial.

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
                    ** rewrite scal_minus_distr_r with (x1 := 1).
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

      

