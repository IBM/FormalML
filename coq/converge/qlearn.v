Require Import converge.mdp LM.fixed_point.
Require Import micromega.Lra.

Set Bullet Behavior "Strict Subproofs".

  Section qlearn.

    Context {X : CompleteNormedModule R_AbsRing} {F : X -> X}
            (hF : is_contraction F) (α : nat -> R) (x0 : X).

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

    Lemma is_contraction_RMsync (r : R) :
      (0<r<1) -> (@norm_factor R_AbsRing X <= 1) -> is_contraction (fun (x : X) => plus (scal (1 - r) x) (scal r (F x))).
    Proof.
      intros Hr Hnf.
      unfold is_contraction.
      destruct hF as [γ [Hγ HF]].
      exists (1 - r + r*γ).
      split.
      + admit.
      + unfold is_Lipschitz in *.
        destruct HF as [Hγ0 HF].
        split; intros.
        ++ admit.
        ++ rewrite Rmult_plus_distr_r.
           apply (@norm_compat1 R_AbsRing X).
           rewrite plus_minus_scal_distr.
           generalize (norm_triangle (scal (1-r) (minus x2 x1)) (scal r (minus (F x2) (F x1)))) ; intros.
           eapply Rle_lt_trans ; eauto.
           apply Rplus_lt_compat.
           -- unfold ball_x in H0.
              generalize (norm_scal (1-r) (minus x2 x1)) ; intros.
              eapply Rle_lt_trans ; try apply H2.
              generalize (@norm_compat2 R_AbsRing X x1 x2 (mkposreal r0 H)) ; intros.
              specialize (H3 H0).
              unfold abs ; simpl.
              replace (Rabs (1-r)) with (1-r) by (symmetry; try apply Rabs_pos_eq; try (left ; lra)).
              apply Rmult_lt_compat_l ; try lra.
              simpl in H3. eapply Rlt_le_trans ; eauto.
              rewrite <-Rmult_1_l.
              apply Rmult_le_compat_r ; lra.
           -- generalize (norm_scal r (minus (F x2) (F x1))); intros.
              eapply Rle_lt_trans; eauto.
              unfold abs ; simpl.
              rewrite Rabs_pos_eq ; try (left ; lra).
              rewrite Rmult_assoc.
              apply Rmult_lt_compat_l; try lra.
              specialize (HF (x1) (x2) r0 H H0).
              unfold ball_y in HF.
              enough (0 < γ*r0).
              generalize (@norm_compat2 R_AbsRing X (F x1) (F x2) (mkposreal _ H3) HF); intros.
              eapply Rlt_le_trans ; eauto.
              simpl.
              rewrite <-Rmult_1_l.
              apply Rmult_le_compat_r ; lra.
              admit.
    Admitted.

  End qlearn.
