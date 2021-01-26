Require Import converge.mdp LM.fixed_point.
Require Import RealAdd.
Require Import micromega.Lra.

Set Bullet Behavior "Strict Subproofs".

  Section qlearn.

    Fixpoint list_product (l : list R) : R :=
      match l with
      | nil => 1
      | cons x xs => x*list_product xs
      end.

    (* Lemma 4 of Vasily's blueprint.*)
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

    Definition is_norm_Lipschitz {K1 K2: AbsRing}
               {X : NormedModule K1} {Y : NormedModule K2} (f: X -> Y) (k:R) :=
      0 <= k /\
        forall x1 x2 r, 0 < r ->
        ball_norm x1 r x2 -> ball_norm (f x1) (k*r) (f x2).

    Definition is_norm_contraction {K1 K2: AbsRing}
               {X : NormedModule K1} {Y : NormedModule K2}(f: X -> Y) :=
      exists k, k < 1 /\ is_norm_Lipschitz f k.

    Lemma ball_norm_zero {K : AbsRing} (X : NormedModule K) :
      forall x y : X, ball_norm x 0 y -> x=y.
    Proof.
      intros.
      unfold ball_norm in H.
      generalize (norm_ge_0 (minus y x)); intros Hge.
      assert (norm (minus y x) = 0) by lra.
      generalize (norm_eq_zero (minus y x) H0); intros Hmz.
      replace (zero) with (minus x x) in Hmz by (apply minus_eq_zero).
      unfold minus in Hmz.
      eapply plus_reg_r; eauto.
    Qed.

    Lemma is_norm_Lipschitz_zero  {K1 K2: AbsRing}
          {X : NormedModule K1} {Y : NormedModule K2} (f: X -> Y):
      is_norm_Lipschitz f 0 -> (forall x y, f x = f y).
    Proof.
      intros Hl x y.
      unfold is_norm_Lipschitz in Hl.
      destruct Hl as [? Hn].
      apply ball_norm_zero.
      replace 0 with (0*(norm(minus y x) + 1)) by lra.
      apply Hn.
      + replace 0 with (0+0) by lra.
        apply Rplus_le_lt_compat; try lra.
        apply norm_ge_0.
      + unfold ball_norm.
        apply Rlt_n_Sn.
    Qed.

    Context {X : CompleteNormedModule R_AbsRing} {F : X -> X}
            (hF : is_norm_contraction F) (α : nat -> R) (x0 : X).

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

    Lemma is_norm_contraction_RMsync (r : R) :
      (0<r<1) ->
      is_norm_contraction (fun (x : X) => plus (scal (1 - r) x) (scal r (F x))).
    Proof.
      intros Hr.
      unfold is_norm_contraction.
      destruct hF as [γ [Hγ HF]].
      exists (1 - r + r*γ).
      split.
      + destruct HF.
        rewrite <-(Rplus_0_r).
        replace (1 -r + r*γ) with (1 + r*(γ-1)) by lra.
        apply Rplus_lt_compat_l.
        replace 0 with (r*0) by lra.
        apply Rmult_lt_compat_l ; lra.
      + unfold is_Lipschitz in *.
        destruct HF as [Hγ0 HF].
        split; intros.
        ++ replace 0 with  (0+0) by lra.
          apply Rplus_le_compat.
          --- lra.
          --- replace 0 with (r*0) by lra.
              apply Rmult_le_compat_l ; lra.
        ++ rewrite Rmult_plus_distr_r.
           unfold ball_norm.
          rewrite plus_minus_scal_distr.
          generalize (norm_triangle (scal (1-r) (minus x2 x1)) (scal r (minus (F x2) (F x1)))) ; intros.
          eapply Rle_lt_trans ; eauto.
          apply Rplus_lt_compat.
          --  generalize (norm_scal (1-r) (minus x2 x1)) ; intros.
              eapply Rle_lt_trans ; try apply H2.
              unfold abs ; simpl.
              replace (Rabs (1-r)) with (1-r) by (symmetry; try apply Rabs_pos_eq;
                                                  try (lra)).
              apply Rmult_lt_compat_l ; try lra.
              eapply Rlt_le_trans ; eauto ; try lra.
          -- generalize (norm_scal r (minus (F x2) (F x1))); intros.
              eapply Rle_lt_trans; eauto.
              unfold abs ; simpl.
              rewrite Rabs_pos_eq ; try (left ; lra).
              rewrite Rmult_assoc.
              apply Rmult_lt_compat_l; try lra.
              specialize (HF (x1) (x2) r0 H H0).
              unfold ball_norm in HF.
              assumption.
    Qed.


  End qlearn.
