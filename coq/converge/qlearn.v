Require Import converge.mdp LM.fixed_point.
Require Import RealAdd.
Require Import utils.Utils.
Require Import Lra Lia.

Set Bullet Behavior "Strict Subproofs".

  Section qlearn.

    Lemma ball_zero_eq {K : AbsRing} (X : NormedModule K) :
      forall x y : X, ball x 0 y -> x=y.
    Proof.
      intros x y Hxy.
      apply eq_close.
      intros eps.
      apply ball_le with (e1 := 0).
      + left. apply cond_pos.
      + assumption.
    Qed.

    Context {X : CompleteNormedModule R_AbsRing} {F : X -> X}
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


    Lemma is_contraction_RMsync (r : R) :
      (0<r<1) -> (@norm_factor R_AbsRing X <= 1) ->
      is_contraction (fun (x : X) => plus (scal (1 - r) x) (scal r (F x))).
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

    Theorem Vasily_2a gamma xstar :
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
                 
    Theorem Vasily_2b gamma xstar :
      0 <= gamma < 1 ->
      xstar = F xstar ->
      (forall n, 0 <= α n <= 1) ->
      is_lim_seq (fun n => prod_f_R0 (fun k => g_alpha gamma (α k)) n) 0 ->
      (forall x y, norm(minus (F x) (F y)) <= gamma * norm (minus x y)) ->
      is_lim_seq (fun n => norm (minus (RMsync n) xstar)) 0.
    Proof.
      intros.
      generalize (Vasily_2a gamma xstar H H0 H1 H3); intros.
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

  End qlearn.

  Section qlearn2.
    
    Context {X : CompleteNormedModule R_AbsRing} (α : nat -> R).

    Fixpoint RMseq (s : nat -> R) (init : R) (n : nat) : R :=
      match n with
      | 0 => init
      | (S k) => plus (scal (1 - α k) (RMseq s init k)) (scal (α k) (s k))
      end.

    Fixpoint RMseqX (f : nat -> X -> X) (init : X) (n : nat) : X :=
      match n with
      | 0 => init
      | (S k) => plus (scal (1 - α k) (RMseqX f init k)) (scal (α k) (f k (RMseqX f init k)))
      end.
      
    Fixpoint RMseqG (init gamma C : R) (n : nat) : R :=
      match n with
      | 0 => init
      | (S k) => plus (scal (g_alpha gamma (α k)) (RMseqG init gamma C k)) (scal (α k) C)
      end.

    Lemma helper_bounding_5 (s1 s2 : nat -> R) (init1 init2 : R) :
      0 <= init1 <= init2 ->
      (forall n, 0 <= (α n) <= 1) ->
      (forall n, 0 <= s1 n <= s2 n) ->
      forall n, 0 <= RMseq s1 init1 n <= RMseq s2 init2 n.
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

    Lemma helper_convergence_6 (delta : nat -> R) (init:R) :
      0 <= init ->
      (forall n, 0 <= (α n) <= 1) ->
      (forall n, 0 <= delta n) ->
      is_lim_seq α 0 ->
      is_lim_seq delta 0 ->
      (forall k, is_lim_seq (fun n => prod_f_R0 (fun m => 1 - (α (m + k)%nat)) n) 0) ->
      is_lim_seq (RMseq delta init) 0.
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
      generalize (helper_bounding_5 (fun n => delta (N+n)%nat) (fun _ => eps/2) (RMseq delta init N) (RMseq delta init N)); intros.

      generalize (@Vasily_2b R_CompleteNormedModule (fun _ => eps/2) α (RMseq delta init N) 0 (eps/2)).

      Admitted.



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

    Lemma bounding_7 (gamma C : R) (f : nat -> X -> X) (init : X) :
      0 <= gamma < 1 -> 0 <= C ->
      (forall n, 0 <= (α n) <= 1) ->
      (forall n x, norm (f n x) <= gamma * norm x + C) ->
      is_lim_seq α 0 ->
      (forall k, is_lim_seq (fun n => prod_f_R0 (fun m => g_alpha gamma (α (m+k))) n) 0) ->
      exists B, forall n, norm ( RMseqX f init n) <= B.
    Proof.
      intros.
      assert (forall n, norm(RMseqX f init (S n)) <= (1 - α n)*norm(RMseqX f init n) + (α n)*(gamma * norm (RMseqX f init n) + C)).
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

      assert (forall n,  norm(RMseqX f init (S n)) <= (g_alpha gamma  (α n)) * norm(RMseqX f init n) + (α n)*C).
      {
        intros.
        eapply Rle_trans.
        apply H5.
        unfold g_alpha.
        lra.
     }

      assert (forall n, norm(RMseqX f init n) <= RMseqG (norm init) gamma C n).
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
      
      generalize (@Vasily_2b R_CompleteNormedModule (fun s => gamma * s + C) α (norm init) gamma (C/(1-gamma)) H); intros.
      assert (exists B2, forall n, RMseqG (norm init) gamma C n <= B2).
      {
        cut_to H8; trivial.
        - apply finite_lim_bound with (lim := C / (1 - gamma)).
          rewrite <- is_lim_seq_abs_0 in H8.
          generalize (is_lim_seq_const (C / (1 - gamma))); intros.
          generalize (is_lim_seq_plus' _ _ _ _ H8 H9); intros.
          rewrite Rplus_0_l in H10.
          apply is_lim_seq_ext with (v := (fun n => (@RMsync R_CompleteNormedModule (fun s => gamma * s + C) α (norm init) n)) ) in H10.
          + apply is_lim_seq_ext with (v :=  (RMseqG (norm init) gamma C)) in H10.
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
                 rewrite Rplus_assoc.
                 rewrite Rplus_assoc.
                 apply Rplus_eq_compat_l.
                 now rewrite Rplus_comm.
          + intros.
            unfold minus; simpl.
            unfold plus; simpl.
            unfold opp; simpl.
            now ring_simplify.
        - simpl; field.
          lra.
        - specialize (H4 0%nat).
          apply is_lim_seq_ext with (u := (fun n : nat => prod_f_R0 (fun k : nat => g_alpha gamma (α (k + 0)%nat)) n)).
          intros.
          f_equal.
          apply FunctionalExtensionality.functional_extensionality; intros.
          f_equal.
          f_equal; lia.
          apply H4.
        - intros.
          unfold minus, plus, opp; simpl.
          right.
          unfold norm; simpl.
          unfold abs; simpl.
          replace (gamma * x + C + - (gamma * y + C)) with (gamma * (x + - y)) by lra.
          rewrite Rabs_mult.
          rewrite Rabs_right; lra.
      }
      destruct H9.
      exists x.
      intros.
      eapply Rle_trans.
      apply H7.
      apply H9.
    Qed.


