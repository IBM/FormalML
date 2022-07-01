Require Import List.
Require Import mdp qvalues fixed_point.
Require Import RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import infprod Dvoretzky Expectation RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace.
Require Import DVector RealVectorHilbert VectorRandomVariable.
Require Import RandomVariableL2.
Require hilbert.
Require Import vecslln.
Require Import ConditionalExpectation VectorConditionalExpectation.
Require Import IndefiniteDescription ClassicalDescription.
Require slln.
Require Import qlearn_aux.

Set Bullet Behavior "Strict Subproofs".

(*
****************************************************************************************
This file is a work-in-progress proof of convergence of the classical Q-learning
algorithm.
****************************************************************************************
*)

Section testQ.

  Context {M : MDP}.
  
  Definition Ts := {x : state M & act M x} .
  Definition Td := Rfct Ts.

  Context {r : Ts -> state M -> R} {gamma : R} (α : nat -> R).

  Definition maxactval := fun W s' => Max_{@act_list M s'}(fun a => W (existT _ s' a)).

  Fixpoint tvector (A:Type) (n:nat) : Type
    := match n with
       | 0%nat => unit
       | S m => prod A (tvector A m)
       end.

  Fixpoint Q (init:Td) (combine:Ts->Td->Td) (n:nat) : tvector Ts n -> Td
    := match n as n' return tvector Ts n' -> Td with
       | 0 => fun _ => init
       | S m => fun '(a, x) =>
                 let b := Q init combine m x in
                 combine a b
       end.

  Definition BellQ (n:nat) (QQ : Td) (sa : Ts) (s' : state M) : Td :=
    fun sa1 => if EqDecsigT sa sa1 then 
                    (r sa s') + gamma * maxactval QQ s'
                  else (QQ sa1).

  Definition Qcombine (n:nat) (sa : Ts) (s' : state M) (W : Td) : Td :=
    fun sa1 => (1 - α n) * (W sa1) + (α n) * ((BellQ n W sa s') sa1).

  Fixpoint Q1 (init:Td) (n:nat) (s' : Ts) : tvector Ts n -> Td
    := match n as n' return tvector Ts n' -> Td with
       | 0 => fun _ => init
       | S m => fun '(a, x) =>
                 let b := Q1 init m a x in
                 Qcombine m a (projT1 s') b 
       end.

End testQ.

Section rv_expressible.

  Lemma increasing_seq (f : nat -> R) :
    (forall n, f n <= f (S n)) ->
    forall (n d : nat),
      f n <= f (n + d)%nat.
   Proof.
    intros.
    induction d.
    - replace (n + 0)%nat with n by lia.
      lra.
    - eapply Rle_trans.
      + apply IHd.
      + replace (n + S d)%nat with (S (n + d))%nat by lia.
        apply H.
  Qed.

  Lemma is_sup_seq_increasing (f : nat -> R) :
    (forall n, f n <= f (S n)) ->
    forall (x:R),
      is_sup_seq f x <-> is_lim_seq f x.
  Proof.
    intros.
    unfold is_sup_seq.
    split; intros.
    - apply is_lim_seq_spec.
      unfold is_lim_seq'.
      intros.
      destruct (H0 eps).
      simpl in H1.
      simpl in H2.
      destruct H2.
      exists x0.
      intros.
      rewrite Rabs_lt_between.
      specialize (H1 n).
      split.
      + generalize (increasing_seq f H x0 (n-x0)%nat); intros.
        replace (x0 + (n - x0))%nat with n in H4 by lia.
        lra.
      + lra.
    - apply is_lim_seq_spec in H0.
      unfold is_lim_seq' in H0.
      simpl.
      destruct (H0 eps).
      split.
      + intros.
        generalize (H1 n); intros.
        destruct (le_dec x0 n).
        * specialize (H2 l).
          rewrite Rabs_lt_between in H2.
          lra.
        * specialize (H1 x0).
          generalize (increasing_seq f H n (x0-n)%nat); intros.
          replace (n + (x0 - n))%nat with x0 in H3 by lia.
          eapply Rle_lt_trans.
          -- apply H3.
          -- cut_to H1; try lia.
             rewrite Rabs_lt_between in H1.
             lra.
      + exists x0.
        specialize (H1 x0).
        cut_to H1; try lia.
        rewrite Rabs_lt_between in H1.        
        lra.
  Qed.

  Lemma Rbar_is_sup_seq_increasing (f : nat -> R) :
    (forall n, f n <= f (S n)) ->
    forall (x:Rbar),
      is_sup_seq f x <-> is_lim_seq f x.
  Proof.
    intros.
    destruct x.
    - now apply is_sup_seq_increasing.
    - unfold is_sup_seq.
      split; intros.
      + apply is_lim_seq_spec.
        unfold is_lim_seq'.
        intros.
        destruct (H0 M).
        simpl in H1.
        exists x.
        intros.
        eapply Rlt_le_trans.
        * apply H1.
        * generalize (increasing_seq f H x (n-x)%nat); intros.
          now replace (x + (n - x))%nat with n in H3 by lia.
     + apply is_lim_seq_spec in H0.
       destruct (H0 M).
       simpl.
       exists x.
       apply H1.
       lia.
   - unfold is_sup_seq.
     split; intros.
     + apply is_lim_seq_spec.
       unfold is_lim_seq'.
       intros.
       specialize (H0 M).
       exists 0%nat.
       intros.
       apply H0.
     + apply is_lim_seq_spec in H0.
       specialize (H0 M).
       destruct H0.
       simpl.
       destruct (le_dec x n).
       * now apply H0.
       * assert (n < x)%nat by lia.
         generalize (increasing_seq f H n (x - n)%nat); intros.
         replace (n + (x - n))%nat with x in H2 by lia.
         eapply Rle_lt_trans.
         -- apply H2.
         -- apply H0.
            lia.
    Qed.    

    Lemma nonneg_measurable_is_expressible {Ts : Type} {Td : Type}
          {dom : SigmaAlgebra Ts} {cod : SigmaAlgebra Td}
          (X : Ts -> Td) (Y : Ts -> R)
          {rv_X : RandomVariable dom cod X}
          {nn_Y : NonnegativeFunction Y}
          {rv_y : RandomVariable (pullback_sa cod X) borel_sa Y} :
      exists g : Td -> Rbar, 
        RandomVariable cod Rbar_borel_sa g /\
        forall x, Finite (Y x) = (g (X x)).
    Proof.
      generalize (simple_approx_lim_seq Y nn_Y); intros.
      generalize (fun n => simple_approx_frf Y n); intros frf.
      assert (forall n, RandomVariable (pullback_sa cod X) borel_sa (simple_approx Y n)).
      {
        intros.
        apply simple_approx_rv; trivial.
        now apply borel_Rbar_borel.
      }
      generalize (fun n =>
                    frf_measurable_is_expressible' X (simple_approx Y n)); intros.
      exists (fun z => Sup_seq (fun n => (proj1_sig (X0 n)) z)).
      split.
      - apply Sup_seq_rv.
        intros.
        apply Real_Rbar_rv.
        unfold proj1_sig.
        now match_destr.
      - intros.
        specialize (H x).
        rewrite <- is_sup_seq_increasing in H.
        + apply is_sup_seq_unique in H.
          rewrite <- H.
          apply Sup_seq_ext.
          intros.
          unfold proj1_sig.
          match_destr.
          destruct a.
          rewrite Rbar_finite_eq.
          apply H2.
        + intros.
          now apply simple_approx_increasing.
     Qed.
    
    Lemma nonneg_measurable_is_expressible' {Ts : Type} {Td : Type}
          {dom : SigmaAlgebra Ts} {cod : SigmaAlgebra Td}
          (X : Ts -> Td) (Y : Ts -> R)
          {rv_X : RandomVariable dom cod X}
          {nn_Y : NonnegativeFunction Y}
          {rv_y : RandomVariable (pullback_sa cod X) borel_sa Y} :
      {g : Td -> Rbar |
        RandomVariable cod Rbar_borel_sa g /\
        forall x, Finite(Y x) = (g (X x))}.
   Proof.
      apply constructive_indefinite_description.
      now apply nonneg_measurable_is_expressible.
    Qed.

    Lemma measurable_is_expressible {Ts : Type} {Td : Type}
          {dom : SigmaAlgebra Ts} {cod : SigmaAlgebra Td}
          (X : Ts -> Td) (Y : Ts -> R)
          {rv_X : RandomVariable dom cod X}
          {rv_y : RandomVariable (pullback_sa cod X) borel_sa Y} :
      exists g : Td -> Rbar, 
        RandomVariable cod Rbar_borel_sa g /\
        forall x, Finite (Y x) = (g (X x)).
    Proof.
      generalize (nonneg_measurable_is_expressible' X (pos_fun_part Y)); intros pos.
      generalize (nonneg_measurable_is_expressible' X (neg_fun_part Y)); intros neg.
      exists (Rbar_rvminus (proj1_sig pos) (proj1_sig neg)).
      split.
      - apply Rbar_rvminus_rv.
        + unfold proj1_sig.
          now match_destr.
        + unfold proj1_sig.
          now match_destr.
      - intros.
        unfold proj1_sig.
        match_destr; match_destr.
        destruct a; destruct a0.
        specialize (H0 x).
        specialize (H2 x).
        unfold Rbar_rvminus, Rbar_rvplus, Rbar_rvopp.
        rewrite <- H0.
        rewrite <- H2.
        generalize (rv_pos_neg_id Y); intros.
        specialize (H3 x).
        rewrite H3.
        unfold rvplus, rvopp, rvscale.
        simpl.
        apply Rbar_finite_eq.
        lra.
    Qed.

    Lemma measurable_is_expressible' {Ts : Type} {Td : Type}
          {dom : SigmaAlgebra Ts} {cod : SigmaAlgebra Td}
          (X : Ts -> Td) (Y : Ts -> R)
          {rv_X : RandomVariable dom cod X}
          {rv_y : RandomVariable (pullback_sa cod X) borel_sa Y} :
      {g : Td -> Rbar |
        RandomVariable cod Rbar_borel_sa g /\
        forall x, Finite (Y x) = (g (X x))}.
    Proof.
      apply constructive_indefinite_description.
      now apply measurable_is_expressible.
    Qed.

End rv_expressible.

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

    (*TODO: Use this to simplify the proof above. *)
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

    (* Product of a list of real numbers. Move this to RealAdd.v *)
    Fixpoint list_product (l : list R) : R :=
      match l with
      | nil => 1
      | cons x xs => x*list_product xs
      end.

    Lemma list_product_pos (l : list R) :
      List.Forall (fun r => 0 < r) l -> 0 < list_product l.
    Proof.
      intros H.
      induction l; simpl; try lra.
      invcs H; try intuition.
      apply Rmult_lt_0_compat; assumption.
    Qed.

    Lemma log_list_product (l : list R) :
      List.Forall (fun r => 0 < r) l ->
      ln (list_product l) = list_sum (map (fun x => ln x) l).
    Proof.
      intros H.
      induction l.
      + simpl.
        apply ln_1.
      + simpl. invcs H.
        specialize (IHl H3).
        rewrite ln_mult; try assumption.
        - now f_equal.
        - now apply list_product_pos.
    Qed.

    (* Lemma 4.*)
    Lemma product_sum_helper (l : list R):
      List.Forall (fun r => 0 <= r <= 1) l -> 1 - list_sum l <=
                                        list_product (List.map (fun x => 1 - x) l).
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

    Lemma prod_f_R0_succ (f : nat -> R) {k : nat} (hk : (0 < k)%nat):
      prod_f_R0 f k = f 0%nat * prod_f_R0 (fun n => f (S n)) (pred k).
    Proof.
      generalize (prod_SO_split f k 0 hk); intros.
      rewrite H. simpl.
      f_equal. f_equal.
      lia.
    Qed.

    Lemma prod_f_R0_pred (f : nat -> R) {k : nat} (hk : (0 < k)%nat):
      prod_f_R0 f k = prod_f_R0 f (pred k)*(f k).
    Proof.
      generalize (prod_SO_split f k (pred k)); intros.
      rewrite H; try lia.
      f_equal.
      replace (k - pred k - 1)%nat with 0%nat by lia.
      simpl. f_equal.  lia.
    Qed.

    Lemma list_product_prod_f_R0 (l : list R) :
      list_product l =
      prod_f_R0 (fun n => nth n l 1) (length l).
    Proof.
      induction l; try now simpl.
      simpl.
      destruct (lt_dec 0 (length l)).
      + rewrite prod_f_R0_succ; try assumption.
        rewrite IHl. rewrite Rmult_assoc.
        f_equal. rewrite prod_f_R0_pred; try assumption.
        reflexivity.
      + assert (length l = 0%nat) by lia.
        rewrite length_zero_iff_nil in H.
        rewrite H. now simpl.
    Qed.

    Lemma list_product_prod_f_R0_map (f : R -> R) (l : list R) :
      list_product (map f l) =
      prod_f_R0 (fun n => nth n (map f l) 1) (length l).
    Proof.
      rewrite list_product_prod_f_R0.
      now rewrite map_length.
    Qed.

    Lemma prod_f_R0_ne_zero {f : nat -> R} :
      (forall n, f n <> 0) -> (forall k, prod_f_R0 f k <> 0).
    Proof.
      intros Hf k.
      induction k; simpl; try auto.
    Qed.

    Lemma prod_f_R0_pos {f : nat -> R} :
      (forall n, 0 < f n) -> (forall k, 0 < prod_f_R0 f k).
    Proof.
      intros Hf k.
      induction k; simpl; try auto.
      apply Rmult_lt_0_compat; auto.
    Qed.

    Lemma prod_f_R0_nonneg {f : nat -> R} :
      (forall n, 0 <= f n) -> (forall k, 0 <= prod_f_R0 f k).
    Proof.
      intros Hf k.
      induction k; simpl; try auto.
      apply Rmult_le_pos; auto.
    Qed.

    Lemma prod_f_R0_inv {f : nat -> R} :
      (forall n, f n <> 0) ->
      forall k, prod_f_R0 (fun n => / (f n)) k = /(prod_f_R0 f k).
    Proof.
      intros Hf k.
      induction k; simpl; try lra.
      rewrite IHk.
      field_simplify; [reflexivity|
      (split; try apply prod_f_R0_ne_zero; try auto)|
      (split; try apply prod_f_R0_ne_zero; try auto)].
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
          rewrite sum_Sn in H0.
          apply Rle_lt_trans with (r2 := sum_n f N + f (S N)); trivial.
          replace (sum_n f N) with ((sum_n f N) + 0) at 1 by lra.
          apply Rplus_le_compat_l.
          apply H; lia.
        + assert (n = S N) by lia.
          rewrite H2.
          apply Rle_lt_trans with (r2 := sum_n f (S N)); trivial.
          rewrite sum_Sn.
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
        rewrite sum_Sn.
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
            apply Rge_trans with (r2 := 1 - x (S N) - sum_n x N); [ |unfold plus; simpl; lra].
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

    Lemma Rbar_mult_0_lt (a b : Rbar) :
      Rbar_lt 0 a ->
      Rbar_lt 0 b ->
      Rbar_lt 0 (Rbar_mult a b).
    Proof.
      intros.
      destruct a; destruct b; try now simpl in *.
      - simpl in *.
        now apply Rmult_lt_0_compat.
      - simpl in H.
        now rewrite Rbar_mult_comm, Rbar_mult_p_infty_pos.
      - simpl in H0.
        now rewrite Rbar_mult_p_infty_pos.
    Qed.


    Lemma ex_series_prod_Rbar_lt_0 (a : nat -> R) :
      (forall n, 0 <= a n < 1) ->
      ex_series a ->
      Rbar_lt 0 (Lim_seq (prod_f_R0 (fun n => 1 - a n))).
    Proof.
      intros.
      assert (forall n, 0 <= a n <= 1).
      {
        intros; specialize (H n); lra.
      }
      destruct (product_sum_assumption_b_helper a H1 H0) as [N ?].
      generalize (product_sum_helper_lim a N H1); intros.
      cut_to H3; trivial; [|now apply series_finite_sum_shift with (N := N) in H0].
      destruct N.
      - rewrite Lim_seq_ext with
            (v := (prod_f_R0 (fun n : nat => 1 - a n))) in H3; trivial.
        intros.
        apply prod_f_R0_proper; trivial.
        red; intros.
        now replace (a0 + 0)%nat with a0 by lia.
      - generalize (prod_SO_split (fun n => 1 - a n)); intros.
        rewrite <- Lim_seq_incr_n with (N := (S N)).
        rewrite Lim_seq_ext with
            (v := fun n =>
                    (prod_f_R0 (fun n0 => 1 - a n0) N) *
                    (prod_f_R0 (fun n0 => 1 - a (n0 + (S N))%nat) n)).
        + rewrite Lim_seq_scal_l.
          apply Rbar_mult_0_lt; trivial.
          apply prod_f_R0_pos.
          intros; specialize (H n); lra.
        + intros.
          rewrite prod_SO_split with (n := (n + S N)%nat) (k := N); try lia.
          f_equal.
          apply prod_f_R0_proper; try lia.
          red; intros.
          f_equal; f_equal; lia.
     Qed.

    Lemma prod_f_R0_one :
      forall n, prod_f_R0 (fun _ => 1) n = 1.
    Proof.
      induction n.
      - now simpl.
      - rewrite prod_f_R0_Sn, IHn.
        lra.
    Qed.


    Lemma finite_lim_prod (a : nat -> R) :
      (forall n, 0 <= a n <= 1) ->
      is_finite (Lim_seq (prod_f_R0 (fun n => 1 - a n))).
    Proof.
      intros.
      apply is_finite_Lim_bounded with (m := 0) (M := 1).
      intros.
      split.
      - apply prod_SO_pos.
        intros.
        specialize (H n0); lra.
      - generalize (prod_f_R0_one n); intros.
        rewrite <- H0.
        apply prod_SO_Rle.
        intros.
        rewrite H0.
        specialize (H n0); lra.
    Qed.

    Lemma ex_series_prod_lt_0 (a : nat -> R) :
      (forall n, 0 <= a n < 1) ->
      ex_series a ->
      0 < (Lim_seq (prod_f_R0 (fun n => 1 - a n))).
    Proof.
      intros.
      generalize (ex_series_prod_Rbar_lt_0 a H H0); intros.
      generalize (finite_lim_prod a); intros.
      cut_to H2.
      - rewrite <- H2 in H1.
        now simpl in H1.
      - intros.
        specialize (H n); lra.
    Qed.

    Lemma is_lim_seq_pos_inv_p_infty {α : nat -> R} (ha1 : forall n, 0 < α n):
      is_lim_seq α 0 <-> is_lim_seq (fun n => /α n) p_infty.
    Proof.
      rewrite is_lim_seq_p_infty_Reals.
      rewrite is_lim_seq_Reals.
      assert (forall n, α n <> 0) by (intros; specialize (ha1 n); lra).
      assert (forall n, /α n <> 0) by (intros; apply Rinv_neq_0_compat; eauto).
      split; intros.
      + revert H1.
        contrapose.
        unfold cv_infty, Un_cv.
        push_neg. intros.
        destruct H1 as [M HM].
        exists (/M); split.
        -- destruct (HM 0%nat) as [k [hk1 hk2]].
           apply Rlt_gt. apply Rge_le in hk2.
           apply Rinv_pos.
           eapply Rlt_le_trans with (r2 := /α k); auto.
           apply Rinv_pos; auto.
        -- intros n. specialize (HM n).
           destruct HM as [k [hk1 hk2]].
           exists k. split; try auto.
           unfold R_dist.
           rewrite Rminus_0_r.
           rewrite Rabs_pos_eq; [|left; try auto].
           apply Rle_ge. apply Rge_le in hk2.
           rewrite <-(Rinv_involutive (α k)); try auto.
           apply Rinv_le_contravar; auto.
           apply Rinv_pos; auto.
      + generalize (cv_infty_cv_R0 (fun n => /α n) H0); intros.
        specialize (H2 H1).
        intros eps Heps. specialize (H2 eps Heps).
        destruct H2 as [N HN]. exists N; intros.
        specialize (HN n H2).
        rewrite Rinv_involutive in HN; auto.
    Qed.

    (* Lemma 3 *)
    Theorem product_sum_iff {α : nat -> R} (gamma : R) (hg : 0 <= gamma < 1)
      (ha1 : forall n, 0 <= α n <= 1)
      (ha2 : is_lim_seq α 0) :
      is_lim_seq (sum_n α) p_infty <->
      (forall k, is_lim_seq (fun n => prod_f_R0 (fun m => g_alpha gamma (α (m + k)%nat)) n) 0).
    Proof.
      split; intros.
      - apply product_sum_assumption_a; try eauto.
      - apply product_sum_assumption_b with (gamma := gamma); try eauto.
    Qed.

    Theorem product_sum_gamma0 {α : nat -> R} {N0 : nat} (ha0 : forall n, 0 <= α n <= 1)
            (ha1 : forall n, (n >= N0)%nat -> 0 <= α n < 1)(ha2 : is_lim_seq α 0)
            (ha3 : is_lim_seq (sum_n α) p_infty) :
      (is_lim_seq (fun n => prod_f_R0 (fun m => /(1 - α (m + N0)%nat)) n) p_infty).
    Proof.
      rewrite product_sum_iff with (gamma := 0) in ha3; try lra; auto.
      - specialize (ha3 N0).
        unfold g_alpha in ha3.
        setoid_rewrite prod_f_R0_inv.
        -- apply is_lim_seq_ext with
               (v := fun n => prod_f_R0 (fun m => 1 - α (m + N0)%nat) n) in ha3.
        + unfold Rdiv.
          rewrite <-is_lim_seq_pos_inv_p_infty; auto.
          intros n. apply prod_f_R0_pos; intros.
          specialize (ha1 (n0+N0)%nat). cut_to ha1; try lra; try lia.
           + intros. apply prod_f_R0_proper; [|reflexivity].
             intros m; lra.
        -- intros; specialize (ha1 (n0+N0)%nat); cut_to ha1 ; try lra; try lia.
    Qed.

    Theorem product_sum_gamma0_0 {α : nat -> R} 
            (ha1 : forall n, 0 <= α n < 1) (ha2 : is_lim_seq α 0)
            (ha3 : is_lim_seq (sum_n α) p_infty) :
      (is_lim_seq (fun n => prod_f_R0 (fun m => /(1 - α m)) n) p_infty).
    Proof.
      rewrite product_sum_iff with (gamma := 0) in ha3; try lra; auto.
      - specialize (ha3 0%nat).
        unfold g_alpha in ha3.
        setoid_rewrite prod_f_R0_inv.
        + apply is_lim_seq_ext with
              (v := fun n => prod_f_R0 (fun m => 1 - α (m)%nat) n) in ha3.
          unfold Rdiv.
          rewrite <-is_lim_seq_pos_inv_p_infty; auto.
          intros n. apply prod_f_R0_pos; intros.
          specialize (ha1 (n0)%nat); lra.
          intros. apply prod_f_R0_proper; [|reflexivity].
          intros m.
          replace (m + 0)%nat with m by lia.
          lra.
        + intros; specialize (ha1 (n0)%nat).
          lra.
      - intros.
        specialize (ha1 n).
        lra.
    Qed.

    (* To be used for Lemma 9. *)
    Theorem product_sum_increasing0
        {α : nat -> R} (ha1 : forall n, 0 <= α n < 1)
      : let b := fun n => prod_f_R0 (fun m => / (1 - α (m)%nat)) n in
               forall p, 0 < b p <= b (S p).
    Proof.
      intros b p.
      subst b.
      simpl; split.
      + apply prod_f_R0_pos.
        intros n.
        apply Rinv_pos.
        specialize (ha1 (n)%nat); try lra.
      + rewrite <-Rmult_1_r at 1.
        apply Rmult_le_compat_l.
        -- apply prod_f_R0_nonneg.
           intros n.
           left. apply Rinv_pos.
           specialize (ha1 (n)%nat).
           lra.
        -- rewrite <-Rinv_1 at 1.
           apply Rinv_le_contravar; specialize (ha1 (S(p)%nat)); lra.
    Qed.

    Theorem product_sum_increasing
        {α : nat -> R} {N0 : nat} (ha1 : forall n, (N0 <= n)%nat -> 0 <= α n < 1)
      : let b := fun n => prod_f_R0 (fun m => / (1 - α (m + N0)%nat)) n in
               forall p, 0 < b p <= b (S p).
    Proof.
      intros b p.
      subst b.
      simpl; split.
      + apply prod_f_R0_pos.
        intros n.
        apply Rinv_pos.
        specialize (ha1 (n+N0)%nat). cut_to ha1; try lra; try lia.
      + rewrite <-Rmult_1_r at 1.
        apply Rmult_le_compat_l.
        -- apply prod_f_R0_nonneg.
           intros n.
           left. apply Rinv_pos.
           specialize (ha1 (n+N0)%nat). cut_to ha1; try lra; try lia.
        -- rewrite <-Rinv_1 at 1.
           apply Rinv_le_contravar.
           specialize (ha1 (S(p+N0)%nat)). cut_to ha1; try lra; try lia.
           specialize (ha1 (S (p+N0)%nat)). cut_to ha1; try lra; try lia.
    Qed.

    Fixpoint RMseq (α : nat -> R) (s : nat -> R) (init : R) (n : nat) : R :=
      match n with
      | 0 => init
      | (S k) => plus (scal (1 - α k) (RMseq α s init k)) (scal (α k) (s k))
      end.

    Global Instance RMseq_rv  {Ts:Type} {dom : SigmaAlgebra Ts} (α : nat -> R) (s : nat -> Ts -> R) (init : R) (n : nat) 
           {rx : forall n, RandomVariable dom borel_sa (s n)} :
     RandomVariable dom borel_sa (fun omega => RMseq α (fun n => s n omega) init n).
    Proof.
      induction n.
      - simpl.
        apply rvconst.
      - simpl.
        apply rvplus_rv.
        + now apply rvscale_rv.
        + typeclasses eauto.
    Qed.

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

    (* Lemma 7. stochastic *)

  Lemma bounding_7_alt {SS : Type} (hSS : Finite.Finite SS) (α : nat -> R) (gamma C : R) (f : nat -> X -> SS -> X) (init : X) :
      0 <= gamma < 1 -> 0 <= C ->
      (forall n, 0 <= (α n) <= 1) ->
      (forall n x, forall (s:SS), norm (f n x s) <= gamma * norm x + C) ->
      is_lim_seq α 0 ->
      (forall k, is_lim_seq (fun n => prod_f_R0 (fun m => g_alpha gamma (α (m+k)%nat)) n) 0) ->
      exists B, 
        forall (s_seq : nat -> SS), 
        forall n, norm ( RMseqX α (fun n x => f n x (s_seq n)) init n) <= B.
    Proof.
      intros.
      assert (forall (s_seq : nat -> SS), 
              forall (n:nat), 
                norm(RMseqX α (fun n x => f n x (s_seq n)) init (S n)) <= 
                (1 - α n)*norm(RMseqX α (fun n x => f n x (s_seq n)) init n) + 
                (α n)*(gamma * norm (RMseqX α (fun n x => f n x (s_seq n)) init n) + C)).
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

      assert (forall (s_seq : nat -> SS),
                 forall n,
                   norm(RMseqX α (fun n x => f n x (s_seq n)) init (S n)) <=
                   (g_alpha gamma  (α n)) * norm(RMseqX α (fun n x => f n x (s_seq n)) init n) + (α n)*C).
      {
        intros.
        eapply Rle_trans.
        apply H5.
        unfold g_alpha.
        lra.
     }

      assert (forall (s_seq : nat -> SS),
                 forall n, norm(RMseqX α (fun n x => f n x (s_seq n)) init n) <=
                           RMseqG α (norm init) gamma C n).
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
      NonnegativeFunction (fun v => inner (f v) (f v) ).
    Proof.
      unfold NonnegativeFunction.
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

    Lemma forall_FiniteRangeFunction_ext {rv1 rv2 : nat -> Ts -> R} 
          {frf1 : forall n, FiniteRangeFunction (rv1 n)} :
      (forall n, rv_eq (rv1 n) (rv2 n)) ->
      forall n, FiniteRangeFunction (rv2 n).
    Proof.
      intros.
      specialize (frf1 n).
      specialize (H n).
      generalize (FiniteRangeFunction_ext _ _ H frf1).
      trivial.
    Qed.

    Lemma forall_SimpleExpectation_ext {rv1 rv2 : nat -> Ts -> R}
          {rrv1 : forall n, RandomVariable dom borel_sa (rv1 n)}
          {frf1 : forall n, FiniteRangeFunction (rv1 n)}
          {rrv2 : forall n, RandomVariable dom borel_sa (rv2 n)}
          {frf2 : forall n, FiniteRangeFunction (rv2 n)} :
      (forall n, rv_eq (rv1 n) (rv2 n)) ->
      forall n, SimpleExpectation (rv1 n) = SimpleExpectation (rv2 n).
    Proof.
      intros.
      now apply SimpleExpectation_ext.
    Qed.

    Lemma isfinexp_finite_neg_part (rv_X : Ts -> R)
          {rv : RandomVariable dom borel_sa rv_X} :
      IsFiniteExpectation prts rv_X ->
      is_finite (NonnegExpectation (neg_fun_part rv_X)).
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
        {nnf : NonnegativeFunction rv_X} :
    is_finite (NonnegExpectation (neg_fun_part rv_X)).
  Proof.
    unfold neg_fun_part; simpl.
    unfold NonnegativeFunction in nnf.
    assert (rv_eq (fun x : Ts => Rmax (- rv_X x) 0) (const 0)).
    intro x.
    specialize (nnf x).
    unfold const.
    rewrite Rmax_right; lra.
    rewrite (NonnegExpectation_re H).
    assert (0 <= 0) by lra.
    generalize (NonnegExpectation_const 0 H0); intros.
    erewrite NonnegExpectation_pf_irrel.
    rewrite H1.
    reflexivity.
  Qed.

  Lemma Expectation_sum_first_finite_snd_pos 
        (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {nnf2 : NonnegativeFunction rv_X2} :
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
            (frfx : FiniteRangeFunction x) :
     RandomVariable dom (Rvector_borel_sa I) (F_alpha a x).
   Proof.
     eapply frf_singleton_rv; intros.
     apply (sa_preimage_singleton (σ:=Rvector_borel_sa I)).
     unfold F_alpha.
     typeclasses eauto.
  Qed.
   
   Lemma L2_convergent_helper (C : R) (w x : nat -> Ts -> vector R I) (xstar : vector R I) (n:nat)
         (rx : forall n, RandomVariable dom (Rvector_borel_sa I) (x n))
         (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n))
         (srw : forall n, FiniteRangeFunction  (w n)) 
         (srx : forall n, FiniteRangeFunction  (x n)) :
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
          (frf: FiniteRangeFunction f) :
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
          (frf: FiniteRangeFunction f) :
      0 <= SimpleExpectation (rvinner f f).
    Proof.
      apply SimpleExpectation_pos.
      intro v.
      now generalize (inner_ge_0 (f v)).
   Qed.

    Lemma SimpleExpectation_rvmaxabs_pos (f : Ts -> vector R I) 
          (rx : RandomVariable dom (Rvector_borel_sa I) f)
          (frf: FiniteRangeFunction f) :
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
         (srx : forall n, FiniteRangeFunction  (x n)) :
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
         (srx : forall n, FiniteRangeFunction  (x n)) :
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
         {frf : FiniteRangeFunction x}
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
          (frf : FiniteRangeFunction rv_X) : list dec_sa_event
    :=                                                   
      refine_dec_sa_partitions (vec_induced_sigma_generators frf) l.

  Lemma update_partition_list
          (l : list dec_sa_event)
          {rv_X : Ts -> vector R I}
          {rv:RandomVariable dom (Rvector_borel_sa I) rv_X}
          (frf : FiniteRangeFunction rv_X) :
    is_partition_list (map dsa_event l) ->
    is_partition_list (map dsa_event (update_sa_dec_history l frf)).
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
          (frf : FiniteRangeFunction rv_X) :
    partition_measurable (cod:=Rvector_borel_sa I) rv_X (map dsa_event (update_sa_dec_history l frf)).
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
    destruct frf.
    unfold vec_induced_sigma_generators in H3.
    rewrite in_map_iff in H3.
    destruct H3 as [? [? ?]].
    unfold RandomVariable.frf_vals in *.
    exists x2.
    rewrite nodup_In in H4.
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
         (srw : forall n, FiniteRangeFunction  (w n)) 
         (srx : forall n, FiniteRangeFunction  (x n)) :
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
      (forall n, rv_eq (vector_SimpleConditionalExpectationSA (w n) (hist n)) (const zero)) ->
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
        generalize (simple_expectation_rvinner_measurable_zero
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
    
    Global Instance L2_convergent_x_frf (xinit:Ts->vector R I) (w: nat -> Ts -> vector R I) (n:nat)
          (srx : FiniteRangeFunction xinit)
          (srw : forall n, FiniteRangeFunction (w n)) :
      FiniteRangeFunction (L2_convergent_x xinit w n).
    Proof.
      induction n.
      - now simpl.
      - typeclasses eauto.
    Qed.

    Global Instance L2_convergent_x_rv (xinit:Ts->vector R I) (w: nat -> Ts -> vector R I) (n:nat)
          (rx : RandomVariable dom (Rvector_borel_sa I) xinit)
          (srx : FiniteRangeFunction xinit)
          (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n)) 
          (srw : forall n, FiniteRangeFunction (w n)) :
      RandomVariable dom (Rvector_borel_sa I) (L2_convergent_x xinit w n). 
    Proof.
      induction n.
      - now simpl.
      - generalize (L2_convergent_x_frf xinit w n srx srw); intros.
        typeclasses eauto.
    Qed.

    Section hist.
      Context (x:nat->Ts->vector R I).
      Context (rvx:forall n, RandomVariable dom (Rvector_borel_sa I) (x n)).
      Context (frfx: forall n, FiniteRangeFunction (x n)).
      
      Fixpoint L2_convergent_hist (n:nat) : list dec_sa_event
        := match n with
           | 0 => 
             @vec_induced_sigma_generators Ts dom I
                                   (x 0%nat)
                                   (rvx 0%nat)
                                   (frfx 0%nat)
           | S k =>
             @update_sa_dec_history (L2_convergent_hist k)
                                   (x (S k))
                                   (rvx (S k))
                                   (frfx (S k))
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
          (frfxinit : FiniteRangeFunction xinit)
          (srw : forall n, FiniteRangeFunction  (w n)) :
      0 <= C ->
      0 <= gamma < 1 ->
      (forall n, 0 <= α n <= 1) -> 
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      (forall n, rv_eq (vector_SimpleConditionalExpectationSA 
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

    (* Move this. *)
    Lemma vector_nth_between_rvmaxabs {N} (X : Ts -> vector R N)
      {rv : RandomVariable dom (Rvector_borel_sa N) X}:
      forall k pf omega, -rvmaxabs X omega <= vector_nth k pf (X omega) <= rvmaxabs X omega.
    Proof.
      intros.
      generalize (Rvector_max_abs_nth_le (X omega) k pf); intros.
      split; intros.
      - unfold rvmaxabs.
        split_Rabs; lra.
      - unfold rvmaxabs.
        split_Rabs; lra.
    Qed.

  Lemma filter_finite_imp {A B} {fin:Finite.Finite B} {FF} {filterF:Filter FF} (P:B->A->Prop) : 
    (forall b, FF (P b)) -> FF (fun x => (forall b, P b x)).
  Proof.
    intros HH.
    destruct fin.
    cut (FF (fun x : A => forall b : B, In b elms -> P b x)).
    {
      apply filter_imp; intros; auto.
    }
    clear finite.
    induction elms.
    - eapply filter_imp; try eapply filter_true.
      simpl; intros; tauto.
    - eapply filter_imp; [| apply filter_and; [apply (HH a) | apply IHelms]].
      simpl; intros.
      destruct H0; subst; firstorder.
  Qed.

  Lemma vector_index_filter_imp {A} {FF} {n} {filterF:Filter FF} (P:forall k, (k < n)%nat->A->Prop):
    (forall k (pf: (k < n)%nat), FF (P k pf)) ->
    FF (fun x => (forall k pf, P k pf x)).
  Proof.
    intros.
    cut (FF (fun x => (forall (i:{k | (k < n)%nat}), P (proj1_sig i) (proj2_sig i) x))).
    {
      apply filter_imp; intros.
      apply (H0 (exist _ k pf)).
    }
    now apply filter_finite_imp; intros [??]; simpl.
  Qed.

    Lemma is_lim_seq_rvmaxabs_zero_iff {N} (X : nat -> Ts -> vector R N)
          {rv : forall n, RandomVariable dom (Rvector_borel_sa N) (X n)} :
      forall omega, is_lim_seq (fun n => rvmaxabs (X n) omega) 0 <->
      (forall k pf, is_lim_seq (fun n => vector_nth k pf (X n omega)) 0).
    Proof.
      intros omega.
      split.
      ++ intros Hnth k pf.
         assert (is_lim_seq (fun n => - rvmaxabs (X n) omega) 0).
         {
           rewrite is_lim_seq_opp.
           simpl. setoid_rewrite Ropp_involutive.
           now rewrite Ropp_0.
         }
         apply is_lim_seq_le_le with (w := fun n => rvmaxabs (X n) omega)
                                     (u := fun n => -rvmaxabs (X n) omega); try assumption.
         intros n.
         apply vector_nth_between_rvmaxabs; eauto.
      ++ intros.
         unfold is_lim_seq in *.
         apply is_lim_seq_spec; intros eps.
         assert (forall k pf, eventually (fun n => Rabs (vector_nth k pf (X n omega) - 0) < eps)).
         {
           intros.
           specialize (H k pf).
           apply is_lim_seq_spec in H.
           apply H.
         } 
         apply vector_index_filter_imp in H0.
         revert H0.
         apply filter_imp; intros.
         unfold rvmaxabs.
         destruct N.
      * rewrite (vector0_0 (X x omega)).
        unfold Rvector_max_abs.
        simpl.
        vm_compute.
        repeat match_destr; lra.
      * destruct (Rvector_max_abs_nth_in (X x omega)) as [?[? eqq1]].
        rewrite eqq1.
        specialize (H0 _ x1).
        rewrite Rminus_0_r in H0.
        rewrite Rminus_0_r.
        now rewrite Rabs_Rabsolu.
    Qed.


    (* Move this. *)
    Lemma Rvector_nth_sum_telescope {f vec : nat -> vector R I}
          (Hf : forall n, f (S n) = Rvector_plus (f n) (vec n)) :
      forall n i pf, vector_nth i pf (Rvector_minus (f (S n)) (f 0%nat))
                = sum_f_R0 (fun k => vector_nth i pf (vec k)) n.
    Proof.
      intros n i pf.
      induction n.
      + simpl. rewrite Hf. rewrite Rvector_nth_minus.
        rewrite Rvector_nth_plus. ring.
      + simpl. rewrite Rvector_nth_minus.
        rewrite <-IHn. rewrite Hf.
        rewrite Rvector_nth_plus.
        rewrite Rvector_nth_minus.
        ring.
    Qed.

    Lemma F0_xrel (w : nat -> Ts -> vector R I) :
      F = const (Rvector_zero) ->
      forall n, 
        rv_eq (L2_convergent_x (const Rvector_zero) w (S n))
              (vecrvplus
                 (vecrvscale (1 - α n) (L2_convergent_x (const Rvector_zero) w n))
                 (vecrvscale (α n) (w n))).
      Proof.
        intros n ??.
        simpl.
        unfold F_alpha.
        rewrite n.
        unfold vecrvplus, vecrvscale, const.
        rewrite Rvector_scale_zero.
        now rewrite Rvector_plus_zero.
      Qed.

  Lemma history_pair_minus_scale_vec (x : nat -> Ts -> vector R I) (c : nat -> R) :
    rv_eq (x 0%nat) (const Rvector_zero) ->
    forall n,
      sa_equiv (filtration_history_sa (cod := Rvector_borel_sa I) (fun n => (x (S n))) n) 
               (filtration_history_sa (cod := Rvector_borel_sa I)
                                      (fun n => vecrvminus (x (S n)) (vecrvscale (c n) (x n))) n).
 Proof.
   intros.
   induction n.
   - simpl.
     rewrite H.
     unfold vecrvminus, vecrvplus, vecrvopp, const, vecrvscale.
     do 2 setoid_rewrite Rvector_scale_zero.
     now setoid_rewrite Rvector_plus_zero.
   - simpl.
     rewrite <- IHn.
     apply sa_equiv_subs.
     split.
     + apply union_sa_sub_both.
       * assert (rv_eq (x (S (S n))) 
                       (vecrvplus (vecrvminus (x (S (S n))) (vecrvscale (c (S n)) (x (S n))))
                                  (vecrvscale (c (S n)) (x (S n))))).
        {
          intros ?.
          unfold vecrvminus, vecrvplus, vecrvopp, const, vecrvscale.          
          rewrite Rvector_scale_scale.
          rewrite <- Rvector_plus_assoc.
          rewrite <- Rvector_scale_plus_r.
          replace  (-1 * c (S n) + c (S n)) with (0) by lra.
          rewrite Rvector_scale0.
          now rewrite Rvector_plus_zero.
        }
        rewrite H0 at 1.
        rewrite union_sa_comm.
        apply pullback_rv_sub.
        apply Rvector_plus_rv.
         -- generalize (pullback_rv (Rvector_borel_sa I) (vecrvminus (x (S (S n))) (vecrvscale (c (S n)) (x (S n))))).
            apply RandomVariable_proper_le; try reflexivity.
            apply union_sa_sub_r.

         -- apply Rvector_scale_rv.
            generalize (filtration_history_sa_rv (cod := Rvector_borel_sa I) 
                                                 (fun n => x (S n)) n).
            apply RandomVariable_proper_le; try reflexivity.           
            apply union_sa_sub_l.
       * apply union_sa_sub_r.
     + apply union_sa_sub_both.
       * apply pullback_rv_sub.
         apply Rvector_minus_rv.
         -- generalize (pullback_rv (Rvector_borel_sa I) (x (S (S n)))).
            apply RandomVariable_sa_sub.
            apply union_sa_sub_l.
         -- apply Rvector_scale_rv.
            generalize (filtration_history_sa_rv (cod := Rvector_borel_sa I)
                                                 (fun n => x (S n)) n).
            apply RandomVariable_sa_sub.
            apply union_sa_sub_r.
       * apply union_sa_sub_r.
 Qed.

 Lemma history_scale (x : nat -> Ts -> vector R I) (c : nat -> R) :
   (forall n, c n <> 0) ->
    forall n,
      sa_equiv (filtration_history_sa (cod := Rvector_borel_sa I) x n) 
               (filtration_history_sa (cod := Rvector_borel_sa I)
                                      (fun n => (vecrvscale (c n) (x n))) n).
 Proof.
   intros.
   apply filtrate_sa_proper.
   intros ??.
   now apply pullback_sa_vecrvscale_equiv.
 Qed.


 Lemma iso_hist_x_z_b (x z : nat -> Ts -> vector R I) (b : nat -> R) :
   rv_eq (x 0%nat) (const Rvector_zero) ->
   rv_eq (x 0%nat) (z 0%nat) ->
   (forall n, b n <> 0) ->
   (forall n,
       rv_eq (x (S n)) 
             (vecrvplus 
                (vecrvscale (1 - α n) (x n))
                (vecrvscale (/ (b (S n))) (z (S n))))) ->
   forall n, 
     sa_equiv (filtration_history_sa (cod := Rvector_borel_sa I) (fun n => x (S n)) n)
              (filtration_history_sa (cod := Rvector_borel_sa I) (fun n => z (S n)) n).
 Proof.
   intros.
   generalize ( history_pair_minus_scale_vec x (fun n => (1 - α n)) H); intros.
   generalize ( history_scale (fun n => z (S n)) (fun n => (/ (b (S n))))); intros.
   intros.
   rewrite H3.
   rewrite H4.
   assert (forall n0,
              rv_eq  (vecrvminus (x (S n0)) (vecrvscale (1 - α n0) (x n0)))
                     (vecrvscale (/ (b (S n0))) (z (S n0)))).
   {
     intros n0.
     rewrite H2.
     intros zz.
     unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale.
     rewrite Rvector_scale_scale.
     rewrite (Rvector_plus_comm (Rvector_scale (1 - α n0) (x n0 zz)) _).
     rewrite <- Rvector_plus_assoc.
     rewrite <- Rvector_scale_plus_r.
     replace  (1 - α n0 + -1 * (1 - α n0)) with (0) by lra.
     now rewrite Rvector_scale0, Rvector_plus_zero.
   }
   apply filtrate_sa_proper.
   intros ??.
   apply pullback_sa_sigma_proper; try easy.
   now rewrite H5.
   intros.
   now apply Rinv_neq_0_compat.
 Qed.         
  
  Lemma filtrate_sa_shift1 {Td} (f : nat -> SigmaAlgebra Td) n :
    sa_equiv (filtrate_sa f (S n))
             (union_sa (f 0%nat) (filtrate_sa (fun k => f (S k)) n)).
  Proof.
    induction n; simpl.
    - apply union_sa_comm.
    - rewrite IHn.
      rewrite union_sa_assoc.
      rewrite (union_sa_comm (f (S (S n)))).
      rewrite <- union_sa_assoc.
      reflexivity.
  Qed.
    
  Lemma shift_filtrate_sa {Td} (f g : nat -> SigmaAlgebra Td) :
    sa_equiv (f 0%nat) (g 0%nat) ->
    (forall n, sa_equiv (filtrate_sa (fun k => f (S k)) n)
                   (filtrate_sa (fun k => g (S k)) n)) ->
    forall n, sa_equiv (filtrate_sa f n)
                  (filtrate_sa g n).
  Proof.
    intros eqq0 eqqn.
    destruct n.
    - now simpl.
    - repeat  rewrite filtrate_sa_shift1.
      now apply union_sa_proper.
  Qed.

 Lemma shift_history_equiv {Td} (cod:SigmaAlgebra Td) (f g : nat -> Ts -> Td) :
   sa_equiv
     (pullback_sa cod (f 0%nat))
     (pullback_sa cod (g 0%nat))  ->
   (forall (n:nat),
       sa_equiv
         (filtration_history_sa (cod := cod) (fun n0 => f (S n0)) n)
         (filtration_history_sa (cod := cod) (fun n0 => g (S n0)) n)) ->
   forall (n:nat),
     sa_equiv (filtration_history_sa (cod := cod) f n)
              (filtration_history_sa (cod := cod) g n).
  Proof.
    intros eqqs0 eqqsn n.
    now apply shift_filtrate_sa.
  Qed.


    Lemma condexp_hist_z (w z: nat -> Ts -> vector R I) (b : nat -> R)
          (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n)) 
          (rx : forall n, RandomVariable dom (Rvector_borel_sa I)
                                         (L2_convergent_x (const Rvector_zero) w n))
          (rz : forall n, RandomVariable dom (Rvector_borel_sa I) (z n))                    
          {isfew:forall n, vector_IsFiniteExpectation prts (w n)}
          {isfez:forall n, vector_IsFiniteExpectation prts (z n)} :
     (forall n, rv_eq (vector_FiniteConditionalExpectation
                         prts (filtration_history_sa_sub (cod := Rvector_borel_sa I) 
                                                         (L2_convergent_x (const Rvector_zero) w)
                                                         n) (w n))
                      (const Rvector_zero)) ->
     (forall n, b n <> 0) ->
     rv_eq (z 0%nat) (const Rvector_zero) ->
     (forall n,
         rv_eq (L2_convergent_x (const Rvector_zero) w (S n)) 
               (vecrvplus 
                  (vecrvscale (1 - α n) (L2_convergent_x (const Rvector_zero) w n))
                  (vecrvscale (/ (b (S n))) (z (S n))))) ->
     (forall n,
         rv_eq (z (S n)) (vecrvscale ((b (S n)) * α n) (w n))) ->
     forall n,
       almostR2 prts eq
          (vector_FiniteConditionalExpectation
             prts (filtration_history_sa_sub (cod := Rvector_borel_sa I) z n)  (z (S n)))
          (const Rvector_zero).
    Proof.
      intros.
      generalize (iso_hist_x_z_b  (L2_convergent_x (const Rvector_zero) w) z b); intros.
      cut_to H4.
      - assert (forall n : nat,
                   sa_equiv
                     (filtration_history_sa (cod := Rvector_borel_sa I) (L2_convergent_x (const Rvector_zero) w) n)
                     (filtration_history_sa (cod := Rvector_borel_sa I) z n)).
        {
          intros.
          destruct n0.
          - simpl.
            rewrite H1.
            reflexivity.
          - apply shift_history_equiv.
            + now apply pullback_sa_proper.
            + apply H4.
        }
        assert (
          almostR2 
            prts eq
            (vector_FiniteConditionalExpectation 
               prts (filtration_history_sa_sub (cod := Rvector_borel_sa I) z n) (z (S n)))
            (vector_FiniteConditionalExpectation 
               prts (filtration_history_sa_sub (cod := Rvector_borel_sa I) 
                                               (L2_convergent_x (const Rvector_zero) w) n)
               (vecrvscale (b (S n) * α n) (w n)))).
        {
          symmetry in H5.
          generalize (vector_FiniteCondexp_all_proper 
                        prts 
                    (filtration_history_sa_sub (cod := Rvector_borel_sa I) z n)    
                    (filtration_history_sa_sub (cod := Rvector_borel_sa I) 
                                               (L2_convergent_x (const Rvector_zero) w) n)
                    (H5 n)
                    (z (S n))
                    (vecrvscale (b (S n) * α n) (w n))); intros.
          apply almost_prob_space_sa_sub_lift in H6.          
          apply H6.
          apply all_almost.
          intros.
          apply H3.
        }
        generalize (vector_FiniteCondexp_scale 
                      prts 
                      (filtration_history_sa_sub (cod := Rvector_borel_sa I)
                                                 (L2_convergent_x (const Rvector_zero) w) n) 
                      (b (S n) * α n) (w n)); intros.
        apply almost_prob_space_sa_sub_lift in H7.
        revert H6; apply almost_impl.
        revert H7; apply almost_impl.
        apply all_almost.
        intros ???.
        rewrite H7.
        rewrite H6.
        unfold vecrvscale.
        rewrite H.
        unfold const.
        now rewrite Rvector_scale_zero.
      - simpl.
        reflexivity.
      - simpl.
        now rewrite H1.
      - trivial.
      - apply H2.
    Qed.

    (* Lemma 9*)
    Lemma as_convergent_lemma (C : R) (w : nat -> Ts -> vector R I)
          (rw : forall n, RandomVariable dom (Rvector_borel_sa I) (w n))
          (isfew : forall n, vector_IsFiniteExpectation prts (w n))
          (srw : forall n, FiniteRangeFunction  (w n)) :
      0 <= C ->
      F = const (Rvector_zero) ->

      (forall n, 0 <= α n < 1) ->
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      ex_series (fun n => (α n)^2) -> 
     (forall n, rv_eq (vector_FiniteConditionalExpectation
                         prts (filtration_history_sa_sub (cod := Rvector_borel_sa I) 
                                                         (L2_convergent_x (const Rvector_zero) w)
                                                         n) (w n))
                      (const Rvector_zero)) ->
      (forall n, SimpleExpectation (rvinner (w n) (w n)) < C)  ->
      almost prts (fun w1 =>
                     is_lim_seq (fun n => (rvmaxabs (L2_convergent_x (const Rvector_zero) w n)) w1) 0).
    Proof.
      intros Hc HF Ha1 Ha2 Ha3 Ha4 HCE HE.
      assert (isfe_mult : forall j k : nat,
              vector_IsFiniteExpectation prts (vecrvmult (w j) (w k))).
      {
        intros.
        apply vector_IsFiniteExpectation_simple.
        - typeclasses eauto.
        - now apply frf_vecrvmult.
      }
      setoid_rewrite is_lim_seq_rvmaxabs_zero_iff.
      pose (N0 := 0%nat).
      assert (Hp1 : let b := fun m => /(prod_f_R0 (fun k => 1 - α (k + N0)) (pred (m))) in
                    let y := (fun n => vecrvscale (b n) (fun omega => L2_convergent_x (const Rvector_zero) w (n + N0)%nat omega)) in
            forall n w0, (0 < n)%nat -> (y (S n) w0) = Rvector_plus (y n w0) (vecrvscale ((b (S n)%nat) * α (n + N0)%nat) (w (n + N0)%nat) w0)).
      {
        intros b y n Hn w0. unfold y.
        simpl. unfold vecrvscale, vecrvplus.
        rewrite Rvector_scale_plus_l.
        rewrite Rvector_scale_scale. f_equal.
        unfold b, F_alpha, vecrvscale,vecrvplus.
        rewrite Rvector_scale_plus_l.
        do 2 rewrite Rvector_scale_scale.
        rewrite HF. unfold const. rewrite Rvector_scale_zero.
        rewrite Rvector_plus_zero.
        f_equal. simpl.
        rewrite prod_f_R0_pred. assert (n+N0 >= N0)%nat by lia.
        rewrite Rinv_mult_distr.
        + rewrite Rmult_assoc. rewrite Rinv_l; try lra.
          unfold N0; replace (n + 0)%nat with (n) by lia.
          specialize (Ha1 n); lra.
        + apply prod_f_R0_ne_zero.
          intros. specialize (Ha1 (n0 + N0)%nat). lra.
        + specialize (Ha1 (n + N0)%nat); lra.
        + assumption.
      }
      assert (H60_2 : ex_series (fun n => SimpleExpectation (rvinner (vecrvscale (α (n + N0)%nat) (w (n + N0)%nat))
                                                                     (vecrvscale (α (n + N0)%nat) (w (n + N0)%nat))))).
      {
        apply ex_series_ext with 
            (a :=  (fun n =>  (α (n + N0)%nat)^2* SimpleExpectation (rvinner (w (n + N0)%nat)
                                                                             (w (n + N0)%nat)))).
        - intros.
          rewrite scaleSimpleExpectation.
          apply SimpleExpectation_ext.
          intros ?.
          unfold rvscale, rvinner, vecrvscale.
          symmetry.
          rewrite Rvector_inner_scal.
          rewrite Rvector_inner_comm.
          rewrite Rvector_inner_scal.
          ring.
        - generalize (ex_series_le
                        (fun n : nat =>
                           α (n + N0) ^ 2 * SimpleExpectation (rvinner (w (n + N0)%nat) (w (n + N0)%nat)))
                        (fun n => (α (n + N0)%nat)^2 * C)); intros.
          apply H.
          + intros.
            unfold norm; simpl; unfold abs; simpl.
            rewrite Rmult_1_r.
            replace (α (n + N0) * α (n + N0)) with ((α (n + N0))^2) by ring.
            rewrite Rabs_right.
            * apply Rmult_le_compat_l.
              -- apply pow2_ge_0.
              -- left; apply HE.
            * apply Rle_ge, Rmult_le_pos.
              -- apply pow2_ge_0.
              -- apply SimpleExpectation_pos.
                 intros.
                 apply rv_inner_ge_0.
          + apply ex_series_scal_r.
            rewrite ex_series_incr_n in Ha4.
            setoid_rewrite Nat.add_comm.
            apply Ha4.
      }
      pose (b := fun (m:nat) => 
                   match m with
                   | 0 => 1
                   | S n => (prod_f_R0 (fun k => /(1 - α (k))) n)
                   end).
      pose (z := fun (m:nat) =>
                   match m with
                   | 0 => (const Rvector_zero) 
                   | S n => vecrvscale ((b m)*(α n)) (w n)
                   end).
      assert (rv : forall n : nat, RandomVariable dom (Rvector_borel_sa I) (z n)).
      {
        destruct n.
        - simpl; typeclasses eauto.
        - simpl; typeclasses eauto.
      }
      assert (rx : forall n : nat,
                 RandomVariable dom (Rvector_borel_sa I) 
                                (L2_convergent_x (const Rvector_zero) w n)) by typeclasses eauto.
      assert (frf : forall n : nat, FiniteRangeFunction (z n)).
      {
        destruct n.
        - simpl; typeclasses eauto.
        - simpl; typeclasses eauto.
      }
      assert (isfez : forall n : nat, vector_IsFiniteExpectation prts (z n)).
      {
        
        destruct n.
        - simpl; typeclasses eauto.
        - simpl.
          apply vector_IsFiniteExpectation_simple; typeclasses eauto.
      }
      assert (bneq0: forall n, b n <> 0).
      {
        intros.
        destruct n.
        - simpl; lra.
        - simpl.
          apply Rgt_not_eq.
          apply product_sum_increasing0.
          intros; apply Ha1.
      }
      assert (isfe_mult2 : forall j k : nat,
                      vector_IsFiniteExpectation prts (vecrvmult (z j) (z k))).
      {
        intros.
        apply vector_IsFiniteExpectation_simple.
        - typeclasses eauto.
        - now apply frf_vecrvmult.
      }
      generalize (vec_Ash_6_2_2 z b); intros Kol.      
      cut_to Kol; trivial.
      - revert Kol;apply almost_impl; apply all_almost; intros ??.
        intros; specialize (H k pf).
        eapply is_lim_seq_ext; try eapply H.
        intros.
        simpl.
        unfold rvscale, rvplus, vecrvnth, rvsum.
        unfold vecrvplus.
        apply Rmult_eq_reg_l with (r := b n); trivial.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_r; trivial.
        unfold const.
        simpl.
        unfold z.
        induction n.
        + rewrite sum_O.
          simpl.
          unfold F_alpha.
          unfold vecrvplus, vecrvscale.
          unfold const.
          lra.
        + unfold F_alpha.
          rewrite sum_Sn.
          rewrite IHn.
          unfold plus; simpl.
          unfold F_alpha, vecrvplus, vecrvscale.
          rewrite HF.
          unfold const.
          rewrite Rvector_scale_zero.
          do 2 rewrite Rvector_nth_plus.
          do 3 rewrite Rvector_nth_scale.          
          rewrite Rvector_nth_zero.
          rewrite Rplus_0_r.
          rewrite Rmult_plus_distr_l.
          f_equal; try lra.
          rewrite <- Rmult_assoc.
          f_equal.
          destruct n.
          * simpl.
            rewrite <- Rinv_l_sym; trivial.
            specialize (Ha1 0%nat); lra.
          * simpl.
            rewrite Rmult_assoc.
            rewrite <- Rinv_l_sym; try lra.
            specialize (Ha1 (S n)); lra.
      - generalize (condexp_hist_z w z b rw _ _ HCE); intros.
        apply H; trivial.
        + now simpl.
        + intros.
          simpl.
          unfold F_alpha.
          rewrite HF.
          unfold vecrvplus, vecrvscale, const.
          intros ?; simpl.
          rewrite Rvector_scale_zero.
          rewrite Rvector_plus_zero.
          f_equal.
          rewrite Rvector_scale_scale.
          f_equal.
          field.
          specialize (bneq0 (S n0)).
          unfold b in bneq0; now simpl in bneq0.
        + intros.
          unfold z; now simpl.
      - intros.
        destruct n.
        + simpl.
          split; try lra.
          replace (1) with (/ 1) at 1 by lra.
          specialize (Ha1 0%nat).
          apply Rinv_le_contravar; lra.
        + simpl.
          now apply product_sum_increasing0.
      - apply is_lim_seq_incr_1.
        unfold b. simpl.
        now apply product_sum_gamma0_0.
      - apply ex_series_incr_1.
        revert H60_2.
        apply ex_series_ext.
        intros.
        erewrite FiniteExpectation_simple.
        apply SimpleExpectation_ext.
        intros ?.
        unfold z, rvinner, rvscale, vecrvscale.
        rewrite Rvector_scale_scale.
        rewrite <- Rmult_assoc.
        rewrite <- Rinv_l_sym; trivial.
        rewrite Rmult_1_l.
        unfold N0.
        now replace (n + 0)%nat with (n) by lia.
      - typeclasses eauto.
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

    Lemma ps_inter_bound (A B : event dom) (prts : ProbSpace dom) :
      ps_P (event_inter A B) >= ps_P A + ps_P B - 1.
    Proof.
      generalize (ps_union prts A B); intros.
      assert (ps_P (event_union A B) <= 1) by apply ps_le1.
      lra.
    Qed.

    Lemma Induction_I2_18 (α : nat -> R) (xtilde : nat -> Ts -> R) (w : nat -> Ts -> R) (C:R) :
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

    Lemma Induction_I2_18_alt (α : nat -> R) (xtilde : nat -> Ts -> R) (w : nat -> Ts -> R) (C:R) :
      (forall n, 0 <= α n <= 1) -> 
      (forall n, forall omega, Rabs (xtilde n omega) <= C) ->
      (forall n, forall omega, 
            (- α n)*gamma*C <= (xtilde (S n) omega) -  (1 - α n)*(xtilde n omega) -  (α n)*(w n omega) <= (α n)*gamma*C) ->
      forall n, forall omega, 
          - (RMseq α (fun n => gamma * C) C n) <= (xtilde n omega) - (RMseq α (fun n0 => w n0 omega) 0 n) 
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

    Lemma Induction_I2_18_Rabs (α : nat -> R) (xtilde : nat -> Ts -> R) (w : nat -> Ts -> R) (C:R) :
      (forall n, 0 <= α n <= 1) -> 
      (forall n, forall omega, Rabs (xtilde n omega) <= C) ->
      (forall n, forall omega, 
            (- α n)*gamma*C <= (xtilde (S n) omega) -  (1 - α n)*(xtilde n omega) -  (α n)*(w n omega) <= (α n)*gamma*C) ->
      forall n, forall omega, 
          Rabs ((xtilde n omega) - (RMseq α (fun n0 => w n0 omega) 0 n)) 
          <= RMseq α (fun n => gamma * C) C n.
     Proof.
       intros.
       rewrite Rabs_le_between.
       now apply Induction_I2_18_alt.
     Qed.

   Lemma Induction_I2_full  (α : nat -> R) (x : nat -> Ts -> R) (w : nat -> Ts -> R) (C:R) (xstar : R) (F : R -> R) :
      (forall n, 0 <= α n <= 1) -> 
      0 <= gamma < 1 ->
      (forall (x y : R), Rabs (F x  - F y) <= gamma * (Rabs (x - y))) ->
      let xtilde := fun n => fun omega => x n omega - xstar in
      (forall n, forall omega, Rabs (xtilde n omega) <= C) ->
      (forall n, forall omega, xtilde (S n) omega = (1 - α n) * (xtilde n omega) +  
                                                    (α n)*((F (x n omega)) - (F xstar) + (w n omega))) ->
      forall n, forall omega, 
          Rabs ((xtilde n omega) - (RMseq α (fun n0 => w n0 omega) 0 n)) <=
          RMseq α (fun n => gamma * C) C n.
    Proof.
      intros.
      apply Induction_I2_18_Rabs; trivial.
      intros.
      specialize (H3 n0 omega0).
      rewrite H3.
      unfold xtilde.
      replace ( (1 - α n0) * (x n0 omega0 - xstar) + 
                α n0 * (F (x n0 omega0) - F xstar + w n0 omega0) -
                (1 - α n0) * (x n0 omega0 - xstar) - α n0 * w n0 omega0) with
          (α n0 * (F (x n0 omega0) - F xstar)) by lra.
      replace (- α n0 * gamma * C) with (- ( α n0 * gamma * C)) by lra.
      rewrite <- Rabs_le_between.
      rewrite Rabs_mult.
      rewrite Rabs_right.
      - rewrite Rmult_assoc.
        apply Rmult_le_compat_l; try apply H.
        eapply Rle_trans.
        apply H1.
        apply Rmult_le_compat_l; try apply H0.
        unfold xtilde in H2.
        apply H2.
      - apply Rle_ge.
        apply H.
   Qed.      
      
   Lemma Induction_I2_full_vec {k:nat} (α : nat -> R) (x : nat -> Ts -> vector R k) (w : nat -> Ts -> vector R k) (C:R) (xstar : vector R k) (F : vector R k -> vector R k) :
      (forall n, 0 <= α n <= 1) -> 
      0 <= gamma < 1 ->
      (forall (x y : vector R k),
          Rvector_max_abs (Rvector_minus (F x) (F y)) <= 
          gamma * Rvector_max_abs (Rvector_minus x y)) ->
      (forall n,
          (rv_eq (x (S n))
                 (vecrvplus
                    (vecrvscale (1 - α n) (x n)) 
                    (vecrvscale (α n)
                                (vecrvplus (fun v => F (x n v)) (w n)))))) ->
      (forall n, forall omega, 
            rvmaxabs (vecrvminus (x n) (const xstar)) omega <= C) ->
      F xstar = xstar ->
      let xtilde := fun n => fun omega => Rvector_minus (x n omega) xstar in
      forall n, forall omega, 
          forall i,
            forall (pf : (i < k)%nat),
              Rabs (vector_nth i pf (xtilde n omega) - 
                    (RMseq α (fun n0 => (vector_nth i pf (w n0 omega))) 0 n)) <=
              RMseq α (fun n => gamma * C) C n.
     Proof.
       intros.
       generalize (Induction_I2_18_Rabs α (fun n omega => vector_nth i pf (xtilde n omega))
                                        (fun n omega => vector_nth i pf (w n omega)) C H); intros.
       assert  (forall (n0 : nat) (omega0 : Ts), Rabs (vector_nth i pf (xtilde n0 omega0)) <= C).
       {
         intros.
         specialize (H3 n0 omega0).
         generalize (Rvector_max_abs_nth_le (xtilde n0 omega0) i pf); intros.        
         eapply Rle_trans.
         apply H6.
         unfold rvmaxabs in H3.
         eapply Rle_trans.
         apply H3.
         lra.
       }
       apply H5; trivial.
       intros.
       specialize (H2 n0 omega0).
       unfold xtilde.
       rewrite H2.
       replace  (vector_nth i pf
                            (Rvector_minus
                               (vecrvplus (vecrvscale (1 - α n0) (x n0))
                                          (vecrvscale (α n0) 
                                                      (vecrvplus 
                                                         (fun v : Ts => F (x n0 v))
                                                         (w n0))) 
                                          omega0) 
                               xstar) -
                 (1 - α n0) * vector_nth i pf (Rvector_minus (x n0 omega0) xstar) -
                 α n0 * vector_nth i pf (w n0 omega0)) with
           (α n0 * vector_nth i pf (Rvector_minus (F (x n0 omega0)) (F xstar))).
       - replace (- α n0 * gamma * C) with (- ( α n0 * gamma * C)) by lra.
         rewrite <- Rabs_le_between.
         rewrite Rabs_mult.
         rewrite Rabs_right.
         + rewrite Rmult_assoc.
           apply Rmult_le_compat_l; try apply H.
           specialize (H1 (x n0 omega0) xstar).
           generalize (Rvector_max_abs_nth_le  (Rvector_minus (F (x n0 omega0)) (F xstar))); intros.
           eapply Rle_trans.
           apply H7.
           eapply Rle_trans.
           apply H1.
           apply Rmult_le_compat_l; try apply H0.           
           specialize (H3 n0 omega0).
           apply H3.
         + apply Rle_ge.
           apply H.
       - unfold vecrvplus, vecrvscale, Rvector_minus.
         unfold Rvector_opp.
         ring_simplify.
         rewrite Rvector_scale_plus_l.
         do 5 rewrite Rvector_nth_plus.
         rewrite H4.
         do 4 rewrite Rvector_nth_scale.
         now ring_simplify.
     Qed.

     Lemma Induction_I2_18_ptwise (α : nat -> R) (xtilde : nat -> Ts -> R) (w : nat -> Ts -> R) (C:R) (omega0 : Ts) :
      (forall n, 0 <= α n <= 1) -> 
      (forall n, Rabs (xtilde n omega0) <= C) ->
      (forall n, 
            (- α n)*gamma*C <= (xtilde (S n) omega0) -  (1 - α n)*(xtilde n omega0) -  (α n)*(w n omega0) <= (α n)*gamma*C) ->
      forall n,
          - (RMseq α (fun n => gamma * C) C n) <= (xtilde n omega0) - (RMseq α (fun n0 => w n0 omega0) 0 n) 
          <= RMseq α (fun n => gamma * C) C n.
    Proof.
      intros.
      induction n.
      - unfold const; simpl.
        rewrite Rminus_0_r.
        specialize (H0 0%nat).
        now apply Rabs_le_between.
      - simpl.
        specialize (H1 n).
        unfold plus, scal; simpl.
        unfold Hierarchy.mult; simpl.
        destruct IHn.
        specialize (H n).
        split.
        + apply Rmult_le_compat_l with (r := 1 - α n) in H2; lra.
        + apply Rmult_le_compat_l with (r := 1 - α n) in H3; lra.
     Qed.

    Lemma Induction_I2_18_Rabs_ptwise (α : nat -> R) (xtilde : nat -> Ts -> R) (w : nat -> Ts -> R) (C:R) (omega0:Ts) :
      (forall n, 0 <= α n <= 1) -> 
      (forall n, Rabs (xtilde n omega0) <= C) ->
      (forall n, 
            (- α n)*gamma*C <= (xtilde (S n) omega0) -  (1 - α n)*(xtilde n omega0) -  (α n)*(w n omega0) <= (α n)*gamma*C) ->
      forall n, 
          Rabs ((xtilde n omega0) - (RMseq α (fun n0 => w n0 omega0) 0 n)) 
          <= RMseq α (fun n => gamma * C) C n.
     Proof.
       intros.
       rewrite Rabs_le_between.
       now apply Induction_I2_18_ptwise.
     Qed.

   Lemma Induction_I2_full_vec_ptwise {k:nat} (α : nat -> R) (x : nat -> Ts -> vector R k) (w : nat -> Ts -> vector R k) (C:R) (xstar : vector R k) (F : vector R k -> vector R k) :
      (forall n, 0 <= α n <= 1) -> 
      0 <= gamma < 1 ->
      (forall (x y : vector R k),
          Rvector_max_abs (Rvector_minus (F x) (F y)) <= 
          gamma * Rvector_max_abs (Rvector_minus x y)) ->
      (forall n,
          (rv_eq (x (S n))
                 (vecrvplus
                    (vecrvscale (1 - α n) (x n)) 
                    (vecrvscale (α n)
                                (vecrvplus (fun v => F (x n v)) (w n)))))) ->
      F xstar = xstar ->
      let xtilde := fun n => fun omega => Rvector_minus (x n omega) xstar in
      forall omega0,
      (forall n, 
            rvmaxabs (vecrvminus (x n) (const xstar)) omega0 <= C) ->        
      forall n,
          forall i,
            forall (pf : (i < k)%nat),
              Rabs (vector_nth i pf (xtilde n omega0) - 
                    (RMseq α (fun n0 => (vector_nth i pf (w n0 omega0))) 0 n)) <=
              RMseq α (fun n => gamma * C) C n.
     Proof.
       intros.
       generalize (Induction_I2_18_Rabs_ptwise α (fun n omega => vector_nth i pf (xtilde n omega))
                                        (fun n omega => vector_nth i pf (w n omega)) C omega0 H); intros.
       assert  (forall (n0 : nat), Rabs (vector_nth i pf (xtilde n0 omega0)) <= C).
       {
         intros.
         specialize (H4 n0).
         generalize (Rvector_max_abs_nth_le (xtilde n0 omega0) i pf); intros.        
         eapply Rle_trans.
         apply H6.
         unfold rvmaxabs in H3.
         eapply Rle_trans.
         apply H4.
         lra.
       }
       apply H5; trivial.
       intros.
       specialize (H2 n0).
       unfold xtilde.
       rewrite H2.
       replace  (vector_nth i pf
                            (Rvector_minus
                               (vecrvplus (vecrvscale (1 - α n0) (x n0))
                                          (vecrvscale (α n0) 
                                                      (vecrvplus 
                                                         (fun v : Ts => F (x n0 v))
                                                         (w n0))) 
                                          omega0) 
                               xstar) -
                 (1 - α n0) * vector_nth i pf (Rvector_minus (x n0 omega0) xstar) -
                 α n0 * vector_nth i pf (w n0 omega0)) with
           (α n0 * vector_nth i pf (Rvector_minus (F (x n0 omega0)) (F xstar))).
       - replace (- α n0 * gamma * C) with (- ( α n0 * gamma * C)) by lra.
         rewrite <- Rabs_le_between.
         rewrite Rabs_mult.
         rewrite Rabs_right.
         + rewrite Rmult_assoc.
           apply Rmult_le_compat_l; try apply H.
           specialize (H1 (x n0 omega0) xstar).
           generalize (Rvector_max_abs_nth_le  (Rvector_minus (F (x n0 omega0)) (F xstar))); intros.
           eapply Rle_trans.
           apply H7.
           eapply Rle_trans.
           apply H1.
           apply Rmult_le_compat_l; try apply H0.           
           specialize (H4 n0).
           apply H4.
         + apply Rle_ge.
           apply H.
       - unfold vecrvplus, vecrvscale, Rvector_minus.
         unfold Rvector_opp.
         ring_simplify.
         rewrite Rvector_scale_plus_l.
         do 5 rewrite Rvector_nth_plus.
         rewrite H3.
         do 4 rewrite Rvector_nth_scale.
         now ring_simplify.
    Qed.

     Lemma Induction_I2_18_prob  (prts : ProbSpace dom) {k:nat} (α : nat -> R) (x : nat -> Ts -> vector R k) (w : nat -> Ts -> vector R k) (C P:R) (xstar : vector R k) (F : vector R k -> vector R k)
           {rv: forall n, RandomVariable dom borel_sa (rvmaxabs (vecrvminus (x n) (const xstar)))}
           {rv2: let xtilde := fun n => fun omega => Rvector_minus (x n omega) xstar in
                 forall n i pf,
                   RandomVariable dom borel_sa
                                  (fun omega : Ts =>
                                     Rabs
                                       (vector_nth i pf (xtilde n omega) -
                                        RMseq α (fun n0 : nat => vector_nth i pf (w n0 omega)) 0 n) -
                                     RMseq α (fun _ : nat => gamma * C) C n)} :
      (forall n, 0 <= α n <= 1) -> 
      0 <= gamma < 1 ->
      (forall (x y : vector R k),
          Rvector_max_abs (Rvector_minus (F x) (F y)) <= 
          gamma * Rvector_max_abs (Rvector_minus x y)) ->
      (forall n,
          (rv_eq (x (S n))
                 (vecrvplus
                    (vecrvscale (1 - α n) (x n)) 
                    (vecrvscale (α n)
                                (vecrvplus (fun v => F (x n v)) (w n)))))) ->
      F xstar = xstar ->
      ps_P (inter_of_collection
              (fun n =>
                 event_le dom (rvmaxabs (vecrvminus (x n) (const xstar))) C)) >= P ->
      let xtilde := fun n => fun omega => Rvector_minus (x n omega) xstar in
      ps_P (inter_of_collection
              (fun n => 
                 (bounded_inter_of_collection 
                    (fun i pf =>
                       event_le 
                         dom (rv := rv2 n i pf)
                         (fun omega =>
                            (Rabs ((vector_nth i pf (xtilde n omega)) - 
                                   (RMseq α (fun n0 => (vector_nth i pf (w n0 omega))) 0 n))) -
                            (RMseq α (fun n => gamma * C) C n)) 0)))) >= P.
     Proof.
       intros.
       assert (
           ps_P (inter_of_collection
              (fun n =>
                 event_le dom (rvmaxabs (vecrvminus (x n) (const xstar))) C)) <=
           ps_P (inter_of_collection
                   (fun n => 
                      (bounded_inter_of_collection 
                         (fun i pf =>
                            event_le 
                              dom (rv := rv2 n i pf)
                              (fun omega =>
                                 (Rabs ((vector_nth i pf (xtilde n omega)) - 
                                        (RMseq α (fun n0 => (vector_nth i pf (w n0 omega))) 0 n))) -
                                 (RMseq α (fun n => gamma * C) C n)) 0))))).
       {
         apply ps_sub.
         intros ? ?.
         apply inter_of_collection_as_pre.
         simpl.
         intros ? ? ?.
         simpl.
         apply Rplus_le_reg_r with (r :=  RMseq α (fun _ : nat => gamma * C) C n).
         unfold Rminus at 1.
         rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
         now apply Induction_I2_full_vec_ptwise with (F0 := F).
       }
       lra.
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
          {frf: FiniteRangeFunction f}       :
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
        (frfxn : forall n0, FiniteRangeFunction (Xn n0))
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
    
    Lemma conv_l2_vector_prob_i {n:nat}
        (eps : posreal) 
        (i : nat)
        (pf : (i < n)%nat)
        {prts: ProbSpace dom}
        (Xn: nat -> Ts -> vector R n) 
        (frfxn : forall n0, FiniteRangeFunction (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq (fun n0 => ps_P (event_ge dom (rvabs (vecrvnth i pf (Xn n0))) eps)) 0.
    Proof.
      intros.
      apply conv_l2_prob1.
      intros.
      replace (NonnegExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0)))))
        with (Finite (SimpleExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0)))))).
      now simpl.
      generalize (frf_NonnegExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0))))).      
      intros.
      symmetry.
      apply H0.
      apply is_lim_seq_ext with
          (u :=  (fun n0 : nat => SimpleExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0)))))).  
      intros.
      symmetry.
      generalize (frf_NonnegExpectation (rvsqr (rvabs (vecrvnth i pf (Xn n0))))); intros.
      now rewrite H0.
      now apply lim_rvinner_0 with (frfxn0 := frfxn).
   Qed.

    Lemma conv_l2_vector_prob {n:nat}
          (eps : posreal)
        {prts: ProbSpace dom}          
        (Xn: nat -> Ts -> vector R n) 
        (frfxn : forall n0, FiniteRangeFunction (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        forall i (pf: (i<n)%nat),
          is_lim_seq (fun n0 => ps_P (event_ge dom (rvabs (vecrvnth i pf (Xn n0))) eps)) 0.
    Proof.
      intros.
      now apply conv_l2_vector_prob_i with (frfxn0 := frfxn).
    Qed.

    Lemma conv_l2_conv_linf_sqr {n:nat}
        {prts: ProbSpace dom}                    
        (Xn: nat -> Ts -> vector R n) 
        (frfxn : forall n0, FiniteRangeFunction (Xn n0))
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
        {frf: FiniteRangeFunction X}  :       
      IsFiniteExpectation prts X.
    Proof.
      generalize (Expectation_simple X); intros.
      generalize (Expectation_IsFiniteExpectation prts X); intros.
      now specialize (H0 _ H).
    Qed.

    Program Instance frfpower
           (rv_X : Ts -> R) (r:R)
           {prts: ProbSpace dom}                    
           {frf:FiniteRangeFunction rv_X} : 
      FiniteRangeFunction (rvpower (rvabs rv_X) (const r)) :=
      {frf_vals := map (fun x => power (Rabs x) r) frf_vals }.
    Next Obligation.
      unfold rvpower, rvabs, const.
      apply in_map_iff.
      destruct frf.
      exists (rv_X x).
      split; trivial.
    Qed.

    Instance IsLp_simple
        (X:  Ts -> R)
        {prts: ProbSpace dom}                    
        (rv : RandomVariable dom borel_sa X) 
        (frf: FiniteRangeFunction X)  :       
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
        {frf : FiniteRangeFunction X} :
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
        (frfxn : forall n, FiniteRangeFunction (Xn n))  :       
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
        {frfxn : forall n0, FiniteRangeFunction (Xn n0)}
        {rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)} :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq
          (fun n0 : nat =>
             SimpleExpectation (rvmaxabs (Xn n0))) 0.
     Proof.
       intros.
       generalize (conv_l2_conv_linf_sqr Xn frfxn rvxn H); intros.
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
          (frf : FiniteRangeFunction X)
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
          (frf : FiniteRangeFunction X)
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
          (frf : FiniteRangeFunction X)
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
      NonnegativeFunction (rvmaxabs X).
    Proof.
      unfold NonnegativeFunction, rvmaxabs.
      intros.
      apply Rvector_max_abs_nonneg.
    Qed.

    Lemma conv_l2_vector_prob_max_abs {n:nat}
        (eps : posreal)
          {prts: ProbSpace dom}                              
        (Xn: nat -> Ts -> vector R n) 
        (frfxn : forall n0, FiniteRangeFunction (Xn n0))
        (rvxn : forall n0, RandomVariable dom (Rvector_borel_sa n) (Xn n0)) :
        is_lim_seq
          (fun n0 : nat =>
              SimpleExpectation (rvinner (Xn n0) (Xn n0))) 0 ->
        is_lim_seq (fun n0 => ps_P (event_ge dom (rvmaxabs (Xn n0)) eps)) 0.
    Proof.
      intros.
      apply conv_l2_conv_linf in H.
      apply is_lim_seq_le_le_loc with (u := fun _ => 0) 
                                      (w := (fun n => (NonnegExpectation (rvmaxabs (Xn n))) / eps)).
      - exists (0%nat); intros.
        split.
        + apply ps_pos.
        + generalize (conv_l1_prob_le prts eps (rvmaxabs (Xn n0))); intros.
          rewrite NonnegExpectation_ext with (nnf2 := nnfabs (rvmaxabs (Xn n0))).
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
            generalize (simple_NonnegExpectation (rvabs (rvmaxabs (Xn n0)))); intros.
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
          generalize (simple_NonnegExpectation (rvmaxabs (Xn n0))); intros.
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

    Declare Scope Rvector_scope.
    Delimit Scope Rvector_scope with Rvector.
    Bind Scope Rvector_scope with vector R.
    Local Open Scope Rvector_scope.

    Notation "c .* v" := (Rvector_scale (c%R) v) (at level 41, right associativity) : Rvector_scope.
    Notation "x + y" := (Rvector_plus x y) (at level 50, left associativity) : Rvector_scope.

    Hint Rewrite @Rvector_nth_plus @Rvector_nth_scale @Rvector_nth_mult @Rvector_nth_minus @Rvector_nth_opp : vector.

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

  End qlearn4.

  Section qlearn5.
    Context (gamma : R) {Ts : Type}
            {dom: SigmaAlgebra Ts}.

    Lemma is_sup_seq_const (c : R) :
      is_sup_seq (fun n => c)  c.
    Proof.
      unfold is_sup_seq.
      intros.
      assert (eps > 0) by apply cond_pos.
      split.
      - intros.
        simpl; lra.
      - exists (0%nat).
        simpl; lra.
   Qed.
    
    Lemma Sup_seq_const (c : R) :
      Sup_seq (fun n => c) = c.
    Proof.
      generalize (is_sup_seq_const c); intros.
      now apply is_sup_seq_unique.
    Qed.
    
    Lemma conv_as_prob_0 {prts: ProbSpace dom} (f : nat -> Ts -> R) 
          {rv : forall n, RandomVariable dom borel_sa (f n)} :
      almost prts (fun x => is_lim_seq (fun n => f n x) 0) ->
      forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_gt dom (rvabs (f n)) eps)) 0.
    Proof.
      intros.
      assert (almost prts (fun x => is_lim_seq (fun n =>
                            EventIndicator (classic_dec (event_gt dom (rvabs (f n)) eps)) x) 0)).
      {
        apply almost_impl' with (P1 := (fun x => is_lim_seq (fun n => f n x) 0)); trivial.
        apply all_almost.
        intros.
        unfold EventIndicator; simpl.
        apply is_lim_seq_spec in H0.
        apply is_lim_seq_spec.
        unfold is_lim_seq'.
        unfold is_lim_seq' in H0.
        intros.
        specialize (H0 eps).
        destruct H0.
        exists x0.
        intros.
        specialize (H0 n H1).
        unfold rvabs.
        rewrite Rminus_0_r in H0.
        match_destr; try lra.
        rewrite Rminus_0_r.
        rewrite Rabs_R0.
        apply cond_pos.
      }
      generalize (Dominated_convergence_almost 
                    prts 
                    (fun n => 
                       EventIndicator (classic_dec (event_gt dom (rvabs (f n)) eps)))
                    (const 0)
                 ); intros.
      specialize (H1 (const 1)).
      cut_to H1; try typeclasses eauto.
      assert  (isfefn : forall n : nat,
                   IsFiniteExpectation prts
                     (EventIndicator (classic_dec (event_gt dom (rvabs (f n)) eps)))).
      {
        intros.
        apply IsFiniteExpectation_simple; try typeclasses eauto.
      }
      assert (isfefn' : forall n : nat,
                 Rbar_IsFiniteExpectation prts
                                          (EventIndicator (classic_dec (event_gt dom (rvabs (f n)) eps)))).
      {
        intros.
        now apply IsFiniteExpectation_Rbar.
      } 
      specialize (H1 isfefn' (Rbar_IsFiniteExpectation_const prts 0) (Rbar_IsFiniteExpectation_const prts 1)).
      cut_to H1.
      - generalize (fun n => Expectation_EventIndicator (classic_dec (event_gt dom (rvabs (f n)) eps)) ); intros.
        apply is_lim_seq_ext with (v := (fun n : nat => ps_P (event_gt dom (rvabs (f n)) eps))) in H1.
        + replace (Rbar_FiniteExpectation prts (const 0)) with (0) in H1; trivial.
          now rewrite Rbar_FiniteExpectation_const.
        + intros.
          generalize (FiniteExpectation_indicator prts (classic_dec (event_gt dom (rvabs (f n)) eps))); intros.
          rewrite <- H3.
          rewrite (Rbar_FinExp_FinExp _ _).
          apply FiniteExpectation_pf_irrel.
      - intros.
        apply all_almost.
        intros.
        simpl.
        rv_unfold.
        match_destr.
        + rewrite Rabs_right; lra.
        + rewrite Rabs_R0; lra.
      - revert H0.
        apply almost_impl.
        apply all_almost; intros ??.
        now apply is_Elim_seq_fin.
   Qed.

    Lemma conv_as_prob_1 {prts: ProbSpace dom} (f : nat -> Ts -> R) 
          {rv : forall n, RandomVariable dom borel_sa (f n)} :
      almost prts (fun x => is_lim_seq (fun n => f n x) 0) ->
      forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_lt dom (rvabs (f n)) eps)) 1.
    Proof.
      intros.
      assert (almost prts (fun x => is_lim_seq (fun n =>
                            EventIndicator (classic_dec (event_lt dom (rvabs (f n)) eps)) x) 1)).
      {
        apply almost_impl' with (P1 := (fun x => is_lim_seq (fun n => f n x) 0)); trivial.
        apply all_almost.
        intros.
        unfold EventIndicator; simpl.
        apply is_lim_seq_spec in H0.
        apply is_lim_seq_spec.
        unfold is_lim_seq'.
        unfold is_lim_seq' in H0.
        intros.
        specialize (H0 eps).
        destruct H0.
        exists x0.
        intros.
        specialize (H0 n H1).
        unfold rvabs.
        rewrite Rminus_0_r in H0.
        match_destr; try lra.
        replace (1 - 1) with (0) by lra.
        rewrite Rabs_R0.
        apply cond_pos.
      }
      generalize (Dominated_convergence_almost 
                    prts 
                    (fun n => 
                       EventIndicator (classic_dec (event_lt dom (rvabs (f n)) eps)))
                    (const 1)
                 ); intros.
      specialize (H1 (const 1)).
      cut_to H1; try typeclasses eauto.
      assert  (isfefn : forall n : nat,
                   IsFiniteExpectation prts
                     (EventIndicator (classic_dec (event_lt dom (rvabs (f n)) eps)))).
      {
        intros.
        apply IsFiniteExpectation_simple; try typeclasses eauto.
      }
      assert  (isfefn' : forall n : nat,
                   Rbar_IsFiniteExpectation prts
                     (EventIndicator (classic_dec (event_lt dom (rvabs (f n)) eps)))).
      {
        intros.
        now apply IsFiniteExpectation_Rbar.
      }
      specialize (H1 isfefn' (Rbar_IsFiniteExpectation_const prts 1) (Rbar_IsFiniteExpectation_const prts 1)).
      cut_to H1.
      - generalize (fun n => Expectation_EventIndicator (classic_dec (event_lt dom (rvabs (f n)) eps)) ); intros.
        apply is_lim_seq_ext with (v := (fun n : nat => ps_P (event_lt dom (rvabs (f n)) eps))) in H1.
        + now rewrite Rbar_FiniteExpectation_const in H1.
        + intros.
          generalize (FiniteExpectation_indicator prts (classic_dec (event_lt dom (rvabs (f n)) eps))); intros.
          rewrite <- H3.
          rewrite (Rbar_FinExp_FinExp _ _).
          apply FiniteExpectation_pf_irrel.
      - intros.
        apply all_almost.
        intros; simpl.
        rv_unfold.
        match_destr.
        + rewrite Rabs_right; lra.
        + rewrite Rabs_R0; lra.
      - revert H0.
        apply almost_impl; apply all_almost; intros ??.
        now apply is_Elim_seq_fin.
   Qed.

(*
  Lemma sa_le_Rbar_gt_rv {domm}
        (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : sa_sigma _ (fun omega => Rbar_gt (rv_X omega) x).
  Proof.
    apply Rbar_sa_le_gt.
    intros.
    now apply rv_Rbar_measurable.
  Qed.

  Definition event_Rbar_gt {domm}
             (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : event domm
    := @exist (pre_event Ts) _ _ (sa_le_Rbar_gt_rv rv_X x).

  Lemma sa_le_Rbar_lt_rv {domm}
        (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : sa_sigma _ (fun omega => Rbar_lt (rv_X omega) x).
  Proof.
    apply Rbar_sa_le_lt.
    intros.
    now apply rv_Rbar_measurable.
  Qed.

  Definition event_Rbar_lt {domm}
             (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : event domm
    := @exist (pre_event Ts) _ _ (sa_le_Rbar_lt_rv rv_X x).

  Lemma sa_le_Rbar_le_rv {domm}
        (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : sa_sigma _ (fun omega => Rbar_le (rv_X omega) x).
  Proof.
    now apply rv_Rbar_measurable.
  Qed.

  Definition event_Rbar_le {domm}
             (rv_X : Ts -> Rbar) {rv : RandomVariable domm Rbar_borel_sa rv_X} x
    : event domm
    := @exist (pre_event Ts) _ _ (sa_le_Rbar_le_rv rv_X x).

  Lemma inter_coll_le_sup {prts: ProbSpace dom} (f : nat -> Ts -> R) (eps:R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
    forall n,
      event_equiv
        (inter_of_collection (fun t : nat => event_le dom (rvabs (f (n + t)%nat)) eps))
        (event_Rbar_le (fun x0 : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x0))) eps).
    Proof.
      intros n z.
      simpl.
      unfold rvabs.
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

    Lemma event_Rbar_gt_complement (f : Ts -> Rbar) (eps:posreal)
          {rv : RandomVariable dom Rbar_borel_sa f} :
      event_equiv
        (event_Rbar_gt f eps)
        (event_complement (event_Rbar_le f eps)).
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
        (event_Rbar_gt (fun x0 : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x0))) eps).
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

    Lemma conv_as_prob_sup_1 {prts: ProbSpace dom} (f : nat -> Ts -> R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
      almost prts (fun x => is_lim_seq (fun n => f n x) 0) ->
      forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_Rbar_le (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) eps)) 1. 
      Proof.
        intros.
        destruct H as [? [? ?]].
        pose (A := union_of_collection (fun m => inter_of_collection (fun t => event_le dom (rvabs (f (m + t)%nat)) eps))).
        assert (ps_P A = 1).
        {
          assert (ps_P x <= ps_P A).
          {
            apply ps_sub.
            intros ? ?.
            simpl.
            specialize (H0 x0 H1).
            apply is_lim_seq_spec in H0.
            specialize (H0 eps).
            destruct H0.
            exists x1.
            unfold rvabs.
            setoid_rewrite Rminus_0_r in H0.
            intros.
            specialize (H0 (x1 + n)%nat).
            cut_to H0; try lia.
            lra.
          }
          rewrite H in H1.
          generalize (ps_le1 prts A); intros.
          lra.
        }
        assert (is_lim_seq (fun m => ps_P (inter_of_collection (fun t => event_le dom (rvabs (f (m + t)%nat)) eps))) (ps_P A)).
        {
          unfold A.
          apply lim_prob.
          - intros n ? ?.
            simpl.
            simpl in H2.
            intros.
            specialize (H2 (S n0)).
            now replace (S (n + n0)%nat) with (n + S n0)%nat by lia.
          - intros ?.
            simpl.
            tauto.
        }
        generalize (inter_coll_le_sup f eps); intros.
        rewrite H1 in H2.
        apply is_lim_seq_ext with
            (u :=  (fun m : nat =>
          ps_P (inter_of_collection (fun t : nat => event_le dom (rvabs (f (m + t)%nat)) eps)))).
        - intros.
          now rewrite H3.
        - apply H2.
      Qed.
          
     Lemma conv_prob_sup_0_as {prts: ProbSpace dom} (f : nat -> Ts -> R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x)))}:
      (forall (eps:posreal),
        is_lim_seq (fun n => ps_P (event_Rbar_gt (fun x => Sup_seq (fun m => Rabs (f (n + m)%nat x))) eps)) 0) ->
      almost prts (fun x => is_lim_seq (fun n => f n x) 0).
    Proof.
      intros.
      rewrite  slln.almost_is_lim_seq_iff.
      intros.
      assert (0 < eps) by apply cond_pos.
      assert (0 < eps/2) by lra.
      specialize (H (mkposreal _ H1)).
      apply is_lim_seq_le_le with (u := fun n => 0)
                                  (w :=  (fun n : nat =>
         ps_P
           (event_Rbar_gt (fun x : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x)))
                          (mkposreal _ H1)))); trivial.
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

 *)
    
    Lemma L2_convergent_x_nth_RMseq (i n:nat) (pf : (i < S n)%nat) (α : nat -> R) 
          (w : nat -> Ts -> vector R (S n)) (omega:Ts) :
      forall n0, 
        vector_nth i pf (@L2_convergent_x 
                           (S n) α 
                           (vecrvconst (S n) 0) Ts
                           (vecrvconst (S n) 0) w n0 omega) =
        RMseq (fun n0 : nat => α (n0)%nat)
              (fun n0 : nat => vector_nth i pf (w (n0)%nat omega)) 
              0 n0.
    Proof.
      unfold vecrvconst.
      induction n0.
      - simpl.
        now rewrite vector_nth_const.
      - simpl.
        unfold F_alpha, vecrvplus, vecrvscale.
        do 2 rewrite Rvector_nth_plus.
        do 3 rewrite Rvector_nth_scale.
        rewrite IHn0, vector_nth_const.
        unfold plus, scal; simpl.
        unfold Hierarchy.mult; simpl.
        ring.
    Qed.

    Lemma one_minus_a_lt_one_minus_b (a b : R) :
      1 - a < 1 - b -> a > b.
    Proof.
      lra.
    Qed.

    Lemma rvabs_rvmaxabs {n} (f : Ts -> vector R n) :
      rv_eq
        (rvabs (rvmaxabs f))
        (rvmaxabs f).
    Proof.
      intros ?.
      unfold rvmaxabs, rvabs.
      rewrite Rabs_right; trivial.
      apply Rle_ge.
      apply Rvector_max_abs_nonneg.
    Qed.

    Lemma Rvector_max_abs_nth_Rabs_le {n} (v : vector R (S n)) (c:R) :
      Rvector_max_abs v <= c <->
      forall (i : nat) (pf : (i < S n)%nat),
        Rabs (vector_nth i pf v) <= c.
    Proof.
      split; intros.
      - eapply Rle_trans.
        apply Rvector_max_abs_nth_le.
        apply H.
      - destruct (Rvector_max_abs_nth_in v) as [? [? ?]].
        rewrite H0.
        apply H.
    Qed.
    

  Lemma inter_coll_le_sup_pos {prts: ProbSpace dom} (f : nat -> Ts -> R) (eps:R)
          {rv : forall n, RandomVariable dom borel_sa (f n)} 
          {nneg : forall n, NonnegativeFunction (f n)}
          {rv2: forall n, RandomVariable dom Rbar_borel_sa (fun x => Sup_seq (fun m => f (n + m)%nat x))}:
    forall n,
      event_equiv
        (inter_of_collection (fun t : nat => event_le dom (f (n + t)%nat) eps))
        (event_Rbar_le (fun x0 : Ts => Sup_seq (fun m : nat => f (n + m)%nat x0)) eps).
    Proof.
      intros.
      assert (forall n, rv_eq (f n) (rvabs (f n))).
      {
        intros ? ?.
        unfold rvabs.
        rewrite Rabs_right; trivial.
        apply Rle_ge.
        apply nneg.
      }
      assert (forall n, rv_eq
                (fun x : Ts => Sup_seq (fun m : nat => rvabs (f (n+m)%nat) x))
                (fun x : Ts => Sup_seq (fun m : nat => (f (n+m)%nat) x))).
      {
        intros ? ?.
        apply Sup_seq_ext.
        intros.
        unfold rvabs.
        rewrite Rabs_right; trivial.
        apply Rle_ge.
        apply nneg.
      }
      assert (event_equiv
                (inter_of_collection (fun t : nat => event_le dom (f (n+t)%nat) eps))
                (inter_of_collection (fun t : nat => event_le dom (rvabs (f (n+t)%nat)) eps))).
      {
        intros ?.
        simpl.
        split; intros.
        - now rewrite <- H.
        - now rewrite H.
      }
      rewrite H1.
      rewrite inter_coll_le_sup.
      intros ?.
      simpl.
      unfold rvabs in H0.
      now rewrite H0.
      Unshelve.
      intros.
      unfold rvabs in H0.
      now rewrite H0.
   Qed.

    Lemma vecrvminus_unfold {n} (x y : Ts -> vector R n)
      : rv_eq (vecrvminus x y)  (fun a => Rvector_minus (x a) (y a)).
    Proof.
      unfold vecrvminus, vecrvplus, Rvector_minus.
      intros a.
      f_equal.
    Qed.

    Lemma Induction_I1_17 {n} (eps P C0: posreal) (α : nat -> R) (C : R) (w x : nat -> Ts -> vector R (S n)) (xstar : vector R (S n))
          (F : (vector R (S n)) -> (vector R (S n)))
          {prts: ProbSpace dom}                              
          (rx : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (x n0))
          (rw : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (w n0))
          (isfew : forall n0, vector_IsFiniteExpectation prts (w n0))
          (srw : forall n0, FiniteRangeFunction  (w n0))
          (rvsup : forall nk, RandomVariable dom Rbar_borel_sa
                    (fun (omega : Ts) =>
                       Sup_seq (fun (n0 : nat) =>
                                  (rvmaxabs (vecrvminus (x (nk + n0)%nat) (const xstar))) omega))) :
      P < 1 ->
      0 <= C ->
      0 <= gamma < 1 ->
      gamma + eps < 1 ->
(*      (forall n, 0 <= α n <= 1) -> *)
      (forall n, 0 <= α n < 1) ->             
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      ex_series (fun n => (α n)^2) ->
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
         rv_eq (vector_FiniteConditionalExpectation
                  prts (filtration_history_sa_sub 
                          (cod := Rvector_borel_sa (S n)) 
                          (@L2_convergent_x (S n)
                                            (fun k => α (k + nk)%nat) 
                                            (const Rvector_zero) Ts
                                            (const Rvector_zero) 
                                            (fun k => w (k + nk)%nat))
                          n0) 
                  (w (n0 + nk)%nat))
         (const Rvector_zero)) ->
      forall (k:nat),
      exists (nk : nat),
        ps_P 
          (event_Rbar_le
                    (fun (omega : Ts) =>
                       Sup_seq (fun (n0 : nat) =>
                                  (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar))) omega))
                    (C0 * (gamma + eps)^k))
        >= 1 - (INR k) * (1 - P).
    Proof.
      intros Plim Clim glim geps alim aseq sumaseq exser_asq Fcont Fxstar xrel xlim wexp condexp k.
       induction k.
      - exists (0%nat).
        intros.
        simpl.
        rewrite Rmult_0_l.
        rewrite Rminus_0_r.
        rewrite Rmult_1_r.
        assert (event_equiv 
                  (event_Rbar_le
                            (fun omega : Ts =>
                               Sup_seq (fun n0 : nat => rvmaxabs (vecrvminus (x (n0 + 0)%nat) 
                                                                             (const xstar)) omega)) 
                            C0)
                    Ω).
        {
          intro omega.
          unfold  Ω, pre_Ω, sa_all; simpl.
          generalize (Sup_seq_le (fun n0 : nat => rvmaxabs (vecrvminus (x (n0 + 0)%nat) 
                                                                       (const xstar)) omega)
                                 (fun n0 => C0)); intros.
          cut_to H.
          - rewrite Sup_seq_const in H.
            tauto.
          - intros.
            simpl.
            apply xlim.
        }
        rewrite H.
        right.
        apply ps_one.
      - destruct IHk as [nk IHk].
        generalize (RMseq_const_lim gamma (fun n0 => α (n0 + nk)%nat) (C0 * (gamma + eps)^k) (C0 * (gamma + eps)^k) glim); intros.
        assert (forall n, 0 <= α (n + nk)%nat <= 1).
        {
          intros.
          specialize (alim (n0 + nk)%nat).
          lra.
        }
        assert (is_lim_seq (fun n0 : nat => α (n0 + nk)%nat) 0) by now apply is_lim_seq_incr_n.
        specialize (H H0 H1).
        assert (0 < eps * (C0 * (gamma + eps)^k)/2).
        {
          apply Rmult_lt_0_compat; try lra.
          apply Rmult_lt_0_compat; try apply cond_pos.
          apply Rmult_lt_0_compat; try apply cond_pos.
          apply pow_lt.
          apply Rlt_le_trans with (r2 := eps).
          apply cond_pos.
          replace (pos eps) with (0 + eps) at 1 by lra.
          now apply Rplus_le_compat_r.
        }
        cut_to H.
        + assert (exists (n2 :nat), 
                     forall n,
                       (RMseq (fun n0 : nat => α (n0 + nk)%nat)
                              (fun _ : nat => gamma * (C0 * (gamma + eps) ^ k)) 
                              (C0 * (gamma + eps)^k)
                              (n + n2) ) <= gamma * (C0 * (gamma + eps)^k) + 
                                            eps * (C0 * (gamma + eps)^k)/2).
          {
            apply is_lim_seq_spec in H.
            specialize (H (mkposreal _ H2)).
            destruct H.
            exists x0.
            intros.
            specialize (H (n0 + x0)%nat).
            cut_to H; try lia.
            simpl in H.
            apply Rabs_lt_between in H.
            lra.
          }
          generalize (as_convergent_lemma (I := S n) ); intros.
          specialize (H4 (fun n0 : nat => α (n0 + nk)%nat) (const (@ Rvector_zero (S n))) Ts dom prts C
                         (fun n0 : nat => w (n0 + nk)%nat)).
          specialize (H4 (fun n2 : nat => rw (n2 + nk)%nat) _ (fun n2 : nat => srw (n2 + nk)%nat)).
          cut_to H4; trivial.
          * pose (f := (fun n0 w1 =>  
                                 rvmaxabs
                                   (L2_convergent_x (F := (const (@ Rvector_zero (S n))))
                                      (fun n1 : nat => α (n1 + nk)%nat) (const Rvector_zero)
                                      (fun n1 : nat => w (n1 + nk)%nat) n0) w1)).
            assert (forall n0, RandomVariable dom borel_sa (f n0)) by typeclasses eauto.
            assert (forall n,  
                       RandomVariable dom Rbar_borel_sa
                                      (fun x : Ts => Sup_seq (fun m : nat => Rabs (f (n + m)%nat x)))) by
                typeclasses eauto.
            generalize (conv_as_prob_sup_1 _ H4  (mkposreal _ H2) ); intros.
            apply is_lim_seq_spec in H7.
            assert (1-P > 0) by lra.
            specialize (H7 (mkposreal _ H8)).
            destruct H7.
            simpl in H7.
            setoid_rewrite Rabs_minus_sym in H7.
            destruct H3.
            exists (x0 + x1 + nk)%nat.
            assert (rv2_18 : let xtilde :=
                  fun (n0 : nat) (omega : Ts) => Rvector_minus (x (n0 + nk)%nat omega) xstar in
                forall (n0 i : nat) (pf : (i < S n)%nat),
                RandomVariable dom borel_sa
                  (fun omega : Ts =>
                   Rabs
                     (vector_nth i pf (xtilde n0 omega) -
                      RMseq (fun n0 => α (n0 + nk)%nat) (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega)) 0 n0) -
                   RMseq (fun n0 => α (n0 + nk)%nat) (fun _ : nat => gamma * (C0 * (gamma + eps) ^ k)) 
                         (C0 * (gamma + eps) ^ k) n0)).
            {
              simpl.
              intros.
              generalize (rvminus_rv dom
                            (fun omega : Ts =>
                               Rabs
                                 (vector_nth i pf (Rvector_minus (x (n0 + nk)%nat omega) xstar) -
                                  RMseq (fun n0 => α (n0 + nk)%nat) (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega)) 0 n0) )); intros.
              specialize (H9
                            (fun omega : Ts =>
                               RMseq (fun n0 => α (n0 + nk)%nat) (fun _ : nat => gamma * (C0 * (gamma + eps) ^ k)) 
                                     (C0 * (gamma + eps) ^ k) n0)).
              rewrite rvminus_unfold in H9.
              apply H9.
              - apply rvabs_rv.
                unfold Rminus.
                apply rvplus_rv.
                + assert (rv_eq
                            (fun omega : Ts => vector_nth i pf (Rvector_minus (x (n0 + nk)%nat omega) xstar))
                            (vector_nth i pf (iso_f (fun omega : Ts => Rvector_minus (x (n0 + nk)%nat omega) xstar)))).

                  {
                    intros ?.
                    unfold iso_f; simpl.
                    now rewrite vector_nth_fun_to_vector.
                  }
                  rewrite H10.
                  apply vec_rv.
                  apply Rvector_minus_rv.
                  * typeclasses eauto.
                  * apply rvconst.
                + generalize (rvopp_rv dom); intros.
                  specialize (H10
                                (fun omega : Ts => RMseq (fun n0 => α (n0 + nk)%nat) (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega)) 0 n0)).
                  unfold rvopp in H10.
                  unfold rvscale in H10.
                  assert (rv_eq
                            (fun omega : Ts =>
                               -1 * RMseq (fun n0 => α (n0 + nk)%nat) (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega)) 0 n0)
                             (fun omega : Ts => - RMseq (fun n0 => α (n0 + nk)%nat) (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega)) 0 n0)).
                  {
                    intros ?.
                    lra.
                  }
                  rewrite H11 in H10.
                  apply H10.
                  apply RMseq_rv.
                  intros.
                  assert (rv_eq
                            (fun omega : Ts => vector_nth i pf (w (n1 + nk)%nat omega))
                            (vector_nth i pf (iso_f (w (n1 + nk)%nat)))).
                  {
                    intros ?.
                    unfold iso_f; simpl.
                    now rewrite vector_nth_fun_to_vector.
                  }
                  rewrite H12.
                  now apply vec_rv.
                - apply rvconst.
            }
            simpl in rv2_18.
            generalize (Induction_I2_18_prob gamma prts (fun n => α (n + nk)%nat)
                                             (fun n => x (n + nk)%nat )
                                             (fun n => w (n + nk)%nat )
                                             (C0 * (gamma + eps)^k) (1 - INR k * (1 - P)) xstar F (rv2 := rv2_18) ) ; intros.
            assert (forall n0,
                       (x0 <= n0)%nat ->
                       ps_P
                         (inter_of_collection 
                            (fun m => 
                               event_le 
                                 dom 
                                 (rvabs 
                                    (rvmaxabs
                                       (L2_convergent_x (F := const Rvector_zero)
                                                        (fun n1 : nat => α (n1 + nk)%nat) 
                                                        (const Rvector_zero) (fun n1 : nat => w (n1 + nk)%nat) 
                                                        (n0 + m))))
                                 (eps * (C0 * (gamma + eps) ^ k) / 2))) > P).
            {
              intros.
              specialize (H7 n0 H10).
              rewrite Rabs_right in H7.
              - apply one_minus_a_lt_one_minus_b in H7.
                eapply Rge_gt_trans.
                shelve.
                apply H7.
                Unshelve.
                right.
                apply ps_proper.
                rewrite (inter_coll_le_sup
                           (fun t =>  (rvmaxabs
                                         (L2_convergent_x 
                                            (F := const Rvector_zero) 
                                            (fun n1 : nat => α (n1 + nk)%nat) 
                                            (const Rvector_zero)
                                            (fun n1 : nat => w (n1 + nk)%nat) (t))))  
                           (mkposreal _ H2) n0).
                simpl.
                intros ?.
                unfold event_Rbar_le; simpl.
                erewrite Sup_seq_ext; try reflexivity.
              - apply Ropp_ge_cancel.
                apply Rle_ge.
                apply Rplus_le_reg_r with (r := 1).
                ring_simplify.
                apply ps_le1.
            }
            clear H7.
            assert (forall n0,
                       (x0 <= n0)%nat ->
                       ps_P
                         (inter_of_collection 
                            (fun m =>
                               bounded_inter_of_collection
                                 (fun (i : nat) (pf : (i < S n)%nat) =>
                                    event_le 
                                      dom 
                                      (fun omega =>
                                      (Rabs
                                         (RMseq (fun n1 : nat => α (n1 + nk)%nat)
                                               (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega))
                                               0 (n0 + m)%nat)))
                                      (eps * (C0 * (gamma + eps) ^ k) / 2)))) > P).
            {
              intros.
              specialize (H10 n0 H7).
              eapply Rge_gt_trans.
              shelve.
              apply H10.
              Unshelve.
              right.
              apply ps_proper.
              intros ?.
              simpl.
              unfold pre_bounded_inter_of_collection; simpl.
              split; intros.
              - specialize (H11 n1).
                rewrite rvabs_rvmaxabs.
                unfold rvmaxabs.
                rewrite Rvector_max_abs_nth_Rabs_le.
                intros.
                now rewrite L2_convergent_x_nth_RMseq.
              - specialize (H11 n1).
                rewrite rvabs_rvmaxabs in H11.
                unfold rvmaxabs in H11.
                rewrite Rvector_max_abs_nth_Rabs_le in H11.
                specialize (H11 i pf).
                now rewrite L2_convergent_x_nth_RMseq in H11.
            }
            clear H10.
            cut_to H9; trivial.
            -- simpl in H9.
               pose (A := inter_of_collection
                            (fun n0 : nat =>
                               bounded_inter_of_collection
                                 (fun (i : nat) (pf : (i < S n)%nat) =>
                                    event_le 
                                      dom
                                      (fun omega : Ts =>
                                         Rabs
                                           (vector_nth i pf (Rvector_minus (x (n0 + nk)%nat omega) xstar)
                                            -  RMseq (fun n : nat => α (n + nk)%nat)
                                                     (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega)) 0 n0)
                                         -
                                         RMseq (fun n : nat => α (n + nk)%nat)
                                               (fun _ : nat => gamma * (C0 * (gamma + eps) ^ k)) 
                                               (C0 * (gamma + eps) ^ k) n0) 0))).
               pose (B := fun n0 =>
                            (inter_of_collection
                               (fun m : nat =>
                                   bounded_inter_of_collection
                                     (fun (i : nat) (pf : (i < S n)%nat) =>
                                        event_le 
                                          dom
                                          (fun omega : Ts =>
                                             Rabs
                                               (RMseq (fun n1 : nat => α (n1 + nk)%nat)
                                                      (fun n1 : nat => vector_nth i pf (w (n1 + nk)%nat omega)) 0 
                                                      (n0 + m))) 
                                          (eps * (C0 * (gamma + eps) ^ k) / 2))))).
               pose (D := fun n =>
                            RMseq (fun n0 : nat => α (n0 + nk)%nat) 
                                  (fun _ : nat => gamma * (C0 * (gamma + eps) ^ k))
                                  (C0 * (gamma + eps)^k) (n + x1) <=
                            gamma * (C0 * (gamma + eps) ^ k) + eps * (C0 * (gamma + eps) ^ k) / 2).
               pose (E :=
                       event_Rbar_le
                          (fun omega : Ts =>
                             Sup_seq
                               (fun n0 : nat =>
                                  rvmaxabs (vecrvminus 
                                              (x ((x0 + x1 + nk) + n0)%nat) 
                                              (const xstar))
                                           omega)) 
                          (C0 * (gamma + eps) ^ S k)).
               (* show A /\ B -> E *)
               (* ps_P (A) >= 1 - INR k *(1-P) by H9 *)
               (* B comes from H7 with prob > P for n0 >= x0*)
               (* D is absolute from H3 *)
               assert (forall (x:Ts), ((A x) /\ (forall n0, (x0 <= n0)%nat -> (B n0 x)) /\ (forall n0, (D n0))) -> E x).
               {
                 unfold A, B, D, E.
                 intros.
                 generalize (inter_coll_le_sup_pos
                               (fun n0 : nat =>
                                  rvmaxabs (vecrvminus (x n0)%nat 
                                                       (const xstar)))); intros.
                 specialize (H11  (C0 * (gamma + eps) ^ S k)).
                 assert (forall n0,
                             RandomVariable dom borel_sa (rvmaxabs (vecrvminus (x n0) (const xstar)))) 
                   by typeclasses eauto.
                 assert  (forall n0 : nat, NonnegativeFunction (rvmaxabs (vecrvminus (x n0) (const xstar)))).
                 {
                   intros.
                   unfold rvmaxabs.
                   unfold NonnegativeFunction.
                   intros.
                   apply Rvector_max_abs_nonneg.
                 }
                 specialize (H11 H12 H13 rvsup).
                 specialize (H11 (x0 + x1 + nk)%nat).
                 specialize (H11 x2).
                 simpl in H11.
                 simpl.
                 rewrite <- H11.
                 intros.
                 unfold rvmaxabs.
                 rewrite Rvector_max_abs_nth_Rabs_le; intros.
                 destruct H10 as [AA [BB DD]].
                 simpl in AA.
                 simpl in BB.
                 specialize (AA (x0 + x1 + n0)%nat).
                 unfold pre_bounded_inter_of_collection in AA.
                 specialize (AA i pf).
                 simpl in AA.
                 replace (x0 + x1 + n0 + nk)%nat with (x0 + x1 + nk + n0)%nat in AA by lia.
                 specialize (BB (x0 + x1)%nat).
                 cut_to BB; try lia.
                 specialize (BB n0).
                 unfold pre_bounded_inter_of_collection in BB.
                 specialize (BB i pf).
                 simpl in BB.
                 specialize (DD (x0 + n0)%nat).
                 rewrite Rabs_le_between.
                 clear H11.
                 rewrite Rabs_le_between in BB.
                 apply Rplus_le_compat_r with 
                     (r :=
                        RMseq (fun n : nat => α (n + nk)%nat) 
                              (fun _ : nat => gamma * (C0 * (gamma + eps) ^ k))
                              (C0 * (gamma + eps) ^ k) 
                              (x0 + x1 + n0)%nat) in AA.
                 ring_simplify in AA.
                 rewrite Rabs_le_between in AA.
                 replace (x0 + n0 + x1)%nat with (x0 + x1 + n0)%nat in DD by lia.
                 rewrite vecrvminus_unfold.
                 unfold const.
                 lra.
              }
               assert (ps_P (event_inter A (inter_of_collection (fun t => B (t + x0)%nat))) <= ps_P E).
               {
                 apply ps_sub.
                 intros ? [? ?].
                 apply H10.
                 split; trivial.
                 split.
                 intros.
                 specialize (H12 (n0 - x0)%nat).
                 unfold proj1_sig in H12.
                 replace (n0 - x0 + x0)%nat with n0 in H12 by lia.
                 apply H12.
                 unfold D.
                 apply H3.
               }
               assert (ps_P A >= 1 - INR k * (1 - P)).
               {
                 unfold A.
                 apply H9.
               }
               assert (ps_P  (inter_of_collection (fun t => B (t + x0)%nat)) > P).
               {
                 unfold B.
                 specialize (H7 x0).
                 cut_to H7; try lia.
                 erewrite ps_proper; try eapply H7.
                 symmetry.
                 rewrite <- inter_of_collection_nested_plus.
                 apply inter_of_collection_proper; intros ?.
                 apply inter_of_collection_proper; intros ?.                 
                 replace (x0 + (a0 + a))%nat with (a + x0 +a0)%nat by lia.
                 reflexivity.
               }
               generalize (ps_union prts A (inter_of_collection (fun t => B (t + x0)%nat))); intros.
               generalize (ps_le1 prts (event_union A (inter_of_collection (fun t : nat => B (t + x0)%nat)))); intros.
               assert (ps_P E >= (1 - INR k * (1 - P)) + P - 1) by lra.
               assert (1 - INR k * (1 - P) + P - 1 =  1 - INR (S k) * (1 - P)).
               {
                 rewrite S_INR.
                 ring.
               }
               rewrite H17 in H16.
               unfold E in H16.
               erewrite ps_proper; try eapply H16.
               intros ?.
               simpl.
               rewrite Sup_seq_ext with
                   (v := (fun n0 : nat => rvmaxabs (vecrvminus (x (x0 + x1 + nk + n0)%nat) (const xstar)) x2 )).
               reflexivity.
               intros.
               now replace (n0 + (x0 + x1 + nk))%nat with (x0 + x1 + nk + n0)%nat by lia.
            -- intros ? ?.
               replace (S n0 + nk)%nat with (S (n0 + nk))%nat by lia.
               now rewrite xrel.
            -- assert (event_equiv
                         (inter_of_collection
                            (fun n0 : nat =>
                               event_le dom (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar))) 
                                        (C0 * (gamma + eps) ^ k)))
                         (event_Rbar_le
                            (fun omega : Ts =>
                               Sup_seq (fun n0 : nat => rvmaxabs (vecrvminus (x (n0 + nk)%nat)
                                                                             (const xstar)) omega))
                            (C0 * (gamma + eps) ^ k))).
               {
                 intros ?.
                 simpl.
                 rewrite <- sup_le_bound.
                 now simpl.
               }
               rewrite H10.
               apply IHk.
          * now apply seq_sum_shift.
          * setoid_rewrite Nat.add_comm.
            rewrite ex_series_incr_n in exser_asq.
            apply exser_asq.
        + now apply seq_sum_shift.
    Qed.
    
    Lemma Sup_seq_incr (f : nat -> R) (n1 n2 : nat) :
      (n1 >= n2)%nat ->
      Rbar_le (Sup_seq (fun n => f (n + n1)%nat)) (Sup_seq (fun n => f (n + n2)%nat)).
    Proof.
      intros.
      do 2 rewrite Rbar_sup_eq_lub.
      unfold Rbar_lub, proj1_sig.
      match_destr; match_destr.
      unfold Rbar_is_lub, Rbar_is_upper_bound in *.
      destruct r; destruct r0.
      apply H1.
      intros.
      apply H2.
      destruct H4.
      exists (x2 + (n1 - n2))%nat.
      now replace (x2 + (n1 - n2) + n2)%nat with (x2 + n1)%nat by lia.
    Qed.

    Lemma up_pow_ln (c1 b : posreal) :
      b < 1 ->
      c1 < 1 ->
      c1 >= b ^ Z.to_nat (up ((ln c1)/(ln b))).
    Proof.
      intros.
      generalize (cond_pos b); intro bpos.
      generalize (cond_pos c1); intro c1pos.      
      assert (ln b <> 0).
      {
        apply Rlt_not_eq.
        apply ln_lt_0; lra.
      }
      assert (pos c1 = Rpower b ((ln c1)/(ln b))).
      {
        unfold Rpower.
        replace (ln c1 / ln b * ln b) with (ln c1).
        - now rewrite exp_ln.
        - field_simplify; trivial.
      }
      rewrite H2 at 1.
      rewrite <- Rpower_pow; try apply cond_pos.
      unfold Rpower.
      apply Rle_ge.
      apply exp_increasing_le.
      rewrite INR_up_pos.
      - field_simplify; trivial.
        + apply Rmult_le_reg_r with (r := - /ln b).
          * rewrite <- Ropp_0.
            apply Ropp_lt_contravar.
            apply Rinv_lt_0_compat.
            now apply ln_lt_0.
          * field_simplify; trivial.
            apply Ropp_le_cancel.
            field_simplify; trivial.
            left.
            apply archimed.
      - replace (ln c1 / ln b) with ((- ln c1) / (- ln b)).
        + apply Rle_ge.
          apply Rdiv_le_0_compat.
          * rewrite <- Ropp_0.
            apply Ropp_le_contravar.
            apply ln_le_0; lra.
          * rewrite <- Ropp_0.
            apply Ropp_lt_contravar.
            apply ln_lt_0; lra.
        + replace (- ln c1) with ((-1)*ln c1) by lra.
          replace (- ln b) with ((-1)*ln b) by lra.
          now field_simplify.
    Qed.

    Lemma sa_sigma_is_ELimInf_seq (f : nat -> Ts -> Rbar) (c:Rbar)
          {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} :
      sa_sigma _ (fun omega => is_ELimInf_seq (fun n => f n omega) c).
    Proof.
      assert (pre_event_equiv
                (fun omega => is_ELimInf_seq (fun n => f n omega) c)
                (fun omega => ELimInf_seq (fun n => f n omega) = c)).
      {
        intros ?.
        unfold ELimInf_seq, proj1_sig.
        match_destr.
        split; intros.
        - apply is_ELimInf_seq_unique in i.
          apply is_ELimInf_seq_unique in H.
          now rewrite <- i, <- H.
        - now rewrite <- H.
      }
      rewrite H.
      apply Rbar_sa_le_pt.
      intros.
      apply Rbar_lim_inf_measurable.
      typeclasses eauto.
   Qed.

    Lemma sa_sigma_is_ELimSup_seq (f : nat -> Ts -> Rbar) (c:Rbar)
          {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} :
      sa_sigma _ (fun omega => is_ELimSup_seq (fun n => f n omega) c).
    Proof.
      assert (pre_event_equiv
                (fun omega => is_ELimSup_seq (fun n => f n omega) c)
                (fun omega => ELimSup_seq (fun n => f n omega) = c)).
      {
        intros ?.
        unfold ELimSup_seq, proj1_sig.
        match_destr.
        split; intros.
        - apply is_ELimSup_seq_unique in i.
          apply is_ELimSup_seq_unique in H.
          now rewrite <- i, <- H.
        - now rewrite <- H.
      }
      rewrite H.
      apply Rbar_sa_le_pt.
      intros.
      apply Rbar_lim_sup_measurable.
      typeclasses eauto.
   Qed.

    Lemma sa_sigma_is_Elim_seq (f : nat -> Ts -> Rbar) (c:Rbar)
          {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} :
      sa_sigma _ (fun omega => is_Elim_seq (fun n => f n omega) c).
    Proof.
      assert (pre_event_equiv
                (fun omega : Ts => is_Elim_seq (fun n : nat => f n omega) c)
                (pre_event_inter
                   (fun omega : Ts => is_ELimInf_seq (fun n : nat => f n omega) c)
                   (fun omega : Ts => is_ELimSup_seq (fun n : nat => f n omega) c))).
      {
        intros ?.
        unfold pre_event_inter.
        split; intros.
        - split.
          + now apply is_Elim_LimInf_seq.
          + now apply is_Elim_LimSup_seq.
        - destruct H.
          now apply is_ELimSup_LimInf_lim_seq .
      }
      rewrite H.
      apply sa_inter.
      - now apply sa_sigma_is_ELimInf_seq.
      - now apply sa_sigma_is_ELimSup_seq.
   Qed.


    Lemma lim_ps_complement {prts : ProbSpace dom} (E : nat -> event dom) (p : R) :
      0 <= p <= 1 ->
      is_lim_seq (fun n => ps_P (E n)) p -> 
      is_lim_seq (fun n => ps_P (event_complement (E n))) (1-p).
    Proof.
      intros.
      apply is_lim_seq_spec in H0; unfold is_lim_seq' in H0.
      apply is_lim_seq_spec; unfold is_lim_seq'.
      intros.
      destruct (H0 eps).
      exists x.
      intros.
      specialize (H1 n H2).
      rewrite ps_complement.
      eapply Rle_lt_trans.
      shelve.
      apply H1.
      Unshelve.
      right.
      rewrite <- Rabs_Ropp.
      f_equal.
      ring.
    Qed.

    Lemma lim_Rbar_le_complement {prts : ProbSpace dom} (f : nat -> Ts -> Rbar) (C : Rbar) (p : R) 
          { rv: forall n1, RandomVariable dom Rbar_borel_sa (f n1)} :
      0 <= p <= 1 ->
      is_lim_seq (fun n1 => ps_P ( event_Rbar_le (f n1) C)) p ->
      is_lim_seq (fun n1 => ps_P ( event_Rbar_gt (f n1) C)) (1-p).
    Proof.
      intros.
      apply lim_ps_complement in H0; trivial.
      eapply (is_lim_seq_ext _ _ _ _ H0).
      Unshelve.
      intros.
      simpl.
      apply ps_proper.
      intros ?.
      unfold event_complement, pre_event_complement, event_Rbar_le, event_Rbar_gt, Rbar_gt, proj1_sig.
      split; intros.
      - now apply Rbar_not_le_lt.
      - now apply Rbar_lt_not_le.
    Qed.

    Lemma stochastic_convergence_16 {n} (C0: posreal) (α : nat -> R) (C : R) (w x : nat -> Ts -> vector R (S n)) (xstar : vector R (S n))
          (F : (vector R (S n)) -> (vector R (S n)))
          {prts: ProbSpace dom}                              
          (rx : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (x n0))
          (rw : forall n0, RandomVariable dom (Rvector_borel_sa (S n)) (w n0))
          (isfew : forall n0, vector_IsFiniteExpectation prts (w n0))
          (srw : forall n0, FiniteRangeFunction  (w n0))
          (rvsup : forall nk, RandomVariable dom Rbar_borel_sa
                    (fun (omega : Ts) =>
                       Sup_seq (fun (n0 : nat) =>
                                  (rvmaxabs (vecrvminus (x (nk + n0)%nat) (const xstar))) omega))) :
      0 <= C ->
      0 <= gamma < 1 ->
      (*      (forall n, 0 <= α n <= 1) ->       *)
      (forall n, 0 <= α n < 1) ->  
      is_lim_seq α 0 ->
      is_lim_seq (sum_n α) p_infty ->
      ex_series (fun n => (α n)^2) ->
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
         rv_eq (vector_FiniteConditionalExpectation
                  prts (filtration_history_sa_sub 
                          (cod := Rvector_borel_sa (S n)) 
                          (@L2_convergent_x (S n)
                                            (fun k => α (k + nk)%nat) 
                                            (const Rvector_zero) Ts
                                            (const Rvector_zero) 
                                            (fun k => w (k + nk)%nat))
                          n0) 
                  (w (n0 + nk)%nat))
         (const Rvector_zero)) ->
      almost prts (fun omega => is_lim_seq (fun n =>
                                         (rvmaxabs (vecrvminus (x n) (const xstar))) omega)
                                      0).
    Proof.
      intros.
      pose (eps := (1-gamma)/2).
      assert (gamma + eps < 1).
      {
        unfold eps.
        field_simplify.
        apply Rmult_lt_reg_r with (r := 2); lra.
     }
      generalize (sa_sigma_is_Elim_seq (fun n => (rvmaxabs (vecrvminus (x n) (const xstar)))) 0); intros.
      assert (forall (eps0:posreal),
                 forall (P:R), 
                   0<P<1 ->
                   exists (nk:nat),
                     ps_P 
                       (event_Rbar_le
                          (fun (omega : Ts) =>
                             Sup_seq (fun (n0 : nat) =>
                                        (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar))) omega))
                          eps0) >= P).
      {
        intros.
        destruct (Rlt_dec eps0 C0).
        - pose (k := Z.to_nat(up (ln (eps0 / C0) / ln (gamma + eps)))).
          pose (P0 := 1 - (1 - P)/(INR k)).
          assert (eps > 0) by (unfold eps; lra).
          assert (0 < (ln (eps0 / C0) / ln (gamma + eps))).
          {
            unfold Rdiv.
            apply Rmult_lt_reg_r with (r := - ln(gamma + eps)).
            - apply Ropp_lt_cancel.
              ring_simplify.
              apply ln_lt_0.
              lra.
            - rewrite Rmult_0_l.
              rewrite Rmult_assoc.
              replace (/ ln (gamma + eps) * - ln (gamma + eps)) with (-1).
              + apply Ropp_lt_cancel.
                ring_simplify.
                apply ln_lt_0.
                split.
                * apply Rmult_lt_0_compat.
                  -- apply cond_pos.
                  -- apply Rinv_0_lt_compat, cond_pos.
                * apply Rmult_lt_reg_r with (r := C0).
                  -- apply cond_pos.
                  -- rewrite Rmult_assoc.
                     rewrite <- Rinv_l_sym.
                     ++ rewrite Rmult_1_r.
                        rewrite Rmult_1_l.
                        lra.
                     ++ apply Rgt_not_eq, cond_pos.
              + ring_simplify.
                replace (- / ln (gamma + eps)) with ((-1)*(/ ln (gamma + eps))) by lra.
                rewrite Rmult_assoc.
                rewrite <- Rinv_l_sym.
                * lra.
                * apply Rlt_not_eq.
                  apply ln_lt_0.
                  lra.
          }
          assert (INR k >= 1).
          {
            unfold k.
            rewrite INR_up_pos; try lra.
            apply up_pos in H15.
            assert  (up (ln (eps0 / C0) / ln (gamma + eps)) >= 1)%Z by lia.
            now apply IZR_ge in H16.            
          }
          assert (P0 > 0).
          {
            unfold P0.
            apply Rmult_gt_reg_l with (r := INR k); try lra.
            rewrite Rmult_0_r.
            field_simplify.
            lra.
            apply Rgt_not_eq.
            lra.
          }
          assert (P0 < 1).
          {
            unfold P0.
            apply Rmult_gt_reg_l with (r := INR k); try lra.
            field_simplify.
            lra.
            apply Rgt_not_eq.
            lra.
          }
          assert (exists (nk:nat),
                     ps_P 
                       (event_Rbar_le
                          (fun (omega : Ts) =>
                             Sup_seq (fun (n0 : nat) =>
                                        (rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar))) omega))
                          (C0 * (gamma + eps)^k)) >= 1 - (INR k) * (1 - P0)).
          {
            apply (Induction_I1_17 (mkposreal _ H14) (mkposreal _ H17) C0 α C w) with (F := F) (rw := rw) (srw := srw) (isfew := isfew); trivial.
          }
          assert (eps0 >= (C0 * (gamma + eps)^k)).
          {
            assert (eps0/C0 >= (gamma + eps) ^ k).
            {
              unfold k.
              assert (0 < eps0 / C0) by
                  (apply Rdiv_lt_0_compat; apply cond_pos).
              assert (0 < gamma + eps) by
                  (apply Rlt_le_trans with (r2 := eps); lra).
              apply (up_pow_ln (mkposreal _ H20) (mkposreal _ H21)).
              - simpl; lra.
              - simpl.
                unfold Rdiv.
                apply Rmult_lt_reg_r with (r := C0).
                + apply cond_pos.
                + rewrite Rmult_assoc.
                  rewrite <- Rinv_l_sym.
                  * lra.
                  * apply Rgt_not_eq, cond_pos.
             }
            apply Rmult_ge_compat_r with (r := C0) in H20.
            unfold Rdiv in H20.
            rewrite Rmult_assoc in H20.
            rewrite <- Rinv_l_sym in H20.
            - lra.
            - apply Rgt_not_eq, cond_pos.
            - left; apply cond_pos.
          }
          destruct H19.
          assert (1 - INR k * (1 - P0) >= P).
          {
            unfold P0.
            field_simplify; lra.
          }
          exists x0.
          apply Rge_trans with (r2 :=  1 - INR k * (1 - P0) ); trivial.
          eapply Rge_trans.
          shelve.
          apply H19.
          Unshelve.
          apply Rle_ge.
          apply ps_sub.
          intros ? ?.
          simpl; simpl in H22.
          apply Rbar_le_trans with (y := (C0 * (gamma + eps) ^ k)); trivial.
          simpl; lra.
        - exists (0%nat).
          assert (event_equiv
                     (event_Rbar_le
                        (fun omega : Ts =>
                           Sup_seq (fun n1 : nat => rvmaxabs (vecrvminus (x (n1 + 0)%nat) 
                                                                         (const xstar)) omega)) eps0)
                      Ω).
          {
            intros ?.
            simpl.
            unfold pre_Ω.
            split; intros; trivial.
            replace (Finite eps0) with (Sup_seq (fun n => eps0)).
            apply Sup_seq_le.
            - intros.
              assert (C0 <= eps0) by lra.
              replace (n1 + 0)%nat with n1 by lia.
              apply Rbar_le_trans with (y := C0); now simpl.
            - apply Sup_seq_const.
          }
          rewrite H14.
          rewrite ps_all.
          lra.
        }
      assert (forall (eps:posreal),
                 is_lim_seq ( fun nk => 
                                ps_P
                                  (event_Rbar_le
                                     (fun omega : Ts =>
                                        Sup_seq (fun n0 : nat => rvmaxabs 
                                                                   (vecrvminus (x (n0 + nk)%nat)
                                                                               (const xstar)) omega)) 
                                     eps)) 1).
      {
        intros.
        specialize (H13 eps0).
        apply is_lim_seq_spec.
        unfold is_lim_seq'.
        intros.
        destruct (Rle_dec eps1 1).
        - specialize (H13 (1 - eps1/2)).
          assert (0 < eps1) by apply cond_pos.
          cut_to H13; try lra.
          destruct H13.
          exists x0.
          intros.
          rewrite Rabs_minus_sym.
          rewrite Rabs_right.
          + assert (ps_P
                      (event_Rbar_le
                         (fun omega : Ts =>
                            Sup_seq (fun n0 : nat => rvmaxabs (vecrvminus (x (n0 + x0)%nat) 
                                                                          (const xstar)) omega))
                         eps0) <= 
                    ps_P
                      (event_Rbar_le
                         (fun omega : Ts =>
                            Sup_seq (fun n1 : nat => rvmaxabs (vecrvminus (x (n1 + n0)%nat) 
                                                                          (const xstar)) omega)) eps0)).
            {
              apply ps_sub.
              intros ? ?.
              simpl; simpl in H16.
              eapply Rbar_le_trans.
              shelve.
              apply H16.
              Unshelve.
              apply (Sup_seq_incr (fun n1 : nat => rvmaxabs (vecrvminus (x n1) (const xstar)) x1)).
              lia.
            }
            lra.
          + assert (ps_P
                      (event_Rbar_le
                         (fun omega : Ts =>
                            Sup_seq (fun n1 : nat => rvmaxabs (vecrvminus (x (n1 + n0)%nat) 
                                                                          (const xstar)) omega)) eps0) 
                    <= 1) by  apply ps_le1.
            lra.
       - assert (eps1 > 1) by lra.
         exists (0%nat).
         intros.
         rewrite Rabs_minus_sym.
         rewrite Rabs_right.
         + assert (0 <= ps_P
                          (event_Rbar_le
                             (fun omega : Ts =>
                                Sup_seq (fun n2 : nat => rvmaxabs (vecrvminus (x (n2 + n1)%nat) (const xstar)) omega)) eps0)) by apply ps_pos.
           lra.
          + assert (ps_P
                      (event_Rbar_le
                         (fun omega : Ts =>
                            Sup_seq (fun n2 : nat => rvmaxabs (vecrvminus (x (n2 + n1)%nat) 
                                                                          (const xstar)) omega)) eps0) 
                    <= 1) by  apply ps_le1.
            lra.
      }
      assert (forall (eps:posreal),
                  is_lim_seq
          (fun nk : nat =>
           ps_P
             (event_Rbar_gt
                (fun omega : Ts =>
                 Sup_seq (fun n0 : nat => rvmaxabs (vecrvminus (x (n0 + nk)%nat) (const xstar)) omega))
                eps)) 0).
      {
        intros.
        replace (0) with (1 - 1) by lra.
        apply lim_Rbar_le_complement; try lra.
        apply H14.
      }
      assert (forall n0,  RandomVariable dom Rbar_borel_sa
                                        (fun x0 : Ts =>
                                           Sup_seq (fun m : nat => Rabs (rvmaxabs (vecrvminus (x (n0 + m)%nat) (const xstar)) x0)))) by typeclasses eauto.

      apply conv_prob_sup_0_as with (rv2 := H16); try typeclasses eauto; trivial.
      intros.
      apply is_lim_seq_ext with 
          (u :=
             (fun nk : nat =>
                ps_P
                  (event_Rbar_gt
                     (fun omega : Ts =>
                        Sup_seq (fun n0 : nat => rvmaxabs (vecrvminus (x (n0 + nk)%nat) 
                                                                      (const xstar)) omega))
                     eps0))).
      - intros.
        apply ps_proper.
        symmetry.
        intros ?.
        unfold proj1_sig, event_Rbar_gt, Rbar_gt.
        rewrite Sup_seq_ext with (v := (fun n1 : nat => rvmaxabs (vecrvminus (x (n1 + n0)%nat) (const xstar)) x0)); try tauto.
        intros.
        rewrite Rabs_right.
        now replace (n1 + n0)%nat with (n0 + n1)%nat by lia.
        apply Rle_ge.
        apply rvmaxabs_pos.
      - apply H15.
    Qed.

  End qlearn5.
