Require Import Reals Lra.

Local Open Scope R.

Lemma exp_gt1 (x : R) : 0<x -> 1 < exp x.
Proof.
  intro xgt.
  generalize (exp_ineq1 x xgt); intros.
  apply Rlt_trans with (r2 := 1+x); lra.
Qed.

Lemma exp_ineq (x : R) : 1 + x <= exp x.  
  generalize (exp_pos); intros.
  generalize (MVT_cor2 (fun x=> exp x - (x + 1)) (fun x => exp x - 1)); intros.
  destruct (Rlt_dec 0 x).
  - left; now apply exp_ineq1.
  - destruct (Rlt_dec x 0).
    + specialize (H0 x 0 r).
      assert (forall c : R,
                 x <= c <= 0 -> 
                 derivable_pt_lim (fun x : R => exp x - (x + 1)) c (exp c - 1)); intros.
      * apply derivable_pt_lim_minus.
        -- apply derivable_pt_lim_exp.
        -- replace (1) with (1 + 0) at 1 by lra.
           apply derivable_pt_lim_plus.
           ++ apply derivable_pt_lim_id.
           ++ apply derivable_pt_lim_const.
     * specialize (H0 H1).
       destruct H0 as [c [? ?]].
       rewrite exp_0 in H0; ring_simplify in H0.
       apply Rge_le; apply Rminus_ge.
       apply Ropp_eq_compat in H0; ring_simplify in H0.
       ring_simplify; rewrite H0; left.
       replace (x * exp c - x) with ((-x)*(1-exp c)) by lra.
       apply Rmult_lt_0_compat.
       -- lra.
       -- destruct H2.
          apply Rgt_minus.
          replace (c) with (- - c) by lra.
          rewrite exp_Ropp.
          replace (1) with (/ 1) by lra.
          apply  Rinv_1_lt_contravar; [lra |].
          apply exp_gt1; lra.
    + assert (x = 0) by lra.
      subst.
      rewrite exp_0.
      lra.
  Qed.
