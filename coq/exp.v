Require Import Reals Lra.

Local Open Scope R.

Lemma exp_ineq1 : forall x : R, x <> 0 -> 1 + x < exp x.
Proof.
  assert (Hd : forall c : R,
             derivable_pt_lim (fun x : R => exp x - (x + 1)) c (exp c - 1)).
  intros.
  apply derivable_pt_lim_minus; [apply derivable_pt_lim_exp | ].
  replace (1) with (1 + 0) at 1 by lra.
  apply derivable_pt_lim_plus;
    [apply derivable_pt_lim_id | apply derivable_pt_lim_const].
  intros x xdz; destruct (Rtotal_order x 0)  as [xlz|[xez|xgz]].
  - destruct (MVT_cor2 _ _ x 0 xlz (fun c _ => Hd c)) as [c [HH1 HH2]].
    rewrite exp_0 in HH1.
    assert (H1 : 0 < x * exp c - x); [| lra].
    assert (H2 : x * exp 0  < x * exp c); [| rewrite exp_0 in H2; lra].
    apply Rmult_lt_gt_compat_neg_l; auto.
    now apply exp_increasing.
  - now case xdz.
  - destruct (MVT_cor2 _ _ 0 x xgz (fun c _ => Hd c)) as [c [HH1 HH2]].
    rewrite exp_0 in HH1.
    assert (H1 : 0 < x * exp c - x); [| lra].
    assert (H2 : x * exp 0  < x * exp c); [| rewrite exp_0 in H2; lra].
    apply Rmult_lt_compat_l; auto.
    now apply exp_increasing.
Qed.

Lemma exp_ineq1_le (x : R) : 1 + x <= exp x.
Proof.
  destruct (Req_EM_T x 0) as [xeq|?].
  - rewrite xeq, exp_0; lra.
  - left.
    now apply exp_ineq1.
Qed.
