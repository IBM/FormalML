Require Import Reals RealAdd CoquelicotAdd Coquelicot.Coquelicot.
Require Import utils.Utils FunctionsToReal Morphisms.
Require Import Almost.
Require Import SigmaAlgebras ProbSpace infprod.
Require Import Lra Lia.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R.

Section uniform.
  
Context {Ts : Type} {dom: SigmaAlgebra Ts} {prts: ProbSpace dom}.

Definition is_lim_seq'_uniform_fun (u : nat -> Ts -> R) (l : Ts -> R) :=
   forall eps : posreal, 
     eventually (fun n => forall (x:Ts), Rabs (u n x - l x) < eps).

Lemma is_lim_seq'_uniform_is_lim (u : nat -> Ts -> R) (l : Ts -> R) :
  is_lim_seq'_uniform_fun u l ->
  forall (x : Ts), is_lim_seq (fun n => u n x) (l x).
Proof.
  intros.
  apply is_lim_seq_spec.
  intros eps.
  specialize (H eps).
  revert H.
  apply eventually_impl.
  now apply all_eventually; intros ??.
Qed.

Definition is_lim_seq'_uniform_almost (u : nat -> Ts -> R) (l : Ts -> R) :=
   forall eps : posreal, 
     eventually (fun n => almostR2 prts Rlt (rvabs (rvminus (u n) l)) (const eps)).

Global Instance is_lim_seq'_uniform_almost_ext : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> pointwise_relation _ eq ==> iff) is_lim_seq'_uniform_almost.
  Proof.

    cut ( Proper (pointwise_relation _ (pointwise_relation _ eq) ==> pointwise_relation _ eq ==> impl) is_lim_seq'_uniform_almost).
    {
      intros HH ??????.
      split; apply HH; trivial; now symmetry.
    }
    intros ?? eqq1 ?? eqq2 islim.
    unfold is_lim_seq'_uniform_almost in *.
    intros eps.
    generalize (islim eps).
    apply eventually_impl.
    apply all_eventually; intros ?.
    apply almost_impl; apply all_almost; intros ??.
    rv_unfold.
    now rewrite <- eqq1, <- eqq2.
  Qed.

Lemma is_lim_seq'_uniform_is_lim_almost (u : nat -> Ts -> R) (l : Ts -> R) :
  is_lim_seq'_uniform_almost u l ->
  almost prts (fun x => is_lim_seq (fun n => u n x) (l x)).
Proof.
  unfold is_lim_seq'_uniform_almost.
  intros.
  assert (forall eps : posreal,
             almost prts (fun (x : Ts) => eventually (fun n =>
                                                        (rvabs (rvminus (u n) l) x) < eps))).
  {
    intros.
    specialize (H eps).
    unfold const in H.
    apply almost_eventually.
    revert H.
    apply eventually_impl.
    apply all_eventually; intros ?.
    apply almost_impl.
    now apply all_almost; intros ??.
  }
  assert (forall N,
             almost prts (fun x : Ts => eventually (fun n : nat => rvabs (rvminus (u n) l) x < / INR (S N)))).
  {
    intros.
    assert (0 < / INR (S N)).
    {
      apply Rinv_0_lt_compat.
      apply lt_0_INR.
      lia.
   }
   now specialize (H0 (mkposreal _ H1)).
  }
  apply almost_forall in H1.
  revert H1; apply almost_impl.
  apply all_almost; intros ??.
  apply is_lim_seq_spec.
  intros ?.
  assert (exists N,
             / INR (S N) < eps).
  {
    generalize (archimed_cor1 eps (cond_pos eps)); intros.
    destruct H2 as [N [??]].
    exists (N-1)%nat.
    now replace (S (N - 1)) with N by lia.
  }
  destruct H2 as [N ?].
  specialize (H1 N).
  revert H1.
  apply eventually_impl.
  apply all_eventually.
  intros.
  eapply Rlt_trans; cycle 1.
  apply H2.
  unfold rvabs, rvminus, rvplus, rvopp, rvscale in H1.
  eapply Rle_lt_trans; cycle 1.
  apply H1.
  right.
  f_equal.
  lra.
Qed.

Lemma is_lim_seq'_uniform_ex_series_almost (u : nat -> Ts -> R) (l : Ts -> R) :
  is_lim_seq'_uniform_almost (fun n ω => sum_n (fun n0 => u n0 ω) n) l ->
  almost prts (fun x => ex_series (fun n => u n x)).
Proof.
  intros.
  apply is_lim_seq'_uniform_is_lim_almost in H.
  revert H.
  apply almost_impl.
  apply all_almost; intros ??.
  exists (l x).
  now rewrite series_seq.
Qed.

Lemma uniform_lim_all_almost (u : nat -> Ts -> R) (l : Ts -> R) :
  is_lim_seq'_uniform_fun u l ->
  is_lim_seq'_uniform_almost u l.
Proof.
  intros ??.
  destruct (H eps).
  exists x; intros.
  apply all_almost; intros.
  rv_unfold'.
  now apply H0.
Qed.

Definition is_lim_seq'_uniform_constlim {Ts} (u : nat -> Ts -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, 
      eventually (fun n => forall (x:Ts), Rabs (u n x - l) < eps)
    | p_infty => forall M : R, eventually (fun n => forall (x:Ts), M < u n x)
    | m_infty => forall M : R, eventually (fun n => forall (x:Ts), u n x < M)
  end.

Definition is_lim_seq'_uniform_fun_Rbar {Ts} (u : nat -> Ts -> R) (l : Ts -> Rbar) :=
   forall eps : posreal, 
     eventually (fun n => forall (x:Ts), 
                     match (l x) with
                     | Finite l' => Rabs (u n x - l') < eps
                     | p_infty => 1/eps < u n x
                     | m_infty => u n x < - 1/eps
                     end).

Lemma is_lim_seq'_uniform_Rbar_is_lim (u : nat -> Ts -> R) (l : Ts -> Rbar) :
  is_lim_seq'_uniform_fun_Rbar u l ->
  forall (x : Ts), is_lim_seq (fun n => u n x) (l x).
Proof.
  intros.
  apply is_lim_seq_spec.
  unfold is_lim_seq'.
  match_case; intros.
  - specialize (H eps).
    revert H.
    apply eventually_impl.
    apply all_eventually; intros ??.
    specialize (H x).
    now rewrite H0 in H.
  - pose (eps := / Rmax M 1).
    assert (0 < eps).
    {
      unfold eps.
      apply Rinv_0_lt_compat.
      generalize (Rmax_r M 1); intros.
      lra.
   }
   generalize (H (mkposreal _ H1)).
   apply eventually_impl.
   apply all_eventually; intros ??.
   specialize (H2 x).
   rewrite H0 in H2.
   simpl in H2.
   eapply Rle_lt_trans; cycle 1.
   apply H2.
   unfold eps.
   unfold Rdiv.
   rewrite Rinv_inv, Rmult_1_l.
   apply Rmax_l.
 - pose (eps := / (- (Rmin M (-1)))).
   assert (0 < eps).
   {
     unfold eps.
     apply Rinv_0_lt_compat.
     generalize (Rmin_r M (-1)); intros.
     lra.
   }
   generalize (H (mkposreal _ H1)).
   apply eventually_impl.
   apply all_eventually; intros ??.
   specialize (H2 x).
   rewrite H0 in H2.
   simpl in H2.
   eapply Rlt_le_trans.
   apply H2.
   unfold eps.
   unfold Rdiv.
   rewrite Rinv_inv.
   ring_simplify.
   apply Rmin_l.
 Qed.

Lemma uniform_converge_sq (α : nat -> Ts -> R) :
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
  is_lim_seq'_uniform_almost (fun n => rvsqr (α n)) (const 0) ->
  eventually (fun n => almostR2 prts Rle  (α n) (const 1)).
Proof.
  intros.
  assert (0 < 1) by lra.
  specialize (H0 (mkposreal _ H1)).
  destruct H0 as [N ?].
  exists N.
  intros.
  specialize (H0 n H2).
  specialize (H n).
  revert H; apply almost_impl.
  revert H0; apply almost_impl.
  apply all_almost; unfold impl; intros.
  unfold const in *.
  unfold rvsqr, rvabs in H.
  rewrite rvminus_unfold in H.
  simpl in H.
  rewrite Rminus_0_r, <- Rabs_sqr in H.
  replace 1 with (Rsqr 1) in H by (unfold Rsqr; lra).
  apply Rsqr_lt_abs_0 in H.
  do 2 rewrite Rabs_right in H; lra.
Qed.    

Lemma uniform_converge_sum_sq (α : nat -> Ts -> R) :
  let A := fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω)) in
  is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (α k) ω) n) A ->
  is_lim_seq'_uniform_almost (fun n => rvsqr (α n)) (const 0).
Proof.
  unfold is_lim_seq'_uniform_almost; intros.
  assert (0 < eps/2).
  {
    generalize (cond_pos eps); intros; lra.
  }
  specialize (H (mkposreal _ H0)).
  destruct H as [N ?].
  exists (S N).
  intros.
  assert (N <= (n-1))%nat by lia.
  generalize (H _ H2); intros.
  assert (N <= n)%nat by lia.
  specialize (H _ H4).
  revert H; apply almost_impl.
  revert H3; apply almost_impl.
  apply all_almost; unfold impl; intros.
  simpl in H; simpl in H3.
  rv_unfold'_in_star.
  rewrite Rminus_0_r, <- Rabs_sqr.
  pose (A := Lim_seq (sum_n (fun k => rvsqr (α k) x))).
  pose (B := fun n => sum_n (fun k : nat => (α k x)²) n).
  generalize (Rabs_triang (B n - A) (A - B (n-1)%nat)); intros.
  replace  (Rabs (B n - A + (A - B (n-1)%nat))) with (α n x)² in H5.
  - eapply Rle_lt_trans.
    apply H5.
    rewrite Rabs_minus_sym in H.
    unfold A, B, rvsqr.
    lra.
  - replace (n) with (S (n-1)) by lia.
    replace (S (n-1) - 1)%nat with (n-1)%nat by lia.
    unfold B.
    rewrite sum_Sn.
    unfold plus; simpl.
    replace (S (n-1)) with (n) by lia.
    rewrite Rabs_sqr at 1.
    f_equal.
    lra.
 Qed.

Lemma uniform_converge_sum_sq_le_1 (α : nat -> Ts -> R) :
  (forall (n:nat), almostR2 prts Rle (const 0) (α n)) -> 
  let A := fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω)) in
  is_lim_seq'_uniform_almost (fun n => fun ω => sum_n (fun k => rvsqr (α k) ω) n) A ->
  eventually (fun n => almostR2 prts Rle  (α n) (const 1)).
Proof.
  intros.
  apply uniform_converge_sq; trivial.
  apply uniform_converge_sum_sq.
  apply H0.
Qed.

Lemma uniform_converge_sum_sq_tails (α : nat -> Ts -> R) : 
  let A := fun ω => Lim_seq (sum_n (fun k => rvsqr (α k) ω)) in
  is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (α k) ω) n) A ->
  forall (eps : posreal),
    eventually (fun n => almostR2 prts Rbar_le (fun ω : Ts => Lim_seq (sum_n (fun n0 : nat => (α (S n + n0)%nat ω)²))) (const eps)).
Proof.
  intros A uniform eps.
  assert (ex_ser :   almost prts (fun ω => ex_series (fun k => rvsqr (α k) ω))).
  {
    now apply is_lim_seq'_uniform_ex_series_almost with (l := A).
  }
  specialize (uniform eps).
  revert uniform.
  apply eventually_impl.
  apply all_eventually; intros ?.
  apply almost_impl.
  revert ex_ser; apply almost_impl.
  apply all_almost; intros ???.
  rv_unfold'_in_star.
  generalize H; intros HH.
  destruct H.
  rewrite series_seq in H.
  apply is_lim_seq_unique in H.
  assert (isfin: is_finite  (Lim_seq (sum_n (fun n0 : nat => (α (S x + n0)%nat x0)²)))).
  {
    rewrite ex_series_incr_n with (n := S x) in HH.
    rewrite <- ex_finite_lim_series in HH.
    destruct HH.
    apply is_lim_seq_unique in H1.
    now rewrite H1.
  }
  assert (limeq1: Lim_seq (sum_n (fun k : nat => (α k x0)²)) =
            Rbar_plus (sum_n (fun k : nat => (α k x0)²) x)
              (Lim_seq (sum_n (fun n0 : nat => (α (S x + n0)%nat x0)²)))).
  {
    assert (0 <= x)%nat by lia.
    generalize (sum_n_m_Series (fun k : nat => (α k x0)²) 0%nat x H1 HH); intros.
    unfold Series in H2.
    rewrite <- isfin.
    simpl in H2.
    simpl.
    unfold sum_n in *.
    rewrite H2, H, Rbar_finite_eq.
    simpl; lra.
  }
  assert (limeq2: Lim_seq (sum_n (fun n0 : nat => (α (S x + n0)%nat x0)²)) = 
            Rbar_minus (A x0) (sum_n (fun k : nat => (α k x0)²) x)).
  {
    unfold A.
    rewrite limeq1, <- isfin; simpl.
    rewrite Rbar_finite_eq.
    lra.
  }
  rewrite limeq2.
  unfold A.
  rewrite H.
  simpl.
  unfold A in H0.
  rewrite H, Rabs_minus_sym, Rabs_right in H0; simpl in H0; try lra.
  rewrite <- H, limeq1, <- isfin.
  simpl.
  ring_simplify.
  generalize (Lim_seq_pos (sum_n (fun n0 : nat => (α (S (x + n0)) x0)²))); intros.
  rewrite <- isfin in H1.
  simpl in H1.
  apply Rle_ge.
  apply H1.
  intros.
  apply sum_n_nneg.
  intros.
  apply Rle_0_sqr.
Qed.

Lemma uniform_converge_series_sum_sq_tails (α : nat -> Ts -> R) : 
  let A := fun ω => Series (fun k => rvsqr (α k) ω) in
  is_lim_seq'_uniform_almost (fun n ω => sum_n (fun k => rvsqr (α k) ω) n) A ->
  forall (eps : posreal),
    eventually (fun n => almostR2 prts Rle (fun ω : Ts => Series (fun n0 : nat => (α (S n + n0)%nat ω)²)) (const eps)).
Proof.
  intros A uniform eps.
  assert (ex_ser :   almost prts (fun ω => ex_series (fun k => rvsqr (α k) ω))).
  {
    now apply is_lim_seq'_uniform_ex_series_almost with (l := A).
  }
  specialize (uniform eps).
  revert uniform.
  apply eventually_impl.
  apply all_eventually; intros ?.
  apply almost_impl.
  revert ex_ser; apply almost_impl.
  apply all_almost; intros ???.
  rv_unfold'_in_star.
  generalize H; intros HH.
  destruct H.
  apply is_series_unique in H.
  assert (limeq1: Series (fun k : nat => (α k x0)²) =
                    (sum_n (fun k : nat => (α k x0)²) x) + 
                      (Series (fun n0 : nat => (α (S x + n0)%nat x0)²))).
  {
    assert (0 <= x)%nat by lia.
    generalize (sum_n_m_Series (fun k : nat => (α k x0)²) 0%nat x H1 HH); intros.
    unfold sum_n.
    simpl in H2.
    simpl.
    lra.
  }
  assert (limeq2: Series (fun n0 : nat => (α (S x + n0)%nat x0)²) = 
            (A x0) - (sum_n (fun k : nat => (α k x0)²) x)).
  {
    unfold A.
    rewrite limeq1;  lra.
  }
  rewrite limeq2.
  unfold A.
  rewrite H.
  simpl.
  unfold A in H0.
  rewrite H, Rabs_minus_sym, Rabs_right in H0; simpl in H0; try lra.
  rewrite <- H, limeq1.
  simpl.
  ring_simplify.
  apply Rle_ge.
  apply Series_nonneg.
  intros.
  apply Rle_0_sqr.
Qed.

End uniform.
