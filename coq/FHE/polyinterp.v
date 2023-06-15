Require Import Reals Permutation Morphisms.
Require Import Coquelicot.Complex.
Require Import List.
Require Import Lra Lia.

Set Bullet Behavior "Strict Subproofs".

(* represent complex number as pair *)
Definition nth_root (j n : nat) : C :=
  let c := (2*PI*INR(j)/INR(n))%R in 
  (cos c, sin c).

Lemma S_INR_not_0 n :
  INR (S n) <> 0%R.
Proof.
  rewrite S_INR.
  generalize (pos_INR n).
  lra.
Qed.

Lemma nth_root_0 n :
  nth_root 0 (S n) = R1.
Proof.
  unfold nth_root.
  assert ((2 * PI * INR 0 / INR (S n))%R = 0%R).
  {
    unfold INR at 1.
    field.
    apply S_INR_not_0.
  }
  rewrite H.
  now rewrite cos_0, sin_0.
Qed.

Lemma nth_root_2PI n j :
  nth_root (j * (S n)) (S n) = R1.
Proof.
  unfold nth_root.
  rewrite mult_INR.
  replace (2 * PI * (INR j * INR (S n)) / INR (S n))%R with
    (0 + 2 * INR(j) * PI)%R.
  - rewrite cos_period, sin_period.
    now rewrite cos_0, sin_0.
  - field.
    apply S_INR_not_0.
Qed.


Lemma nth_root_2PI_plus n j k :
  nth_root (j + k * (S n)) (S n) = nth_root j (S n).
Proof.
  unfold nth_root.
  replace (2 * PI * INR (j + k * S n) / INR (S n))%R with
    (2 * PI * INR(j)/INR(S n) + 2 * INR k * PI)%R.
  - now rewrite cos_period, sin_period.
  - rewrite plus_INR, mult_INR.
    field.
    apply S_INR_not_0.
 Qed.

Definition nth_roots (n:nat) :=
  map (fun j => nth_root j n) (seq 0 n).

Lemma de_moive (x : R) (n : nat) :
  Cpow (cos x, sin x) n = (cos ((INR n) * x), sin ((INR n) * x)).
Proof.
  induction n.
  - simpl.
    rewrite Rmult_0_l.
    now rewrite cos_0, sin_0.
  - simpl Cpow.
    rewrite IHn.
    unfold Cmult, fst, snd.
    replace (INR (S n) * x)%R with (x + (INR n) * x)%R.
    + rewrite cos_plus, sin_plus.
      f_equal.
      lra.
    + rewrite S_INR.
      lra.
  Qed.

Lemma Cpow_nth_root j n e :
  Cpow (nth_root j (S n)) e = nth_root (e * j) (S n).
Proof.
  unfold nth_root.
  rewrite de_moive.
  rewrite mult_INR.
  do 2 f_equal; field; apply S_INR_not_0.
Qed.

Lemma Cpow_nth_root_comm j n e :
  Cpow (nth_root j (S n)) e = Cpow (nth_root e (S n)) j.
Proof.
  do 2 rewrite Cpow_nth_root.
  f_equal.
  lia.
Qed.

Lemma nth_root_npow j n :
  Cpow (nth_root j (S n)) (S n) = RtoC R1.
Proof.
  rewrite Cpow_nth_root.
  replace (S n * j) with (j * S n) by lia.
  now rewrite nth_root_2PI.
Qed.

Lemma minus_mod (j1 j2 n : nat) :
  j1 mod (S n) = j2 mod (S n) ->
  (j2 - j1) mod (S n) = 0.
Proof.
  intros eqq1.
  destruct (le_dec j1 j2).
  - generalize (Zdiv.Zminus_mod (Z.of_nat j2) (Z.of_nat j1) (Z.of_nat (S n)))
    ; intros HH.
    rewrite <- Nat2Z.inj_sub in HH by trivial.
    repeat rewrite <- Nat2Z.inj_mod in HH.
    rewrite <- eqq1 in HH.
    rewrite Z.sub_diag in HH.
    rewrite Zdiv.Zmod_0_l in HH.
    apply (f_equal Z.to_nat) in HH.
    now rewrite Nat2Z.id in HH.
  - rewrite Minus.not_le_minus_0_stt by trivial.
    now apply Nat.mod_0_l.
Qed.    

Lemma nth_root_mod j1 j2 n :
  j1 mod (S n) = j2 mod (S n) ->
  nth_root j1 (S n) = nth_root j2 (S n).
Proof.
  intros.
  destruct (le_dec j1 j2).
  - assert (exists (k:nat), j2 = j1 + k * (S n)).
    {
      generalize (Nat.div_mod_eq (j2 - j1) (S n)); intros.
      exists ((j2 - j1)/(S n)).
      rewrite minus_mod in H0; trivial; lia.
    }
    destruct H0.
    rewrite H0.
    now rewrite nth_root_2PI_plus.
  - assert (exists (k:nat), j1 = j2 + k * (S n)).
    {
      generalize (Nat.div_mod_eq (j1 - j2) (S n)); intros.
      exists ((j1 - j2)/(S n)).
      rewrite minus_mod in H0; trivial; lia.
    }
    destruct H0.
    rewrite H0.
    now rewrite nth_root_2PI_plus.
 Qed.

Fixpoint list_Cplus (l : list C) : C :=
  match l with
  | nil => R0
  | a :: l' => Cplus a (list_Cplus l')
  end.


Lemma prim_nth_root j n :
  nth_root j (S n) = Cpow (nth_root 1 (S n)) j.
Proof.
  rewrite Cpow_nth_root.
  f_equal.
  lia.
 Qed.

Lemma nth_root_not_0 j n :
  nth_root j (S n) <> R0.
Proof.
  unfold nth_root.
  unfold RtoC.
  generalize cos_sin_0; intros.
  specialize (H (2 * PI * INR j / INR (S n))%R).
  replace R0 with 0%R by lra.
  unfold not.
  intros.
  apply H.
  split.
  - apply (f_equal (fun c => fst c)) in H0.
    now unfold fst in H0.
  - apply (f_equal (fun c => snd c)) in H0.
    now unfold snd in H0.
 Qed.


Lemma cos1_sin0 (x : R) :
  cos x = R1 ->
  sin x = R0.
Proof.
  intros eqq1.
  generalize (cos2 x).
  rewrite eqq1; intros eqq2.
  replace R1 with 1%R in eqq2 by trivial.
  rewrite Rsqr_1 in eqq2.
  apply Rsqr_0_uniq.
  lra.
Qed.  

Lemma cosneg1_sin0 (x : R) :
  cos x = Ropp R1 ->
  sin x = R0.
Proof.
  intros eqq1.
  generalize (cos2 x).
  rewrite eqq1; intros eqq2.
  replace R1 with 1%R in eqq2 by trivial.
  rewrite <- Rsqr_neg in eqq2.
  rewrite Rsqr_1 in eqq2.
  apply Rsqr_0_uniq.
  lra.
Qed.  

Lemma cos_eq_1_aux_pos (x : R) :
  cos x = R1 ->
  exists k, x = (PI * IZR(k))%R.
Proof.
  intros eqq1.
  generalize (cos1_sin0 _ eqq1); intros eqq2.
  apply sin_eq_0_0 in eqq2.
  destruct eqq2 as [k eqqk].
  exists k.
  lra.
Qed.

Lemma cos_eq_1_aux_neg (x : R) :
  cos x = Ropp R1 ->
  exists k, x = (PI * IZR(k))%R.
Proof.
  intros eqq1.
  generalize (cosneg1_sin0 _ eqq1); intros eqq2.
  apply sin_eq_0_0 in eqq2.
  destruct eqq2 as [k eqqk].
  exists k.
  lra.
Qed.

Lemma cos_eq_1 (x : R) :
  cos x = R1 ->
  exists k, x = (2 * PI * IZR(k))%R.
Proof.
  intros eqq1.
  destruct (cos_eq_1_aux_pos _ eqq1) as [kk eqq2]; subst.
  assert (cutter:(forall kk, ((0 <= kk)%Z ->  cos (PI * IZR kk) = R1 -> exists k : Z, (PI * IZR kk)%R = (2 * PI * IZR k)%R)) ->  (forall kk, (cos (PI * IZR kk) = R1 -> (exists k : Z, (PI * IZR kk)%R = (2 * PI * IZR k)%R
         )))).
  {
    clear.
    intros HH kk eqq1.
    destruct (Z_le_gt_dec 0 kk); [eauto |].
    destruct (HH (Z.opp kk)%Z).
    - lia.
    - rewrite opp_IZR.
      replace (PI * - IZR kk)%R with (- (PI * IZR kk))%R by lra.
      now rewrite cos_neg.
    - exists (Z.opp x).
      rewrite opp_IZR in H |- *.
      lra.
  }

  apply cutter; trivial; clear.
  intros kk kk_nneg eqq1.
  destruct (Zeven_odd_dec kk).
  - destruct (Zeven_ex _ z); subst.
    exists x.
    rewrite mult_IZR.
    lra.
  - destruct (Zodd_ex _ z); subst.
    rewrite plus_IZR, mult_IZR in eqq1.
    replace ((PI * (2 * IZR x + 1))%R) with
      (2 * IZR x * PI + PI)%R in eqq1 by lra.
    rewrite neg_cos in eqq1.
    assert (eqq2: cos (2 * IZR x * PI)%R = Ropp R1) by lra.
    generalize (cos_period 0 (Z.to_nat x)); intros HH.
    rewrite cos_0 in HH.
    rewrite INR_IZR_INZ in HH.
    rewrite Z2Nat.id in HH by lia.
    replace (2 * IZR x * PI)%R with (0 + 2 * IZR x * PI)%R in eqq2 by lra.
    lra.
Qed.

Lemma cos_eq_1_1 : forall x:R, (exists k : Z, x = (IZR k * 2 * PI)%R) -> cos x = 1%R.
Proof.
  assert (forall n, cos (INR n * 2 * PI) = 1%R). {
    intros n;induction n as [|n IHn].
    { change (INR 0) with 0%R.
      replace (0 * 2 * PI)%R with 0%R by ring.
      exact cos_0. }
    rewrite S_INR.
    replace ((INR n + 1) * 2 * PI)%R with ((INR n) * 2 * PI + 2 * PI)%R by ring.
    rewrite cos_plus, IHn, cos_2PI, sin_2PI.
    ring.
  }
  intros x [k Hx].
  rewrite Hx;clear x Hx.
  destruct (Z.abs_or_opp_abs k).
  - replace (IZR k) with (INR (Z.to_nat k)).
    { apply H. }
    rewrite INR_IZR_INZ.
    f_equal.
    apply Z2Nat.id.
    lia.
  - replace (IZR k) with (- INR (Z.to_nat (- k)))%R.
    { replace (- INR (Z.to_nat (- k)) * 2 * PI)%R with (- (INR (Z.to_nat (- k)) * 2 * PI))%R by ring.
      rewrite cos_neg.
      rewrite H;ring. }
    rewrite INR_IZR_INZ.
    rewrite <-opp_IZR. f_equal.
    lia.
Qed.

Lemma cos_lt_1 (x : R) :
  (0 < x)%R ->
  (x < 2*PI)%R ->
  (cos x < 1)%R.
Proof. 
  intros.
  generalize (COS_bound x); intros.
  generalize PI_RGT_0; intro pi_gt.
  destruct H1.
  assert (cos x <> 1)%R.
  {
    unfold not.
    intros.
    generalize (cos_eq_1_aux_pos x H3); intros.
    destruct H4.
    rewrite H4 in H0.
    rewrite Rmult_comm in H0.
    apply Rmult_lt_reg_r in H0; trivial.
    rewrite H4 in H.
    replace 0%R with (PI * 0)%R in H by lra.
    apply Rmult_lt_reg_l in H; trivial.
    assert (x0 = 1)%Z.
    {
      apply lt_IZR in H.
      apply lt_IZR in H0.
      lia.
    }
    rewrite H5 in H4.
    rewrite Rmult_1_r in H4.
    rewrite H4 in H3.
    generalize cos_PI; intros.
    lra.
  }
  lra.
 Qed.

Lemma cos_eq_1_alt (x : R) :
  cos x = R1 ->
  exists (k:Z), x = (2 * PI * IZR(k))%R.
Proof.
  intros Hx.
  assert (PI2_neq0: (2 * PI <> 0)%R).
  {
    generalize PI_neq0.
    lra.
  }
  destruct (euclidian_division x (2*PI) PI2_neq0) as (q & r & EQ & Hr & Hr').
  exists q.
  rewrite <- (Rplus_0_r (_*_)). subst.
  rewrite Rmult_comm.
  apply Rplus_eq_compat_l.
  rewrite cos_plus in Hx.
  assert (H : cos (IZR q * 2 * PI)%R = 1%R) by ( apply cos_eq_1_1; now exists q).
  rewrite <- Rmult_assoc in Hx.
  rewrite H, Rmult_1_l in Hx.
  rewrite sin_eq_0_1 in Hx.
  - rewrite Rmult_0_l, Rminus_0_r in Hx.
    rewrite Rabs_right in Hr'.
    + destruct Hr as [Hr | ->]; trivial.
      exfalso.
      generalize (cos_lt_1 r Hr Hr'); intros.
      lra.
    + generalize PI_RGT_0; lra.
  - exists (2*q)%Z.
    rewrite mult_IZR.
    lra.
 Qed.

Lemma cos_eq_1_nneg (x : R) :
  cos x = R1 ->
  (0 <= x)%R ->
  exists (k:nat), x = (2 * PI * INR(k))%R.
Proof.
  intros.
  generalize (cos_eq_1 x H); intros.
  destruct H1.
  rewrite H1 in H0.
  replace (0%R) with (2 * PI * 0)%R in H0 by lra.
  apply Rmult_le_reg_l in H0.
  - apply le_IZR in H0.
    exists (Z.abs_nat x0).
    rewrite H1.
    do 2 f_equal.
    destruct x0; simpl; trivial; try lia.
    now rewrite INR_IPR.
  - generalize PI_RGT_0; lra.
Qed.

Lemma nth_root_not_1 j n :
  j mod (S n) <> 0 ->
  nth_root j (S n) <> R1.
Proof.
  unfold nth_root.
  intros.
  unfold RtoC.
  unfold not.
  intros.
  replace (S n) with (n + 1) in H0 by lia.
  inversion H0; clear H0.
  assert (xnneg :(0 <= 2 * PI * INR j / INR (n + 1))%R).
  {
    apply Rmult_le_pos.
    - generalize (pos_INR j); intros.
      apply Rmult_le_pos; trivial.
      generalize PI_RGT_0; intros.
      lra.
    - left.
      apply Rinv_0_lt_compat.
      apply lt_0_INR.
      lia.
  }
  apply cos_eq_1_nneg in H2; trivial.
  destruct H2.
  apply (f_equal (fun r => (r /(2 * PI))%R)) in H0.
  unfold Rdiv in H0.
  rewrite Rmult_comm in H0.
  assert ((2 * PI)%R <> R0).
  {
    generalize PI_neq0; intros.
    lra.
  }
  do 2 rewrite <- Rmult_assoc in H0.
  rewrite <- Rinv_l_sym in H0; trivial.
  rewrite Rmult_1_l in H0.
  symmetry in H0.
  rewrite Rmult_comm in H0.
  rewrite <- Rmult_assoc in H0.
  rewrite <- Rinv_l_sym in H0; trivial.
  rewrite Rmult_1_l in H0.
  replace (n+1) with (S n) in H0 by lia.
  apply (f_equal (fun r => (r * INR (S n))%R)) in H0.
  rewrite Rmult_assoc in H0.
  rewrite <- Rinv_l_sym in H0.
  - rewrite Rmult_1_r in H0.
    rewrite <- mult_INR in H0.
    apply INR_eq in H0.
    apply (f_equal (fun k => k mod (S n))) in H0.
    rewrite Nat.mod_mul in H0; try lia.
  - apply not_0_INR.
    lia.
 Qed.

Lemma Cinv_1_r :
  Cinv 1%R = 1%R.
Proof.
  unfold Cinv.
  unfold RtoC.
  simpl.
  f_equal; field.
Qed.

Lemma Cpow_sub_r (c : C) (n m : nat):
  m <= n ->
  c <> R0 ->
  (c ^ (n - m))%C = (c ^ n / c ^ m)%C.
Proof.
  intros.
  assert (Cmult (Cpow c (n - m)) (Cpow c m) = Cpow c n).
  {
    rewrite <- Cpow_add_r.
    f_equal.
    lia.
  }
  rewrite <- H1.
  unfold Cdiv.
  rewrite <- Cmult_assoc.
  rewrite Cinv_r.
  - now rewrite Cmult_1_r.
  - now apply Cpow_nz.
 Qed.

Lemma nth_root_diff j k n :
  j <= k ->
  Cdiv (nth_root k (S n)) (nth_root j (S n)) = nth_root (k-j) (S n).
Proof.
  intros.
  rewrite (prim_nth_root k _).
  rewrite (prim_nth_root j _).
  rewrite (prim_nth_root (k-j) _).
  rewrite Cpow_sub_r; trivial.
  apply nth_root_not_0.
Qed.

Instance list_Cplus_perm_proper : Proper (@Permutation _ ==> eq) list_Cplus.
Proof.
  repeat red.
  apply Permutation_ind_bis; trivial; simpl; intros.
  - now rewrite H0.
  - rewrite H0; ring.
  - now rewrite H0, H2.
Qed.
    
Lemma C_telescope_mult (c : C) (n : nat) :
  (Cmult (c - R1) (list_Cplus (map (fun j => Cpow c j) (seq 0 (S n)))) = 
    (Cpow c (S n) - 1%R))%C.
Proof.
  induction n.
  - simpl; ring.
  - rewrite seq_S.
    simpl plus.
    rewrite map_app.
    unfold map at 2.
    rewrite <- Permutation_cons_append.
    unfold list_Cplus; fold list_Cplus.
    transitivity ((c - R1) * c ^ S n + (c - R1) * list_Cplus (map (fun j : nat => c ^ j) (seq 0 (S n))))%C; [ring |].
    rewrite IHn.
    simpl; ring.
Qed.

Lemma C_telescope_div (c : C) (n : nat) :
  c <> R1 ->
  list_Cplus (map (fun j => Cpow c j) (seq 0 (S n))) = 
    Cdiv (Cpow c (S n) - 1%R) (c - R1).
Proof.
  intros.
  generalize (C_telescope_mult c n); intros.
  rewrite <- H0.
  unfold Cdiv.
  rewrite Cmult_comm.
  rewrite Cmult_assoc.
  rewrite Cinv_l.
  - now rewrite Cmult_1_l.
  - unfold not.
    intros.
    unfold not in H.
    apply H.
    apply (f_equal (fun cc => Cplus cc (RtoC R1))) in H1.
    now ring_simplify in H1.
 Qed.

Lemma sum_nth_roots_0 n :
  list_Cplus (map (fun j => Cpow (nth_root 1 (S (S n))) j) (seq 0 (S (S n)))) = R0.
Proof.
  rewrite C_telescope_div.
  - rewrite nth_root_npow.
    unfold Cminus.
    rewrite Cplus_opp_r.
    unfold Cdiv.
    now rewrite Cmult_0_l.
  - apply nth_root_not_1.
    rewrite Nat.mod_1_l; lia.
 Qed.

Lemma sum_nth_roots_0_gen k n :
  k mod (S (S n)) <> 0 ->
  list_Cplus (map (fun j => Cpow (nth_root k (S (S n))) j) (seq 0 (S (S n)))) = R0.
Proof.
  intros.
  rewrite C_telescope_div.
  - rewrite nth_root_npow.
    unfold Cminus.
    rewrite Cplus_opp_r.
    unfold Cdiv.
    now rewrite Cmult_0_l.
  - now apply nth_root_not_1.
Qed.

Lemma pow_nth_root_prim n :
  Cpow (nth_root 1 (S n)) (S n) = R1.  
Proof.
  unfold nth_root.
  rewrite de_moive.
  replace (INR (S n) * (2 * PI * INR 1 / INR (S n)))%R with (2 * PI)%R.
  - now rewrite cos_2PI, sin_2PI.
  - replace (INR 1) with R1 by now unfold INR.
    field.
    apply S_INR_not_0.
 Qed.

Lemma list_Cplus_app l1 l2 :
  list_Cplus (l1 ++ l2) = Cplus (list_Cplus l1) (list_Cplus l2).
Proof.
  induction l1.
  - simpl.
    now rewrite Cplus_0_l.
  - simpl.
    rewrite IHl1.
    now rewrite Cplus_assoc.
 Qed.

Lemma root_prod_1 j n :
  list_Cplus
    (map (fun k => Cmult (Cpow (nth_root j (S n)) k) (Cpow (Cinv (nth_root k (S n))) j)) 
       (seq 0 (S n))) = INR (S n).
Proof.
  replace (map (fun k => Cmult (Cpow (nth_root j (S n)) k) (Cpow (Cinv (nth_root k (S n))) j)) 
             (seq 0 (S n))) with
          (map (fun k => RtoC R1) (seq 0 (S n))).
  - induction n.
    + simpl.
      now rewrite Cplus_0_r.
    + rewrite seq_S.
      rewrite map_app.
      rewrite list_Cplus_app.
      rewrite IHn.
      replace (S n) with (n + 1) by lia.
      replace (S (n + 1)) with (n + 2) by lia.
      simpl.
      do 2 rewrite plus_INR.
      simpl.
      unfold RtoC.
      rewrite Cplus_0_r.
      unfold Cplus, fst, snd.
      f_equal; lra.
  - apply map_ext.
    intros.
    rewrite Cpow_inv.
    + do 2 rewrite Cpow_nth_root.
      replace (j * a) with (a * j) by lia.
      rewrite Cinv_r.
      * now replace R1 with 1%R by lra.
      * apply nth_root_not_0.
    + apply nth_root_not_0.
  Qed.

Lemma pow_nth_root j n :
  Cpow (nth_root j (S n)) (S n) = R1.
Proof.
  rewrite prim_nth_root.
  rewrite <- Cpow_mult_r.
  replace (j * S n) with (S n * j) by lia.
  rewrite Cpow_mult_r.
  rewrite pow_nth_root_prim.
  now rewrite Cpow_1_l.
Qed.

Definition Ceval_Rpoly (p : list R) (c : C) :=
  let cpows := map (fun j => Cpow c j) (seq 0 (length p)) in
  fold_right Cplus 0%R (map (fun '(a, b) => Cmult (RtoC a) b) (combine p cpows)).

Fixpoint C_horner_eval (p : list C) (c : C) : C :=
  match p with
  | nil => R0
  | a :: p' => Cplus a (Cmult c (C_horner_eval p' c))
  end.

Fixpoint C_horner_eval_Rpoly (p : list R) (c : C) : C :=
  match p with
  | nil => R0
  | a :: p' => Cplus a (Cmult c (C_horner_eval_Rpoly p' c))
  end.




