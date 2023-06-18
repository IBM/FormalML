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

Lemma cos_eq_neg1 (x : R) :
  cos x = Ropp R1 ->
  exists k, x = (2 * PI * IZR(k) + PI)%R.
Proof.
  intros eqq1.
  generalize (Rtrigo_facts.cos_pi_plus x); intros eqq2.
  rewrite eqq1 in eqq2.
  rewrite Ropp_involutive in eqq2.
  apply cos_eq_1 in eqq2.
  destruct eqq2 as [k eqq2].
  exists (k-1)%Z.
  rewrite minus_IZR.
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

Lemma sin_cos_eq x y:
  sin x = sin y /\ cos x = cos y ->
  exists (k:Z),
    x = (y + 2 * PI * IZR(k))%R.
Proof.
  intros.
  generalize (cos_minus x y); intros.
  destruct H.
  rewrite H, H1 in H0.
  generalize (sin2_cos2 y); intros.
  rewrite Rplus_comm in H0.
  unfold Rsqr in H2.
  rewrite H2 in H0.
  apply cos_eq_1 in H0.
  destruct H0.
  exists x0.
  rewrite <- H0.
  lra.
Qed.

Lemma nth_root_eq j k n :
  j mod (S n) = k mod (S n) <->
  nth_root j (S n) = nth_root k (S n).
Proof.
  split; intros. 
  - now apply nth_root_mod.
  - unfold nth_root in H.
    replace (S n) with (n + 1) in H by lia.
    inversion H; clear H.
    generalize (sin_cos_eq (2 * PI * INR j / INR (n + 1)) 
                 (2 * PI * INR k / INR (n + 1))); intros.
    destruct H.
    + split; trivial.
    + replace  (2 * PI * INR k / INR (n + 1) + 2 * PI * IZR x)%R with
        (2 * PI * (INR k / INR (n+1) + IZR x))%R in H by lra.
      replace  (2 * PI * INR j / INR (n + 1))%R with
         (2 * PI * (INR j / INR (n + 1)))%R in H by lra.
      apply (f_equal (fun r => (/ (2 * PI)) * r))%R in H.
      assert (2 * PI <> 0)%R.
      {
        generalize PI_neq0.
        lra.
      }
      rewrite <- Rmult_assoc in H.
      rewrite <- Rinv_l_sym, Rmult_1_l in H; trivial.
      rewrite <- Rmult_assoc in H.
      rewrite <- Rinv_l_sym, Rmult_1_l in H; trivial.
      clear H0 H1 H2.
      repeat rewrite plus_INR in H.
      simpl in H.
      assert (possn:(INR n + 1)%R <> 0%R).
      {
        generalize (pos_INR n); lra.
      } 
      field_simplify in H; try lra.
      apply (f_equal (Rmult (INR n + 1))) in H.
      field_simplify in H; try lra.
      repeat rewrite INR_IZR_INZ in H.
      repeat rewrite <- mult_IZR in H.
      repeat rewrite <- plus_IZR in H.
      apply eq_IZR in H.
      apply Nat2Z.inj.
      repeat rewrite Nat2Z.inj_mod.
      rewrite H.
      transitivity ((Z.of_nat k + (x * (Z.of_nat (S n)))) mod Z.of_nat (S n))%Z.
      * f_equal.
        rewrite Nat2Z.inj_succ.
        lia.
      * now rewrite Zdiv.Z_mod_plus_full.
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

Lemma nth_root_1 j n :
  j mod (S n) = 0 ->
  nth_root j (S n) = R1.
Proof.
  intros.
  rewrite (nth_root_mod j 0 n).
  - now rewrite nth_root_0.
  - rewrite H.
    rewrite Nat.mod_small; lia.
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

Lemma nth_root_mul j k n :
  Cmult (nth_root j (S n)) (nth_root k (S n)) = nth_root (j + k) (S n).
Proof.
  intros.
  rewrite (prim_nth_root k _).
  rewrite (prim_nth_root j _).
  rewrite (prim_nth_root (j + k) _).
  rewrite Cpow_add_r; trivial.
 Qed.

Lemma nth_root_Sn n :
  nth_root (S n) (S n) = 1%R.
Proof.
  rewrite prim_nth_root.
  now rewrite nth_root_npow.
Qed.

Lemma nth_root_inv j n :
  Cinv (nth_root j (S n)) = nth_root (S n - (j mod S n)) (S n).
Proof.
  generalize (nth_root_diff (j mod S n) (S n) n); intros.
  rewrite <- H.
  - rewrite nth_root_Sn.
    unfold Cdiv.
    rewrite Cmult_1_l.
    f_equal.
    apply (nth_root_mod j (j mod S n) n).
    rewrite Nat.mod_mod; try lia.
  - assert (S n <> 0) by lia.
    generalize (Nat.mod_upper_bound j (S n) H0); intros.
    lia.
 Qed.
    
Lemma nth_root_div j k n :
  Cdiv (nth_root j (S n)) (nth_root k (S n)) = 
    nth_root (j + (S n - (k mod S n))) (S n).
Proof.
  unfold Cdiv.
  rewrite nth_root_inv.
  apply nth_root_mul.
Qed.

Lemma nth_root_Cmod j n :
  Cmod (nth_root j (S n)) = 1%R.
Proof.
  unfold Cmod, nth_root, fst, snd.
  rewrite Rplus_comm.
  rewrite <- sqrt_1.
  f_equal.
  do 2 rewrite <- Rsqr_pow2.
  now rewrite sin2_cos2.
Qed.

Lemma Cmod_Cconj (c : C) :
  Cmult c (Cconj c) = Rsqr (Cmod c).
Proof.
  destruct c.
  unfold Cconj, Cmod, Cmult, fst, snd.
  rewrite Rsqr_sqrt.
  - unfold RtoC.
    f_equal; lra.
  - apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

Lemma nth_root_conj j n :
  Cconj (nth_root j (S n)) = Cinv (nth_root j (S n)).
Proof.
  generalize (Cmod_Cconj (nth_root j (S n))); intros.
  rewrite nth_root_Cmod in H.
  rewrite Rsqr_1 in H.
  apply (f_equal (fun c => Cmult (/ nth_root j (S n)) c)) in H.
  rewrite Cmult_1_r in H.
  rewrite Cmult_assoc in H.
  rewrite Cinv_l in H.
  - now rewrite Cmult_1_l in H.
  - apply nth_root_not_0.
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

Lemma pow2_S (j:nat) :
  exists (k : nat), 2^j = S k.
Proof.
  exists (2^j-1).
  induction j.
  - now simpl.
  - simpl.
    rewrite IHj.
    lia.
Qed.

Lemma nth_root_half_pow_aux n :
  Cpow (nth_root (S n) (2 * (S n))) 2 = 1%R.
Proof.
  replace (2 * (S n)) with (S (2 * n + 1)) by lia.
  rewrite Cpow_nth_root.
  do 2 replace (2 * (S n)) with (S (2 * n + 1)) by lia.
  now rewrite nth_root_Sn.
Qed.

Lemma pow2_inv x y : (x ^ 2)%R = y -> Rabs x = sqrt y.
Proof.
  intros eqq1.
  apply (f_equal sqrt) in eqq1.
  destruct (Rle_dec 0 x).
  - intros.
    rewrite sqrt_pow2 in eqq1 by trivial.
    rewrite eqq1.
    rewrite Rabs_right; trivial.
    generalize (sqrt_pos y); lra.
  - assert (eqq1':sqrt ((-x) ^2) = sqrt y).
    {
      now rewrite <- Rsqr_pow2, <- Rsqr_neg, Rsqr_pow2.
    } 
    rewrite sqrt_pow2 in eqq1' by lra.
    now rewrite Rabs_left by lra.
Qed.

Lemma Rabs_pm_l x y : Rabs x = y -> x = y \/ (- x)%R = y.
Proof.
  unfold Rabs.
  destruct (Rcase_abs); [right|left]; lra.
Qed.

Lemma Rabs_pm_r x y : Rabs x = y -> x = y \/ x = (- y)%R.
Proof.
  unfold Rabs.
  destruct (Rcase_abs); [right|left]; lra.
Qed.
  
Lemma Cpow_2 (c : C) :
  Cpow c 2 = 1%R -> c = 1%R \/ c = (-1)%R.
Proof.
  unfold Cpow.
  rewrite Cmult_1_r.
  intros.
  destruct c.
  unfold Cmult, fst, snd, RtoC in H.
  injection H; intros; clear H.
  ring_simplify in H0.
  apply (f_equal (fun z => (/2 * z)%R)) in H0.
  do 2 rewrite <- Rmult_assoc in H0.
  rewrite <- Rinv_l_sym in H0; try lra.
  rewrite Rmult_1_l, Rmult_0_r in H0.
  apply Rmult_integral in H0.
  destruct H0; subst; ring_simplify in H1.
  - assert (0 <= r0 ^ 2)%R by apply pow2_ge_0.
    lra.
  - apply pow2_inv in H1.
    rewrite sqrt_1 in H1.
    apply Rabs_pm_r in H1.
    unfold RtoC.
    destruct H1; [left|right]; f_equal; lra.
Qed.

Lemma nth_root_half_pow n :
  nth_root (S n) (2 * (S n)) = (-1)%R.
Proof.
  generalize (nth_root_half_pow_aux n); intros.
  apply Cpow_2 in H.
  destruct H; trivial.
  replace (2 * (S n)) with (S (2 * n + 1)) in H by lia.
  replace 1%R with R1 in H by lra.
  generalize (nth_root_not_1 (S n) (2*n+1)); intros.
  assert (S n mod S (2 * n + 1) <> 0).
  {
    rewrite Nat.mod_small; lia.
  }
  tauto.
Qed.

Lemma odd_roots_prim j n :
  Cpow (nth_root (2 * j + 1) (2 ^ (S n))) (2^n) = (-1)%R.
Proof.
  generalize (pow2_S (S n)); intros.
  destruct H.
  rewrite H.
  rewrite Cpow_nth_root.
  rewrite <- H.
  assert ((2 ^ n * (2 * j + 1) mod (2 ^ S n)) =
           (2 ^ n mod (2 ^ S n))).
  {
    replace (2 ^n * (2 * j + 1)) with (2 ^ n + j*(2 * 2^n)) by lia.
    replace (2 ^ (S n)) with (2 * 2^n).
    - rewrite Nat.mod_add; try lia.
      assert (2^n <> 0).
      {
        apply Nat.pow_nonzero.
        lia.
      }
      lia.
    - simpl.
      lia.
  }
  rewrite H in H0.
  apply nth_root_mod in H0.
  rewrite <- H in H0.
  rewrite H0.
  generalize (pow2_S n); intros.
  destruct H1.
  simpl.
  replace (2 ^ n + (2 ^n + 0)) with (2 * 2^n) by lia.
  rewrite H1.
  now rewrite nth_root_half_pow.
Qed.  

Lemma Cmult_conj (x y : C) :
  Cmult (Cconj x) (Cconj y) = Cconj (Cmult x y).
Proof.
  destruct x; destruct y.
  unfold Cconj, Cmult, fst, snd.
  f_equal; lra.
Qed.  

(*
Lemma Cpow_conj (x : C) (n : nat) :
  Cconj (Cpow x n) = Cpow (Cconj x) n.
Proof.
  induction n.
  - unfold Cconj.
    simpl.
    now replace (- 0)%R with 0%R by lra.
  - simpl.
    rewrite <- Cmult_conj.
    now rewrite IHn.
Qed.
*)

Definition odd_nth_roots (n : nat) :=
  (map (fun j => nth_root (2*j+1) (2 ^ (S n))) (seq 0 (2^n))).

Definition odd_nth_roots_half (n : nat) :=
  (map (fun j => nth_root (2*j+1) (2 ^ (S (S n)))) (seq 0 (2^n))).

Definition decode (p : list R) (n : nat) :=
  map (C_horner_eval_Rpoly p) (odd_nth_roots n).

Definition decode_half (p : list R) (n : nat) :=
  map (C_horner_eval_Rpoly p) (odd_nth_roots_half n).

Definition Cinner_prod (l1 l2 : list C) :=
  list_Cplus (map (fun '(a,b) => Cmult a b) (combine l1 l2)).

Definition encode (cl : list C) (n : nat) :=
  let conjroots := map Cconj (odd_nth_roots n) in
  map (fun c => Cdiv c (2^n)%R)
    (map (fun k => Cinner_prod cl (map (fun x => Cpow x k) conjroots))
       (seq 0 (2 ^n))).

Definition encode_half (cl : list C) (n : nat) :=
  let conjroots := map Cconj (odd_nth_roots_half n) in
  map (fun c => ((2 * Re c)/2^(S n))%R)
    (map (fun k => Cinner_prod cl (map (fun x => Cpow x k) conjroots))
       (seq 0 (2 ^n))).

Lemma Im_div_real (c : C) (r : R) :
  r <> 0%R ->
  Im c = 0%R <-> Im (Cdiv c r) = 0%R.
Proof.
  intros.
  destruct c.
  unfold Cdiv, Cinv, Cmult, Im, fst, snd.
  simpl.
  split; intros.
  - rewrite H0.
    now field.
  - field_simplify in H0; try easy.
    unfold pow in H0.
    field_simplify in H0; try easy.
    unfold Rdiv in H0.
    apply (f_equal (fun z => (z * r)%R)) in H0.
    rewrite Rmult_assoc, Rmult_0_l in H0.
    rewrite <- Rinv_l_sym in H0; trivial.
    lra.
Qed.

Lemma Cconj_im_0 (c : C) :
  Cconj c = c -> Im c = 0%R.
Proof.
  destruct c.
  unfold Cconj; simpl.
  intros.
  injection H; intros.
  lra.
Qed.

Lemma conj_rev_even n cl :
  length cl = 2 * n ->
  map Cconj cl = rev cl <->
    map Cconj (firstn n cl) = firstn n (rev cl).
Proof.
  revert cl.
  induction n.
  - replace (2 * 0) with 0 by lia.
    intros.
    apply length_zero_iff_nil in H.
    rewrite H.
    now simpl.
  - intros.
    destruct cl; try easy.
    simpl.
    intros.
    replace (n + 0) with n in H by lia.
    injection H; intros.
    generalize (rev_length cl); intros.
    replace (n + S (n + 0)) with (S (2*n)) in H0 by lia.
    rewrite H0 in H1.
    case_eq (rev cl); intros.
    + rewrite H2 in H1; simpl in H1; lia.
    + simpl.
      rewrite H2 in H1.
      simpl in H1.
      inversion H1.
      generalize (rev_length l); intros.
      rewrite H4 in H3.
      specialize (IHn (rev l) H3).
      apply (f_equal (fun ll => rev ll)) in H2.
      simpl in H2.
      rewrite rev_involutive in H2.
      rewrite H2.
      destruct IHn.
      split; intros; inversion H7; f_equal; rewrite map_app.
      * do 2 rewrite firstn_app.
        replace (n - length (rev l)) with (0) by (rewrite rev_length; lia).
        replace (n - length (map Cconj (rev l))) with (0).
        -- simpl.
           rewrite map_app; simpl.
           f_equal.
           assert (map Cconj (rev l) = rev (rev l)).
           {
             rewrite rev_involutive.
             rewrite map_app in H10.
             simpl in H10.
             rewrite Cconj_conj in H10.
             now apply app_inv_tail in H10.
           }
           rewrite H5; trivial.
           now f_equal.
        -- rewrite map_length, rev_length; lia.
      * simpl.
        rewrite Cconj_conj.
        f_equal.
        do 2 rewrite firstn_app in H10.
        replace (n - length (rev l)) with (0) in H10 by (rewrite rev_length; lia).
        replace (n - length l) with (0) in H10 by lia.
        rewrite map_app in H10.
        simpl in H10.
        apply app_inv_tail in H10.
        rewrite rev_involutive in H6.
        now apply H6.
Qed.

Lemma conj_rev_half (cl_half:list C) :
  let cl := cl_half ++ rev (map Cconj cl_half) in
  map Cconj cl = rev cl.
Proof.
  intros.
  pose (n := length cl_half).
  assert (length cl = 2*n).
  {
    unfold cl.
    rewrite app_length.
    rewrite rev_length.
    rewrite map_length.
    lia.
  }
  generalize (conj_rev_even n cl H); intros.
  apply H0.
  unfold cl.
  rewrite firstn_app.
  replace (length cl_half) with n by easy.
  replace (n - n) with 0 by lia.
  simpl.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  rewrite firstn_app.
  replace (n - length (map Cconj cl_half)) with 0.
  - rewrite map_app.
    simpl.
    f_equal.
    now rewrite firstn_map.
  - rewrite map_length.
    lia.
 Qed.

Lemma conj_rev_half_conv n (cl:list C) :
  length cl = 2*n ->
  map Cconj cl = rev cl ->
  let cl_half := firstn n cl in
  cl = cl_half ++ rev (map Cconj cl_half) .
Proof.
  intros.
  generalize (conj_rev_even n cl H); intros.
  apply H1 in H0.
  unfold cl_half.
  rewrite H0.
  rewrite firstn_rev.
  rewrite rev_involutive.
  replace (length cl - n) with n by lia.
  now rewrite firstn_skipn.
Qed.

Lemma conj_rev_rev (cl : list C) :
  map Cconj cl = rev cl ->
  cl = map Cconj (rev cl).
Proof.
  intros.
  apply (f_equal (fun l => rev l)) in H.
  rewrite rev_involutive in H.
  rewrite <- H at 1.
  now rewrite map_rev.
Qed.
  
Lemma conj_rev_odd cl n :
  length cl = 2 * n + 1 ->
  map Cconj cl = rev cl <->
    (map Cconj (firstn n cl) = rev (skipn (S n) cl) /\
      Im (nth n cl Ci) = 0%R).
Proof.
  Admitted.

Lemma list_Cplus_conj_rev_0 (cl : list C):
  length cl < 2 ->
  map Cconj cl = rev cl ->
  Im (list_Cplus cl) = 0%R.
Proof.
  intros.
  pose (n := length cl).
  destruct cl.
  - now simpl.
  - destruct cl.
    + simpl.
      simpl in H0.
      inversion H0.
      rewrite H2.
      apply Cconj_im_0 in H2.
      now rewrite Rplus_0_r.
    + simpl in H.
      lia.
Qed.

Lemma list_Cplus_conj_rev_recur (n : nat) :
  (forall (cl : list C),
      length cl = n ->
      map Cconj cl = rev cl ->    
      Im (list_Cplus cl) = 0%R) ->
  forall (cl : list C),
    length cl = n + 2 ->
    map Cconj cl = rev cl ->    
    Im (list_Cplus cl) = 0%R.
Proof.
  intros.
  destruct cl; trivial.
  simpl in H0.
  assert (lcl: length cl = n+1) by lia.
  assert(exists (c2 : C) (cl2 : list C),
            cl = cl2 ++ (c2 :: nil)).
  {
    assert (cl <> nil).
    {
      unfold not; intros.
      rewrite H2 in H0.
      simpl in H0.
      lia.
    }
    destruct (exists_last H2) as [? [??]].
    exists x0.
    now exists x.
  }
  destruct H2 as [c2 [cl2 ?]].
  rewrite H2.
  specialize (H cl2).
  simpl.
  rewrite list_Cplus_app.
  rewrite im_plus.
  rewrite H2 in H1.
  simpl in H1.
  rewrite map_app in H1.
  rewrite rev_app_distr in H1.
  simpl in H1.
  inversion H1.
  rewrite Cconj_conj in H5.  
  apply app_inv_tail in H5.
  rewrite H; trivial.
  - simpl.
    lra.
  - rewrite H2 in H0.
    rewrite app_length in H0.
    simpl in H0.
    lia.
 Qed.

Lemma pair_induction (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 Hstep n.
  enough (P n /\ P (S n)) by easy.
  induction n; intuition.
Qed.

Lemma list_Cplus_conj_rev (cl : list C):
  map Cconj cl = rev cl ->
  Im (list_Cplus cl) = 0%R.
Proof.
  intros.
  pose (P := fun n => forall (cl : list C),
                 length cl = n -> map Cconj cl = rev cl -> Im (list_Cplus cl) = 0%R).
  apply (pair_induction P) with (n := length cl); trivial; unfold P; intros.
  - apply (list_Cplus_conj_rev_0 cl0); trivial; lia.
  - apply (list_Cplus_conj_rev_0 cl0); trivial; lia.
  - apply (list_Cplus_conj_rev_recur n); trivial; lia.
Qed.

Lemma combine_app {T} (cl1 cl2 cl1' cl2' : list T) :
  length cl1 = length cl2 ->
  length cl1' = length cl2' ->
  combine (cl1 ++ cl1') (cl2 ++ cl2') = combine cl1 cl2 ++ combine cl1' cl2'.
Proof.
  Admitted.

Lemma combine_rev {T} (cl1 cl2 : list T) :
  length cl1 = length cl2 ->
  combine (rev cl1) (rev cl2) = rev (combine cl1 cl2).
Proof.
  revert cl2.
  induction cl1; intros ; simpl; trivial.
  destruct cl2; simpl.
  - now rewrite combine_nil.
  - simpl in H.
    injection H; intros.
    rewrite <- IHcl1; trivial.
    rewrite combine_app.
    + now simpl.
    + now do 2 rewrite rev_length.
    + now simpl.
 Qed.        

Lemma Cmult_combine_rev (cl1 cl2 : list C) :
  map (fun '(a, b) => (a * b)%C) (combine (rev cl1) (rev cl2)) =
    rev (map (fun '(a, b) => (a * b)%C) (combine cl1 cl2)).
Proof.
  rewrite <- map_rev.
  f_equal.
  apply combine_rev.
Qed.

  Lemma combine_map {A B C D:Type} (f:A->C) (g:B->D) (l1:list A) (l2:list B) :
    combine (map f l1) (map g l2) = map (fun '(x,y) => (f x, g y)) (combine l1 l2).
  Proof.
    revert l2.
    induction l1; intros l2; simpl; trivial.
    destruct l2; simpl; trivial.
    f_equal.
    auto.
  Qed.

Lemma Cmult_combine_conv (cl1 cl2 : list C) :
  map (fun '(a, b) => (a * b)%C) (combine (map Cconj cl1) (map Cconj cl2)) =
    map Cconj (map (fun '(a, b) => (a * b)%C) (combine cl1 cl2)).
Proof.
  rewrite combine_map.
  do 2 rewrite map_map.
  apply map_ext.
  intros.
  destruct a.
  now rewrite Cmult_conj.
Qed.
  
Lemma map_mult_conj_rev (cl1 cl2 : list C):
  map Cconj cl1 = rev cl1 ->
  map Cconj cl2 = rev cl2 ->
  length cl1 = length cl2 ->
  let cl := map (fun '(a,b) => Cmult a b) (combine cl1 cl2) in
  map Cconj cl = rev cl.
Proof.
  intros.
  assert (combine (map Cconj cl1) (map Cconj cl2) =
            combine (rev cl1) (rev cl2)).
  {
    now rewrite H, H0.
  }
  apply (f_equal (fun ll => map (fun '(a, b) => (a * b)%C) ll)) in H2.
  now rewrite Cmult_combine_rev, Cmult_combine_conv in H2.
Qed.

Search Cconj.

Lemma map_pow_conj_rev (cl : list C) (n : nat) :
  map Cconj cl = rev cl ->
  map Cconj (map (fun c => Cpow c n) cl) = 
    rev (map (fun c => Cpow c n) cl).
Proof.
  intros.
  apply (f_equal (fun ll => map (fun cc => Cpow cc n) ll)) in H.
  rewrite map_map in H.
  rewrite map_rev in H.
  rewrite <- H.
  rewrite map_map.
  apply map_ext.
  intros.
  now rewrite Cpow_conj.
Qed.

Lemma odd_nth_roots_conj_rev n :
  let cl := map Cconj (odd_nth_roots (S n)) in
  map Cconj cl = rev cl.
Proof.
  Admitted.

Lemma encode_real (cl : list C) (n : nat):
  map Cconj cl = rev cl ->
  length cl = length (odd_nth_roots (S n)) ->
  forall (x : C),
    In x (encode cl (S n)) -> Im x = 0%R.
Proof.
  intros.
  unfold encode in H1.
  apply in_map_iff in H1.
  destruct H1 as [? [? ?]].
  apply in_map_iff in H2.
  destruct H2 as [? [? ?]].  
  assert (Im x0 = 0%R).
  {
    rewrite <- H2.
    unfold Cinner_prod.
    apply list_Cplus_conj_rev.
    apply map_mult_conj_rev; trivial.
    - apply map_pow_conj_rev.
      apply odd_nth_roots_conj_rev.
    - now do 2 rewrite map_length.
  }
  rewrite <- H1.
  apply Im_div_real; trivial.
  apply pow_nonzero.
  lra.
Qed.
  
Lemma encode_decode (cl : list C) (n : nat):
  map Cconj cl = rev cl ->
  length cl = length (odd_nth_roots (S n)) ->
  decode (map Re (encode cl n)) n = cl.
Proof.
  intros.
  unfold encode.
  Admitted.

Lemma encode_half_correct (cl : list C) (n : nat):
    map Cconj cl = rev cl ->
    encode_half cl n = map Re (encode cl (S n)).
Proof.
  intros.
  unfold encode_half, encode.
  rewrite map_map.
  rewrite map_map.
  rewrite map_map.
  Admitted.

Lemma Cplus_conj (c : C) :
  Cplus c (Cconj c) = (2 * Re c)%R.
Proof.
  destruct c.
  simpl.
  unfold Cconj, RtoC, Cplus, fst, snd.
  f_equal; lra.
Qed.

(* claim (nxn vandermonde on odd roots) x conjugate transpose = n * I. *)

Lemma mult_conj_root j n :
  Cmult (nth_root j (S n)) (Cconj (nth_root j (S n))) = 1%R.
Proof.
  rewrite nth_root_conj.
  rewrite Cinv_r; trivial.
  apply nth_root_not_0.
Qed.


