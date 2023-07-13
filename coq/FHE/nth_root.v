Require Import Reals Lra Lia List.
From mathcomp Require Import ssrbool choice Rstruct complex.
Import ssralg.GRing.

Set Bullet Behavior "Strict Subproofs".

Lemma S_INR_not_0 n :
  INR (S n) <> 0%R.
Proof.
  rewrite S_INR.
  generalize (pos_INR n).
  lra.
Qed.

(* represent complex number as pair *)
Definition nth_root (j n : nat) : R[i] :=
  let c := (2*PI*INR(j)/INR(n))%R in 
  ((cos c) +i* (sin c))%C.

Local Open Scope ring_scope.
Delimit Scope complex_scope with C.
Local Open Scope complex_scope.

Definition RtoC (x : R) := Complex x R0.
Definition C1 := Complex R1 R0.
Definition C0 := Complex R0 R0.
Definition C := ComplexField.complex_ringType R_fieldType.
Definition Cplus (x y : R[i]) := add x y.
Definition Cmult (x y : R[i]) := mul x y.


Lemma nth_root_0 n :
  nth_root 0 (S n) = C1.
Proof.
  unfold nth_root.
  assert ((2 * PI * INR 0 / INR (S n))%R = 0%R).
  {
    unfold INR at 1.
    field.
    apply S_INR_not_0.
  }
  rewrite H.
  now rewrite cos_0; rewrite sin_0.
Qed.

Lemma nth_root_2PI n j :
  nth_root (j * (S n)) (S n) = C1.
Proof.
  unfold nth_root.
  rewrite mult_INR.
  replace (2 * PI * (INR j * INR (S n)) / INR (S n))%R with
    (0 + 2 * INR(j) * PI)%R.
  - rewrite cos_period.
    rewrite sin_period.
    now rewrite cos_0; rewrite sin_0.
  - field.
    apply S_INR_not_0.
Qed.

Lemma nth_root_2PI_plus n j k :
  nth_root (j + k * (S n)) (S n) = nth_root j (S n).
Proof.
  unfold nth_root.
  replace (2 * PI * INR (j + k * S n) / INR (S n))%R with
    (2 * PI * INR(j)/INR(S n) + 2 * INR k * PI)%R.
  - now rewrite cos_period; rewrite sin_period.
  - rewrite plus_INR; rewrite mult_INR.
    field.
    apply S_INR_not_0.
 Qed.

Definition nth_roots (n:nat) :=
  map (fun j => nth_root j n) (seq 0 n).

(*
Fixpoint Cpow (x : R[i]) (n : nat) : R[i] :=
  match n with
  | 0 => C1
  | S n' => ComplexField.mulc x (Cpow x n')
  end.

Lemma Cpow_exp (x : R[i]) (n : nat) :
  Cpow x n = exp x n.
Proof.
  rewrite <- iter_mulr_1.
  induction n.
  - simpl.
    unfold one, Ring.one; simpl.
    unfold one, Ring.one; simpl.
    unfold C1.
    unfold real_complex_def.
    unfold zero; simpl.
    f_equal.
  - simpl.
    rewrite IHn.
    now unfold mul, Ring.mul; simpl.
Qed.
 *)

Definition Cpow (x : R[i]) (n : nat) : R[i] := exp x n.
Lemma Cpow_exp (x : R[i]) (n : nat) :
  Cpow x n = exp x n.
Proof.
  now unfold Cpow.
Qed.

Lemma de_moivre (x : R) (n : nat) :
  exp (cos x +i* sin x) n = (cos ((INR n) * x) +i* sin ((INR n) * x)).
Proof.
  rewrite <- iter_mulr_1.
  induction n.
  - simpl.
    rewrite Rmult_0_l.
    now rewrite cos_0; rewrite sin_0.
  - replace (INR (S n) * x)%R with (x + (INR n) * x)%R.
    + simpl.
      simpl in IHn.
      rewrite IHn.
      unfold mul; simpl.
      unfold add; simpl.
      unfold opp; simpl.
      unfold mul; simpl.
      rewrite cos_plus, sin_plus.
      f_equal.
      lra.
    + rewrite S_INR; lra.
  Qed.

Lemma Cpow_nth_root j n e :
  Cpow (nth_root j (S n)) e = nth_root (e * j) (S n).
Proof.
  unfold nth_root, Cpow.
  rewrite de_moivre.
  rewrite mult_INR.
  do 2 f_equal; field; apply S_INR_not_0.
Qed.

Lemma Cpow_nth_root_comm j n e :
  Cpow (nth_root j (S n)) e = Cpow (nth_root e (S n)) j.
Proof.
  do 2 rewrite Cpow_nth_root.
  f_equal.
  apply ssrnat.mulnC.
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
  - rewrite Minus.not_le_minus_0_stt; trivial.
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
      rewrite minus_mod in H0; lia.
    }
    destruct H0.
    rewrite H0.
    now rewrite nth_root_2PI_plus.
 Qed.

Lemma prim_nth_root j n :
  nth_root j (S n) = Cpow (nth_root 1 (S n)) j.
Proof.
  rewrite Cpow_nth_root.
  f_equal.
  lia.
 Qed.

Lemma nth_root_not_0 j n :
  nth_root j (S n) <> RtoC R0.
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
  - apply (f_equal (fun c => Re c)) in H0.
    now unfold Re in H0.
  - apply (f_equal (fun c => Im c)) in H0.
    now unfold Im in H0.
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
  nth_root j (S n) <> RtoC R1.
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
  nth_root j (S n) = RtoC R1.
Proof.
  intros.
  rewrite (nth_root_mod j 0 n).
  - now rewrite nth_root_0.
  - rewrite H.
    rewrite Nat.mod_small; lia.
Qed.

Lemma nth_root_1_iff  n j :
  nth_root j (S n) = C1 <-> j mod (S n) = 0.
Proof.
  rewrite <- (nth_root_0 n).
  rewrite <- nth_root_eq.
  replace (0 mod S n) with 0; try easy.
  rewrite Nat.mod_small; lia.
Qed.

Lemma pow_nth_root_prim n :
  Cpow (nth_root 1 (S n)) (S n) = RtoC R1.  
Proof.
  unfold nth_root, Cpow.
  rewrite de_moivre.
  replace (INR (S n) * (2 * PI * INR 1 / INR (S n)))%R with (2 * PI)%R.
  - now rewrite cos_2PI, sin_2PI.
  - replace (INR 1) with R1 by now unfold INR.
    field.
    apply S_INR_not_0.
Qed.

Lemma pow_nth_root_prim_exp n :
  exp (nth_root 1 (S n)) (S n) = RtoC R1.  
Proof.
  rewrite <- Cpow_exp.
  apply pow_nth_root_prim.
Qed.

Lemma pow_nth_root j n :
  Cpow (nth_root j (S n)) (S n) = RtoC R1.
Proof.
  unfold Cpow.
  rewrite prim_nth_root.
  unfold Cpow.
  rewrite <- exprM.
  rewrite ssrnat.mulnC.
  rewrite exprM.
  rewrite pow_nth_root_prim_exp.
  now rewrite expr1n.
Qed.

Lemma nth_root_mul j k n :
  Cmult (nth_root j (S n)) (nth_root k (S n)) = nth_root (j + k) (S n).
Proof.
  intros.
  rewrite (prim_nth_root k _).
  rewrite (prim_nth_root j _).
  rewrite (prim_nth_root (j + k) _).
  unfold Cpow, Cmult.
  now rewrite <- exprD.
 Qed.

Lemma nth_root_Sn n :
  nth_root (S n) (S n) = RtoC 1%R.
Proof.
  rewrite prim_nth_root.
  now rewrite nth_root_npow.
Qed.

Definition Cinv (x : R[i]) := inv x.
Definition Cdiv (x y : R[i]) := mul x (inv y).

Lemma Cinv_1_r :
  Cinv C1 = RtoC 1%R.
Proof.
  unfold Cinv.
  unfold RtoC.
  now rewrite Theory.invr1.
Qed.

Lemma Cinv_r (x : R[i]) :
  x <> C0 ->
  Cmult x (Cinv x) = C1.
Proof.
  intros.
  unfold Cmult, Cinv, C1.
  etransitivity; [etransitivity |]; [| apply (@divff _ x) |]; try reflexivity.
  match goal with
    | [|- context [negb ?x] ] => case_eq x
  end; intros HH; simpl; trivial.
  elim H.
  vm_compute in HH.
  destruct x.
  now destruct (Req_EM_T Re R0); destruct (Req_EM_T Im R0); subst; try discriminate.
Qed.  

Lemma Cinv_l (x : R[i]) :
  x <> C0 ->
  Cmult (Cinv x) x = C1.
Proof.
  intros.
  unfold Cmult, Cinv, C1.
  etransitivity; [etransitivity |]; [| apply (@mulrC _ (inv x) x) |]; try reflexivity.
  now apply Cinv_r.
Qed.  


Lemma Cpow_sub_r (c : R[i]) (n m : nat):
  m <= n ->
  c <> C0 ->
  Cpow c (n - m) = Cdiv (Cpow c n) (Cpow  c m).
Proof.
  intros.
  assert (Cmult (Cpow c (n - m)) (Cpow c m) = Cpow c n).
  {
    unfold Cpow, Cmult.
    rewrite <- exprD.
    f_equal.
    unfold ssrnat.addn, ssrnat.addn_rec.
    lia.
  }
  rewrite <- H1.
  unfold Cdiv, Cmult.
  rewrite <- mulrA.
  assert (Cpow c m <> C0).
  {
    unfold Cpow.
    generalize Theory.expf_neq0; intros.
    assert (is_true (negb (eqtype.eq_op c C0))).
    {
      vm_compute.
      destruct c.
      now destruct (Req_EM_T Re R0); destruct (Req_EM_T Im R0); subst; try discriminate.
    }
    generalize (Theory.expf_neq0 m H3); intros.
    vm_compute in H4.
    vm_compute.
    destruct ((fix Ffix (x : nat) : R[i] :=
                match x with
                | 0 => R1 +i* R0
                | 1 => c
                | S (S _ as x0) =>
                    match c with
                    | Re +i* Im =>
                        match Ffix x0 with
                        | Re0 +i* Im0 => (Re * Re0 + - (Im * Im0))%R +i* (Re * Im0 + Im * Re0)%R
                        end
                    end
                end) m).
    intros HH.
    inversion HH; subst.
    destruct (Req_EM_T R0 R0); destruct (Req_EM_T R0 R0); subst; congruence.
  }
  generalize (Cinv_r (Cpow c m) H2); intros.
  unfold Cmult, Cinv in H3.
  rewrite H3.
  unfold C1.
  now rewrite mulr1.
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

Lemma nth_root_inv j n :
  Cinv (nth_root j (S n)) = nth_root (S n - (j mod S n)) (S n).
Proof.
  generalize (nth_root_diff (j mod S n) (S n) n); intros.
  rewrite <- H.
  - rewrite nth_root_Sn.
    unfold Cdiv, Cinv.
    rewrite mul1r.
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

Definition Cconj (x : R[i]) := conjc x.

Definition Cmod (x : R[i]) := (* ComplexField.Normc.normc. *)
  let: a +i* b := x in sqrt (exp a 2 + exp b 2).

Lemma nth_root_Cmod j n :
  Cmod (nth_root j (S n)) = 1%R.
Proof.
  unfold Cmod, nth_root, fst, snd.
  rewrite Rplus_comm.
  rewrite <- sqrt_1.
  f_equal.
  do 2 rewrite <- RpowE.
  do 2 rewrite <- Rsqr_pow2.
  now rewrite sin2_cos2.
Qed.

Lemma Cmod_Cconj (c : R[i]) :
  Cmult c (Cconj c) = RtoC (Rsqr (Cmod c)).
Proof.
  unfold Cconj, Cmod, Cmult, fst, snd, RtoC.
  destruct c.
  do 2 rewrite <- RpowE.    
  rewrite Rsqr_sqrt.
  - unfold RtoC.
    unfold mul, Ring.mul; simpl.
    unfold add, mul, opp; simpl.
    f_equal; lra.
  - apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

Lemma nth_root_conj j n :
  Cconj (nth_root j (S n)) = Cinv (nth_root j (S n)).
Proof.
  generalize (Cmod_Cconj (nth_root j (S n))); intros.
  rewrite nth_root_Cmod in H.
  rewrite Rsqr_1 in H.
  apply (f_equal (fun c => Cmult (Cinv (nth_root j (S n))) c)) in H.
  unfold Cmult, RtoC in H.
  rewrite mulr1 in H.
  rewrite mulrA in H.
  rewrite Cinv_l in H.
  - now rewrite mul1r in H.
  - apply nth_root_not_0.
Qed.

Lemma nth_root_conj_alt j n :
  Cconj (nth_root j (S n)) = nth_root (S n - j mod (S n)) (S n).
Proof.
  rewrite nth_root_conj.
  now rewrite nth_root_inv.
Qed.

Lemma nth_root_half_pow_aux n :
  Cpow (nth_root (S n) (2 * (S n))) 2 = C1.
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

Lemma Cpow_2 (c : R[i]) :
  Cpow c 2 = C1 -> c = C1 \/ c = opp C1.
Proof.
  unfold Cpow.
  rewrite expr2.
  intros.
  destruct c.
  unfold mul in H; simpl in H.
  unfold add in H; simpl in H.
  unfold mul, opp in H; simpl in H.
  unfold C1, RtoC in H.
  injection H; intros; clear H.
  ring_simplify in H0.
  apply (f_equal (fun z => (/2 * z)%R)) in H0.
  do 2 rewrite <- Rmult_assoc in H0.
  rewrite <- Rinv_l_sym in H0; try lra.
  rewrite Rmult_1_l, Rmult_0_r in H0.
  apply Rmult_integral in H0.
  destruct H0; subst; ring_simplify in H1.
  - assert (0 <= Im ^ 2)%R by apply pow2_ge_0.
    lra.
  - apply pow2_inv in H1.
    rewrite sqrt_1 in H1.
    apply Rabs_pm_r in H1.
    unfold C1, RtoC.
    unfold opp; simpl.
    unfold opp; simpl.
    destruct H1; [left|right]; f_equal; lra.
Qed.

Lemma nth_root_half_pow n :
  nth_root (S n) (2 * (S n)) = opp C1.
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

Lemma odd_roots_prim j n :
  Cpow (nth_root (2 * j + 1) (2 ^ (S n))) (2^n) = opp C1.
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

Lemma mult_conj_root j n :
  Cmult (nth_root j (S n)) (Cconj (nth_root j (S n))) = C1.
Proof.
  rewrite nth_root_conj.
  rewrite Cinv_r; trivial.
  apply nth_root_not_0.
Qed.

Lemma nth_root_half n :
  nth_root (2 ^n) (2 ^ (S n)) = opp C1.
Proof.
  destruct (pow2_S (S n)).
  generalize (odd_roots_prim 0 n); intros.
  replace (2 * 0 +1) with 1 in H by lia.
  rewrite H in H0.
  rewrite Cpow_nth_root in H0.
  rewrite <- H in H0.
  now replace (2^n * (2 * 0 + 1)) with (2 ^ n) in H0 by lia.
Qed.

Lemma nth_root_opp j n :
  add (nth_root j (2 ^ (S n))) (nth_root (j + 2^n) (2 ^ (S n))) = C0.
Proof.
  destruct (pow2_S (S n)).
  rewrite H.
  rewrite <- nth_root_mul.
  rewrite <- H.
  rewrite nth_root_half.
  unfold Cmult, C0, C1.
  rewrite mulrN1.  
  rewrite addrC.
  rewrite addNr.
  reflexivity.
Qed.

