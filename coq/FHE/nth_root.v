Require Import Reals Lra Lia List.
From mathcomp Require Import complex ssreflect common eqtype ssrint ssrnat Rstruct.
Import ssralg.GRing.
Import ssralg.

Ltac coq_lra := lra.

From mathcomp Require Import lra.

Set Bullet Behavior "Strict Subproofs".

Lemma S_INR_not_0 n :
  INR (S n) <> Rdefinitions.R0.
Proof.
  rewrite S_INR.
  generalize (pos_INR n).
  coq_lra.
Qed.

Lemma S_INR_n0 n : is_true (INR (S n) != (zero R_ringType)).
Proof.
  intros.
  move: (S_INR_not_0 n) => HH.
  by case eqP.
Qed.

(* represent complex number as pair *)
Definition nth_root (j n : nat) : R[i] :=
  let c := (2*PI*INR(j)/INR(n))%R in 
  ((cos c) +i* (sin c))%C.

Local Open Scope ring_scope.
Delimit Scope complex_scope with C.
Local Open Scope complex_scope.

Definition RtoC (x : R) := Complex x Rdefinitions.R0.
Definition C1 := Complex R1 Rdefinitions.R0.
Definition C0 := Complex Rdefinitions.R0 Rdefinitions.R0.
Definition C := ComplexField.complex_ringType R_fieldType.

Lemma nth_root_0 n :
  nth_root 0 (S n) = 1.
Proof.
  unfold nth_root.
  assert ((2 * PI * INR 0 / INR (S n))%R = 0%R).
  {
    unfold INR at 1.
    by rewrite mulr0 mul0r.
  }
  by rewrite H /zero /= cos_0 sin_0.
Qed.

Lemma nth_root_2PI n j :
  nth_root (j * (S n)) (S n) = 1.
Proof.
  unfold nth_root.
  replace (2 * PI * INR (j * S n) / INR (S n))%R with
    (0 + 2 * (INR j) * PI)%R.
  - by rewrite cos_period sin_period /zero /= cos_0 sin_0.
  - rewrite add0r mult_INR -mulrA -mulrA.
    rewrite (mulrC _ PI) -(mulrA 2 _).
    f_equal.
    f_equal.
    rewrite -mulrA divff.
    + by rewrite mulr1.
    + by apply S_INR_n0.
Qed.

Lemma nth_root_2PI_plus n j k :
  nth_root (j + k * (S n)) (S n) = nth_root j (S n).
Proof.
  unfold nth_root.
  replace (2 * PI * INR (j + k * S n) / INR (S n))%R with
    (2 * PI * INR(j)/INR(S n) + 2 * INR k * PI)%R.
  - now rewrite cos_period; rewrite sin_period.
  - rewrite plus_INR; rewrite mult_INR.
    rewrite (mulrDr (2 * PI) _ _) mulrDl.
    f_equal.
    rewrite -mulrA (mulrC _ PI) -mulrA -mulrA.
    f_equal.
    f_equal.
    rewrite -mulrA divff.
    + by rewrite mulr1.
    + by apply S_INR_n0.
Qed.

Definition nth_roots (n:nat) :=
  map (fun j => nth_root j n) (seq 0 n).


Lemma de_moivre (x : R) (n : nat) :
  exp (cos x +i* sin x) n = (cos ((INR n) * x)%R +i* sin ((INR n) * x)%R).
Proof.
  rewrite /mul /= -iter_mulr_1.
  induction n.
  - simpl.
    rewrite Rmult_0_l.
    now rewrite cos_0; rewrite sin_0.
  - simpl iter.
    rewrite IHn S_INR Rmult_plus_distr_r Rmult_1_l.
    rewrite cos_plus sin_plus /= /mul /=.
    rewrite /mul /add /opp /=.
    f_equal; ring.
  Qed.

Lemma exp_nth_root j n e :
  exp (nth_root j (S n)) e = nth_root (e * j) (S n).
Proof.
  unfold nth_root.
  rewrite de_moivre mult_INR.
  assert ((INR e * (2 * PI * INR j / INR n.+1)%R)%R = 2 * PI * (INR e * INR j)%R / INR n.+1).
  {
    replace (S n) with (n + 1)%nat by lia.
    unfold mul, inv; simpl.
    field.
  }
  by rewrite -H.
Qed.

Lemma exp_nth_root_comm j n e :
  exp (nth_root j (S n)) e = exp (nth_root e (S n)) j.
Proof.
  do 2 rewrite exp_nth_root.
  f_equal.
  apply mulnC.
Qed.

Lemma nth_root_npow j n :
  exp (nth_root j (S n)) (S n) = 1.
Proof.
  by rewrite exp_nth_root mulnC nth_root_2PI.
Qed.

Lemma minus_mod (j1 j2 n : nat) :
  j1 mod (S n) = j2 mod (S n) ->
  (j2 - j1) mod (S n) = 0%nat.
Proof.
  intros eqq1.
  destruct (le_dec j1 j2).
  - generalize (Zdiv.Zminus_mod (Z.of_nat j2) (Z.of_nat j1) (Z.of_nat (S n)))
    ; intros HH.
    rewrite <- Nat2Z.inj_sub in HH by trivial.
    repeat rewrite <- Nat2Z.inj_mod in HH.
    rewrite -eqq1 Z.sub_diag Zdiv.Zmod_0_l in HH.
    apply (f_equal Z.to_nat) in HH.
    now rewrite Nat2Z.id in HH.
  - unfold subn, subn_rec.
    rewrite Minus.not_le_minus_0_stt; trivial.
    now apply Nat.mod_0_l.
Qed.    

Lemma nth_root_mod j1 j2 n :
  j1 mod (S n) = j2 mod (S n) ->
  nth_root j1 (S n) = nth_root j2 (S n).
Proof.
  intros.
  destruct (le_dec j1 j2).
  - assert (exists (k:nat), (j2 = j1 + k * (S n))%N).
    {
      generalize (Nat.div_mod_eq (j2 - j1) (S n)); intros.
      exists ((j2 - j1)/(S n))%N.
      rewrite minus_mod in H0; trivial; lia.
    }
    destruct H0.
    rewrite H0.
    now rewrite nth_root_2PI_plus.
  - assert (exists (k:nat), (j1 = j2 + k * (S n))%N).
    {
      generalize (Nat.div_mod_eq (j1 - j2) (S n)); intros.
      exists ((j1 - j2)/(S n))%N.
      rewrite minus_mod in H0; lia.
    }
    destruct H0.
    rewrite H0.
    now rewrite nth_root_2PI_plus.
 Qed.

Lemma prim_nth_root j n :
  nth_root j (S n) = exp (nth_root 1 (S n)) j.
Proof.
  rewrite exp_nth_root.
  f_equal.
  lia.
 Qed.

Lemma nth_root_not_0 j n :
  nth_root j (S n) <> 0.
Proof.
  rewrite /nth_root.
  generalize (cos_sin_0 (2 * PI * INR j / INR (S n))%R); intros.
  intros ?.
  apply H.
  split.
  - by apply (f_equal (fun c => Re c)) in H0.
  - by apply (f_equal (fun c => Im c)) in H0.
 Qed.

Lemma cos1_sin0 (x : R) :
  cos x = 1 ->
  sin x = 0.
Proof.
  intros eqq1.
  generalize (cos2 x).
  rewrite eqq1; intros eqq2.
  rewrite Rsqr_1 in eqq2.
  apply Rsqr_0_uniq.
  coq_lra.
Qed.  

Section sin_cos.
  Local Open Scope R_scope.

Lemma cosneg1_sin0 (x : R) :
  cos x = - 1 ->
  sin x = 0.
Proof.
  intros eqq1.
  generalize (cos2 x).
  rewrite eqq1; intros eqq2.
  rewrite -Rsqr_neg Rsqr_1 in eqq2.
  apply Rsqr_0_uniq.
  coq_lra.
Qed.  

Lemma cos_sin0_alt (x : R) :
  sin x = 0 <->
    Rsqr(cos x) = 1.
Proof.
  split; intro eqq.
  - generalize (sin2_cos2 x); intros.
    rewrite eqq in H.
    rewrite Rsqr_0 in H.
    now rewrite Rplus_0_l in H.
  - generalize (sin2 x); intros.
    rewrite eqq in H.
    rewrite Rminus_eq_0 in H.
    now apply Rsqr_0_uniq in H.
Qed.

Lemma Rsqr_1_iff (x : R) :
  Rsqr x = 1 <->
    x = 1 \/ x = -1.
Proof.
  generalize (Rsqr_eq x 1); intros.
  rewrite Rsqr_1 in H.
  split; intros.
  - now apply H.
  - unfold Rsqr.
    destruct H0; rewrite H0; coq_lra.
Qed.      

Lemma cos_sin0 (x : R) :
  sin x = 0 <->
   cos x = 1 \/ cos x = -1.
Proof.
  split; intros.
  - apply cos_sin0_alt in H.
    now apply Rsqr_1_iff in H.
  - apply Rsqr_1_iff in H.
    now apply cos_sin0_alt in H.
Qed.    


Lemma cos_eq_1_aux_pos (x : R) :
  cos x = 1 ->
  exists k, x = (PI * IZR(k))%R.
Proof.
  intros eqq1.
  generalize (cos1_sin0 _ eqq1); intros eqq2.
  apply sin_eq_0_0 in eqq2.
  destruct eqq2 as [k eqqk].
  exists k.
  unfold mul; simpl; coq_lra.
Qed.

Lemma cos_eq_1_aux_neg (x : R) :
  cos x = - 1 ->
  exists k, x = (PI * IZR(k))%R.
Proof.
  intros eqq1.
  generalize (cosneg1_sin0 _ eqq1); intros eqq2.
  apply sin_eq_0_0 in eqq2.
  destruct eqq2 as [k eqqk].
  exists k.
  unfold mul; simpl; coq_lra.
Qed.

Lemma sin_eq_0_aux (x : R) :
  sin x = 0 ->
  exists k, x = (PI * IZR(k))%R.
Proof.
  intros.
  apply cos_sin0 in H.
  destruct H.
  - now apply cos_eq_1_aux_pos.
  - now apply cos_eq_1_aux_neg.
Qed.

Lemma cos_eq_1_1 :
  forall k:Z,
    cos (IZR k * 2 * PI)%R = 1.
Proof.
  intros k.
  assert (forall n, cos (INR n * 2 * PI) = 1%R). {
    intros n;induction n as [|n IHn].
    { change (INR 0) with Rdefinitions.R0.
      rewrite !Rmult_0_l.
      exact cos_0. }
    rewrite S_INR !Rmult_plus_distr_r cos_plus IHn.
    rewrite !Rmult_1_l cos_2PI sin_2PI Rmult_0_r Rminus_0_r.    
    reflexivity.
  }
  destruct (Z.abs_or_opp_abs k).
  - replace (IZR k) with (INR (Z.to_nat k)).
    { apply H. }
    rewrite INR_IZR_INZ.
    f_equal.
    apply Z2Nat.id.
    lia.
  - replace (IZR k) with (- INR (Z.to_nat (- k)))%R.
    + by rewrite mulNr mulNr cos_neg H.
    + rewrite INR_IZR_INZ.
      rewrite <-opp_IZR. f_equal.
      lia.
Qed.

Lemma cos_lt_1 (x : R) :
  0 < x ->
  x < 2*PI ->
  cos x < 1.
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
    rewrite H4 mulrC /mul /= in H0.
    apply Rmult_lt_reg_r in H0; trivial.
    rewrite H4 in H.
    replace (IZR Z0) with (Rmult PI 0)%R in H by coq_lra.
    rewrite /mul /= in H.
    apply Rmult_lt_reg_l in H; trivial.
    assert (x0 = Z.one).
    {
      apply lt_IZR in H.
      apply lt_IZR in H0.
      unfold Z.one.
      lia.
    }
    rewrite H5 /Z.one /IZR /IPR mulr1 in H4.
    rewrite H4 cos_PI /one /= in H3.
    coq_lra.
  }
  rewrite /one /= in H3.
  coq_lra.
 Qed.

Lemma cos_eq_1 (x : R) :
  cos x = 1 ->
  exists (k:Z), x = (2 * PI * IZR(k))%R.
Proof.
  intros Hx.
  assert (PI2_neq0: (2 * PI <> 0)%R).
  {
    generalize PI_neq0.
    unfold mul, one, zero, natmul, add; simpl.
    coq_lra.
  }
  destruct (euclidian_division x (2*PI) PI2_neq0) as (q & r & EQ & Hr & Hr').
  exists q.
  rewrite <- (Rplus_0_r (_*_)). subst.
  rewrite Rmult_comm.
  apply Rplus_eq_compat_l.
  rewrite cos_plus in Hx.
  assert (H : cos (IZR q * 2 * PI)%R = 1%R) by ( apply cos_eq_1_1; now exists q).
  rewrite -Rmult_assoc H /one /= Rmult_1_l sin_eq_0_1 in Hx.
  - rewrite Rmult_0_l Rminus_0_r in Hx.
    rewrite Rabs_right in Hr'.
    + destruct Hr as [Hr | ->]; trivial.
      exfalso.
      generalize (cos_lt_1 r Hr Hr'); intros.
      coq_lra.
    + generalize PI_RGT_0; coq_lra.
  - exists (Z.mul 2 q).
    rewrite mult_IZR.
    coq_lra.
 Qed.

Lemma cos_eq_neg1 (x : R) :
  cos x = -1 ->
  exists k, x = (2 * PI * IZR(k) + PI)%R.
Proof.
  intros eqq1.
  generalize (Rtrigo_facts.cos_pi_plus x); intros eqq2.
  rewrite eqq1 in eqq2.
  rewrite Ropp_involutive in eqq2.
  apply cos_eq_1 in eqq2.
  destruct eqq2 as [k eqq2].
  exists (Z.sub k 1)%Z.
  rewrite minus_IZR.
  replace (Rplus PI x) with (PI + x)%R in eqq2.
  - replace (Rminus (IZR k) 1) with ((IZR k) - 1)%R.
    + lra.
    + unfold add, opp, one; simpl; coq_lra.
  - unfold add; simpl; coq_lra.
Qed.

Lemma cos_eq_1_nneg (x : R) :
  cos x = 1 ->
  0 <= x ->
  exists (k:nat), x = (2 * PI * INR(k))%R.
Proof.
  intros.
  generalize (cos_eq_1 x H); intros.  
  destruct H1.
  rewrite H1 in H0.
  replace (IZR Z0) with (2 * PI * 0)%R in H0.
  - apply Rmult_le_reg_l in H0.
    + unfold zero in H0; simpl in H0.
      apply le_IZR in H0.
      exists (Z.abs_nat x0).
      rewrite H1.
      do 2 f_equal.
      destruct x0; simpl; trivial; try lia.
      now rewrite INR_IPR.
    + unfold mul, one, natmul, add; simpl.
      generalize PI_RGT_0; coq_lra.
  - by rewrite mulr0.
Qed.

Lemma sin_cos_eq x y:
  sin x = sin y /\ cos x = cos y ->
  exists (k:Z),
    x = (y + 2 * PI * IZR(k))%R.
Proof.
  intros.
  generalize (cos_minus x y); intros.
  destruct H.
  rewrite H H1 in H0.
  generalize (sin2_cos2 y); intros.
  rewrite Rplus_comm in H0.
  unfold Rsqr in H2.
  rewrite H2 in H0.
  apply cos_eq_1 in H0.
  destruct H0.
  exists x0.
  rewrite <- H0.
  unfold add; simpl.
  coq_lra.
Qed.

Lemma Pi2_neq0 :
  (2 * PI <> 0)%R.
Proof.
  generalize PI_neq0.
  unfold mul, one, zero, natmul, add; simpl.
  coq_lra.
Qed.

Lemma Pi2_neq0_alt :
  is_true (2 * PI != 0).
Proof.
  generalize Pi2_neq0.
  by case eqP.
Qed.

End sin_cos.

Lemma nth_root_eq j k n :
  j mod (S n) = k mod (S n) <->
  nth_root j (S n) = nth_root k (S n).
Proof.
  split; intros. 
  - now apply nth_root_mod.
  - unfold nth_root in H.
    replace (S n) with (addn n 1) in H by lia.
    inversion H; clear H.
    pose (jj := (2 * PI * INR j)/ (INR (addn n 1))).
    pose (kk := (2 * PI * INR k)/ (INR (addn n 1))).    
    generalize (sin_cos_eq jj kk); intros.
    destruct H.
    + split; trivial.
    + unfold jj, kk in H.
      clear H1 H2 jj kk.
      replace  (2 * PI * INR k / INR (addn n 1) + 2 * PI * IZR x)%R with
        (2 * PI * (INR k / INR (addn n 1) + IZR x))%R in H by lra.
      replace  (2 * PI * INR j / INR (addn n 1))%R with
         (2 * PI * (INR j / INR (addn n 1)))%R in H by lra.
      apply (f_equal (fun r => (inv (2 * PI)) * r))%R in H.
      generalize Pi2_neq0_alt; intros.
      rewrite mulrDr -(mulrA _ (INR k) _) !(mulrA _ (2 * PI) _) (mulrC _ (2 * PI)) divff in H; trivial.
      rewrite !mul1r in H.
      apply (f_equal (fun r => r * (INR (addn n 1)))) in H.
      replace (addn n 1) with (S n) in H by lia.
      generalize (S_INR_n0 n); intros.
      rewrite mulrDl -!mulrA !(mulrC _ (INR (S n))) divff in H; trivial.
      rewrite !mulr1 mulrC !INR_IZR_INZ in H.
      repeat rewrite <- mult_IZR in H.
      repeat rewrite <- plus_IZR in H.
      apply eq_IZR in H.
      apply Nat2Z.inj.
      rewrite !Nat2Z.inj_mod H.
      transitivity (Z.modulo (Z.add (Z.of_nat k) (Z.mul x (Z.of_nat (S n)))) (Z.of_nat (S n))).
      * by f_equal.
      * by rewrite Zdiv.Z_mod_plus_full.
Qed.

Lemma nth_root_pow_eq (n j k : nat) :
  0%N <> n ->
  forall (e1 e2 : nat),
    (nth_root j n) ^+ e1 = 
    (nth_root k n) ^+ e2 <->
      (e1 * j) mod n = (e2 * k) mod n.
Proof.
  intros.
  destruct n; try lia.
  by rewrite !exp_nth_root -nth_root_eq.
Qed.

Lemma nth_root_1_iff  n j :
  nth_root j (S n) = 1 <-> j mod (S n) = 0%N.
Proof.
  rewrite <- (nth_root_0 n).
  rewrite <- nth_root_eq.
  replace (0 mod S n) with 0%N; try easy.
  rewrite Nat.mod_small; lia.
Qed.

Lemma nth_root_not_1 j n :
  j mod (S n) <> 0%N ->
  nth_root j (S n) <> 1.
Proof.
  intros ??.
  rewrite nth_root_1_iff in H0.
  by rewrite H0 in H.
Qed.

Lemma pow_nth_root_prim n :
  exp (nth_root 1 (S n)) (S n) = 1.  
Proof.
  unfold nth_root.
  rewrite de_moivre.
  replace (INR n.+1 * (2 * PI * INR 1 / INR n.+1)%R) with (2 * PI)%R.
  - by rewrite cos_2PI sin_2PI.
  - rewrite [INR 1]INRE mulr1.
    rewrite [INR n.+1 * _]mulrC.
    rewrite -!mulrA mulVf ?mulr1//.
    replace (zero (Field.zmodType R_fieldType)) with (INR 0) by trivial.
    by rewrite !INRE ssrnum.Num.Theory.eqr_nat.
Qed.

Lemma pow_nth_root j n :
  exp (nth_root j (S n)) (S n) = 1.
Proof.
  by rewrite prim_nth_root -exprM mulnC exprM pow_nth_root_prim expr1n.
Qed.

Lemma nth_root_mul j k n :
  mul (nth_root j (S n)) (nth_root k (S n)) = nth_root (j + k) (S n).
Proof.
  intros.
  rewrite (prim_nth_root k _).
  rewrite (prim_nth_root j _).
  rewrite (prim_nth_root (j + k) _).
  now rewrite <- exprD.
 Qed.

Lemma nth_root_Sn n :
  nth_root (S n) (S n) = 1.
Proof.
  by rewrite prim_nth_root nth_root_npow.
Qed.

Lemma Cinv_r (x : R[i]) :
  x <> 0 ->
  x * (inv x) = 1.
Proof.
  intros.
  rewrite divff //.
  by case eqP.
Qed.  

Lemma Cinv_l (x : R[i]) :
  x <> 0 ->
  (inv x) * x = 1.
Proof.
  intros.
  rewrite mulrC Cinv_r //.
Qed.  

Lemma exp_sub_r (c : R[i]) (n m : nat):
  (le m n) ->
  c <> 0 ->
  exp c (n - m) = (exp c n) / (exp  c m).
Proof.
  intros.
  destruct H.
  - rewrite subnn expr0 Cinv_r//.
    generalize (@expf_neq0 _ c m).
    case: eqP => //.
    case: eqP => //.
    intuition.
  - rewrite expfB//.
    case: leP => //.
    lia.
Qed.

Lemma nth_root_diff j k n :
  (le j k) ->
  (nth_root k (S n)) / (nth_root j (S n)) = nth_root (k-j) (S n).
Proof.
  intros.
  rewrite (prim_nth_root k _).
  rewrite (prim_nth_root j _).
  rewrite (prim_nth_root (k-j) _).
  rewrite exp_sub_r; trivial.
  apply nth_root_not_0.
Qed.

Lemma nth_root_inv j n :
  inv (nth_root j (S n)) = nth_root (S n - (j mod S n)) (S n).
Proof.
  generalize (nth_root_diff (j mod S n) (S n) n); intros.
  rewrite <- H.
  - rewrite nth_root_Sn mul1r.
    f_equal.
    apply (nth_root_mod j (j mod S n) n).
    rewrite Nat.mod_mod; try lia.
  - assert (S n <> 0%N) by lia.
    generalize (Nat.mod_upper_bound j (S n) H0); lia.
 Qed.
    
Lemma nth_root_div j k n :
  (nth_root j (S n)) / (nth_root k (S n)) = 
    nth_root (j + (S n - (k mod S n))) (S n).
Proof.
  rewrite nth_root_inv.
  apply nth_root_mul.
Qed.

Definition Cmod (x : R[i]) := (* ComplexField.Normc.normc. *)
  let: a +i* b := x in sqrt (exp a 2 + exp b 2).

Lemma nth_root_Cmod j n :
  Cmod (nth_root j (S n)) = 1%R.
Proof.
  unfold Cmod, nth_root, fst, snd.
  rewrite Rplus_comm /one /= -sqrt_1.
  f_equal.
  by rewrite -!RpowE -!Rsqr_pow2 sin2_cos2.
Qed.

Lemma Cmod_Cconj_alt (c : R[i]) :
  let: a +i* b :=c in
  c * (conjc c) = (a^+2 + b^+2) +i* 0.
Proof.
  destruct c.
  unfold mul; simpl.
  f_equal; lra.
Qed.

Lemma Cmod_Cconj (c : R[i]) :
  c * (conjc c) = RtoC (Rsqr (Cmod c)).
Proof.
  generalize (Cmod_Cconj_alt c); intros.
  unfold Cmod, fst, snd, RtoC.
  unfold RtoC in H.
  destruct c.
  rewrite H.
  f_equal.
  rewrite -!RpowE Rsqr_sqrt //.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

Lemma nth_root_conj j n :
  conjc (nth_root j (S n)) = inv (nth_root j (S n)).
Proof.
  generalize (Cmod_Cconj (nth_root j (S n))); intros.
  rewrite nth_root_Cmod Rsqr_1 in H.
  apply (f_equal (fun c => mul (inv (nth_root j (S n))) c)) in H.
  rewrite /RtoC mulr1 mulrA Cinv_l in H.
  - now rewrite mul1r in H.
  - by apply nth_root_not_0.
Qed.

Lemma nth_root_conj_alt j n :
  conjc (nth_root j (S n)) = nth_root (S n - j mod (S n)) (S n).
Proof.
  by rewrite nth_root_conj nth_root_inv.
Qed.

Lemma nth_root_half_pow_aux n :
  exp (nth_root (S n) (2 * (S n))) 2 = 1.
Proof.
  replace (muln 2 (S n)) with (S (2 * n + 1)) by lia.
  rewrite exp_nth_root.
  do 2 replace (muln 2 (S n)) with (S (2 * n + 1)) by lia.
  now rewrite nth_root_Sn.
Qed.

Lemma pow2_inv x y : (x ^+ 2)%R = y -> Rabs x = sqrt y.
Proof.
  intros eqq1.
  apply (f_equal sqrt) in eqq1.
  rewrite expr2 in eqq1.
  rewrite -eqq1 -sqrt_Rsqr_abs //.
Qed.

Lemma Rabs_pm_l x y : Rabs x = y -> x = y \/ (- x)%R = y.
Proof.
  unfold Rabs.
  destruct (Rcase_abs); [right|left]; rewrite -H //.
Qed.

Lemma Rabs_pm_r x y : Rabs x = y -> x = y \/ x = (- y)%R.
Proof.
  unfold Rabs.
  destruct (Rcase_abs); [right|left]; rewrite -H //.
  unfold opp; simpl.
  by rewrite Ropp_involutive.
Qed.

Lemma cmult_real (c : R[i]) :
  Im (c * c) = 0 <->
  Re c = 0 \/ Im c = 0.
Proof.
  destruct c.
  simpl.
  split; intros.
  - assert (Re * Im = 0) by lra.
    rewrite /mul /zero /= in H0.
    apply Rmult_integral in H0.
    by rewrite /zero /=.
  - destruct H; rewrite H; lra.
Qed.                  

Lemma Cpow_2 (c : R[i]) :
  exp c 2 = 1 -> c = 1 \/ c = - 1.
Proof.
  rewrite expr2; intros.
  assert (Im (c * c) = 0).
  {
    by rewrite H /=.
  }
  rewrite cmult_real in H0.
  destruct c.
  simpl in H0.
  destruct H0.
  - rewrite H0 /mul /= !mul0r mulr0 !add0r in H.
    injection H; intros.
    rewrite /mul /one /opp /= in H1.
    generalize (pow2_ge_0 Im); intros.
    rewrite /pow Rmult_1_r in H2.
    coq_lra.
  - rewrite H0 /mul /= !mul0r !mulr0 oppr0 !addr0 in H.
    rewrite H0.
    injection H; intros.
    generalize (Rsqr_1_iff Re); intros.
    unfold Rsqr in H2.
    rewrite /one /mul /= in  H1.
    rewrite H2 in H1.
    destruct H1.
    + left.
      by rewrite H1 /one /=.
    + right.
      by rewrite H1 /one /= /opp /= oppr0 /opp /one /= -IZR_NEG.
Qed.

Lemma nth_root_half_pow n :
  nth_root (S n) (2 * (S n)) = -1.
Proof.
  generalize (nth_root_half_pow_aux n); intros.
  apply Cpow_2 in H.
  destruct H; trivial.
  replace (muln 2 (S n)) with (S (2 * n + 1)) in H by lia.
  generalize (nth_root_not_1 (S n) (2*n+1)); intros.
  assert (S n mod S (2 * n + 1) <> 0%N).
  {
    rewrite Nat.mod_small; lia.
  }
  tauto.
Qed.

Lemma pow2_S (j:nat) :
  exists (k : nat), expn 2 j = S k.
Proof.
  exists (2^j-1)%nat.
  lia.
Qed.

Lemma odd_roots_prim j n :
  exp (nth_root (2 * j + 1) (2 ^ (S n))) (2^n) = -1.
Proof.
  generalize (pow2_S (S n)); intros.
  destruct H.
  rewrite H.
  rewrite exp_nth_root.
  rewrite <- H.
  assert ((2 ^ n * (2 * j + 1) mod (2 ^ S n)) =
           (2 ^ n mod (2 ^ S n)))%N.
  {
    replace (2 ^n * (2 * j + 1))%N with (2 ^ n + j*(2 * 2^n))%N by lia.
    replace (2 ^ (S n))%N with (2 * 2^n)%N.
    - rewrite Nat.mod_add; try lia.
    - by rewrite expnS.
  }
  rewrite H in H0.
  apply nth_root_mod in H0.
  rewrite <- H in H0.
  rewrite H0.
  generalize (pow2_S n); intros.
  destruct H1.
  simpl.
  replace (2 ^ n + (2 ^n + 0))%N with (2 * 2^n)%N by lia.
  rewrite expnS H1.
  apply nth_root_half_pow.
Qed.  

Lemma mult_conj_root j n :
  (nth_root j (S n)) * (conjc (nth_root j (S n))) = 1.
Proof.
  rewrite nth_root_conj Cinv_r //.
  by apply nth_root_not_0.
Qed.

Lemma nth_root_half n :
  nth_root (2 ^n) (2 ^ (S n)) = - 1.
Proof.
  destruct (pow2_S (S n)).
  generalize (odd_roots_prim 0 n); intros.
  rewrite H exp_nth_root -H in H0.
  by rewrite muln0 add0n muln1 in H0.
Qed.

Lemma nth_root_opp j n :
  (nth_root j (2 ^ (S n))) + (nth_root (j + 2^n) (2 ^ (S n))) = 0.
Proof.
  destruct (pow2_S (S n)).
  by rewrite H -nth_root_mul -H nth_root_half mulrN1 addrC addNr.
Qed.

Definition Nat2Zinj := (Nat2Z.inj_mod, Nat2Z.inj_mul, Nat2Z.inj_add, Nat2Z.inj_sub).

Lemma inv_pow_nth_root j k :
  exp (nth_root j (S k)) k = inv (nth_root j (S k)).
Proof.
  rewrite nth_root_inv exp_nth_root -nth_root_eq.
  apply Nat2Z.inj.
  rewrite !Nat2Zinj.
  - rewrite Zdiv.Zmult_mod Zdiv.Zminus_mod.
    rewrite Zdiv.Z_mod_same_full Zdiv.Zmod_mod.
    rewrite Z.sub_0_l Z.opp_eq_mul_m1 Z.mul_comm.
    symmetry.
    rewrite Zdiv.Zmult_mod !Zdiv.Zmod_mod.    
    f_equal.
    f_equal.
    replace (Zneg xH)%Z with (Z.sub (Z.of_nat k) (Z.of_nat (S k))).
    + rewrite Zdiv.Zminus_mod Zdiv.Z_mod_same_full.
      f_equal.
      rewrite Z.mod_small; lia.
    + rewrite Nat2Z.inj_succ; lia.
  - generalize (Nat.mod_upper_bound j (S k)); lia.
Qed.

Lemma conj_pow_nth_root j k :
  exp (nth_root j (S k)) k = conjc (nth_root j (S k)).
Proof.
  by rewrite nth_root_conj inv_pow_nth_root.
Qed.
  

(* testing notations *)
Definition C0': R[i] := 0.
Definition C1': R[i] := 1.
Definition Cplus' (x y : R[i]) := x + y.
Definition Cmult' (x y : R[i]) := x * y.
Definition Cexp' (x : R[i]) (n : nat) := x ^+ n.
Definition Cdiv' (x y : R[i]) := x / y.
Definition Cinv' (x : R[i]) := x^-1.

