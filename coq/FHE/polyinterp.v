Require Import Reals.
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
  intros.
  destruct (le_dec j1 j2).
  - generalize (Nat.add_mod (j2 - j1) j1 (S n) ); intros.
    replace (j2 - j1 + j1) with j2 in H0 by lia.
    rewrite <- H in H0.
Admitted.

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

Lemma cos_eq_1 (x : R) :
  cos x = R1 ->
  exists k, x = (2 * PI * INR(k))%R.
Proof.
  Admitted.

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
  apply cos_eq_1 in H2.
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

Lemma C_telescope_mult (c : C) (n : nat) :
  c <> R1 ->
  (Cmult (c - R1) (list_Cplus (map (fun j => Cpow c j) (seq 0 (S n)))) = 
    (Cpow c (S n) - 1%R))%C.
Proof.
  intros.
  induction n.
  - simpl.
    rewrite Cplus_0_r.
    now do 2 rewrite Cmult_1_r.
  - Search seq.
    rewrite seq_S.
Admitted.

Lemma C_telescope_div (c : C) (n : nat) :
  c <> R1 ->
  list_Cplus (map (fun j => Cpow c j) (seq 0 (S n))) = 
    Cdiv (Cpow c (S n) - 1%R) (c - R1).
Proof.
  intros.
  generalize (C_telescope_mult c n H); intros.
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
    unfold Cminus in H1.
    rewrite <- Cplus_assoc in H1.
    rewrite Cplus_0_l in H1.
    rewrite <- H1.
    replace  (Cplus (Copp (RtoC R1)) (RtoC R1)) with (RtoC R0).
    + now rewrite Cplus_0_r.
    + rewrite Cplus_comm.
      now rewrite Cplus_opp_r.
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
  Admitted.

Lemma root_prod_1 j n :
  list_Cplus
    (map (fun k => Cmult (Cpow (nth_root j (S n)) k) (Cpow (Cinv (nth_root k (S n))) j)) 
       (seq 0 (S n))) = INR (S n).
Proof.
  replace (map (fun k => Cdiv (Cpow (nth_root j (S n)) k)(Cpow (nth_root k (S n)) j)) 
             (seq 0 (S n))) with
          (map (fun k => RtoC R1) (seq 0 (S n))).
  - induction n.
    + simpl.
      rewrite Cmult_1_l.
      rewrite Cplus_0_r.
      rewrite nth_root_0.
      replace R1 with 1%R by lra.
      rewrite Cinv_1_r.
      now rewrite Cpow_1_l.
    + rewrite seq_S.
      rewrite map_app.
      rewrite list_Cplus_app.
      
      
     Admitted.

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



