Require Import Reals Permutation Morphisms.
Require Import Coquelicot.Complex.
Require Import List.
Require Import Lra Lia.
Require Import Utils.

Set Bullet Behavior "Strict Subproofs".

Lemma Forall2_nth_error_iff {A B} (P:A->B->Prop) (l1 : list A) (l2: list B) :
  (forall (i : nat), match nth_error l1 i, nth_error l2 i with
              | Some a, Some b => P a b
              | None, None => True
              | _, _ => False
              end
  ) <->
  Forall2 P l1 l2.
Proof.
  split.
  - revert l2; induction l1; destruct l2; simpl in *; trivial; intros HH.
    + specialize (HH 0); simpl in HH; contradiction.
    + specialize (HH 0); simpl in HH; contradiction.
    + constructor.
      * now specialize (HH 0); simpl in HH.
      * apply IHl1; intros i.
        now specialize (HH (S i)).
  - induction 1; intros [| i]; simpl; trivial.
    apply IHForall2.
Qed.

Lemma nth_error_eqs {A} (l1 l2 : list A) :
  (forall (i : nat), nth_error l1 i = nth_error l2 i) ->
  l1 = l2.
Proof.
  intros HH.
  apply Forall2_eq.
  apply Forall2_nth_error_iff; intros i.
  rewrite HH.
  now destruct (nth_error l2 i).
Qed.

Lemma rev_nth_error {A} (l:list A) (n:nat) :
  n < length l -> nth_error (rev l) n = nth_error l (length l - S n).
Proof.
  revert n.
  induction l using rev_ind; simpl; [lia |]; intros n nlt.
  rewrite rev_app_distr, app_length; simpl.
  destruct n.
  - simpl.
    rewrite nth_error_app2 by lia.
    now replace (length l + 1 - 1 - length l) with 0 by lia.
  - simpl.
    rewrite app_length in nlt; simpl in nlt.
    rewrite IHl by lia.
    rewrite nth_error_app1 by lia.
    f_equal.
    lia.
Qed.

Lemma seq_nth_error [len : nat] (start : nat) [n : nat] :
    n < len -> nth_error (seq start len) n = Some (start + n).
Proof.
  intros nlt.
  rewrite (nth_error_nth' _ 0).
  - now rewrite seq_nth.
  - now rewrite seq_length.
Qed.

Lemma rev_seq start n :
  rev (seq start n) = map (fun i => (n + 2 * start - S i)) (seq start n).
Proof.
  apply nth_error_eqs; intros i.
  rewrite nth_error_map.
  destruct (lt_dec i (length (seq start n))).
  - rewrite rev_nth_error by trivial.
    rewrite seq_length in l.
    repeat rewrite seq_nth_error; trivial
    ; rewrite seq_length.
    + simpl; f_equal; lia.
    + lia.
  - assert (length (seq start n) <= i) by lia.
    assert (length (rev (seq start n)) <= i) by (rewrite rev_length; lia).
    apply nth_error_None in H.
    apply nth_error_None in H0.
    now rewrite H, H0.
Qed.

Lemma map_skipn_S_error {A:Type} (l:list A) n a :
  nth_error l n = Some a ->
  skipn n l = a :: skipn (S n) l.
Proof.
  revert l.
  induction n; simpl; destruct l; simpl; intros; try congruence.
  rewrite IHn; trivial.
Qed.

Lemma list_cons_app_hyp_even {A} (P:list A->Prop) (R:A->A->Prop)
  (Pnil : P nil)
  (Psmoosh : forall a z l, R a z -> R z a -> P l -> P (a::(l ++ z ::nil)))
  : forall n (l:list A), length l = 2 * n -> Forall2 R l (rev l) -> P l.
Proof.
  induction n; simpl.
  - intros [|]; simpl; congruence.
  - intros.
    destruct l; simpl in *; [lia |].
    destruct l using rev_ind; simpl in *; [lia |].
    rewrite app_length in H; simpl in H.
    assert (eqq1:length l = 2 * n) by lia.
    specialize (IHn _ eqq1).
    rewrite rev_app_distr in H0.
    simpl in H0.
    invcs H0.
    apply Forall2_app_tail_inv in H6.
    destruct H6.
    auto.
Qed.

Lemma list_cons_app_hyp_odd {A} (P:list A->Prop) (R:A->A->Prop)
  (Psingle : forall a, R a a -> P (a :: nil))
  (Psmoosh : forall a z l, R a z -> R z a -> P l -> P (a::(l ++ z ::nil)))
  : forall n (l:list A), length l = 2 * n + 1 -> Forall2 R l (rev l) -> P l.
Proof.
  induction n; simpl.
  - intros [|]; simpl; try lia.
    destruct l; simpl; try lia; intros.
    invcs H0.
    auto.
  - intros.
    destruct l; simpl in *; [lia |].
    destruct l using rev_ind; simpl in *; [lia |].
    rewrite app_length in H; simpl in H.
    assert (eqq1:length l = 2 * n + 1) by lia.
    specialize (IHn _ eqq1).
    rewrite rev_app_distr in H0.
    simpl in H0.
    invcs H0.
    apply Forall2_app_tail_inv in H6.
    destruct H6.
    auto.
Qed.

Lemma list_cons_app_hyp {A} (P:list A->Prop) (R:A->A->Prop)
  (Pnil : P nil)
  (Psingle : forall a, R a a -> P (a :: nil))
  (Psmoosh : forall a z l, R a z -> R z a -> P l -> P (a::(l ++ z ::nil)))
  : forall (l:list A), Forall2 R l (rev l) -> P l.
Proof.
  intros.
  destruct (NPeano.Nat.Even_Odd_dec (length l)).
  - destruct e.
    eapply list_cons_app_hyp_even; eauto.
  - destruct o.
    eapply list_cons_app_hyp_odd; eauto.
Qed.

Lemma nth_error_firstn_in {A} (l:list A) n i :
  i < n ->
  nth_error (firstn n l) i = nth_error l i.
Proof.
  revert n l.
  induction i; simpl; intros
  ; destruct n; destruct l; simpl; trivial; try lia.
  apply IHi; lia.
Qed.

Lemma nth_error_skipn {A} (l:list A) n i :
  nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  revert l i.
  induction n; simpl; trivial; intros.
  destruct l; trivial.
  now rewrite nth_error_nil.
Qed.

Lemma firstn_seq n1 n2 start :
  n1 <= n2 ->
  firstn n1 (seq start n2) = seq start n1.
Proof.
  intros.
  apply  nth_error_eqs; intros i.
  destruct (lt_dec i n1).
  - rewrite nth_error_firstn_in; trivial.
    rewrite seq_nth_error by lia.
    now rewrite seq_nth_error.
  - destruct (nth_error_None (firstn n1 (seq start n2)) i) as [_ eqq1].
    destruct (nth_error_None (seq start n1) i) as [_ eqq2].
    rewrite eqq1, eqq2; trivial.
    + rewrite seq_length; lia.
    + rewrite firstn_length; lia.
Qed.

Lemma skipn_seq n1 n2 start :
  skipn n1 (seq start n2) = seq (start+n1) (n2-n1).
Proof.
  intros.
  apply  nth_error_eqs; intros i.
  rewrite nth_error_skipn.
  destruct (lt_dec (n1 + i) n2).
  - rewrite seq_nth_error by lia.
    rewrite seq_nth_error by lia.
    f_equal; lia.
  - destruct (nth_error_None ((seq start n2)) (n1 + i)) as [_ eqq1].
    destruct (nth_error_None (seq (start + n1) (n2 - n1)) i) as [_ eqq2].
    rewrite eqq1, eqq2; trivial
    ; rewrite seq_length; lia.
Qed.

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

Lemma C_telescope_pow_0 (c : C) (n : nat) :
  c <> R1 ->
  Cpow c (S n) = 1%R ->
  list_Cplus (map (fun j => Cpow c j) (seq 0 (S n))) = 0%R.
Proof.
  intros.
  rewrite C_telescope_div; trivial.
  rewrite H0.
  field.
  simpl.
  unfold not; intros.
  apply (f_equal (fun cc => (cc + 1%R)%C)) in H1.
  now ring_simplify in H1.
Qed.
  
Lemma sum_nth_roots_0 n :
  list_Cplus (map (fun j => Cpow (nth_root 1 (S (S n))) j) (seq 0 (S (S n)))) = R0.
Proof.
  apply C_telescope_pow_0.
  - apply nth_root_not_1.
    rewrite Nat.mod_1_l; lia.
  - now rewrite nth_root_npow.
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
  let conjroots := map Cconj (odd_nth_roots (S n)) in
  map (fun c => Cdiv c (2^(S n))%R)
    (map (fun k => Cinner_prod cl (map (fun x => Cpow x k) conjroots))
       (seq 0 (2 ^(S n)))).

Definition encode_half (cl : list C) (n : nat) :=
  let conjroots := map Cconj (odd_nth_roots_half n) in
  map (fun c => Rdiv c (2^(S n))%R)
    (map (fun k => (2 * (Re (Cinner_prod (firstn (2^n) cl) (map (fun x => Cpow x k) conjroots))))%R)
       (seq 0 (2 ^(S n)))).

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

Lemma map_inv_rev_even {A} n (l:list A) f (finv: forall x, f (f x) = x):
  length l = 2 * n ->
  map f l = rev l <->
    map f (firstn n l) = rev (skipn n l).
Proof.
  intros llen.
  split; intros HH.
  - rewrite firstn_skipn_rev.
    rewrite llen, map_rev, <- skipn_map, map_rev.
    replace (2 * n - n) with n by lia.
    now rewrite HH, rev_involutive.
  - rewrite <- (firstn_skipn n l).
    rewrite map_app, rev_app_distr.
    f_equal; trivial.
    apply (f_equal (rev (A:=_))) in HH.
    repeat rewrite rev_involutive in HH.
    rewrite <- HH.
    rewrite map_rev, map_map.
    now erewrite map_ext; [rewrite map_id |].
Qed.

Lemma map_inv_rev_odd {A} n (l:list A) f (finv: forall x, f (f x) = x):
  length l = 2 * n + 1 ->
  map f l = rev l <->
    map f (firstn n l) = rev (skipn (S n) l) /\
      option_map f (nth_error l n) = (nth_error l n).
Proof.
  intros llen.
  split; intros HH.
  - rewrite firstn_skipn_rev.
    rewrite llen, map_rev, <- skipn_map, map_rev.
    replace (2 * n + 1 - n) with (S n) by lia.
    split.
    + now rewrite HH, rev_involutive.
    + apply (f_equal (map f )) in HH.
      rewrite map_map in HH.
      erewrite map_ext in HH; [rewrite map_id in HH|]; trivial.
      apply (f_equal (fun x => nth_error x n)) in HH.
      rewrite  map_rev, rev_nth_error in HH by (rewrite map_length, llen; lia).
      rewrite map_length in HH.
      replace (length l - S n)%nat with n in HH by lia.
      now rewrite nth_error_map in HH.
  - destruct HH as [HH1 HH2].
    rewrite <- (firstn_skipn (S n) l) at 2.
    rewrite <- (firstn_skipn n l) at 1.
    rewrite map_app, rev_app_distr.
    f_equal; trivial.
    case_eq (nth_error l n).
    + intros a ntha.
      rewrite (map_skipn_S_error _ _ _ ntha).
      apply (f_equal (@rev _)) in HH1.
      rewrite rev_involutive in HH1.
      rewrite <- HH1.
      rewrite map_cons, map_rev, map_map.
      erewrite map_ext; [rewrite map_id | auto].
      apply nth_error_split in ntha.
      destruct ntha as [l1 [l2 [? lenl1]]]; subst.
      repeat rewrite firstn_app.
      repeat rewrite rev_app_distr.
      replace ((length l1) - length l1) with 0 by lia.
      replace (S (length l1) - length l1) with 1 by lia.
      rewrite firstn_cons.
      repeat rewrite firstn_O.
      repeat rewrite firstn_all2 by lia.
      simpl; f_equal.
      rewrite nth_error_app2 in HH2 by trivial.
      replace (length l1 - length l1) with 0 in HH2 by lia.
      simpl in HH2.
      congruence.
    + intros HH.
      apply nth_error_None in HH.
      assert (n = 0) by lia.
      subst.
      destruct l; simpl in *; [lia |].
      destruct l; simpl in *; [| lia].
      congruence.
Qed.

Lemma conj_rev_even n cl :
  length cl = 2 * n ->
  map Cconj cl = rev cl <->
    map Cconj (firstn n cl) = firstn n (rev cl).
Proof.
  intros llen.
  generalize (map_inv_rev_even n cl Cconj (Cconj_conj) llen).
  rewrite firstn_rev.
  now replace (length cl - n) with n by lia.
Qed.  

Lemma conj_rev_odd cl n :
  length cl = 2 * n + 1 ->
  map Cconj cl = rev cl <->
    (map Cconj (firstn n cl) = rev (skipn (S n) cl) /\
      Im (nth n cl Ci) = 0%R).
Proof.
  intros llen.
  rewrite (map_inv_rev_odd n cl Cconj (Cconj_conj) llen).
  split; intros [? HH]; split; trivial.
  - rewrite (nth_error_nth' cl Ci) in HH by lia.
    simpl in HH.
    invcs HH.
    apply Cconj_im_0.
    now rewrite Cconj_conj.
  - case_eq (nth_error cl n); simpl; trivial; intros.
    rewrite (nth_error_nth _ _ _ H0) in HH.
    destruct c; unfold Cconj; simpl in *.
    rewrite HH.
    do 2 f_equal.
    lra.
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

Lemma list_Cplus_rev (cl : list C) :
  list_Cplus (rev cl) = list_Cplus cl.
Proof.
  apply list_Cplus_perm_proper.
  apply Permutation_sym.
  apply Permutation_rev.
Qed.

Lemma list_Cplus_conj (cl : list C) :
  list_Cplus (map Cconj cl) = Cconj (list_Cplus cl).
Proof.
  induction cl.
  - unfold Cconj, fst, snd; simpl.
    unfold RtoC; f_equal; lra.
  - simpl.
    rewrite Cplus_conj.
    now f_equal.
Qed.

Lemma conj_rev_half_sum n (cl : list C) :
  length cl = 2*n ->
  map Cconj cl = rev cl ->
  let sum_cl_half := list_Cplus (firstn n cl) in
  list_Cplus cl = (sum_cl_half + Cconj sum_cl_half)%C.
Proof.
  intros.
  rewrite (conj_rev_half_conv n cl); trivial.
  rewrite list_Cplus_app.
  unfold sum_cl_half.
  f_equal.
  rewrite list_Cplus_rev.
  now rewrite list_Cplus_conj.
Qed.

Lemma Cplus_conj (c : C) :
  Cplus c (Cconj c) = (2 * Re c)%R.
Proof.
  destruct c.
  unfold Cplus, Cconj, RtoC, Re, fst, snd.
  f_equal; lra.
Qed.

Lemma conj_rev_half_sum_alt n (cl : list C) :
  length cl = 2*n ->
  map Cconj cl = rev cl ->
  let sum_cl_half := list_Cplus (firstn n cl) in
  list_Cplus cl = (2*(Re sum_cl_half))%R.
Proof.
  intros.
  rewrite (conj_rev_half_sum n); trivial.
  now rewrite Cplus_conj.
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
  intros HH.
  apply (list_cons_app_hyp 
           (fun cl => Im (list_Cplus cl) = 0%R)
           (fun x y => Cconj x = y)).
  - trivial.
  - simpl; intros.
    rewrite Cconj_im_0; trivial.
    lra.
  - intros.
    simpl.
    rewrite <- Permutation_cons_append; simpl.
    unfold Im in *.
    rewrite H1.
    rewrite <- H.
    simpl; lra.
  - rewrite <- HH.
    apply Forall2_map_Forall.
    rewrite Forall_forall; trivial.
Qed.

Lemma combine_app {T} (cl1 cl2 cl1' cl2' : list T) :
  length cl1 = length cl2 ->
  length cl1' = length cl2' ->
  combine (cl1 ++ cl1') (cl2 ++ cl2') = combine cl1 cl2 ++ combine cl1' cl2'.
Proof.
  revert cl2.
  induction cl1; intros; simpl; trivial.
  - simpl in H.
    symmetry in H.
    apply length_zero_iff_nil in H.
    rewrite H; now simpl.
  - destruct cl2; simpl; [now simpl in H|].
    rewrite IHcl1; trivial.
    simpl in H.
    lia.
 Qed.

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
  length cl1 = length cl2 ->
  map (fun '(a, b) => (a * b)%C) (combine (rev cl1) (rev cl2)) =
    rev (map (fun '(a, b) => (a * b)%C) (combine cl1 cl2)).
Proof.
  intros.
  rewrite <- map_rev.
  f_equal.
  now apply combine_rev.
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

Lemma map_conj_conj_rev (cl : list C) :
  map Cconj cl = rev cl ->
  map Cconj (map Cconj cl) = 
    rev (map Cconj cl).
Proof.
  intros.
  apply (f_equal (fun ll => map Cconj ll)) in H.
  rewrite map_map in H.
  rewrite map_rev in H.
  rewrite <- H.
  rewrite map_map.
  now apply map_ext.
Qed.
  
Lemma odd_nth_roots_conj_rev n :
  let cl := map Cconj (odd_nth_roots (S n)) in
  map Cconj cl = rev cl.
Proof.
  simpl.
  apply map_conj_conj_rev.
  unfold odd_nth_roots.
  rewrite <- map_rev.
  rewrite rev_seq.
  do 2 rewrite map_map.
  apply map_ext_in; intros.
  rewrite plus_0_r.
  apply in_seq in H.
  destruct H as [_ alt].
  rewrite plus_0_l in alt.
  destruct (pow2_S (S (S n))); intros.
  rewrite H.
  rewrite nth_root_conj.
  rewrite nth_root_inv.
  f_equal.
  rewrite <- H.
  replace (2 ^ (S (S n))) with (2 * 2 ^ (S n)) by (simpl; lia).
  rewrite Nat.mod_small; lia.
Qed.

Lemma Cinner_prod_conj_rev (cl1 cl2 : list C) :
  length (cl1) = length cl2 ->
  map Cconj cl1 = rev cl1 ->
  map Cconj cl2 = rev cl2 ->    
  Im (Cinner_prod cl1 cl2) = 0%R.
Proof.
  intros.
  unfold Cinner_prod.
  apply list_Cplus_conj_rev.
  apply map_mult_conj_rev; trivial.
Qed.

Lemma encode_real (cl : list C) (n : nat):
  map Cconj cl = rev cl ->
  length cl = length (odd_nth_roots (S n)) ->
  forall (x : C),
    In x (encode cl n) -> Im x = 0%R.
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
    apply Cinner_prod_conj_rev; trivial.
    - now do 2 rewrite map_length.
    - apply map_pow_conj_rev.
      apply odd_nth_roots_conj_rev.
  }
  rewrite <- H1.
  apply Im_div_real; trivial.
  apply pow_nonzero.
  lra.
Qed.

Lemma Re_Im (c : C) :
  Im c = 0%R <-> c = RtoC (Re c).
Proof.
  destruct c.
  unfold RtoC, Im, Re, fst, snd.
  split; intros.
  - now rewrite H.
  - now inversion H.
Qed.

Lemma clist_real (cl : list C) :
  (forall (x : C),
      In x cl -> Im x = 0%R) ->
  cl = map RtoC (map Re cl).
Proof.
  intros.
  rewrite <- List.map_id at 1.
  rewrite map_map.
  apply map_ext_in.
  intros.
  specialize (H a H0).
  now apply Re_Im.
Qed.

Lemma encode_real_alt (cl : list C) (n : nat):
  map Cconj cl = rev cl ->
  length cl = length (odd_nth_roots (S n)) ->
  encode cl n = map RtoC (map Re (encode cl n)).
Proof.
  intros.
  apply clist_real.
  now apply encode_real.
Qed.

Lemma Re_Cmult_R_C (r : R) (c : C) :
  Re (Cmult r c) = Rmult r (Re c).
Proof.
  destruct c; simpl.
  ring.
Qed.

Lemma Re_Cmult_list_Cplus (r : R) (cl : list C) :
  RtoC (Re (Cmult r (list_Cplus cl))) =
    Cmult r (list_Cplus (map RtoC (map Re cl))).
Proof.
  intros.
  induction cl.
  - simpl.
    unfold Cmult, Re, RtoC, fst, snd.
    f_equal; lra.
  - simpl.
    rewrite Rmult_0_l.
    rewrite Rminus_0_r.
    rewrite Cmult_plus_distr_l.
    rewrite <- IHcl.
    rewrite <- RtoC_mult.
    rewrite <- RtoC_plus.
    f_equal.
    rewrite Rmult_plus_distr_l.
    f_equal.
    now rewrite Re_Cmult_R_C.
Qed.

Lemma map_commute {A} (l : list A) (f g : A -> A) :
  (forall a, f (g a) = g (f a)) ->
  map f (map g l) = map g (map f l).
Proof.
  intros.
  do 2 rewrite map_map.
  apply map_ext.
  apply H.
Qed.

Lemma double_Re_commute (c : C) :
  (2 * (Re c))%R = Re (2%R * c)%C.
Proof.
  destruct c.
  unfold RtoC, Re, fst, snd.
  simpl.
  now ring.
Qed.

Lemma div_Re_commute (c : C) (r : R) :
  (r <> 0)%R ->
  (Re c / r)%R = Re (c / r)%C.
Proof.
  intros.
  destruct c.
  unfold RtoC, Re, fst, snd.
  simpl.
  now field.
Qed.

Lemma encode_half_correct (cl : list C) (n : nat):
    length cl = 2^S n ->
    map Cconj cl = rev cl ->
    encode_half cl n = map Re (encode cl n).
Proof.
  intros.
  unfold encode_half, encode.
  rewrite map_map.
  rewrite map_map.
  rewrite map_map.
  apply map_ext.
  intros.
  rewrite double_Re_commute.
  rewrite <- div_Re_commute; [| apply pow_nonzero; lra].
  f_equal.
  unfold Cinner_prod.
  symmetry.
  rewrite (conj_rev_half_sum_alt (2 ^ n)).
  - rewrite double_Re_commute.
    rewrite re_RtoC.
    do 3 f_equal.
    rewrite firstn_map.
    f_equal.
    rewrite combine_firstn.
    f_equal.
    rewrite firstn_map.
    f_equal.
    unfold odd_nth_roots, odd_nth_roots_half.
    do 2 rewrite firstn_map.
    do 2 f_equal.
    apply firstn_seq.
    simpl; lia.
  - rewrite map_length.
    rewrite combine_length.
    do 2 rewrite map_length.
    unfold odd_nth_roots.
    rewrite map_length.
    rewrite seq_length.
    rewrite H.
    apply Nat.min_id.
  - apply map_mult_conj_rev; trivial.
    + apply map_pow_conj_rev.
      apply odd_nth_roots_conj_rev.
    + rewrite map_length.
      rewrite map_length.
      unfold odd_nth_roots.
      rewrite map_length.
      now rewrite seq_length.
Qed.

Lemma encode_half_correct_alt (cl : list C) (n : nat):
  length cl = 2^S n ->
  map Cconj cl = rev cl ->
  map RtoC (encode_half cl n) = encode cl n.
Proof.
  intros.
  generalize (encode_half_correct cl n H H0); intros.
  rewrite (encode_real_alt cl n H0).
  - now f_equal.
  - unfold odd_nth_roots.
    now rewrite map_length, seq_length.
Qed.

Lemma encode_decode (cl : list C) (n : nat):
  map Cconj cl = rev cl ->
  length cl = length (odd_nth_roots (S n)) ->
  decode (map Re (encode cl n)) n = cl.
Proof.
  intros.
  unfold encode.
  Admitted.


(* claim (nxn vandermonde on odd roots) x conjugate transpose = n * I. *)

Lemma mult_conj_root j n :
  Cmult (nth_root j (S n)) (Cconj (nth_root j (S n))) = 1%R.
Proof.
  rewrite nth_root_conj.
  rewrite Cinv_r; trivial.
  apply nth_root_not_0.
Qed.

Lemma nth_root_half n :
  nth_root (2 ^n) (2 ^ (S n)) = (-1)%R.
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
  (nth_root j (2 ^ (S n)) + nth_root (j + 2^n) (2 ^ (S n)) = 0%R)%C.
Proof.
  destruct (pow2_S (S n)).
  rewrite H.
  rewrite <- nth_root_mul.
  rewrite <- H.
  rewrite nth_root_half.
  ring.
Qed.

Hint Rewrite Nat2Z.inj_mul : of_nat_re.
Hint Rewrite Nat2Z.inj_add : of_nat_re.
Hint Rewrite Nat2Z.inj_sub  : of_nat_re.
Hint Rewrite Nat2Z.inj_mod : of_nat_re.
Hint Rewrite Nat2Z.inj_pow : of_nat_re.
Hint Rewrite Nat2Z.inj_div : of_nat_re.
Hint Rewrite Nat2Z.inj_0 : of_nat_re.

Lemma of_nat_1 : Z.of_nat 1 = 1%Z.
Proof.
  lia.
Qed.

Lemma of_nat_2 : Z.of_nat 2 = 2%Z.
Proof.
  lia.
Qed.

Hint Rewrite of_nat_1 : of_nat_re.
Hint Rewrite of_nat_2 : of_nat_re.


Lemma mod_odd_even x y :
  y <> 0 ->
  Nat.Odd x -> Nat.Even y -> Nat.Odd (x mod y).
Proof.
  intros.
  rewrite Nat.mod_eq; trivial.
  generalize (Nat.Even_mul_l y (x / y) H1); intros HH2.
  apply Nat.odd_spec.
  rewrite Nat.odd_sub.
  - apply Nat.odd_spec in H0.
    rewrite H0.
    apply Nat.even_spec in HH2.
    now rewrite <- Nat.negb_even, HH2.
  - now apply Nat.mul_div_le.
Qed.

Lemma mod_even_even x y :
  y <> 0 -> 
  Nat.Even x -> Nat.Even y -> Nat.Even (x mod y).
Proof.
  intros.
  rewrite Nat.mod_eq; trivial.
  generalize (Nat.Even_mul_l y (x / y) H1); intros HH2.
  apply Nat.even_spec.
  rewrite Nat.even_sub.
  - apply Nat.even_spec in H0.
    rewrite H0.
    apply Nat.even_spec in HH2.
    now rewrite HH2.
  - now apply Nat.mul_div_le.
Qed.

Lemma odd_nth_root_div_pow_sum_0 j k n :
  (2*j+1) mod (2^(S n)) <> (2*k+1) mod (2 ^ (S n)) ->
  let w := Cdiv (nth_root (2*j+1) (2 ^ (S n))) (nth_root (2*k+1) (2 ^ (S n))) in
  list_Cplus (map (fun j => Cpow w j) (seq 0 (2^n))) = 0%R.
Proof.
  intros.
  destruct (pow2_S n).
  rewrite H0.
  destruct (pow2_S (S n)).
  assert (nz:2 ^ (S n) <> 0) by lia.
  apply C_telescope_pow_0.
  - unfold w.
    rewrite H1.
    rewrite nth_root_div.
    apply nth_root_not_1.
    rewrite <- H1.
    intros HH.
    apply (f_equal Z.of_nat) in HH.

    autorewrite with of_nat_re in HH.
    + rewrite <- Zdiv.Zplus_mod_idemp_r in HH.
      rewrite <- Zdiv.Zminus_mod_idemp_l in HH.
      rewrite Zdiv.Z_mod_same_full in HH.
      rewrite Zdiv.Zminus_mod_idemp_r in HH.
      rewrite Zdiv.Zplus_mod_idemp_r in HH.
      apply H.
      apply Nat2Z.inj.
      autorewrite with of_nat_re.
      apply (f_equal (fun x => (x + (2 * Z.of_nat k + 1)) mod 2 ^ Z.of_nat (S n)))%Z in HH.
      rewrite Zplus_0_l in HH.
      rewrite <- HH.
      rewrite Zdiv.Zplus_mod_idemp_l.
      f_equal.
      lia.
    + apply Nat.lt_le_incl.
      apply Nat.mod_upper_bound.
      lia.
  - unfold w.
    rewrite H1.
    rewrite nth_root_div.
    rewrite Cpow_nth_root.
    apply nth_root_1.
    rewrite <- H0, <- H1.
    assert (exists (k2 : nat),
               (2 ^ S n - (2 * k + 1) mod 2^ S n = 2*k2 + 1)).
    {
      assert (odd1:Nat.Odd ((2 * k + 1) mod 2 ^ S n)).
      {
        apply mod_odd_even; trivial; red; eauto.
        exists (2 ^ n).
        simpl; lia.
      } 
      apply Nat.odd_spec in odd1.
      apply Nat.odd_spec.
      rewrite Nat.odd_sub.
      - rewrite odd1.
        now rewrite Nat.odd_pow by congruence.
      - apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        lia.
    }
    destruct H2.
    rewrite H2.
    replace (2 * j + 1 + (2 *x1 + 1)) with (2 * (j + x1 + 1)) by lia.
    replace (2 ^ n * (2 * (j + x1 + 1))) with
      ((j + x1 + 1) * (2 ^ S n)).
    + apply Nat.mod_mul; lia.
    + simpl; lia.
Qed.


Lemma sum_pow_div (c1 c2 : C) n :
  c1 = c2 ->
  c2 <> 0%R ->
  list_Cplus (map (fun j => Cpow (Cdiv c1 c2) j) (seq 0 n)) = INR (n).
Proof.
  intros.
  replace (map (fun j => Cpow (Cdiv c1 c2) j) (seq 0 n)) with
    (map (fun (j:nat) => RtoC 1%R) (seq 0 n)).
  - induction n.
    + easy.
    + rewrite seq_S.
      rewrite map_app.
      rewrite list_Cplus_app.
      rewrite IHn.
      rewrite S_INR.
      simpl.
      rewrite Cplus_0_r.
      now rewrite RtoC_plus.
  - apply map_ext.
    intros.
    rewrite H.
    unfold Cdiv.
    rewrite Cinv_r; trivial.
    now rewrite Cpow_1_l.
Qed.
  
Lemma odd_nth_root_div_pow_sum_1 j k n :
  j mod (2^(S n)) = k mod (2 ^ (S n)) ->
  let w := Cdiv (nth_root j (2 ^ (S n))) (nth_root k (2 ^ (S n))) in
  list_Cplus (map (fun j => Cpow w j) (seq 0 (2^n))) = INR (2^n).
Proof.
  intros.
  unfold w.
  destruct (pow2_S (S n)).
  rewrite H0.
  apply sum_pow_div.
  - apply nth_root_mod.
    now rewrite <- H0.
  - apply nth_root_not_0.
Qed.
