Require Import Reals Permutation Morphisms.
Require Import Coquelicot.Complex.
Require Import List.
Require Import Lra Lia.
Require Import Utils.
Require Import Vector.

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

Lemma nth_error_firstn_nin {A} (l:list A) n i :
  i >= n ->
  nth_error (firstn n l) i = None.
Proof.
  intros.
  apply nth_error_None.
  rewrite firstn_length.
  lia.
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

Lemma combine_nth_error [A B : Type] (l : list A) (l' : list B) (n : nat) :
  length l = length l' -> nth_error (combine l l') n = match nth_error l n, nth_error l' n with
                                                      | Some x, Some y => Some (x,y)
                                                      | _, _ => None
                                                      end.
Proof.
  revert l l'.
  induction n; destruct l; destruct l'; simpl; try congruence.
  intros.
  apply IHn; congruence.
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

Lemma list_Cplus_mult_l c l :
  (list_Cplus (map (fun a => c * a) l) = c * list_Cplus l)%C.
Proof.
  induction l; simpl.
  - ring. 
  - rewrite IHl.
    ring.
Qed.

Lemma list_cplus_mult_seq_comm c (p : list R) :
list_Cplus
    (map (fun '(a0, b) => (RtoC a0 * b)%C)
       (combine p (map (fun j : nat => (c ^ j)%C) (seq 1 (length p))))) =
  (c *
   list_Cplus
     (map (fun '(a0, b) => RtoC a0 * b)
        (combine p (map (fun j : nat => c ^ j) (seq 0 (length p))))))%C.
Proof.
  rewrite <- list_Cplus_mult_l.
  rewrite <- seq_shift.
  rewrite map_map.
  rewrite <- (map_id p) at 1 3.
  repeat rewrite combine_map.
  repeat rewrite map_map.
  f_equal.
  apply map_ext; intros [??]; simpl.
  ring.
Qed.

Lemma list_Cplus_Re (l : list C) :
  Re (list_Cplus l) = list_sum (map Re l).
Proof.
  induction l.
  - now simpl.
  - simpl.
    now rewrite <- IHl.
Qed.

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

Definition Ceval_poly (p : list C) (c : C) :=
  let cpows := map (fun j => Cpow c j) (seq 0 (length p)) in
  list_Cplus (map (fun '(a, b) => Cmult a b) (combine p cpows)).

Definition Ceval_Rpoly (p : list R) (c : C) :=
  let cpows := map (fun j => Cpow c j) (seq 0 (length p)) in
  list_Cplus (map (fun '(a, b) => Cmult (RtoC a) b) (combine p cpows)).

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

Lemma Ceval_horner_Rpoly (p : list R) (c : C) :
  Ceval_Rpoly p c = C_horner_eval_Rpoly p c.
Proof.
  induction p.
  - now simpl.
  - unfold Ceval_Rpoly.
    simpl.
    rewrite Cmult_1_r.
    f_equal.
    rewrite <- IHp.
    unfold Ceval_Rpoly.
    now rewrite list_cplus_mult_seq_comm.
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

Definition V_odd_nth_roots (n : nat) : Vector C (2^n) :=
  fun j => nth_root (2 * (proj1_sig j) + 1) (2 ^ (S n)).

Definition odd_nth_roots_half (n : nat) :=
  (map (fun j => nth_root (2*j+1) (2 ^ (S (S n)))) (seq 0 (2^n))).

Definition decode (p : list R) (n : nat) :=
  map (C_horner_eval_Rpoly p) (odd_nth_roots (S n)).

Definition decode_eval (p : list R) (n : nat) :=
  map (Ceval_Rpoly p) (odd_nth_roots (S n)).

Definition decode_Ceval (p : list C) (n : nat) :=
  map (Ceval_poly p) (odd_nth_roots (S n)).

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

Definition peval_mat (l : list C) :=
  let n := length l in
  map (fun c => map (fun k => Cpow c k) (seq 0 n)) l.

Definition V_peval_mat {n} (roots : Vector C n) : Matrix C n n :=
  (fun n1 n2 => Cpow (roots n1) (proj1_sig n2)).

Definition conj_mat (m : list (list C)) :=
  map (fun cl => map Cconj cl) m.

Definition V_conj_mat {n1 n2} (m : Matrix C n1 n2) :=
  fun n1' n2' => Cconj (m n1' n2').

Definition V_inv_mat {n1 n2} (m : Matrix C n1 n2) :=
  fun n1' n2' => Cinv (m n1' n2').

Definition transpose_mat (m : list (list C)) :=
  let n := length m in
  map (fun k =>
         map (fun cl => nth k cl (RtoC 0%R)) m)
    (seq 0 n).

Definition mat_vec_mult (m : list (list C)) (v : list C) :=
  map (fun ml => Cinner_prod ml v) m.

Definition vector_sum {n} (v : Vector C n) :=
  vector_fold_right Cplus 0%R v.

Definition V_inner_prod {n} (v1 v2 : Vector C n) :=
  vector_sum (fun n' => Cmult (v1 n') (v2 n')).

Definition V_mat_vec_mult {n1 n2} (m  : Matrix C n1 n2) (v : Vector C n2) :=
  fun n' => V_inner_prod (m n') v.
    
Definition vec_mat_mult (v : list C) (m : list (list C)) :=
  map (fun cl => Cinner_prod v cl) (transpose_mat m).

Definition V_vec_mat_mult {n1 n2} (v : Vector C n1) (m : Matrix C n1 n2) :=
  fun n' => V_inner_prod v ((transpose m) n').

Definition mat_mat_mult (m1 m2 : list (list C)) :=
  map (fun v => mat_vec_mult m1 v) (transpose_mat m2).

Definition V_mat_mat_mult {n1 n2 n3} (m1: Matrix C n1 n2) (m2 : Matrix C n2 n3) :=
  (fun n1' n3' => V_inner_prod (m1 n1') ((transpose m2) n3')).

Lemma mmv_mult_assoc_row (m2: list (list C)) (r1 v : list C) :
  length r1 = length m2 ->
  (forall r2, In r2 m2 -> length r2 = length v) ->
  Cinner_prod r1 (mat_vec_mult m2 v) =
    Cinner_prod (vec_mat_mult r1 m2) v.
Proof.
  intros.
  unfold mat_vec_mult, vec_mat_mult.
  unfold Cinner_prod.
  f_equal.
Admitted.

Definition Vscale {n} (r : C) (v : Vector C n) :=
  fun n' => Cmult r (v n').

Definition Vscale_r {n} (r : C) (v : Vector C n) :=
  fun n' => Cmult (v n') r.

Lemma vector_sum_scale {n} (c : C) (v : Vector C n) :
  Cmult c (vector_sum v) = vector_sum (Vscale c v).
Proof.
  unfold vector_sum, Vscale.
  induction n.
  - unfold vector_fold_right, vector_fold_right_dep, vector_fold_right_bounded_dep.
    simpl.
    now rewrite Cmult_0_r.
  - rewrite vector_fold_right_Sn.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    now rewrite vector_fold_right_Sn.
Qed.

Lemma vector_sum_scale_r {n} (v : Vector C n) (c : C) :
  Cmult (vector_sum v) c = vector_sum (Vscale_r c v).
Proof.
  unfold vector_sum, Vscale.
  induction n.
  - unfold vector_fold_right, vector_fold_right_dep, vector_fold_right_bounded_dep.
    simpl.
    now rewrite Cmult_0_l.
  - rewrite vector_fold_right_Sn.
    rewrite Cmult_plus_distr_r.
    rewrite IHn.
    now rewrite vector_fold_right_Sn.
Qed.

Definition vmap' {A B} {n} (f:A->B) (v:Vector A n) : Vector B n
  := fun n' => f (v n').

Definition mmap' {A B} {m n} (f:A->B) (mat:Matrix A m n) : Matrix B m n
    := fun n1' n2' => f (mat n1' n2').

Lemma vector_sum_const {n} (c : C) :
  vector_sum (ConstVector n c) = Cmult (RtoC (INR n)) c.
Proof.
  unfold vector_sum, ConstVector.
  induction n.
  - unfold vector_fold_right, vector_fold_right_dep, vector_fold_right_bounded_dep.
    simpl.
    now rewrite Cmult_0_l.
  - rewrite vector_fold_right_Sn.
    unfold vlast, vdrop_last.
    rewrite S_INR.
    replace  ((INR n + 1)%R * c)%C with
      (c + (INR n) * c)%C.
    + f_equal.
      rewrite <- IHn.
      f_equal.
      apply FunctionalExtensionality.functional_extensionality.        
      intros.
      now destruct x.
    + unfold RtoC.
      destruct c.
      unfold Cplus, Cmult, fst, snd.
      f_equal; lra.
 Qed.

Lemma vector_sum_sum {n1 n2} (m : Matrix C n1 n2) :
  vector_sum (fun n' => vector_sum (m n')) =
  vector_sum (fun n'' => vector_sum ((transpose m) n'')).
Proof.
  unfold transpose.
  unfold vector_sum.
Admitted.

Lemma V_mmv_mult_assoc {n1 n2 n3} 
  (m1 : Matrix C n1 n2)
  (m2: Matrix C n2 n3)
  (v : Vector C n3) :
  V_mat_vec_mult m1 (V_mat_vec_mult m2 v) =
    V_mat_vec_mult (V_mat_mat_mult m1 m2) v.
Proof.
  intros.
  unfold V_mat_vec_mult, V_mat_mat_mult.
  unfold V_inner_prod, transpose.
  apply FunctionalExtensionality.functional_extensionality.  
  intros.
  Admitted.


Lemma mmv_mult_assoc (m1 m2: list (list C)) (v : list C) :
  (forall r1, In r1 m1 -> length r1 = length m2) ->
  (forall r2, In r2 m2 -> length r2 = length v) ->
  mat_vec_mult m1 (mat_vec_mult m2 v) =
    mat_vec_mult (mat_mat_mult m1 m2) v.
Proof.
  intros.
  unfold mat_mat_mult.
  unfold mat_vec_mult at 1.
  replace (map (fun ml => Cinner_prod ml (mat_vec_mult m2 v)) m1) with
    (map (fun r1 =>    
           Cinner_prod (vec_mat_mult r1 m2) v) m1).
  - unfold vec_mat_mult, mat_vec_mult.
    unfold Cinner_prod.
    rewrite map_map.
    admit.
  - apply map_ext_in.
    intros.
    rewrite mmv_mult_assoc_row; trivial.
    now specialize (H a H1).

Admitted.

Lemma map_Cmult_combine_comm l1 l2 :
  map (fun '(a0, b) => (a0 * b)%C) (combine l1 l2) =
  map (fun '(a0, b) => (a0 * b)%C) (combine l2 l1).
Proof.
  rewrite combine_swap.
  rewrite map_map.
  apply map_ext.
  intros.
  destruct a.
  unfold fst, snd.
  now rewrite Cmult_comm.
Qed.

Lemma peval_mat_decode_Ceval (p : list C) n :
  length p = length (odd_nth_roots (S n)) ->
  decode_Ceval p n =
    mat_vec_mult (peval_mat (odd_nth_roots (S n))) p.
Proof.
  intros.
  unfold decode_Ceval, mat_vec_mult, peval_mat, Ceval_poly.
  rewrite map_map.
  apply map_ext.
  intros.
  unfold Cinner_prod.
  apply list_Cplus_perm_proper, refl_refl.
  rewrite map_Cmult_combine_comm.
  now rewrite <- H.
Qed.

Lemma map_Cinv_l (lc : list C) (c : C) :
  c <> 0%R ->
  map (fun x => (x / c * c)%C) lc = lc.
Proof.
  intros.
  replace lc with (map (fun (x : C) => x) lc) at 2.
  - apply map_ext.
    intros.
    unfold Cdiv.
    rewrite <- Cmult_assoc.
    rewrite Cinv_l; trivial.
    now rewrite Cmult_1_r.
  - now rewrite map_id.
Qed.

Lemma nth_map_seq {A} (f : nat -> A) (d : A) (a m : nat) :
  In a (seq 0 m) ->
  nth a (map f (seq 0 m)) d = f a.
Proof.
  intros.
  induction m.
  - now simpl in H.
  - rewrite seq_S.
    rewrite map_app.
    destruct (lt_dec a m).
    + simpl.
      rewrite app_nth1.
      * rewrite IHm; trivial.
        rewrite in_seq; lia.
      * now rewrite map_length, seq_length.
    + rewrite in_seq in H.
      assert (a = m) by lia.
      rewrite H0.
      simpl.
      rewrite app_nth2.
      * rewrite map_length, seq_length.
        now replace (m - m) with 0 by lia.
      * rewrite map_length, seq_length; lia.
Qed.

Lemma conj_trans_mat_encode (cl : list C) n :
  length cl = length (odd_nth_roots (S n)) ->
  map (fun c => Cmult c (2^(S n))%R) (encode cl n) =
    mat_vec_mult (conj_mat (transpose_mat (peval_mat (odd_nth_roots (S n)))))
      cl.
  Proof.
    intros.
    unfold encode.
    rewrite map_map.
    assert (length (odd_nth_roots (S n)) = 2^(S n)).
    {
      unfold odd_nth_roots.
      now rewrite map_length, seq_length.
    }
    rewrite map_Cinv_l.
    - unfold mat_vec_mult, conj_mat.
      rewrite map_map.
      unfold transpose_mat.
      rewrite map_map.
      unfold peval_mat.
      rewrite map_length.
      rewrite H0.
      apply map_ext_in.
      intros.
      unfold Cinner_prod.
      apply list_Cplus_perm_proper, refl_refl.
      rewrite map_Cmult_combine_comm.
      do 2 f_equal.
      do 3 rewrite map_map.
      apply map_ext.
      intros.
      rewrite <- Cpow_conj.
      f_equal.
      now rewrite nth_map_seq.
    - unfold RtoC.
      unfold not; intros.
      replace (S n) with (n + 1) in H1 by lia.
      injection H1; intros.
      generalize (pow_nonzero 2 (n+1)); intros.
      cut_to H3; lra.
 Qed.

Lemma encode_decode_eval (cl : list C) (n : nat):
  map Cconj cl = rev cl ->
  length cl = length (odd_nth_roots (S n)) ->
  decode_eval (map Re (encode cl n)) n = cl.
Proof.
  intros.
  unfold encode, decode_eval.
  rewrite map_map.
  rewrite map_map.
  unfold Ceval_Rpoly.
  rewrite map_length.
  rewrite seq_length.
  etransitivity.
  - apply map_ext; intros.
    apply list_Cplus_perm_proper.
    rewrite combine_map.
    rewrite combine_self.
    repeat rewrite map_map.
    reflexivity.
  - apply nth_error_eqs; intros.
    destruct (lt_dec i (length cl)).
    + rewrite nth_error_map.
      unfold odd_nth_roots at 2.
      rewrite nth_error_map.
      rewrite seq_nth_error.
      * unfold option_map.
        admit.
      * unfold odd_nth_roots in H0.
        rewrite map_length, seq_length in H0.
        congruence.
    + assert (length cl <= i) by lia.
      apply nth_error_None in H1.
      rewrite H1.
      apply nth_error_None.
      rewrite map_length, <- H0; lia.
Admitted.  

Lemma encode_decode (cl : list C) (n : nat):
  map Cconj cl = rev cl ->
  length cl = length (odd_nth_roots (S n)) ->
  decode (map Re (encode cl n)) n = cl.
Proof.
  intros.
  rewrite <- encode_decode_eval with (n := n); trivial.
  unfold decode, decode_eval.
  apply map_ext.
  intros.
  now rewrite Ceval_horner_Rpoly. 
Qed.

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

Lemma conj_transpose (m : list (list C)) :
  conj_mat (transpose_mat m) = transpose_mat (conj_mat m).
Proof.
  unfold conj_mat, transpose_mat.
  rewrite map_map, map_length.
  apply map_ext; intros.
  do 2 rewrite map_map.
  apply map_ext; intros.
  replace (RtoC 0%R) with (Cconj 0%R) at 2.
  - now rewrite map_nth.
  - unfold Cconj, RtoC, fst, snd.
    f_equal; lra.
Qed.

Lemma V_conj_transpose {n} (m : Matrix C n n) :
  V_conj_mat (transpose m) = transpose (V_conj_mat m).
Proof.
  unfold V_conj_mat, transpose.
  easy.
Qed.

Lemma transpose_involutive (m : list (list C)) :
  transpose_mat (transpose_mat m) = m.
Proof.
  unfold transpose_mat.
  rewrite map_length.
  rewrite seq_length.
  apply nth_error_eqs; intros.
  rewrite nth_error_map.
  destruct (lt_dec i (length m)).
  - rewrite seq_nth_error; trivial.
    unfold option_map.
    rewrite nth_error_nth' with (d := nil); trivial.
    f_equal.
    rewrite map_map.
    
    admit.
  - unfold option_map.
    assert (length m <= i) by lia.
    apply nth_error_None in H.
    rewrite H.
    assert (i >= length (seq 0 (length m))).
    {
      rewrite seq_length; lia.
    }
    apply nth_error_None in H0.
    now rewrite H0.
  Admitted.

Lemma deocde_mat_encode_mat_on_diag (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let prod := mat_mat_mult pmat (conj_mat (transpose_mat pmat)) in
  forall n,
(*    n < length prod -> *)
    nth n (nth n prod nil) 0%R = RtoC (2^S n)%R.
Proof.
  intros.
  unfold prod, mat_mat_mult.
  rewrite conj_transpose.
  rewrite transpose_involutive.
  unfold mat_vec_mult.
  unfold pmat, peval_mat, conj_mat.
  do 2 rewrite map_map.
    
Admitted.
  
Lemma V_transpose_involutive {T} {n1 n2} (m : Matrix T n1 n2) :
  transpose (transpose m) = m.
Proof.
  now unfold transpose.
Qed.

Lemma nth_root_conj_alt j n :
  Cconj (nth_root j (S n)) = nth_root (S n - j mod (S n)) (S n).
Proof.
  rewrite nth_root_conj.
  now rewrite nth_root_inv.
Qed.

Lemma vector_sum_list_Cplus {n} (v : Vector C n) :
  vector_sum v = list_Cplus (vector_to_list v).
Proof.
  Admitted.

Lemma list_Cplus_vector_sum (l : list C) :
  list_Cplus l = vector_sum (list_to_vector l).
Proof.
  unfold list_to_vector.
  unfold vector_sum.
Admitted.    


Lemma V_telescope_pow_0 (c : C) (n : nat) :
  c <> R1 ->
  Cpow c (S n) = 1%R ->
  vector_sum (fun (j : { j | j < S n}) => Cpow c (proj1_sig j)) = 0%R.
Proof.
  intros.
  generalize (C_telescope_pow_0 c n H H0); intros.
  rewrite <- H1.
  rewrite vector_sum_list_Cplus.
  apply list_Cplus_perm_proper.
  unfold vector_to_list.

Admitted.

Lemma nat_mod_mul a b c :
  (a * c) <> 0 ->
  b mod c = 0 ->
  (a * b) mod (a * c) = 0.
Proof.
  intros.
  generalize (Nat.div_mod_eq b c); intros.
  rewrite H0 in H1.
  replace (c * (b / c) + 0) with (c * (b / c)) in H1 by lia.
  rewrite H1.
  replace (a * (c * (b / c))) with ((b/c) * (a * c)) by lia.
  now rewrite Nat.mod_mul.
Qed.

Lemma V_decode_mat_encode_mat_off_diag (n : nat):
  let pmat := (V_peval_mat (V_odd_nth_roots (S n))) in
  let prod := V_mat_mat_mult pmat (V_conj_mat (transpose pmat)) in
  forall i j,
    proj1_sig i <> proj1_sig j ->
    prod i j = 0%R.
Proof.
  intros.
  unfold prod.
  rewrite V_conj_transpose.
  unfold V_mat_mat_mult, V_conj_mat.
  rewrite V_transpose_involutive.
  unfold pmat.
  unfold V_inner_prod.
  unfold V_peval_mat.
  unfold V_odd_nth_roots.
  destruct i.
  destruct j.
  unfold proj1_sig in *.
  destruct (pow2_S (S n)).
  rewrite H0.
  destruct (pow2_S (S (S n))).
  rewrite H1.
  generalize (V_telescope_pow_0  (Cmult (nth_root (2 * x + 1) (S x2))
                                        (Cconj (nth_root (2 * x0 + 1) (S x2))))
                                 x1
             ); intros.
  rewrite <- H2.
  - f_equal.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct x3.
    simpl.
    now rewrite Cpow_mult_l, Cpow_conj.
  - rewrite nth_root_conj_alt.
    rewrite nth_root_mul.
    apply nth_root_not_1.
    rewrite <- H1.
    assert (2 * x + 1 < 2 ^ (S (S n))).
    {
      simpl.
      simpl in l.
      lia.
    }
    assert (2 * x0 + 1 < 2 ^ (S (S n))).
    {
      simpl.
      simpl in l0.
      lia.
    }
    intros HH.
    apply (f_equal Z.of_nat) in HH.
    autorewrite with of_nat_re in HH; [|rewrite Nat.mod_small; lia].
    rewrite <- Zdiv.Zplus_mod_idemp_r in HH.
    rewrite <- Zdiv.Zminus_mod_idemp_l in HH.
    rewrite Zdiv.Z_mod_same_full in HH.
    rewrite Zdiv.Zminus_mod_idemp_r in HH.
    rewrite Zdiv.Zplus_mod_idemp_r in HH.
    apply H.
    apply Nat2Z.inj.
    autorewrite with of_nat_re.
    replace (2 * Z.of_nat x + 1 + (0 - (2 * Z.of_nat x0 + 1)))%Z with
      (2 * Z.of_nat x - 2 * Z.of_nat x0)%Z in HH by lia.
    apply (f_equal (fun x => (x + (2 * Z.of_nat x0)) mod 2 ^ Z.of_nat (S (S n))))%Z in HH.
    rewrite Zplus_0_l in HH.
    rewrite Zdiv.Zplus_mod_idemp_l in HH.
    replace (2 * Z.of_nat x - 2 * Z.of_nat x0 + 2 * Z.of_nat x0)%Z with
      (2 * Z.of_nat x)%Z in HH by lia.
    rewrite Z.mod_small in HH.
    + rewrite Z.mod_small in HH; try lia.
      split; try lia.
      apply inj_lt in l0.
      rewrite Nat2Z.inj_pow in l0.
      replace (2 ^ Z.of_nat (S (S n)))%Z with
        (2 * 2 ^ Z.of_nat (S n))%Z; try lia.
      rewrite (Nat2Z.inj_succ (S n)).
      rewrite Z.pow_succ_r; lia.
    + split; try lia.
      apply inj_lt in l.
      rewrite Nat2Z.inj_pow in l.
      replace (2 ^ Z.of_nat (S (S n)))%Z with
        (2 * 2 ^ Z.of_nat (S n))%Z; try lia.
      rewrite (Nat2Z.inj_succ (S n)).
      rewrite Z.pow_succ_r; lia.
  - rewrite nth_root_conj_alt.
    rewrite nth_root_mul.
    generalize nth_root_1; intros.
    rewrite Cpow_nth_root.
    apply nth_root_1.
    rewrite <- H0, <- H1.
    replace (2 ^ (S (S n))) with ((2 ^ S n)*2) by (simpl;lia).
    rewrite nat_mod_mul; try lia.
    rewrite Nat.add_mod; try lia.
    assert ((2 * x + 1) mod 2 = 1).
    {
      rewrite Nat.add_mod; try lia.
      replace (2 * x) with (x * 2) by lia.
      rewrite Nat.mod_mul; try lia.
      now simpl.
    }
    rewrite H4.
    assert (exists (k : nat),
               (2 ^ S n * 2 - (2 * x0 + 1) mod (2^ S n * 2) = 2 * k + 1)).
    {
      assert (odd1:Nat.Odd ((2 * x0 + 1) mod (2 ^ S n * 2))).
      {
        apply mod_odd_even; trivial; red; eauto; try lia.
        exists (2 ^ S n).
        simpl; lia.
      } 
      apply Nat.odd_spec in odd1.
      apply Nat.odd_spec.
      rewrite Nat.odd_sub.
      - rewrite odd1.
        rewrite Nat.odd_mul.
        now rewrite Nat.odd_pow by congruence.
      - apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        lia.
    }
    destruct H5.
    rewrite H5.
    replace (2 * x3 + 1) with (1 + x3 * 2) by lia.
    replace ((1 + x3 * 2) mod 2) with 1; [now simpl | ].
    rewrite Nat.add_mod; try lia.
    rewrite Nat.mod_mul; try lia.
    simpl; lia.
 Qed.

Lemma root_conj_power_inv i j n :
  Cmult (Cpow (nth_root i (S n)) j) 
        (Cconj (Cpow (nth_root i (S n)) j)) = 1%R.
Proof.
  Search nth_root.
  rewrite Cpow_nth_root.
  now rewrite mult_conj_root.
Qed.

Lemma V_decode_mat_encode_mat_on_diag (n : nat):
  let pmat := (V_peval_mat (V_odd_nth_roots (S n))) in
  let prod := V_mat_mat_mult pmat (V_conj_mat (transpose pmat)) in
  forall n0,
    prod n0 n0 = RtoC (2^S n)%R.
Proof.
  intros.
  unfold prod.
  rewrite V_conj_transpose.
  unfold V_mat_mat_mult, V_conj_mat.
  rewrite V_transpose_involutive.
  unfold pmat.
  unfold V_inner_prod.
  replace  (fun n' : {n' : nat | n' < 2 ^ S n} =>
     (V_peval_mat (V_odd_nth_roots (S n)) n0 n' *
        Cconj (V_peval_mat (V_odd_nth_roots (S n)) n0 n'))%C) with
   (ConstVector (2 ^ S n) (RtoC 1%R)).
  - rewrite vector_sum_const.
    rewrite Cmult_1_r.
    f_equal.
    now rewrite pow_INR.
  - apply FunctionalExtensionality.functional_extensionality.
    intros.
    unfold ConstVector.
    unfold V_peval_mat.
    unfold V_odd_nth_roots.
    destruct (pow2_S (S (S n))).
    rewrite H.
    now rewrite root_conj_power_inv.
 Qed.

Lemma decode_mat_encode_mat_off_diag (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let prod := mat_mat_mult pmat (conj_mat (transpose_mat pmat)) in
  forall i j,
(*    i < length prod ->
    j < length prod ->
*)
    i <> j ->
    nth i (nth j prod nil) 0%R = 0%R.
Proof.
  intros.
  unfold prod, mat_mat_mult.
  rewrite conj_transpose.
  rewrite transpose_involutive.
  unfold mat_vec_mult.
  unfold pmat, peval_mat, conj_mat.
  do 2 rewrite map_map.
  

Admitted.


Lemma deocde_mat_encode_mat (cl : list C) (n : nat):
  length cl = length (odd_nth_roots (S n)) ->
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  mat_vec_mult (mat_mat_mult pmat (conj_mat (transpose_mat pmat))) cl =
    map (fun c => Cmult c (2^(S n))%R) cl.
Proof.
  intros.
  unfold mat_vec_mult, mat_mat_mult.
  rewrite conj_transpose.
  rewrite transpose_involutive.
  rewrite map_map.
  unfold mat_vec_mult.
  unfold pmat.
  Admitted.
  
Lemma vector_sum_all_but_1_0 n i c :
  vector_sum (fun (n' : {n' : nat | n' < n}) => if eq_nat_decide i (proj1_sig n') then c else 0%R) = c.
  Proof.
    Admitted.

Lemma V_deocde_mat_encode_mat_assoc_l (n : nat) (cl : Vector C (2^(S n))) :
  let pmat := (V_peval_mat (V_odd_nth_roots (S n))) in
  let prod := V_mat_mat_mult pmat (V_conj_mat (transpose pmat)) in
  V_mat_vec_mult prod cl = Vscale (RtoC (2^S n)%R) cl.
Proof.
  generalize (V_decode_mat_encode_mat_on_diag n); intros.
  generalize (V_decode_mat_encode_mat_off_diag n); intros.  
  simpl in H; simpl in H0.
  unfold prod, pmat.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold V_mat_vec_mult, Vscale.
  unfold V_inner_prod.
  generalize (vector_sum_all_but_1_0  (2 ^ S n) (proj1_sig x) ((RtoC (2 ^ S n)%R) * cl x)); intros.
  rewrite <- H1.
  f_equal.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  clear H1.
  destruct (eq_nat_decide (proj1_sig x) (proj1_sig x0)).
  - apply eq_nat_eq in e.
  specialize (H x).
    assert (x0 = x).
    {
      admit.
    }
    rewrite H1.
    apply (f_equal (fun z => (z * cl x)%C)) in H.
    replace (2 ^ S n)%R with (2 * 2^n)%R by now simpl.
    rewrite <- H.
    f_equal.
  - specialize (H0 x x0).
    cut_to H0.
    + apply (f_equal (fun z => (z * cl x0)%C)) in H0.
      rewrite Cmult_0_l in H0.
      rewrite <- H0.
      f_equal.
    + unfold not; intros.
      now apply eq_eq_nat in H1.
Admitted.


Lemma V_deocde_mat_encode_mat (n : nat) (cl : Vector C (2^(S n))) :
  let pmat := (V_peval_mat (V_odd_nth_roots (S n))) in
  let encmat := (V_conj_mat (transpose pmat)) in
  V_mat_vec_mult pmat (V_mat_vec_mult encmat cl) = Vscale (RtoC (2^S n)%R) cl.
Proof.
  generalize (V_deocde_mat_encode_mat_assoc_l n cl); intros.
  rewrite <- H.
  now rewrite V_mmv_mult_assoc.
Qed.

                             
