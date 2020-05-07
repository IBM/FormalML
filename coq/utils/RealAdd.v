Require Import Coq.Reals.Rbase Coq.Reals.RList.
Require Import Coq.Reals.Rfunctions.
Require Import Ranalysis_reg.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List.
Require Import EquivDec Nat Omega Lra.

Require Import LibUtils ListAdd.
Require Import Relation_Definitions Sorted.

Require Import Isomorphism.

Import ListNotations.

Local Open Scope R.


Lemma INR_nzero {n} :
  (n > 0)%nat -> INR n <> 0.
Proof.
  destruct n.
  - omega.
  - rewrite S_INR.
    generalize (pos_INR n); intros.
    lra.
Qed.

Lemma INR_nzero_eq {n} :
  (~ n = 0)%nat -> INR n <> 0.
Proof.
  destruct n.
  - omega.
  - rewrite S_INR.
    generalize (pos_INR n); intros.
    lra.
Qed.

Lemma INR_zero_lt {n} :
  (n > 0)%nat -> 0 < INR n.
Proof.
  destruct n.
  - omega.
  - rewrite S_INR.
    generalize (pos_INR n); intros.
    lra.
Qed.

Lemma Rinv_pos n :
  0 < n ->
  0 < / n.
Proof.
  intros.
  rewrite <- (Rmult_1_l ( / n)).
  apply Rdiv_lt_0_compat; lra.
Qed.

Lemma pos_Rl_nth (l:list R) n : pos_Rl (iso_b l) n = nth n l 0.
Proof.
  revert n.
  induction l; destruct n; simpl in *; trivial.
Qed.

Lemma Rlength_length (l:list R) : Rlength (iso_b l) = length l.
Proof.
  induction l; simpl in *; trivial.
  rewrite IHl; trivial.
Qed.

Hint Rewrite pos_Rl_nth Rlength_length : R_iso.

Lemma Rlt_le_sub : subrelation Rlt Rle.
Proof.
  repeat red; intuition.
Qed.

Lemma find_bucket_nth_finds_Rle needle l idx d1 d2:
  StronglySorted Rle l ->
  (S idx < length l)%nat ->
  nth idx l d1 < needle ->
  needle <= nth (S idx) l d2 ->
  find_bucket Rle_dec needle l = Some (nth idx l d1, nth (S idx) l d2).
Proof.
  intros.
  apply find_bucket_nth_finds; trivial
  ; repeat red; intros; lra.
Qed.

Lemma find_bucket_bounded_Rle_exists {a b needle} :
  a <= needle <= b ->
  forall l,
    exists lower upper,
      find_bucket Rle_dec needle (a::l++[b]) = Some (lower, upper).
Proof.
  intros.
  apply find_bucket_bounded_le_exists; intros; lra.
Qed.

Lemma telescope_plus_fold_right_sub_seq f s n :
  fold_right Rplus 0 (map (fun x => (f (INR x)) -  (f (INR (x+1)))) (seq s n)) = (f (INR s)) - (f (INR (s+n))).
Proof.
  Opaque INR.
  revert s.
  induction n; simpl; intros s.
  - replace (s+0)%nat with s by omega.
    lra.
  - specialize (IHn (S s)).
    unfold Rminus in *.    
    rewrite Rplus_assoc in *.
    f_equal.
    simpl in IHn.
    replace (S (s + n))%nat with (s + (S n))%nat in IHn by omega.
    rewrite IHn.
    replace (s+1)%nat with (S s) by omega.
    lra.
    Transparent INR.
Qed.

Lemma fold_right_Rplus_mult_const {A:Type} (f:A->R) c l :
  fold_right Rplus 0 (map (fun x : A => f x * c) l) =
  (fold_right Rplus 0 (map (fun x : A => f x) l))*c.
Proof.
  induction l; simpl; lra.
Qed.

Lemma bounded_dist_le  x lower upper :
  lower <= x <= upper ->
  R_dist x upper <= R_dist lower upper.
Proof.
  intros.
  rewrite (R_dist_sym x).
  rewrite (R_dist_sym lower).
  unfold R_dist.
  repeat rewrite Rabs_pos_eq by lra.
  lra.
Qed.

Lemma bounded_dist_le_P2  x lower upper :
  lower <= x <= upper ->
  R_dist x lower <= R_dist upper lower.
Proof.
  intros.
  unfold R_dist.
  repeat rewrite Rabs_pos_eq by lra.
  lra.
Qed.

Definition interval_increasing f (a b:R) : Prop :=
  forall x y :R, a <= x -> y <= b -> x<=y -> f x <= f y.

Definition interval_decreasing f (a b:R) : Prop :=
  forall x y :R, a <= x -> y <= b -> x<=y -> f y <= f x.

Lemma bounded_increasing_dist_le (f : R -> R) x lower upper :
  interval_increasing f lower upper ->
  lower <= x <= upper ->
  R_dist (f x) (f upper) <= R_dist (f lower) (f upper).
Proof.
  intros df xin.
  apply bounded_dist_le.
  destruct xin as [ltx gtx].
  red in df.
  split; apply df; trivial.
  apply Rle_refl.
  apply Rle_refl.  
Qed.

Lemma bounded_decreasing_dist_le (f : R -> R) x lower upper :
  interval_decreasing f lower upper ->
  lower <= x <= upper ->
  R_dist (f x) (f upper) <= R_dist (f lower) (f upper).
Proof.
  intros df xin.
  apply bounded_dist_le_P2.
  destruct xin as [ltx gtx].
  red in df.
  split; apply df; trivial.
  apply Rle_refl.
  apply Rle_refl.
Qed.

Lemma subinterval_increasing (f : R -> R) (a b x y : R) :
  a <= x -> x <= y -> y <= b -> interval_increasing f a b -> interval_increasing f x y.
Proof.
  intros.
  red in H2.
  red.
  intros.
  cut (y0 <= b).
  cut (a <= x0).
  intuition.
  lra.
  lra.
Qed.

Lemma subinterval_decreasing (f : R -> R) (a b x y : R) :
  a <= x -> x <= y -> y <= b -> interval_decreasing f a b -> interval_decreasing f x y.
Proof.
  intros.
  red in H2.
  red.
  intros.
  cut (y0 <= b).
  cut (a <= x0).
  intuition.
  lra.
  lra.
Qed.

Lemma increasing_decreasing_opp (f : R -> R) (a b:R) :
  a <= b -> interval_increasing f a b -> interval_decreasing (fun x => -f x) a b.
Proof.
  unfold interval_increasing.
  unfold interval_decreasing.
  intros.
  apply Ropp_le_contravar.
  apply H0.
  trivial.
  trivial.
  trivial.
Qed.

Fixpoint Int_SF' (l k : list R) {struct l} : R :=
  match l with
  | nil => 0
  | a::l' =>
    match k with
    | nil => 0
    | x::nil => 0
    | x::y::k' => a * (y - x) + Int_SF' l' (y:: k')
    end
  end.

Lemma Int_SF'_eq l k : Int_SF (iso_b l) (iso_b k) = Int_SF' l k.
Proof.
  revert k.
  induction l; simpl; trivial.
  destruct k; simpl; trivial.
  destruct k; simpl; trivial.
  rewrite <- IHl.
  trivial.
Qed.

Definition Int_SF'_alt l k
  := fold_right Rplus 0
                (map (fun '(x,y) => x * y)
                     (combine l
                              (map (fun '(x,y) => y - x) (adjacent_pairs k)))).

Lemma Int_SF'_alt_eq l k :
  Int_SF' l k = Int_SF'_alt l k.
Proof.
  unfold Int_SF'_alt.
  revert k.
  induction l; simpl; trivial.
  destruct k; simpl; trivial.
  destruct k; simpl; trivial.
  rewrite IHl; trivial.
Qed.

Lemma up_IZR n : up (IZR n) = (Z.succ n)%Z.
Proof.
  symmetry.
  apply tech_up; try rewrite succ_IZR; lra.
Qed.

Lemma up0 : up 0 = 1%Z.
Proof.
  apply up_IZR.
Qed.

Lemma up_pos (r:R) :
  r>0 -> ((up r) > 0)%Z.
Proof.
  intros.
  destruct (archimed r) as [lb ub].
  assert (IZR (up r) > 0) by lra.
  apply lt_IZR in H0.
  omega.
Qed.

Lemma up_nonneg (r:R) :
  r>=0 -> ((up r) >= 0)%Z.
Proof.
  inversion 1.
  - unfold Z.ge; rewrite up_pos; congruence.
  - subst. rewrite up0.
    omega.
Qed.

Lemma INR_up_pos r :
  r >= 0 -> INR (Z.to_nat (up r)) = IZR (up r).
Proof.
  intros.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id; trivial.
  generalize (up_nonneg _ H).
  omega.
Qed.

Lemma frac_max_frac_le (x y:R) :
  1 <= x ->
  x <= y ->
  x / (x + 1) <= y / (y + 1).
Proof.
  intros.
  assert (1 <= x) by lra.
  cut (x * (y + 1) <= y * (x + 1)).
  - intros HH.
    apply (Rmult_le_compat_r (/ (x+1))) in HH.
    + rewrite Rinv_r_simpl_l in HH by lra.
      apply (Rmult_le_compat_r (/ (y+1))) in HH.
      * eapply Rle_trans; try eassumption.
        unfold Rdiv.
        repeat rewrite Rmult_assoc.
        apply Rmult_le_compat_l; [lra | ].
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m by lra.
        right; trivial.
      * left; apply Rinv_0_lt_compat; lra.
    + left; apply Rinv_0_lt_compat; lra.
  - lra.
Qed.
