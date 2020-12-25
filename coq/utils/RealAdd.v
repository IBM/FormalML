Require Import Coq.Reals.Rbase Coq.Reals.RList.
Require Import Coq.Reals.Rfunctions.
Require Import Ranalysis_reg.
Require Import Coquelicot.Hierarchy Coquelicot.PSeries Coquelicot.Series Coquelicot.ElemFct.
Require Import Coquelicot.Lim_seq.
Require Import Lia Lra.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List.
Require Import Morphisms Permutation.
Require Import EquivDec.

Require Import LibUtils ListAdd.
Require Import Relation_Definitions Sorted.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

Local Open Scope R.


Lemma INR_nzero {n} :
  (n > 0)%nat -> INR n <> 0.
Proof.
  destruct n.
  - lia.
  - rewrite S_INR.
    generalize (pos_INR n); intros.
    lra.
Qed.

Lemma INR_nzero_eq {n} :
  (~ n = 0)%nat -> INR n <> 0.
Proof.
  destruct n.
  - lia.
  - rewrite S_INR.
    generalize (pos_INR n); intros.
    lra.
Qed.

Lemma INR_zero_lt {n} :
  (n > 0)%nat -> 0 < INR n.
Proof.
  destruct n.
  - lia.
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

Lemma pos_Rl_nth (l:list R) n : pos_Rl l n = nth n l 0.
Proof.
  revert n.
  induction l; destruct n; simpl in *; trivial.
Qed.

Hint Rewrite pos_Rl_nth  : R_iso.

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
  - replace (s+0)%nat with s by lia.
    lra.
  - specialize (IHn (S s)).
    unfold Rminus in *.    
    rewrite Rplus_assoc in *.
    f_equal.
    simpl in IHn.
    replace (S (s + n))%nat with (s + (S n))%nat in IHn by lia.
    rewrite IHn.
    replace (s+1)%nat with (S s) by lia.
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

Definition Int_SF_alt l k
  := fold_right Rplus 0
                (map (fun '(x,y) => x * y)
                     (combine l
                              (map (fun '(x,y) => y - x) (adjacent_pairs k)))).

Lemma Int_SF_alt_eq l k :
  Int_SF l k = Int_SF_alt l k.
Proof.
  unfold Int_SF_alt.
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
  lia.
Qed.

Lemma up_nonneg (r:R) :
  r>=0 -> ((up r) >= 0)%Z.
Proof.
  inversion 1.
  - unfold Z.ge; rewrite up_pos; congruence.
  - subst. rewrite up0.
    lia.
Qed.

Lemma INR_up_pos r :
  r >= 0 -> INR (Z.to_nat (up r)) = IZR (up r).
Proof.
  intros.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id; trivial.
  generalize (up_nonneg _ H).
  lia.
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

Section list_sum.


Fixpoint list_sum (l : list R) : R :=
  match l with
  | nil => 0
  | x :: xs => x + list_sum xs
  end.

Lemma list_sum_cat (l1 l2 : list R) :
  list_sum (l1 ++ l2) = (list_sum l1) + (list_sum l2).
Proof.
  induction l1.
  * simpl ; nra.
  * simpl.  nra.
Qed.

Lemma list_sum_map_concat (l : list(list R)) :
  list_sum (concat l) = list_sum (map list_sum l).
Proof.
  induction l.
  - simpl ; reflexivity.
  - simpl ; rewrite list_sum_cat. now rewrite IHl.
Qed.



Global Instance list_sum_Proper : Proper (@Permutation R ==> eq) list_sum.
Proof.
  unfold Proper. intros x y H.
  apply (@Permutation_ind_bis R (fun a b => list_sum a = list_sum b)).
  - simpl ; lra.
  - intros x0 l l' Hpll' Hll'. simpl ; f_equal. assumption.
  - intros x0 y0 l l' H0 H1. simpl. rewrite H1 ; lra.
  - intros l l' l'' H0 H1 H2 H3. rewrite H1. rewrite <-H3. reflexivity.
  - assumption.
Qed.

Lemma list_sum_perm_eq (l1 l2 : list R) : Permutation l1 l2 -> list_sum l1 = list_sum l2.
Proof.
  intro H.
  now rewrite H.
Qed.

  Lemma list_sum_const_mul {A : Type} f (l : list A) :
    forall r, list_sum (map (fun x => r*f x) l)  =
         r* list_sum (map (fun x => f x) l).
Proof.
  intro r.
  induction l.
  simpl; lra.
  simpl. rewrite IHl ; lra.
Qed.

Lemma list_sum_map_const {A} (l : list A) (a : A) (f : A -> R) :
  list_sum (map (fun x => f a) l) = INR(length l)* (f a).
Proof.
  induction l.
  - simpl ; lra.
  - simpl. rewrite IHl.
    enough (match length l with
            | 0%nat => 1
            | S _ => INR (length l) + 1
            end = INR(length l) + 1).
    rewrite H ; lra.
    generalize (length l) as n.
    intro n.  induction n.
    + simpl ; lra.
    + lra.
Qed.

  Lemma list_sum_map_zero {A} (s : list A)  :
  list_sum (List.map (fun _ => 0) s) = 0.
Proof.
  induction s.
  - simpl; reflexivity.
  - simpl. rewrite IHs ; lra.
Qed.


Lemma list_sum_le {A} (l : list A) (f g : A -> R) :
  (forall a, f a <= g a) ->
  list_sum (List.map f l) <= list_sum (List.map g l).
Proof.
  intros Hfg.
  induction l.
  - simpl ; right ; trivial.
  - simpl. specialize (Hfg a).
    apply Rplus_le_compat ; trivial.
Qed.

Lemma list_sum_mult_const (c : R) (l : list R) :
  list_sum (List.map (fun z => c*z) l) = c*list_sum (List.map (fun z => z) l).
Proof.
  induction l.
  simpl; lra.
  simpl in *. rewrite IHl.
  lra.
Qed.

Lemma list_sum_const_mult_le {x y : R} (l : list R) (hl : list_sum l = R1) (hxy : x <= y) :
  list_sum (List.map (fun z => x*z) l) <= y.
Proof.
  rewrite list_sum_mult_const. rewrite map_id.
  rewrite hl. lra.
Qed.

Lemma list_sum_fun_mult_le {x y D : R} {f g : R -> R}(l : list R)(hf : forall z, f z <= D) (hg : forall z , 0 <= g z) :
  list_sum (List.map (fun z => (f z)*(g z)) l) <= D*list_sum (List.map (fun z => g z) l).
Proof.
  induction l.
  simpl. lra.
  simpl. rewrite Rmult_plus_distr_l.
  assert (f a * g a <= D * g a). apply Rmult_le_compat_r. exact (hg a). exact (hf a).
  exact (Rplus_le_compat _ _ _ _ H IHl).
Qed.

Lemma list_sum_map (A:Type) (f g : A -> R) (l : list A) :
     list_sum (map f l) + list_sum (map g l) = 
     list_sum (map (fun x => f x + g x) l).
Proof.
  rewrite <- list_sum_cat.
  rewrite map2_app_interleave_perm.
  rewrite list_sum_map_concat.
  rewrite map_map.
  simpl.
  f_equal.
  apply map_ext; intros.
  lra.
Qed.

Lemma list_sum_fold_right l : list_sum l = fold_right Rplus 0 l.
Proof.
  induction l; firstorder.
Qed.

Lemma list_sum_pos_pos l :
  Forall (fun x => x >= 0) l ->
  list_sum l >= 0.
Proof.
  induction l; simpl; try lra.
  intros HH; invcs HH.
  specialize (IHl H2).
  lra.
Qed.

Lemma list_sum_all_pos_zero_all_zero l : list_sum l = 0 ->
                                         Forall (fun x => x >= 0) l ->
                                         Forall (fun x => x = 0) l.
Proof.
  induction l; intros.
  - constructor.
  - invcs H0.
    simpl in H.
    generalize (list_sum_pos_pos _ H4); intros HH.
    assert (a = 0) by lra.
    subst.
    field_simplify in H.
    auto.
Qed.

End list_sum.

Lemma Rsqrt_le (x y : nonnegreal) : 
  x <= y <-> Rsqrt x <= Rsqrt y.
Proof.
  split; intros.
  - apply Rsqr_incr_0; try apply Rsqrt_positivity.
    unfold Rsqr.
    now repeat rewrite Rsqrt_Rsqrt.
  - rewrite <- (Rsqrt_Rsqrt x).
    rewrite <- (Rsqrt_Rsqrt y).
    apply Rsqr_incr_1; try apply Rsqrt_positivity.
    trivial.
Qed.

Lemma Rsqrt_sqr (x:nonnegreal) :
  Rsqrt {| nonneg := x²; cond_nonneg := Rle_0_sqr x |} = x.
Proof.
  unfold Rsqr.
  apply Rsqr_inj.
  - apply Rsqrt_positivity.
  - apply cond_nonneg.
  - unfold Rsqr. rewrite Rsqrt_Rsqrt.
    trivial.
Qed.

Lemma Rsqr_le_to_Rsqrt (r x:nonnegreal):
  x² <= r <-> x <= Rsqrt r.
Proof.
  intros.
  etransitivity.
  - eapply (Rsqrt_le (mknonnegreal _ (Rle_0_sqr x)) r).
  - rewrite Rsqrt_sqr.
    intuition.
Qed.

Lemma Rsqr_continuous :
  continuity Rsqr.
Proof.
  apply derivable_continuous.
  apply derivable_Rsqr.
Qed.

Global Instance EqDecR : EqDec R eq := Req_EM_T.

Section sum_n.


Lemma sum_n_pos {a : nat -> R} (n:nat) : (forall n, 0 < a n) -> 0 < sum_n a n.
Proof.
  intros.
  induction n.
  - unfold sum_n.
    now rewrite sum_n_n.
  - unfold sum_n.
    rewrite sum_n_Sm.
    apply Rplus_lt_0_compat ; trivial.
    lia.
Qed.

Lemma sum_n_zero (n : nat): sum_n (fun _ => 0) n = 0.
Proof.
  induction n.
  + unfold sum_n. now rewrite sum_n_n.
  + unfold sum_n. rewrite sum_n_Sm.
    unfold sum_n in IHn. rewrite IHn.
    unfold plus. simpl ; lra.
    lia.
Qed.

(* TODO(Kody) : Maybe get rid of Functional Extensionality? *)
Lemma Series_nonneg {a : nat -> R} : ex_series a -> (forall n, 0 <= a n) -> 0 <= Series a.
Proof.
  intros Ha Hpos.
  generalize (Series_le (fun n => 0) a).
  intros H.
  assert (forall n, 0 <= 0 <= a n) by (intro n; split ; try (lra ; trivial) ; try (trivial)).
  specialize (H H0 Ha).
  assert (Series (fun _ => 0) = 0).
  unfold Series.
  assert (sum_n (fun _ => 0) = (fun _ => 0))
    by (apply FunctionalExtensionality.functional_extensionality ; intros ; apply sum_n_zero).
  rewrite H1. now rewrite Lim_seq_const.
  now rewrite H1 in H.
Qed.


Lemma Series_pos {a : nat -> R} : ex_series a -> (forall n, 0 < a n) -> 0 < Series a.
Proof.
  intros Ha Hpos.
  rewrite Series_incr_1 ; trivial.
  apply Rplus_lt_le_0_compat ; trivial.
  apply Series_nonneg.
  + now rewrite <-ex_series_incr_1.
  + intros n. left. apply (Hpos (S n)).
Qed.

End sum_n.



Section expprops.

Lemma ex_series_exp_even (x:R): ex_series (fun k :nat => /INR(fact(2*k))*(x^2)^k).
Proof.
  generalize (ex_series_le (fun k : nat => /INR(fact (2*k))*(x^2)^k) (fun k : nat => (x^2)^k /INR(fact k)));intros.
  apply H. unfold norm. simpl.
  intros n. replace (n+(n+0))%nat with (2*n)%nat by lia.
  replace (x*1) with x by lra.
  replace ((x*x)^n) with (x^(2*n)).
  rewrite Rabs_mult. rewrite Rmult_comm.
  replace (Rabs (x^(2*n))) with (x^(2*n)).
  apply Rmult_le_compat_l.
  rewrite pow_mult. apply pow_le.
  apply Ratan.pow2_ge_0.
  generalize Rprod.INR_fact_lt_0;intros.
  rewrite Rabs_right.
  apply Rinv_le_contravar ; trivial.
  apply le_INR.
  apply fact_le ; lia.
  left.  apply Rlt_gt.
  apply Rinv_0_lt_compat ; trivial.
  symmetry. apply Rabs_right.
  rewrite pow_mult. apply Rle_ge.
  apply pow_le. apply Ratan.pow2_ge_0.
  rewrite pow_mult. f_equal ; lra.
  exists (exp (x^2)).
  generalize (x^2) as y. intro y.
  apply is_exp_Reals.
Qed.


Lemma ex_series_exp_odd (x:R): ex_series (fun k :nat => /INR(fact(2*k + 1)) * (x^2)^k).
Proof.
  generalize (ex_series_le (fun k : nat => (/INR(fact (2*k + 1))*(x^2)^k)) (fun k : nat => (x^2)^k /INR(fact k)));intros.
  apply H ; intros.
  unfold norm ; simpl.
  replace (n+(n+0))%nat with (2*n)%nat by lia.
  replace (x*1) with x by lra.
  replace ((x*x)^n) with (x^(2*n)) by (rewrite pow_mult ; f_equal ; lra).
  rewrite Rabs_mult.
  replace (Rabs (x^(2*n))) with (x^(2*n)).
  rewrite Rmult_comm. unfold Rdiv.
  apply Rmult_le_compat_l.
  rewrite pow_mult ; apply pow_le ;apply Ratan.pow2_ge_0.
  generalize Rprod.INR_fact_lt_0;intros.
  rewrite Rabs_right.
  apply Rinv_le_contravar ; trivial.
  apply le_INR.
  apply fact_le ; lia.
  left. apply Rlt_gt.
  apply Rinv_0_lt_compat ; trivial.
  symmetry. apply Rabs_right.
  rewrite pow_mult. apply Rle_ge.
  apply pow_le. apply Ratan.pow2_ge_0.
  exists (exp (x^2)).
  generalize (x^2) as y. intro y.
  apply is_exp_Reals.
Qed.

Lemma exp_even_odd (x : R) :
  exp x = (Series (fun n => (x^(2*n)/INR(fact (2*n)) + x^(2*n + 1)/INR(fact (2*n + 1))))).
Proof.
  rewrite exp_Reals.
  rewrite PSeries_odd_even ;
    try (rewrite ex_pseries_R ; apply ex_series_exp_even) ;
    try (rewrite ex_pseries_R ; apply ex_series_exp_odd).
  unfold PSeries.
  rewrite <-Series_scal_l.
  rewrite <-Series_plus ; try (apply ex_series_exp_even).
  -- apply Series_ext ; intros. f_equal.
     rewrite pow_mult.
     now rewrite Rmult_comm.
     rewrite Rmult_comm. rewrite <-pow_mult.
     rewrite Rmult_assoc.
     replace (x^(2*n)*x) with (x^(2*n +1)) by (rewrite pow_add ; f_equal ; lra).
     now rewrite Rmult_comm.
  --  generalize (ex_series_scal x (fun n => (/ INR (fact (2 * n + 1)) * (x ^ 2) ^ n)))
      ;intros.
      apply H.
      apply ex_series_exp_odd.
Qed.

Lemma ex_series_even_odd (x:R) :
  ex_series (fun n : nat => x ^ (2 * n) / INR (fact (2 * n)) + x ^ (2 * n + 1) / INR (fact (2 * n + 1))).
Proof.
   generalize ex_series_exp_odd ; intros Hodd.
    generalize ex_series_exp_even ; intros Heven.
    specialize (Hodd x).
    specialize (Heven x).
    assert (Heven' : ex_series (fun n => x^(2*n)/INR (fact (2*n)))).
    {
      eapply (ex_series_ext); intros.
      assert (/INR(fact(2*n))*(x^2)^n = x^(2*n)/INR(fact (2*n)))
        by (rewrite pow_mult; apply Rmult_comm).
      apply H.
      apply Heven.
    }
    assert (Hodd' : ex_series (fun n => x^(2*n + 1)/INR (fact (2*n + 1)))).
    {
      eapply (ex_series_ext); intros.
      assert (x*(/INR(fact(2*n + 1))*(x^2)^n) = x^(2*n + 1)/INR(fact (2*n + 1))).
      rewrite Rmult_comm. rewrite <-pow_mult.
      rewrite pow_add. rewrite pow_1. rewrite Rmult_assoc.
      now rewrite Rmult_comm at 1.
      apply H.
      generalize (ex_series_scal x (fun n => (/ INR (fact (2 * n + 1)) * (x ^ 2) ^ n)))
      ;intros.
      apply H. apply Hodd.
    }
    generalize (ex_series_plus _ _ Heven' Hodd') ; intros.
    exact H.
Qed.


Lemma exp_even_odd_incr_1 (x : R) :
  exp x = (1 + x) + (Series (fun n =>
                            (x^(2*(S n)))/INR(fact (2*(S n)))
                               + x^(2*(S n) + 1)/INR(fact (2*(S n) + 1)))).
Proof.
  rewrite exp_even_odd.
  rewrite Series_incr_1 at 1.
  + simpl.
    f_equal.
    field.
  + apply ex_series_even_odd.
Qed.


Lemma exp_ineq2 : forall x : R, x <= -1 -> (1 + x < exp x).
Proof.
  intros x Hx.
  eapply Rle_lt_trans with 0.
  - lra.
  - apply exp_pos.
Qed.


Lemma exp_ineq3_aux (n : nat) {x : R}:
  (-1 < x < 0) -> 0 < (x^(2*n)/INR(fact (2*n)) + x^(2*n + 1)/INR(fact (2*n + 1))).
Proof.
  intros Hx.
  replace (x^(2*n + 1)) with (x^(2*n) * x) by (rewrite pow_add ; ring).
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite <-Rmult_plus_distr_l.
  apply Rmult_gt_0_compat.
  -- rewrite pow_mult.
     apply Rgt_lt. apply pow_lt.
     apply Rcomplements.pow2_gt_0 ; lra.
  -- replace (/INR(fact (2*n))) with (1 / INR(fact (2*n))) by lra.
     replace (x*/INR(fact(2*n+1))) with (x/INR(fact(2*n + 1))) by trivial.
     rewrite Rcomplements.Rdiv_plus.
     2,3 : (apply (not_0_INR _ (fact_neq_0 _))).
     rewrite <-mult_INR. unfold Rdiv.
     apply Rmult_gt_0_compat.
     2: apply Rinv_pos ; rewrite mult_INR ;
        apply Rmult_gt_0_compat ; apply Rprod.INR_fact_lt_0.
     eapply Rlt_le_trans with (INR(fact(2*n)) + x*INR(fact(2*n))).
     --- replace (INR(fact(2*n)) + x*INR(fact(2*n)))
         with (1*INR(fact(2*n)) + x* INR(fact(2*n))) by (f_equal ; now rewrite Rmult_1_l).
         rewrite <-Rmult_plus_distr_r.
         apply Rmult_lt_0_compat ; try lra ; try (apply Rprod.INR_fact_lt_0).
     --- rewrite Rmult_1_l.
         apply Rplus_le_compat_r. apply le_INR.
         apply fact_le ; lia.
Qed.

Lemma exp_ineq3 {x : R} : -1 < x < 0 -> 1+x < exp x.
Proof.
  intro Hx.
  rewrite exp_even_odd.
  rewrite Series_incr_1. 2 : apply ex_series_even_odd.
  replace (1+x) with (1+x+ 0) by ring.
  replace (2*0) with 0 by lra.
  replace (fact(2*0)) with 1%nat by (simpl;trivial).
  replace (fact(2*0 + 1)) with 1%nat by (simpl;trivial).
  replace (x^(2*0)) with 1 by (simpl;trivial).
  replace (x^(2*0 + 1)) with x by (simpl;trivial;ring).
  replace (INR 1) with 1 by (simpl;trivial).
  replace (1/1 + x/1) with (1+x) by field.
  apply Rplus_lt_compat_l.
  apply Series_pos.
  + generalize (ex_series_even_odd x) ;intros.
    now rewrite ex_series_incr_1 in H.
  + intro n. now apply exp_ineq3_aux.
Qed.


Lemma exp_ineq (x : R) : 1+x <= exp x.
Proof.
  destruct (Rlt_or_le (-1) x).
  + destruct (Rlt_or_le x 0).
    -- left. apply exp_ineq3. lra.
    -- destruct H0.
       ++ left. now apply exp_ineq1.
       ++ right. subst ; simpl.
          rewrite exp_0 ; lra.
  + left. now apply exp_ineq2.
Qed.

End expprops.

Section convex.

  Definition convex (f : R -> R) (a x y : R) :=
    0<=a<=1 -> f (a * x + (1-a) * y) <= a * f x + (1-a)*f y.

  Lemma compose_convex (f g : R -> R) (a x y : R) :
    (forall (x y : R), convex f a x y) ->
    convex g a x y -> 
    increasing f ->
    convex (fun z => f (g z)) a x y.
  Proof.
    unfold convex, increasing.
    intros.
    apply Rle_trans with (r2 := f (a * g x + (1 - a) * g y)).
    apply H1.
    now apply H0.
    now apply H.
 Qed.

  Lemma abs_convex : forall (a x y : R), convex Rabs a x y.
   Proof.
     unfold convex; intros.
     generalize (Rabs_triang (a*x) ((1-a)*y)); intros.
     do 2 rewrite Rabs_mult in H0.
     replace (Rabs a) with a in H0.
     replace (Rabs (1-a)) with (1-a) in H0.
     apply H0.
     now rewrite Rabs_right; lra.
     now rewrite Rabs_right; lra.
  Qed.
     
   Lemma pos_convex_deriv (f f' : R -> R) :
     (forall c : R,  0 <= c -> derivable_pt_lim f c (f' c)) ->
     (forall x y : R, 0 <= x -> 0 <= y  -> f y >= f x + f' x * (y - x)) ->
     forall x y c : R, 0 <= x -> 0 <= y -> convex f c x y.
     Proof.
     unfold convex.
     intros.
     assert (0 <= c * x + (1-c)*y).
     apply Rmult_le_compat_l with (r := c) in H1; try lra.
     apply Rmult_le_compat_l with (r := 1-c) in H2; try lra.     
     
     generalize (H0 (c * x + (1-c)*y) x H4 H1); intros.
     generalize (H0 (c * x + (1-c)*y) y H4 H2); intros.
     apply Rge_le in H5.
     apply Rge_le in H6.
     apply Rmult_le_compat_l with (r := c) in H5; try lra.
     apply Rmult_le_compat_l with (r := 1-c) in H6; try lra.
   Qed.
     
   Lemma pos_deriv_incr_convex (f f' : R -> R) :
     (forall c : R,  0 <= c -> derivable_pt_lim f c (f' c)) ->
     (forall (x y : R), 0<=x -> 0 <= y -> x <= y -> f' x <= f' y) ->
     forall (x y : R), 0 <= x -> 0 <= y -> f y >= f x + f' x * (y-x).
   Proof.
     intros.
     generalize (MVT_cor3 f f'); intros.
     destruct (Rtotal_order x y).
     - specialize (H3 x y H4).
       cut_to H3.
       + destruct H3 as [x0 [? [? ?]]].
         assert (f' x <= f' x0) by (apply H0; lra).
         apply Rmult_le_compat_r with (r := (y-x)) in H7; lra.
       + intros; apply H; lra.
     - destruct H4; [subst; lra| ].
       specialize (H3 y x H4).
       cut_to H3.
       + destruct H3 as [x0 [? [? ?]]].
         assert (f' x0 <= f' x) by (apply H0; lra).
         apply Rmult_le_compat_r with (r := (x-y)) in H7; lra.
       + intros; apply H; lra.
  Qed.

   Lemma pow_convex (n : nat) :
     forall (a x y : R), 0<=x -> 0<=y ->  convex (fun z => pow z n) a x y.
  Proof.
    intros.
    apply pos_convex_deriv with (f' := fun z => INR n * pow z (pred n)); trivial.
    - intros; apply derivable_pt_lim_pow.
    - intros.
      apply (pos_deriv_incr_convex (fun z => pow z n) (fun z => INR n * pow z (pred n))); trivial.
      + intros; apply derivable_pt_lim_pow.
      + intros.
        apply Rmult_le_compat_l; [apply pos_INR |].
        apply pow_maj_Rabs; trivial.
        rewrite Rabs_right; lra.
  Qed.

  Lemma exp_convex {r : R}:
    forall (x y : R),(0 <= x) -> (0 <= y) -> convex exp r x y.
  Proof.
    intros.
    eapply pos_convex_deriv with  (f' := exp) ; trivial.
    - intros; apply derivable_pt_lim_exp.
    - intros.
      apply (pos_deriv_incr_convex); trivial.
      + intros; apply derivable_pt_lim_exp.
      + intros.
        destruct H5 ; trivial.
        -- left. apply exp_increasing ; trivial.
        -- subst ; trivial.
           right ; trivial.
  Qed.

End convex.
