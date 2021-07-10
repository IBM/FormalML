Require Import Program.Basics.
Require Import Coq.Reals.Rbase Coq.Reals.RList.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rprod Coq.Reals.ROrderedType.
Require Import Ranalysis_reg utils.Finite.
Require Import Coquelicot.Coquelicot.
Require Import Lia Lra.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List Finite.
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

  Lemma list_sum_map_ext {A : Type} (f g : A -> R) (l : list A):
    (forall x, f x = g x) -> list_sum (map f l) = list_sum (map g l).
  Proof.
    intros Hfg.
    f_equal. now apply List.map_ext.
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

  Lemma list_sum_map_add {A:Type} (f g : A -> R) (l : list A) :
    list_sum (map (fun x => f x + g x) l) =
    list_sum (map f l) + list_sum (map g l).
  Proof.
    induction l; simpl; lra.
  Qed.

  Lemma list_sum_map_sub {A:Type} (f g : A -> R) (l : list A) :
    list_sum (map (fun x => f x - g x) l) =
    list_sum (map f l) - list_sum (map g l).
  Proof.
    induction l; simpl; lra.
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

Lemma list_sum_pos_pos' l :
  Forall (fun x => 0 <= x) l ->
  0 <= list_sum l.
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

Lemma Rsqrt_lt (x y : nonnegreal) : 
  x < y <-> Rsqrt x < Rsqrt y.
Proof.
  split.
  - generalize (Rsqr_incrst_0 (Rsqrt x) (Rsqrt y)); intros.
    apply H.
    unfold Rsqr.
    now repeat rewrite Rsqrt_Rsqrt.
    apply Rsqrt_positivity.
    apply Rsqrt_positivity.    
  - rewrite <- (Rsqrt_Rsqrt x).
    rewrite <- (Rsqrt_Rsqrt y).
    generalize (Rsqr_incrst_1 (Rsqrt x) (Rsqrt y)); unfold Rsqr; intros.
    apply H; trivial.
    apply Rsqrt_positivity.
    apply Rsqrt_positivity.    
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

Lemma Rsqr_lt_to_Rsqrt (x r:nonnegreal) :
  r < x² <-> Rsqrt r < x.
Proof.
  intros.
  etransitivity.
  - eapply (Rsqrt_lt r (mknonnegreal _ (Rle_0_sqr x))).
  - rewrite Rsqrt_sqr.
    intuition.
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

  Lemma sum_n_pos {a : nat -> R} (N:nat) : 
    (forall n, (n <= N)%nat -> 0 < a n) -> 
    0 < sum_n a N.
  Proof.
    intros.
    induction N.
    - unfold sum_n.
      rewrite sum_n_n.
      apply H; lia.
    - rewrite sum_Sn.
      apply Rplus_lt_0_compat.
      apply IHN.
      intros.
      apply H; lia.
      apply H; lia.
  Qed.

  Lemma sum_n_nneg {a : nat -> R} (N:nat) : 
    (forall n, (n <= N)%nat -> 0 <= a n) -> 
    0 <= sum_n a N.
  Proof.
    intros.
    induction N.
    - unfold sum_n.
      rewrite sum_n_n.
      apply H; lia.
    - rewrite sum_Sn.
      apply Rplus_le_le_0_compat.
      apply IHN.
      intros.
      apply H; lia.
      apply H; lia.
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
  
  Lemma convex_deriv (f f' : R -> R) :
    (forall c : R,  derivable_pt_lim f c (f' c)) ->
    (forall x y : R, f y >= f x + f' x * (y - x)) ->
    forall x y c : R, convex f c x y.
  Proof.
    unfold convex.
    intros.
    generalize (H0 (c * x + (1-c)*y) x); intros.
    generalize (H0 (c * x + (1-c)*y) y); intros.
    apply Rge_le in H2.
    apply Rge_le in H3.
    apply Rmult_le_compat_l with (r := c) in H2; try lra.
    apply Rmult_le_compat_l with (r := 1-c) in H3; try lra.
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

  Lemma ppos_convex_deriv (f f' : R -> R) :
    (forall c : R,  0 < c -> derivable_pt_lim f c (f' c)) ->
    (forall x y : R, 0 < x -> 0 < y  -> f y >= f x + f' x * (y - x)) ->
    forall x y c : R, 0 < x -> 0 < y -> convex f c x y.
  Proof.
    unfold convex.
    intros.
    assert (ineq:0 < c * x + (1-c)*y).
    {
      destruct (Req_EM_T c 0).
      - subst.
        lra.
      - apply Rplus_lt_le_0_compat.
        + apply Rmult_lt_0_compat; lra.
        + apply Rmult_le_pos; lra.
    }
    generalize (H0 (c * x + (1-c)*y) x ineq H1); intros HH1.
    generalize (H0 (c * x + (1-c)*y) y ineq H2); intros HH2.
    apply Rge_le in HH1.
    apply Rge_le in HH2.
    apply Rmult_le_compat_l with (r := c) in HH1; try lra.
    apply Rmult_le_compat_l with (r := 1-c) in HH2; try lra.
  Qed.

  Lemma deriv_incr_convex (f f' : R -> R) :
    (forall c : R,   derivable_pt_lim f c (f' c)) ->
    (forall (x y : R), x <= y -> f' x <= f' y) ->
    forall (x y : R), f y >= f x + f' x * (y-x).
  Proof.
    intros.
    generalize (MVT_cor3 f f'); intros.
    destruct (Rtotal_order x y).
    - specialize (H1 x y H2).
      cut_to H1.
      + destruct H1 as [x0 [? [? ?]]].
        assert (f' x <= f' x0) by (apply H0; lra).
        apply Rmult_le_compat_r with (r := (y-x)) in H5; lra.
      + intros; apply H; lra.
    - destruct H2; [subst; lra| ].
      specialize (H1 y x H2).
      cut_to H1.
      + destruct H1 as [x0 [? [? ?]]].
        assert (f' x0 <= f' x) by (apply H0; lra).
        apply Rmult_le_compat_r with (r := (x-y)) in H5; lra.
      + intros; apply H; lra.
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

  Lemma ppos_deriv_incr_convex (f f' : R -> R) :
    (forall c : R,  0 < c -> derivable_pt_lim f c (f' c)) ->
    (forall (x y : R), 0<x -> 0 < y -> x <= y -> f' x <= f' y) ->
    forall (x y : R), 0 < x -> 0 < y -> f y >= f x + f' x * (y-x).
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

  Lemma exp_convex (r : R):
    forall (x y : R), convex exp r x y.
  Proof.
    intros.
    eapply convex_deriv with  (f' := exp) ; trivial.
    - intros; apply derivable_pt_lim_exp.
    - intros.
      apply deriv_incr_convex; trivial.
      + intros; apply derivable_pt_lim_exp.
      + intros.
        destruct H ; trivial.
        -- left. apply exp_increasing ; trivial.
        -- subst ; trivial.
           right ; trivial.
  Qed.

End convex.

Section Rpower.

  Lemma Rpower_pos b e : 0 < Rpower b e.
  Proof.
    unfold Rpower.
    apply exp_pos.
  Qed.

  Lemma Rpower_nzero b e : ~ (Rpower b e = 0).
  Proof.
    generalize (Rpower_pos b e).
    lra.
  Qed.


  Lemma Rpower_inv_cancel x n :
    0 < x ->
    n <> 0 ->
    Rpower (Rpower x n) (Rinv n) = x.
  Proof.
    intros.
    rewrite Rpower_mult.
    rewrite <- Rinv_r_sym; trivial.
    now rewrite Rpower_1.
  Qed.

  Lemma pow0_Sbase n : pow 0 (S n) = 0.
  Proof.
    simpl; field.
  Qed.

  Lemma pow_integral n y :
    y ^ S n = 0 -> y = 0.
  Proof.
    intros.
    induction n; simpl in *.
    - lra.
    - apply Rmult_integral in H.
      destruct H; lra.
  Qed.
  
  Lemma Rabs_pow_eq_inv x y n :
    Rabs x ^ S n = Rabs y ^ S n ->
    Rabs x = Rabs y.
  Proof.
    intros.
    destruct (Req_EM_T x 0).
    - subst.
      rewrite Rabs_pos_eq in H by lra.
      rewrite pow0_Sbase in H.
      symmetry in H.
      apply pow_integral in H.
      apply Rcomplements.Rabs_eq_0 in H.
      congruence.
    - destruct (Req_EM_T y 0).
      + subst.
        symmetry in H.
        rewrite Rabs_pos_eq in H by lra.
        rewrite pow0_Sbase in H.
        symmetry in H.
        apply pow_integral in H.
        apply Rcomplements.Rabs_eq_0 in H.
        congruence.
      + assert (0 < Rabs x) by now apply Rabs_pos_lt.
        assert (0 < Rabs y) by now apply Rabs_pos_lt.
        rewrite <- (Rpower_inv_cancel (Rabs x) (INR (S n))); trivial
        ; try (apply not_0_INR; congruence).
        rewrite <- (Rpower_inv_cancel (Rabs y) (INR (S n))); trivial
        ; try (apply not_0_INR; congruence).
        f_equal.
        repeat rewrite Rpower_pow by trivial.
        trivial.
  Qed.
End Rpower.

Section power.

  (* Rpower at 0 is problematic, so we define a variant that defines it to be 0. *)
  Definition power (b e : R)
    := if Rle_dec b 0
       then 0
       else Rpower b e.

  Lemma power_Rpower (b e : R) :
    0 < b ->
    power b e = Rpower b e.
  Proof.
    unfold power.
    match_destr; lra.
  Qed.

  Lemma power_nonneg (b e : R) :
    0 <= power b e .
  Proof.
    unfold power.
    match_destr; [lra |].
    left; apply Rpower_pos.
  Qed.

  Lemma power_pos (b e : R) :
    0 < b ->
    0 < power b e .
  Proof.
    unfold power.
    match_destr; [lra |].
    intros; apply Rpower_pos.
  Qed.

  Lemma power_Ropp (x y : R) :
    0 < x ->
    power x (- y) = / power x y.
  Proof.
    intros.
    repeat rewrite power_Rpower by trivial.
    apply Rpower_Ropp.
  Qed.
  
  Lemma power_integral b e :
    power b e = 0 ->
    b <= 0.
  Proof.
    unfold power.
    match_destr.
    intros; eelim Rpower_nzero; eauto.
  Qed.

  Lemma power_le_0 b e :
    power b e <= 0 ->
    b <= 0.
  Proof.
    unfold power.
    match_destr.
    generalize (Rpower_pos b e); intros.
    lra.
  Qed.

  Lemma power_mult (x y z : R) :
    power (power x y) z = power x (y * z).
  Proof.
    unfold power.
    generalize (Rpower_pos x y); intros.
    repeat match_destr.
    - lra.
    - lra.
    - apply Rpower_mult.
  Qed.

  Lemma power_plus (x y z : R) :
    power z (x + y) = power z x * power z y.
  Proof.
    unfold power.
    repeat match_destr.
    - lra.
    - apply Rpower_plus.
  Qed.

  Lemma power_1 (x : R) :
    0 <= x ->
    power x 1 = x.
  Proof.
    unfold power; intros.
    match_destr; [lra |].
    apply Rpower_1; lra.
  Qed.
  
  Lemma power_O (x : R) :
    0 < x ->
    power x 0 = 1.
  Proof.
    unfold power; intros.
    match_destr; [lra |].
    now apply Rpower_O.
  Qed.

  Lemma powerRZ_power (x : R) (z : Z) :
    0 < x ->
    powerRZ x z = power x (IZR z).
  Proof.
    intros.
    unfold power.
    match_destr; [lra |].
    now apply powerRZ_Rpower.
  Qed.

  Lemma Rle_power (e n m : R) :
    1 <= e ->
    n <= m ->
    power e n <= power e m.
  Proof.
    unfold power; intros.
    match_destr; [lra |].
    now apply Rle_Rpower.
  Qed.

  Lemma power_lt (x y z : R) :
    1 < x ->
    y < z ->
    power x y < power x z.
  Proof.
    unfold power; intros.
    match_destr; [lra |].
    now apply Rpower_lt.
  Qed.

  Lemma power0_Sbase e :
    power 0 e = 0.
  Proof.
    unfold power.
    match_destr.
    lra.
  Qed.

  Lemma power_inv_cancel b e :
    0 <= b ->
    e <> 0 ->
    power (power b (/ e)) e = b.
  Proof.
    intros.
    rewrite power_mult.
    rewrite Rinv_l; trivial.
    now rewrite power_1.
  Qed.

  Lemma inv_power_cancel b e :
    0 <= b ->
    e <> 0 ->
    power (power b e) (/ e) = b.
  Proof.
    intros.
    rewrite power_mult.
    rewrite Rinv_r; trivial.
    now rewrite power_1.
  Qed.

  Lemma power_eq_inv x y n :
    0 <> n ->
    0 <= x ->
    0 <= y ->
    power x n = power y n ->
    x = y.
  Proof.
    intros.
    apply (f_equal (fun x => power x (/n))) in H2.
    now repeat rewrite inv_power_cancel in H2 by lra.
  Qed.

  Lemma power_pow (n : nat) (x : R) :
    0 < x ->
    power x (INR n) = x ^ n.
  Proof.
    unfold power; intros.
    match_destr; [lra |].
    now apply Rpower_pow.
  Qed.

  Lemma power_Spow (n : nat) (x : R) :
    0 <= x ->
    power x (INR (S n)) = x ^ (S n).
  Proof.
    unfold power; intros.
    match_destr.
    - assert (x= 0) by lra.
      subst.
      now rewrite pow0_Sbase.
    - apply Rpower_pow; lra.
  Qed.

  Lemma power2_sqr (x : R) :
    0 <= x ->
    power x 2 = Rsqr x.
  Proof.
    intros.
    replace 2 with (INR 2%nat) by reflexivity.
    rewrite power_Spow by trivial.
    now rewrite Rsqr_pow2.
  Qed.

  Lemma power_abs2_sqr (x : R) :
    power (Rabs x) 2 = Rsqr x.
  Proof.
    rewrite power2_sqr.
    - now rewrite <- Rsqr_abs.
    - apply Rabs_pos.
  Qed.

  Lemma power_2_sqrt (x : nonnegreal) :
    power x (/2) = Rsqrt x.
  Proof.
    intros.
    generalize (Rsqr_eq_abs_0 (power x (/ 2)) (Rsqrt x))
    ; intros HH.
    cut_to HH.
    - rewrite Rabs_right in HH.
      + rewrite Rabs_right in HH; trivial.
        apply Rle_ge.
        apply Rsqrt_positivity.
      + apply Rle_ge.
        apply power_nonneg.
    - unfold Rsqr at 2.
      rewrite Rsqrt_Rsqrt.
      rewrite <- power2_sqr.
      + rewrite power_inv_cancel; trivial.
        apply cond_nonneg.
      + apply power_nonneg.
  Qed.

  Lemma Rlt_power_l (a b c : R) :
    0 < c ->
    0 <= a < b ->
    power a c < power b c.
  Proof.
    unfold power; intros.
    repeat (match_destr; [try lra |]).
    - apply Rpower_pos.
    - apply Rlt_Rpower_l; lra.
  Qed.
  
  Lemma Rle_power_l (a b c : R) :
    0 <= c ->
    0 <= a <= b ->
    power a c <= power b c.
  Proof.
    unfold power; intros.
    repeat (match_destr; [try lra |]).
    - left; apply Rpower_pos.
    - apply Rle_Rpower_l; lra.
  Qed.

  Lemma power_sqrt (x : R) :
    0 <= x ->
    power x (/ 2) = sqrt x.
  Proof.
    unfold power; intros.
    match_destr.
    - assert (x = 0) by now apply Rle_antisym.
      subst.
      now rewrite sqrt_0.
    - apply Rpower_sqrt; lra.
  Qed.

  Lemma power_mult_distr (x y z : R) :
    0 <= x ->
    0 <= y ->
    power x z * power y z = power (x * y) z.
  Proof.
    unfold power; intros.
    repeat match_destr; subst; try lra.
    - assert (x = 0) by lra; subst; lra.
    - assert (x = 0) by lra; subst; lra.
    - assert (y = 0) by lra; subst; lra.
    - assert (0 < x) by lra.
      assert (0 < y) by lra.
      generalize (Rmult_lt_0_compat _ _ H1 H2); intros.
      lra.
    - apply Rpower_mult_distr; lra.
  Qed.
  
  Lemma power_incr_inv (x y:R) (n : R) :
    0 < n ->
    0 <= x ->
    0 <= y ->
    power x n <= power y n ->
    x <= y.
  Proof.
    intros.
    generalize (Rle_power_l (power x n) (power y n) (/n))
    ; intros HH.
    repeat rewrite inv_power_cancel in HH by lra.
    apply HH.
    - now left; apply Rinv_pos.
    - split; trivial.
      apply power_nonneg.
  Qed.

  Lemma derivable_pt_lim_power' (x y : R) :
    0 < x ->
    derivable_pt_lim (fun x0 : R => power x0 y) x (y * power x (y - 1)).
  Proof.
    intros.
    unfold power.
    match_destr.
    - lra.
    - generalize (derivable_pt_lim_power x y H); intros HH.
      apply derivable_pt_lim_locally_ext with (f := fun x => Rpower x y) (a := x/2) (b := x + x/2); trivial.
      + lra.
      + intros.
        match_destr.
        lra.
  Qed.
  
  Lemma Dpower' (y z : R) :
    0 < y ->
    D_in (fun x : R => power x z) (fun x : R => z * power x (z - 1))
         (fun x : R => 0 < x) y.
  Proof.
    intros.
    generalize (derivable_pt_lim_D_in (fun x : R => power x z)
                                      (fun x : R => z * power x (z - 1)) y); intros.
    apply D_in_imp with (D := no_cond).
    intros.
    now unfold no_cond.
    apply H0.
    now apply derivable_pt_lim_power'.
  Qed.

End power.

Section ineqs.

  Lemma Rpower_ln : forall x y : R, ln (Rpower x y) = y*ln x.
  Proof.
    unfold Rpower ; intros.
    now rewrite ln_exp.
  Qed.

  Lemma Rpower_base_1 : forall x : R, Rpower 1 x = 1.
  Proof.
    intros.
    unfold Rpower.
    rewrite ln_1.
    replace (x*0) with 0 by lra.
    apply exp_0.
  Qed.

  Lemma power_base_1 e : power 1 e = 1.
  Proof.
    unfold power.
    match_destr; try lra.
    apply Rpower_base_1.
  Qed.

  Lemma sum_one_le : forall x y : R, 0 <= x -> 0 <= y -> x + y = 1 -> x <= 1.
  Proof.
    intros.
    rewrite <-H1.
    replace (x) with (x+0) by lra.
    replace (x+0+y) with (x+y) by lra.
    apply Rplus_le_compat_l ; trivial.
  Qed.

  Lemma Rmult_four_assoc (a b c d : R) : a * b * (c * d) = a * (b*c) * d.
  Proof.
    ring.
  Qed.

  (*
   This theorem also holds for a b : nonnegreal. But it is awkward since
   Rpower x y is defined in terms of exp and ln.
   *)
  Theorem Rpower_youngs_ineq {p q : posreal} {a b : R} (Hpq : 1/p + 1/q = 1) :
    0 < a -> 0 < b -> a*b <= (Rpower a p)/p + (Rpower b q)/q.
  Proof.
    intros apos bpos.
    replace (a*b) with (exp (ln (a*b)))
      by (rewrite exp_ln ; trivial ; apply Rmult_lt_0_compat ; trivial).
    rewrite ln_mult ; trivial.
    destruct p as [p ppos] ; destruct q as [q qpos] ; simpl in *.
    assert (Hp : p <> 0) by lra.
    assert (Hq : q <> 0) by lra.
    replace (ln a) with (/p*p*(ln a)) by (rewrite Rinv_l ; lra).
    replace (ln b) with (/q*q*(ln b)) by (rewrite Rinv_l ; lra).
    rewrite Rmult_assoc; rewrite Rmult_assoc.
    replace (p*ln a) with (ln(Rpower a p)) by (apply Rpower_ln).
    replace (q*ln b) with (ln(Rpower b q)) by (apply Rpower_ln).
    generalize (exp_convex (/p) (ln (Rpower a p)) (ln(Rpower b q))); intros.
    unfold convex in H. unfold Rdiv.
    replace (/q) with (1 - /p) by lra.
    eapply Rle_trans.
    - apply H.
      split.
      + left ; apply Rinv_pos ; trivial.
      + apply sum_one_le with (y := /q) ; try (left ; apply Rinv_pos ; trivial) ; try lra.
    - right.
      repeat (rewrite exp_ln; try (unfold Rpower ; apply exp_pos)).
      ring.
  Qed.

  Theorem youngs_ineq {p q : posreal} {a b : R} (Hpq : 1/p + 1/q = 1) :
    0 <= a -> 0 <= b -> a*b <= (power a p)/p + (power b q)/q.
  Proof.
    unfold power; intros apos bpos.
    repeat match_destr; subst.
    - assert (a = 0) by lra; subst.
      lra.
    - destruct p; destruct q; simpl in *.
      assert ( a = 0 ) by lra; subst.
      field_simplify; [| lra].
      apply Rmult_le_pos.
      + apply Rmult_le_pos; try lra.
        generalize (Rpower_pos b pos0); lra.
      + left.
        apply Rinv_pos.
        now apply Rmult_lt_0_compat.
    - destruct p; destruct q; simpl in *.
      assert (b = 0) by lra; subst.
      field_simplify; [| lra].
      apply Rmult_le_pos.
      + apply Rmult_le_pos; try lra.
        generalize (Rpower_pos a pos); lra.
      + left.
        apply Rinv_pos.
        now apply Rmult_lt_0_compat.
    - apply Rpower_youngs_ineq; lra.
  Qed.

  (*
    Young's inequality is needed in the proof of Holder's inequality.
   *)

  Theorem youngs_ineq_2 {p q : posreal} (Hpq : 1/p + 1/q = 1):
    forall (t a b : R), 0 <= a -> 0 <= b -> 0 < t ->
                   (power a (1/p))*(power b (1/q)) <= (power t (-1/q))*a/p + (power t (1/p))*b/q.
  Proof.
    intros t a b apos bpos tpos.
    assert (Hq : pos q <> 0)
      by (generalize (cond_pos q) ; intros H notq ; rewrite notq in H ; lra).
    assert (Hp : pos p <> 0)
      by (generalize (cond_pos p) ; intros H notp ; rewrite notp in H ; lra).
    assert (Hap : 0 <= ((power a (1/p))*power t (-1/(q*p))))
      by (apply Rmult_le_pos; apply power_nonneg).
    assert (Hbq : 0 <= (power t (1/(q*p))*(power b (1/q))))
      by (apply Rmult_le_pos; apply power_nonneg).
    generalize (youngs_ineq Hpq Hap Hbq) ; intros.
    rewrite Rmult_four_assoc in H.
    replace (power t (-1/(q*p)) * power t (1/(q*p))) with 1 in H.
    -- ring_simplify in H.
       eapply Rle_trans.
       apply H. clear H.
       repeat (rewrite <-power_mult_distr ; try apply power_nonneg).
       unfold Rdiv.
       repeat (rewrite power_mult).
       replace (1 */p *p) with 1 by (field ; trivial).
       replace (1 */q *q) with 1 by (field ; trivial).
    + repeat (rewrite power_1 ; trivial).
      right.
      f_equal.
      ++  rewrite Rmult_assoc.  rewrite Rmult_comm.
          replace (-1 * /(q*p) * p) with (-1 * /q).
          ring. field ; split ; trivial.
      ++  rewrite Rmult_assoc.
          replace (1 * /(q*p) * q) with (1 * /p).
          ring. field ; split ; trivial.
      -- unfold Rdiv.
         rewrite <-power_plus.
         rewrite <-power_O with (x := t) ; trivial.
         f_equal. rewrite power_O;trivial.
         ring.
  Qed.

  Theorem Rpower_youngs_ineq_2 {p q : posreal} (Hpq : 1/p + 1/q = 1):
    forall (t a b : R), 0 < a -> 0 < b -> 0 < t ->
                   (Rpower a (1/p))*(Rpower b (1/q)) <= (Rpower t (-1/q))*a/p + (Rpower t (1/p))*b/q.
  Proof.
    intros.
    generalize (youngs_ineq_2 Hpq t a b) ; intros HH.
    cut_to HH; try lra.
    now repeat rewrite power_Rpower in HH by lra.
  Qed.        

  
  Corollary ag_ineq (a b : R):
    0 <= a -> 0 <= b ->  sqrt (a*b) <= (a+b)/2.
  Proof.
    intros Ha Hb.
    destruct Ha as [Hapos | Haz].
    destruct Hb as [Hbpos | Hbz].
    ++ rewrite <-Rpower_sqrt ; try (apply Rmult_lt_0_compat ; trivial).
       rewrite <-Rpower_mult_distr ; trivial.
       rewrite Rdiv_plus_distr.
       assert (Hpq : 1/pos(mkposreal 2 Rlt_0_2) + 1/pos(mkposreal 2 Rlt_0_2) = 1)
         by (simpl;field).
       generalize (Rpower_youngs_ineq_2 Hpq 1 a b Hapos Hbpos Rlt_0_1) ; simpl ; intros.
       replace (/2) with (1/2) by lra.
       eapply Rle_trans. apply H.
       repeat rewrite Rpower_base_1.
       right ; field.
    ++ subst. left.
       rewrite Rmult_0_r.
       rewrite sqrt_0 ; lra.
    ++ subst.
       rewrite Rmult_0_l.
       rewrite sqrt_0; lra.
  Qed.

  Lemma pow_minkowski_helper_aux (p:nat) (a t : R) : 0 < t ->
                                                   t*(pow(a/t) (S p)) = (pow a (S p))*(pow (/t) p).
  Proof.
    intros.
    unfold Rdiv.
    rewrite Rpow_mult_distr.
    rewrite Rmult_comm, Rmult_assoc.
    f_equal.
    simpl.
    rewrite Rmult_comm.
    rewrite <- Rmult_assoc.
    rewrite Rinv_r.
    now rewrite Rmult_1_l.
    now apply Rgt_not_eq.
  Qed.

  Lemma pow_minkowski_helper (p : nat) {a b t : R}:
    (0 <= a) -> (0 <= b) -> 0<t<1 ->
    (pow (a+b) (S p)) <= (pow (/t) p)*(pow a (S p)) + (pow (/(1-t)) p)*(pow b (S p)).
  Proof.
    intros Ha Hb Ht.
    assert (Ht1 : t <> 0) by (intro not; destruct Ht as [h1 h2] ; subst ; lra).
    assert (Ht2 : 1-t <> 0) by (intro not; destruct Ht as [h1 h2] ; subst ; lra).
    assert (Hat : 0 <= a/t) by (apply Rcomplements.Rdiv_le_0_compat ; lra).
    assert (Hbt : 0 <= b/(1-t)) by  (apply Rcomplements.Rdiv_le_0_compat ; lra).
    assert (Ht' : 0 <= t <= 1) by lra.
    replace (a+b) with (t*(a/t) + (1-t)*(b/(1-t))) by (field ; split ; trivial).
    generalize (pow_convex (S p) t (a/t) (b/(1-t)) Hat Hbt Ht'); intros.
    eapply Rle_trans. apply H.
    repeat (rewrite pow_minkowski_helper_aux ; try lra).
  Qed.

  Lemma pow_minkowski_subst (p : nat) {a b : R} :
    (0 < a) -> (0 < b) -> 
    (pow (/(a / (a + b))) p)*(pow a (S p)) +
    (pow (/(1-(a / (a + b)))) p)*(pow b (S p)) = (pow (a + b) (S p)).
  Proof.
    intros; simpl.
    assert (a <> 0) by now apply Rgt_not_eq.
    assert (a + b <> 0) by (apply Rgt_not_eq; now apply Rplus_lt_0_compat).
    replace (/ (a / (a + b))) with ((a+b)* (/a)).
    - rewrite Rpow_mult_distr, Rmult_assoc.
      replace ((/ a) ^ p * (a * a ^ p)) with (a).
      + replace (/ (1 - a / (a + b))) with ((a+b)/b).
        * unfold Rdiv; rewrite Rpow_mult_distr, Rmult_assoc.
          replace ((/ b) ^ p * (b * b ^ p)) with (b).
          ring.
          rewrite <- Rmult_assoc, Rmult_comm.
          rewrite <- Rmult_assoc, <- Rpow_mult_distr.      
          rewrite Rinv_r, pow1; lra.
        * field; split; trivial.
          replace (a + b - a) with b by lra.
          now apply Rgt_not_eq.
      + rewrite <- Rmult_assoc, Rmult_comm.
        rewrite <- Rmult_assoc, <- Rpow_mult_distr.
        rewrite Rinv_r, pow1; lra.
    - field; now split.
  Qed.

  Lemma minkowski_range (a b : R) :
    (0 < a) -> (0 < b) -> 
    0 < a / (a + b) < 1.
    split.
    - apply Rdiv_lt_0_compat; trivial.
      now apply Rplus_lt_0_compat.
    - apply Rmult_lt_reg_r with (r := a+b).
      now apply Rplus_lt_0_compat.
      unfold Rdiv.
      rewrite Rmult_assoc, Rinv_l.
      + rewrite Rmult_1_r, Rmult_1_l.
        replace (a) with (a + 0) at 1 by lra.
        now apply Rplus_lt_compat_l.
      + apply Rgt_not_eq.
        now apply Rplus_lt_0_compat.
  Qed.

End ineqs.

Lemma Rpower_neg1 b e : b < 0 -> Rpower b e = 1.
Proof.
  intros.
  unfold Rpower.
  unfold ln.
  match_destr; try lra.
  - elimtype False; try tauto; lra.
  - rewrite Rmult_0_r.
    now rewrite exp_0.
Qed.

Lemma derivable_pt_lim_abs_power2' (x y : R) :
  0 <= x ->
  1 < y ->
  derivable_pt_lim (fun x0 : R => power (Rabs x0) y) x (y * power x (y - 1)).
Proof.
  intros.
  unfold power.
  match_destr.
  - red; intros.
    assert (x = 0) by lra.
    subst.

    assert (dpos:0 <  (power eps (Rinv (y-1)))).
    {
      apply power_pos; lra.
    } 
    exists (mkposreal _ dpos); intros.
    rewrite Rplus_0_l.
    match_destr.
    -- rewrite Rabs_R0.
       match_destr; try lra.
       unfold Rabs.
       match_destr; lra.
    -- simpl in *.
       rewrite Rmult_0_r.
       repeat rewrite Rminus_0_r.
       generalize (Rlt_power_l (Rabs h) (power eps (Rinv (y - 1))) (y-1))
       ; intros HH.
       cut_to HH.
    + rewrite power_mult in HH.
      rewrite Rinv_l in HH by lra.
      rewrite power_1 in HH by lra.
      unfold power in HH.
      match_destr_in HH; try lra.
      unfold Rminus in HH.
      rewrite Rpower_plus in HH.
      rewrite Rpower_Ropp in HH.
      rewrite Rpower_1 in HH
        by now apply Rabs_pos_lt.
      unfold Rdiv.
      rewrite Rabs_mult.
      rewrite Rabs_Rinv by trivial.
      rewrite Rabs_R0.
      match_destr; try lra.
      rewrite Rminus_0_r.
      rewrite (Rabs_pos_eq (Rpower (Rabs h) y)); trivial.
      left.
      apply Rpower_pos.
    + lra.
    + split; trivial.
      apply Rabs_pos.
  - assert ( 0 < x) by lra.
    generalize (derivable_pt_lim_comp
                  Rabs
                  (fun x0 : R => if Rle_dec x0 0 then 0 else Rpower x0 y)
                  x
                  1
                  (y * Rpower x (y - 1)))
    ; intros HH2.
    rewrite Rmult_1_r in HH2.
    apply HH2.
    + apply Rabs_derive_1; lra.
    + rewrite Rabs_pos_eq by lra.
      generalize (derivable_pt_lim_power' x y); intros HH.
      cut_to HH; [| lra].
      unfold power in HH.
      match_destr_in HH; try lra.
Qed.

Lemma Rpower_convex_pos (e:R) :
  1 <= e ->
  forall (x y a : R), 0<x -> 0<y -> convex (fun z => Rpower z e) a x y.
Proof.
  intros.
  eapply ppos_convex_deriv; trivial.
  - intros.
    now apply derivable_pt_lim_power.
  - intros.
    apply (ppos_deriv_incr_convex (fun z => Rpower z e)); trivial.
    + intros; now apply derivable_pt_lim_power.
    + intros.
      apply Rmult_le_compat_l; [lra |].
      apply Rle_Rpower_l; lra.
Qed.

Lemma Rpower_base_0 e : Rpower 0 e = 1.
Proof.
  unfold Rpower, ln.
  match_destr.
  - elimtype False; try tauto; lra.
  - rewrite Rmult_0_r.
    now rewrite exp_0.
Qed.

Lemma power_convex_pos (e:R) :
  1 <= e ->
  forall (x y a : R), 0<x -> 0<y -> convex (fun z => power z e) a x y.
Proof.
  intros.
  eapply ppos_convex_deriv; trivial.
  - intros.
    now apply derivable_pt_lim_power'.
  - intros.
    apply (ppos_deriv_incr_convex (fun z => power z e)); trivial.
    + intros; now apply derivable_pt_lim_power'.
    + intros.
      apply Rmult_le_compat_l; [lra |].
      apply Rle_power_l; lra.
Qed.

Section power_minkowski.

  Lemma power_minkowski_helper_aux (p:R) (a t : R) :
    0 <= a ->
    0 < t ->
    1 <= p ->
    t*(power (a/t) p) = (power a p)*(power (/t) (p-1)).
  Proof.
    intros.
    unfold Rdiv.
    rewrite <- power_mult_distr; trivial.
    - rewrite Rmult_comm, Rmult_assoc.
      f_equal.
      unfold Rminus.
      rewrite power_plus.
      f_equal.
      rewrite power_Ropp.
      + rewrite power_1.
        * rewrite Rinv_involutive; lra.
        * left.
          now apply Rinv_pos.
      + now apply Rinv_0_lt_compat.
    - left.
      now apply Rinv_pos.
  Qed.

  Lemma power_minkowski_helper_lt (p : R) {a b t : R}:
    (0 < a) ->
    (0 < b) ->
    0<t<1 ->
    1 <= p ->
    (power (a+b) p) <= (power (/t) (p-1))*(power a p) + (power (/(1-t)) (p-1))*(power b p).
  Proof.
    intros Ha Hb Ht pbig.
    assert (Ht1 : t <> 0) by (intro not; destruct Ht as [h1 h2] ; subst ; lra).
    assert (Ht2 : 1-t <> 0) by (intro not; destruct Ht as [h1 h2] ; subst ; lra).
    assert (Hat : 0 < a/t) by (apply Rcomplements.Rdiv_lt_0_compat ; lra).
    assert (Hbt : 0 < b/(1-t)) by  (apply Rcomplements.Rdiv_lt_0_compat ; lra).
    assert (Ht' : 0 <= t <= 1) by lra.
    replace (a+b) with (t*(a/t) + (1-t)*(b/(1-t))) by (field ; split ; trivial).
    
    generalize (power_convex_pos p pbig (a/t) (b/(1-t)) t Hat Hbt Ht'); intros.
    eapply Rle_trans. apply H.
    repeat (rewrite power_minkowski_helper_aux ; try lra).
  Qed.

  Lemma Rmult_bigpos_le_l a b :
    0 <= a ->
    1 <= b ->
    a <= b * a.
  Proof.
    intros.
    rewrite <- (Rmult_1_l a) at 1.
    now apply Rmult_le_compat_r.
  Qed.

  Lemma power_big_big a e :
    0 <= e ->
    1 <= a ->
    1 <= power a e.
  Proof.
    intros nne pbig.
    generalize (Rle_power a 0 e pbig nne).
    rewrite power_O; lra.
  Qed.
    
  Lemma power_minkowski_helper (p : R) {a b t : R}:
    (0 <= a) ->
    (0 <= b) ->
    0<t<1 ->
    1 <= p ->
    (power (a+b) p) <= (power (/t) (p-1))*(power a p) + (power (/(1-t)) (p-1))*(power b p).
  Proof.
    intros Ha Hb Ht pbig.
    destruct (Req_EM_T a 0).
    - subst.
      rewrite power0_Sbase by lra.
      rewrite Rmult_0_r.
      repeat rewrite Rplus_0_l.
      apply Rmult_bigpos_le_l.
      + apply power_nonneg.
      + assert (1 <= / (1 - t)).
        * rewrite <- Rinv_1 at 1.
          apply Rinv_le_contravar; lra.
        * apply power_big_big; lra.
    - destruct (Req_EM_T b 0).
      + subst.
        rewrite power0_Sbase by lra.
        rewrite Rmult_0_r.
        repeat rewrite Rplus_0_r.
        apply Rmult_bigpos_le_l.
      * apply power_nonneg.
      * assert (1 <= / t).
        -- rewrite <- Rinv_1 at 1.
          apply Rinv_le_contravar; lra.
        -- apply power_big_big; lra.
      + apply power_minkowski_helper_lt; trivial; lra.
  Qed.

  Lemma power_minus1 b e :
    0 <= b ->
    power b e = b * power b (e-1).
  Proof.
    intros.
    replace e with ((e-1)+1) at 1 by lra.
    rewrite power_plus.
    rewrite power_1; trivial.
    lra.
  Qed.

  Lemma power_minkowski_subst (p : R) {a b : R} :
    (0 < a) ->
    (0 < b) ->
    1 <= p ->
    (power (/(a / (a + b))) (p-1))*(power a p) +
    (power (/(1-(a / (a + b)))) (p-1))*(power b p) = (power (a + b) p).
  Proof.
    intros; simpl.
    assert (a <> 0) by auto with real. 
    assert (a + b <> 0) by lra. 
    replace (/ (a / (a + b))) with ((a+b)* (/a))
      by (field; now split).
    rewrite <- power_mult_distr, Rmult_assoc by (try lra; auto with real).
    replace (power (/ a) (p-1) * (power a p)) with (a).
    - replace (/ (1 - a / (a + b))) with ((a+b)/b).
      + unfold Rdiv; rewrite <- power_mult_distr, Rmult_assoc by (try lra; auto with real).
       replace (power (/ b) (p-1) * ( power b p)) with (b).
       * rewrite <- Rmult_plus_distr_l.
         rewrite Rmult_comm.
         rewrite <- power_minus1; trivial.
         lra.
       * rewrite (power_minus1 b) by lra.
         rewrite <-  Rmult_assoc, Rmult_comm, <- Rmult_assoc.
         rewrite power_mult_distr by (try lra; auto with real).
         rewrite Rinv_r by lra.
         rewrite power_base_1.
         lra.
      + rewrite <- (Rinv_r (a+b)) by lra.
        fold (Rdiv (a+b) (a+b)).
        field_simplify; try lra.
    - rewrite (power_minus1 a p) by auto with real.
      rewrite <- Rmult_assoc, Rmult_comm, <- Rmult_assoc.
      rewrite power_mult_distr by auto with real.
      rewrite Rinv_r, power_base_1 by lra.
      lra.
  Qed.
  
  Lemma power_ineq_convex p :
    1 <= p ->
    forall (x y : R), 0 < x -> 0 < y -> 
                 power (x + y) p <= (power 2 (p-1))*(power x p + power y p).
  Proof.
    intros pbig; intros.
    assert (0 <= (/2) <= 1) by lra.
    generalize (power_convex_pos p pbig x y _ H H0 H1); intros HH.
    replace (1 - /2) with (/2) in HH by lra.
    repeat rewrite <- Rmult_plus_distr_l in HH.
    rewrite <- power_mult_distr in HH by lra.
    apply Rmult_le_compat_l with (r := power 2 p) in HH
    ; [| apply power_nonneg].
    repeat rewrite <- Rmult_assoc in HH.
    replace (power 2 p * power (/2) p) with (1) in HH.
    + replace (power 2 p * (/2)) with (power 2 (p - 1)) in HH.
      * now repeat rewrite Rmult_1_l in HH.
      * replace (/2) with (power 2 ((Ropp 1))).
        -- now rewrite <- power_plus.
        -- rewrite power_Ropp by lra.
           rewrite power_1; lra.
    + rewrite power_mult_distr by lra.
      replace (2 * /2) with (1) by lra.
      now rewrite power_base_1.
  Qed.

  Lemma power_abs_ineq (p : R) (x y : R) :
    0 <= p ->
    power (Rabs (x + y)) p <= (power 2 p)*(power (Rabs x) p + power (Rabs y) p).
  Proof.
    intros pnneg.
    pose (m:=Rmax (Rabs x) (Rabs y)).

    assert (eqq:Rabs (x + y) <= 2*m).
    {
      unfold m.
      eapply Rle_trans; try eapply Rcomplements.Rplus_le_Rmax.
      apply Rabs_triang.
    }
    eapply Rle_trans
    ; try apply (Rle_power_l (Rabs (x + y)) (2 * m) p); trivial.
    - split; trivial.
      apply Rabs_pos.
    - rewrite <- power_mult_distr.
      + apply Rmult_le_compat_l.
        * apply power_nonneg.
        * unfold m, Rmax.
          generalize (power_nonneg (Rabs x) p); intros.
          generalize (power_nonneg (Rabs y) p); intros.
          match_destr; lra.
      + lra.
      + unfold m; eapply Rle_trans; [| eapply Rmax_l].
        apply Rabs_pos.
  Qed.

End power_minkowski.

Lemma Rbar_pos_finite (r : Rbar):
  0 < r -> is_finite r.
Proof.
  intros.
  destruct r.
  now unfold is_finite.
  simpl in H; lra.
  simpl in H; lra.
Qed.

Global Instance prod_f_R0_proper :
  Proper (pointwise_relation _ eq ==> eq ==> eq) prod_f_R0.
Proof.
  intros f1 f2 feqq N N' xeqq; subst N'.
  induction N; simpl; congruence.
Qed.
  
Lemma bounded_is_finite (a b : R) (x : Rbar) :
  Rbar_le a x -> Rbar_le x b -> is_finite x.
Proof.
  intros.
  unfold is_finite.
  destruct x.
  - now simpl.
  - simpl in H0.
    tauto.
  - simpl in H.
    tauto.
Qed.

Section lim_seq_sup_seq.
  
    Lemma le_incr0 (f : nat -> R) :
      (forall n, f n <= f (S n)) ->
      (forall n k, f n <= f (n + k)%nat).
    Proof.
      intros.
      induction k.
      - replace (n + 0)%nat with n by lia.
        lra.
      - eapply Rle_trans.
        apply IHk.
        replace (n + S k)%nat with (S (n + k)%nat) by lia.
        apply H.
     Qed.

    Lemma le_incr (f : nat -> R) :
      (forall n, f n <= f (S n)) ->
      (forall n m, (n<=m)%nat -> f n <= f m).
    Proof.
      intros.
      replace (m) with (n + (m-n))%nat by lia.
      now apply le_incr0.
    Qed.

    Lemma lim_seq_sup_seq_incr (f : nat -> R) (l : Rbar) :
      (forall n, f n <= f (S n)) ->
      is_lim_seq f l <-> is_sup_seq f l.
   Proof.
     intros.
     split; intros.
     apply is_lim_LimSup_seq in H0.
     destruct l.
     - unfold is_LimSup_seq in H0.
       unfold is_sup_seq.
       intros.
       specialize (H0 eps).
       destruct H0.
       simpl.
       split; intros.
       + destruct H1.
         destruct (le_dec x n).
         * now apply H1.
         * assert (n <= x)%nat by lia.
           apply Rle_lt_trans with (r2 := f x).
           now apply le_incr.
           apply H1; lia.
       + specialize (H0 0%nat).
         destruct H0 as [n [? ?]].
         exists n.
         apply H2.
     - unfold is_LimSup_seq in H0.
       unfold is_sup_seq; simpl; intros.
       specialize (H0 M 0%nat).
       destruct H0 as [n [? ?]].
       exists n.
       apply H1.
     - unfold is_LimSup_seq in H0.
       unfold is_sup_seq; simpl; intros.
       specialize (H0 M).
       destruct H0 as [N H0].
       destruct (le_dec N n).
       + now apply H0.
       + assert (n <= N)%nat by lia.
         apply Rle_lt_trans with (r2 := f N).
         * now apply le_incr.
         * apply H0; lia.
     - rewrite <- is_lim_seq_spec.
       destruct l.
       + unfold is_sup_seq in H0.
         unfold is_lim_seq'; intros.
         specialize (H0 eps).
         destruct H0 as [? [n ?]].
         simpl in H1; simpl in H0.
         exists n; intros.
         destruct (Rge_dec (f n0) r).
         * specialize (H0 n0).
           rewrite Rabs_right; lra.
         * assert (f n0 < r) by lra.
           rewrite Rabs_left; [|lra].
           generalize (le_incr f H n n0 H2); intros.
           lra.
       + unfold is_sup_seq in H0.
         unfold is_lim_seq'; intros.
         specialize (H0 M); simpl in H0.
         destruct H0 as [n ?].
         exists n; intros.
         apply Rlt_le_trans with (r2 := f n); trivial.
         now apply le_incr.
       + unfold is_sup_seq in H0.
         unfold is_lim_seq'; intros.
         specialize (H0 M); simpl in H0.
         exists (0%nat); intros.
         apply H0.
    Qed.

   Lemma is_lub_sup_seq (u : nat -> R) (l : Rbar) :
     is_lub_Rbar (fun x => exists n, x = u n) l ->
     is_sup_seq u l.
   Proof.
     intros.
     apply Rbar_is_lub_sup_seq.
     unfold is_lub_Rbar in H.
     unfold Rbar_is_lub.
     destruct H.
     split.
     - unfold Rbar_is_upper_bound.
       unfold is_ub_Rbar in H.
       intros.
       destruct x.
       + apply H.
         destruct H1.
         exists x.
         now rewrite Rbar_finite_eq in H1.
       + destruct H1.
         discriminate.
       + destruct H1.
         discriminate.
     - intros.
       apply H0.
       unfold is_ub_Rbar.
       intros.
       apply H1.
       destruct H2.
       exists x0.
       rewrite H2.
       reflexivity.
   Qed.

   Lemma is_sub_seq_lub_R (u : nat -> R) (l : Rbar) :
     is_sup_seq u l -> is_lub_Rbar (fun x => exists n, x = u n) l.
   Proof.
     intros.
     apply is_sup_seq_lub in H.
     unfold Rbar_is_lub in H.
     unfold is_lub_Rbar.
     destruct H.
     split.
     - unfold Rbar_is_upper_bound in H.
       unfold is_ub_Rbar.
       intros.
       apply H.
       destruct H1.
       exists x0.
       rewrite H1.
       reflexivity.
     - intros.
       apply H0.
       unfold Rbar_is_upper_bound.
       unfold is_ub_Rbar in H1.
       intros.
       destruct x.
       + apply H1.
         destruct H2.
         exists x.
         now rewrite Rbar_finite_eq in H2.
       + destruct H2.
         discriminate.
       + destruct H2.
         discriminate.
   Qed.

    Lemma lim_seq_is_lub_incr (f : nat -> R) (l : Rbar) :
      (forall n, f n <= f (S n)) ->
      (is_lim_seq f l) <-> (is_lub_Rbar (fun x => exists n, x = f n) l).
    Proof.
      intros.
      rewrite lim_seq_sup_seq_incr; trivial.
      split; intros.
      now apply is_sub_seq_lub_R.
      now apply is_lub_sup_seq.
    Qed.

End lim_seq_sup_seq.

Section Rmax_list.

  (*
   Definition and properties about the maximum element of a list of real numbers.
   Dump this into RealAdd.
   *)

Open Scope list_scope.
Open Scope R_scope.

Import ListNotations.

Fixpoint Rmax_list (l : list R) : R :=
  match l with
  | nil => 0
  | a :: nil => a
  | a :: l1 => Rmax a (Rmax_list l1)
  end.


Lemma Rmax_spec_map {A} (l : list A) (f : A -> R) : forall a:A, In a l -> f a <= Rmax_list (List.map f l).
Proof.
  intros a Ha.
  induction l.
  - simpl ; firstorder.
  - simpl in *. intuition.
    + rewrite H. destruct l. simpl. right; reflexivity.
      simpl. apply Rmax_l.
    + destruct l. simpl in *; firstorder.
      simpl in *. eapply Rle_trans ; eauto. apply Rmax_r.
Qed.

Lemma Rmax_spec {l : list R} : forall a:R, In a l -> a <= Rmax_list l.
Proof.
  intros a Ha.
  induction l.
  - simpl ; firstorder.
  - simpl in *. intuition.
    + rewrite H. destruct l. simpl. right; reflexivity.
      simpl. apply Rmax_l.
    + destruct l. simpl in *; firstorder.
      simpl in *. eapply Rle_trans ; eauto. apply Rmax_r.
Qed.

Lemma Rmax_list_map_const_mul {A} (l : list A) (f : A -> R) {r : R} (hr : 0 <= r) :
  Rmax_list (List.map (fun a => r*f(a)) l) = r*(Rmax_list (List.map f l)).
Proof.
  induction l.
  - simpl ; lra.
  - simpl. rewrite IHl.
    rewrite RmaxRmult ; trivial.
    destruct l.
    + simpl ; reflexivity.
    + simpl in *. f_equal ; trivial.
Qed.

Lemma Rmax_list_const_add (l : list R) (d : R) :
  Rmax_list (List.map (fun x => x + d) l) =
  if (l <> []) then ((Rmax_list l) + d) else 0.
Proof.
  induction l.
  - simpl ; reflexivity.
  - simpl in *.
    destruct l.
    + simpl ; reflexivity.
    + simpl in * ; rewrite IHl.
      now rewrite Rcomplements.Rplus_max_distr_r.
Qed.

Lemma Rmax_list_zero {A} (l : list A) :
  Rmax_list (List.map (fun x => 0) l) = 0.
Proof.
  induction l.
  -- simpl ; reflexivity.
  -- simpl in *. rewrite IHl.
     replace (Rmax 0 0) with 0.
     destruct l ; [simpl ; reflexivity | simpl ; reflexivity] .
     symmetry. apply Rmax_left ; lra.
Qed.


Lemma Rmax_list_ge (l : list R) (r : R) :
  forall x, In x l -> r <= x -> r <= Rmax_list l.
Proof.
  intros x Hx Hrx.
  eapply Rle_trans ; eauto.
  now apply Rmax_spec.
Qed.

Lemma Rmax_list_le (l : list R) (r : R) :
  Rmax_list l <= r -> forall x, In x l -> x <= r.
Proof.
  intros H x Hx.
  set (Rmax_spec x Hx).
  eapply Rle_trans; eauto.
Qed.


Lemma Rmax_list_In (l : list R):
  ([] <> l) -> In (Rmax_list l) l.
Proof.
  induction l.
  - simpl ; firstorder.
  - intros H. simpl in *.
    destruct l.
    -- now left.
    -- assert ([] <> r :: l)  by apply nil_cons.
       specialize (IHl H0) ; clear H0.
       destruct (Rle_dec a (Rmax_list (r :: l))).
       ++ rewrite Rmax_right. now right ; assumption. assumption.
       ++ rewrite Rmax_left. now left.
          left ; apply ROrder.not_ge_lt ; assumption.
Qed.

Lemma Rmax_list_lub (l : list R) (r : R):
  ([] <> l) -> (forall x, In x l -> x <= r) -> Rmax_list l <= r.
Proof.
  intros Hl H.
  apply H. eapply Rmax_list_In ; auto.
Qed.

Lemma Rmax_list_le_iff {l : list R} (hl : [] <> l) (r : R):
  Rmax_list l <= r <-> (forall x, In x l -> x <= r)  .
Proof.
  split.
  apply Rmax_list_le.
  apply Rmax_list_lub ; auto.
Qed.

Lemma Rmax_list_lt_iff {l : list R} (hl : [] <> l) (r : R):
  Rmax_list l < r <-> (forall x, In x l -> x < r)  .
Proof.
  split.
  -- intros Hr x Hx.
     eapply Rle_lt_trans. eapply Rmax_spec ; eauto. assumption.
  -- intro H. apply H ; auto. now apply Rmax_list_In.
Qed.

Definition Rmax_list_incl l1 l2 : nil <> l1 -> incl l1 l2 -> Rmax_list l1 <= Rmax_list l2.
Proof.
  unfold Proper, respectful, incl
  ; intros.
  apply Rmax_list_le_iff; trivial.
  intros.
  apply Rmax_spec; auto.
Qed.

Global Instance Rmax_list_equivlist : Proper (equivlist ==> eq) Rmax_list.
Proof.
  unfold Proper, respectful; intros x y equivs.
  destruct x.
  - symmetry in equivs.
    apply equivlist_nil in equivs.
    subst; simpl; trivial.
  - destruct y.
    + apply equivlist_nil in equivs.
      discriminate.
    + apply equivlist_incls in equivs.
      destruct equivs.
      generalize (Rmax_list_incl (r::x) (r0::y)); intros HH1.
      generalize (Rmax_list_incl (r0::y) (r::x)); intros HH2.
      cut_to HH1; trivial; try discriminate.
      cut_to HH2; trivial; try discriminate.
      lra.
Qed.

Lemma Rmax_list_sum {A B} {la : list A} (lb : list B) (f : A -> B -> R) (Hla : [] <> la):
  Rmax_list (List.map (fun a => list_sum (List.map (f a) lb)) la) <=
  list_sum (List.map (fun b => Rmax_list (List.map (fun a => f a b) la)) lb).
Proof.
  rewrite Rmax_list_le_iff.
  * intro x. rewrite in_map_iff.
    intros [x0 [Hlsx Hin]].
    rewrite <-Hlsx. apply list_sum_le.
    intro b. apply (Rmax_spec_map la (fun a => f a b) x0 Hin).
  * now rewrite map_not_nil.
Qed.


Lemma Rmax_list_cons_cons (l : list R) (a b : R) :
  Rmax_list (a :: b :: l) = Rmax a (Rmax_list (b :: l)).
Proof.
  constructor.
Qed.

Lemma Rmax_list_Rmax_swap (l : list R) (a b : R) :
  Rmax a (Rmax_list (b :: l)) = Rmax b (Rmax_list (a :: l)).
Proof.
  induction l.
  - simpl ; apply Rmax_comm.
  - do 2 rewrite Rmax_list_cons_cons.
    do 2 rewrite Rmax_assoc.
    now rewrite (Rmax_comm _ b).
Qed.

Lemma Rmax_list_cons (x0 : R)  (l1 l2 : list R) :
  Permutation l1 l2 -> (Rmax_list l1 = Rmax_list l2) -> Rmax_list (x0 :: l1) = Rmax_list(x0 :: l2).
Proof.
  intros Hpl Hrl.
  case_eq l1.
  * intro Hl. rewrite Hl in Hpl. set (Permutation_nil Hpl).
    now rewrite e.
  * case_eq l2.
    ++ intro Hl2. rewrite Hl2 in Hpl. symmetry in Hpl. set (Permutation_nil Hpl).
       now rewrite e.
    ++ intros r l H r0 l0 H0.
       rewrite <-H0, <-H. simpl ; rewrite Hrl.
       now rewrite H0, H.
Qed.

Lemma Rmax_list_cons_swap (x0 y0 : R)  (l1 l2 : list R) :
  Permutation l1 l2 -> (Rmax_list l1 = Rmax_list l2) ->
  Rmax_list (x0 :: y0 :: l1) = Rmax_list(y0 :: x0 :: l2).
Proof.
  intros Hpl Hrl.
  rewrite Rmax_list_cons_cons. rewrite Rmax_list_Rmax_swap.
  rewrite <-Rmax_list_cons_cons.
  case_eq l1.
  * intro Hl. rewrite Hl in Hpl. set (Permutation_nil Hpl).
    now rewrite e.
  * case_eq l2.
    ++ intro Hl2. rewrite Hl2 in Hpl. symmetry in Hpl. set (Permutation_nil Hpl).
       now rewrite e.
    ++ intros r l H r0 l0 H0.  rewrite <-H0, <-H. simpl ; rewrite Hrl.
       now rewrite H0, H.
Qed.

Global Instance Rmax_list_Proper : Proper (@Permutation R ++> eq) Rmax_list.
Proof.
  unfold Proper. intros x y H.
  apply (@Permutation_ind_bis R (fun a b => Rmax_list a = Rmax_list b)).
  - simpl ; lra.
  - intros x0. apply Rmax_list_cons.
  - intros x0 y0 l l' H0 H1. apply Rmax_list_cons_swap ; trivial.
  - intros l l' l'' H0 H1 H2 H3. rewrite H1. rewrite <-H3. reflexivity.
  - assumption.
Qed.

Definition Rmax_list_map {A} (l : list A) (f : A -> R) := Rmax_list (List.map f l).

Declare Scope rmax_scope.
Notation "Max_{ l } ( f )" := (Rmax_list (List.map f l)) (at level 50) : rmax_scope.

Open Scope rmax_scope.
Delimit Scope rmax_scope with rmax.

(* This is very important. *)
Lemma Rmax_list_map_exist {A} (f : A -> R) (l : list A) :
  [] <> l -> exists a:A, In a l /\ f a = Max_{l}(f).
Proof.
  intro Hne.
  set (Hmap := Rmax_list_In (List.map f l)).
  rewrite <-(map_not_nil l f) in Hne.
  specialize (Hmap Hne).
  rewrite in_map_iff in Hmap.
  destruct Hmap as  [a [Hfa Hin]].
  now exists a.
Qed.

Lemma exists_in_strengthen_dec {A} (P:A->Prop) l (dec:forall x, {P x} + {~ P x})
      (ex:exists x, In x l /\ P x) : {x | In x l /\ P x}.
Proof.
  induction l; simpl.
  - elimtype False.
    destruct ex ; intuition.
  - destruct (dec a).
    + exists a ; eauto.
    + destruct IHl as [x [inx px]].
      * destruct ex as [x [inx px]].
        destruct inx.
        -- congruence.
        -- eauto.
      * eauto.
Qed.

(* This is very important too. *)
Lemma Rmax_list_map_exist_sig {A} (f : A -> R) {l : list A} :
  [] <> l -> { a:A | In a l /\ f a = Max_{l}(f)}.
Proof.
  intro Hne.
  apply exists_in_strengthen_dec.
  - intro x. apply Req_EM_T.
  - now apply Rmax_list_map_exist.
Qed.

Definition argmax {A} {l : list A} (hl : [] <> l)(f : A -> R) : A :=
  proj1_sig (Rmax_list_map_exist_sig f hl).

Lemma argmax_is_max {A} {l : list A} (hl : [] <> l) (f : A->R) :
  f (argmax hl f) = Max_{l}(f).
Proof.
  unfold argmax.
  destruct (Rmax_list_map_exist_sig f hl).
  simpl. now destruct a.
Qed.

Lemma argmax_in_list {A} {l : list A} (hl : [] <> l) (f : A -> R):
  In (argmax hl f) l.
Proof.
  unfold argmax.
  destruct (Rmax_list_map_exist_sig f hl).
  simpl. now destruct a.
Qed.

Global Instance Rmax_eq_Proper {A} {l : list A} (hl : [] <> l) :
  Proper (pointwise_relation _ eq ++> eq) (@Rmax_list_map A l).
Proof.
  unfold Proper, respectful, pointwise_relation.
  intros f g H.
  unfold Rmax_list_map.
  induction l.
  -- simpl. reflexivity.
  -- simpl. destruct l.
     ++ simpl. apply H.
     ++ simpl. rewrite H. simpl in IHl. rewrite IHl. reflexivity.
        apply nil_cons.
Qed.

Lemma Rmax_list_prod_le {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  Max_{la}(fun a => Max_{lb} (fun b => f a b)) =
  Max_{list_prod la lb} (fun ab => f (fst ab) (snd ab)).
Proof.
  apply Rle_antisym.
  ++  rewrite Rmax_list_le_iff.
      -- intros x Hx. eapply (@Rmax_list_ge _ _ x).
         ** rewrite in_map_iff in *.
            destruct Hx as [a [Hx' HInx']].
            set (Hmax := Rmax_list_map_exist (fun b => f a b) lb).
            specialize (Hmax Hlb).
            destruct Hmax as [b Hb].
            exists (a,b). simpl. split; [now rewrite <-Hx' |].
            apply in_prod ; trivial; intuition.
         ** now right.
      -- now rewrite map_not_nil.
  ++ rewrite Rmax_list_le_iff.
     * intros x Hx.
       rewrite in_map_iff in Hx.
       destruct Hx as [ab [Hab HInab]].
       eapply (@Rmax_list_ge _ _ (Rmax_list (List.map (fun b : B => f (fst ab) b) lb))).
       --- rewrite in_map_iff.
           exists (fst ab). split ; trivial.
           setoid_rewrite surjective_pairing in HInab.
           rewrite in_prod_iff in HInab. destruct HInab ; trivial.
       --- eapply (Rmax_list_ge _ _ (f (fst ab) (snd ab))).
           +++ rewrite in_map_iff. exists (snd ab). split ; trivial.
               setoid_rewrite surjective_pairing in HInab.
               rewrite in_prod_iff in HInab. destruct HInab ; trivial.
           +++ rewrite <-Hab. right ; trivial.
     * rewrite map_not_nil. now apply list_prod_not_nil.
Qed.

(* There has to be a better way of doing this... *)
Lemma Rmax_list_prod_le' {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
   Max_{lb}(fun b => Max_{la} (fun a => f a b))  =
   Max_{list_prod la lb} (fun ab => f (fst ab) (snd ab)).
Proof.
  apply Rle_antisym.
  ++  rewrite Rmax_list_le_iff.
      -- intros x Hx. eapply (@Rmax_list_ge _ _ x).
         ** rewrite in_map_iff in *.
            destruct Hx as [b [Hx' HInx']].
            set (Hmax := Rmax_list_map_exist (fun a => f a b) la).
            specialize (Hmax Hla).
            destruct Hmax as [a Ha].
            exists (a,b). simpl. split; [now rewrite <-Hx' |].
            apply in_prod ; trivial; intuition.
         ** now right.
      -- now rewrite map_not_nil.
  ++ rewrite Rmax_list_le_iff.
     * intros x Hx.
       rewrite in_map_iff in Hx.
       destruct Hx as [ab [Hab HInab]].
       eapply (@Rmax_list_ge _ _ (Rmax_list (List.map (fun a : A  => f a (snd ab)) la))).
       --- rewrite in_map_iff.
           exists (snd ab). split ; trivial.
           setoid_rewrite surjective_pairing in HInab.
           rewrite in_prod_iff in HInab. destruct HInab ; trivial.
       --- eapply (Rmax_list_ge _ _ (f (fst ab) (snd ab))).
           +++ rewrite in_map_iff. exists (fst ab). split ; trivial.
               setoid_rewrite surjective_pairing in HInab.
               rewrite in_prod_iff in HInab. destruct HInab ; trivial.
           +++ rewrite <-Hab. right ; trivial.
     * rewrite map_not_nil. now apply list_prod_not_nil.
Qed.

Lemma Rmax_list_map_comm {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  Max_{la}(fun a => Max_{lb} (fun b => f a b)) = Max_{lb}(fun b => Max_{la} (fun a => f a b)) .
Proof.
  etransitivity; [|symmetry].
  - apply Rmax_list_prod_le ; trivial.
  - apply Rmax_list_prod_le'; trivial.
Qed.

Lemma Rmax_list_prod_combine {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  equivlist (list_prod la lb) (combine la lb) ->
  Max_{la}(fun a => Max_{lb} (fun b => f a b))  =
  Max_{combine la lb} (fun ab => f (fst ab) (snd ab)).
Proof.
  intros. rewrite <- H.
  now apply Rmax_list_prod_le.
Qed.


Lemma Rmax_list_minus_le {A} {B : A -> Type} (f g : forall a, B a -> R) (la : forall a, list (B a)):
 forall a:A, (Max_{la a}(f a) - Max_{la a}(g a)) <= Max_{la a}(fun x => f a x - g a x).
Proof.
  intro a0.
  destruct (is_nil_dec (la a0)).
  - setoid_rewrite e. simpl. lra.
  - rewrite Rcomplements.Rle_minus_l.
    rewrite Rmax_list_le_iff. intros x Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
    replace (f a0 a) with ((f a0 a - g a0 a) + g a0 a) by ring.
    apply Rplus_le_compat.
    -- apply Rmax_spec. rewrite in_map_iff.
       exists a ; split ; trivial.
    -- apply Rmax_spec. rewrite in_map_iff.
       exists a ; split ; trivial.
    -- rewrite map_not_nil. congruence.
Qed.

Lemma Rmax_list_map_triangle {A} (f g : A -> R) (l : list A):
  Max_{ l}(fun a : A => Rabs (f a + g a)) <=
  Max_{ l}(fun a : A => Rabs (f a)) + (Max_{ l}(fun a : A => Rabs (g a))).
Proof.
   destruct (is_nil_dec l).
  - subst; simpl. lra.
  - rewrite Rmax_list_le_iff.
    intros x Hx. rewrite in_map_iff in Hx.
    destruct Hx as [a [Ha Hina]].
    rewrite <-Ha.
    eapply Rle_trans; try apply Rabs_triang.
    apply Rplus_le_compat; try (apply Rmax_spec; rewrite in_map_iff; exists a; split ; trivial).
    rewrite map_not_nil.
    congruence.
Qed.

Lemma Rmax_list_minus_le_abs {A} (f g : A -> R) (la : list A):
  Rabs (Max_{la}(f) - Max_{la}(g)) <= Max_{la}(fun a => Rabs(f a - g a)).
Proof.
   destruct (is_nil_dec la).
  - subst; simpl. replace (0-0) with 0 by ring. right. now apply Rabs_R0.
  - rewrite Rcomplements.Rabs_le_between'.
    split.
    -- rewrite Rcomplements.Rle_minus_l.
       rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (g a) with (f a + (g a - f a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
    -- rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (f a) with (g a + (f a - g a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial. apply Rabs_minus_sym.
Qed.


Lemma Rmax_list_minus_le_abs' {A} {B : A -> Type} (f g : forall a, B a -> R) (la : forall a, list (B a)):
 forall a:A, Rabs (Max_{la a}(f a) - Max_{la a}(g a)) <= Max_{la a}(fun x => Rabs(f a x - g a x)).
Proof.
  intro a0.
  destruct (is_nil_dec (la a0)).
  - setoid_rewrite e. simpl. replace (0-0) with 0 by ring. right. now apply Rabs_R0.
  - rewrite Rcomplements.Rabs_le_between'.
    split.
    -- rewrite Rcomplements.Rle_minus_l.
       rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (g a0 a) with (f a0 a + (g a0 a - f a0 a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
    -- rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (f a0 a) with (g a0 a + (f a0 a - g a0 a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial. apply Rabs_minus_sym.
Qed.


(* max_{x:A} (max_{f:A->B}(g (f a) f)) = max_{f:A->B} (max_{a:map f A} (g (a,f))) *)

Lemma Rmax_list_fun_swap {A B} {lf : list(A -> B)}{la : list A}
      (g :B -> (A -> B) -> R)
      (hl : [] <> lf) (hla : [] <> la)  :
      Max_{la} (fun s => Max_{lf} (fun f => g (f s) f))  =
      Max_{lf} (fun f => Max_{List.map f la} (fun b => g b f)).
Proof.
  rewrite Rmax_list_map_comm; trivial.
  f_equal. apply map_ext.
  intros a.
  now rewrite map_map.
Qed.

Lemma Rmax_list_le_range {A B} (f : A -> B) (g : B -> R) {la : list A} {lb : list B}
      (hla : [] <> la)
      (hf : forall {a}, In a la -> In (f a) lb) :
  Max_{la} (fun a => g(f a)) <= Max_{lb} (fun b => g b).
Proof.
  rewrite Rmax_list_le_iff.
  intros x Hx.
  rewrite in_map_iff in Hx.
  -- destruct Hx as [a [Ha Hina]].
     eapply Rmax_list_ge.
     rewrite in_map_iff. exists (f a). split;eauto.
     now right.
  -- now rewrite map_not_nil.
Qed.

Lemma Rmax_list_le_range' {A B} (g : B -> R) lf {lb : list B}
      (hlf : [] <> lf){a : A}
      (hfa : forall f, In (f a) lb)  :
  Max_{lf} (fun f => g(f a)) <= Max_{lb} (fun b => g b).
Proof.
  destruct (Rmax_list_map_exist (fun f => g (f a)) lf hlf) as [f [Hf Hinf]].
  rewrite <-Hinf.
  eapply Rmax_spec_map. apply hfa.
Qed.

Lemma Rmax_list_fun_le {A} {la : list A}
      (f : A -> R) (g : A -> R) :
      (forall a, f a <= g a) ->
      Max_{la} (fun a => f a) <= Max_{la} (fun a => g a).
Proof.
  intros Hfg.
  destruct (is_nil_dec la) ; [subst ; simpl ; lra|].
  assert (n' : [] <> la) by congruence.
  destruct (Rmax_list_map_exist (fun a => g a) la n') as [a1 [Ha1 Hina1]].
  destruct (Rmax_list_map_exist (fun a => f a) la n') as [a2 [Ha2 Hina2]].
  rewrite <-Hina1.
  rewrite Rmax_list_le_iff.
  intros x Hx. rewrite in_map_iff in Hx.
  destruct Hx as [a0 [ha0 hina0]]. rewrite <-ha0.
  enough (f a0 <= f a2).
  assert (f a2 <= g a2) by (apply Hfg).
  enough (g a2 <= g a1).
  lra.
  rewrite Hina1. apply Rmax_spec. rewrite in_map_iff. exists a2 ; split ; trivial.
  rewrite Hina2. apply Rmax_spec. rewrite in_map_iff. exists a0 ; split ; trivial.
  now rewrite map_not_nil.
Qed.

Lemma Rmax_list_map_nonneg {A} {la : list A}
      (f : A -> R):
      (forall a, 0 <= f a) ->
      0 <= Max_{la}(fun a => f a).
Proof.
  intros Hf.
  rewrite <-(Rmax_list_zero la).
  now apply Rmax_list_fun_le.
Qed.

Lemma Rmax_list_map_transf {A B} (l : list A) (f : A -> R) (f' : B -> R) (g : A -> B) :
 (List.Forall (fun x => f x = f'(g x)) l) -> Max_{l}(f) = Max_{List.map g l}(f').
Proof.
  intros H.
  rewrite Forall_forall in H.
  rewrite map_map. f_equal.
  apply List.map_ext_in.
  assumption.
Qed.

Lemma fin_fun_bounded {A} (finA : Finite A) (f : A -> R) : {D | forall a, f a <= D}.
Proof.
  exists (Max_{@elms _ finA}(f)).
  intro a.
  apply Rmax_spec.
  rewrite in_map_iff.
  exists a ; split ; trivial.
  destruct finA ; eauto.
Qed.

Lemma fin_fun_bounded_Rabs {A} (finA : Finite A) (f : A -> R) : { D | forall a, Rabs(f a) <= D }.
Proof.
  exists (Max_{@elms _ finA}(fun x => Rabs (f x))).
  intros a.
  apply Rmax_spec.
  rewrite in_map_iff.
  exists a.
  split; trivial.
  apply finite.
Qed.

End Rmax_list.

Lemma seq_iota_seq m n : seq.iota m n = seq m n.
Proof.
  revert m.
  induction n; intros m; simpl; trivial.
Qed.

Lemma sum_n_m_fold_right_seq (f:nat->R) n m:
  sum_n_m (fun n0 : nat => f n0) m n =
  fold_right Rplus 0 (map f (List.seq m (S n - m))).
Proof.
  unfold sum_n_m, Iter.iter_nat.
  rewrite seq_iota_seq.
  generalize (S n - m)%nat; intros nn.
  clear n.
  revert m.
  induction nn; unfold plus; simpl; trivial; intros m.
  now rewrite IHnn.
Qed.

Lemma sum_n_fold_right_seq (f:nat->R) n :
  sum_n (fun n0 : nat => f n0) n =
  fold_right Rplus 0 (map f (seq 0 (S n))).
Proof.
  unfold sum_n.
  now rewrite sum_n_m_fold_right_seq.
Qed.

Lemma list_sum_sum_n (l:list R) :
  list_sum l =
  @Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun i:nat => match nth_error l i with
                                                     | Some x => x
                                                     | None => 0%R
                                                     end) (length l).
Proof.
  rewrite sum_n_fold_right_seq.
  rewrite  list_sum_fold_right.
  induction l; simpl; try lra.
  f_equal.
  rewrite IHl.
  destruct l; simpl; try lra.
  f_equal.
  f_equal.
  rewrite <- (@seq_shift _ 2).
  rewrite map_map.
  apply fold_right_ext; trivial.
Qed.


Lemma sum_n_m_shift (α : nat -> R) (k n0 : nat) :
  sum_n_m α k (n0 + k)%nat = sum_n (fun n1 : nat => α (n1 + k)%nat) n0.
Proof.
  unfold sum_n.
  induction n0.
  - replace (0 + k)%nat with (k) by lia.
    do 2 rewrite sum_n_n.
    f_equal; lia.
  - replace (S n0 + k)%nat with (S (n0 + k)%nat) by lia.
    rewrite sum_n_Sm; try lia.
    rewrite sum_n_Sm; try lia.
    replace (S n0 + k)%nat with (S (n0 + k)%nat) by lia.
    now rewrite IHn0.
Qed.

Lemma sum_n_m_pos a n1 n2 :
  (forall n, (n1 <= n <= n2)%nat -> 0 <= a n) ->
  0 <= (sum_n_m a n1 n2).
Proof.
  intros.
  rewrite sum_n_m_fold_right_seq.
  cut (forall x, List.In x ((List.seq n1 (S n2 - n1))) -> 0 <= a x).
  - generalize ( (List.seq n1 (S n2 - n1))); intros l.
    induction l; simpl; intros.
    + lra.
    + apply Rplus_le_le_0_compat; auto.
  - intros ? inn.
    apply List.in_seq in inn.
    apply H.
    lia.
Qed.

                                   
Lemma sum_n_pos_incr a n1 n2 : (forall n, (n1 < n <= n2)%nat -> 0 <= a n) -> 
                               (n1 <= n2)%nat -> sum_n a n1 <= sum_n a n2.
Proof.
  intros.
  destruct (Nat.eq_dec n1 n2); [rewrite e; lra|].
  assert (n1 < n2)%nat by lia.
  unfold sum_n.
  rewrite sum_n_m_Chasles with (k:=n2) (m:=n1); try lia.
  replace (sum_n_m a 0 n1) with ((sum_n_m a 0 n1) + 0) at 1 by lra.
  unfold plus; simpl.
  apply Rplus_le_compat_l.
  apply sum_n_m_pos; intros.
  apply H.
  lia.
Qed.

Lemma Rmult_lt_1 (a b :R) :
  0 <= a <= 1 ->
  b < 1 ->
  a*b < 1.
Proof.
  intros.
  destruct H.
  destruct (Rlt_dec 0 a).
  - apply Rmult_lt_compat_l with (r := a) in H0; trivial.
    rewrite Rmult_1_r in H0.
    now generalize (Rlt_le_trans _ _ _ H0 H1).
  - assert (a = 0) by lra.
    subst.
    lra.
Qed.

Lemma Rmult_le_1 (a b :R) :
  0 <= a <= 1 ->
  0 <= b <= 1 ->
  0 <= a*b <= 1.
Proof.
  intros.
  split.
  now apply Rmult_le_pos.
  replace (1) with (1 * 1) by lra.
  now apply Rmult_le_compat.
Qed.

Lemma Rplus_minus_cancel1 : forall a b, a + b - a = b.
Proof. intros; ring. Qed.

Lemma Rplus_le_pos_l (f g : R) :
  0 <= g ->
  f <= f + g.
Proof.
  intros.
  rewrite <- Rplus_0_r at 1.
  now apply Rplus_le_compat_l.
Qed.

Lemma Rsqrt_ext x y : nonneg x = nonneg y -> Rsqrt x = Rsqrt y.
Proof.
  intros.
  destruct x; destruct y; simpl in *.
  subst.
  unfold Rsqrt.
  repeat match_destr.
  simpl in *.
  destruct a as [??].
  destruct a0 as [??].
  subst.
  apply Rsqr_eq_abs_0 in H2.
  now repeat rewrite Rabs_pos_eq in H2 by trivial.
Qed.

Lemma Rabs_sqr (x : R) : x² = Rabs (x²).
Proof.
  rewrite Rabs_pos_eq; trivial.
  apply Rle_0_sqr.
Qed.

Lemma fold_left_Rmax_init_le l d :
  d <= fold_left Rmax l d.
Proof.
  revert d.
  induction l; simpl; intros.
  - lra.
  - specialize (IHl (Rmax d a)).
    eapply Rle_trans; try eapply IHl.
    apply Rmax_l.
Qed.

Lemma fold_left_Rmax_le l d x :
  In x l ->
  x <= fold_left Rmax l d.
Proof.
  revert d.
  induction l; simpl.
  - tauto.
  - intros.
    destruct H.
    + subst.
      eapply Rle_trans
      ; try eapply (fold_left_Rmax_init_le l (Rmax d x)).
      apply Rmax_r.
    + now eapply IHl.
Qed.

Lemma fold_left_lub l d r:
  (forall x, In x l -> x <= r) ->
  d <= r ->
  fold_left Rmax l d <= r.
Proof.
  revert d.
  induction l; simpl.
  - tauto.
  - intros.
    apply IHl.
    + eauto.
    + apply Rmax_lub; eauto.
Qed.

Lemma Rsqrt_le_to_Rsqr: forall r x : nonnegreal, x <= r² <-> Rsqrt x <= r.
Proof.
  intros.
  unfold Rsqrt.
  match_destr.
  destruct a as [? eqq].
  rewrite eqq.
  split; intros HH.
  - apply Rsqr_le_abs_0 in HH.
    destruct r; destruct x; simpl in *.
    now repeat (rewrite Rabs_pos_eq in HH by lra).
  - apply Rsqr_le_abs_1.
    destruct r; destruct x; simpl in *.
    now repeat (rewrite Rabs_pos_eq by lra).
Qed.

Lemma Rsqrt_lt_to_Rsqr: forall r x : nonnegreal, x < r² <-> Rsqrt x < r.
Proof.
  intros.
  unfold Rsqrt.
  match_destr.
  destruct a as [? eqq].
  rewrite eqq.
  split; intros HH.
  - apply Rsqr_lt_abs_0 in HH.
    destruct r; destruct x; simpl in *.
    now repeat (rewrite Rabs_pos_eq in HH by lra).
  - apply Rsqr_lt_abs_1.
    destruct r; destruct x; simpl in *.
    now repeat (rewrite Rabs_pos_eq by lra).
Qed.

Lemma Rbar_mult_1_r (x:Rbar) : Rbar_mult x 1 = x.
Proof.  
  destruct x; simpl.
  + rewrite Rbar_finite_eq; lra.
  + destruct (Rle_dec 0 1); [|lra].
    destruct (Rle_lt_or_eq_dec 0 1 r); intuition.
  + destruct (Rle_dec 0 1); [|lra].
    destruct (Rle_lt_or_eq_dec 0 1 r); intuition.
Qed.

Lemma Rbar_mult_1_l (x:Rbar) : Rbar_mult 1 x = x.
Proof.
  rewrite Rbar_mult_comm.
  apply Rbar_mult_1_r.
Qed.

  Lemma Rbar_mult_mult_pos (c : posreal) (l : Rbar) :
    Rbar_mult_pos l c = Rbar_mult l c.
  Proof.
    assert (0 < c) as cpos by apply cond_pos.
    unfold Rbar_mult_pos.
    unfold Rbar_mult, Rbar_mult'.
    destruct l.
    - trivial.
    - match_case; intros; match_case_in H; intros; try lra; rewrite H0 in H; 
        match_case_in H; intros; try lra; rewrite H1 in H; [now invcs H| congruence].
    - match_case; intros; match_case_in H; intros; try lra; rewrite H0 in H; 
        match_case_in H; intros; try lra; rewrite H1 in H; [now invcs H| congruence].
  Qed.

  Lemma Rbar_div_mult_pos (c : posreal) (l : Rbar) :
    Rbar_mult_pos (Rbar_div l c) c = l.
  Proof.
    assert (c > 0) as cpos by apply cond_pos.
    assert ((pos c) <> 0) as cneq0 by lra.
    assert (/c > 0) by apply Rinv_0_lt_compat, cpos.
    unfold Rbar_div; simpl.
    unfold Rbar_mult, Rbar_mult', Rbar_mult_pos.
    destruct l.
    - f_equal; field; trivial.
    - case (Rle_dec 0 (/ c)) ; intros; try lra.
      match_case; intros; match_case_in H0; intros; match_case_in H1; intros; 
        try lra; rewrite H2 in H0; invcs H0.
    - case (Rle_dec 0 (/ c)) ; intros; try lra.
      match_case; intros; match_case_in H0; intros; match_case_in H1; intros; 
        try lra; rewrite H2 in H0; invcs H0.
  Qed.

  Lemma Rbar_lt_div_r (a b: Rbar) (c : R) :
    c > 0 -> Rbar_lt (Rbar_mult a c) b <-> Rbar_lt a (Rbar_div b c).
  Proof.
    intros.
    assert (0 < (/ c)) by now apply Rinv_pos.
    destruct a; destruct b; simpl; destruct (Rle_dec 0 c); try lra
      ; destruct (Rle_dec 0 (/ c)); try lra
      ; destruct (Rle_lt_or_eq_dec 0 (/ c)); simpl; try lra
      ; destruct (Rle_lt_or_eq_dec 0 (c)); simpl; try lra.
    now apply Rcomplements.Rlt_div_r.
  Qed.

  Lemma Rbar_le_div_r (a b : Rbar) (c : R) :
    c > 0 -> Rbar_le (Rbar_mult a c) b <-> Rbar_le a (Rbar_div b c).
  Proof.
    intros.
    assert (0 < (/ c)) by now apply Rinv_pos.
    destruct a; destruct b; simpl; destruct (Rle_dec 0 c); try lra
      ; destruct (Rle_dec 0 (/ c)); try lra
      ; destruct (Rle_lt_or_eq_dec 0 (/ c)); simpl; try lra
      ; destruct (Rle_lt_or_eq_dec 0 (c)); simpl; try lra.
    now apply Rcomplements.Rle_div_r.
  Qed.

  Lemma Rbar_lt_div_l (a b : Rbar) (c : R) :
    c > 0 -> Rbar_lt (Rbar_div a c) b <-> Rbar_lt a (Rbar_mult b c).
  Proof.
    intros.
    assert (0 < (/ c)) by now apply Rinv_pos.
    destruct a; destruct b; simpl; destruct (Rle_dec 0 c); try lra
      ; destruct (Rle_dec 0 (/ c)); try lra
      ; destruct (Rle_lt_or_eq_dec 0 (/ c)); simpl; try lra
      ; destruct (Rle_lt_or_eq_dec 0 (c)); simpl; try lra.
    now apply Rcomplements.Rlt_div_l.
  Qed.
  
  Lemma Rbar_le_div_l (a b : Rbar) (c : R) :
    c > 0 -> Rbar_le (Rbar_div a c) b <-> Rbar_le a (Rbar_mult b c).
  Proof.
    intros.
    assert (0 < (/ c)) by now apply Rinv_pos.
    destruct a; destruct b; simpl; destruct (Rle_dec 0 c); try lra
      ; destruct (Rle_dec 0 (/ c)); try lra
      ; destruct (Rle_lt_or_eq_dec 0 (/ c)); simpl; try lra
      ; destruct (Rle_lt_or_eq_dec 0 (c)); simpl; try lra.
    now apply Rcomplements.Rle_div_l.
  Qed.

  Lemma Rbar_div_Rdiv (x y : R) :
    Rbar_div (Rbar.Finite x) (Rbar.Finite y) = Rdiv x y.
  Proof.
    easy.
  Qed.

  Lemma Rbar_lt_Rlt (x y : R) :
    Rbar_lt (Rbar.Finite x) (Rbar.Finite y) <-> Rlt x y.
  Proof.
    easy.
  Qed.

  Lemma Rbar_le_Rle (x y : R) :
    Rbar_le (Rbar.Finite x) (Rbar.Finite y) <-> Rle x y.
  Proof.
    easy.
  Qed.
