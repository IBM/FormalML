Require Import Reals Sums Lra Lia.
(* Require Import Coquelicot.Hierarchy Coquelicot.Series Coquelicot.Lim_seq Coquelicot.Rbar.*)
Require Import Coquelicot.Coquelicot.
Require Import LibUtils.
Require Import sumtest.

Set Bullet Behavior "Strict Subproofs".

Section fold_iter.

Lemma fold_right_mult_acc (acc : R) (l : list R) :
  List.fold_right Rmult acc l =
  List.fold_right Rmult 1 l * acc.
Proof.
  revert acc.
  induction l; simpl; intros acc.
  - lra.
  - rewrite IHl.
    lra.
Qed.

Lemma iota_is_an_annoying_seq m n : seq.iota m n = List.seq m n.
Proof.
  revert m.
  induction n; simpl; trivial.
Qed.

Lemma fold_right_mult_pos {A} (a: A -> posreal) (l:list A) :
  0 < List.fold_right (fun (a1 : A) (b : R) => a a1 * b) 1 l.
Proof.
  induction l; simpl.
  - lra.
  - apply Rmult_lt_0_compat.
    + apply cond_pos.
    + trivial.
Qed.

Lemma fold_right_max_upper_list  acc l x :
  List.In x l -> x <= List.fold_right Rmax acc l.
Proof.
  induction l; simpl; intros inn; [intuition | ].
  destruct inn.
  - subst.    
    apply Rmax_l.
  - specialize (IHl H).
    eapply Rle_trans.
    + eapply IHl.
    + apply Rmax_r.
Qed.

Lemma fold_right_max_upper_acc acc l :
  acc <= List.fold_right Rmax acc l.
Proof.
  induction l; simpl.
  - lra.
  - eapply Rle_trans.
    + eapply IHl.
    + apply Rmax_r.
Qed.

Lemma fold_right_max_in acc l :
  (List.fold_right Rmax acc l) = acc \/
  List.In (List.fold_right Rmax acc l) l.
Proof.
  induction l; simpl.
  - intuition.
  - destruct IHl.
    + rewrite H.
      apply Rmax_case; eauto.
    + apply Rmax_case; eauto.
Qed.

Lemma fold_right_max_acc (acc1 acc2 : R) (l : list R) :
  Rmax acc2 (List.fold_right Rmax acc1 l) =
  Rmax acc1 (List.fold_right Rmax acc2 l).
Proof.
  revert acc1 acc2.
  induction l; simpl; intros acc1 acc2.
  - apply Rmax_comm.
  - rewrite Rmax_comm, <- Rmax_assoc.
    rewrite (Rmax_comm _ acc2).
    rewrite IHl.
    rewrite Rmax_assoc.
    rewrite (Rmax_comm a _).
    now rewrite <- Rmax_assoc.
Qed.

Lemma fold_right_plus_acc (f : nat -> R) (acc : R) (l : list nat) :
  List.fold_right (fun (i : nat) (acc : R) => f i + acc) acc l =
  List.fold_right (fun (i : nat) (acc : R) => f i + acc) 0 l + acc.
Proof.
  revert acc.
  induction l; simpl; intros acc.
  - lra.
  - rewrite IHl.
    lra.
Qed.

Lemma fold_right_rmax_const acc l c:
  0 <= c ->
  List.fold_right Rmax acc l * c = List.fold_right Rmax (acc*c) (List.map (fun x => x * c) l).
Proof.
  induction l; simpl; trivial; intros.
  rewrite <- IHl by trivial.
  repeat rewrite (Rmult_comm _ c).
  now rewrite RmaxRmult by trivial.
Qed.


Lemma iter_plus_times_const {A} F (l:list A)  c :
        Iter.iter Rplus 0 l (fun k  => F k * c) =
        Iter.iter Rplus 0 l (fun k => F k) * c.
Proof.
  induction l; simpl; intros.
  - lra.
  - rewrite IHl.
    lra.
Qed.

Lemma list_seq_init_map init len :
  List.seq init len = List.map (fun x => (init + x)%nat) (List.seq 0 len).
Proof.
  induction init; simpl.
  - now rewrite List.map_id.
  - simpl.
    rewrite <- List.seq_shift.
    rewrite IHinit.
    now rewrite List.map_map.
Qed.    

End fold_iter.


Section products.

Definition part_prod_n (a : nat -> posreal) (n m : nat) :R  :=
  List.fold_right Rmult 1 (List.map (fun x => (a x).(pos)) (List.seq n (S m - n)%nat)).

Definition part_prod (a : nat -> posreal) (n : nat) : R :=
  part_prod_n a 0 n.

Lemma pos_part_prod_n  (a : nat -> posreal) (m n : nat) :
  0 < part_prod_n a m n.
Proof.
  unfold part_prod_n.
  generalize (S n - m)%nat; intros.
  revert m.
  induction n0; simpl; intros m.
  - lra.
  - apply Rmult_lt_0_compat; [|trivial].
    apply cond_pos.
Qed.

Lemma pos_part_prod (a : nat -> posreal) (n : nat) :
  0 < part_prod a n.
Proof.
  apply pos_part_prod_n.
Qed.

Definition part_prod_n_pos (a : nat -> posreal) (m n : nat) : posreal :=
  mkposreal (part_prod_n a m n) (pos_part_prod_n a m n).

Definition part_prod_pos (a : nat -> posreal) (n : nat) : posreal :=
  mkposreal (part_prod a n) (pos_part_prod a n).

Lemma part_prod_n_S a m n :
  (m <= S n)%nat ->
  (part_prod_n a m (S n)) = part_prod_n a m n * a (S n).
Proof.
  intros mle.
  unfold part_prod_n.
  replace (S (S n) - m)%nat with ((S n - m) + 1)%nat by lia.
  rewrite seq_plus, List.map_app, List.fold_right_app, fold_right_mult_acc.
  f_equal.
  simpl.
  destruct m; simpl.
  - lra.
  - field_simplify.
    simpl.
    do 3 f_equal.
    lia.
Qed.

Lemma part_prod_n_k_k a k :
  part_prod_n a k k = a k.
Proof.
  unfold part_prod_n.
  replace (S k - k)%nat with (1%nat) by lia.
  simpl; lra.
Qed.

Lemma part_prod_n_1 a m n :
  (m > n)%nat ->
  (part_prod_n a m n) = 1.
Proof.
  intros.
  unfold part_prod_n.
  replace (S n - m)%nat with (0%nat) by lia.
  now simpl.
Qed.  


Theorem ln_part_prod (a : nat -> posreal) (n : nat) :
  ln (part_prod_pos a n) = sum_n (fun n1 => ln (a n1)) n.
Proof.
  unfold part_prod_pos, part_prod; simpl.
  unfold sum_n, sum_n_m.
  unfold Iter.iter_nat.
  rewrite Iter.iter_iter'.
  rewrite iota_is_an_annoying_seq.
  unfold Iter.iter', part_prod_n.
  generalize (List.seq 0 (S n - 0)); intros l; simpl.
  rewrite ListAdd.fold_right_map.
  induction l; simpl.
  - apply ln_1.
  - rewrite ln_mult.
    + now rewrite IHl.
    + apply cond_pos.
    + apply fold_right_mult_pos.
Qed.

Lemma initial_seg_prod (a : nat -> posreal) (m k:nat):
  part_prod a (m + S k)%nat = (part_prod a m) * (part_prod_n a (S m) (m + S k)%nat).
Proof.
  induction k; simpl.
  - unfold part_prod.
    replace (m+1)%nat with (S m) by lia.
    rewrite part_prod_n_S; [|lia].
    rewrite part_prod_n_k_k; lra.
  - replace (m + S (S k))%nat with (S (m + S k)%nat) by lia; simpl.
    unfold part_prod in *.
    rewrite part_prod_n_S; [|lia].
    rewrite IHk; simpl.
    rewrite part_prod_n_S; [|lia]; lra.
Qed.

Lemma initial_seg_prod_n (a : nat -> posreal) (k m n:nat):
  (k <= m)%nat -> 
  part_prod_n a k (S m + n)%nat = (part_prod_n a k m) * (part_prod_n a (S m) (S m + n)%nat).
Proof.
  intros.
  induction n; simpl.
  - replace (m+0)%nat with (m) by lia.
    rewrite part_prod_n_S.
    now rewrite part_prod_n_k_k.
    lia.
  - rewrite part_prod_n_S; [|lia].
    rewrite part_prod_n_S; [|lia].
    replace (m + S n)%nat with (S m + n)%nat by lia.
    rewrite IHn; lra.
Qed.

Lemma part_prod_n_shift (F : nat -> posreal) (m n:nat) :
  part_prod_n (fun k : nat => F (m + k)%nat) 0 n = part_prod_n F m (n +  m).
Proof.
  unfold part_prod_n.
  f_equal.
  replace (S n - 0)%nat with (S n) by lia.
  replace (S (n + m) - m)%nat with (S n) by lia.
  induction n.
  - simpl.
    now replace (m + 0)%nat with (m) by lia.
  - replace (S (S n)) with (S n+1)%nat by lia.
    rewrite seq_plus, seq_plus, List.map_app.
    rewrite IHn.
    replace (S n) with (n+1)%nat by lia.
    rewrite List.map_app.
    now simpl.
Qed.    

Lemma initial_seg_prod2 (a : nat -> posreal) (m k:nat):
  part_prod a (k + S m)%nat =
  (part_prod a m) * (part_prod (fun k0 : nat => a (S m + k0)%nat) k).
Proof.
  generalize (initial_seg_prod a m k).
  unfold part_prod.
  intros.
  replace (k + S m)%nat with (m + S k)%nat by lia.
  rewrite H, part_prod_n_shift.
  now replace (m + S k)%nat with (k + S m)%nat by lia.
Qed.

Program Definition pos_sq (c : posreal) : posreal :=
  mkposreal (c * c) _.
Next Obligation.
  apply Rmult_lt_0_compat; apply (cond_pos c).
Qed.

Definition pos_sq_fun (a : nat -> posreal) : (nat -> posreal) :=
  fun n => pos_sq (a n).

Lemma part_prod_pos_sq_pos (a : nat -> posreal) (n:nat) :
  (part_prod_pos (pos_sq_fun a) n).(pos) = (pos_sq_fun (part_prod_pos a) n).(pos).
Proof.
  unfold pos_sq_fun, pos_sq, part_prod_pos; simpl.
  induction n; simpl; trivial.
  - unfold part_prod, part_prod_n.
    simpl; lra.
  - unfold part_prod in *.
    rewrite part_prod_n_S; [|lia].
    rewrite IHn; simpl.
    rewrite part_prod_n_S; [|lia]; lra.
Qed.

Lemma inf_prod_sq_0 (a : nat -> posreal) :
  is_lim_seq (part_prod_pos a) 0 ->
  is_lim_seq (part_prod_pos (pos_sq_fun a)) 0.
Proof.
  intros.
  apply (is_lim_seq_ext (fun n => pos_sq_fun (part_prod_pos a) n)).
  intros; now rewrite (part_prod_pos_sq_pos a n).
  simpl; replace (0) with (0 * 0) by lra.
  now apply is_lim_seq_mult with (l1 := 0) (l2 := 0).
Qed.


Lemma inf_prod_m_0 (a : nat -> posreal):
  is_lim_seq (part_prod_pos a) 0 ->
  forall (m:nat), is_lim_seq (part_prod_pos (fun n => a (m + n)%nat)) 0.
Proof.
  intros.
  destruct m.
  - apply (is_lim_seq_ext (part_prod a)); trivial.
  - generalize (is_lim_seq_incr_n (part_prod_pos a) (S m) 0).
    intros.
    destruct H0.
    specialize (H0 H).
    apply (is_lim_seq_ext (fun k => (/ (part_prod a m)) *
                                  (part_prod a (k + S m)))).
    + intros.
      rewrite initial_seg_prod2.
      rewrite <- Rmult_assoc.
      rewrite Rmult_comm with (r2 := part_prod a m).
      rewrite  Rinv_r_simpl_r; trivial.
      apply Rgt_not_eq.
      apply Rlt_gt.
      apply pos_part_prod.
    + apply is_lim_seq_mult with (l1 := / (part_prod_pos a m)) (l2 := 0).
      * apply is_lim_seq_const.
      * apply H0.
      * unfold is_Rbar_mult; simpl.
        now rewrite Rmult_0_r.
Qed.

Lemma inf_prod_n_m_0 (a : nat -> posreal):
  is_lim_seq (part_prod_pos a) 0 ->
  forall (m:nat), is_lim_seq (part_prod_n_pos a m) 0.
Proof.
  intros.
  unfold part_prod_n_pos.
  apply is_lim_seq_incr_n with (N := m).
  apply (is_lim_seq_ext (fun n : nat => part_prod_pos (fun k : nat => a (m + k)%nat) n)).
  intros; simpl.
  unfold part_prod.
  now rewrite part_prod_n_shift.  
  now apply inf_prod_m_0.
Qed.  

End products.

Section series_sequences.

Lemma series_seq (a : nat -> R) (l:R) :
  is_series a l <-> is_lim_seq (sum_n a) l.
Proof.
  now unfold is_series, is_lim_seq.
Qed.

Lemma log_product_iff_sum_logs (a : nat -> posreal) (l:R): 
  is_lim_seq (fun n => (ln (part_prod_pos a n))) l <-> is_series (fun n => ln (a n)) l .
Proof.
  rewrite series_seq.
  split.
  - apply is_lim_seq_ext; intros.
    apply ln_part_prod.
  - apply is_lim_seq_ext; intros.
    now rewrite <- ln_part_prod.  
Qed.

Lemma derivable_pt_ln (x:R) :
  0 < x -> derivable_pt ln x.
Proof.
  intros.
  unfold derivable_pt, derivable_pt_abs.
  exists (/ x).
  now apply derivable_pt_lim_ln.
Qed.

Lemma log_product_iff_product (a : nat -> posreal) (l:posreal): 
  is_lim_seq (fun n => (ln (part_prod_pos a n))) (ln l) <-> is_lim_seq (part_prod_pos a) l .
Proof.
  assert (0 < l) by (apply (cond_pos l)).
  split; intros.
  - apply (is_lim_seq_ext (fun n =>  exp (ln (part_prod_pos a n)))).
    + intros.
      rewrite exp_ln; f_equal.
      apply pos_part_prod.
    + replace (pos l) with (exp (ln (pos l))) by (rewrite exp_ln; trivial).
      apply is_lim_seq_continuous; [|trivial].
      apply derivable_continuous_pt; apply derivable_pt_exp.
  - apply is_lim_seq_continuous; [|trivial].
    apply derivable_continuous_pt; now apply derivable_pt_ln.
Qed.

Lemma is_product_iff_is_log_sum (a : nat -> posreal) (l:posreal) :
  is_lim_seq (part_prod_pos a) l <-> is_series (fun n => ln (a n)) (ln l).
Proof.
  rewrite <- log_product_iff_sum_logs.
  now rewrite log_product_iff_product.
Qed.

Lemma is_lim_seq_pos (a : nat -> posreal) (l:R) (lb:posreal):
  (forall n, lb <= a n) -> is_lim_seq a l -> 0 < l.
Proof.
  generalize (is_lim_seq_const lb); intros.
  generalize (is_lim_seq_le (fun _ => lb) a lb l H0 H H1).
  destruct lb; simpl.
  lra.
Qed.    

Lemma ex_product_iff_ex_log_sum (a : nat -> posreal) (lb:posreal):
  (forall n, lb <= part_prod_pos a n) -> 
  ex_finite_lim_seq (part_prod_pos a) <-> ex_series (fun n => ln (a n)).
Proof.
  unfold ex_finite_lim_seq, ex_series.
  split; intros; destruct H0.
  - generalize (is_lim_seq_pos (part_prod_pos a) x lb H H0); intros.
    exists (ln x).
    now apply is_product_iff_is_log_sum with (l := mkposreal x H1).
  - exists (exp x).
    replace (x) with (ln (exp x)) in H0 by apply ln_exp.
    assert (0 < exp x) by apply exp_pos.
    now apply is_product_iff_is_log_sum with (l := mkposreal (exp x) H1).
Qed.

Lemma sum_S (f : nat -> R) (n : nat) :
  sum_n f (S n) = sum_n f n + f (S n).
Proof.
  unfold sum_n, sum_n_m.
  unfold Iter.iter_nat.
  repeat rewrite Iter.iter_iter'.
  unfold Iter.iter'.
  rewrite iota_is_an_annoying_seq.
  rewrite (iota_is_an_annoying_seq 0 (S n - 0)).
  replace (S (S n) - 0)%nat with (S n + 1)%nat by lia.
  rewrite seq_plus.
  replace (0 + S n)%nat with (S n) by lia.
  replace (S n - 0)%nat with (S n) by lia.  
  rewrite List.fold_right_app.
  simpl.
  unfold plus, zero; simpl.
  rewrite fold_right_plus_acc.
  lra.
Qed.  

Lemma sum_split (f : nat -> R) (n1 n2 m : nat) :
  (n1 <= m)%nat -> (m < n2)%nat -> 
  sum_n_m f n1 n2 = sum_n_m f n1 m + sum_n_m f (S m) n2.
Proof.
  intros.
  unfold sum_n_m.
  unfold Iter.iter_nat.
  repeat rewrite Iter.iter_iter'.
  unfold Iter.iter'.
  rewrite iota_is_an_annoying_seq.
  rewrite (iota_is_an_annoying_seq n1  (S m - n1)).
  rewrite (iota_is_an_annoying_seq (S m) (S n2 - S m)).  
  replace (S n2 - n1)%nat with ((S m - n1) + (S n2 - S m))%nat by lia.
  rewrite seq_plus.
  rewrite List.fold_right_app.
  rewrite fold_right_plus_acc.
  replace (n1 + (S m - n1))%nat with (S m) by lia.
  unfold plus, zero.
  simpl.
  lra.
Qed.

Lemma nneg_sum_n_m_sq  (a : nat -> R) (n m : nat) :
  0 <= sum_n_m (fun k => Rsqr (a k)) n m.
Proof.
  replace (0) with (INR (S m - n) * 0) by lra.
  rewrite <- sum_n_m_const.
  apply sum_n_m_le.
  intros.
  apply Rle_0_sqr.
Qed.

Lemma nneg_series_sq (a : nat -> R) :
  let fnsq := (fun n => Rsqr (a n)) in
  ex_series fnsq ->
  0 <= Series fnsq.
Proof.
  intros.
  assert (Series (fun _ => 0) = 0).
  unfold Series.
  rewrite <- (Lim_seq_ext (fun _ => 0)).
  now rewrite Lim_seq_const.
  intros.
  rewrite sum_n_const; lra.
  rewrite <- H0.
  apply Series_le; trivial.
  intros.
  split; [lra|apply Rle_0_sqr].
Qed.

Lemma sub_sum_limit (a : nat -> R) (n: nat) :
  let fnsq := (fun n => Rsqr (a n)) in      
  ex_series fnsq ->
  sum_n fnsq n <= Series fnsq.
Proof.
  intros.
  assert (0 < S n)%nat by lia.
  generalize (Series_incr_n fnsq (S n) H0 H).
  intros.
  rewrite H1.
  rewrite <- sum_n_Reals.
  replace (Init.Nat.pred (S n)) with (n) by lia.
  replace (sum_n fnsq n) with (sum_n fnsq n + 0) at 1 by lra.
  apply Rplus_le_compat_l.
  apply (nneg_series_sq (fun k => a (S n + k)%nat)).
  rewrite <- (ex_series_incr_n (fun n => Rsqr (a n)) (S n)); trivial.
Qed.

Lemma sum_n_le_loc (a b : nat -> R) (k : nat) :
  (forall n : nat, (n <= k)%nat -> a n <= b n) -> 
  sum_n a k <= sum_n b k.
Proof.
  intros.
  induction k.
  - rewrite sum_O.
    rewrite sum_O.
    apply H; lia.
  - rewrite sum_Sn.
    rewrite sum_Sn.
    assert (forall n : nat, (n <= k)%nat -> a n <= b n).
    intros.
    apply H; lia.
    specialize (IHk H0).
    apply Rplus_le_compat; trivial; apply H; lia.
Qed.

Lemma lim_sq_0 (a : nat -> R) :
  is_series (fun k => Rsqr (a k)) 0 ->
  forall n, 0 = a n.
Proof.
  intros.
  assert (H' := H).
  apply is_series_unique in H.
  assert (ex_series (fun k : nat => (a k)²)).
  unfold ex_series.
  exists 0; trivial.
  generalize (sub_sum_limit a n H0); intros.
  rewrite H in H1.
  generalize (nneg_sum_n_m_sq  a 0%nat n); intros.
  unfold sum_n in H1.
  generalize  (Rle_antisym _ _ H2 H1); intros.
  induction n.
  - rewrite sum_n_n in H3; trivial.
    now rewrite Rsqr_eq_0.
  - rewrite sum_n_Sm in H3; unfold plus in H3; simpl in H3; [|lia].
    generalize (Rle_0_sqr (a (S n))); intros.
    generalize (nneg_sum_n_m_sq  a 0%nat n); intros.    
    generalize (Rplus_eq_R0 _ _ H4 H5).
    intros.
    destruct H6; [lra|].
    now apply Rsqr_eq_0 in H6.
Qed.

End series_sequences.


Section max_prod.

Definition max_prod_fun (a : nat -> posreal) (m n : nat) : R :=
  List.fold_right Rmax 0 (List.map (fun k => part_prod_n a k n) (List.seq 0 (S m)%nat)).


Lemma max_prod_le (F : nat -> posreal) (k m n:nat) :
  (k <= m)%nat ->
  (m <= n)%nat ->  
  part_prod_n F k n <= max_prod_fun F m n.
Proof.
  intros.
  unfold max_prod_fun.
  apply fold_right_max_upper_list.
  apply List.in_map_iff.
  exists k.
  split; trivial.
  apply List.in_seq; lia.
Qed.
    
Lemma max_bounded1_pre_le (F : nat -> posreal) (m n:nat) :
  (forall (n:nat), F n <= 1) ->
  (S m <= n)%nat ->
  part_prod_n F m n <= part_prod_n F (S m) n.
Proof.
  intros.
  unfold part_prod_n.
  replace (S n - S m)%nat with (n - m)%nat by lia.
  replace (S n - m)%nat with (1 + (n - m))%nat by lia.
  rewrite seq_plus, List.map_app; simpl.
  replace (m + 1)%nat with (S m) by lia.
  specialize (H m).
  rewrite <- Rmult_1_l.
  apply Rmult_le_compat_r; trivial.
  rewrite ListAdd.fold_right_map.
  left; apply fold_right_mult_pos.
Qed.

Lemma max_bounded1 (F : nat -> posreal) (m n:nat) :
  (forall (n:nat), F n <= 1) ->
  (m <= n)%nat -> max_prod_fun F m n = part_prod_n F m n.
Proof.
  intros.
  unfold max_prod_fun.
  induction m.
  - apply Rmax_left.
    left.
    apply pos_part_prod_n.
  - replace (S (S m)) with (S m + 1)%nat by lia.
    rewrite seq_plus, List.map_app, List.fold_right_app.
    replace (List.fold_right Rmax
    (List.fold_right Rmax 0 (List.map (fun k : nat => part_prod_n F k n) (List.seq (0 + S m) 1)))
    (List.map (fun k : nat => part_prod_n F k n) (List.seq 0 (S m))))
      with
        (Rmax 0 (List.fold_right Rmax
    (List.fold_right Rmax 0 (List.map (fun k : nat => part_prod_n F k n) (List.seq (0 + S m) 1)))
    (List.map (fun k : nat => part_prod_n F k n) (List.seq 0 (S m))))).
    + rewrite fold_right_max_acc.
      rewrite IHm by lia.
      simpl.
      rewrite (Rmax_left _ 0).
      * apply Rmax_left.
        now apply max_bounded1_pre_le.
      * left; apply pos_part_prod_n.
    + apply Rmax_right; simpl.
      apply Rle_trans with (r2 := part_prod_n F 0 n); trivial.
      left; apply pos_part_prod_n.
      apply Rmax_l.
Qed.

Lemma lim_max_bounded1 (F : nat -> posreal) (m:nat) :
  (forall (n:nat), F n <= 1) ->
  is_lim_seq (part_prod F) 0 -> is_lim_seq (fun n => max_prod_fun F m (n+m)%nat) 0.
Proof.
  intros.
  apply (is_lim_seq_ext (part_prod (fun k : nat => F (m + k)%nat))).
  - intros.
    rewrite max_bounded1; [|trivial|lia].
    unfold part_prod.
    apply part_prod_n_shift.
  - now apply inf_prod_m_0.
Qed.

Lemma pos_sq_bounded1 (F : nat -> posreal) (n : nat) :
  F n <= 1 -> (pos_sq_fun F) n <= 1.
Proof.
  intros.
  unfold pos_sq_fun, pos_sq; simpl.
  replace (1) with (1 * 1) by lra.
  assert (0 <= F n) by (destruct (F n); simpl; lra).
  apply Rmult_le_compat; trivial.
Qed.

Lemma lim_max_bounded1_sq (F : nat -> posreal) (m:nat) :
  (forall (n:nat), F n <= 1) ->
  is_lim_seq (part_prod F) 0 -> is_lim_seq (fun n => max_prod_fun (pos_sq_fun F) m (n+m)%nat) 0.
Proof.
  intros.
  apply lim_max_bounded1; intros.
  now apply pos_sq_bounded1.
  apply inf_prod_sq_0.
  apply H0.
Qed.

Lemma max_prod_index_n (F : nat -> posreal) (m : nat) (n:nat) (mle:(m <= n)%nat) :
  exists k : nat,
    (k <= m)%nat /\
     part_prod_n F k n = max_prod_fun F m n.
Proof.
  unfold max_prod_fun.
  destruct (fold_right_max_in 0 (List.map (fun k : nat => part_prod_n F k n) (List.seq 0 (S m)))).
  - generalize (pos_part_prod_n F); intros.
    simpl in H.
    generalize (Rmax_l  (part_prod_n F 0 n) (List.fold_right Rmax 0 (List.map (fun k : nat => part_prod_n F k n) (List.seq 1 m)))); intros ineq1.
    rewrite H in ineq1.
    specialize (H0 0%nat n); lra.
  - rewrite List.in_map_iff in H.
    destruct H as [k [keqq ink]].
    apply List.in_seq in ink.
    exists k.
    split; trivial; lia.
Qed.

Lemma max_prod_n_S (a: nat -> posreal) (m n : nat) :
  (m <= n)%nat ->
  (max_prod_fun a m (S n)) = max_prod_fun a m n * a (S n).
Proof.
  intros mle.
  unfold max_prod_fun.
  rewrite fold_right_rmax_const.
  - rewrite List.map_map.
    f_equal.
    + lra.
    + apply List.map_ext_in; intros.
      apply List.in_seq in H.
      apply part_prod_n_S.
      lia.
  - left. apply cond_pos. 
Qed.  

Lemma initial_max_prod_n (a : nat -> posreal) (k m n:nat):
  (k <= m)%nat -> 
  max_prod_fun a k (S m + n)%nat = (max_prod_fun a k m) * (part_prod_n a (S m) (S m + n)%nat).
Proof.
  intros.
  induction n; simpl.
  - replace (m+0)%nat with (m) by lia.
    rewrite part_prod_n_k_k, max_prod_n_S; trivial.
  - rewrite part_prod_n_S; [|lia].
    rewrite max_prod_n_S; [|lia].
    replace (m + S n)%nat with (S m + n)%nat by lia.
    rewrite IHn; lra.
Qed.

Lemma max_prod_index (F : nat -> posreal) (m:nat) :
  exists (k:nat), (k<=m)%nat /\
                  forall (n:nat), (m <= n)%nat ->
                  part_prod_n F k n = max_prod_fun F m n.
Proof.
  intros.
  assert (m <= m)%nat by lia.
  generalize (max_prod_index_n F m m H); intros.
  destruct H0 as [k H0]; destruct H0.
  exists k.
  split; trivial; intros.
  destruct (lt_dec m n).
  + remember (n - S m)%nat as nm.
    replace (n) with (S m + nm)%nat; [|lia].
    rewrite initial_seg_prod_n; trivial.
    rewrite initial_max_prod_n; trivial.
    now rewrite H1.
  + replace (n) with (m) by lia.
    now rewrite H1.
Qed.

Lemma lim_max_prod_m_0 (a : nat -> posreal):
  is_lim_seq (part_prod_pos a) 0 -> 
  forall (m:nat), is_lim_seq (max_prod_fun a m) 0.
Proof.
  intros.
  generalize (max_prod_index a m); intros.
  destruct H0 as [k H0]; destruct H0.
  apply is_lim_seq_incr_n with (N:=m).
  apply (is_lim_seq_ext (fun n => part_prod_n a k (n+m)%nat)).
  intros; apply H1; lia.
  generalize (inf_prod_n_m_0 a H k); intros.
  apply is_lim_seq_incr_n.
  now unfold part_prod_n_pos in H2; simpl in H2.
Qed.

End max_prod.

Lemma prod_sq_bounded_1 (F : nat -> posreal) (r s :nat) :
  (forall (n:nat), F n <= 1) -> part_prod_n (pos_sq_fun F) r s <= 1.
Proof.
  intros.
  generalize (pos_sq_bounded1 F); intros.
  unfold part_prod_n.
  induction (S s-r)%nat.
  - simpl.
    lra.
  - replace (S n) with (n+1)%nat by lia.
    rewrite seq_plus, List.map_app, List.fold_right_app; simpl.
    replace (1) with (1*1) at 2 by lra.
    rewrite fold_right_mult_acc.
    apply Rmult_le_compat; trivial.
    + rewrite ListAdd.fold_right_map; left.
      apply (fold_right_mult_pos (pos_sq_fun F)).
    + left; apply Rmult_lt_0_compat; [|lra].
      apply Rmult_lt_0_compat; apply cond_pos.
    + rewrite Rmult_1_r, <- Rmult_1_r.
      apply Rmult_le_compat; trivial.
      left; apply cond_pos.
      left; apply cond_pos.      
Qed.

Lemma part_prod_le (F : nat -> posreal) (m k n:nat) :
  (forall (n:nat), F n <= 1) ->
  (m + k <= n)%nat ->
  part_prod_n (pos_sq_fun F) m n <= part_prod_n (pos_sq_fun F) (m + k)%nat n.
Proof.
  intros.
  induction k.
  - replace (m + 0)%nat with (m) by lia; lra.
  - assert (m + k <= n)%nat by lia.
    specialize (IHk H1).
    apply Rle_trans with (r2 := part_prod_n (pos_sq_fun F) (m + k) n); trivial.
    replace (m + S k)%nat with (S (m+k)%nat) by lia.
    destruct (le_gt_dec (S (m+k)) n).
    + apply max_bounded1_pre_le; trivial.
      intros; apply pos_sq_bounded1; trivial.
    + rewrite (part_prod_n_1 (pos_sq_fun F) (S (m + k)%nat)) ; [|lia].
      apply prod_sq_bounded_1; trivial.
Qed.      

Section Dvoretsky.

Theorem Dvoretzky4_0 (F: nat -> posreal) (sigma V : nat -> R) :
  (forall (n:nat), V (S n) <= (F n) * (V n) + (sigma n)) ->
  (forall (n:nat), 
      V (S n) <= sum_n (fun k => (sigma k)*(part_prod_n F (S k) n)) n + 
                 (V 0%nat)*(part_prod_n F 0 n)).
Proof.
  intros.
  induction n.
  - unfold sum_n, part_prod_n; simpl.
    unfold sum_n_m, Iter.iter_nat; simpl.
    specialize (H 0%nat).
    unfold plus, zero; simpl; lra.
  - rewrite sum_Sn.
    unfold sum_n in *.
    unfold sum_n_m, Iter.iter_nat in *; simpl.
    unfold plus, zero in *; simpl in *.
    rewrite (Iter.iter_ext _ _ _ (fun k : nat => sigma k * part_prod_n F (S k) (S n))
                           (fun k : nat => (sigma k * part_prod_n F (S k) n) * F (S n))).
    + rewrite iter_plus_times_const.
      specialize (H (S n)).
      rewrite part_prod_n_S; [|lia].
      rewrite (part_prod_n_1 _ (S (S n)) (S n)); [|lia].
      rewrite part_prod_n_S; [|lia].
      apply Rle_trans with (r2 := F (S n) * V (S n) + sigma (S n)); trivial.
      apply Rmult_le_compat_l with (r:=F (S n)) in IHn.
      apply Rplus_le_compat_r with (r:=sigma (S n))  in IHn.
      lra.
      left; apply cond_pos.
    + intros.
      rewrite part_prod_n_S.
      * lra.
      * generalize (Iter.In_iota 1 x n); intros HH.
        replace (S n - 1)%nat with n in HH by lia.
        apply HH in H0; lia.
Qed.

Lemma sum_bound_prod_A (F : nat -> posreal) (sigma : nat -> R) (A : R) (n m:nat) :
  (forall r s, part_prod_n (pos_sq_fun F) r s <= A) ->
  sum_n_m (fun k => (Rsqr (sigma k))*(part_prod_n (pos_sq_fun F) (S k) n)) (S m) n <=
  (sum_n_m (fun k => Rsqr (sigma k)) (S m) n) * A.
Proof.
  intros.
  rewrite <- sum_n_m_mult_r with (a := A).
  apply sum_n_m_le; intros.
  specialize (H (S k) n).
  apply Rmult_le_compat; trivial.
  apply Rle_0_sqr.
  left; apply pos_part_prod_n.
  lra.
Qed.

Lemma sum_bound3_max (F : nat -> posreal) (sigma : nat -> R) (n m:nat) :
  (S m <= n)%nat ->
  sum_n (fun k => (Rsqr (sigma k))*(part_prod_n (pos_sq_fun F) (S k) n)) m <=
  (sum_n (fun k => (Rsqr (sigma k))) m) * (max_prod_fun (pos_sq_fun F) (S m) n).
Proof.  
  intros.
  rewrite <- sum_n_mult_r with (a := (max_prod_fun (pos_sq_fun F) (S m) n)).
  apply sum_n_le_loc; intros.
  apply Rmult_le_compat_l.
  apply Rle_0_sqr.
  apply max_prod_le; lia.
Qed.
    
Theorem Dvoretzky4_8_5 (F : nat -> posreal) (sigma V: nat -> R) (n m:nat) (A:R):
  (forall r s, part_prod_n (pos_sq_fun F) r s <= A) ->
  (forall (n:nat), Rsqr (V (S n)) <= (pos_sq_fun F) n * Rsqr (V n) + Rsqr (sigma n)) ->
  (m<n)%nat ->
   Rsqr (V (S n)) <= 
     ( sum_n_m (fun k => Rsqr (sigma k)) (S m) n) * A +
     (Rsqr (V 0%nat) + sum_n (fun k => (Rsqr (sigma k))) m) *
             (max_prod_fun (pos_sq_fun F) (S m) n).
Proof.
  intros F1 Vsqle mn.
  generalize (Dvoretzky4_0 (pos_sq_fun F) (fun k => Rsqr(sigma k)) (fun k => Rsqr (V k))).
  intros.
  specialize (H Vsqle n).
  unfold sum_n in H.
  rewrite sum_split with (m := m) in H; trivial; [|lia].
  generalize (sum_bound_prod_A F sigma A n m F1); intros.
  generalize (max_prod_le (pos_sq_fun F) 0 (S m) n); intros.
  generalize (sum_bound3_max F sigma n m); intros.
  apply Rmult_le_compat_l with (r := Rsqr (V 0%nat)) in H1; try lia; [|apply Rle_0_sqr].
  unfold sum_n in *.
  assert (S m <= n)%nat by lia.
  specialize (H2 H3).
  generalize (Rplus_le_compat _ _ _ _ H0 H1); intros.
  generalize (Rplus_le_compat _ _ _ _ H2 H4); intros; lra.
Qed.


Theorem Dvoretzky4_8_5_1 (F : nat -> posreal) (sigma V: nat -> R) (n m:nat) (A sigmasum:R) :
  (forall r s, part_prod_n (pos_sq_fun F) r s <= A) ->
  (forall (n:nat), Rsqr (V (S n)) <= (pos_sq_fun F) n * Rsqr (V n) + Rsqr (sigma n)) ->
  is_series (fun n => Rsqr (sigma n)) sigmasum ->   
  (m<n)%nat ->
   Rsqr (V (S n)) <= 
      (sum_n_m (fun k => Rsqr (sigma k)) (S m) n) * A +
     (Rsqr (V 0%nat) + sigmasum) * (max_prod_fun (pos_sq_fun F) (S m) n).      
Proof.
  intros.
  generalize (Dvoretzky4_8_5 F sigma V n m A H H0 H2); intros.
  assert (sum_n (fun k : nat => (sigma k)²) m <= sigmasum).
  assert (H1' := H1).
  apply is_series_unique in H1.
  assert (ex_series (fun k : nat => (sigma k)²)).
  unfold ex_series.
  exists sigmasum; trivial.
  rewrite <- H1.
  apply sub_sum_limit; trivial.
  apply Rplus_le_compat_l with (r := Rsqr (V 0%nat)) in H4.
  apply Rmult_le_compat_r with 
      (r := max_prod_fun (pos_sq_fun F) (S m) n) in H4.
  lra.
  assert (part_prod_n (pos_sq_fun F) (S m) n <=  max_prod_fun (pos_sq_fun F) (S m) n).
  apply max_prod_le; lia.
  assert (0 <= part_prod_n (pos_sq_fun F) (S m) n).
  left; apply pos_part_prod_n.
  apply (Rle_trans  _ _ _ H6 H5).
Qed.

Lemma Dvoretzky4_sigma_v0_2_0 (F : nat -> posreal) (sigma V: nat -> R) :
  (forall (n:nat), Rsqr (V (S n)) <= (pos_sq_fun F) n * Rsqr (V n) + Rsqr (sigma n)) ->
  ex_series (fun n => Rsqr (sigma n)) ->
  Series (fun n => Rsqr (sigma n)) + Rsqr (V 0%nat) = 0 ->
  forall n, V n = 0.
Proof.
  intros.
  remember (Series (fun n => Rsqr (sigma n))) as sigma_sum.
  generalize (nneg_series_sq sigma H0); simpl; intros.
  generalize (Rle_0_sqr (V 0%nat)); intros.
  rewrite <- Heqsigma_sum in H2.
  generalize (Rplus_eq_R0 sigma_sum (Rsqr (V 0%nat)) H2 H3 H1); intros.
  destruct H4.
  generalize (lim_sq_0 sigma).
  rewrite Heqsigma_sum in H4; intros.
  generalize (Series_correct _ H0); intros.
  rewrite H4 in H7.
  specialize (H6 H7).
  induction n.
  - now apply Rsqr_eq_0 in H5.
  - specialize (H n).
    rewrite IHn, <- H6 in H.
    rewrite Rsqr_0, Rplus_0_r, Rmult_0_r in H.
    generalize (Rle_0_sqr (V (S n))); intros.
    generalize (Rle_antisym _ _ H H8).
    apply Rsqr_eq_0.
Qed.
  

Theorem Dvoretzky4_A (F : nat -> posreal) (sigma V: nat -> R) (A:posreal) :
  (forall r s, part_prod_n (pos_sq_fun F) r s <= A) ->
  (forall (n:nat), Rsqr (V (S n)) <= (pos_sq_fun F) n * Rsqr (V n) + Rsqr (sigma n)) ->
  is_lim_seq (part_prod F) 0 ->
  ex_series (fun n => Rsqr (sigma n)) ->   
  is_lim_seq (fun n => Rsqr (V n)) 0.
Proof.
  intros.
  generalize (Cauchy_ex_series (fun n : nat => (sigma n)²) H2); intros.
  unfold Cauchy_series in H3.
  generalize (inf_prod_sq_0 F H1); intros lim_prod_sq.
  generalize (lim_max_prod_m_0 (pos_sq_fun F) lim_prod_sq); intros.
  rewrite is_lim_seq_Reals; unfold Un_cv; intros.
  assert (0 < eps/(2*A)).
  apply Rdiv_lt_0_compat; trivial.
  apply Rmult_lt_0_compat; [lra|apply cond_pos].
  remember (mkposreal (eps/(2*A)) H6) as half_eps_div_A.
  specialize (H3 half_eps_div_A).
  destruct H3 as [Nsigma H3].
  unfold norm in H3; simpl in H3.
  unfold abs in H3; simpl in H3.
  assert (H2' := H2).
  unfold ex_series in H2.
  destruct H2 as [sigma_sum H2].
  remember (sigma_sum + Rsqr (V 0%nat)) as sigma_V0_2.
  destruct (Req_dec sigma_V0_2 0).
  - exists (0%nat); intros.
    rewrite Heqsigma_V0_2 in H7.
    apply is_series_unique in H2.
    rewrite <- H2 in H7.
    rewrite (Dvoretzky4_sigma_v0_2_0 F sigma); trivial.
    unfold R_dist.
    now rewrite Rsqr_0, Rminus_0_r, Rabs_R0.
  - assert (0 <= sigma_V0_2).
    rewrite Heqsigma_V0_2.
    apply Rplus_le_le_0_compat.
    assert (H2'' := H2).
    apply is_series_unique in H2''.
    rewrite <- H2''.
    apply nneg_series_sq; trivial.
    apply Rle_0_sqr.
    destruct H8; [|congruence].
    remember ((eps / 2) / sigma_V0_2) as part_prod_eps.
    specialize (H4 (S Nsigma)).
    rewrite is_lim_seq_Reals in H4; unfold Un_cv in H4.
    specialize (H4 part_prod_eps).
    assert (part_prod_eps > 0).
    rewrite Heqpart_prod_eps.
    apply  Rdiv_lt_0_compat; trivial; lra.
    specialize (H4 H9). 
    destruct H4 as [NH4 H4].
    remember ( NH4 + S Nsigma)%nat as NV.
    exists (S NV).
    unfold R_dist in *; intros.
    rewrite Rminus_0_r, Rabs_pos_eq; [| apply Rle_0_sqr].
    generalize (Dvoretzky4_8_5_1 F sigma V (n-1)%nat Nsigma A sigma_sum H H0 H2).
    replace (S (n-1)%nat) with n by lia; intros.
    cut_to H11; [|lia].
    specialize (H3 (S Nsigma) (n-1)%nat).
    cut_to H3; try lia.
    rewrite Rabs_pos_eq in H3; [|apply nneg_sum_n_m_sq ].
    specialize (H4 (n - 1)%nat).
    rewrite Rminus_0_r in H4.
    assert (0 < max_prod_fun (pos_sq_fun F) (S Nsigma) (n - 1)).

    + generalize (max_prod_index_n (pos_sq_fun F) (S Nsigma) (n-1)%nat); intros.
      destruct H12 as [k H12]; [lia|]; destruct H12.
      rewrite <- H13.
      apply pos_part_prod_n.
    + rewrite Rabs_pos_eq in H4; [|left; apply H12].
      apply Rmult_lt_compat_l with (r := sigma_V0_2) in H4; trivial; try lia.
      rewrite Heqpart_prod_eps in H4.
      replace (sigma_V0_2 * (eps / 2 / sigma_V0_2)) with (eps/2) in H4; [|now field_simplify].
      rewrite Rplus_comm in Heqsigma_V0_2.
      rewrite <- Heqsigma_V0_2 in H11.
      unfold part_prod_pos, pos in H4.
      rewrite Heqhalf_eps_div_A in H3; simpl in H3.
      apply Rmult_lt_compat_r with (r := A) in H3; [|apply cond_pos].
      replace (eps / ( 2 * A) * A) with (eps / 2) in H3; 
        [|field_simplify;trivial; apply Rgt_not_eq; apply cond_pos].
      generalize (Rplus_lt_compat _ _ _ _ H3 H4); intros.
      replace (eps/2 + eps/2) with (eps) in H13 by lra.
      apply (Rle_lt_trans  _ _ _ H11 H13).
Qed.

Theorem Dvoretzky4B (F : nat -> posreal) (sigma V: nat -> R) :
  (forall n, F n <= 1) ->
  (forall (n:nat), Rsqr (V (S n)) <= (pos_sq_fun F) n * Rsqr (V n) + Rsqr (sigma n)) ->
  is_lim_seq (part_prod F) 0 ->
  ex_series (fun n => Rsqr (sigma n)) ->   
  is_lim_seq (fun n => Rsqr (V n)) 0.
Proof.
  intros.
  apply Dvoretzky4_A with (F := F) (sigma := sigma) (A := mkposreal _ Rlt_0_1); trivial.
  intros; apply prod_sq_bounded_1; trivial.
Qed.  

Section Generalized_Harmonic_Series.

Lemma inv_bound_gt (a b : posreal) :
  / a  > / (a + b).
Proof.
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat.
    + apply cond_pos.
    + apply Rplus_lt_0_compat; apply cond_pos.
  - replace (pos a) with (a + 0) at 1 by lra.
    apply Rplus_lt_compat_l.
    apply cond_pos.
Qed.

Lemma inv_bound_sq_gt (a b : posreal) :
  Rsqr (/ a)  > Rsqr (/ (a + b)).
Proof.
  apply Rsqr_incrst_1.
  + apply inv_bound_gt.
  + left.
    apply Rinv_0_lt_compat.
    apply Rplus_lt_0_compat; apply cond_pos.    
  + left.
    apply Rinv_0_lt_compat; apply cond_pos.
Qed.

Lemma inv_bound_exists_lt  (a b : posreal) :
  exists (j : nat), forall (n:nat), / (a * (INR ((S n) + j))) < / (a * INR (S n) + b).
Proof.
  exists (Z.to_nat (up (b/a))).
  intros.
  generalize  (RealAdd.up_pos (b/a)); intros.
  cut_to H.
  apply Z.gt_lt in H.
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat.
    + apply Rplus_lt_0_compat; [| apply cond_pos].
      apply Rmult_lt_0_compat; [apply cond_pos | ].
      apply lt_0_INR; lia.
    + apply Rmult_lt_0_compat; [apply cond_pos | ].
      apply lt_0_INR; lia.
  - rewrite plus_INR.
    rewrite Rmult_plus_distr_l.
    apply Rplus_lt_compat_l.
    assert (b/a < IZR (up (b/a))) by apply archimed.
    rewrite INR_IZR_INZ.
    rewrite Z2Nat.id; trivial; [|lia].
    apply Rmult_lt_compat_l with (r:=a) in H0; [|apply cond_pos].
    replace (a * (b / a)) with (pos b) in H0.
    generalize (cond_pos a); intros.
    lra.
    field.
    apply  Rgt_not_eq, cond_pos.
  - unfold Rdiv.
    apply Rmult_gt_0_compat; [apply cond_pos|].
    apply Rinv_0_lt_compat; apply cond_pos.    
Qed.

Lemma genharmonic_series_sq (b c : posreal) :
  ex_series (fun n => Rsqr (/ (b + c * INR (S n)))).
Proof.
  apply (@ex_series_le R_AbsRing) with (b := fun n => Rsqr ( / (c * INR (S n)))).
  - intros.
    assert (0 < c * INR (S n)).    
    + apply Rmult_lt_0_compat; [apply cond_pos | ].
      apply lt_0_INR; lia.
    + rewrite Rabs_right.
      * left; apply Rgt_lt.
        rewrite Rplus_comm.
        generalize (inv_bound_sq_gt (mkposreal _ H) b); intros.
        apply H0.
      * apply Rle_ge.
        apply Rle_0_sqr.
  - generalize sum_inv_sqr_bounded; intros.
    unfold ex_finite_lim_seq in H.
    destruct H.
    apply (ex_series_ext (fun n => Rsqr (/ c) * Rsqr (/ INR (S n)))).
    + intros.
      rewrite Rinv_mult_distr.
      * now rewrite Rsqr_mult.
      * apply Rgt_not_eq; apply cond_pos.
      * apply Rgt_not_eq.
        apply RealAdd.INR_zero_lt; lia.
    + apply (@ex_series_scal R_AbsRing).
      unfold ex_series.
      exists x.
      apply is_series_Reals.
      apply infinite_sum_is_lim_seq.
      apply (is_lim_seq_ext (fun n : nat => sum_f_R0 (fun i : nat => 1 / (INR i + 1)²) n)); trivial; intros.
      apply sum_f_R0_ext; intros.
      unfold Rdiv.
      rewrite  Rmult_1_l.
      rewrite Rsqr_inv.
      * now rewrite S_INR.
      * apply not_0_INR; lia.
Qed.

Lemma genharmonic_sq_lim (b c : posreal) :
  is_lim_seq (fun n => Rsqr (/ (b + c * INR (S n)))) 0.
Proof.  
  apply ex_series_lim_0.
  apply genharmonic_series_sq.
Qed.

Lemma harmonic_increasing :
  let f := fun i => sum_f_R0' (fun n => 1 / INR (S n)) i in
  forall n m : nat, (n <= m)%nat -> f n <= f m.
Proof.
  intros.
  subst f.
  simpl.
  replace (m) with (n + (m-n))%nat by lia.
  rewrite sum_f_R0'_plus_n.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat_l.
  induction (m-n)%nat.
  - simpl; lra.
  - simpl.
    apply Rplus_le_le_0_compat; trivial.
    unfold Rdiv.
    rewrite Rmult_1_l.
    left.
    apply Rinv_0_lt_compat.
    destruct (n + n0)%nat.
    + lra.
    + rewrite <- S_INR.
      apply lt_0_INR; lia.
Qed.
  
Lemma harmonic_series :
  is_lim_seq (fun i => sum_f_R0' (fun n => 1 / INR (S n)) i) p_infty.
Proof.
  apply is_lim_seq_spec.
  intro.
  unfold eventually.
  generalize (sum_f_R0'_bound2 (Z.to_nat (up (2 * (Rabs M))))); intros.
  exists (2 ^ Z.to_nat (up (2 * (Rabs M))))%nat.
  intros.
  assert (IZR (up (2 * Rabs M)) > 2*Rabs M) by apply archimed.
  assert (1 + INR (Z.to_nat (up (2 * (Rabs M)))) / 2 > Rabs M).
  rewrite RealAdd.INR_up_pos.
  lra.
  assert (0 <= Rabs M) by apply Rabs_pos; lra.
  generalize (harmonic_increasing (2 ^ Z.to_nat (up (2 * Rabs M))) n H0).
  intros.
  generalize (Rle_abs M); intros.
  lra.
Qed.

Lemma harmonic_series2 (c:posreal) :
  is_lim_seq (fun i => sum_f_R0' (fun n =>  1 / (c * INR (S n))) i) p_infty.
Proof.
  generalize (cond_pos c); intros cpos.
  generalize harmonic_series; intros.
  apply is_lim_seq_scal_l with (a := /c) in H.
  replace (Rbar_mult (/c) p_infty) with p_infty in H.
  - apply (is_lim_seq_ext (fun n : nat => /c * sum_f_R0' (fun n0 : nat => 1 / INR (S n0)) n)); intros; trivial.
    rewrite <- sum_f_R0'_mult_const.
    apply sum_f_R0'_ext.
    intros.
    unfold Rdiv.
    do 2 rewrite Rmult_1_l.
    rewrite Rinv_mult_distr; trivial.
    lra.
    apply not_0_INR; lia.
  - rewrite Rbar_mult_comm; symmetry.
    apply is_Rbar_mult_unique.
    apply is_Rbar_mult_p_infty_pos.
    apply Rinv_0_lt_compat; apply cond_pos.
Qed.

Lemma harmonic_series3 (j:nat) (f : nat -> R) :
  is_lim_seq (fun i => sum_f_R0' f i) p_infty ->
  is_lim_seq (fun i => sum_f_R0' (fun n => f (n + j)%nat) i) p_infty.
Proof.
  intros.
  apply (is_lim_seq_incr_n _ j) in H.
  apply is_lim_seq_minus with (v := fun _ => sum_f_R0' f j) (l2 := sum_f_R0' f j) (l1 := p_infty) (l := p_infty) in H.
  - apply (is_lim_seq_ext  (fun n : nat => sum_f_R0' f (n + j) - sum_f_R0' f j)); trivial.
    intros.
    rewrite sum_f_R0'_split with (m := j); [|lia].
    replace (n+j-j)%nat with n by lia.
    lra.
  - apply is_lim_seq_const.
  - unfold is_Rbar_minus, is_Rbar_plus.
    now simpl.
Qed.

Lemma genharmon (a b : posreal) :
  forall (n:nat), / ((a+b)*(INR (S n))) <= /(a*(INR (S n)) + b) < /(a * (INR (S n))).
Proof.
  intros.
  split.
  - apply Rinv_le_contravar.
    + apply Rplus_lt_0_compat; [ | apply cond_pos].
      apply Rmult_lt_0_compat; [apply cond_pos | ].
      apply lt_0_INR; lia.
    + rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat_l.
      replace (pos b) with (b * 1) at 1 by lra.
      apply Rmult_le_compat_l; [left;apply cond_pos | ].
      rewrite S_O_plus_INR.
      replace 1 with (1 + 0) by lra.
      apply Rplus_le_compat_l.
      apply pos_INR.
  - assert (0 < a * INR (S n)).
    + apply Rmult_lt_0_compat; [apply cond_pos | ].
      apply lt_0_INR; lia.
    + apply Rinv_lt_contravar.
      * apply Rmult_lt_0_compat; trivial.
        apply Rplus_lt_0_compat; [trivial | apply cond_pos].
      * replace (a * INR (S n)) with (a * INR (S n) + 0) at 1 by lra.
        apply Rplus_lt_compat_l; apply cond_pos.
Qed.

Lemma genharmon_sq (a b : posreal) :
  forall (n:nat), 
    Rsqr (/ ((a+b)*(INR (S n)))) <= Rsqr (/ (a*(INR (S n)) + b)) < Rsqr (/ (a * (INR (S n)))).
Proof.
  intros.
  generalize (genharmon a b n); intros.
  destruct H.
  assert (0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (0 < (a + b) * INR (S n)).
  - apply Rmult_lt_0_compat; trivial.
    apply Rplus_lt_0_compat; apply cond_pos.
  - assert (0 < a * INR (S n) + b).
    + apply Rplus_lt_0_compat; [ | apply cond_pos].
      apply Rmult_lt_0_compat; [apply cond_pos| trivial].
    + split.
      * apply Rsqr_incr_1; trivial.
        -- left; apply Rinv_0_lt_compat; trivial.
        -- left; apply Rinv_0_lt_compat; trivial.        
      * apply Rsqr_incrst_1; trivial.
        -- left; apply Rinv_0_lt_compat; trivial.
        -- left; apply Rinv_0_lt_compat.
           apply Rmult_lt_0_compat; [apply cond_pos | trivial].
Qed.

Lemma genharmonic_series (b c : posreal) :
  is_lim_seq (fun i => sum_f_R0' (fun n => 1 / (b + c * INR (S n))) i) p_infty.
Proof.
  generalize (cond_pos c); intros cpos.
  generalize (inv_bound_exists_lt c b); intros.
  destruct H as [j H].
  unfold is_lim_seq.
  apply filterlim_ge_p_infty with (f := fun n : nat => sum_f_R0' (fun n0 : nat => 1 / (c *INR (S (n0) + j))) n).
  unfold eventually;  exists (0%nat); intros.
  apply sum_f_R0'_le_f.
  intros.
  unfold Rdiv; do 2 rewrite Rmult_1_l.
  rewrite Rplus_comm; left; apply H.
  generalize (harmonic_series2 c); intros.
  generalize (harmonic_series3 j (fun n => 1 / (c * INR (S n))) H0); trivial.
Qed.
  
Lemma genharmonic_series2 (b c : posreal) :
  is_lim_seq (fun i => sum_f_R0' (fun n => 1 / (b + c * INR (S n))) i) p_infty.
Proof.
  generalize (genharmon c b); intros.
  assert (0 < c + b).
  apply Rplus_lt_0_compat; apply cond_pos.
  generalize (harmonic_series2 (mkposreal _ H0)); intros.
  unfold is_lim_seq in *.
  apply filterlim_ge_p_infty
    with (f := (fun i : nat =>
          sum_f_R0' (fun n : nat => 1 / ({| pos := c + b; cond_pos := H0 |} * INR (S n))) i)); trivial.
  unfold eventually;  exists (0%nat); intros.
  apply sum_f_R0'_le_f.
  intros.
  specialize (H i); destruct H.
  unfold Rdiv.
  do 2 rewrite Rmult_1_l.
  replace (b + c * INR (S i)) with (c * INR (S i) + b) by lra.
  apply H.
Qed.  

End Generalized_Harmonic_Series.

Lemma Robbins_Monro_0 (u : R) (a : nat -> posreal) (g : R -> R) (A B : posreal) :
  (forall (u:R), u <> 0 -> A <= g u <= B) ->
  forall (n:nat), 
    (u <> 0) ->
    Rabs (1 - a n * g u) <= Rmax (1-A*(a n)) (B*(a n) - 1).
Proof.
  intros.
  specialize (H u H0).
  destruct H.
  replace (B*(a n) - 1) with (- (1 - B*a n)) by lra.
  apply Rcomplements.Rabs_le_between_Rmax; unfold Rminus.
  split; apply Rplus_le_compat_l, Ropp_le_contravar; rewrite Rmult_comm.
  - apply Rmult_le_compat_r; trivial.    
    left; apply cond_pos.
  - apply Rmult_le_compat_l; trivial.
    left; apply cond_pos.
Qed.

Lemma Robbins_Monro_1 (r : nat -> R) (a : nat -> posreal) (f : R -> R) (A B : posreal) :
  (forall (u:R), u <> 0 -> A <= f(u)/u <= B) ->
  forall (n:nat), r n <> 0 -> Rabs (r n - a n * f (r n)) <= Rabs (r n) * Rmax (1-A*(a n)) (B*(a n) - 1).
Proof.
  intros.
  replace (r n - a n * f (r n)) with ((r n)*(1 - a n * (f(r n)/(r n)))).
  - rewrite Rabs_mult.
    apply Rmult_le_compat_l; [apply Rabs_pos | ].
    apply Robbins_Monro_0 with (g := fun u => f u / u); trivial.
  - now field.    
Qed.    

Lemma Robbins_Monro_1b (a A B : posreal) :
  a < 2/(A + B) -> Rmax (1-A*a) (B*a-1) = 1-A*a.
Proof.
  intros.
  assert (0 < A + B).
  apply Rplus_lt_0_compat; apply cond_pos.
  apply Rmax_left; left.
  unfold Rdiv in H.
  replace (pos a) with (a * (A + B) * / (A + B)) in H.
  - apply Rmult_lt_reg_r in H; [lra | ].
    now apply Rinv_0_lt_compat.
  - field.
    now apply Rgt_not_eq.
Qed.

Lemma is_derive_Rsqr (f : R -> R) (x df : R) :
  is_derive f x df -> is_derive (fun x0 => Rsqr (f x0)) x (2 * (f x) * df).
Proof.
  intros.
  apply (is_derive_ext (fun x0 => (f x0) * (f x0))); [now unfold Rsqr |].
  replace (2 * f x * df) with ((df * f x) + (f x * df)) by lra.
  apply (@is_derive_mult R_AbsRing); trivial.
  apply Rmult_comm.
Qed.

Lemma Robbins_Monro_2a (A sigma : posreal) (a0 V : R) :
  let f := fun a => (Rsqr (1-A*a) * (Rsqr V)) + (Rsqr a * (Rsqr sigma)) in
  is_derive f a0 ((2 * (1-A*a0) * (-A) * (Rsqr V)) + (2 * a0 * (Rsqr sigma))).
Proof.
  intros.
  apply (@is_derive_plus R_AbsRing).
  - apply (@is_derive_scal_l R_AbsRing).
    apply (is_derive_Rsqr (fun x => (1 - A * x))).
    replace (-A) with (0 - A) by lra.
    apply (@is_derive_minus R_AbsRing).
    + apply (@is_derive_const R_AbsRing).
    + replace (pos A) with (A*1) at 2 by lra.
      apply is_derive_scal.
      apply (@is_derive_id R_AbsRing).
  - apply (@is_derive_scal_l R_AbsRing).
    replace (2 * a0) with (2 * a0 * 1) by lra.
    apply is_derive_Rsqr.
    apply (@is_derive_id R_AbsRing).
Qed.
    
Lemma Robbins_Monro_2b (A sigma : posreal) (V : R) :
  let a0 := (A * V^2) / (sigma^2 + A^2 * V^2) in
  (2 * (1-A*a0) * (-A) * (Rsqr V)) + (2 * a0 * (Rsqr sigma)) = 0.
Proof.
  intros.
  subst a0; unfold Rsqr.
  field.
  apply Rgt_not_eq.
  apply Rlt_gt.
  generalize (cond_pos sigma); intros.
  apply Rplus_lt_le_0_compat.
  - apply Rmult_lt_0_compat; [apply cond_pos | ].
    rewrite Rmult_1_r; apply cond_pos.
  - replace ((A * V)^2) with (Rsqr (A*V)) by (unfold Rsqr; lra).
    apply Rle_0_sqr.
Qed.

Lemma Robbins_Monro_2c (A sigma : posreal) (V x : R) :
  let f := fun a => (Rsqr (1-A*a) * (Rsqr V)) + (Rsqr a * (Rsqr sigma)) in
  let a0 := (A * V^2) / (sigma^2 + A^2 * V^2) in
  is_derive f a0 0.
Proof.
  intros.
  subst f.
  generalize (Robbins_Monro_2a A sigma a0 V); intros.
  simpl in H; subst a0.
  now rewrite (Robbins_Monro_2b A sigma V) in H.
Qed.

Lemma Robbins_Monro_2d (A sigma : posreal) (V x : R) :
  let f := fun a => (Rsqr (1-A*a) * (Rsqr V)) + (Rsqr a * (Rsqr sigma)) in
  let a0 := (A * V^2) / (sigma^2 + A^2 * V^2) in
  f a0 = sigma^2 * V^2 / (sigma^2 + (A*V)^2).
Proof.
  intros.
  subst f; subst a0; simpl.
  unfold Rsqr.
  field.
  apply Rgt_not_eq.
  apply Rlt_gt.
  apply Rplus_lt_le_0_compat.
  - apply Rmult_lt_0_compat; apply cond_pos.
  - replace (A * V * (A * V)) with (Rsqr (A * V)) by (unfold Rsqr; lra).
    apply Rle_0_sqr.
Qed.  
  

End Dvoretsky.
