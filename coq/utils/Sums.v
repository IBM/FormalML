Require Import Coquelicot.Coquelicot.
Set Bullet Behavior "Strict Subproofs".

Require Import Program.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import List.
Require Import EquivDec Nat Lia Lra.

Require Import LibUtils ListAdd RealAdd.
Import ListNotations.

Local Open Scope R.
(* The standard library defines sum_f_R0 as an inclusive sum from 0.
   It then defines infinite_sum in terms of it.
   
   Inclusive ranges are much harder to reason about formulate lemmas than exclusive (end) ranges,       
   since they don't allow for empty ranges.

   infinite summations don't really care, so we formulate the nicer version here,
   along with an alternative infinite_sum that is proven identical to the original
 *)

Section sum'.
  Fixpoint sum_f_R0' (f : nat -> R) (N : nat) {struct N} : R :=
    match N with
    | 0%nat => 0%R
    | S i => sum_f_R0' f i + f i
    end.

  Lemma sum_f_R0_sum_f_R0' f N :
    sum_f_R0 f N = sum_f_R0' f (S N).
  Proof.
    induction N; simpl.
    - lra.
    - rewrite IHN.
      simpl; trivial.
  Qed.

  Lemma sum_f_R0'_ext (f1 f2:nat->R) n :
    (forall x, (x < n)%nat -> f1 x = f2 x) ->
    sum_f_R0' f1 n = sum_f_R0' f2 n.
  Proof.
    intros eqq.
    induction n; simpl.
    - trivial. 
    - rewrite eqq by lia.
      rewrite IHn; trivial.
      intros; apply eqq.
      lia.
  Qed.

  Lemma sum_f_R0'_split f n m :
    (m <= n)%nat ->
    sum_f_R0' f n =
    sum_f_R0' f m +
    sum_f_R0' (fun x => f (x+m)%nat) (n-m).
  Proof.
    intros lem.
    induction n; simpl.
    - assert (m = 0)%nat by lia.
      subst; simpl; lra.
    - destruct (m == S n); unfold equiv, complement in *.
      + subst.
        simpl.
        rewrite Rplus_assoc.
        f_equal.
        replace (n - n)%nat with 0%nat by lia.
        simpl.
        lra.
      + rewrite IHn by lia.
        rewrite Rplus_assoc.
        f_equal.
        destruct m; simpl.
        * replace (n-0)%nat with n by lia.
          replace (n+0)%nat with n by lia.
          trivial.
        * replace (n - m)%nat with (S (n - S m))%nat by lia.
          simpl.
          f_equal.
          f_equal.
          lia.
  Qed.

  Lemma sum_f_R0'_split_on f n m :
    (m < n)%nat ->
    sum_f_R0' f n =
    sum_f_R0' f m +
    f m + 
    sum_f_R0' (fun x => f (x+S m)%nat) (n- S m).
  Proof.
    intros ltm.
    rewrite (sum_f_R0'_split f n (S m) ltm).
    simpl; trivial.
  Qed.

  Lemma sum_f_R0_peel f n :
    sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
  Proof.
    simpl; trivial.
  Qed.

  Lemma sum_f_R0_ext (f1 f2:nat->R) n :
    (forall x, (x <= n)%nat -> f1 x = f2 x) ->
    sum_f_R0 f1 n = sum_f_R0 f2 n.
  Proof.
    intros eqq.
    induction n; simpl.
    - apply eqq; lia.
    - rewrite eqq by lia.
      rewrite IHn; trivial.
      intros; apply eqq.
      lia.
  Qed.

  Lemma sum_f_R0_split f n m:
    (m < n)%nat ->
    sum_f_R0 f n =
    sum_f_R0 f m +
    sum_f_R0 (fun x => f (x+S m))%nat (n-S m).
  Proof.
    intros ltm.
    induction n; simpl.
    - lia.
    - destruct (m == n); unfold equiv, complement in *.
      + subst.
        rewrite Nat.sub_diag; simpl; trivial.
      + rewrite IHn by lia.
        rewrite Rplus_assoc.
        f_equal.
        replace (n - m)%nat with (S (n - S m))%nat by lia.
        simpl.
        f_equal.
        f_equal.
        lia.
  Qed.

  Lemma sum_f_R0_split_on f n m:
    (S m < n)%nat ->
    sum_f_R0 f n =
    sum_f_R0 f m +
    f (S m) + 
    sum_f_R0 (fun x => f (x+S (S m)))%nat (n-S (S m)).
  Proof.
    intros ltm.
    rewrite (sum_f_R0_split f n m) by lia.
    repeat rewrite Rplus_assoc.
    f_equal.
    rewrite (sum_f_R0_split  (fun x : nat => f (x + S m)%nat) (n - S m) 0) by lia.
    simpl.
    f_equal.
    replace (n - S (S m))%nat with (n - S m - 1)%nat by lia.
    apply sum_f_R0_ext.
    intros.
    f_equal.
    lia.
  Qed.

  Lemma sum_f_R0'_chisel f N n :
  (n < N)%nat ->
  sum_f_R0' f N = sum_f_R0'  (fun x : nat => if equiv_dec x n then 0 else f x) N + (f n).
Proof.
  Proof.
    intros ltm.
    repeat rewrite (sum_f_R0'_split_on _ N n ltm).
    destruct (n == n); unfold equiv, complement in *; subst; [| intuition].
    rewrite Rplus_0_r.
    rewrite Rplus_comm.
    repeat rewrite <- Rplus_assoc.
    f_equal.
    rewrite Rplus_comm.
    f_equal.
    + apply sum_f_R0'_ext; intros.
      destruct (x == n);  unfold equiv, complement in *; subst; [| intuition].
      lia.
    + apply sum_f_R0'_ext; intros.
      destruct (x + S n == n)%nat;  unfold equiv, complement in *; subst; [| intuition].
      lia.
  Qed.

  Lemma sum_f_R0'_const c n: sum_f_R0' (fun _ : nat => c) n = (c * INR n)%R.
  Proof.
    induction n; simpl.
    - lra.
    - rewrite IHn.
      destruct n; simpl; lra.
  Qed.

    
  Lemma sum_f'_as_fold_right f (n:nat) s :
    sum_f_R0' (fun x : nat => f (x + s)%nat) n = fold_right (fun a b => f a + b) 0 (seq s n).
  Proof.
    revert s.
    induction n; simpl; trivial.
    intros.
    rewrite (IHn s).
    destruct n; [simpl; lra | ].
    replace (seq s (S n)) with ([s]++seq (S s) n) by (simpl; trivial).
    rewrite seq_Sn.
    repeat rewrite fold_right_app.
    simpl.
    rewrite (fold_right_plus_acc _ (f (S (s + n)) + 0)).
    rewrite Rplus_assoc.
    f_equal.
    f_equal.
    rewrite Rplus_0_r.
    f_equal.
    lia.
  Qed.

  Lemma sum_f_R0'_as_fold_right f (n:nat) :
    sum_f_R0' f n = fold_right (fun a b => f a + b) 0 (seq 0 n).
  Proof.
    generalize (sum_f'_as_fold_right f n 0); simpl; intros HH.
    rewrite <- HH.
    apply sum_f_R0'_ext.
    intros.
    f_equal.
    lia.
  Qed.

  Lemma sum_f_R0'_plus f1 f2 n :
    sum_f_R0' (fun x => f1 x + f2 x) n = sum_f_R0' f1 n + sum_f_R0' f2 n.
  Proof.
    induction n; simpl; [lra | ].
    rewrite IHn.
    lra.
  Qed.

  Lemma sum_f_R0'_mult_const f1 n c :
    sum_f_R0' (fun x => c * f1 x) n = c * sum_f_R0' f1 n.
  Proof.
    induction n; simpl; [lra | ].
    rewrite IHn.
    lra.
  Qed.

  Lemma sum_f_R0'_le f n :
    (forall n, (0 <= f n)) ->
    0 <= sum_f_R0' f n.
  Proof.
    intros fpos.
    induction n; simpl.
    - lra.
    - specialize (fpos n).
      lra.
  Qed.

  Lemma sum_f_R0'_plus_n f n1 n2 : sum_f_R0' f (n1 + n2) =
                                   sum_f_R0' f n1 +
                                   sum_f_R0' (fun x => f (n1+x))%nat n2.
  Proof.
    repeat rewrite sum_f_R0'_as_fold_right.
    rewrite seq_plus.
    rewrite fold_right_app.
    rewrite fold_right_plus_acc.
    simpl.
    rewrite (seq_shiftn_map n1).
    rewrite fold_right_map.
    trivial.
  Qed.

  Lemma sum_f_R0'_le_f (f g:nat->R) n :
    (forall i, (i < n)%nat -> f i <= g i) ->
    sum_f_R0' f n <= sum_f_R0' g n.
  Proof.
    induction n; simpl.
    - lra.
    - intros fa.
      apply Rplus_le_compat; auto.
  Qed.        

End sum'.

Section inf_sum'.

  Definition infinite_sum' (s : nat -> R) (l : R) : Prop
    := forall eps : R,
      eps > 0 ->
      exists N : nat,
        forall n : nat,
          (n >= N)%nat ->
          R_dist (sum_f_R0' s n) l < eps.

  Theorem infinite_sum_infinite_sum' (s : nat -> R) (l : R) :
    infinite_sum s l <-> infinite_sum' s l.
  Proof.
    unfold infinite_sum, infinite_sum'.
    split; intros H.
    - intros eps epsgt.
      destruct (H eps epsgt) as [N Nconv].
      exists (S N); intros n ngt.
      destruct n.
      + lia.
      + rewrite <- sum_f_R0_sum_f_R0'.
        apply Nconv.
        lia.
    - intros eps epsgt.
      destruct (H eps epsgt) as [N Nconv].
      exists N; intros n ngt.
      rewrite sum_f_R0_sum_f_R0'.
      apply Nconv.
      lia.
  Qed.

  Lemma infinite_sum'_ext (s1 s2 : nat -> R) (l : R) :
    (forall x, s1 x = s2 x) ->
    infinite_sum' s1 l <-> infinite_sum' s2 l.
  Proof.
    intros eqq.
    unfold infinite_sum'.
    split; intros H eps eps_gt
    ; destruct (H eps eps_gt) as [N Nconv]
    ; exists N; intros n0 n0_ge
    ; specialize (Nconv n0 n0_ge)
    ; erewrite sum_f_R0'_ext; eauto.
  Qed.    
    

  Lemma infinite_sum'_prefix s l n :
    infinite_sum' s (l + (sum_f_R0' s n)) <->
    infinite_sum' (fun x => s (x + n))%nat l.
  Proof.
    unfold infinite_sum'.
    split; intros H
    ; intros eps eps_gt
    ; specialize (H eps eps_gt)
    ; destruct H as [N Nconv].
    - exists N
      ; intros n0 n0_ge.
      specialize (Nconv (n + n0)%nat).
      cut_to Nconv; [ | lia].
      replace (R_dist (sum_f_R0' (fun x : nat => s (x + n)%nat) n0) l) with
            ( R_dist (sum_f_R0' s (n + n0)) (l + sum_f_R0' s n)); trivial.
      unfold R_dist.
      rewrite (sum_f_R0'_split s (n+n0) n) by lia.
      replace ((n + n0 - n)%nat) with n0 by lia.
      f_equal.
      lra.
    - exists (N+n)%nat
      ; intros n0 n0_ge.
      specialize (Nconv (n0-n)%nat).
      cut_to Nconv; [ | lia].
      replace (R_dist (sum_f_R0' s n0) (l + sum_f_R0' s n))
                      with (R_dist (sum_f_R0' (fun x : nat => s (x + n)%nat) (n0 - n)) l); trivial.
      unfold R_dist.
      rewrite (sum_f_R0'_split s n0 n) by lia.
      f_equal.
      lra.
  Qed.
    
    Lemma infinite_sum'_split n s l :
      infinite_sum' s l <->
      infinite_sum' (fun x => s (x + n))%nat (l - (sum_f_R0' s n)).
    Proof.
      rewrite <- (infinite_sum'_prefix s (l - (sum_f_R0' s n)) n).
      replace (l - sum_f_R0' s n + sum_f_R0' s n) with l by lra.
      tauto.
    Qed.

    (*
    Lemma infinite_sum'_unique_half f l1 l2 :
      infinite_sum' f l1 ->
      infinite_sum' f l2 ->
      l2 <= l1 ->
      l1 = l2.
    Proof.
      unfold infinite_sum'; intros inf1 inf2 le.
      destruct (Req_dec (l1 - l2) 0); [lra | ].
      assert (gt0:(l1 - l2) / 2 > 0) by lra.
      specialize (inf1 _ gt0).
      destruct inf1 as [N1 inf1].
      specialize (inf2 _ gt0).
      destruct inf2 as [N2 inf2].
      specialize (inf1 (max N1 N2)).
      specialize (inf2 (max N1 N2)).

      l2 - x < (l1 - l2) / 2
                         l1 - x < (l1 - l2) / 2k
      
     *)

    Lemma R_dist_too_small_impossible_lt r l1 l2 :
      l1 < l2 ->
      R_dist r l1 < R_dist l1 l2 / 2 ->
      R_dist r l2 < R_dist l1 l2 / 2 -> False.
    Proof.
      intros ltl inf1 inf2.
      generalize (Rplus_lt_compat _ _ _ _ inf1 inf2); intros ltt.
      replace (R_dist l1 l2 / 2 + R_dist l1 l2 / 2) with (R_dist l1 l2) in ltt by lra.
      rewrite (R_dist_sym r l1) in ltt.
      generalize (R_dist_tri l1 l2 r); intros.
      lra.
    Qed.
             
    Lemma R_dist_too_small_impossible_neq r l1 l2 :
      l1 <> l2 ->
      R_dist r l1 < R_dist l1 l2 / 2 ->
      R_dist r l2 < R_dist l1 l2 / 2 -> False.
    Proof.
      intros neq inf1 inf2.
      destruct (Rlt_le_dec l1 l2).
      - eapply R_dist_too_small_impossible_lt; eauto.
      - destruct r0.
        + rewrite (R_dist_sym l1 l2) in * .
          eapply R_dist_too_small_impossible_lt; eauto.
        + intuition.
    Qed.
                                                     
    Lemma infinite_sum'_unique {f l1 l2} :
      infinite_sum' f l1 ->
      infinite_sum' f l2 ->
      l1 = l2.
    Proof.
      unfold infinite_sum'; intros inf1 inf2.
      destruct (Req_dec (l1 - l2) 0); [lra | ].
      generalize (Rabs_pos_lt _ H); intros gt0.
      apply Rlt_gt in gt0.
      assert (gt02:R_dist l1  l2 / 2 > 0) by (unfold R_dist; lra).
      specialize (inf1 _ gt02).
      specialize (inf2 _ gt02).
      destruct inf1 as [N1 inf1].
      destruct inf2 as [N2 inf2].
      specialize (inf1 (max N1 N2)).
      specialize (inf2 (max N1 N2)).
      cut_to inf1; [ | apply Nat.le_max_l].
      cut_to inf2; [ | apply Nat.le_max_r].
      revert inf1 inf2.
      generalize (sum_f_R0' f (max N1 N2)); intros.
      eelim R_dist_too_small_impossible_neq; try eapply inf1; eauto.
      lra.
    Qed.

    Lemma infinite_sum'_const_shift {c d} :
      infinite_sum' (fun _ => c) d ->
      (infinite_sum' (fun _ => c) (d+c)).
    Proof.
      intros.
      apply (infinite_sum'_split 1  (fun _ => c) (d+c)).
      simpl.
      replace (d + c - (0 + c)) with d; trivial.
      lra.
    Qed.

    Lemma infinite_sum'_const0 {d} :
      infinite_sum' (fun _ : nat => 0) d ->
      d = 0.
    Proof.
      unfold infinite_sum'; intros HH.
      destruct (Req_dec d 0); trivial.
      assert (gt0:Rabs d/2>0).
      {
        generalize (Rabs_pos_lt d H).
        lra.
      }
      specialize (HH _ gt0).
      destruct HH as [N Nconv].
      specialize (Nconv N).
      cut_to Nconv; [ | left; trivial].
      rewrite sum_f_R0'_const in Nconv.
      unfold R_dist in Nconv.
      replace (0 * INR N - d) with (- d) in Nconv by lra.
      rewrite Rabs_Ropp in Nconv.
      lra.
    Qed.

    Lemma infinite_sum'_const1 {c d} :
      infinite_sum' (fun _ => c) d -> c = 0.
    Proof.
      intros inf1.
      generalize (infinite_sum'_const_shift inf1); intros inf2.
      generalize (infinite_sum'_unique inf1 inf2); intros eqq.
      lra.
    Qed.

    Lemma infinite_sum'_const {c d} :
      infinite_sum' (fun _ => c) d -> c = 0 /\ d = 0.
    Proof.
      intros inf1.
      generalize (infinite_sum'_const1 inf1); intros; subst.
      generalize (infinite_sum'_const0 inf1); intros; subst.
      tauto.
    Qed.

    Lemma infinite_sum'_const2 {c d} :
      infinite_sum' (fun _ => c) d -> d = 0.
    Proof.
      intros inf1.
      generalize (infinite_sum'_const inf1); tauto.
    Qed.

  Hint Resolve Nat.le_max_l Nat.le_max_r : arith.
    
  Lemma infinite_sum'_plus {f1 f2} {sum1 sum2} :
    infinite_sum' f1 sum1 ->
    infinite_sum' f2 sum2 ->
    infinite_sum' (fun x => f1 x + f2 x) (sum1 + sum2).
  Proof.
    intros inf1 inf2 ε εpos.
    destruct (inf1 (ε/2)) as [N1 H1]
    ; [lra | ].
    destruct (inf2 (ε/2)) as [N2 H2]
    ; [lra | ].

    exists (max N1 N2).
    intros n ngt.

    specialize (H1 n).
    cut_to H1; [ | apply (le_trans _ (max N1 N2)); auto with arith].
    specialize (H2 n).
    cut_to H2; [ | apply (le_trans _ (max N1 N2)); auto with arith].

    rewrite sum_f_R0'_plus.
    generalize (R_dist_plus (sum_f_R0' f1 n) sum1 (sum_f_R0' f2 n) sum2); intros.
    lra.
  Qed.

  Lemma infinite_sum'0 : infinite_sum' (fun _ : nat => 0) 0.
  Proof.
    intros ε εgt.
    exists 0%nat.
    intros.
    rewrite sum_f_R0'_const.
    replace (0 * INR n) with 0 by lra.
    rewrite R_dist_eq.
    lra.
  Qed.
        
  Lemma infinite_sum'_mult_const {f1} {sum1} c :
    infinite_sum' f1 sum1 ->
    infinite_sum' (fun x => c * f1 x) (c * sum1).
  Proof.
    intros inf1.
    destruct (Req_dec c 0).
    - subst.
      rewrite (infinite_sum'_ext _ (fun _ => 0)) by (intros; lra).
      replace (0 * sum1) with 0 by lra.
      apply infinite_sum'0.
    - intros ε εpos.
      assert (Rabs c > 0) by (apply Rabs_pos_lt; trivial).
      destruct (inf1 (ε/ (Rabs c))) as [N1 H1].
      + apply Rdiv_lt_0_compat; lra.
      + exists N1.
        intros n ngt.
        specialize (H1 n ngt).
        rewrite sum_f_R0'_mult_const.
        rewrite R_dist_mult_l.
        apply (Rmult_lt_compat_l (Rabs c)) in H1; [ | lra].
        replace ( Rabs c * (ε / Rabs c)) with ε in H1; trivial.
        unfold Rdiv.
        rewrite Rmult_comm.
        rewrite Rmult_assoc.
        rewrite (Rmult_comm (/ Rabs c)).
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_l; trivial.
        lra.
  Qed.
     
  Lemma Rabs_pos_plus_lt x y :
    x > 0 ->
    y > 0 ->
    y < Rabs (x + y).
  Proof.
    intros.
    rewrite Rabs_right; lra.
  Qed.

  Lemma infinite_sum'_pos f sum :
    infinite_sum' f sum ->
    (forall n, (0 <= f n)) ->
    0 <= sum.
  Proof.
    intros inf fpos.
    destruct (Rge_dec sum 0); [ lra | ].
    red in inf.
    apply Rnot_ge_lt in n.
    destruct (inf (- sum)); [ lra | ].
    specialize (H x).
    cut_to H; [ | lia].
    unfold R_dist in H.
    destruct (Req_dec (sum_f_R0' f x) 0).
    - rewrite H0 in H.
      replace (0 - sum) with (- sum) in H by lra.
      rewrite Rabs_right in H by lra.
      lra.
    - generalize (Rabs_pos_plus_lt (sum_f_R0' f x ) (- sum)); intros HH.
      cut_to HH.
      + eelim Rlt_irrefl.
        eapply Rlt_trans; eauto.
      + generalize (sum_f_R0'_le f x fpos); intros HH2.
        lra.
      + lra.
Qed.

  Lemma infinite_sum'_le f1 f2 sum1 sum2 :
    infinite_sum' f1 sum1 ->
    infinite_sum' f2 sum2 ->
    (forall n, (f1 n <= f2 n)) ->
    sum1 <= sum2.
  Proof.
    intros inf1 inf2 fle.

    generalize (infinite_sum'_mult_const (-1)%R inf1); intros ninf1.
    generalize (infinite_sum'_plus inf2 ninf1); intros infm.
    apply infinite_sum'_pos in infm.
    - lra.
    - intros.
      specialize (fle n).
      lra.
  Qed.    
  
End inf_sum'.

Section harmonic.

  Lemma pow_le1 n : (1 <= 2 ^ n)%nat.
  Proof.
    induction n; simpl; lia.
  Qed.

  Lemma Sle_mult_gt1 a n :
    (n > 0)%nat ->
    (a > 1)%nat ->
    (S n <= a * n)%nat.
  Proof.
    destruct a; lia.
  Qed.

  Lemma pow_exp_gt a b :
    (a > 1)%nat ->
    (a ^ b > b)%nat.
  Proof.
    intros neq.
    induction b; simpl.
    - lia.
    - apply gt_n_S in IHb.
      eapply le_gt_trans; try eassumption.
      apply Sle_mult_gt1; lia. 
  Qed.      
  Lemma sum_f_R0'_eq2 n :
    sum_f_R0' (fun _:nat => 1 / INR (2^(S n))) (2^n)%nat = 1/2.
  Proof.
    intros.
    rewrite sum_f_R0'_const.
    replace (2 ^ S n)%nat with (2 * 2 ^ n)%nat by reflexivity.
    rewrite mult_INR.
    unfold Rdiv.
    rewrite Rinv_mult_distr.
    - repeat rewrite Rmult_assoc.
      rewrite <- Rinv_l_sym.
      + simpl; lra.
      + apply INR_nzero_eq.
        apply Nat.pow_nonzero.
        lia.
    - simpl; lra.
    - apply INR_nzero_eq.
      apply Nat.pow_nonzero.
      lia.
  Qed.
  
  Lemma sum_f_R0'_bound2 (n:nat) : sum_f_R0' (fun i:nat => 1 / INR (S i)) (2^n)%nat >= 1+(INR n)/2.
  Proof.
    intros.
    induction n.
    - simpl; lra.
    - rewrite S_INR.
      simpl pow.
      rewrite sum_f_R0'_plus_n.
      replace ( 1 + (INR n + 1) / 2) with ( 1 + INR n / 2 + 1 / 2) by lra.
      apply Rplus_ge_compat; trivial.
      rewrite Nat.add_0_r.
      clear.
      eapply Rge_trans; [ | right; apply (sum_f_R0'_eq2 n)].
      apply Rle_ge.
      apply sum_f_R0'_le_f; intros.
      unfold Rdiv.
      apply Rmult_le_compat_l; [ lra | ].
      apply Rinv_le_contravar.
      + apply INR_zero_lt.
        lia.
      + apply le_INR.
        simpl.
        lia.
  Qed.

  Lemma harmonic_diverges' l : ~ infinite_sum' (fun i:nat => 1 / INR (S i)) l.
  Proof.
    intros inf.
    specialize (inf 1).
    cut_to inf; try lra.
    destruct inf as [N Npf].
    specialize (Npf (2^(2*(N + Z.to_nat (up l))))%nat).
    cut_to Npf.
    - generalize (sum_f_R0'_bound2 (2 * (N + Z.to_nat (up l)))); intros sle.
      rewrite mult_INR in sle.
      unfold Rdiv in sle.
      rewrite Rinv_r_simpl_m in sle by (simpl; lra).
      unfold R_dist in Npf.
      apply Rabs_def2 in Npf.
      destruct Npf as [Npf1 Npf2].
      assert (oops:INR (N + Z.to_nat (up l)) < l) by lra.
      rewrite plus_INR in oops.
      assert (lgt:l > 0).
      { eapply Rle_lt_trans; try eapply oops.
        apply Rplus_le_le_0_compat
        ; apply pos_INR.
      }
      rewrite INR_up_pos in oops by lra.
      destruct (archimed l).
      generalize (pos_INR N).
      lra.
    - rewrite Nat.pow_mul_r.
      simpl.
      rewrite NPeano.Nat.pow_add_r.
      unfold ge.
      replace N with (N * 1)%nat at 1 by lia.
      apply mult_le_compat.
      + generalize (pow_exp_gt 4 N)
        ; lia.
      + generalize (Z.to_nat (up l)); intros n.
        destruct n; simpl.
        * lia.
        * generalize (pow_exp_gt 4 n); lia.
  Qed.

  
  Definition diverges (f:nat->R)
    := forall l, ~ infinite_sum f l.
  
  Theorem harmonic_diverges : diverges (fun i:nat => 1 / INR (S i)).
  Proof.
    intros l inf.
    apply infinite_sum_infinite_sum' in inf.
    eapply harmonic_diverges'; eauto.
  Qed.

End harmonic.

Section coquelicot.
Lemma infinite_sum_is_lim_seq (f:nat->R) (l:R) : is_lim_seq (fun i => sum_f_R0 f i) l <-> infinite_sum f l.
Proof.
  split; intros HH.
  - apply Series.is_series_Reals.
    unfold Series.is_series.
    red in HH.
    eapply filterlim_ext; try eapply HH.
    intros; simpl.
    rewrite sum_n_Reals.
    reflexivity.
  - apply Series.is_series_Reals in HH.
    unfold Series.is_series in HH.
    red.
    eapply filterlim_ext; try eapply HH.
    intros; simpl.
    rewrite sum_n_Reals.
    reflexivity.
Qed.

Lemma is_lim_seq_list_sum (l:list (nat->R)) (l2:list R) :
  Forall2 is_lim_seq l (map Finite l2) ->
  is_lim_seq (fun n => list_sum (map (fun x => x n) l)) (list_sum l2).
Proof.
  intros F2.
  dependent induction F2.
  - destruct l2; simpl in x; try congruence.
    simpl.
    apply is_lim_seq_const.
  - destruct l2; simpl in x; try congruence.
    invcs x.
    specialize (IHF2 l2 (eq_refl _)).
    simpl.
    eapply is_lim_seq_plus; eauto.
    reflexivity.
Qed.

End coquelicot.

Lemma infinite_sum'_one f n l :
  (forall n', n' <> n -> f n' = 0%R) ->
  infinite_sum' f l <-> l = f n.
Proof.
  intros.
  rewrite (infinite_sum'_split (S n) f l).
  split; intros.
  - erewrite infinite_sum'_ext in H0.
    + apply infinite_sum'_const0 in H0.
      simpl in H0.
      erewrite sum_f_R0'_ext in H0.
      * rewrite (sum_f_R0'_const 0) in H0.
        lra.
      * intros; simpl.
        apply H; lia.
    + intros; simpl.
      apply H; lia.
  - subst.
    apply infinite_sum'_ext with (s1:=fun _ => 0%R).
    + intros; simpl.
      symmetry; apply H; lia.
    + replace (f n - sum_f_R0' f (S n))%R with  0%R.
      * apply infinite_sum'0.
      * simpl.
        erewrite sum_f_R0'_ext.
        rewrite (sum_f_R0'_const 0).
        -- lra.
        -- intros; simpl.
           apply H; lia.
Qed.
