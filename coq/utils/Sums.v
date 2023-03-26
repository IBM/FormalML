Require Import Coquelicot.Coquelicot.
Set Bullet Behavior "Strict Subproofs".
Require Import Morphisms.
Require Import Program.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import List.
Require Import EquivDec Nat Lia Lra.
Require Import Reals.R_sqrt.
Require Import PushNeg.
Require Import Reals.Sqrt_reg.

Require FinFun.

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

    Lemma sum_f_R0_le (f g : nat -> R) n :
      (forall (i:nat), (i<=n)%nat -> (f i) <= (g i)) ->
      sum_f_R0 f n <= sum_f_R0 g n.
    Proof.
      intros.
      induction n.
      - unfold sum_f_R0.
        simpl.
        apply H.
        lia.
      - do 2 rewrite sum_f_R0_peel.
        eapply Rle_trans.
        + apply Rplus_le_compat_r.
          apply IHn.
          intros.
          apply H.
          lia.
        + apply Rplus_le_compat_l.
          apply H.
          lia.
    Qed.

    Lemma sum_f_R0_nneg f N :
      (forall n, (n<=N)%nat -> 0 <= f n) ->
      0 <= sum_f_R0 f N.
    Proof.
      rewrite <- sum_n_Reals.
      apply sum_n_nneg.
    Qed.

   Lemma sum_f_R0_pos_incr f :
      (forall i, 0 <= f i) ->
      forall n : nat, sum_f_R0 f n <= sum_f_R0 f (S n).
     Proof.
       intros.
       simpl.
       rewrite <- Rplus_0_r at 1.
       now apply Rplus_le_compat_l.
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

  Lemma sum_f_R0_mult_const f1 n c :
    sum_f_R0 (fun x => c * f1 x) n = c * sum_f_R0 f1 n.
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

Lemma infinite_sum'_pos_prefix_le f l n:
  infinite_sum' f l ->
  (forall n, 0 <= f n) ->
  sum_f_R0' f n <= l.
Proof.
  intros.
  apply (infinite_sum'_split n f l) in H.
  apply infinite_sum'_pos in H.
  - lra.
  - auto.
Qed.

Lemma infinite_sum'_pos_one_le f l n:
  infinite_sum' f l ->
  (forall n, 0 <= f n) ->
  f n <= l.
Proof.
  intros.
  apply (infinite_sum'_pos_prefix_le _ _ (S n)) in H; trivial.
  simpl in H.
  generalize (sum_f_R0'_le f n H0).
  lra.
Qed.

Lemma sum_f_R0'_list_sum f n :
  sum_f_R0' f n = list_sum (map f (seq 0 n)).
Proof.
  now rewrite sum_f_R0'_as_fold_right, list_sum_fold_right, fold_right_map.
Qed.

Lemma list_sum_pos_sublist_le l1 l2 :
  (forall x, In x l2 -> 0 <= x) ->
  sublist l1 l2 ->
  list_sum l1 <= list_sum l2.
Proof.
  intros pos subl.
  induction subl.
  - lra.
  - simpl.
    apply Rplus_le_compat_l.
    apply IHsubl.
    simpl in *; eauto.
  - simpl.
    replace (list_sum l1) with (0 + list_sum l1) by lra.
    apply Rplus_le_compat.
    + simpl in *.
      eauto.
    + eapply IHsubl.
      simpl in *; eauto.
Qed.

Lemma list_sum_Rabs_triangle l :
  Rabs (list_sum l) <= list_sum (map Rabs l).
Proof.
  induction l; simpl.
  - rewrite Rabs_R0; lra.
  - eapply Rle_trans.
    + apply Rabs_triang.
    + lra.
Qed.

Lemma bijective_injective {B C} (f:B->C) : FinFun.Bijective f -> FinFun.Injective f.
Proof.
  intros [g [??]] ?? eqq.
  generalize (f_equal g eqq); intros eqq2.
  now repeat rewrite H in eqq2.
Qed.

(* proof based on 
       https://www.math.ucdavis.edu/~npgallup/m17_mat25/lecture_notes/lecture_15/m17_mat25_lecture_15_notes.pdf *)
Theorem infinite_sum'_perm (g:nat->nat) (f:nat -> R) l:
  FinFun.Bijective g ->
  (exists l2, infinite_sum' (fun x => Rabs (f x)) l2) ->
  infinite_sum' f l ->
  infinite_sum' (fun n => f (g n)) l.
Proof.
  intros bij fabs inf.
  
  assert (cc:Rseries.Cauchy_crit (sum_f_R0 (fun x => Rabs (f x)))).
  {
    destruct fabs as [? inf2].
    apply SeqProp.CV_Cauchy.
    rewrite <- infinite_sum_infinite_sum' in inf2.
    rewrite  <- infinite_sum_is_lim_seq in inf2.
    rewrite is_lim_seq_Reals in inf2.
    eauto.
  } 

  generalize bij; intros [ginv [ginvg gginv]].

  unfold infinite_sum' in *; intros eps eps_pos.
  assert (eps2_pos : eps / 2 > 0) by lra.
  destruct (inf _ eps2_pos) as [N1 N1_lt].
  destruct (cc _ eps2_pos) as [N2 N2_lt].
  pose (N := S (max N1 N2)).
  pose (M := S (List.list_max (map ginv (seq 0 N)))).
  pose (sN := sum_f_R0' f N).
  assert (MltN:(N <= M)%nat).
  {
    unfold M.
    generalize (NoDup_list_max_count (map ginv (seq 0 N)))
    ; intros HH.
    cut_to HH.
    - now rewrite map_length, seq_length in HH.
    - apply FinFun.Injective_map_NoDup.
      + intros ???.
        apply (f_equal g) in H.
        now repeat rewrite gginv in H.
      + apply seq_NoDup.
  }
  exists M; intros m mbig.
  unfold R_dist.
  replace (sum_f_R0' (fun n : nat => f (g n)) m - l)
    with ((sum_f_R0' (fun n : nat => f (g n)) m - sN) + (sN - l))
    by lra.
  eapply Rle_lt_trans.
  { eapply Rabs_triang. }
  apply (Rlt_le_trans _ (Rabs (sum_f_R0' (fun n : nat => f (g n)) m - sN) + eps / 2)).
  {
    apply Rplus_lt_compat_l.
    apply N1_lt.
    lia.
  }
  cut (Rabs (sum_f_R0' (fun n : nat => f (g n)) m - sN)   <= eps / 2); [lra|].
  
  unfold sN.
  repeat rewrite sum_f_R0'_list_sum.
  rewrite <- map_map.

  destruct (@incl_NoDup_sublist_perm _ _ (seq 0 N) (map g (seq 0 m)))
    as [gpre [gpre_perm gpre_subl]].
  {
    apply seq_NoDup.
  }
  {
    intros x xinn.
    apply in_seq in xinn.
    destruct xinn as [_ xlt].
    simpl in xlt.
    eapply in_map_iff.
    exists (ginv x).
    rewrite gginv.
    split; trivial.
    apply in_seq.
    split; [lia|].
    simpl.
    eapply lt_le_trans; try apply mbig.
    unfold M.
    unfold lt.
    generalize (list_max_upper (map ginv (seq 0 N))); intros FF.
    rewrite Forall_forall in FF.
    specialize (FF (ginv x)).
    cut_to FF.
    - lia.
    - apply in_map.
      apply in_seq; lia.
  } 
  rewrite gpre_perm.
  destruct (sublist_perm_head gpre_subl) as [l2 l2perm].
  rewrite <- l2perm.
  rewrite map_app.
  rewrite list_sum_cat.
  replace (list_sum (map f gpre) + list_sum (map f l2) - list_sum (map f gpre))
    with (list_sum (map f l2)) by lra.

  assert (ndgl:NoDup (gpre ++ l2)).
  {
    rewrite l2perm.
    apply FinFun.Injective_map_NoDup.
    - now apply bijective_injective.
    - apply seq_NoDup.
  }

  assert(l2_lower: (forall x, In x l2 -> x >= N)%nat).
  {
    intros.
    destruct (ge_dec x N); trivial.
    apply Compare_dec.not_ge in n.
    assert (inn:In x gpre).
    { 
      rewrite <- gpre_perm.
      apply in_seq.
      lia.
    }
    apply NoDup_app_disj in ndgl.
    elim (ndgl x inn H).
  } 
  pose (nn:=List.list_max l2).
  destruct (list_max_le l2 nn) as [l2_upper _].
  specialize (l2_upper (le_refl _)).
  assert (incl1:incl l2 (seq N (S nn-N))).
  {
    intros ? inn.
    apply in_seq.
    split.
    - now specialize (l2_lower _ inn).
    - rewrite Forall_forall in l2_upper.
      specialize (l2_upper _ inn).
      lia.
  }
  apply NoDup_app_inv2 in ndgl.
  destruct (incl_NoDup_sublist_perm ndgl incl1)
    as [l2' [perm2 subl2]].
  rewrite perm2.

  apply (Rle_trans _ (list_sum (map Rabs (map f l2')))).
  {
    apply list_sum_Rabs_triangle.
  } 

  destruct l2.
  {
    apply Permutation.Permutation_nil in perm2.
    subst; simpl.
    lra.
  } 
  
  eapply (Rle_trans _ (list_sum (map Rabs (map f (seq N (S nn - N)))))).
  { 
    eapply list_sum_pos_sublist_le.
    - intros.
      apply in_map_iff in H.
      destruct H as [?[??]]; subst.
      apply Rabs_pos.
    - now do 2 apply sublist_map.
  }

  assert (Nltnn:(N <= nn)%nat).
  {
    unfold nn.
    simpl.
    transitivity n.
    - simpl in *.
      specialize (l2_lower n).
      cut_to l2_lower; [| eauto].
      lia.
    - apply Nat.le_max_l.
  } 

  rewrite map_map.
  specialize (N2_lt nn (max N1 N2))%nat.
  cut_to N2_lt.
  - unfold R_dist in N2_lt.
    repeat rewrite sum_f_R0_sum_f_R0' in N2_lt.
    repeat rewrite sum_f_R0'_list_sum in N2_lt.
    replace (S nn) with (N + (S nn - N))%nat in N2_lt.
    + rewrite seq_app, map_app, list_sum_cat in N2_lt.
      replace (S (N - 1)) with N in N2_lt by lia.
      rewrite Rplus_minus_cancel1 in N2_lt.
      rewrite plus_O_n in N2_lt.
      rewrite Rabs_pos_eq in N2_lt.
      * lra.
      * apply list_sum_pos_pos'.
        rewrite Forall_forall; intros.
        apply in_map_iff in H.
        destruct H as [?[??]]; subst.
        apply Rabs_pos.
    + apply le_plus_minus_r.
      lia.
  - red.
    transitivity N; lia.
  - lia.
Qed.

Corollary infinite_sum'_pos_perm (g:nat->nat) (f:nat -> R) l:
  FinFun.Bijective g ->
  (forall x, 0 <= f x) ->
  infinite_sum' f l ->
  infinite_sum' (fun n => f (g n)) l.
Proof.
  intros.
  eapply infinite_sum'_perm; eauto.
  eexists.
  eapply infinite_sum'_ext; try eapply H1.
  intros.
  rewrite Rabs_pos_eq; auto.
Qed.

Lemma sum_f_R0_0_inv (a:nat->R) :
  (forall n : nat, sum_f_R0 a n = 0) ->
  forall n, a n = 0.
Proof.
  intros eqq.
  destruct n.
  - now specialize (eqq 0)%nat; simpl in eqq.
  - generalize (eqq n); intros eqq1.
    generalize (eqq (S n)); simpl; intros eqq2.
    lra.
Qed.


Section sum_n.


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

Lemma sum_n_m_le_loc_alt (a b : nat -> R) (j k : nat) :
  (forall n : nat, (j <= n <= j + k)%nat -> a n <= b n) ->
  sum_n_m a j (j + k)%nat <= sum_n_m b j (j + k)%nat.
Proof.
  intros.
  induction k.
  - replace (j + 0)%nat with (j) by lia.
    do 2 rewrite sum_n_n.
    apply H; lia.
  - replace (j + S k)%nat with (S (j + k))%nat by lia.
    rewrite sum_n_Sm; try lia.
    rewrite sum_n_Sm; try lia.
    assert (forall n : nat, (j <= n <= j + k)%nat -> a n <= b n).
    + intros.
      apply H; lia.
    + specialize (IHk H0).
      apply Rplus_le_compat; trivial.
      apply H; lia.
  Qed.

Lemma sum_n_m_le_loc (a b : nat -> R) (j k : nat) :
  (j <= k)%nat ->
  (forall n : nat, (j <= n <= k)%nat -> a n <= b n) ->
  sum_n_m a j k <= sum_n_m b j k.
Proof.
  intros.
  pose (h := (k - j)%nat).
  replace (k) with (j + h)%nat by lia.
  apply sum_n_m_le_loc_alt.
  intros.
  apply H0.
  unfold h in H1.
  lia.
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

End sum_n.


Section Sequences.

  Global Instance is_lim_seq_proper:
    Proper (pointwise_relation _ eq ==> eq ==> iff) (is_lim_seq).
  Proof.
    unfold Proper, pointwise_relation, respectful.
    intros.
    split; subst; apply is_lim_seq_ext; eauto.
  Qed.

  Global Instance Lim_seq_proper:
    Proper (pointwise_relation _ eq ==> eq) (Lim_seq).
  Proof.
    unfold Proper, pointwise_relation, respectful; intros.
    now apply Lim_seq_ext.
  Qed.

  Global Instance ex_lim_seq_proper:
    Proper (pointwise_relation _ eq ==> iff) (ex_lim_seq).
  Proof.
    unfold Proper,pointwise_relation, respectful; intros.
    split; intros.
    + eapply ex_lim_seq_ext; eauto.
    + symmetry in H. eapply ex_lim_seq_ext; eauto.
  Qed.


  Lemma sup_seq_pos (f : nat -> R) :
    (forall n, 0 <= f n) ->
    Rbar_le 0 (Sup_seq f).
  Proof.
    intros.
    replace (Finite 0) with (Sup_seq (fun _ => 0)).
    now apply Sup_seq_le.
    apply Sup_seq_const.
  Qed.

  Lemma ex_finite_lim_seq_bounded (f : nat -> R) :
    ex_finite_lim_seq f ->
    exists (M:R),
    forall n, Rabs (f n) <= M.
  Proof.
    intros.
    destruct H.
    apply is_lim_seq_spec in H.
    unfold is_lim_seq' in H.
    assert (0 < 1) by lra.
    specialize (H (mkposreal _ H0)).
    destruct H.
    exists (Rmax ((Rabs x)+1) (Rmax_list (map (fun n => Rabs (f n)) (seq 0 x0)))).
    intros.
    destruct (dec_le x0 n).
    - specialize (H n H1).
      apply Rle_trans with (r2 := Rabs x + 1).
      + simpl in H.
        generalize (Rabs_triang_inv (f n) x); intros.
        lra.
      + apply Rmax_l.
    - assert (n < x0)%nat by lia.
      apply Rle_trans with (r2 := Rmax_list (map (fun n0 : nat => Rabs (f n0)) (seq 0 x0))).
      + apply (Rmax_spec_map (seq 0 x0) (fun n => Rabs (f n)) n).
        apply in_seq; lia.
      + apply Rmax_r.
  Qed.

  Lemma ex_finite_lim_seq_plus (f g : nat -> R) :
    ex_finite_lim_seq f ->
    ex_finite_lim_seq g ->
    ex_finite_lim_seq (fun n => f n + g n).
  Proof.
    intros.
    destruct H.
    destruct H0.
    exists (x + x0).
    now apply is_lim_seq_plus'.
  Qed.

 Lemma ex_finite_lim_seq_ext (f g : nat -> R) :
    (forall n, f n = g n) ->
    ex_finite_lim_seq f <-> ex_finite_lim_seq g.
  Proof.
    intros.
    unfold ex_finite_lim_seq.
    split; intros;
      destruct H0 as [l ?]; exists l.
    - now apply is_lim_seq_ext with (u := f).
    - now apply is_lim_seq_ext with (u := g).
  Qed.

  Lemma ex_finite_lim_seq_S (f : nat -> R) :
    ex_finite_lim_seq f <-> ex_finite_lim_seq (fun n => f (S n)).
  Proof.
    unfold ex_finite_lim_seq.
    split; intros; destruct H as [l ?]; exists l.
    now apply is_lim_seq_incr_1 in H.
    now apply is_lim_seq_incr_1.
  Qed.

Lemma ex_finite_lim_seq_incr_n (f : nat -> R) (N : nat) :
  ex_finite_lim_seq f <-> ex_finite_lim_seq (fun n => f (N + n)%nat).
Proof.
  induction N.
  - apply ex_finite_lim_seq_ext.
    intros.
    f_equal.
  - generalize (ex_finite_lim_seq_S (fun n => f (N + n)%nat)); intros.
    rewrite IHN.
    rewrite H.
    apply ex_finite_lim_seq_ext.
    intros.
    f_equal.
    lia.
  Qed.

 Lemma is_lim_seq_max (f g : nat -> R) (l : Rbar) :
   is_lim_seq f l ->
   is_lim_seq g l ->
   is_lim_seq (fun n => Rmax (f n) (g n)) l.
 Proof.
   intros.
   apply is_lim_seq_spec.
   apply is_lim_seq_spec in H.
   apply is_lim_seq_spec in H0.
   unfold is_lim_seq' in *; intros.
   destruct l; intros.
   - destruct (H eps); destruct (H0 eps).
     exists (max x x0); intros.
     specialize (H1 n); specialize (H2 n).
     cut_to H1; try lia.
     cut_to H2; try lia.
     unfold Rmax; match_destr.
   - destruct (H M); destruct (H0 M).
     exists (max x x0); intros.
     specialize (H1 n); specialize (H2 n).
     cut_to H1; try lia.
     cut_to H2; try lia.
     unfold Rmax; match_destr.
   - destruct (H M); destruct (H0 M).
     exists (max x x0); intros.
     specialize (H1 n); specialize (H2 n).
     cut_to H1; try lia.
     cut_to H2; try lia.
     unfold Rmax; match_destr.
 Qed.


End Sequences.

Section Series.

Global Instance Series_proper :
  Proper (pointwise_relation _ eq  ==> eq) (Series).
Proof.
  unfold Proper, pointwise_relation, respectful.
  apply Series_ext.
Qed.

Global Instance ex_series_proper (K : AbsRing) (V : NormedModule K):
  Proper (pointwise_relation _ eq ==> iff) (@ex_series K V).
Proof.
  unfold Proper,pointwise_relation,respectful; intros.
  split; intros.
  + now apply ex_series_ext with (a := x).
  + apply ex_series_ext with (a := y); trivial.
    now congruence.
Qed.
  Lemma sum_f_R0_nonneg_le_Series {x : nat -> R}(hx1 : ex_series x) (hx2 : forall n, 0 <= x n) :
    forall N, sum_f_R0 x N <= Series x.
  Proof.
    intros N.
    unfold Series.
    rewrite <-sum_n_Reals.
    apply is_lim_seq_incr_compare.
    + apply Lim_seq_correct'.
      now rewrite ex_finite_lim_series.
    + intros n.
      apply sum_n_pos_incr; try lia; intros; auto.
  Qed.


  Lemma lim_0_nneg (a : nat -> R) :
    is_series a 0 ->
    (forall n, 0 <= a n) ->
    forall n, a n = 0.
  Proof.
    intros ser nneg.
    assert (serex:ex_series a) by (eexists; eauto).
    generalize (sum_f_R0_nonneg_le_Series serex nneg); intros HH.
    rewrite (is_series_unique _ _ ser) in HH.
    apply sum_f_R0_0_inv; intros n.
    apply antisymmetry; trivial.
    apply sum_f_R0_nneg; trivial.
  Qed.

  Lemma ex_series_nneg_bounded (f g : nat -> R) :
    (forall n, 0 <= f n) ->
    (forall n, f n <= g n) ->
    ex_series g ->
    ex_series f.
  Proof.
    intros.
    apply (ex_series_le f g); trivial.
    intros.
    unfold norm; simpl.
    unfold abs; simpl.
    rewrite Rabs_right; trivial.
    now apply Rle_ge.
  Qed.

    Lemma ex_series_bounded (f : nat -> R) :
    ex_series f ->
    exists (M:R),
      forall n, Rabs (sum_n f n) <= M.
  Proof.
    intros.
    apply ex_finite_lim_seq_bounded.
    now apply ex_finite_lim_series.
  Qed.

  Lemma ex_series_pos_bounded (f : nat -> R) (B:R) :
    (forall n, 0 <= f n) ->
    (forall n, sum_n f n <= B) ->
    ex_series f.
  Proof.
    intros.
    rewrite <- ex_finite_lim_series.
    apply ex_finite_lim_seq_incr with (M := B); trivial.
    intros.
    rewrite sum_Sn.
    unfold plus; simpl.
    specialize (H (S n)).
    lra.
  Qed.

  Lemma Abel_descending_convergence  (a b : nat -> R) :
    ex_series b ->
    (forall n, a n >= a (S n)) ->
    (exists M, forall n, a n >= M) ->
    ex_series (fun n => a n * b n).
  Proof.
    intros.
    pose (B := sum_n b).
    assert (forall n, sum_n (fun j => a j * b j) (S n) =
                      (a (S n))*(B (S n)) + sum_n (fun j => (B j) * (a j - (a (S j)))) n).
    {
      intros.
      do 2 rewrite sum_n_Reals.
      induction n.
      - unfold B.
        rewrite sum_n_Reals.
        simpl.
        rewrite sum_O.
        ring_simplify; lra.
      - replace (S (S n)) with (S (n+1)) by lia.
        simpl.
        replace (n+1)%nat with (S n) by lia.
        rewrite IHn.
        apply Rplus_eq_reg_r with (r := sum_f_R0 (fun j : nat => B j * (a (j) - a (S j))) n).
        ring_simplify.
        apply Rplus_eq_reg_r with (r := - (a (S n) * B (S n))).
        ring_simplify.
        unfold B.
        do 2 rewrite sum_n_Reals.
        replace (S n) with (n+1)%nat by lia.
        simpl.
        now ring_simplify.
    }
    rewrite <- ex_finite_lim_series.
    rewrite ex_finite_lim_seq_S.
    apply (ex_finite_lim_seq_ext _ _ H2).
    generalize (ex_series_bounded _ H); intros.
    rewrite <- ex_finite_lim_series in H.
    destruct H.
    assert (ex_finite_lim_seq a).
    {
      destruct H1.
      apply ex_finite_lim_seq_decr with (M := x0).
      - intros.
        specialize (H0 n).
        lra.
      - intros.
        specialize (H1 n).
        lra.
    }
    destruct H4.
    apply ex_finite_lim_seq_plus.
    - unfold ex_finite_lim_seq.
      exists (x0 * x).
      apply is_lim_seq_mult'.
      + now apply is_lim_seq_incr_1 in H4.
      + now apply is_lim_seq_incr_1 in H.
    - destruct H3.
      unfold B.
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 (sum_n (fun j : nat => scal x1 (Rabs (a j - a (S j)))) n)).
      {
        intros.
        apply sum_n_le_loc; intros.
        rewrite Rabs_mult.
        apply Rmult_le_compat_r; trivial.
        apply Rabs_pos.
      }
      assert (forall i h, a i >= a (i + h)%nat).
      {
        induction h.
        - replace (i + 0)%nat with i by lia; lra.
        - eapply Rge_trans.
          apply IHh.
          now replace (i + S h)%nat with (S (i + h))%nat by lia.
      }
      assert (forall i j, (i<=j)%nat -> a i >= a j).
      {
        intros.
        specialize (H6 i (j - i)%nat).
        now replace (i + (j - i))%nat with j in H6 by lia.
      }
      assert (forall n, sum_n (fun j => Rabs (a j - a (S j))) n = Rabs(a (0%nat) - a (S n))).
      {
        induction n.
        - now rewrite sum_O.
        - rewrite sum_Sn.
          rewrite IHn.
          unfold plus; simpl.
          rewrite Rabs_right, Rabs_right, Rabs_right.
          + ring.
          + specialize (H7 (0%nat) (S (S n))).
            cut_to H7; try lia.
            lra.
          + specialize (H0 (S n)); lra.
          + specialize (H7 (0%nat) (S n)).
            cut_to H7; try lia.
            lra.
     }
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 x1 * Rabs((a 0%nat) - a (S n))).
      {
        intros.
        specialize (H5 n).
        rewrite sum_n_scal_l in H5.
        unfold scal in H5; simpl in H5.
        unfold mult in H5; simpl in H5.
        now rewrite H8 in H5.
      }
      rewrite ex_finite_lim_series.
      apply ex_series_Rabs.
      destruct H1.
      assert (forall n, Rabs (a n) <= Rmax (a 0%nat) (-x2)).
      {
        intros.
        apply Rabs_le_between_Rmax.
        split; apply Rge_le; trivial.
        apply H7; lia.
      }
      assert (forall n, Rabs (a 0%nat - a (S n)) <= Rabs(a 0%nat) + Rmax (a 0%nat) (-x2)).
      {
        intros.
        unfold Rminus.
        generalize (Rabs_triang (a 0%nat) (- a (S n))); intros.
        eapply Rle_trans.
        apply H11.
        apply Rplus_le_compat_l.
        now rewrite Rabs_Ropp.
      }
      apply ex_series_pos_bounded with (B := x1 * (Rabs (a 0%nat) + Rmax (a 0%nat) (- x2))).
      + intros.
        apply Rabs_pos.
      + intros.
        eapply Rle_trans.
        apply H9.
        apply Rmult_le_compat_l.
        * specialize (H3 0%nat).
          apply Rle_trans with (r2 := Rabs (sum_n b 0%nat)); trivial.
          apply Rabs_pos.
        * apply H11.
  Qed.

  Lemma Abel_ascending_convergence  (a b : nat -> R) :
    ex_series b ->
    (forall n, a n <= a (S n)) ->
    (exists M, forall n, a n <= M) ->
    ex_series (fun n => a n * b n).
  Proof.
    intros.
    pose (B := sum_n b).
    assert (forall n, sum_n (fun j => a j * b j) (S n) =
                      (a (S n))*(B (S n)) + sum_n (fun j => (B j) * (a j - (a (S j)))) n).
    {
      intros.
      do 2 rewrite sum_n_Reals.
      induction n.
      - unfold B.
        rewrite sum_n_Reals.
        simpl.
        rewrite sum_O.
        ring_simplify; lra.
      - replace (S (S n)) with (S (n+1)) by lia.
        simpl.
        replace (n+1)%nat with (S n) by lia.
        rewrite IHn.
        apply Rplus_eq_reg_r with (r := sum_f_R0 (fun j : nat => B j * (a (j) - a (S j))) n).
        ring_simplify.
        apply Rplus_eq_reg_r with (r := - (a (S n) * B (S n))).
        ring_simplify.
        unfold B.
        do 2 rewrite sum_n_Reals.
        replace (S n) with (n+1)%nat by lia.
        simpl.
        now ring_simplify.
    }
    rewrite <- ex_finite_lim_series.
    rewrite ex_finite_lim_seq_S.
    apply (ex_finite_lim_seq_ext _ _ H2).
    generalize (ex_series_bounded _ H); intros.
    rewrite <- ex_finite_lim_series in H.
    destruct H.
    assert (ex_finite_lim_seq a).
    {
      destruct H1.
      apply ex_finite_lim_seq_incr with (M := x0).
      - intros.
        specialize (H0 n).
        lra.
      - intros.
        specialize (H1 n).
        lra.
    }
    destruct H4.
    apply ex_finite_lim_seq_plus.
    - unfold ex_finite_lim_seq.
      exists (x0 * x).
      apply is_lim_seq_mult'.
      + now apply is_lim_seq_incr_1 in H4.
      + now apply is_lim_seq_incr_1 in H.
    - destruct H3.
      unfold B.
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 (sum_n (fun j : nat => scal x1 (Rabs (a j - a (S j)))) n)).
      {
        intros.
        apply sum_n_le_loc; intros.
        rewrite Rabs_mult.
        apply Rmult_le_compat_r; trivial.
        apply Rabs_pos.
      }
      assert (forall i h, a i <= a (i + h)%nat).
      {
        induction h.
        - replace (i + 0)%nat with i by lia; lra.
        - eapply Rle_trans.
          apply IHh.
          now replace (i + S h)%nat with (S (i + h))%nat by lia.
      }
      assert (forall i j, (i<=j)%nat -> a i <= a j).
      {
        intros.
        specialize (H6 i (j - i)%nat).
        now replace (i + (j - i))%nat with j in H6 by lia.
      }
      assert (forall n, sum_n (fun j => Rabs (a j - a (S j))) n = Rabs(a (0%nat) - a (S n))).
      {
        induction n.
        - now rewrite sum_O.
        - rewrite sum_Sn.
          rewrite IHn.
          unfold plus; simpl.
          rewrite Rabs_left1, Rabs_left1, Rabs_left1.
          + ring.
          + specialize (H7 (0%nat) (S (S n))).
            cut_to H7; try lia.
            lra.
          + specialize (H0 (S n)); lra.
          + specialize (H7 (0%nat) (S n)).
            cut_to H7; try lia.
            lra.
     }
      assert (forall n,
                 (sum_n (fun j : nat => Rabs (sum_n b j * (a j - a (S j)))) n)  <=
                 x1 * Rabs((a 0%nat) - a (S n))).
      {
        intros.
        specialize (H5 n).
        rewrite sum_n_scal_l in H5.
        unfold scal in H5; simpl in H5.
        unfold mult in H5; simpl in H5.
        now rewrite H8 in H5.
      }
      rewrite ex_finite_lim_series.
      apply ex_series_Rabs.
      destruct H1.
      assert (forall n, Rabs (a n) <= Rmax (x2) (- (a 0%nat))).
      {
        intros.
        apply Rabs_le_between_Rmax.
        split; trivial.
        apply H7; lia.
      }
      assert (forall n, Rabs (- a 0%nat + a (S n)) <= Rmax (x2) (- a 0%nat) + Rabs (a (S n)) ).
      {
        intros.
        unfold Rminus.
        generalize (Rabs_triang (- a 0%nat) (a (S n))); intros.
        eapply Rle_trans.
        apply H11.
        apply Rplus_le_compat_r.
        now rewrite Rabs_Ropp.
      }
      apply ex_series_pos_bounded with (B := x1 * (2* Rmax x2 (- a 0%nat))).
      + intros.
        apply Rabs_pos.
      + intros.
        eapply Rle_trans.
        apply H9.
        apply Rmult_le_compat_l.
        * specialize (H3 0%nat).
          apply Rle_trans with (r2 := Rabs (sum_n b 0%nat)); trivial.
          apply Rabs_pos.
        * rewrite <- Rabs_Ropp.
          rewrite Ropp_minus_distr.
          unfold Rminus.
          rewrite Rplus_comm.
          eapply Rle_trans.
          apply H11.
          specialize (H10 (S n)).
          lra.
  Qed.

  Lemma sum_n_m_Series_alt (f : nat -> R) (n m : nat) :
     (n <= m)%nat ->
     ex_series f ->
     sum_n_m f n m = Series (fun i => f (n + i)%nat) -
                     Series (fun i => f (S m + i)%nat).
   Proof.
     intros.
     destruct (n == 0%nat).
     + setoid_rewrite e. clear H.
       induction m.
       -- cbn. rewrite (Series_incr_1); [lra |assumption].
       -- simpl. rewrite sum_n_Sm;[|lia].
          rewrite IHm. cbn.
          rewrite (Series_incr_1 (fun i => f (S(m + i)))).
          setoid_rewrite <-Nat.add_succ_l.
          replace (S m + 0)%nat with (S m) by lia.
          ring_simplify.
          now setoid_rewrite plus_n_Sm at 2.
          setoid_rewrite <-plus_Sn_m.
          now rewrite <-ex_series_incr_n.
     +
       assert (Hn : (0 < n)%nat).
       {
         destruct n.
         + intuition.
         + lia.
       }
     assert (Hm : (0 < S m)%nat) by lia.
     generalize (Series_incr_n f n Hn H0); intros.
     generalize (Series_incr_n f _ Hm H0); intros.
     rewrite H1 in H2.
     rewrite Radd_radd_minus in H2.
     rewrite <-H2. simpl.
     do 2 rewrite <-sum_n_Reals.
     replace n with (S (pred n)) by lia.
     rewrite sum_n_m_sum_n; try lia.
     reflexivity.
   Qed.

   Lemma sum_n_m_Series1 (f : nat -> R) (n m : nat) :
     (0 < n <= m)%nat ->
     ex_series f ->
     sum_n_m f n m = Series (fun i => f (n + i)%nat) -
                     Series (fun i => f (S m + i)%nat).
   Proof.
     intros.
     assert (Hn : (0 < n)%nat) by (now destruct H).
     assert (Hm : (0 < S m)%nat) by lia.
     generalize (Series_incr_n f n Hn H0); intros.
     generalize (Series_incr_n f _ Hm H0); intros.
     rewrite H1 in H2.
     rewrite Radd_radd_minus in H2.
     rewrite <-H2. simpl.
     do 2 rewrite <-sum_n_Reals.
     replace n with (S (pred n)) by lia.
     rewrite sum_n_m_sum_n; try lia.
     reflexivity.
   Qed.


   Lemma sum_n_m_Series (f : nat -> R) (n m : nat) :
     (n <= m)%nat ->
     ex_series f ->
     sum_n_m f n m = Series (fun i => f (n + i)%nat) -
                     Series (fun i => f (S m + i)%nat).
   Proof.
     intros.
     destruct (lt_dec 0 n).
     - apply sum_n_m_Series1; trivial; lia.
     - assert (n=0)%nat by lia.
       setoid_rewrite H1.
       assert (Hm : (0 < S m)%nat) by lia.
       generalize (Series_incr_n f _ Hm H0); intros.
       rewrite Series_ext with (b := f); [|now setoid_rewrite Nat.add_0_l].
       rewrite H2.
       unfold Rminus.
       rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
       replace (pred (S m)) with m by lia.
       now rewrite <- sum_n_Reals.
   Qed.

   Lemma Rmax_list_sum_series_eps (f : nat -> R) :
     ex_series f ->
     forall (eps : posreal),
     exists (NN : nat),
     forall (n N : nat),
       (N >= NN)%nat ->
       (n >= N)%nat ->
        Rmax_list
          (map
             (fun k : nat =>
                Rabs (sum_n_m f k n))
             (seq N (S (n - N)))) < eps.
   Proof.
     intros.
     generalize (Cauchy_ex_series _ H eps); intros.
     destruct H0.
     exists x.
     intros.
     apply Rmax_list_map_seq_lt_gen; try lia.
     intros.
     specialize (H0 (N+k)%nat n).
     destruct (le_dec (N + k)%nat n).
     - apply H0; lia.
     - assert (n < N + k)%nat by lia.
       rewrite sum_n_m_zero; try lia.
   Qed.

   (* to handle out of range limit *)
   Lemma Rmax_list_sum_series_eps2(f : nat -> R) :
     ex_series f ->
     forall (eps : posreal),
     exists (NN : nat),
     forall (n N : nat),
       (N >= NN)%nat ->
       (n > (S N))%nat ->
        Rmax_list
          (map
             (fun k : nat =>
                Rabs (sum_n_m f (S k) (n-1)%nat))
             (seq N (S ((n-1) - N)))) < eps.
   Proof.
     intros.
     generalize (Cauchy_ex_series _ H eps); intros.
     destruct H0.
     exists x.
     intros.
     apply Rmax_list_map_seq_lt_gen; try lia.
     intros.
     specialize (H0 (S (N + k)) (n - 1)%nat).
     destruct (lt_dec (n-1)%nat (S (N + k))).
     - rewrite sum_n_m_zero; try lia.
       unfold zero; simpl.
       cbn.
       rewrite Rabs_R0.
       apply cond_pos.
     - apply H0; lia.
   Qed.
End Series.



Section tails.

  (* Vraious properties of tail of a series. *)

  Definition tail_series (a : nat -> R) := fun n => Series(fun k => a((n+k)%nat)).

   Lemma tail_succ_sub {a : nat -> R} (ha : ex_series a) :
      forall n, a n = tail_series a n - tail_series a (S n).
  Proof.
    intros n. unfold tail_series.
    rewrite Series_incr_1.
    setoid_rewrite plus_n_Sm.
    ring_simplify. f_equal; lia.
    now rewrite <-ex_series_incr_n.
  Qed.

  Lemma tail_series_nonneg_le {a : nat -> R}(ha : ex_series a)(ha' : forall n, 0 <= a n):
    forall n, 0 <= tail_series a (S n) <= tail_series a n.
  Proof.
    intros n.
    split.
    + unfold tail_series.
      apply Series_nonneg.
      intros. apply ha'.
    + generalize (tail_succ_sub ha); intros.
      setoid_rewrite H in ha'.
      specialize (ha' n); lra.
  Qed.


  Lemma tail_series_pos_lt {a : nat -> R}(ha : ex_series a)(ha' : forall n, 0 < a n):
    forall n, 0 < tail_series a (S n) < tail_series a n.
  Proof.
    intros n.
    split.
    + unfold tail_series.
      apply Series_pos.
      now rewrite <-ex_series_incr_n.
      intros. apply ha'.
    + generalize (tail_succ_sub ha); intros.
      setoid_rewrite H in ha'.
      specialize (ha' n); lra.
  Qed.

  Lemma tail_series_nonneg_eventually_pos (a : nat -> R) :
    (forall n, 0 <= a n) ->
    (forall n, exists h, 0 < a (n + h)%nat) ->
    ex_series a ->
    forall n, 0 < tail_series a n.
  Proof.
    intros. unfold tail_series.
    destruct (H0 n).
    eapply Rlt_le_trans; eauto.
    apply Rle_trans with
        (r2 := sum_f_R0 (fun k => a (n+k)%nat) x).
    - destruct (Nat.eq_dec 0%nat x).
      + rewrite <- e.
        now simpl.
      + replace (x) with (S (x - 1)) at 2 by lia.
        simpl.
        replace (a ( n + x)%nat) with (0 + a (n + x)%nat) by lra.
        apply Rplus_le_compat.
        * rewrite <- sum_n_Reals.
          apply sum_n_nneg.
          intros.
          apply H.
        * now replace (S (x - 1)) with (x) by lia.
    - apply sum_f_R0_nonneg_le_Series.
      + now apply ex_series_incr_n.
      + intros; apply H.
  Qed.

  Lemma rudin_12_b_aux1_nonneg {a : nat -> R} (ha : ex_series a)(ha' : forall n, 0 <= a n)
        (ha'' : forall n, exists h, 0 < a (n + h)%nat):
    forall n, R_sqrt.sqrt(tail_series a n) + R_sqrt.sqrt(tail_series a (S n)) <= 2*R_sqrt.sqrt(tail_series a n).
  Proof.
    intros n.
    replace (2*sqrt(tail_series a n)) with (sqrt(tail_series a n) + sqrt(tail_series a n)) by lra.
    apply Rplus_le_compat_l with (r := sqrt (tail_series a n)).
    apply sqrt_le_1_alt.
    generalize (tail_series_nonneg_le ha ha' n); intros.
    lra.
  Qed.

  Lemma rudin_12_b_aux2_nonneg {a : nat -> R} (ha : ex_series a)(ha' : forall n, 0 <= a n):
      forall n, a n = (sqrt(tail_series a n) + sqrt(tail_series a (S n)))*(sqrt(tail_series a n) - sqrt(tail_series a (S n))).
  Proof.
     intros n.
    rewrite Rsqr_plus_minus.
    rewrite Rsqr_sqrt;[| apply Series_nonneg].
    rewrite Rsqr_sqrt;[| apply Series_nonneg].
    now apply tail_succ_sub.
    intros. apply ha'.
    intros. apply ha'.
  Qed.

  Lemma rudin_12_b_aux3_nonneg {a : nat -> R}(ha : ex_series a) (ha' : forall n, 0 <= a n)
    (ha'' : forall n, exists h, 0 < a (n + h)%nat) :
    forall n, a n*/sqrt(tail_series a n) <= 2*(sqrt(tail_series a n) - sqrt(tail_series a (S n))).
  Proof.
    intros n.
    generalize (tail_series_nonneg_le ha ha'); intros.
    assert (hr1 : 0 < sqrt(tail_series a n)).
    {
      apply sqrt_lt_R0. specialize (H n).
      destruct H.
      apply tail_series_nonneg_eventually_pos; auto.
    }
    assert (hr2 : 0 <> sqrt(tail_series a n)) by lra.
    replace (a n) with ((sqrt(tail_series a n) + sqrt(tail_series a (S n)))*(sqrt(tail_series a n) - sqrt(tail_series a (S n))))
                       by (symmetry; rewrite rudin_12_b_aux2_nonneg; trivial).
    rewrite <-Rmult_1_r.
    rewrite <-Rinv_r with (r := (sqrt(tail_series a n)));[| congruence].
    rewrite <-Rmult_assoc.
    apply Rmult_le_compat_r.
    ++ left. now apply Rinv_pos.
    ++ rewrite Rmult_comm.
       rewrite Rmult_comm with (r1 := 2).
       rewrite Rmult_assoc. apply Rmult_le_compat_l.
       enough (sqrt(tail_series a (S n)) <= sqrt(tail_series a n)) by lra.
       apply sqrt_le_1_alt.
       apply (H n).
       apply rudin_12_b_aux1_nonneg; trivial.
  Qed.

  Lemma rudin_12_b_aux4_nonneg {a : nat -> R}(ha : ex_series a) (ha' : forall n, 0 <= a n)
   (ha'' : forall n, exists h, 0 < a (n + h)%nat):
    forall m, sum_f_R0 (fun n => a n */ sqrt(tail_series a n)) m <= 2*(sqrt(tail_series a 0%nat) - sqrt(tail_series a(S m))).
  Proof.
    intros m.
    induction m; simpl.
    + apply (rudin_12_b_aux3_nonneg ha ha' ha'').
    + replace (2*(sqrt(tail_series a 0%nat) - sqrt(tail_series a(S(S m))))) with
          (2*(sqrt(tail_series a 0%nat) - sqrt(tail_series a (S m))) + 2*((sqrt(tail_series a (S m))) - sqrt(tail_series a(S(S m))))) by lra.
      apply (Rplus_le_compat _ _ _ _ IHm).
      apply (rudin_12_b_aux3_nonneg); auto.
  Qed.

  Lemma is_lim_seq_inv_pos_p_infty {a : nat -> R}(ha: is_lim_seq a 0) (ha' : forall n, 0 < a n):
    is_lim_seq (fun n => / a n) p_infty.
  Proof.
    rewrite is_lim_seq_p_infty_Reals.
    rewrite is_lim_seq_Reals in ha.
    unfold SeqProp.cv_infty. unfold Rseries.Un_cv in ha.
    unfold R_dist in ha. setoid_rewrite Rminus_0_r in ha.
    assert (ha'' : forall n, 0 <= a n) by (intros; left; trivial).
    intros M. specialize (ha (/(1+Rabs (M)))).
    assert (/(1 + Rabs(M)) > 0).
    {
      apply Rlt_gt.
      apply Rinv_pos.
      replace (0) with (0+0) by lra.
      apply Rplus_lt_le_compat; try lra.
      apply Rabs_pos.
    }
    specialize (ha H).
    destruct ha as [N HN].
    exists N; intros n Hn.
    eapply Rlt_trans with (r2 := 1 + Rabs M).
    rewrite <-Rplus_0_l at 1.
    apply Rplus_lt_le_compat; [lra|].
    apply Rle_abs.
    specialize (HN n Hn). rewrite Rabs_pos_eq in HN; firstorder.
    replace (1 + Rabs M) with (//(1 + Rabs M)).
    apply Rinv_lt_contravar; trivial.
    apply Rmult_lt_0_compat; firstorder.
    rewrite Rinv_involutive; trivial.
    enough (0 < 1 + Rabs M) by lra.
    replace 0 with (0 + 0) by lra.
    apply Rplus_lt_le_compat; try lra.
    apply Rabs_pos.
  Qed.

  (* No worst convergent series exsits. *)

   Lemma no_worst_converge_nonneg (a: nat -> R) :
     (forall n, 0 <= a n) ->
         (forall n, exists h, 0 < a (n + h)%nat) ->
    ex_series a ->
    exists (b : nat -> R),
      (forall n, 0 < b n) /\
      is_lim_seq b p_infty /\
      ex_series (fun n => a n * b n).
   Proof.
     intros Ha1 Hpos Ha2.
     pose (r := fun n => tail_series a n).
     assert (Hr : is_lim_seq r 0).
     {
       generalize (zerotails a Ha2); intros.
       unfold r.
       setoid_rewrite is_lim_seq_incr_1.
       now setoid_rewrite <-Nat.add_succ_l in H.
     }
     assert (Hr' : is_lim_seq (fun n => sqrt(r n)) 0).
     {
       generalize (is_lim_seq_continuous (sqrt) r 0); intros.
       cut_to H; trivial.
       now rewrite sqrt_0 in H.
       apply Sqrt_reg.continuity_pt_sqrt; lra.
     }
     exists (fun n => 1/sqrt(tail_series a n)).
     split.
     + intros n.
       apply Rdiv_lt_0_compat; try lra.
       apply sqrt_lt_R0.
       apply tail_series_nonneg_eventually_pos; auto.
     + split.
       ** unfold Rdiv.
          setoid_rewrite Rmult_1_l.
          apply (is_lim_seq_inv_pos_p_infty Hr'); intros.
          apply sqrt_lt_R0.
          unfold r. apply tail_series_nonneg_eventually_pos; auto.
       ** unfold Rdiv. setoid_rewrite Rmult_1_l.
          rewrite <-ex_finite_lim_series.
          apply ex_finite_lim_seq_incr with (M := 2*(sqrt(r 0%nat))).
          -- intros. do 2 rewrite sum_n_Reals.
             simpl. apply Rplus_le_compat1_l.
             apply Rmult_le_pos;[apply Ha1|left].
             apply Rinv_pos.
             apply sqrt_lt_R0.
             unfold r.
             apply tail_series_nonneg_eventually_pos; auto.
          -- intros n. rewrite sum_n_Reals.
             eapply Rle_trans.
             apply (rudin_12_b_aux4_nonneg Ha2 Ha1); intros; try auto.
             apply Rmult_le_compat_l; try lra.
             replace (sqrt (r 0%nat)) with (sqrt(r 0%nat) - 0) by lra.
             unfold r; simpl. apply Rplus_le_compat_l.
             apply Ropp_le_contravar.
             rewrite <-sqrt_0. apply sqrt_le_1_alt.
             left. apply tail_series_nonneg_eventually_pos; auto.
    Qed.


 Lemma no_worst_converge_pos (a: nat -> R) :
   (forall n, 0 < a n) ->
    ex_series a ->
    exists (b : nat -> R),
      (forall n, 0 < b n) /\
      is_lim_seq b p_infty /\
      ex_series (fun n => a n * b n).
 Proof.
   intros.
   assert (Ha : forall n, 0 <= a n) by (intros n ; left; auto).
   generalize (no_worst_converge_nonneg a Ha); intros Hn.
   apply Hn; auto.
   intros. exists 0%nat.
   apply H.
 Qed.

 Definition eventually_pos_dec (a : nat -> R) :
   {forall n : nat, exists h : nat, 0 < a (n + h)%nat} +{~(forall n : nat, exists h : nat, 0 < a (n + h)%nat)}.
 Proof.
   apply EM_dec'.
   apply Classical_Prop.classic.
 Qed.

 Theorem no_worst_converge_iff (a : nat -> R):
   (forall n, 0 <= a n) ->
   ex_series a <->
   exists (b : nat -> R),
     (forall n, 0 < b n) /\
     is_lim_seq b p_infty /\
     ex_series (fun n => a n * b n).
 Proof.
   intros.
   split; intros.
   --- destruct (eventually_pos_dec a) as [H1|H2].
       + apply no_worst_converge_nonneg; auto.
       + push_neg_in H2.
         destruct H2 as [N0 HN0].
         exists (fun n => 1 + INR n).
         split.
         -- intros n.
            rewrite Rplus_comm.
            apply INRp1_pos.
         -- split.
            ++ generalize (is_lim_seq_INR); intros.
               eapply is_lim_seq_le_p_loc with (u := fun n => INR n); auto.
               exists 0%nat. intros; lra.
            ++ setoid_rewrite Rmult_plus_distr_l.
               setoid_rewrite Rmult_1_r.
               apply ex_series_plus with (b := fun n => (a n)*(INR n)); trivial.
               apply ex_series_incr_n  with (n := N0).
               assert (forall n, a (N0 + n)%nat = 0).
               {
                 intros.
                 apply Rle_antisym.
                 - apply Rge_le, HN0.
                 - apply H.
               }
               apply (ex_series_ext (const 0)); try (apply ex_series_const0).
               intros.
               unfold const.
               rewrite H1.
               lra.
  --- destruct H0 as [b [Hb1 [Hb2 Hb3]]].
      rewrite is_lim_seq_p_infty_Reals in Hb2.
      destruct (Hb2 1%R) as [N0 HN0].
      apply ex_series_incr_n with (n := N0).
      apply ex_series_incr_n with (n := N0) in Hb3.
      apply (ex_series_le (fun n => a (N0 + n)%nat) (fun n => a (N0 + n)%nat * b (N0 + n)%nat)); auto.
      intros n.
      rewrite Rabs_pos_eq; trivial.
      rewrite <-Rmult_1_r at 1.
      apply Rmult_le_compat; try (trivial; lra).
      left. apply HN0; lia.
 Qed.

  Lemma no_best_diverge_pos (gamma : nat -> R) :
   0 < gamma 0%nat ->
   (forall n, 0 <= gamma n) ->
   is_lim_seq (sum_n gamma) p_infty ->
   exists (rho : nat -> posreal),
     is_lim_seq rho 0 /\ is_lim_seq (sum_n (fun n => rho n * gamma n)) p_infty.
 Proof.
   intros Ha0 Ha1 Ha2.
   pose (s := sum_n gamma).
   assert (forall n, 0 < s n).
   {
     unfold s; intros.
     induction n.
     - now rewrite sum_O.
     - rewrite sum_Sn.
       unfold plus; simpl.
       specialize (Ha1 (S n)).
       lra.
   }
    assert (Hs1 : is_lim_seq (fun n => /(s n)) 0).
     {
       replace (Finite 0) with (Rbar_inv p_infty) by now simpl.
       apply is_lim_seq_inv; trivial; try discriminate.
     }
     assert (forall n m, (n <= m)%nat -> (s n <= s m)).
     {
       intros.
       unfold s.
       destruct (lt_dec n m).
       - unfold sum_n.
         apply Rge_le.
         rewrite (sum_n_m_Chasles _ _ n); try lia.
         apply Rle_ge.
         replace (sum_n_m gamma 0 n) with ((sum_n_m gamma 0 n) + 0) at 1 by lra.
         unfold plus; simpl.
         apply Rplus_le_compat_l.
         apply sum_n_m_pos; trivial.
       - assert (n = m) by lia.
         now rewrite H1.
     }
     assert (Hs2 : forall n, 0 < / (s n)).
     {
       intros.
       now apply Rinv_0_lt_compat.
     }
     exists (fun n => mkposreal _ (Hs2 n)).
     split; trivial.
     assert (forall N k, sum_n_m (fun n => (gamma n)/(s n)) (S N) (S N + k) >= 1 - (s N) / (s (S N + k)%nat)).
     {
       intros.
       apply Rge_trans with (r2 := sum_n_m (fun n => (gamma n)/(s (S N + k)%nat)) (S N) (S N + k)).
       - apply Rle_ge.
         apply sum_n_m_le_loc; intros; try lia.
         unfold Rdiv.
         apply Rmult_le_compat_l; trivial.
         apply Rinv_le_contravar; trivial.
         apply H0.
         lia.
       - unfold Rdiv.
         rewrite sum_n_m_ext with (b := (fun n : nat => scal (/ s (S N + k)%nat) (gamma n))).
         + rewrite sum_n_m_scal_l.
           rewrite sum_n_m_sum_n; try lia.
           unfold s.
           unfold scal; simpl.
           unfold mult; simpl.
           rewrite Rmult_comm.
           replace (1 - sum_n gamma N * / sum_n gamma (S (N + k))) with
               ((sum_n gamma (S (N + k))%nat - sum_n gamma N) * / sum_n gamma (S (N + k))).
           * apply Rmult_ge_compat_r.
             left; apply Hs2.
             right.
             unfold minus; simpl.
             unfold plus; simpl.
             unfold opp; simpl.
             now ring_simplify.
           * field.
             apply Rgt_not_eq.
             apply H.
         + intros.
           unfold scal; simpl.
           unfold mult; simpl.
           now rewrite Rmult_comm.
     }
     simpl.
     generalize (ex_lim_seq_incr  (sum_n (fun n : nat => / s n * gamma n)) ); intros.
     cut_to  H2.
   - destruct H2.
     destruct x; trivial.
     + assert (ex_finite_lim_seq  (sum_n (fun n : nat => / s n * gamma n)) )
         by (now exists (r)).
       apply ex_lim_seq_cauchy_corr in H3.
       unfold ex_lim_seq_cauchy in H3.
       assert (0 < /2) by lra.
       specialize (H3 (mkposreal _ H4)).
       destruct H3 as [N ?].
       assert (forall k, s (S N + k)%nat < (s N)/(1 - mkposreal _ H4)).
       {
         intros.
         specialize (H3 N (S N + k)%nat).
         cut_to H3; try lia.
         assert (1 - s N / s (S N + k)%nat < mkposreal _ H4).
         {
           specialize (H1 N k).
           apply Rge_le in H1.
           eapply Rle_lt_trans.
           apply H1.
           rewrite sum_n_m_ext with (b := fun n => / s n * gamma n) by (intros; unfold Rdiv; now rewrite Rmult_comm).
           generalize (sum_n_m_sum_n (fun n : nat => / s n * gamma n) N (S N + k)); intros.
           cut_to H5; try lia.
           rewrite H5.
           unfold minus; simpl.
           unfold plus, opp; simpl.
           rewrite Rabs_minus_sym in H3.
           replace (S (N + k))%nat with (S N + k)%nat by lia.
           rewrite Rabs_right in H3; trivial.
           unfold minus, plus, opp in H5; simpl in H5.
           unfold Rminus.
           replace (S N + k)%nat with (S (N + k))%nat by lia.
           rewrite <- H5.
           apply Rle_ge.
           apply sum_n_m_pos.
           intros.
           apply Rmult_le_pos; trivial.
           left; now apply Rinv_0_lt_compat.
         }
         assert (s N / (s (S N + k)%nat) > 1 - mkposreal _ H4) by lra.
         apply Rmult_gt_compat_r with (r :=  s (S N + k)%nat ) in H6; [| apply H].
         unfold Rdiv in H6.
         rewrite Rmult_assoc in H6.
         rewrite Rinv_l in H6; [| apply Rgt_not_eq, H].
         simpl in H6; simpl; lra.
       }
       assert (ex_finite_lim_seq s).
       {
         rewrite ex_finite_lim_seq_incr_n with (N := (S N)).
         apply ex_finite_lim_seq_incr with (M := (s N)/(1 - mkposreal _ H4)).
         - intros.
           unfold s.
           replace (S N + S n)%nat with (S (S N + n))%nat by lia.
           rewrite sum_Sn.
           replace (sum_n gamma (S N + n)) with (sum_n gamma (S N + n) + 0) at 1 by lra.
           unfold plus; simpl.
           apply Rplus_le_compat_l; trivial.
         - intros.
           left; apply H5.
       }
       destruct H6.
       unfold s in H6.
       apply is_lim_seq_unique in H6.
       apply is_lim_seq_unique in Ha2.
       rewrite Ha2 in H6.
       discriminate.
     + apply is_lim_seq_spec in H2; unfold is_lim_seq' in H2.
       specialize (H2 0).
       destruct H2.
       specialize (H2 x).
       cut_to H2; try lia.
       assert (0 <= sum_n (fun n : nat => / s n * gamma n) x).
       {
         apply sum_n_nneg.
         intros.
         apply Rmult_le_pos; trivial.
         - now left.
       }
       lra.
     - intros.
       rewrite sum_Sn.
       unfold plus; simpl.
       assert (0 <= / s (S n) * gamma (S n)).
       + apply Rmult_le_pos; trivial.
         now left.
       + lra.
 Qed.

  Lemma sum_shift_diff (X : nat -> R) (m a : nat) :
     sum_n X (a + S m) - sum_n X m =
     sum_n (fun n0 : nat => X (n0 + S m)%nat) a.
   Proof.
     rewrite <-sum_n_m_shift.
     rewrite sum_n_m_sum_n; try lia.
     reflexivity.
   Qed.

 Lemma is_lim_seq_sum_shift_inf1 (f : nat -> R) (N : nat) :
   is_lim_seq (sum_n f) p_infty <->
   is_lim_seq (sum_n (fun n => f (n + (S N))%nat)) p_infty.
 Proof.
   generalize (sum_shift_diff f N); intros.
   generalize (is_lim_seq_ext _ _ p_infty H); intros.
   split; intros.
   - apply H0.
     apply is_lim_seq_minus with (l1 := p_infty) (l2 := sum_n f N).
     + now apply is_lim_seq_incr_n with (N := S N) in H1.
     + apply is_lim_seq_const.
     + unfold is_Rbar_minus, is_Rbar_plus.
       now simpl.
   - symmetry in H.
     generalize (is_lim_seq_ext _ _ p_infty H); intros.
     apply H2 in H1.
     apply is_lim_seq_incr_n with (N := S N).
     apply is_lim_seq_ext with (u := fun a : nat => (sum_n f (a + S N) - sum_n f N) + (sum_n f N)).
     + intros; lra.
     + apply is_lim_seq_plus with (l1 := p_infty) (l2 := sum_n f N); trivial.
       apply is_lim_seq_const.
       unfold is_Rbar_plus; now simpl.
  Qed.

 Lemma is_lim_seq_sum_shift_inf (f : nat -> R) (N : nat) :
   is_lim_seq (sum_n f) p_infty <->
   is_lim_seq (sum_n (fun n => f (n + N)%nat)) p_infty.
 Proof.
   destruct N.
   - split; apply is_lim_seq_ext; intros; apply sum_n_ext; intros; f_equal; lia.
   - apply is_lim_seq_sum_shift_inf1.
 Qed.


  Lemma no_best_diverge (gamma : nat -> R) :
   (forall n, 0 <= gamma n) ->
   is_lim_seq (sum_n gamma) p_infty ->
   exists (rho : nat -> posreal),
     is_lim_seq rho 0 /\ is_lim_seq (sum_n (fun n => rho n * gamma n)) p_infty.
  Proof.
    intros.
    assert (exists N, 0 < gamma N).
    {
      apply is_lim_seq_spec in H0.
      unfold is_lim_seq' in H0.
      specialize (H0 0).
      destruct H0 as [N ?].
      specialize (H0 N).
      cut_to H0; try lia.
      now apply pos_ind_sum with (N := N).
    }
    destruct H1 as [N ?].
    generalize (no_best_diverge_pos (fun n => gamma (n + N)%nat)); intros.
    cut_to H2; trivial.
    - destruct H2 as [rho [? ?]].
      assert (0 < 1) by lra.
      exists (fun n => if (lt_dec n N) then (mkposreal _ H4) else rho (n - N)%nat).
      split.
      + apply is_lim_seq_incr_n with (N := N).
        apply is_lim_seq_ext with (u := rho); trivial.
        intros.
        match_destr; try lia.
        now replace (n + N - N)%nat with (n) by lia.
      + rewrite is_lim_seq_sum_shift_inf with (N := N).
        apply is_lim_seq_ext with (u := sum_n (fun n => rho n * gamma (n + N)%nat)); trivial.
        intros.
        apply sum_n_ext; intros.
        match_destr; try lia.
        now replace (n0 + N - N)%nat with (n0) by lia.
    - now rewrite <- is_lim_seq_sum_shift_inf.
  Qed.
  (* No best divergent series exists. *)

  Theorem no_best_diverge_iff (gamma : nat -> R) :
   (forall n, 0 <= gamma n) ->
   is_lim_seq (sum_n gamma) p_infty <->
   exists (rho : nat -> posreal),
     is_lim_seq rho 0 /\ is_lim_seq (sum_n (fun n => rho n * gamma n)) p_infty.
  Proof.
    intros.
    split; intros.
    - now apply no_best_diverge.
    - destruct H0 as [? [? ?]].
      apply is_lim_seq_spec in H0.
      unfold is_lim_seq' in H0.
      assert (0 < 1) by lra.
      destruct (H0 (mkposreal _ H2)) as [? ?].
      rewrite is_lim_seq_sum_shift_inf with (N := x0) in H1.
      rewrite is_lim_seq_sum_shift_inf with (N := x0).
      assert (forall n, x (n + x0)%nat < 1).
      {
        intros.
        specialize (H3 (n + x0)%nat).
        cut_to H3; try lia.
        rewrite Rminus_0_r in H3.
        rewrite Rabs_right in H3; [|left; apply cond_pos].
        apply H3.
      }
      apply is_lim_seq_le_p_loc with (u :=  (sum_n (fun n : nat => x (n + x0)%nat * gamma (n + x0)%nat))); trivial.
      exists (0%nat); intros.
      apply sum_n_le_loc.
      intros.
      replace (gamma (n0 + x0)%nat) with (1 *  gamma (n0 + x0)%nat) at 2 by lra.
      apply Rmult_le_compat_r; trivial.
      now left.
   Qed.

   Lemma no_worst_converge_div (a : nat -> R) :
    (forall n, 0 <= a n) ->
    ex_series a ->
    exists (b : nat -> R),
      (forall n, 0 < b n) /\
      is_lim_seq b 0 /\
      ex_series (fun n => a n / Rsqr (b n)).
    Proof.
      intros apos aconv.
      destruct (no_worst_converge_iff a apos).
      specialize (H aconv).
      destruct H as [? [? [? ?]]].
      exists (fun n => sqrt (/ (x n))).
      split.
      - intros.
        apply sqrt_lt_R0.
        now apply Rinv_0_lt_compat.
      - split.
        + replace (0) with (sqrt 0) by apply sqrt_0.
          apply is_lim_seq_continuous.
          apply continuity_pt_sqrt; lra.
          replace (Finite 0) with (Rbar_inv p_infty); [| now simpl].
          apply is_lim_seq_inv; trivial; discriminate.
        + apply (ex_series_ext (fun n => a n * x n)); trivial.
          intros.
          unfold Rdiv.
          f_equal.
          rewrite Rsqr_sqrt.
          * rewrite Rinv_involutive; trivial.
            now apply Rgt_not_eq, Rlt_gt.
          * left.
            now apply Rinv_0_lt_compat.
   Qed.


 End tails.
