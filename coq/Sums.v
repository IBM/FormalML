Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import List.
Require Import EquivDec Nat Omega Lra.

Require Import BasicTactics ListAdd.
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
    - rewrite eqq by omega.
      rewrite IHn; trivial.
      intros; apply eqq.
      omega.
  Qed.

  Lemma sum_f_R0'_split f n m :
    (m <= n)%nat ->
    sum_f_R0' f n =
    sum_f_R0' f m +
    sum_f_R0' (fun x => f (x+m)%nat) (n-m).
  Proof.
    intros lem.
    induction n; simpl.
    - assert (m = 0)%nat by omega.
      subst; simpl; lra.
    - destruct (m == S n); unfold equiv, complement in *.
      + subst.
        simpl.
        rewrite Rplus_assoc.
        f_equal.
        replace (n - n)%nat with 0%nat by omega.
        simpl.
        lra.
      + rewrite IHn by omega.
        rewrite Rplus_assoc.
        f_equal.
        destruct m; simpl.
        * replace (n-0)%nat with n by omega.
          replace (n+0)%nat with n by omega.
          trivial.
        * replace (n - m)%nat with (S (n - S m))%nat by omega.
          simpl.
          f_equal.
          f_equal.
          omega.
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
    - apply eqq; omega.
    - rewrite eqq by omega.
      rewrite IHn; trivial.
      intros; apply eqq.
      omega.
  Qed.

  Lemma sum_f_R0_split f n m:
    (m < n)%nat ->
    sum_f_R0 f n =
    sum_f_R0 f m +
    sum_f_R0 (fun x => f (x+S m))%nat (n-S m).
  Proof.
    intros ltm.
    induction n; simpl.
    - omega.
    - destruct (m == n); unfold equiv, complement in *.
      + subst.
        rewrite Nat.sub_diag; simpl; trivial.
      + rewrite IHn by omega.
        rewrite Rplus_assoc.
        f_equal.
        replace (n - m)%nat with (S (n - S m))%nat by omega.
        simpl.
        f_equal.
        f_equal.
        omega.
  Qed.

  Lemma sum_f_R0_split_on f n m:
    (S m < n)%nat ->
    sum_f_R0 f n =
    sum_f_R0 f m +
    f (S m) + 
    sum_f_R0 (fun x => f (x+S (S m)))%nat (n-S (S m)).
  Proof.
    intros ltm.
    rewrite (sum_f_R0_split f n m) by omega.
    repeat rewrite Rplus_assoc.
    f_equal.
    rewrite (sum_f_R0_split  (fun x : nat => f (x + S m)%nat) (n - S m) 0) by omega.
    simpl.
    f_equal.
    replace (n - S (S m))%nat with (n - S m - 1)%nat by omega.
    apply sum_f_R0_ext.
    intros.
    f_equal.
    omega.
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
      omega.
    + apply sum_f_R0'_ext; intros.
      destruct (x + S n == n)%nat;  unfold equiv, complement in *; subst; [| intuition].
      omega.
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
    omega.
  Qed.

  Lemma sum_f_R0'_as_fold_right f (n:nat) :
    sum_f_R0' f n = fold_right (fun a b => f a + b) 0 (seq 0 n).
  Proof.
    generalize (sum_f'_as_fold_right f n 0); simpl; intros HH.
    rewrite <- HH.
    apply sum_f_R0'_ext.
    intros.
    f_equal.
    omega.
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
      + omega.
      + rewrite <- sum_f_R0_sum_f_R0'.
        apply Nconv.
        omega.
    - intros eps epsgt.
      destruct (H eps epsgt) as [N Nconv].
      exists N; intros n ngt.
      rewrite sum_f_R0_sum_f_R0'.
      apply Nconv.
      omega.
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
      cut_to Nconv; [ | omega].
      replace (R_dist (sum_f_R0' (fun x : nat => s (x + n)%nat) n0) l) with
            ( R_dist (sum_f_R0' s (n + n0)) (l + sum_f_R0' s n)); trivial.
      unfold R_dist.
      rewrite (sum_f_R0'_split s (n+n0) n) by omega.
      replace ((n + n0 - n)%nat) with n0 by omega.
      f_equal.
      lra.
    - exists (N+n)%nat
      ; intros n0 n0_ge.
      specialize (Nconv (n0-n)%nat).
      cut_to Nconv; [ | omega].
      replace (R_dist (sum_f_R0' s n0) (l + sum_f_R0' s n))
                      with (R_dist (sum_f_R0' (fun x : nat => s (x + n)%nat) (n0 - n)) l); trivial.
      unfold R_dist.
      rewrite (sum_f_R0'_split s n0 n) by omega.
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
    
End inf_sum'.