Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import EquivDec Nat Omega Lra.

Require Import BasicTactics.

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

    Lemma infinite_sum'_const_to_0 c :
      infinite_sum' (fun _ => c) 0 -> c = 0.
    Proof.
      unfold infinite_sum'; intros inf.
      destruct (Req_dec c 0).
      - subst; tauto.
      - specialize (inf (Rabs c)).
        cut_to inf.
        + destruct inf as [N Nconv].
          specialize (Nconv (N+2))%nat.
          cut_to Nconv; [| omega].
          unfold R_dist in Nconv.
          rewrite sum_f_R0'_const in Nconv.
          rewrite Rminus_0_r in Nconv.
          apply Rsqr_lt_abs_1 in Nconv.
          rewrite Rsqr_mult in Nconv.
          apply Rlt_not_le in Nconv.
          elim Nconv.
          replace (c²) with ((c² * 1)%R) at 1 by lra.
          { apply Rmult_le_compat_l.
            - apply Rle_0_sqr.
            - rewrite plus_INR.
              rewrite Rsqr_plus.
              replace (INR 2)² with (INR 4) by (vm_compute; lra).
              apply (Rle_trans _ (INR 4)).
              + vm_compute; lra.
              + rewrite Rplus_assoc.
                rewrite Rplus_comm.
                replace (INR 4) with (INR 4 + 0)%R at 1 by lra.
                rewrite Rplus_assoc.
                apply Rplus_le_compat_l.
                apply Rplus_le_le_0_compat.
                * rewrite Rmult_assoc.
                  apply Rmult_le_pos; [ lra | ].
                  apply Rmult_le_pos; apply pos_INR.
                * apply Rle_0_sqr.
          }
        + apply Rabs_pos_lt; trivial.
    Qed.
    
(*
  Lemma infinite_sum'_chisel s l : infinite_sum' s l <->
                                  forall n,
                                    infinite_sum' (fun x =>
                                                    if x == n then 0
                                                    else s x) (l - s n).
  Proof.
    unfold infinite_sum'.
    split; intros H.
    - intros n eps eps_gt.
      destruct (H eps eps_gt) as [N Nconv].
      exists (S (max n N)).
      assert (n <= max n N)%nat by apply Nat.le_max_l.
      intros n0 n0_gt.
      specialize (Nconv (S (max n N))).
      cut_to Nconv.
      + rewrite (sum_f_R0'_chisel s (S (max n N)) n) in Nconv by omega.
        
        
      + apply Nat.le_max_r.
        
  Qed.
 *)
    
End inf_sum'.