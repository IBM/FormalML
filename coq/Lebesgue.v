Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Ranalysis_reg.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List Permutation.

Require Import Lra Omega.
Require Import BasicTactics Sums ListAdd.

Local Open Scope R_scope.
Implicit Type f : R -> R.

Definition Partition (a b : R) (n : nat) : (list R) :=
  let inc := (b - a)/(INR n) in
  map (fun i => a + (INR i)*inc) (seq 0 (n+1)).

Lemma telescope f (a b : R) (n : nat) :
  (n > 0)%nat ->
  let pl := Partition a b n in
  (fold_right Rplus 0 (map f (removelast pl))) - (fold_right Rplus 0 (map f (tl pl))) =
  f(a) - f(b).
Proof.
  (* strategy: 
     A) show that we are mapping over 1..n+1 and 0..n . 
     B) Then reorder the folds to run over (n+1),1..n and 0,1..n .
     C) since the tail parts of the fold are the same, we just need to reduce the first
     elements and show the desired results
   *)

  (* A *)
  intros nzero.
  simpl.
  unfold Partition.
  rewrite removelast_map, tl_map.
  repeat rewrite fold_right_map.
  rewrite removelast_seq, tl_seq.
  replace ((n + 1 - 1)%nat) with n by omega.

  (* B *)
  destruct n; [ omega | ].
  replace (seq 0 (S n)) with (0%nat :: seq 1 n) by reflexivity.
  rewrite seq_Sn.

  assert (eqq:forall (l:list nat),
             fold_right (fun a0 b0 => f (a + (INR a0) * ((b - a) / INR (S n))) + b0) 0 l =
             fold_right Rplus 0
                        (map f (map (fun i : nat => a + INR i * ((b - a) / INR (S n))) l))).
  - intros.
    repeat rewrite fold_right_map; trivial.
  - repeat rewrite eqq.
    
    replace (fold_right Rplus 0 (map f
         (map (fun i : nat => a + INR i * ((b - a) / INR (S n))) (seq 1 n ++ (1 + n)%nat :: Datatypes.nil))))
                                     with 
    (fold_right Rplus 0 (map f
         (map (fun i : nat => a + INR i * ((b - a) / INR (S n))) ((1 + n)%nat :: seq 1 n)))).
    + (* C *)
      repeat rewrite map_cons.
      simpl fold_right.
      generalize (fold_right Rplus 0
    (map f
       (map (fun i : nat => a + INR i * ((b - a) / match n with
                                                   | 0%nat => 1
                                                   | S _ => INR n + 1
                                                   end)) (seq 1 n)))); intros ?.
      rewrite Rmult_0_l.
      replace (match n with
      | 0%nat => 1
      | S _ => INR n + 1
               end) with (INR (S n)) by reflexivity.
      field_simplify.
      repeat f_equal.
      * lra.
      * rewrite (Rmult_comm (INR (S n))).
        unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite <- Rinv_l_sym; [lra | ].
        generalize (pos_INR n); intros.
        rewrite S_INR.
        lra.
    + apply fold_right_perm.
      * intros; lra.
      * intros; lra.
      * apply Permutation_map.
        rewrite Permutation_app_comm.
        trivial.
Qed.
