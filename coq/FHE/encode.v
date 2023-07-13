Require Import Reals Lra Lia List.
From mathcomp Require Import ssreflect fintype bigop ssrnat matrix Rstruct complex.
From mathcomp Require Import ssralg.
Import ssralg.GRing.
Require Import nth_root.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope ring_scope.

Definition odd_nth_roots (n : nat) :=
  \row_(j < 2^n) (nth_root (2 * j + 1) (2 ^ (S n))).

Definition even_nth_roots (n : nat) :=
  \row_(j < 2^n) (nth_root (2 * j) (2 ^ (S n))).

Definition nth_roots_half (n : nat) :=
  \row_(j < 2^n) (nth_root j (2 ^ (S n))).

Lemma lt_0_1 :
  is_true (0 < 1).
Proof.
  easy.
Qed.

Definition I0 := Ordinal lt_0_1.

Definition peval_mat {n} (roots : 'rV[R[i]]_n) : 'M[R[i]]_(n,n) :=
  \matrix_(i < n, j < n) (exp (roots I0 i) j).

Definition conj_mat {n1 n2} (m : 'M[R[i]]_(n1,n2)) :=
  map_mx conjc m.

Definition Vscale {n} (c : R[i]) (v : 'rV[R[i]]_n) :=
  map_mx (mul c) v.

Definition Vscale_r {n} (c : R[i]) (v : 'rV[R[i]]_n) :=
  map_mx (fun x => mul x c) v.

Definition vector_sum {n} (v : 'rV[R[i]]_n) :=
  \sum_(j < n) (v I0 j).

Definition inner_prod {n} (v1 v2 : 'rV[R[i]]_n) :=
  (v1 *m (v2^T)) I0 I0.

Definition H_inner_prod {n} (v1 v2 : 'rV[R[i]]_n) :=
  inner_prod v1 (conj_mat v2).

Lemma vector_sum_scale {n} (c : R[i])  (v : 'rV[R[i]]_n) :
  mul c (vector_sum v) = vector_sum (Vscale c v).
Proof.
  unfold vector_sum.
  unfold Vscale.
  rewrite Theory.mulr_sumr.
  erewrite eq_big_seq; [reflexivity |].
  simpl.
  apply ssrbool.in1W; intros.
  now rewrite mxE.
Qed.

Lemma V_scale_l_r {n} (c : R[i])  (v : 'rV[R[i]]_n) :
  Vscale c v = Vscale_r c v.
Proof.
  unfold Vscale, Vscale_r.
  apply eq_map_mx; intros ?.
  apply mulrC.
Qed.

Lemma vector_sum_scale_r {n} (c : R[i])  (v : 'rV[R[i]]_n) :
  mul (vector_sum v) c = vector_sum (Vscale_r c v).
Proof.
  rewrite <- V_scale_l_r.
  rewrite <- vector_sum_scale.
  apply mulrC.
Qed.

Definition ConstVector n (c : R[i]) : 'rV[R[i]]_n:= const_mx c.

Definition RtoC (x : R):R[i] := Complex x R0.

Lemma vector_sum_const {n} (c : R[i]) :
  vector_sum (ConstVector n c) = mul (n%:R) c.
Proof.
  unfold vector_sum, ConstVector.
  rewrite (eq_big_seq  (fun _ => c)).
  - rewrite big_const_ord iter_addr_0.
    now rewrite Theory.mulr_natl.
  - apply ssrbool.in1W; intros.
    now rewrite mxE.
Qed.

Lemma conj_transpose {n} (m : 'M[R[i]]_(n,n)) :
  conj_mat (m^T) = (conj_mat m)^T.
Proof.
  now rewrite map_trmx.
Qed.

Lemma RtoCnat_eq n : RtoC (INR n) = n%:R.
Proof.
  unfold RtoC.
  induction n.
  - now rewrite Theory.mulr0n.
  - rewrite Theory.mulrSr S_INR -IHn /add/= add0r//.
Qed.

(* testing notations *)
Definition C0': R[i] := 0.
Definition C1': R[i] := 1.
Definition Cplus' (x y : R[i]) := x + y.
Definition Cmult' (x y : R[i]) := x * y.
Definition Cexp' (x : R[i]) (n : nat) := x ^+ n.
Definition Cdiv' (x y : R[i]) := x / y.
Definition Cinv' (x : R[i]) := x^-1.

Lemma peval_row (n : nat) :
  forall n0,
    row n0 (peval_mat (odd_nth_roots (S n))) =
      \row_(j < 2^(S n)) (odd_nth_roots (S n) I0 n0) ^+ j.
Proof.
  intros.
  unfold row.
  simpl.
  unfold peval_mat.
  apply eq_mx; intros ??.
  now rewrite mxE.
Qed.

Lemma pow_nth_root j n e :
  (nth_root j (S n)) ^+ e = nth_root (e * j) (S n).
Proof.
  unfold nth_root.
  rewrite de_moivre.
  rewrite mult_INR.
  do 2 f_equal; field; apply S_INR_not_0.
Qed.

Lemma pow2_S (j:nat) :
  exists (k : nat), 2^j = S k.
Proof.
  exists (2^j-1)%nat.
  induction j.
  - now simpl.
  - simpl.
    rewrite expnS.
    rewrite IHj.
    Admitted.

Lemma nth_root_conj' j n :
  conjc (nth_root j (S n)) = inv (nth_root j (S n)).
Proof.
  apply (nth_root_conj j n).
Qed.

Lemma mult_conj_root' j n :
  (nth_root j (S n)) * (conjc (nth_root j (S n))) = 1.
Proof.
  apply mult_conj_root.
Qed.

Lemma decode_mat_encode_mat_on_diag_row (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  forall n0,
    H_inner_prod (row n0 pmat) (row n0 pmat) = (2^S n)%:R.
Proof.
  intros.
  unfold H_inner_prod, inner_prod, pmat.
  rewrite mxE.
  rewrite (eq_big_seq  (fun _ => 1)).
  - now rewrite big_const_ord iter_addr_0.
  - apply ssrbool.in1W; intros.
    rewrite peval_row.
    unfold odd_nth_roots.
    do 5 rewrite mxE.
    destruct (pow2_S (S (S n))).
    rewrite H.
    rewrite pow_nth_root.
    apply mult_conj_root.
Qed.

Lemma H_inner_prod_mat n (M : 'M[R[i]]_(n,n)) :
  forall i j,
    (M *m (conj_mat (M ^T))) i j =
      H_inner_prod (row i M) (row j M).
Proof.
  Admitted.


Lemma decode_mat_encode_mat_on_diag (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let prod := pmat *m (conj_mat (pmat^T)) in
  forall n0,
    prod n0 n0 = (2^S n)%:R.
Proof.
  intros.
  unfold prod, pmat, peval_mat.
  rewrite H_inner_prod_mat.
  apply decode_mat_encode_mat_on_diag_row.
Qed.

Lemma telescope_pow_0 (c : C) (n : nat) :
  c <> (one C) ->
  c ^+ (S n) = 1%R ->
  \sum_(j < S n) (c ^+ j) = C0'.
Proof.
Admitted.

Lemma decode_mat_encode_mat_off_diag_row (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  forall n1 n2,
    n1 <> n2 ->
    H_inner_prod (row n1 pmat) (row n2 pmat) = 0.
Proof.
  Admitted.

Lemma decode_mat_encode_mat_off_diag (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let prod := pmat *m (conj_mat (pmat^T)) in
  forall n1 n2,
    n1 <> n2 ->
    prod n1 n2 = 0.
Proof.
  intros.
  unfold prod, pmat, peval_mat.
  rewrite H_inner_prod_mat.
  now apply decode_mat_encode_mat_off_diag_row.
Qed.
