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

Definition inv_mat {n1 n2} (m : 'M[R[i]]_(n1,n2)) :=
  map_mx inv m.

Definition Vscale {n} (c : R[i]) (v : 'rV[R[i]]_n) :=
  map_mx (mul c) v.

Definition Vscale_r {n} (c : R[i]) (v : 'rV[R[i]]_n) :=
  map_mx (fun x => mul x c) v.

Definition vector_sum {n} (v : 'rV[R[i]]_n) :=
  \sum_(j < n) (v I0 j).

Definition inner_prod {n} (v1 v2 : 'rV[R[i]]_n) :=
  v1 *m (v2^T).

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
  apply eq_map_mx.
  unfold ssrfun.eqfun; intros.
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
  - simpl.
    apply ssrbool.in1W; intros.
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
Definition Cinv' (x : R[i]) := x^-1.

Lemma telescope_pow_0 (c : C) (n : nat) :
  c <> (one C) ->
  c ^+ (S n) = 1%R ->
  \sum_(j < S n) (c ^+ j) = C0'.
Proof.
Admitted.


