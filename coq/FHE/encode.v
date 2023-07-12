Require Import Reals Lra Lia List.
From mathcomp Require Import ssreflect fintype bigop ssrnat matrix Rstruct complex.
From mathcomp Require Import ssralg.
Import ssralg.GRing.


Set Bullet Behavior "Strict Subproofs".

(* represent complex number as pair *)
Definition nth_root (j n : nat) : R[i] :=
  let c := (2*PI*INR(j)/INR(n))%R in 
  ((cos c) +i* (sin c))%C.

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
  \matrix_(i < n1, j< n2) (conjc (m i j)).

Definition inv_mat {n1 n2} (m : 'M[R[i]]_(n1,n2)) :=
  \matrix_(i < n1, j< n2) (inv (m i j)).

Definition Vscale {n} (c : R[i]) (v : 'rV[R[i]]_n) :=
  \row_(j < n) (mul c (v I0 j)).

Definition Vscale_r {n} (c : R[i]) (v : 'rV[R[i]]_n) :=
  \row_(j < n) (mul (v I0 j) c).

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
  Admitted.

Definition ConstVector n (c : R[i]) :=
  \row_(j < n) c.

Definition RtoC (x : R) := Complex x R0.

Lemma vector_sum_const {n} (c : R[i]) :
  vector_sum (ConstVector n c) = mul (RtoC (INR n)) c.
Proof.
  unfold vector_sum, ConstVector.
Admitted.

Lemma conj_transpose {n} (m : 'M[R[i]]_(n,n)) :
  conj_mat (m^T) = (conj_mat m)^T.
Proof.
  unfold conj_mat.
  Admitted.


