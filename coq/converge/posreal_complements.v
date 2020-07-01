(** * Utilities on positive and non negative reals *)

Require Import ZArith Reals Psatz.
From Coq Require Import ssreflect.
Require Import Coquelicot.Coquelicot.

Arguments mkposreal  {pos}.
Arguments mknonnegreal {nonneg}.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Posreal.

Implicit Types (x y z : posreal).

(* Inserts canonical structures based automation in by and // *)
Lemma posreal_lt_0 x : 0 < x. Proof.  apply x. Qed.
Hint Resolve posreal_lt_0.

Lemma posreal_le_0 x : 0 <= x. Proof. exact: Rlt_le. Qed.
Hint Resolve posreal_le_0.

Lemma posreal_not_0 x : pos x <> 0. Proof. by move: (cond_pos x); lra. Qed.
Hint Resolve posreal_not_0.

Lemma posreal_add' x y : 0 < x + y.
Proof. case: x => x lt0x; case: y => y lt0y /=; lra. Qed.
Canonical posreal_add x y := mkposreal (posreal_add' x y).

Lemma posreal_mult' x y : 0 < x * y.
Proof. case: x => x lt0x; case: y => y lt0y /=; exact:Rmult_lt_0_compat. Qed.
Canonical posreal_mult x y := mkposreal (posreal_mult' x y).

Lemma posreal_div' x y : 0 < x / y.
Proof. case: x => x lt0x; case: y => y lt0y /=; exact:Rdiv_lt_0_compat. Qed.
Canonical posreal_div x y := mkposreal (posreal_div' x y).

Lemma posreal_pow' x n : 0 < x ^ n.
Proof. case: x => x lt0n; exact: pow_lt. Qed.
Canonical posreal_pow x n := mkposreal (posreal_pow' x n).

Lemma posreal_min' x y : 0 < Rmin x y.
Proof. exact: Rmin_stable_in_posreal. Qed.
Canonical posreal_min x y := mkposreal (posreal_min' x y).

Lemma posreal_max' x y : 0 < Rmax x y.
Proof. exact: Rlt_le_trans (Rmax_l _ _). Qed.
Canonical posreal_max x y := mkposreal (posreal_max' x y).

Definition posreal_from_positive (n : positive) : posreal.
Proof. by exists (INR (Pos.to_nat n)); apply pos_INR_nat_of_P. Defined.

(* For numerals, like 0 < 3 *)
Lemma IZR_Zpos p : 0 < IZR (Zpos p).
Proof. rewrite /IZR -INR_IPR; apply: pos_INR_nat_of_P. Qed.
Canonical IZR_Zpositive p := mkposreal (IZR_Zpos p).

Definition posreal_from_R (x : posreal) (phx : phantom R x) := x.

End Posreal.

Notation "x %:posreal" := (posreal_from_R (Phantom _ x))
  (at level 0, format "x %:posreal") : R_scope.
Hint Resolve posreal_lt_0.
Hint Resolve posreal_le_0.
Hint Resolve posreal_not_0.



Section Nonnegreal.

Implicit Types (x y z : nonnegreal).


(* Inserts canonical structures based automation in by and // *)
Lemma nonnegreal_le_0 x : 0 <= x. Proof. apply x. Qed.
Hint Resolve nonnegreal_le_0.

Lemma nonnegreal_add' x y : 0 <= x + y.
Proof. case: x => x lt0x; case: y => y lt0y /=; lra. Qed.
Canonical nonnegreal_add x y := mknonnegreal (nonnegreal_add' x y).

Lemma nonnegreal_mult' x y : 0 <= x * y.
Proof. case: x => x lt0x; case: y => y lt0y /=; exact:Rmult_le_pos. Qed.
Canonical nonnegreal_mult x y := mknonnegreal (nonnegreal_mult' x y).

Lemma nonnegreal_posreal_div' x (y : posreal) : 0 <= x / y.
Proof. case: x => x Hx; case: y => y Hy /=. exact: Rdiv_le_0_compat. Qed.
Canonical nonnegreal_posreal_div x (y : posreal) := mknonnegreal (nonnegreal_posreal_div' x y).

Lemma nonnegreal_pow' x n : 0 <= x ^ n.
Proof. case: x => x lt0n; exact: pow_le. Qed.
Canonical nonnegreal_pow x n := mknonnegreal (nonnegreal_pow' x n).

Lemma nonnegreal_min' x y : 0 <= Rmin x y.
Proof. exact: Rmin_case. Qed.
Canonical nonnegreal_min x y := mknonnegreal (nonnegreal_min' x y).

Lemma nonnegreal_max' x y : 0 <= Rmax x y.
Proof. exact: Rmax_case. Qed.
Canonical nonnegreal_max x y := mknonnegreal (nonnegreal_max' x y).

(* For numerals, like 0 < 3 *)
Lemma nonnegative_from_nat' n : 0 <= INR n.
Proof. apply pos_INR. Qed.
Canonical nonnegative_from_nat n := mknonnegreal (nonnegative_from_nat' n).

Definition nonnegreal_from_positive (n : positive) : nonnegreal.
Proof. by exists (INR (Pos.to_nat n)); apply Rlt_le, pos_INR_nat_of_P. Defined.

(* For numerals, like 0 < 3 *)
Lemma IZR_Zpos_nonneg p : 0 <= IZR (Zpos p).
Proof. apply Rlt_le; apply IZR_Zpos. Qed.
Canonical nonnegative_IZR_Zpositive p := mknonnegreal (IZR_Zpos_nonneg p).

Lemma nonnegreal_from_posreal' (x : posreal) : 0 <= x.
Proof. by []. Qed.
Canonical nonnegreal_from_posreal (x : posreal) := mknonnegreal (nonnegreal_from_posreal' x).

Definition nonnegreal_from_R (x : nonnegreal) (phx : phantom R x) := x.

End Nonnegreal.

Notation "x %:nonnegreal" := (nonnegreal_from_R (Phantom _ x))
  (at level 0, format "x %:nonnegreal") : R_scope.
Hint Resolve nonnegreal_le_0.
