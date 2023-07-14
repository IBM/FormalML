Require Import Reals Lra Lia List Permutation.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix Rstruct complex.
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
  c *: v.

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
    lia.
Qed.

Lemma decode_encode_on_diag (n : nat):
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
  intros.
  unfold H_inner_prod, inner_prod.
  do 2 rewrite mxE.
  simpl.
  apply eq_big_seq.
  intros ??.
  unfold row.
  now do 6 rewrite mxE.
Qed.

Lemma sub_x_x (x : R[i]) :
  x - x = 0.
Proof.
  destruct x.
  vm_compute.
  f_equal; lra.
Qed.

Lemma sub_x_x_l (x : R[i]) :
  -x + x = 0.
Proof.
  rewrite addrC.
  apply sub_x_x.
Qed.

Lemma telescope_bigop_minus (f : nat -> R[i]) (n : nat) :
  \sum_(0 <= j < S n) (f (S j) - f j) =
    f (S n) - f 0%nat.
Proof.
  induction n.
  - now rewrite big_nat1.
  - rewrite big_nat_recr; try lia.
    simpl.
    rewrite IHn.
    rewrite addrC.
    rewrite addrA.
    f_equal.
    rewrite <- addrA.
    rewrite sub_x_x_l.
    now rewrite addr0.
Qed.

Lemma telescope_mult_bigop_aux (c : R[i]) (n : nat) :
  mul (c - 1) (\sum_(0 <= j < S n) (c ^+ j)) = 
  \sum_(0 <= j < S n) ((c^+(S j)) - (c ^+ j)).
Proof.
  Search bigop.
  Admitted.

Lemma telescope_mult_bigop (c : R[i]) (n : nat) :
  (mul (c - 1) (\sum_(0 <= j < S n) (c ^+ j)) = 
     (exp c (S n) - 1))%C.
Proof.
  rewrite telescope_mult_bigop_aux.
  rewrite telescope_bigop_minus.
  now rewrite expr0.
Qed.

Lemma telescope_div (c : R[i]) (n : nat) :
  c <> 1 ->
  \sum_(0 <= j < S n) (c ^+ j) = 
    Cdiv (c ^+ (S n) - 1) (c - 1).
Proof.
  intros.
  generalize (telescope_mult_bigop c n); intros.
  rewrite <- H0.
  unfold Cdiv.
  rewrite mulrC.
  rewrite mulrA.
  rewrite Cinv_l.
  - now rewrite mul1r.
  - unfold not.
    intros.
    clear H0.
    replace C0 with (zero C) in H1 by reflexivity.
    apply (f_equal (fun cc => add cc 1)) in H1.
    rewrite add0r in H1.
    rewrite <- addrA in H1.
    rewrite (addrC _ 1) in H1.
    rewrite sub_x_x in H1.
    now rewrite addr0 in H1.
Qed.

Lemma telescope_pow_0_nat (c : R[i]) (n : nat) :
  c <> 1 ->
  c ^+ (S n) = 1 ->
  \sum_(0 <= j < S n) (c ^+ j) = C0.
Proof.
  intros.
  rewrite telescope_div; trivial.
  rewrite H0.
  rewrite sub_x_x.
  unfold Cdiv.
  now rewrite mul0r.
Qed.

Lemma telescope_pow_0_ord (c : R[i]) (n : nat) :
  c <> 1 ->
  c ^+ (S n) = 1 ->
  \sum_(j < S n) (c ^+ j) = C0.
Proof.
  intros.
  rewrite <- (telescope_pow_0_nat c n); trivial.
  simpl.
  now rewrite big_mkord.
Qed.

Lemma mul_conj (c1 c2 : R[i]) :
  (conjc c1) * (conjc c2) = conjc (c1 * c2).
Proof.
  destruct c1; destruct c2.
  unfold conjc.
  vm_compute.
  f_equal; lra.
Qed.

Lemma exp_conj (c : R[i]) n :
  conjc (c ^+ n) = (conjc c)^+n.
Proof.
  induction n.
  - unfold conjc.
    vm_compute.
    apply f_equal.
    unfold opp; simpl.
    lra.
  - do 2 rewrite exprS.
    rewrite <- IHn.
    now rewrite <- mul_conj.
Qed.

Lemma decode_encode_off_diag (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  forall n1 n2,
    n1 <> n2 ->
    H_inner_prod (row n1 pmat) (row n2 pmat) = C0.
Proof.
  intros.
  unfold H_inner_prod, inner_prod.
  unfold pmat, peval_mat.
  rewrite mxE.
  simpl.
  destruct (pow2_S (S n)).
  unfold odd_nth_roots.
  generalize (telescope_pow_0_ord ((nth_root (2*n1+1) (2^S(S n))) * 
                                 (conjc (nth_root (2*n2+1) (2^S(S n))))) x); intros.
  rewrite <- H1.
  - rewrite <- H0.
    apply f_equal.
    apply FunctionalExtensionality.functional_extensionality; intros.
    apply f_equal.
    do 8 rewrite mxE.
    rewrite exprMn_comm.
    + f_equal.
      now rewrite exp_conj.
    + unfold comm.
      now rewrite mulrC.
  - unfold not; intros.
    destruct (pow2_S (S (S n))).
    rewrite H3 in H2.
    rewrite nth_root_conj_alt in H2.
    rewrite nth_root_mul in H2.
    apply nth_root_1_iff in H2.
    rewrite <- H3 in H2.
    clear H0 H1 H3 pmat x x0.
    admit.
  - destruct (pow2_S (S (S n))).
    rewrite H2.
    rewrite nth_root_conj_alt.
    rewrite nth_root_mul.
    rewrite Cpow_nth_root.
    apply nth_root_1_iff.
    rewrite <- H2.
    rewrite <- H0.
    clear H0 H1 H2 pmat x x0.
  Admitted.

Lemma decode_encode_scalar_mx (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  pmat *m (conj_mat (pmat^T)) = scalar_mx (2^S n)%:R.
Proof.
  intros.
  apply matrixP; intros ??.
  do 2 rewrite mxE.
  destruct (@eqtype.eqP _ x y); intros.
  - rewrite e.
    simpl.
    generalize (decode_encode_on_diag n); intros.
    rewrite eqtype.eq_refl mulr1n.
    unfold pmat in *.
    specialize (H y).
    unfold H_inner_prod, inner_prod in H.
    rewrite mxE in H.
    rewrite <- H.
    simpl.
    erewrite eq_big_seq; [reflexivity |].
    apply ssrbool.in1W; intros.
    now repeat rewrite mxE.
  - simpl.
    generalize (decode_encode_off_diag n x y n0); intros.
    unfold H_inner_prod, inner_prod in H.
    rewrite mxE/=/row in H.
    (* I am sure there is a better way to do this *)
    repeat rewrite /eqtype.eq_op/=.
    destruct (@eqnP x y); simpl in *.
    + elim n0.
      now apply ord_inj.
    + replace ((2 ^ n.+1)%:R *+ 0) with C0 by reflexivity.
      rewrite <- H.
      erewrite eq_big_seq; [reflexivity |].
      apply ssrbool.in1W; intros.
      now repeat rewrite mxE.
Qed.
    
Lemma decode_mat_encode_mat (n : nat) (cl : 'cV[R[i]]_(2^(S n))) :
  let pmat := peval_mat (odd_nth_roots (S n)) in
  let encmat := conj_mat (pmat^T) in
  pmat *m (encmat *m cl) = (2^S n)%:R *: cl.
Proof.
  simpl.
  rewrite mulmxA.
  generalize (decode_encode_scalar_mx n); intros.
  rewrite H.
  now rewrite mul_scalar_mx.
Qed.

(*
(* shows evaluation can be done by modified FFT of half size*)
Lemma V_peval_mat_prod (n : nat) :
  V_peval_mat (V_odd_nth_roots (S n)) =
    V_mat_mat_mult (V_peval_mat (V_even_nth_roots (S n)))
      (diag_matrix (V_nth_roots_half (S n))).
Proof.
  apply vec_eq_eq; intros ?.
  apply vec_eq_eq; intros ?.  
  unfold V_peval_mat, diag_matrix, V_mat_mat_mult.
  unfold V_inner_prod, transpose.
  generalize (vector_sum_all_but_1_0  (2 ^ S n) i0  (V_odd_nth_roots (S n) i ^ proj1_sig i0)%C); intros.
  rewrite <- H.
  f_equal.
  apply vec_eq_eq; intros ?.
  match_destr.
  - unfold V_odd_nth_roots, V_even_nth_roots, V_nth_roots_half.
    destruct (pow2_S (S (S n))).
    rewrite H0.
    do 2 rewrite Cpow_nth_root.
    rewrite nth_root_mul.
    f_equal.
    replace (proj1_sig i1) with (proj1_sig i0); try lia.
    now apply eq_nat_eq.
  - now rewrite Cmult_0_r.
Qed.

(* shows enconding can be done by modified IFFT of half size*)
Lemma V_encode_mat_prod (n : nat) :
  let pmat := (V_peval_mat (V_odd_nth_roots (S n))) in
  let encmat := (V_conj_mat (transpose pmat)) in
  encmat = 
    V_mat_mat_mult
      (diag_matrix (vmap' Cconj (V_nth_roots_half (S n))))
      (V_peval_mat (vmap' Cconj (V_even_nth_roots (S n)))).
Proof.
  apply vec_eq_eq; intros ?.
  apply vec_eq_eq; intros ?.  
  unfold V_peval_mat, diag_matrix, V_mat_mat_mult, V_conj_mat.
  unfold V_inner_prod, transpose.
  generalize (vector_sum_all_but_1_0  (2 ^ S n) i  (Cconj (V_odd_nth_roots (S n) i0 ^ proj1_sig i))); intros.
  rewrite <- H.
  f_equal.
  apply vec_eq_eq; intros ?.
  match_destr.
  - assert (eq_nat (proj1_sig i1) (proj1_sig i)).
    {
      apply eq_nat_eq in e.
      apply eq_eq_nat; lia.
    }
    match_destr; try congruence.
    unfold vmap', V_odd_nth_roots, V_even_nth_roots, V_nth_roots_half.
    destruct (pow2_S (S (S n))).
    rewrite H1.
    rewrite <- Cpow_conj.
    rewrite <- Cmult_conj.
    f_equal.
    do 2 rewrite Cpow_nth_root.
    rewrite nth_root_mul.
    f_equal.
    replace (proj1_sig i1) with (proj1_sig i); try lia.
    now apply eq_nat_eq.
  - assert (~ eq_nat (proj1_sig i1) (proj1_sig i)).
    {
      unfold not; intros.
      apply eq_nat_eq in H0.
      rewrite H0 in n0.
      now generalize (eq_nat_refl (proj1_sig i)).
    }
    match_destr; try congruence.
    now rewrite Cmult_0_l.
Qed.
 *)

Program Definition reflect_ordinal {n} (i:ordinal n) : ordinal n :=
  @Ordinal n (n-(S i)) _.
Next Obligation.
  intros ?[??]; lia.
Qed.

Definition vector_rev {n} {T}  (v : 'rV[T]_n) :=
  \row_(i < n) v I0 (reflect_ordinal i).

Definition vector_rev_conj {n} (v : 'rV[R[i]]_n) :=
  forall i,
    v I0 i = conjc (v I0 (reflect_ordinal i)).
  
Lemma add_conj (c1 c2 : R[i]) :
  (conjc c1) + (conjc c2) = conjc (c1 + c2).
Proof.
  destruct c1; destruct c2.
  unfold conjc.
  vm_compute.
  f_equal; lra.
Qed.

Lemma vector_rev_conj_plus {n} (v1 v2 : 'rV[R[i]]_n) :
  vector_rev_conj v1 ->
  vector_rev_conj v2 ->
  vector_rev_conj (map2_mx (fun (c1 c2 : R[i]) => add c1 c2) v1 v2).
Proof.
  unfold vector_rev_conj; intros.
  do 2 rewrite mxE.
  rewrite H.
  rewrite H0.
  Search conjc.
  now rewrite add_conj.
Qed.


Lemma vector_rev_conj_mult {n} (v1 v2 : 'rV[R[i]]_n) :
  vector_rev_conj v1 ->
  vector_rev_conj v2 ->
  vector_rev_conj (map2_mx (fun (c1 c2 : R[i]) => mul c1 c2) v1 v2).
Proof.
  unfold vector_rev_conj; intros.
  do 2 rewrite mxE.
  rewrite H; rewrite H0.
  now rewrite mul_conj.
Qed.

Lemma vector_rev_conj_scale {n} (r : R) (v : 'rV[R[i]]_n) :
  vector_rev_conj v ->
  vector_rev_conj (Vscale (RtoC r) v).
Proof.
  unfold vector_rev_conj; intros.
  unfold Vscale.
  rewrite mxE.
  rewrite H.
  rewrite mxE.
  rewrite <- mul_conj.
  f_equal.
  unfold conjc, RtoC.
  apply f_equal.
  unfold opp; simpl.
  lra.
Qed.

Lemma vector_rev_conj_const_R n (r : R) :
  vector_rev_conj (ConstVector n (RtoC r)).
Proof.
  unfold vector_rev_conj, ConstVector, RtoC; intros.
  do 2 rewrite mxE.
  unfold conjc.
  apply f_equal.
  unfold opp; simpl.
  lra.
Qed.

Lemma vector_rev_conj_conj {n} (v : 'rV[R[i]]_n) :
  vector_rev_conj v ->
  vector_rev_conj (map_mx conjc v).
Proof.
  unfold vector_rev_conj; intros.
  do 2 rewrite mxE.
  now rewrite H.
Qed.


Lemma vector_rev_conj_Cpow {n} i (v : 'rV[R[i]]_n) :
  vector_rev_conj v ->
  vector_rev_conj (map_mx (fun c => exp c i) v).
Proof.
  unfold vector_rev_conj; intros.
  do 2 rewrite mxE.
  rewrite H.
  now rewrite exp_conj.
Qed.

(*
Lemma map_Cconj_vector_to_list {n} (v : Vector C n) :
  map Cconj (vector_to_list v) = vector_to_list (vmap' Cconj v).
Proof.
  unfold vector_to_list.
  induction n.
  - unfold vector_fold_right, vector_fold_right_dep, vector_fold_right_bounded_dep.
    now simpl.
  - do 2 rewrite vector_fold_right_Sn.
    rewrite map_cons.
    rewrite IHn.
    f_equal.
 Qed.


Lemma rev_vector_to_list {n} {T} (v : Vector T n) :
  rev (vector_to_list v) = vector_to_list (vector_rev v).
Proof.
  unfold vector_rev.
  unfold vector_to_list.
  induction n.
  - unfold vector_fold_right, vector_fold_right_dep, vector_fold_right_bounded_dep.
    now simpl.
  - do 2 rewrite vector_fold_right_Sn.
  
Admitted.
*)

Lemma vector_rev_conj_sum {n} (v : 'rV[R[i]]_n) :
  vector_rev_conj v ->
  Im (vector_sum v) = 0%R.
Proof.
  intros.
  unfold vector_sum.
  Admitted.
(*
  intros.
  
  rewrite vector_sum_list_Cplus.

  apply list_Cplus_conj_rev.
  rewrite map_Cconj_vector_to_list.
  rewrite rev_vector_to_list.
  f_equal.
  apply vec_eq_eq; intros ?.
  assert (vector_rev_conj (vmap' Cconj v)).
  {
    now apply vector_rev_conj_conj.
  }
  rewrite H0.
  unfold vmap'.
  now rewrite Cconj_conj.
Qed.
*)

Lemma vector_rev_conj_inner {n} (v1 v2 : 'rV[R[i]]_n) :
  vector_rev_conj v1 ->
  vector_rev_conj v2 ->  
  Im (inner_prod v1 v2) = 0%R.
Proof.
  intros.
  unfold inner_prod.
  Admitted.
(*
  
  apply vector_rev_conj_sum.
  now apply vector_rev_conj_mult.
Qed.
*)

Lemma vector_rev_conj_odd_nth_roots (n : nat) :
  vector_rev_conj (odd_nth_roots (S n)).
Proof.
  unfold vector_rev_conj, odd_nth_roots.
  intros.
  do 2 rewrite mxE.
  destruct (pow2_S (S (S n))).
  rewrite H.
  rewrite nth_root_conj_alt.
  f_equal.
  rewrite <- H.
  replace (2^S (S n)) with (2 * 2^S n)%nat.
  - rewrite Nat.mod_small.
    + admit.
    + admit.
  - admit.
Admitted.

(*
Lemma mat_encode_real (n : nat) (cl : 'cV[R[i]]_(2^(S n))) :
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let encmat := (conj_mat (pmat^T)) in 
  vector_rev_conj (cl^T) ->
  forall i,
    Im ((encmat *m cl) i I0) = 0.
Proof.
  unfold peval_mat.
  intros.
  rewrite mxE.
  generalize vector_rev_conj_inner; intros.
  apply (vector_rev_conj_conj (vmap' (fun c => Cpow c (proj1_sig i)) (V_odd_nth_roots (S n)))).
  apply vector_rev_conj_Cpow, vector_rev_conj_odd_nth_roots.
Qed.

Lemma V_mat_encode_real_alt (n : nat) (cl : Vector C (2^(S n))) :
  let pmat := (V_peval_mat (V_odd_nth_roots (S n))) in
  let encmat := (V_conj_mat (transpose pmat)) in
  vector_rev_conj cl ->
  V_mat_vec_mult encmat cl = vmap' RtoC (vmap' Re (V_mat_vec_mult encmat cl)).
Proof.
  intros.
  apply vec_eq_eq; intros ?.
  apply Re_Im.
  now apply V_mat_encode_real.
Qed.

Definition vector_Cplus {n} (v1 v2 : Vector C n) :=
  (vmap' (fun '(a,b) => Cplus a b) (vector_zip v1 v2)).
  
Definition vector_Czero n := ConstVector n (RtoC (0%R)).

Definition vector_norm {n} (v : Vector C n) := V_inner_prod v (vmap' Cconj v).

Definition vector_proj {n} (v1 v2 : Vector C n) := Cdiv (V_inner_prod v1 (vmap' Cconj v2)) (vector_norm v2).

Lemma vector_Cplus_0_r {n} (v : Vector C n) :
  vector_Cplus v (vector_Czero n) = v.
Proof.
  apply vec_eq_eq; intros ?.
  unfold vector_Cplus, vector_Czero, vmap', ConstVector.
  simpl.
  now rewrite Cplus_0_r.
Qed.

Lemma nth_root_odd_project  (n : nat) (cl : Vector C (2^(S n))) :
  cl = fold_right vector_Cplus (vector_Czero (2^(S n)))
         (map (fun e => 
                 let b := vmap' (fun c => Cpow c e) (V_odd_nth_roots (S n)) in
                 Vscale (vector_proj cl b) b) 
              (seq 0 (2^(S n)))).
Proof.
  induction n.
  - simpl.
    unfold vmap', Vscale.
    rewrite vector_Cplus_0_r.
    unfold vector_Cplus, vmap', vector_zip.
    apply vec_eq_eq; intros ?.
    Admitted.
    
  
*)       
    

