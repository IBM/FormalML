Require Import Reals Lra Lia List Permutation.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix Rstruct complex.
From mathcomp Require Import ssralg ssrfun.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv ssrint zmodp eqtype ssrbool.

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

Lemma poly_size_eq0 {R:ringType} (p:{poly R}) :
  seq.size p == 0%nat = (p == 0).
Proof.
  rewrite -size_poly_leq0.
  lia.
Qed.

Definition peval_mat {n} (roots : 'rV[R[i]]_n) : 'M[R[i]]_(n,n) :=
  \matrix_(i < n, j < n) (exp (roots 0 i) j).

Definition conj_mat {n1 n2} (m : 'M[R[i]]_(n1,n2)) :=
  map_mx conjc m.

Definition Vscale {n} (c : R[i]) (v : 'rV[R[i]]_n) :=
  c *: v.

Definition vector_sum {n} (v : 'rV[R[i]]_n) :=
  \sum_(j < n) (v 0 j).

Definition inner_prod {n} (v1 v2 : 'rV[R[i]]_n) :=
  (v1 *m (v2^T)) 0 0.

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

(* Coercion RtoC : R >-> complex. *)

Lemma vector_sum_const {n} (c : R[i]) :
  vector_sum (ConstVector n c) = mul (n%:R) c.
Proof.
  rewrite /vector_sum /ConstVector.
  (under eq_big_seq => - do (apply ssrbool.in1W => ?; rewrite mxE)).
  rewrite big_const_ord iter_addr_0 Theory.mulr_natl//.
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
      \row_(j < 2^(S n)) (odd_nth_roots (S n) 0 n0) ^+ j.
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
  apply Cpow_nth_root.
Qed.

Lemma pow2_S (j:nat) :
  { k : nat | (2^j)%nat == S k}.
Proof.
  exists (2^j-1)%nat.
  induction j.
  - now simpl.
  - simpl.
    rewrite expnS (eqP IHj).
    lia.
Defined.

Lemma decode_encode_on_diag (n : nat):
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  forall n0,
    H_inner_prod (row n0 pmat) (row n0 pmat) = (2^S n)%:R.
Proof.
  intros.
  unfold H_inner_prod, inner_prod, pmat.
  rewrite mxE.
  under eq_big_seq.
  - apply ssrbool.in1W; intros.
    rewrite peval_row /odd_nth_roots !mxE.
    destruct (pow2_S (S (S n))).
    rewrite (eqP i) pow_nth_root mult_conj_root.
    over.
  - rewrite big_const_ord iter_addr_0//.
Qed.

Lemma H_inner_prod_mat n (M : 'M[R[i]]_(n,n)) :
  forall i j,
    (M *m (conj_mat (M ^T))) i j =
      H_inner_prod (row i M) (row j M).
Proof.
  rewrite /H_inner_prod /inner_prod => i j.
  rewrite !mxE //=.
  apply eq_big_seq => ??.
  rewrite !mxE//.
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

Lemma telescope_mult_bigop_aux (c : R[i]) (n : nat) :
  (c - 1) * (\sum_(0 <= j < S n) (c ^+ j)) = 
  \sum_(0 <= j < S n) ((c^+(S j)) - (c ^+ j)).
Proof.
  rewrite big_distrr.
  simpl.
  apply eq_big_seq; intros ??.
  rewrite mulrBl.
  rewrite mul1r.
  f_equal.
  rewrite exprSr.
  now rewrite mulrC.
Qed.

Lemma telescope_mult_bigop (c : R[i]) (n : nat) :
  (c - 1) * (\sum_(0 <= j < S n) (c ^+ j)) = 
     c ^+ (S n) - 1.
Proof.
  rewrite telescope_mult_bigop_aux.
  rewrite telescope_sumr.
  + now rewrite expr0.
  + lia.
Qed.

Lemma telescope_div (c : R[i]) (n : nat) :
  c <> 1 ->
  \sum_(0 <= j < S n) (c ^+ j) = 
    (c ^+ (S n) - 1) / (c - 1).
Proof.
  intros.
  generalize (telescope_mult_bigop c n); intros.
  rewrite -H0 mulrC mulrA Cinv_l.
  - now rewrite mul1r.
  - unfold not.
    intros.
    clear H0.
    replace C0 with (zero C) in H1 by reflexivity.
    apply (f_equal (fun cc => add cc 1)) in H1.
    by rewrite add0r -addrA (addrC _ 1) sub_x_x addr0 in H1.
Qed.

Lemma telescope_pow_0_nat (c : R[i]) (n : nat) :
  c <> 1 ->
  c ^+ (S n) = 1 ->
  \sum_(0 <= j < S n) (c ^+ j) = C0.
Proof.
  intros.
  rewrite telescope_div; trivial.
  by rewrite H0 sub_x_x mul0r.
Qed.

Lemma telescope_pow_0_ord (c : R[i]) (n : nat) :
  c <> 1 ->
  c ^+ (S n) = 1 ->
  \sum_(j < S n) (c ^+ j) = C0.
Proof.
  intros.
  rewrite <- (telescope_pow_0_nat c n); trivial.
  by rewrite /= big_mkord.
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
  - by rewrite !exprS -IHn -mul_conj.
Qed.

Lemma modulo_modn n m : (n mod m)%nat = div.modn n m.
Proof.
  unfold Nat.modulo.
  destruct m; simpl; trivial.
  generalize (Nat.divmod_spec n m 0 m (le_refl _)); intros HH.
  simpl in HH.
  destruct (Nat.divmod n m 0 m); simpl in *.
  rewrite !plusE !multE !minusE in HH*.
  rewrite !muln0 subnn !addn0 in HH.
  destruct HH; subst.
  replace (n0 + m * n0 + (m - n1))%nat with (n0 * m.+1 + (m - n1))%nat by lia.
  rewrite div.modnMDl div.modn_small//.
  lia.
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
  rewrite <- H0.
  - rewrite <- (eqP i).
    erewrite eq_big_seq; [reflexivity |].
    simpl.
    apply ssrbool.in1W; intros.
    rewrite !mxE exprMn_comm.
    + rewrite exp_conj//.
    + rewrite /comm mulrC//.
  - unfold not; intros.
    destruct (pow2_S (S (S n))).
    rewrite (eqP i0) nth_root_conj_alt nth_root_mul in H1.
    apply nth_root_1_iff in H1.
    rewrite -(eqP i0) in H1.
    clear H0 i i0 pmat x x0.
    destruct n1 as [x xlt]; destruct n2 as [y ylt]; simpl in *.
    assert (neq:x <> y).
    {
      intros HH.
      apply H; subst.
      f_equal; apply eqtype.bool_irrelevance.
    }
    clear H.
    rewrite !modulo_modn in H1.
    apply (f_equal ssrint.Posz) in H1.
    revert H1.
    rewrite -intdiv.modz_nat ssrint.PoszD -ssrint.subzn.
    + rewrite -intdiv.modz_nat.
      rewrite -intdiv.modzDm.
      rewrite !addn1 intdiv.modzDl intdiv.modzNm.
      rewrite !intdiv.modzDm expnSr.
      destruct (@leP x y).
      * rewrite -intdiv.modzDl intdiv.modz_small/=; lia.
      * rewrite intdiv.modz_small/=; lia.
    + lia.
  - destruct (pow2_S (S (S n))).
    rewrite (eqP i0) nth_root_conj_alt nth_root_mul Cpow_nth_root.
    apply nth_root_1_iff.
    rewrite -(eqP i0) -(eqP i).
    clear H0 i i0 pmat x x0.
    destruct n1 as [x xlt]; destruct n2 as [y ylt]; simpl in *.
    assert (neq:x <> y).
    {
      intros HH.
      apply H; subst.
      f_equal; apply eqtype.bool_irrelevance.
    }
    clear H.
    rewrite !modulo_modn.
    replace (expn 2 (S (S n))) with (expn 2 (S n) * 2)%nat by (rewrite (expnS _ (S n)); lia).
    rewrite -div.muln_modr -div.modnDm.
    replace (2 * x)%nat with (x * 2)%nat by lia.
    rewrite div.modnMDl.
    replace (div.modn (2 ^ n.+1 * 2 - div.modn (2 * y + 1) (2 ^ n.+1 * 2)) 2) with
      (div.modn 1 2).
    + rewrite div.modnDm.
      replace (1 + 1)%nat with 2%nat by lia.
      rewrite div.modnn; lia.
    + replace ( div.modn (2 * y + 1) (2 ^ n.+1 * 2)) with (2 * y + 1)%nat.
      * rewrite div.modnB; try lia.
      * rewrite div.modn_small; lia.
  Qed.

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


(* shows evaluation can be done by modified FFT of half size*)
Lemma peval_mat_prod (n : nat) :
  peval_mat (odd_nth_roots (S n)) =
    peval_mat (even_nth_roots (S n)) *m diag_mx (nth_roots_half (S n)).
Proof.
  apply matrixP; intros ??.
  unfold nth_roots_half, even_nth_roots, peval_mat.
  rewrite mul_mx_diag.
  repeat rewrite mxE.
  destruct (pow2_S (S (S n))).
  rewrite (eqP i) !pow_nth_root nth_root_mul.
  f_equal.
  lia.
Qed.

(* shows enconding can be done by modified IFFT of half size*)
Lemma encode_mat_prod (n : nat) :
  let pmat := peval_mat (odd_nth_roots (S n)) in
  let encmat := (conj_mat (pmat^T)) in
  encmat = 
    diag_mx (map_mx conjc (nth_roots_half (S n))) 
    *m
       peval_mat (map_mx conjc (even_nth_roots (S n))).
Proof.
  apply matrixP; intros ??.
  unfold nth_roots_half, conj_mat, peval_mat, even_nth_roots.
  rewrite mul_diag_mx.
  repeat rewrite mxE.
  destruct (pow2_S (S (S n))).
  rewrite (eqP i) pow_nth_root -exp_conj mul_conj.
  f_equal.
  rewrite pow_nth_root nth_root_mul.
  f_equal.
  lia.
Qed.

Definition vector_rev {n} {T}  (v : 'rV[T]_n) :=
  \row_(i < n) v 0 (rev_ord i).

Definition vector_rev_conj {n} (v : 'rV[R[i]]_n) :=
  forall i,
    v 0 i = conjc (v 0 (rev_ord i)).
  
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

Lemma Cconj_im_0 (c : C) :
  conjc c = c -> Im c = 0%R.
Proof.
  destruct c.
  unfold conjc; simpl.
  intros.
  injection H; intros.
  apply (f_equal (fun z => z + Im)) in H0.
  unfold add, opp in H0; simpl in H0.
  unfold zero; simpl.
  lra.
Qed.


Lemma vector_rev_sum_rev {n} (v : 'rV[R[i]]_n) :
  vector_rev_conj v ->
  forall i,
    Im ((v + vector_rev v) 0 i) = 0.
Proof.
  intros.
  rewrite /vector_rev !mxE H rev_ordK.
  apply Cconj_im_0.
  rewrite -add_conj conjcK addrC//.
Qed.

Lemma vector_rev_reflect {n} (v : 'rV[R[i]]_n) i :
  vector_rev v 0 i = v 0 (rev_ord i).
Proof.
  rewrite mxE//.
Qed.

Lemma vector_sum_rev {n} (v : 'rV[R[i]]_n) :
  vector_sum v = vector_sum (vector_rev v).
Proof.
  unfold vector_sum, vector_rev.
  rewrite (reindex_inj rev_ord_inj)/=.
  apply eq_big_seq, ssrbool.in1W => x.
  rewrite mxE//.
Qed.

Lemma vector_sum_add {n} (a b : 'rV[R[i]]_n) :
  vector_sum (a + b) = vector_sum a + vector_sum b.
Proof.
  unfold vector_sum.
  cut (\sum_(j < n) (a 0 j + b 0 j) = \sum_(j < n) a 0 j + \sum_(j < n) b 0 j).
  {
    intros HH.
    rewrite -HH/=.
    apply eq_big_seq, ssrbool.in1W => x.
    rewrite mxE//.
  } 
  rewrite big_split //.
Qed.

Lemma Im_add (a b:R[i]) : Im (a + b) = Im a + Im b.
Proof.
  now destruct a; destruct b; simpl.
Qed.

Lemma vector_sum_reals {n} (v : 'rV[R[i]]_n) :
  (forall i, Im (v 0 i) = 0) -> 
  Im (vector_sum v) = 0.
Proof.
  unfold vector_sum.
  apply big_rec; simpl; trivial.
  intros.
  rewrite Im_add H1 H0// addr0//.
Qed.

Lemma vector_rev_conj_sum {n} (v : 'rV[R[i]]_n) :
  vector_rev_conj v ->
  Im (vector_sum v) = 0%R.
Proof.
  intros.
  cut (Im (vector_sum v + vector_sum (vector_rev v)) = 0).
  {
    rewrite -vector_sum_rev.
    destruct (vector_sum v); simpl.
    rewrite /add /zero/=.
    lra.
  }
  rewrite -vector_sum_add vector_sum_reals//.
  now apply vector_rev_sum_rev.
Qed.  

Lemma inner_product_as_sum {n} (v1 v2 : 'rV[R[i]]_n) :
  inner_prod v1 v2 = vector_sum (map2_mx (fun a b => a * b) v1 v2).
Proof.
  rewrite /inner_prod /mulmx/= mxE /vector_sum/=.
  apply eq_big_seq, ssrbool.in1W => x.
  rewrite /map2_mx /trmx !mxE//.
Qed.

Lemma vector_rev_conj_inner {n} (v1 v2 : 'rV[R[i]]_n) :
  vector_rev_conj v1 ->
  vector_rev_conj v2 ->  
  Im (inner_prod v1 v2) = 0.
Proof.
  intros.
  rewrite inner_product_as_sum vector_rev_conj_sum//.
  now apply vector_rev_conj_mult.
Qed.

Lemma vector_rev_conj_odd_nth_roots (n : nat) :
  vector_rev_conj (odd_nth_roots (S n)).
Proof.
  unfold vector_rev_conj, odd_nth_roots.
  intros.
  do 2 rewrite mxE.
  destruct (pow2_S (S (S n))).
  rewrite (eqP i0).
  rewrite nth_root_conj_alt.
  f_equal.
  rewrite -(eqP i0).
  rewrite (expnS _ (S n)).
  unfold rev_ord; simpl.
  rewrite Nat.mod_small; try lia.
  destruct i.
  simpl.
  lia.
Qed.

Lemma mv_rev_conj_real (n1 n2 : nat) (mat : 'M[R[i]]_(n1,n2)) (cl : 'cV[R[i]]_n2) :
  vector_rev_conj (cl^T) ->
  (forall i, vector_rev_conj (row i mat)) ->
  forall i,
    Im ((mat *m cl) i 0) = 0.
Proof.
  intros.
  replace ((mat *m cl) i 0) with (((row i mat) *m cl) 0 0).
  - generalize (vector_rev_conj_inner (row i mat) (cl^T)); intros HH.
    unfold inner_prod in HH.
    rewrite trmxK in HH.
    now apply HH.
  - repeat rewrite mxE.
    apply eq_big_seq; intros ??.
    now repeat rewrite mxE.
Qed.

Lemma encode_mat_pow_odd_roots (n:nat) :
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  forall i,
    row i pmat^T = (map_mx (fun c => c ^+ i) (odd_nth_roots (S n))).
Proof.
  intros.
  unfold odd_nth_roots, pmat, peval_mat.
  apply matrixP; intros ??.
  now repeat rewrite mxE.
Qed.  

Lemma mat_encode_real {n} (cl : 'cV[R[i]]_(2^(S n))) :
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let encmat := (conj_mat (pmat^T)) in 
  vector_rev_conj (cl^T) ->
  forall i,
    Im ((encmat *m cl) i 0) = 0.
Proof.
  intros.
  apply mv_rev_conj_real; trivial.
  intros.
  unfold encmat, conj_mat.
  rewrite <- map_row.
  apply vector_rev_conj_conj; simpl.
  rewrite encode_mat_pow_odd_roots.
  apply vector_rev_conj_Cpow.
  apply vector_rev_conj_odd_nth_roots.
Qed.

Lemma Re_Im_0 (c : R[i]) :
  Im c = 0 <-> c = RtoC (Re c).
Proof.
  destruct c.
  unfold RtoC; simpl.
  split; intros.
  - now rewrite H.
  - inversion H.
    unfold zero; simpl; lra.
Qed.

Lemma mat_encode_real_alt {n} (cl : 'cV[R[i]]_(2^(S n))) :
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let encmat := (conj_mat (pmat^T)) in 
  vector_rev_conj (cl^T) ->
  encmat *m cl = map_mx (fun c => RtoC (Re c)) (encmat *m cl).
Proof.
  intros.
  apply matrixP => x y.
  generalize (mat_encode_real cl H x) => HH.
  apply Re_Im_0 in HH.
  by rewrite ord1 {}HH !mxE.
Qed.

Definition vector_rev_col {n} {T}  (v : 'cV[T]_n) :=
  \col_(i < n) v (rev_ord i) 0.

Program Definition vector_reflect_conj {n} (cl : 'cV[R[i]]_(2^n)) : 'cV[R[i]]_(2^(S n)) :=
  col_mx cl (conj_mat (vector_rev_col cl)).
Next Obligation.
  intros.
  rewrite expnS.
  lia.
Qed.

Lemma vector_reflect_conj_rev_conj {n} (cl : 'cV[R[i]]_(2^n)) :
  vector_rev_conj (vector_reflect_conj cl)^T.
Proof.
  unfold vector_rev_conj, vector_reflect_conj.
  intros.
  unfold eq_rect.
  destruct (vector_reflect_conj_obligation_1 n).
  unfold conj_mat, vector_rev_col.
  repeat rewrite mxE.
  destruct (splitP i); destruct (splitP (rev_ord i)); unfold rev_ord in *; simpl in *.
  - destruct i; destruct j; destruct j0; simpl in *; lia.
  - rewrite !mxE/= conjcK.
    f_equal.
    destruct j.
    cut (m = 2 ^ n - k.+1)%nat.
    {
      intros; subst.
      f_equal; apply eqtype.bool_irrelevance.
    } 
    destruct i; simpl in *; subst; lia.
  - rewrite !mxE/=.
    do 2 f_equal.
    destruct j.
    cut (2 ^ n - k.+1 = m)%nat.
    {
      intros; subst.
      f_equal; apply eqtype.bool_irrelevance.
    } 
    destruct i; simpl in *; subst; lia.
  - destruct i; destruct k; destruct k0; simpl in *; lia.
Qed.

Definition CKKS_poly_encode {n} (cl : 'cV[R[i]]_(2^n)) : 'cV[R]_(2^(S n)) :=
  let pmat := (peval_mat (odd_nth_roots (S n))) in
  let encmat := (conj_mat (pmat^T)) in 
  (inv (2 ^+ S n)) *:
    (map_mx (fun c => Re c) (encmat *m (vector_reflect_conj cl))).

Definition int_to_zmodp (i : int) (p : nat) : 'Z_p := i %:~R.

Definition col_to_poly {n} (cl : 'cV[R]_n) := rVpoly (cl^T).
Definition col_to_poly2 {n} (cl : 'cV[int]_n) := rVpoly (cl^T).

Definition red_poly (pol : {poly int}) p' :=
  map_poly (fun c => int_to_zmodp c p') pol.

Definition mx_round {n m} (mat : 'M[R]_(n,m)) : 'M[int]_(n,m) :=
  map_mx (fun r => ssrZ.int_of_Z (up r)) mat.


From mathcomp Require Import order.

(* 0 <= rand < 1 *)
Definition ran_round (x rand : R) :=
  let hi := up x in
  if (Order.lt (Rminus (IZR hi) x) rand)%R then hi else (Zminus hi 1).

Definition CKKS_poly_encode_Z {n} (cl : 'cV[R[i]]_(2^n)) : 'cV[int]_(2^(S n)) :=
  mx_round (CKKS_poly_encode cl).

Definition vector_proj_coef {n} (v1 v2 : 'rV[R[i]]_n) :=
  (H_inner_prod v1 v2) / (H_inner_prod v2 v2).

(* this is multiplication for vectors mod monic p *)
Definition rv_mul_mod {n} (a b : 'rV[R]_n) (p : {poly R}) : 'rV[R]_n :=
  poly_rV (rVpoly(a) * rVpoly b %% p).

(* poly rem x^n+1 *)
Definition rv_mul_mod_xn_1 {n} (a b : 'rV[R]_n) (n : nat) : 'rV[R]_n :=
  let prod := (rVpoly a * rVpoly b) in
  poly_rV (take_poly n prod - drop_poly n prod).

Lemma size_Xn_addC [R : ringType] (n :nat) (b : R) :
    seq.size ('X^n.+1 + b%:P) = n.+2.
Proof.
  rewrite size_addl size_polyXn// (leq_ltn_trans (size_polyC_leq1 b))//.
Qed.

Lemma lead_coef_xn [R : unitRingType] (n : nat) (c : R) :
  lead_coef ('X^n.+1 + c%:P) \is a unit.
Proof.
  rewrite lead_coefDl.
  - rewrite lead_coefXn unitr1 //.
  - rewrite size_polyXn.
    generalize (size_polyC_leq1 c); lia.
Qed.

Lemma poly_rem_xn [R : idomainType] (n : nat) (c : R) (a : {poly R}) :
  let p := 'X^n.+1 + polyC c in
  a %% p = take_poly n.+1 a + (-c)*: (drop_poly n.+1 a %% p).
Proof.
  simpl.
  have H := lead_coef_xn n c.
  generalize (size_Xn_addC n c); intros.
  rewrite -{1}(poly_take_drop n.+1 a).
  rewrite Pdiv.IdomainUnit.modpD; trivial.
  f_equal.
  - rewrite modp_small; trivial.
    rewrite H0.
    generalize (size_take_poly n.+1 a); intros.
    apply H1.
  - rewrite -Pdiv.IdomainUnit.modp_mul; trivial.
    assert ('X^n.+1 %% ('X^n.+1 + c%:P) = -c%:P).
    {
      assert ('X^n.+1 = 1 * ('X^n.+1 + c%:P) -c%:P).
      {
        rewrite mul1r -addrA subrr addr0//.
      }
      rewrite -(Pdiv.IdomainUnit.modpP H H1)//.
      rewrite size_Xn_addC size_opp ltnS.
      rewrite (leq_trans (size_polyC_leq1 c))//.
    }
    rewrite H1 mulrC -Pdiv.IdomainUnit.modpZl // -mul_polyC polyCN //.
Qed.

From mathcomp Require Import polydiv.

Lemma Xn_add_c_monic [R : ringType] n (c: R) :
  'X^n.+1 + c%:P \is monic.
Proof.
  rewrite monicE lead_coefDl.
  - rewrite lead_coefXn //.
  - rewrite size_polyXn.
    generalize (size_polyC_leq1 c); lia.
 Qed.

Lemma poly_rem_xn_alt [R : comRingType] (n : nat) (c : R) (a : {poly R}) :
  let p := 'X^n.+1 + polyC c in
  Pdiv.CommonRing.rmodp a p = 
    take_poly n.+1 a + 
      (Pdiv.CommonRing.rmodp ((-c)*:(drop_poly n.+1 a)) p).
Proof.
  simpl.
  have H := Xn_add_c_monic n c.
  generalize (size_Xn_addC n c); intros.
  rewrite -{1}(poly_take_drop n.+1 a).
  rewrite Pdiv.RingMonic.rmodpD; trivial.
  f_equal.
  - rewrite Pdiv.CommonRing.rmodp_small; trivial.
    rewrite H0.
    generalize (size_take_poly n.+1 a); intros.
    apply H1.
  - rewrite -Pdiv.RingMonic.rmodp_mulmr; trivial.
    assert (Pdiv.CommonRing.rmodp ('X^n.+1) ('X^n.+1 + c%:P) = -c%:P).
    {
      assert ('X^n.+1 = 1 * ('X^n.+1 + c%:P) -c%:P).
      {
        rewrite mul1r -addrA subrr addr0//.
      }

      rewrite {1}H1.
      rewrite Pdiv.RingMonic.rmodp_addl_mul_small; trivial.
      rewrite size_Xn_addC size_opp ltnS.
      rewrite (leq_trans (size_polyC_leq1 c))//.
    }
    rewrite H1 mulrC; trivial.
    rewrite -mul_polyC polyCN //.
Qed.

Require Import Recdef.
Function poly_rem_xn_1 [R : ringType] (n : nat) (a : {poly R}) {measure seq.size a} : {poly R} :=
  let a1 := take_poly n.+1 a in
  let a2 := drop_poly n.+1 a in
  if a2 == 0 then a1 else
    a1 - poly_rem_xn_1 n a2.
Proof.
  intros.
  rewrite size_drop_poly.
  enough (seq.size a <> 0)%nat by lia.
  intros eqq.
  rewrite drop_poly_eq0 in teq.
  - rewrite eq_refl// in teq.
  - rewrite eqq//.
Defined.

Arguments poly_rem_xn_1 [R] n a : rename.

Lemma poly_rem_xn_id [R : ringType] n (a:{poly R}) : seq.size a <= n.+1 ->
  poly_rem_xn_1 n a = a.
Proof.
  functional induction poly_rem_xn_1 n a => slt.
  - rewrite take_poly_id//.
  - rewrite drop_poly_eq0// eqxx// in y.
Qed.    

Lemma poly_rem_xn_1_le [R : ringType] n (a:{poly R}) : is_true (seq.size (poly_rem_xn_1 n a) <= n.+1).
Proof.
  functional induction poly_rem_xn_1 n a.
  - rewrite size_take_poly//. 
  - rewrite (leq_trans (size_add _ _)) // size_opp geq_max IHp size_take_poly//.
 Qed.

Lemma poly_size_0 {R : ringType} :
  seq.size (zero (poly_zmodType R)) = 0%nat.
Proof.
  rewrite /zero /= size_polyC eqxx//.
Qed.

Lemma drop_poly_eq0_iff {R : ringType} (m : nat) (p : {poly R}) :
  seq.size p <= m <-> drop_poly m p = 0.
Proof.
  split; intros.
  - now apply drop_poly_eq0.
  - generalize (size_drop_poly m p); intros.
    rewrite H poly_size_0 in H0.
    lia.
 Qed.

Lemma poly_rem_xn_1_pmod [R : idomainType] n (a : {poly R}) :
  poly_rem_xn_1 n a = a %% ('X^n.+1 + 1%:P).
Proof.
  functional induction poly_rem_xn_1 n a.
  - move => /eqP in e.
    apply drop_poly_eq0_iff in e.
    rewrite take_poly_id //.
    rewrite modp_small; trivial.
    rewrite size_Xn_addC.
    apply e.
  - rewrite poly_rem_xn IHp scaleN1r//.
Qed.

Definition equiv_xn_1 [R : ringType] (n : nat): rel {poly R} :=
  fun p => fun q => poly_rem_xn_1 n (p - q) == 0.

Definition ideal_xn_1_pred [R : ringType] (n : nat) : pred (poly_zmodType R) :=
  fun p => poly_rem_xn_1 n p == 0.

Lemma  poly_rem_xn_1_1 [R : ringType] n :
  poly_rem_xn_1 (R:=R) n 1 = 1.
Proof.
  apply poly_rem_xn_id.
  rewrite size_poly1//.
Qed.

Lemma  poly_rem_xn_0_0 [R : ringType] n :
  poly_rem_xn_1 (R:=R) n 0 = 0.
Proof.
  apply poly_rem_xn_id.
  rewrite size_poly0//.
Qed.

Lemma rmodp_monic_scale [R : ringType] (c : R) (p d : {poly R}) :
  d \is monic ->
  Pdiv.CommonRing.rmodp (c *: p) d = c *: (Pdiv.CommonRing.rmodp p d). 
Proof.
  move=> monic.
  have sz: seq.size (c *: (Pdiv.CommonRing.rmodp (R:=R) p d)) < seq.size d
    by rewrite (leq_ltn_trans (size_scale_leq c (Pdiv.CommonRing.rmodp (R:=R) p d)))//
         Pdiv.CommonRing.ltn_rmodpN0// monic_neq0//.

  rewrite -(Pdiv.RingMonic.rmodp_addl_mul_small monic (c *: Pdiv.CommonRing.rdivp (R:=R) p d) sz).
  by rewrite {1}(Pdiv.RingMonic.rdivp_eq monic p) scalerDr scalerAl.
Qed.

Lemma rmodp_monic_opp [R : ringType] (p d : {poly R}) :
  d \is monic ->
  Pdiv.CommonRing.rmodp (- p) d = -(Pdiv.CommonRing.rmodp p d). 
Proof.
  rewrite -!scaleN1r.
  by apply rmodp_monic_scale.
Qed.

Lemma poly_rem_xn_1_pmod_alt [R : comRingType] n (a : {poly R}) :
  poly_rem_xn_1 n a = Pdiv.CommonRing.rmodp a ('X^n.+1 + 1%:P).
Proof.
  functional induction poly_rem_xn_1 n a.
  - move => /eqP in e.
    apply drop_poly_eq0_iff in e.
    rewrite take_poly_id //.
    rewrite Pdiv.Ring.rmodp_small; trivial.
    rewrite size_Xn_addC.
    apply e.
  - rewrite poly_rem_xn_alt.
    f_equal.
    rewrite IHp.
    rewrite -rmodp_monic_opp.
    + f_equal.
      rewrite scaleN1r //.
    + apply  Xn_add_c_monic.
Qed.

Lemma poly_rem_xn_1_eq0_mul [R : comRingType] n (a b: {poly R}) :
  poly_rem_xn_1 n b = 0 ->
  poly_rem_xn_1 n (a * b) = 0.
Proof.
  do 2 rewrite poly_rem_xn_1_pmod_alt; intros.
  rewrite -Pdiv.RingMonic.rmodp_mulmr.
  - rewrite H mulr0.
    apply Pdiv.Ring.rmod0p.
  - apply Xn_add_c_monic.
 Qed.

Lemma poly_rem_xn_1_eq0_add  [R : comRingType] n (a b: {poly R}) :
  poly_rem_xn_1 n a = 0 ->
  poly_rem_xn_1 n b = 0 ->
  poly_rem_xn_1 n (a + b) = 0.
Proof.
  do 3 rewrite poly_rem_xn_1_pmod_alt; intros.
  rewrite Pdiv.RingMonic.rmodpD.
  - rewrite H H0 addr0 //.
  - apply Xn_add_c_monic.
 Qed.

Lemma poly_rem_xn_1_eq0_opp [R : comRingType] n (a: {poly R}) :
  poly_rem_xn_1 n a = 0 ->
  poly_rem_xn_1 n (- a) = 0.
Proof.
  replace (-a) with (-1 * a).
  - apply poly_rem_xn_1_eq0_mul.
  - apply Theory.mulN1r.
Qed.

Lemma ideal_xn_1_pred_proper [R : comRingType] n : proper_ideal (ideal_xn_1_pred (R:=R) n).
Proof.
  rewrite /proper_ideal /in_mem /mem/= /ideal_xn_1_pred.
  split.
  - rewrite poly_rem_xn_1_1.
    apply oner_neq0.
  - rewrite /prop_in1/= /in_mem /= => a b /eqP /poly_rem_xn_1_eq0_mul->//.
Qed.

Lemma ideal_xn_1_pred_zmod [R : comRingType] n : zmodPred (ideal_xn_1_pred (R :=R) n).
Proof.
  constructor.
  - constructor; [constructor|].
    constructor.
    + rewrite /in_mem //= /ideal_xn_1_pred poly_rem_xn_0_0 //.
    + rewrite /in_mem //= /prop_in2 /ideal_xn_1_pred => a b.
      rewrite /in_mem /mem /= => /eqP-eqq1 /eqP-eqq2.
      rewrite poly_rem_xn_1_eq0_add //.
  - rewrite /Pred.Exports.oppr_closed /mem /= /ideal_xn_1_pred => a.
    rewrite /in_mem /= => /eqP-eqq1.
    rewrite poly_rem_xn_1_eq0_opp //.
Qed.

Definition ideal_xn_1_idealr [R : comRingType] n : idealr (ideal_xn_1_pred (R := R) n)
  := MkIdeal (ideal_xn_1_pred_zmod n) (ideal_xn_1_pred_proper n).

Definition qring_xn [R : comRingType] n
  := { ideal_quot (KeyedPred (ideal_xn_1_idealr (R := R) n)) }.

Definition foo1_add [R : comRingType] n (a b : qring_xn (R:=R) n) := a + b.

Section polyops.

  Context {T:comRingType}.
  
  Definition monic_poly := {p:{poly T} | (p \is monic) && (seq.size p > 1)}.

  Import Pdiv.
  Import CommonRing.
  Definition princ_ideal_pred (p : {poly T}) : pred {poly T} :=
    fun q => rmodp q p == 0.
(*
  fun q => q %% p == 0.
*)

Lemma princ_ideal_proper (p : monic_poly) :
  proper_ideal (princ_ideal_pred (val p)).
Proof.
  intros.
  unfold proper_ideal, princ_ideal_pred, in_mem, mem; split; simpl.
  - rewrite rmodp_small.
    + rewrite poly1_neq0//.
    + destruct (andP (valP p)).
      rewrite size_poly1 H0 //.
  - intros ??.
    rewrite -RingMonic.rmodp_mulmr // /in_mem/=.
    move => /eqP->.
    rewrite mulr0 rmod0p//.
    now destruct (andP (valP p)).
Qed.

Lemma princ_ideal_zmod (p : monic_poly) :
  zmodPred (princ_ideal_pred (val p)).
Proof.
  constructor.
  - constructor; [constructor|].
    constructor.
    + rewrite /in_mem //= /princ_ideal_pred rmod0p//.
    + rewrite /in_mem //= /prop_in2 /princ_ideal_pred => a b.
      rewrite /in_mem /mem /= RingMonic.rmodpD // /=.
      * move => /eqP-> /eqP->.
        rewrite addr0//.
      * now destruct (andP (valP p)).
  - rewrite /Pred.Exports.oppr_closed /mem /= /princ_ideal_pred => a.
    rewrite /in_mem /= => /eqP-eqq1.
    destruct (andP (valP p)).
    rewrite rmodp_monic_opp // eqq1 oppr0 //.    
Qed.

Definition princ_ideal (p : monic_poly) :
  idealr (princ_ideal_pred (val p))
  := MkIdeal (princ_ideal_zmod p) (princ_ideal_proper p).

Definition qring (p : monic_poly) 
  := { ideal_quot (KeyedPred (princ_ideal p)) }.

Section example.
  Context (p: monic_poly).

  Definition foo_add (a b : qring p) := a + b.
  Definition foo_mul (a b : qring p) := a * b.

  Local Open Scope quotient_scope.

  Definition lift (a : {poly T}) : qring p
    := lift_cst (qring p) a.

  Definition proj (a : {poly T}) := (\pi_(qring p) a).
  Definition proj2 (a : {poly T}) : qring p := (\pi  a).

  Example something (a b : {poly T}) := a == b %[mod (qring p)].

End example.
(*
Require Import qpoly.
Section qpoly.
 Context {T:comRingType}.  
Definition cyclotomic n : {poly T} := ('X^n.+1 + 1%:P).
Definition qpoly_add n (p q : {qpoly (cyclotomic n)}) := p + q.
Definition qpoly_mul n (p q : {qpoly (cyclotomic n)}) := p * q.
Definition qpoly_inj n (p : {poly T}) := in_qpoly (cyclotomic n) p.
End qpoly.
*)

End polyops.

Section rmorphism.
Lemma RtoC_is_rmorphism :
  rmorphism RtoC.
Proof.
  constructor.
  - intros ??.
    unfold RtoC, add; simpl.
    f_equal.
    rewrite addrN //.
  - split.
    + intros ??.
      unfold RtoC, mul; simpl.
      f_equal.
      * rewrite mulr0 oppr0 addr0 //.
      * rewrite mulr0 mul0r addr0 //.
    + unfold RtoC, one; simpl.
      unfold one, real_complex_def; simpl.
      f_equal.
Qed.        

Canonical RtoC_rmorphism := RMorphism RtoC_is_rmorphism.

Lemma map_RtoC_is_rmorphism :
  rmorphism (map_poly RtoC).
Proof.
  apply map_poly_is_rmorphism.
Qed.

Canonical map_RtoC_rmorphism := RMorphism map_RtoC_is_rmorphism.

Lemma ev_C_is_rmorphism (x:R[i]) :
  rmorphism (fun (p : {poly R}) => (map_poly RtoC p).[x]).
Proof.

  destruct map_RtoC_is_rmorphism.
  destruct (horner_eval_is_lrmorphism x) as [[??] ?].
  constructor.
  - intros ??.
    rewrite  -horner_evalE base base0 //.
  - split.
    + intros ??.
      rewrite -horner_evalE mixin mixin0 //.
    + rewrite -horner_evalE mixin mixin0 //.
Qed.

Canonical ev_C_rmorphism (x:R[i]) := RMorphism (ev_C_is_rmorphism x).

End rmorphism.

Module matrix_ring.
Section matrixRing.
  Section base_ring.
    Context {T:ringType}.

    Variable (n m : nat).
    
    Definition MR_mul (A B : 'M[T]_(S n, S m)) := map2_mx (fun (a b : T) => a * b) A B.
    Definition MR1 : 'M[T]_(S n,S m) := const_mx 1.
    Definition MR0: 'M[T]_(S n,S m) := const_mx 0.
    Lemma MR_mulA : associative MR_mul.
    Proof.
      by move=> A B C; apply/matrixP=> i j; rewrite !mxE Monoid.mulmA.
    Qed.

    Lemma MR_mul1z : left_id MR1 MR_mul.
    Proof.
      intros ?.
      unfold MR_mul, MR1.
      unfold map2_mx, const_mx.
      apply matrixP; intros ??.
      rewrite !mxE mul1r //.
    Qed.

    Lemma MR_mulz1 : right_id MR1 MR_mul.
    Proof.
      intros ?.
      unfold MR_mul, MR1.
      unfold map2_mx, const_mx.
      apply matrixP; intros ??.
      rewrite !mxE mulr1 //.
    Qed.

    Fact mul_0MR : left_zero MR0 MR_mul.
    Proof.
      intros ?.
      unfold MR_mul, MR1.
      unfold map2_mx, const_mx.
      apply matrixP; intros ??.
      rewrite !mxE mul0r //.
    Qed.
    
    Fact mul_MR0 : right_zero MR0 MR_mul.
    Proof.
      intros ?.
      unfold MR_mul, MR1.
      unfold map2_mx, const_mx.
      apply matrixP; intros ??.
      rewrite !mxE mulr0 //.
    Qed.

    Lemma MR_mul_addr : right_distributive MR_mul (@addmx T (S n) (S m)).
    Proof.
      move=> A B C; apply/matrixP=> i j.
      unfold MR_mul, addmx, map2_mx.
      rewrite !mxE mulrDr //.
    Qed.

    Lemma MR_mul_addl : left_distributive MR_mul (@addmx T (S n) (S m)).
    Proof.
      move=> A B C; apply/matrixP=> i j.
      unfold MR_mul, addmx, map2_mx.
      rewrite !mxE mulrDl //.
    Qed.
    
    Fact MR1_neq0 : MR1 != MR0.
    Proof.
      unfold MR1, MR0, const_mx.
      apply /eqP/matrixP.
      move/(_ ord0 ord0).
      rewrite !mxE.
      apply/eqP/oner_neq0.
    Qed.

    Definition MR_ringMixin :=
      RingMixin MR_mulA MR_mul1z MR_mulz1 MR_mul_addl MR_mul_addr MR1_neq0.
    
    Canonical MR_ringType := Eval hnf in RingType 'M[T]_(S n,S m) MR_ringMixin.
  End base_ring.

  Section com_ring.

    Context {T:comRingType}.
    Variable (n m : nat).
    
    Lemma MR_mulC : commutative (@MR_mul T n m).
    Proof.
      intros ??.
      unfold MR_mul, map2_mx.
      apply eq_mx; intros ??.
      rewrite mulrC //.
    Qed.

    Canonical MR_comRingType := Eval hnf in ComRingType (@MR_ringType T n m) MR_mulC.

(*    Definition MR_embed (val : 'M[T]_(S n,S m)) : MR_comRingType := val. *)

  End com_ring.

  Section unit_ring.
    Context {T:unitRingType}.
    Variable (n m : nat).
    
    Definition MR_unit : pred 'M[T]_(S n,S m)
      := [pred m : 'M[T]_(S n,S m) | [forall i, [forall j, (m i j) \is a unit]]].

    Definition MR_inv (x:'M[T]_(S n,S m)) : 'M[T]_(S n,S m)
      := if MR_unit x then map_mx inv x else x.

    Lemma MR_mulVr : ({in MR_unit, left_inverse 1 MR_inv (@mul (MR_ringType _ _))}).
    Proof.
      move=> M.
      rewrite /MR_inv.
      rewrite -topredE /= => eqq1.
      rewrite eqq1.
      apply/matrixP => x y.
      rewrite !mxE.
      apply mulVr.
      move: eqq1.
      rewrite/MR_unit simpl_predE.
      by move/forallP /(_ x)/forallP/(_ y).
    Qed.

    Lemma MR_mulrV : ({in MR_unit, right_inverse 1 MR_inv (@mul (MR_ringType _ _))}).
    Proof.
      move=> M.
      rewrite /MR_inv.
      rewrite -topredE /= => eqq1.
      rewrite eqq1.
      apply/matrixP => x y.
      rewrite !mxE.
      apply mulrV.
      move: eqq1.
      rewrite/MR_unit simpl_predE.
      by move/forallP /(_ x)/forallP/(_ y).
    Qed.

    Lemma MR_unitP (x y : MR_ringType n m) : y * x = 1 /\ x * y = 1 -> MR_unit x.
    Proof.
      move=>[/matrixP-linv /matrixP-rinv].
      rewrite/MR_unit/simpl_predE.
      apply/forallP => i.
      apply/forallP => j.
      apply/unitrP.
      exists (y i j).
      move: linv  => /(_ i j).
      move: rinv  => /(_ i j).
      by rewrite !mxE => -> ->.
    Qed.
    
    Lemma MR_inv0id : {in [predC MR_unit], MR_inv =1 id}.
    Proof.
      move => x.
      by rewrite -topredE /= -topredE /= /MR_inv => /Bool.negb_true_iff->.
    Qed.

    Definition MR_unitRingMixin : UnitRing.mixin_of (Ring.Pack (Ring.class (MR_ringType n m)))
      := @UnitRingMixin (MR_ringType _ _) MR_unit MR_inv MR_mulVr MR_mulrV MR_unitP MR_inv0id.

    Canonical MR_unitRingType := Eval hnf in UnitRingType (@MR_ringType T n m) MR_unitRingMixin.

  End unit_ring.
  
  End matrixRing.
End matrix_ring.

Section eval_vectors.
  
  Import matrix_ring.

  Context {n} (vals : 'rV[R[i]]_(n.+1)).

  Definition mx_eval (p : {poly R}) : MR_comRingType 0 n :=
    (map_mx (fun x => (map_poly RtoC p).[x]) vals).

  Lemma mx_evalC c : mx_eval c%:P = const_mx (RtoC c).
  Proof.
    apply matrixP=> a b.
    rewrite !mxE.
    by rewrite (map_polyC RtoC_rmorphism) /= hornerC.
  Qed.
  
  Lemma mx_eval_is_rmorphism :
    rmorphism (fun p => mx_eval p).
  Proof.
    constructor.
    - move=> x y.
      apply matrixP=> a b.
      rewrite !mxE.
      by apply ev_C_is_rmorphism.
    - split.
      + move=> x y.
        apply matrixP=> a b.
        rewrite !mxE.
        by apply ev_C_is_rmorphism.
      + by rewrite mx_evalC.
  Qed.

  Canonical mx_eval_rmorphism 
    : {rmorphism poly_ringType R_ringType -> MR_comRingType 0 n}
    := RMorphism (mx_eval_is_rmorphism).

  Lemma mx_eval_1 :
    mx_eval 1 = 1.
  Proof.
    apply mx_eval_is_rmorphism.
  Qed.

  Definition mx_eval_ker_pred : pred {poly R} :=
    fun p => mx_eval p == 0.

  Lemma mx_eval_ker_proper :
    proper_ideal (mx_eval_ker_pred).
  Proof.
    split.
    - by rewrite /mx_eval_ker_pred /in_mem /mem /= mx_eval_1 oner_neq0.
    - move => a b.
      rewrite /in_mem /=.
      rewrite /mx_eval_ker_pred.
      case: (mx_eval_is_rmorphism) => _ -> /eqP->.
      by rewrite mulr0.
  Qed.

  Lemma mx_eval_ker_zmod :
    zmodPred (mx_eval_ker_pred).
  Proof.
    constructor.
    - constructor; [constructor|].
      constructor.
      + rewrite /in_mem //= /mx_eval_ker_pred /mx_eval /map_mx.
        apply/eqP/matrixP=>a b.
        rewrite !mxE.
        unfold map_poly.
        generalize (hornerC (RtoC 0) (vals a b)); intros.
        rewrite poly_size_0.
        rewrite (eq_poly (fun _ => 0)).
        * rewrite -{2}(horner0 (vals a b)).
          f_equal.
          apply /polyP => i /=.
          rewrite coef_poly coefC /=.
          by case: (i == 0)%nat.
        * move=> i ilt.
          rewrite coefC.
          by case: (i == 0)%nat.
      + rewrite /in_mem //= /prop_in2 /mx_eval_ker_pred => a b.
        rewrite /in_mem /mem /= .
        generalize (raddfD (mx_eval_rmorphism) a b); intros.
        simpl in H; rewrite H.
        revert H0 H1.
        move => /eqP -> /eqP->.
        rewrite add0r //.
    - rewrite /Pred.Exports.oppr_closed /mem /= /mx_eval_ker_pred => a.
      rewrite /in_mem /= => /eqP-eqq1.
      generalize (raddfN (mx_eval_rmorphism) a); intros.
      simpl in H.
      rewrite H eqq1 oppr0 //.
  Qed.

  Definition mx_eval_ker_is_ideal :
    idealr mx_eval_ker_pred
    := MkIdeal mx_eval_ker_zmod mx_eval_ker_proper.

  Canonical mx_eval_ker_ideal := KeyedPred (mx_eval_ker_is_ideal).

  Definition mx_eval_ker_quot_ring
    := { ideal_quot mx_eval_ker_ideal }.

  Local Open Scope quotient_scope.

  Definition mx_eval_quot : mx_eval_ker_quot_ring -> MR_comRingType 0 n
    := lift_fun1 mx_eval_ker_quot_ring mx_eval.

  Lemma pi_mx_eval_quot : {mono (\pi_mx_eval_ker_quot_ring) : x / mx_eval x >-> mx_eval_quot x}.
  Proof.
    move=> x.
    rewrite /mx_eval_quot -eq_lock.
    case piP => a /EquivQuot.eqmodP.
    rewrite /Quotient.equiv_equiv /Quotient.equiv /in_mem /mem /= /mx_eval_ker_pred.
    destruct mx_eval_is_rmorphism.
    rewrite base => eqq.
    move=> /eqP in eqq.
    apply (f_equal (fun z => z + mx_eval a)) in eqq.
    by rewrite -addrA add0r (addrC _ (mx_eval a)) addrN addr0 in eqq.
  Qed.

  Lemma mx_eval_quotC c :
    mx_eval_quot (\pi_({ideal_quot mx_eval_ker_ideal}) c%:P) = const_mx (RtoC c).
  Proof.
    by rewrite pi_mx_eval_quot mx_evalC.
  Qed.

  Lemma mx_eval_quot1 : mx_eval_quot 1 = 1.
  Proof.
    rewrite /one /= /Quotient.one /= /one /= /locked.
    destruct master_key.
    by rewrite mx_eval_quotC.
  Qed.

  Lemma mx_eval_quot_is_rmorphism : rmorphism mx_eval_quot.
  Proof.
    split => [x|].
    - apply quotP=> y <-.
      revert x.
      apply quotP => x <-.
      rewrite !reprK.
      rewrite !pi_mx_eval_quot.
      rewrite /mx_eval_quot -!eq_lock.
      rewrite -pi_is_additive.
      case: piP => y' /eqquotP.
      rewrite /mx_eval_ker_pred /in_mem/mem/= => /eqP.
      generalize (raddfD (mx_eval_rmorphism)); intros mx_eval_add.
      generalize (raddfN (mx_eval_rmorphism)); intros mx_eval_opp.
      generalize (mx_eval_add (x-y) (-y')); intros add1.
      simpl in add1; rewrite add1.
      specialize (mx_eval_add x (-y)); simpl in mx_eval_add.
      rewrite mx_eval_add.
      generalize (mx_eval_opp y); intro opp1.
      simpl in opp1; rewrite opp1.
      specialize (mx_eval_opp y'); simpl in mx_eval_opp.
      rewrite mx_eval_opp.
      intro HH.
      apply (f_equal (fun z => z + mx_eval y')) in HH.
      rewrite add0r -!addrA in HH.
      rewrite (addrC _ (mx_eval y')) addrN addr0 in HH.
      by rewrite -HH.
    - constructor.
      + move => x.
        apply quotP=> y <-.
        revert x.
        apply quotP => x <-.
        rewrite !reprK.
        rewrite !pi_mx_eval_quot.
        rewrite /mx_eval_quot -!eq_lock.
        rewrite -pi_is_multiplicative.
        case: piP => y' /eqquotP.
        rewrite /mx_eval_ker_pred /in_mem/mem/= => /eqP.
        destruct mx_eval_is_rmorphism as [? [??]].
        specialize (base (x * y) y'); simpl in base.
        rewrite base.
        specialize (m x y); simpl in m.
        rewrite m.
        intro HH.
        apply (f_equal (fun z => z + mx_eval y')) in HH.
        rewrite add0r -!addrA in HH.
        rewrite (addrC _ (mx_eval y')) addrN addr0 in HH.
        by rewrite -HH.
      + by apply mx_eval_quot1.
  Qed.

  Lemma mx_eval_quot_is_injective (x y : mx_eval_ker_quot_ring) :
    mx_eval_quot x = mx_eval_quot y -> x = y.
  Proof.
    rewrite /mx_eval_quot -!eq_lock.
    rewrite -{2}[x]reprK -{2}[y]reprK.
    move: (repr x) (repr y) => {x} {y} x y eqq.
    apply/eqquotP.
    rewrite /Quotient.equiv/=.
    rewrite /mx_eval_ker_pred /in_mem/mem/=.
    apply/eqP.
    destruct mx_eval_is_rmorphism.
    specialize (base x y).
    simpl in base.
    by rewrite eqq addrN in base.
 Qed.

End eval_vectors.

Definition odd_nth_roots' n :=
  \row_(j < (S (proj1_sig (pow2_S n))))
    (nth_root (2 * j + 1) (2 ^ (S n))).

Lemma odd_nth_roots_minpoly n :
  forall i,
    root ('X^(2^n) + 1%:P) (odd_nth_roots n 0 i).
Proof.
  move=> i.
  rewrite /odd_nth_roots mxE /root hornerD hornerXn hornerC.
  generalize (odd_roots_prim i n); intros.
  apply (f_equal (fun z => C1 + z)) in H.
  rewrite addrN in H.
  rewrite addrC in H.
  apply /eqP.
  unfold zero in *; simpl in *.
  unfold real_complex_def in *.
  unfold zero in *; simpl in *.
  by rewrite <- H.
Qed.

Lemma minpoly_mult_odd_nth_roots n (p : {poly R[i]}) :
  Pdiv.Ring.rmodp p ('X^(2^n) + 1%:P) = 0 ->
  forall i, root p (odd_nth_roots n 0 i).
Proof.
intros.
move=> /Pdiv.Ring.rmodp_eq0P in H.
rewrite Pdiv.ComRing.rdvdp_eq in H.
destruct (pow2_S n).
generalize (Xn_add_c_monic (R:=ComplexField.complex_comRingType R_fieldType) x 1); intros.
rewrite monicE in H0.
move=> /eqP in H0.
rewrite -(eqP i0) in H0.
rewrite H0 in H.
rewrite Theory.expr1n in H.
move=> /eqP in H.
rewrite Theory.scale1r in H.
rewrite H.
unfold root.
apply /eqP.
rewrite hornerM.
generalize (odd_nth_roots_minpoly n i); intros.
unfold root in H1.
move=> /eqP in H1.
rewrite H1.
rewrite mulr0 //.
Qed.

Lemma drop_poly_opp [S : ringType] n (p : {poly S}) :
  drop_poly n (- p) = - drop_poly n p.
Proof.
  rewrite -!scaleN1r.
  apply drop_polyZ.
Qed.

Lemma drop_poly_diff [S : ringType] n (p q : {poly S}) :
  drop_poly n p = drop_poly n q ->
  seq.size (p - q) <= n.
Proof.
  intros.
  assert (drop_poly n (p - q) = 0).
  {
    by rewrite drop_polyD drop_poly_opp -H addrN.
  }
  generalize (poly_take_drop n (p - q)); intro decomp.  
  rewrite H0 mul0r addr0 in decomp.
  rewrite -decomp.
  apply size_take_poly.
Qed.

Lemma monic_size_pos [S : ringType] (p : {poly S}) :
  p \is monic ->
  seq.size p > 0.
Proof.
  case: ltP => // n0lt.
  have: seq.size p == 0%nat by lia.
  rewrite size_poly_eq0 => eqq1 /monic_neq0.
  by rewrite eqq1.
Qed.

Lemma monic_drop_n_1 [S : ringType] n (p : {poly S}) :
  p \is monic ->
  seq.size p = n.+1 ->
  drop_poly n p = 1.
Proof.
  rewrite monicE /lead_coef.
  rewrite /drop_poly poly_def => /[swap] -> /=.
  replace (n.+1 - n)%nat with 1%nat by lia.
  rewrite big_ord1 add0n => /eqP->.
  by rewrite expr0 alg_polyC.
Qed.

Lemma monic_dif_same_deg (p q : {poly R[i]}) :
  p \is monic ->
  q \is monic ->
  seq.size p = seq.size q ->
  seq.size (q - p) < seq.size p.
Proof.
  intros.
  pose (n := seq.size p).
  pose (n1 := (n-1)%nat).
  assert (n = S n1).
  {
    generalize (monic_size_pos p H); lia.
  }
  unfold n in H2.
  rewrite H2.
  generalize (drop_poly_diff n1 q p); intros.
  apply H3.
  rewrite monic_drop_n_1; trivial.
  - rewrite monic_drop_n_1; trivial.
  - rewrite -H1 H2 //.
 Qed.
  
Lemma monic_divides_same_deg (p q : {poly R[i]}) :
  p \is monic ->
  q \is monic ->
  seq.size p = seq.size q ->
  Pdiv.Ring.rdvdp (R:=ComplexField.complex_unitRingType R_realFieldType)
                  p q ->
  p = q.
Proof.
  intros.
  generalize (Pdiv.RingMonic.rdivp_eq H q); intros.
  generalize (monic_dif_same_deg _ _ H H0 H1); intros.
  generalize (Pdiv.RingMonic.redivp_eq H 1 H4); intros.
  rewrite mul1r (addrC q _) addrA addrN add0r in H5.
  assert (Pdiv.CommonRing.rdivp (R:=ComplexField.complex_ringType R_fieldType) q p = 1).
  {
    unfold Pdiv.CommonRing.rdivp.
    by rewrite H5 /=.
  }
  rewrite H6 mul1r in H3.
  unfold Pdiv.Ring.rdvdp in H2.
  move=> /eqP in H2.
  rewrite H2 addr0 in H3.
  by symmetry.  
Qed.

Lemma seq_all_odd_roots n (p : {poly R[i]}) :
  let rs := MatrixFormula.seq_of_rV (odd_nth_roots n) in
  (forall i, root p (odd_nth_roots n 0 i)) ->
  seq.all (root p) (MatrixFormula.seq_of_rV (odd_nth_roots n)).
Proof.
  intros.
  apply/tuple.all_tnthP => /= i.
  rewrite finfun.tnth_fgraph /= finfun.ffunE.
  by apply H.
Qed.

Lemma odd_roots_uniq' n :
  forall i j,
    odd_nth_roots n 0 i = odd_nth_roots n 0 j ->
    i = j.
Proof.
  rewrite /odd_nth_roots => i j.
  rewrite !mxE.
  destruct (pow2_S (S n)) as [? eqq1].
  rewrite (eqP eqq1) => /nth_root_eq.
  rewrite -(eqP eqq1).
  rewrite !Nat.mod_small /=.
  - move/addIn => eqq2.
    apply/ord_inj.
    lia.
  - rewrite expnS.
    destruct i; destruct j; simpl in *.
    lia.
  - rewrite expnS.
    destruct i; destruct j; simpl in *.
    lia.
Qed.

Lemma odd_roots_uniq n :
  let rs := MatrixFormula.seq_of_rV (odd_nth_roots n) in
  uniq_roots (MatrixFormula.seq_of_rV (odd_nth_roots n)).
Proof.
  rewrite uniq_rootsE /= /odd_nth_roots.
  rewrite /MatrixFormula.seq_of_rV.
  apply /tuple.tuple_uniqP => i j.
  rewrite !finfun.tnth_fgraph !finfun.ffunE => eqq1.
  apply odd_roots_uniq' in eqq1.
  by apply enum_val_inj.
Qed.

Lemma odd_nth_roots_minpoly_mult n (p : {poly R[i]}) :
  (forall i, root p (odd_nth_roots n 0 i)) ->
  Pdiv.Ring.rmodp p ('X^(2^n) + 1%:P) = 0 .
Proof.
  intros roots.
  move: (seq_all_odd_roots n p roots) (odd_roots_uniq n) => allroot uniqroot.
  generalize (Pdiv.UnitRing.uniq_roots_rdvdp allroot uniqroot); intros.
  pose (rs := MatrixFormula.seq_of_rV (odd_nth_roots n)).
  assert  (\prod_(z <- rs) ('X - z%:P) = 'X^(2 ^ n) + 1%:P).
  {
   apply monic_divides_same_deg.
   - apply monic_prod_XsubC.
   - destruct (pow2_S n).
     rewrite (eqP i).
     apply Xn_add_c_monic.
   - rewrite size_prod_XsubC.
     destruct (pow2_S n).
     rewrite (eqP i).
     rewrite size_Xn_addC.
     rewrite -(eqP i).
     by rewrite MatrixFormula.size_seq_of_rV.
   - generalize (seq_all_odd_roots n _ (odd_nth_roots_minpoly n)); intros allroot2.
     apply (Pdiv.UnitRing.uniq_roots_rdvdp allroot2 uniqroot).
  }
  rewrite H0 in H.
  unfold Pdiv.Ring.rdvdp in H.
  by move=> /eqP in H.
 Qed.

Lemma map_RtoC_size (p : {poly R}) :
  seq.size p = seq.size (map_poly RtoC p).
Proof.
  by rewrite (size_map_poly RtoC_rmorphism p).
Qed.

Lemma map_RtoC_lead_coef (p : {poly R}) :
  lead_coef (map_poly RtoC p) = RtoC (lead_coef p).
Proof.
  by rewrite (lead_coef_map RtoC_rmorphism p). 
Qed.

Lemma rmodp_RtoC_morph : {morph (map_poly RtoC) : p q / Pdiv.Ring.rmodp p q }.
Proof.
  rewrite /Pdiv.Ring.rmodp => p q.
  by rewrite redivp_map.
Qed.

Lemma RtoC_inj : injective RtoC.
Proof.
  rewrite /RtoC=>a b.
  by move=> [].
Qed.

Lemma map_poly_RtoC_eq0E p : map_poly RtoC p = 0 <-> (p = 0).
Proof.
  split.
  - rewrite -(map_poly0 RtoC).
    move/map_inj_poly.
    apply => //.
    by apply RtoC_inj.
  - move=> ->.
    by rewrite map_poly0.
Qed.    

Lemma rmodp_R (p q : {poly R}) :
  Pdiv.Ring.rmodp p q = 0 <-> Pdiv.Ring.rmodp (map_poly RtoC p) (map_poly RtoC q) = 0.
Proof.
  rewrite -rmodp_RtoC_morph.
  symmetry.
  apply map_poly_RtoC_eq0E.
Qed.

Lemma map_poly_add_RtoC (p q : {poly R}) :
  map_poly RtoC (p + q) = (map_poly RtoC p) + (map_poly RtoC q).
Proof.
  apply (raddfD map_RtoC_rmorphism).
Qed.

Lemma map_RtoC_Xnpoly n :  
  map_poly (aR:=R_ringType) (rR:=ComplexField.complex_ringType R_fieldType) RtoC
    ('X^(2 ^ n) + 1%:P) = 'X^(2 ^ n) + 1%:P.
Proof.
  rewrite map_poly_add_RtoC map_polyXn.
  f_equal.
  by rewrite (map_polyC RtoC_rmorphism 1).
Qed.

Lemma odd_nth_roots_minpoly_mult_R n (p : {poly R}) :
  (forall i, root (map_poly RtoC p) (odd_nth_roots n 0 i)) ->
  Pdiv.Ring.rmodp p ('X^(2^n) + 1%:P) = 0.
Proof.
  intros.
  generalize (odd_nth_roots_minpoly_mult n (map_poly RtoC p) H); intros.
  rewrite rmodp_R.
  rewrite <- H0.
  f_equal.
  apply map_RtoC_Xnpoly.
Qed.

Lemma minpoly_mult_odd_nth_roots_R n (p : {poly R}) :
  Pdiv.Ring.rmodp p ('X^(2^n) + 1%:P) = 0 ->
  forall i, root (map_poly RtoC p) (odd_nth_roots n 0 i).
Proof.
  intros.
  rewrite rmodp_R in H.
  rewrite map_RtoC_Xnpoly in H.
  by  generalize (minpoly_mult_odd_nth_roots n (map_poly RtoC p) H).
Qed.  

Lemma odd_nth_roots_quot n (p : {poly R}) :
  mx_eval_ker_pred (odd_nth_roots' n) p <->
    princ_ideal_pred ('X^(2^n) + 1%:P) p.
Proof.
  unfold mx_eval_ker_pred, princ_ideal_pred.
  split; intros.
  - apply /eqP.
    apply odd_nth_roots_minpoly_mult_R.
    intros.
    move=> /eqP in H.    
    apply matrixP in H.
    unfold odd_nth_roots' in H.
    unfold odd_nth_roots.
    unfold root.
    destruct i.
    assert (m < (sval (pow2_S n)).+1) by (simpl; lia).
    specialize (H 0 (Ordinal H0)).
    simpl in H.
    rewrite !mxE in H.
    rewrite !mxE.
    replace  (2 * Ordinal (n:=2 ^ n) (m:=m) i + 1)%N with
      (2 * Ordinal (n:=(2 ^ n - 1).+1) (m:=m) H0 + 1)%N.
    + by rewrite H.
    + f_equal.
  - unfold zero;  simpl.
    unfold const_mx.
    apply /eqP.
    apply matrixP.
    intros ??.
    rewrite !mxE.
    move=> /eqP in H.
    generalize (minpoly_mult_odd_nth_roots_R n p H); intros.
    unfold pow2_S in y.
    destruct y as [y' ?].
    assert (y' < 2^n) by lia.
    specialize (H0 (Ordinal H1)).
    unfold root in H0.
    move=> /eqP in H0.
    simpl in H0.
    unfold odd_nth_roots in H0.
    rewrite mxE in H0.
    apply H0.
 Qed.


Section norms.

  Import matrix_ring.
  
  Implicit Types x y : R[i].

  Notation normc := ComplexField.Normc.normc.

  Definition norm1 {n} (v : 'rV[R[i]]_n):R := \sum_(j < n) normc (v 0 j).

  Definition norm_inf {n} (v : 'rV[R[i]]_n):R := \big[Order.max/0]_(j < n) normc (v 0 j).

  Definition coef_norm1 (p : {poly R}):R := \sum_(j < seq.size p) Rabs (p`_ j).

  Definition coef_maxnorm (p : {poly R}):R := \big[Order.max/0]_(j < seq.size p) Rabs (p`_ j).

  Definition canon_norm1 n (p : {poly R}):R := norm1 (mx_eval (odd_nth_roots' n) p).
  Definition canon_norm_inf n (p : {poly R}):R := norm_inf (mx_eval (odd_nth_roots' n) p).

  Lemma R00 : R0 = 0.
  Proof.
    by [].
  Qed.

  Lemma normc_nneg (x : R[i]) :
    (R0  <= normc x)%O.
  Proof.
    rewrite /normc.
    case: x => r i.
    apply ssrnum.Num.Theory.sqrtr_ge0.
  Qed.

  Lemma normc_nnegR (x : R[i]) :
    Rle R0 (normc x).
  Proof.
    move: (normc_nneg x).
    rewrite /Order.le /=.
    by move/RlebP.
  Qed.

  Lemma maxrM (c a b : R) : Rle 0 c -> Order.max (c * a) (c * b)  = c * Order.max a b.
  Proof.
    rewrite /Order.max /Order.lt /=.
    (repeat case: RltbP); try lra; intros.
    - destruct H.
      + apply Rmult_lt_reg_l in p => //.
      + subst.
        by rewrite !mul0r.
    - destruct H.
      + elim n.
        by apply Rmult_lt_compat_l.
      + subst.
        by rewrite !mul0r.
  Qed.

  Lemma norm_infZ {n} (c : R[i]) (v : 'rV[R[i]]_n) :
    norm_inf (c *: v) = (normc c) * norm_inf v.
  Proof.
    rewrite /norm_inf.
    apply (big_rec2 (fun a b => a = normc c * b)).
    - by rewrite mulr0.
    - move=> i a b _ ->.
      rewrite mxE ComplexField.Normc.normcM maxrM //.
      apply normc_nnegR.
  Qed.

  Lemma norm_inf_nneg {n} (v : 'rV[R[i]]_n) :
    (@zero R_ringType <= norm_inf v)%O.
  Proof.
    rewrite /norm_inf.
    apply big_rec => //= i x _ xn.
    by rewrite Order.TotalTheory.le_maxr xn orbT.
  Qed.

  Lemma normc_triang (x y : R[i]) :
    (normc (x + y) <= normc x + normc y)%O.
  Proof.
    generalize (ComplexField.lec_normD x y); intros.    
    rewrite /ComplexField.lec /= addr0 in H.
    move => /andP in H.
    by destruct H.
  Qed.

  Lemma normc_triangR (x y : R[i]) :
    Rle (normc (x + y)) (normc x + normc y).
  Proof.
    move: (normc_triang x y) => /=.
    rewrite /Order.le /Order.POrder.le /=.
    by move/RleP.
  Qed.

  Lemma bigmaxr_le_init {n} (v : 'rV[R[i]]_n) init (f:R[i]->R):
    Order.le init (\big[Order.max/init]_(j < n) f (v 0 j)).
  Proof.
    rewrite BigOp.bigopE.
    unlock reducebig.
    elim: (index_enum _) => /=.
    - by exact: Order.POrderTheory.lexx.
    - move=> a l.
      rewrite Order.TotalTheory.le_maxr => ->.
      by rewrite orbT.
  Qed.

  Lemma omax_l {disp : Datatypes.unit} {T : porderType disp} (x y:T) :  Order.le x (Order.max x y).
  Proof.
    rewrite Order.POrderTheory.maxEle.
    by case_eq (Order.le x y).
  Qed.

  Lemma omax_r {disp : Datatypes.unit} {T : orderType disp} (x y:T) :  Order.le y (Order.max x y).
  Proof.
    rewrite Order.POrderTheory.maxElt.
    case_eq (Order.lt x y) => //.
    rewrite (Order.TotalTheory.leNgt y x).
    by move/negbT.
  Qed.

  Lemma omax_l_real (x y:R) :  Rleb x (Order.max x y).
  Proof.
    by exact: (omax_l x y).
  Qed.

  Lemma omax_r_real (x y:R) :  Rleb y (Order.max x y).
  Proof.
    by exact: (omax_r x y).
  Qed.

  Lemma bigmaxr_le {n} (v : 'rV[R[i]]_n) init f i:
    Rleb (f (v 0 i)) (\big[Order.max/init]_(j < n) f (v 0 j)).
  Proof.
    rewrite BigOp.bigopE.
    unlock reducebig.
    move: (mem_index_enum i).
    elim: (index_enum _) => /= [| a l IHl].
    - by rewrite seq.in_nil.
    - rewrite seq.in_cons => /orP [/eqP->| ].
      + by exact: omax_l_real.
      + move=> inn.
        move: (IHl inn) => /RlebP=>le1.
        apply/RlebP.
        eapply Rle_trans; try apply le1.
        apply/RlebP.
        apply omax_r_real.
  Qed.
  
  Lemma bigmax_normc_nneg {n} (v : 'rV[R[i]]_n):
    Rleb 0 (\big[Order.max/0]_(j < n) normc (v 0 j)).
  Proof.
    apply big_rec.
    - apply /RlebP.
      unfold zero; simpl.
      lra.
    - intros.
      assert  ((zero R_ringType) <= Order.max (normc (R:=R_rcfType) (v 0 i)) x)%O.
      {
        rewrite Order.TotalTheory.le_maxr.      
        apply /orP.
        left.
        apply normc_nneg.
      }
      by rewrite /Order.le /= in H1.
   Qed.

  Lemma norm_inf_triang {n} (v1 v2 : 'rV[R[i]]_n) :
    (norm_inf (v1 + v2) <= norm_inf v1 + norm_inf v2)%O.
  Proof.
    rewrite /norm_inf.
    apply big_rec.
    - unfold Order.le; simpl.
      apply /RlebP.
      erewrite <- addr0 at 1.
      apply Rplus_le_compat; apply /RlebP; apply bigmax_normc_nneg.
    - intros i x _ xn.
      rewrite Order.TotalTheory.le_maxl.
      generalize (normc_triang (v1 0 i) (v2 0 i)); intros.
      rewrite mxE.
      apply /andP; split; trivial.
      unfold Order.le in *; simpl in *.
      apply /RlebP.
      move => /RlebP in H.
      eapply Rle_trans.
      apply H.
      apply Rplus_le_compat; apply /RlebP; apply bigmaxr_le.
   Qed.

  Lemma norm_inf_semi_multiplicative {n} (v1 v2 : 'rV[R[i]]_n) :
    (norm_inf (map2_mx (fun (a b : R[i]) => a * b) v1 v2) <= norm_inf v1 * norm_inf v2)%O.
  Proof.
    rewrite /norm_inf.
    apply big_rec.
    - unfold Order.le, zero, mul; simpl.
      apply /RlebP.
      generalize (Rmult_0_r 0); intros.
      rewrite -H.
      apply Rmult_le_compat; try lra; apply /RlebP; rewrite Rmult_0_r; apply bigmax_normc_nneg.
    - intros i x _ xn.
      rewrite Order.TotalTheory.le_maxl.
      rewrite mxE ComplexField.Normc.normcM.
      apply /andP; split; trivial.
      clear x xn.
      unfold Order.le; simpl.
      apply /RlebP.
      apply Rmult_le_compat; try apply normc_nnegR; apply /RlebP; apply bigmaxr_le.
   Qed.

  Lemma norm_inf_pos_def {n} (v : 'rV[R[i]]_n) :
    norm_inf v = 0 -> v = 0.
  Proof.
    rewrite /norm_inf => HH.
    apply /matrixP => a b.
    move: (ord1 a)->.
    move: (bigmaxr_le v 0 (@normc _) b).
    rewrite {}HH.
    move/RlebP => HH.
    rewrite [v 0 b]ComplexField.eq0_normC ?mxE//.
    move: (normc_nnegR (v 0 b)) => HH2.
    rewrite R00 in HH2.
    rewrite /zero /=.
    f_equal.
    now apply Rle_antisym.
  Qed.

  Lemma normc_Rabs (r : R) :
    normc (RtoC r) = Rabs r.
  Proof.
    rewrite /normc /RtoC R00 (expr2 0) mulr0 addr0.
    by rewrite ssrnum.Num.Theory.sqrtr_sqr.
  Qed.

  Lemma mx_evalZ {n} (v : 'rV[R[i]]_n.+1) (r:R) p : mx_eval v (r *: p) = (RtoC r) *: (mx_eval v p).
  Proof.
    apply matrixP => a b.
    rewrite !mxE /scale /= scale_polyE.
    rewrite rmorphismMP /=.
    rewrite (map_polyC RtoC_rmorphism) /=.
    rewrite -hornerZ /=.
    by rewrite /scale /= scale_polyE.
  Qed.

  (* following 4 lemmas show canon_norm_inf is a norm on quotient by x^+(2^n) + 1 *)
  Lemma canon_norm_infZ n (r : R) (p : {poly R}) :
    canon_norm_inf n (r *: p) = Rabs r * canon_norm_inf n p.
  Proof.
    by rewrite /canon_norm_inf !mx_evalZ norm_infZ normc_Rabs.
  Qed.

  Lemma canon_norm_inf_nneg n (p : {poly R}) :
    (@zero R_ringType <= canon_norm_inf n p)%O.
  Proof.
    apply norm_inf_nneg.
  Qed.

  Lemma canon_norm_inf_triang n (p q : {poly R}) :
    (canon_norm_inf n (p + q) <= canon_norm_inf n p + canon_norm_inf n q)%O.
  Proof.
    unfold canon_norm_inf.
    generalize (raddfD (mx_eval_rmorphism (odd_nth_roots' n))); intros.
    specialize (H p q); simpl in H.
    rewrite H.
    apply norm_inf_triang.
  Qed.
      
  Lemma canon_norm_inf_semi_multiplicative n (p q : {poly R}) :
    (canon_norm_inf n (p * q) <= canon_norm_inf n p * canon_norm_inf n q)%O.
    unfold canon_norm_inf.
    generalize (rmorphM (mx_eval_rmorphism (odd_nth_roots' n))); intros.
    specialize (H p q); simpl in H.
    rewrite H.
    apply norm_inf_semi_multiplicative.
 Qed.

(* following only holds on quotient ring by x^+(2^n) + 1 
  Lemma canon_norm_inf_pos_def n p :
    canon_norm_inf n p = 0 -> p = 0.
*)

  Lemma normc_conj (x : R[i]) :
    ComplexField.Normc.normc x = ComplexField.Normc.normc (conjc x).
  Proof.
    generalize normcJ.
    destruct x.
    simpl.
    do 2 f_equal.
    by rewrite sqrrN.
  Qed.

  Lemma normc_conj_mul (x y : R[i]) :
    normc (x * y) = normc (x * (conjc y)).
  Proof.
    do 2 rewrite ComplexField.Normc.normcM.
    by rewrite (normc_conj y).
  Qed.
    
  Lemma normc_conj_add (r : R) (x y : R[i]) :
    normc (x + y) = normc (conjc x + conjc y).
  Proof.
    by rewrite add_conj normc_conj.
  Qed.

  Lemma normc_conj_exp (x : R[i]) n :
    normc (x ^+ n) = normc ((conjc x) ^+ n).
  Proof.
    by rewrite -exp_conj normc_conj.
  Qed.

  Lemma RtoC1 : RtoC 1 = 1.
  Proof.
    by [].
  Qed.

  Lemma RtoC0E (c:R) : (RtoC c == 0) = (c == 0).
  Proof.
    by rewrite /RtoC !eqE /= !eqE /= R00 eqxx !andbT.
  Qed.

  Lemma RtoC_real a : RtoC a \is ssrnum.Num.real.
  Proof.
    by rewrite complex_real.
  Qed.

  Lemma conjc_id (a:R[i]) :  (a^* = a)%C <-> (a \is ssrnum.Num.real).
  Proof.
    split.
    - move/Cconj_im_0 => eqq.
      apply/ssrnum.Num.Theory.Creal_ImP.
      by rewrite -complexIm /= eqq.
    - rewrite /in_mem/mem /= /Order.le /=.
      case: a => ra ia /= /orP-[/andP-[/eqP-> _]|/andP-[/eqP<- _]]
                ; by rewrite oppr0.
  Qed.      

  Lemma conjc_RtoC a : ((RtoC a)^* )%C = RtoC a.
  Proof.
    by rewrite /RtoC /= oppr0.
  Qed.    
    
  Lemma rpoly_eval_conj (p : {poly R}) (x : R[i]) :
    let pc := map_poly RtoC p in 
    conjc (pc.[x]) = pc.[conjc x].
  Proof.
    case: p => l llast.
    rewrite /horner /= !map_polyE /=.
    have/PolyK->: seq.last (RtoC 1) (seq.map RtoC l) != 0
      by rewrite seq.last_map RtoC0E.
    move => {llast}.
    elim: l => /=.
    - by rewrite oppr0.
    - move=> a l <-.
      by rewrite -add_conj -mul_conj conjc_RtoC.
  Qed.

  Lemma normc_conj_poly (p : {poly R}) (x : R[i]) :
    let pc := map_poly RtoC p in 
    normc (pc.[x]) = normc (pc.[conjc x]).
  Proof.
    simpl.
    by rewrite -rpoly_eval_conj normc_conj.
  Qed.

End norms.

Lemma pmat_normc_1 (n : nat) :
  let pmat := peval_mat (odd_nth_roots (S n)) in
  forall i j,
    Cmod (pmat i j) = 1.
Proof.
  simpl; intros.
  unfold peval_mat, odd_nth_roots.
  rewrite !mxE.
  destruct (pow2_S (n.+2)).
  move => /eqP in i0.
  by rewrite i0 Cpow_nth_root nth_root_Cmod.
Qed.

Definition coefE :=
  (coef0, coef1, coefC, coefX, coefXn, coef_sumMXn,
   coefZ, coefMC, coefCM, coefXnM, coefMXn, coefXM, coefMX, coefMNn, coefMn,
   coefN, coefB, coefD, coef_even_poly, coef_odd_poly,
   coef_take_poly, coef_drop_poly, coef_cons, coef_Poly, coef_poly,
   coef_deriv, coef_nderivn, coef_derivn, coef_map, coef_sum,
   coef_comp_poly_Xn, coef_comp_poly).

Lemma Cmod_normc (c : R[i]) :
  Cmod c = ComplexField.Normc.normc c.
Proof.
  unfold Cmod, ComplexField.Normc.normc.
  destruct c.
  rewrite RsqrtE//.
  apply ssrnum.Num.Theory.addr_ge0; apply ssrnum.Num.Theory.sqr_ge0.
Qed.

Lemma Cmod_triang (x y : R[i]) :
  Rle (Cmod (x + y)) (Cmod x + Cmod y).
Proof.
  rewrite !Cmod_normc.
  by apply normc_triangR.
Qed.

Lemma Cmod_mul (c1 c2 : R[i]):
  Cmod (c1 * c2) = (Cmod c1) * (Cmod c2).
Proof.
  by rewrite !Cmod_normc ComplexField.Normc.normcM.
Qed.

Lemma cmod_1_delta (c1 c2 : R[i]) (delta : R) :
  Cmod c1 = 1 ->
  Rlt (Cmod c2) delta ->
  Rlt (Cmod (c1 * c2)) delta.
Proof.
  intros.
  by rewrite Cmod_mul H mul1r.
Qed.
  
Lemma root_eval_bound_cpoly (c : R[i]) (p : {poly R[i]}) (δ : R) :
  Rle 0 δ ->
  Cmod c = 1 ->
  (forall i, Rle (Cmod (p`_ i)) δ) ->
  Rle (Cmod (p.[c])) (δ *+ (seq.size p)).
Proof.
  intros δnneg Cnorm1 coeffsmall.
  rewrite -{1}[p]polyseqK horner_Poly.
  move: (polyseq p) coeffsmall => {p}.
  elim.
  - move=> _/=.
    rewrite mulr0n expr0n /= !mulr0n Rplus_0_l sqrt_0.
    by apply Rle_refl.
  - move=> a l IHl coeffsmall /=.
    rewrite mulrS [δ + _]addrC.
    rewrite !Cmod_normc.
    eapply Rle_trans; [apply normc_triangR | ].
    rewrite ComplexField.Normc.normcM.
    rewrite -!Cmod_normc Cnorm1 mulr1.
    rewrite /add /=.
    apply Rplus_le_compat.
    + apply IHl.
      move=>i.
      by move: coeffsmall => /(_ (i.+1))/=.
    + by move: coeffsmall => /(_ O) /= //.
Qed.

Lemma RtoC_real_complex (r : R) :
  RtoC r = real_complex _ r.
Proof.
  reflexivity.
Qed.

Lemma Cmod_Rabs (r : R) :
  Cmod (RtoC r) = Rabs r.
Proof.
  rewrite RtoC_real_complex /Cmod /=.
  rewrite (expr2 0) mulr0 Rplus_0_r.
  generalize (pow2_inv r (r^+ 2)); intros.
  by rewrite H.
Qed.

Lemma Cmod_0 :
  Cmod 0 = 0.
Proof.
  unfold Cmod. simpl.
  by rewrite !expr2 !mulr0 Rplus_0_r sqrt_0.
Qed.

Lemma root_eval_bound (c : R[i]) (p : {poly R}) (δ : R) :
  Rle 0 δ ->
  Cmod c = 1 ->
  (forall i, Rle (Rabs (p`_ i)) δ) ->
  Rle (Cmod (map_poly RtoC p).[c])  (δ *+ seq.size p).
Proof.
  intros.
  generalize (root_eval_bound_cpoly c (map_poly RtoC p) δ H H0); intros.
  rewrite (size_map_poly RtoC_rmorphism p) in H2.
  apply H2; intros.
  rewrite coefE.
  destruct (i < seq.size p)%N.
  - by rewrite Cmod_Rabs.
  - by rewrite Cmod_0.
Qed.    

Lemma Cmod_sum (n : nat) (cl : 'I_n -> R[i]) :
  Rle (Cmod (\sum_i cl i)) (\sum_i (Cmod (cl i))).
Proof.
  simpl.
  elim: (index_enum (ordinal_finType n)) => /=.
  - rewrite !big_nil /=.
    rewrite !expr2 !mulr0 Rplus_0_r sqrt_0.
    by apply Rle_refl.
  - move=> a l IHl.
    rewrite !big_cons /=.
    eapply Rle_trans; [ apply Cmod_triang |].
    apply Rplus_le_compat; trivial.
    by apply Rle_refl.
Qed.  

Lemma const_sum (n : nat) (δ : R) :
  \sum_(i < n) δ = n%:R * δ.
Proof.
  rewrite big_const_ord.
  induction n.
  + by rewrite /= mul0r.
  + by rewrite /= IHn mulrS mulrDl mul1r.
Qed.

Lemma leq_sum_R [I : Type] (r : list I) [P : pred I] [E1 E2 : I -> R] :
  (forall i : I, P i -> Rle (E1 i) (E2 i)) ->
  Rle (\sum_(i <- r | P i) E1 i) (\sum_(i <- r | P i) E2 i).
Proof.
  apply big_ind2.
  - by right.
  - by apply Rplus_le_compat.
Qed.

Lemma bounded_sum (n : nat) (cl : 'I_n -> R) (δ : R) :
  Rle 0 δ ->
  (forall i, Rle (cl i) δ) ->
  Rle (\sum_i cl i) (n%:R * δ).
Proof.
  intros.
  apply Rle_trans with (r2 := \sum_(i < n) δ).
  - by apply leq_sum_R.
  - right.
    by apply const_sum.
 Qed.

Lemma Cabs_sum_bound (n : nat) (cl : 'I_n -> R[i]) (δ : R) :
  Rle 0 δ ->
  (forall i, Rle (Cmod (cl i)) δ) ->
  Rle (Cmod (\sum_i cl i)) (n%:R * δ).
Proof.
  intros.
  eapply Rle_trans.
  apply Cmod_sum.
  by apply bounded_sum.
Qed.

Lemma decode_delta (n : nat) (cl : 'cV[R[i]]_(2^(S n))) (δ : R) :
  Rle 0 δ ->
  let pmat := peval_mat (odd_nth_roots (S n)) in
  (forall i, Rle (Cmod (cl i 0)) δ) ->
  forall i, Rle (Cmod ((pmat *m cl) i 0)) ((2^S n)%:R * δ).
Proof.
  simpl; intros.
  rewrite !mxE.
  apply Cabs_sum_bound; trivial.
  intros.
  by rewrite Cmod_mul pmat_normc_1 mul1r.
 Qed.

Section unity.
  Variable (T : comRingType).
  Variable (z : T).

  Lemma two_pow_prim_root (n:N) :
    (one T) <> -(one T) ->
    z ^+ (2^n) = -1 ->
    primitive_root_of_unity (2^(n.+1)) z.
  Proof.
    intros onem1 zpowm1.
    assert (root_of_unity (2^(n.+1)) z).
    {
      apply /unity_rootP.
      by rewrite expnSr exprM zpowm1 expr2 mulrNN mulr1.
    }
    destruct (@prim_order_exists _ (2^(n.+1)) z).
    - destruct (pow2_S (n.+1)).
      move=> /eqP in i.
      by rewrite i.
    - by apply /unity_rootP.
    - assert (exists (k:nat), x = expn 2 k).
      {
        move=> /prime.dvdn_pfactor in i0.
        destruct i0.
          by reflexivity.
        by exists x0.
      }
      move: H0 i0 i => [x0 ->] i0 i.
      have HH: x0 = n.+1.
      {
        move: i0.
        rewrite div.dvdn_Pexp2l; try lia.
        rewrite leq_eqVlt => /orP-[/eqP//|x0lt].
        assert (HH:expn 2 n = muln (expn 2 x0) (expn 2 (n - x0))).
        {
          rewrite -expnD.
          f_equal.
          lia.
        }
        rewrite HH exprM (prim_expr_order i) Theory.expr1n in zpowm1.
        tauto.
      }
      by rewrite HH in i.
  Qed.

  Lemma odd_pow_prim_root (n:N) :
    z ^+ (2^n) = -1 ->
    forall j,
      odd j ->
      ((z ^+ j) ^+ (2^n)) = -1.
  Proof.    
    intros.
    by rewrite exprAC H -signr_odd H0 /= expr1.
  Qed.

  Lemma gcd_odd_pow2 j n :
    odd j ->
    (div.gcdn j (2 ^ (S n)) = 1)%N.
  Proof.
    intros.
    generalize (div.coprime2n j); intros.
    assert (div.gcdn j 2 = 1%N).
    {
      rewrite H in H0.
      unfold div.coprime in H0.
      move => /eqP in H0.
      by rewrite div.gcdnC.
    }
    induction n; trivial.
    rewrite expnS.
    assert (div.coprime j 2).
    {
      unfold div.coprime.
      by apply /eqP.
    }
    now rewrite (@div.Gauss_gcdr j 2).
  Qed.

  Lemma pow2_odd_inv (j n :N) :
    odd j ->
    {k | (j * k mod (2^(S n)) = 1)%N}.
  Proof.
    intros.
    assert (0 < j) by lia.
    destruct (div.egcdnP (2^(S n)) H0).
    exists km.
    rewrite mulnC e addnC Nat.mod_add; try lia.
    rewrite (gcd_odd_pow2 j n H).
    apply Nat.mod_small.
    destruct (pow2_S n).
    move => /eqP in i0.
    rewrite expnS i0; lia.
  Qed.

  Lemma odd_pow_prim_root_inv (j n:N) :
    odd j ->
    exists k,
    forall (z2:T),
      z2 ^+ (2^n) = -1 ->
      ((z2 ^+ j) ^+ k) = z2.
  Proof.
    intros.
    assert (2^(S n) <> 0)%N.
    {
      destruct (pow2_S (S n)).
      move => /eqP in i.
      rewrite i.
      lia.
    }
    generalize (pow2_odd_inv j n H); intros.
    destruct H1 as [k ?].
    exists k.
    intros.
    assert (z2 ^+ (2 ^ (S n)) = 1).
    {
      by rewrite expnS mulnC exprM H1 expr2 mulrNN mulr1.
    }
    rewrite -exprM.
    rewrite (Nat.div_mod (j * k) _ H0) e.
    by rewrite exprD exprM H2 expr1 Theory.expr1n mul1r.
  Qed.

  Lemma odd_pow_prim_inv (n:N) :
    z ^+ (2^n) = -1 ->
    forall j,
      ((z ^+ j) ^+ (2^(S n) -1)) * (z ^+ j) = 1.
  Proof.
    intros.
    rewrite -exprM -exprD /= -{2}(muln1 j) -mulnDr mulnC exprM.
    rewrite addBnCAC; try lia.
    by rewrite subnn add0n expnS mulnC exprM H expr2 mulrNN mulr1 expr1n.
  Qed.    

  Lemma odd_pow_prim_root_inj (j n:N) (z2 : T) :
    z ^+ (2^n) = -1 ->
    z2 ^+ (2^n) = -1 ->
    z <> z2 ->
    odd j ->
    z ^+ j <> z2 ^+ j.
  Proof.
    intros.
    unfold not; intros.
    destruct (odd_pow_prim_root_inv j n H2) as [k ?].
    apply H4 in H.
    apply H4 in H0.
    apply (f_equal (fun z => z ^+k)) in H3.
    by rewrite H H0 in H3.
  Qed.

  Lemma injective_finite_bijective {S} (l : list S) (f : S -> S) :
    NoDup l ->
    (forall s, In s l -> In (f s) l) ->
    injective f ->
    forall s, In s l <-> In s (map f l).
  Proof.
    intros.
    split; intros.
    - assert (NoDup (map f l)).
      {
        now apply FinFun.Injective_map_NoDup.  
      }
      assert (incl l (map f l)).
      {
        apply NoDup_length_incl; trivial.
        - now rewrite map_length.
        - intros ??.
          apply in_map_iff in H4.
          destruct H4 as [? [??]].
          specialize (H0 x H5).
          now rewrite H4 in H0.
      }
      now apply H4.
    - apply in_map_iff in H2.
      destruct H2 as [? [??]].
      rewrite -H2.
      now apply H0.
  Qed.

  Lemma injective_finite_permutation {S} (l : list S) (f : S -> S) :
    NoDup l ->
    (forall s, In s l -> In (f s) l) ->
    injective f ->
    Permutation l (map f l).
  Proof.
    intros.
    apply NoDup_Permutation; trivial.
    - now apply FinFun.Injective_map_NoDup.
    - now apply injective_finite_bijective.
  Qed.

  Lemma char_2_opp_eq :
    one T = - (one T) <-> 2%N \in [char T].
  Proof.
    unfold mem, in_mem; simpl.
    rewrite mulr2n.
    split;intros.
    - apply (f_equal (fun (z : T) => 1 + z)) in H.
      rewrite addrN in H.
      by rewrite H.
    - move=> /eqP in H.
      apply (f_equal (fun (z : T) => z - 1)) in H.
      by rewrite add0r -addrA addrN addr0 in H.
  Qed.

  End unity.
      
