Require Import Reals Lra Lia List.
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
  under eq_big_seq.
  - apply ssrbool.in1W; intros.
    rewrite peval_row.
    unfold odd_nth_roots.
    rewrite !mxE.
    destruct (pow2_S (S (S n))).
    rewrite H pow_nth_root mult_conj_root.
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
  rewrite <- H1.
  - rewrite <- H0.
    erewrite eq_big_seq; [reflexivity |].
    simpl.
    apply ssrbool.in1W; intros.
    repeat rewrite mxE.
    rewrite exprMn_comm.
    + rewrite exp_conj//.
    + rewrite /comm mulrC//.
  - unfold not; intros.
    destruct (pow2_S (S (S n))).
    rewrite H3 in H2.
    rewrite nth_root_conj_alt in H2.
    rewrite nth_root_mul in H2.
    apply nth_root_1_iff in H2.
    rewrite <- H3 in H2.
    clear H0 H1 H3 pmat x x0.
    destruct n1 as [x xlt]; destruct n2 as [y ylt]; simpl in *.
    assert (neq:x <> y).
    {
      intros HH.
      apply H; subst.
      f_equal; apply eqtype.bool_irrelevance.
    }
    clear H.
    rewrite !modulo_modn !plusE !minusE in H2.
    apply (f_equal ssrint.Posz) in H2.
    revert H2.
    rewrite -intdiv.modz_nat ssrint.PoszD -ssrint.subzn.
    + rewrite -intdiv.modz_nat.
      rewrite -intdiv.modzDm.
      rewrite !addn1 intdiv.modzDl intdiv.modzNm.
      rewrite !intdiv.modzDm.
      rewrite expnSr.
      destruct (@leP x y).
      * rewrite -intdiv.modzDl intdiv.modz_small/=; lia.
      * rewrite intdiv.modz_small/=; lia.
    + lia.
  - destruct (pow2_S (S (S n))).
    rewrite H2.
    rewrite nth_root_conj_alt.
    rewrite nth_root_mul.
    rewrite Cpow_nth_root.
    apply nth_root_1_iff.
    rewrite <- H2.
    rewrite <- H0.
    clear H0 H1 H2 pmat x x0.
    destruct n1 as [x xlt]; destruct n2 as [y ylt]; simpl in *.
    assert (neq:x <> y).
    {
      intros HH.
      apply H; subst.
      f_equal; apply eqtype.bool_irrelevance.
    }
    clear H.
    rewrite !modulo_modn !plusE !minusE.
    replace (expn 2 (S (S n))) with (expn 2 (S n) * 2)%nat by (rewrite (expnS _ (S n)); lia).
    rewrite <- div.muln_modr.
    rewrite -div.modnDm.
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
  rewrite H.
  do 2 rewrite pow_nth_root.
  rewrite nth_root_mul.
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
  rewrite H.
  rewrite pow_nth_root.
  rewrite <- exp_conj.
  rewrite mul_conj.
  f_equal.
  rewrite pow_nth_root.
  rewrite nth_root_mul.
  f_equal.
  lia.
Qed.

Definition vector_rev {n} {T}  (v : 'rV[T]_n) :=
  \row_(i < n) v I0 (rev_ord i).

Definition vector_rev_conj {n} (v : 'rV[R[i]]_n) :=
  forall i,
    v I0 i = conjc (v I0 (rev_ord i)).
  
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
    Im ((v + vector_rev v) I0 i) = 0.
Proof.
  intros.
  rewrite /vector_rev !mxE H rev_ordK.
  apply Cconj_im_0.
  rewrite -add_conj conjcK addrC//.
Qed.

Lemma vector_rev_reflect {n} (v : 'rV[R[i]]_n) i :
  vector_rev v I0 i = v I0 (rev_ord i).
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
  cut (\sum_(j < n) (a I0 j + b I0 j) = \sum_(j < n) a I0 j + \sum_(j < n) b I0 j).
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
  (forall i, Im (v I0 i) = 0) -> 
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
  rewrite H.
  rewrite nth_root_conj_alt.
  f_equal.
  rewrite <- H.
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
    Im ((mat *m cl) i I0) = 0.
Proof.
  intros.
  replace ((mat *m cl) i I0) with (((row i mat) *m cl) I0 I0).
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
    Im ((encmat *m cl) i I0) = 0.
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
  apply matrixP; intros ??.
  generalize (mat_encode_real cl H x); intros.
  apply Re_Im_0 in H0.
  unfold encmat, pmat.
  assert (I0 = y).
  {
    destruct I0; destruct y.
    assert (m = m0) by lia.
    subst.
    f_equal.
    apply eqtype.bool_irrelevance.    
  }
  rewrite <- H1, H0.
  now repeat rewrite mxE.
Qed.

Definition vector_rev_col {n} {T}  (v : 'cV[T]_n) :=
  \col_(i < n) v (rev_ord i) I0.

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

From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv ssrint zmodp eqtype ssrbool.

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

Lemma poly_rem_xn (n : nat) (c : int) (a : {poly int}) :
  let p := 'X^n.+1 + polyC c in
  a %% p = take_poly n.+1 a + (-c)*: (drop_poly n.+1 a %% p).
Proof.
  simpl.
  assert (lead_coef ('X^n.+1 + c%:P) \is a unit).
  {
    rewrite lead_coefDl.
    + rewrite lead_coefXn /in_mem /mem //.
    + rewrite size_polyXn.
      generalize (size_polyC_leq1 c); lia.
  }
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
    rewrite H1 mulrC -Pdiv.IdomainUnit.modpZl; trivial.
    f_equal.
    rewrite -mul_polyC.
    f_equal.
    rewrite polyCN //.
Qed.

Require Import Recdef.
Function poly_rem_xn_1 (n : nat) (a : {poly int}) {measure seq.size a} : {poly int} :=
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

Lemma poly_rem_xn_id n (a:{poly int}) : seq.size a <= n.+1 ->
  poly_rem_xn_1 n a = a.
Proof.
  functional induction poly_rem_xn_1 n a => slt.
  - rewrite take_poly_id//.
  - rewrite drop_poly_eq0// eqxx// in y.
Qed.    

Lemma poly_rem_xn_1_le n a : is_true (seq.size (poly_rem_xn_1 n a) <= n.+1).
Proof.
  functional induction poly_rem_xn_1 n a.
  - rewrite size_take_poly//. 
  - rewrite (leq_trans (size_add _ _)) // size_opp geq_max IHp size_take_poly//.
 Qed.

Definition vector_proj_coef {n} (v1 v2 : 'rV[R[i]]_n) :=
  (H_inner_prod v1 v2) / (H_inner_prod v2 v2).

Definition equiv_xn_1 (n : nat): rel {poly int} :=
  fun p => fun q => poly_rem_xn_1 n (p - q) == 0.

Definition poly_rem_xn_1_ringT (n : nat) :=
  ringQuotType (equiv_xn_1 n) 0 (@opp _) (@add _) 1 (@mul _).

Definition ideal_xn_1_pred (n : nat) : pred (poly_zmodType int_Ring) :=
  fun p => poly_rem_xn_1 n p == 0.

Lemma poly_rem_xn_1_1 n :
  poly_rem_xn_1 n 1 = 1.
Proof.
  apply poly_rem_xn_id.
  rewrite size_poly1//.
Qed.

Lemma ideal_xn_1_pred_proper n : proper_ideal (ideal_xn_1_pred n).
Proof.
  unfold proper_ideal.
  split.
  - unfold in_mem, mem; simpl.
    unfold ideal_xn_1_pred.
    rewrite poly_rem_xn_1_1.
    admit.
  - intros ???.
    unfold in_mem, mem in *.
    simpl in *.
    unfold ideal_xn_1_pred in *.
    admit.
 Admitted.

Lemma ideal_xn_1_pred_zmod n : zmodPred (ideal_xn_1_pred n).
Proof.
  apply Pred.Zmod.
  - admit.
  - admit.
Admitted.

Section polyops.

  Context {iT:idomainType}.
  
  Definition monic_poly := {p:{poly iT} | (lead_coef p \is a unit) && (seq.size p > 1)}.

  Definition princ_ideal_pred (p : {poly iT}) : pred {poly iT} :=
  fun q => q %% p == 0.

Lemma princ_ideal_proper (p : monic_poly) :
  proper_ideal (princ_ideal_pred (val p)).
Proof.
  intros.
  unfold proper_ideal, princ_ideal_pred, in_mem, mem; split; simpl.
  - rewrite modp_small.
    + rewrite poly1_neq0//.
    + destruct (andP (valP p)).
      rewrite size_poly1 H0 //.
  - intros ??.
    rewrite -Pdiv.IdomainUnit.modp_mul// /in_mem/=.
    move => /eqP->.
    rewrite mulr0 mod0p//.
    now destruct (andP (valP p)).
Qed.

Lemma princ_ideal_zmod (p : monic_poly) :
  zmodPred (princ_ideal_pred (val p)).
Proof.
  constructor.
  - constructor; [constructor|].
    constructor.
    + rewrite /in_mem //= /princ_ideal_pred mod0p//.
    + rewrite /in_mem //= /prop_in2 /princ_ideal_pred => a b.
      rewrite /in_mem /mem Pdiv.IdomainUnit.modpD // /=.
      * move=> /eqP-> /eqP->.
        rewrite addr0//.
      * now destruct (andP (valP p)).
  - rewrite /Pred.Exports.oppr_closed /mem /= /princ_ideal_pred => a.
    rewrite /in_mem /= => /eqP-eqq1.
    destruct (andP (valP p)).
    rewrite Pdiv.IdomainUnit.modpN // eqq1 oppr0 //.
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

  Definition lift (a : {poly iT}) : qring p
    := lift_cst (qring p) a.

  Local Open Scope quotient_scope.

  Example something (a b : {poly iT}) := a == b %[mod (qring p)].

End example.

End polyops.

(*
Definition princ_ideal_opp (p : {poly iT}) (pn:seq.size p > 1) :
  opp (princ_ideal_pred p).
 *)

(*
Definition qring (p : {poly iT}) (lc:lead_coef p \is a unit) (pn:seq.size p > 1):=
  { ideal_quot  (DefaultKeying.default_keyed_pred (princ_ideal_pred p) ) }.
*)


(*
Lemma nth_root_odd_project  (n : nat) (cl : Vector C (2^(S n))) :
  cl = fold_right vector_Cplus (vector_Czero (2^(S n)))
         (map (fun e => 
                 let b := vmap' (fun c => Cpow c e) (V_odd_nth_roots (S n)) in
                 Vscale (vector_proj_coef cl b) b) 
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
    

