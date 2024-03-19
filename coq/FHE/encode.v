Require Import Reals Lra Lia List Permutation.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix Rstruct complex seq fingroup.
From mathcomp Require Import ssralg ssrfun.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv ssrint zmodp eqtype ssrbool div.

Import ssralg.GRing.
Require Import nth_root.

Ltac coq_lra := lra.
From mathcomp Require Import lra.

Set Bullet Behavior "Strict Subproofs".


Lemma INR0eq (n:nat) : (INR n == 0%R) = (n == 0%nat).
Proof.
  apply/eqP.
  case: eqP.
  - by move=> ->.
  - by apply not_0_INR.
Qed.

Lemma natmul0eq (n : nat) : ((n%:R)%R == 0%R :> R) = (n == 0%nat).
Proof.
  by rewrite -INRE INR0eq.
Qed.

Local Open Scope ring_scope.

Section construct.

  
  Import Ring ComRing UnitRing Pdiv.IdomainDefs Pdiv.WeakIdomain.

  Lemma size_poly1P_w [R : Exports.ringType] (p : {poly R}) :
    size p == 1%nat -> {c | c != 0 & p = c%:P}.
  Proof.
    move/eqP=> pC.
    have def_p: p = (p`_0)%:P
      by rewrite -size1_polyC ?pC.
    by exists p`_0; rewrite // -polyC_eq0 -def_p -size_poly_eq0 pC.
  Qed.

  Lemma eqpP_w [R : idomainType] (m n : {poly R}) :
    (m %= n) ->
    {c12 |  (c12.1 != 0) && (c12.2 != 0) & c12.1 *: m = c12.2 *: n}.
  Proof.
    case: (eqVneq m 0) => [-> /andP [/dvd0pP -> _] | m_nz].
    { by exists (1, 1); rewrite ?scaler0 // oner_eq0. }
    case: (eqVneq n 0) => [-> /andP [_ /dvd0pP ->] | n_nz /andP []].
    { by exists (1, 1); rewrite ?scaler0 // oner_eq0. }
    rewrite !dvdp_eq; set c1 := _ ^+ _; set c2 := _ ^+ _.
    set q1 := _ %/ _; set q2 := _ %/ _; move/eqP => Hq1 /eqP Hq2;
                                                   have Hc1 : c1 != 0 by rewrite expf_eq0 lead_coef_eq0 negb_and m_nz orbT.
    have Hc2 : c2 != 0 by rewrite expf_eq0 lead_coef_eq0 negb_and n_nz orbT.
    have def_q12: q1 * q2 = (c1 * c2)%:P.
    apply: (mulIf m_nz); rewrite mulrAC mulrC -Hq1 -scalerAr -Hq2 scalerA.
    by rewrite -mul_polyC.
    have: q1 * q2 != 0 by rewrite def_q12 -size_poly_eq0 size_polyC mulf_neq0.
    rewrite mulf_eq0; case/norP=> nz_q1 nz_q2.
    have: size q2 <= 1.
    have:= size_mul nz_q1 nz_q2; rewrite def_q12 size_polyC mulf_neq0 //=.
    by rewrite polySpred // => ->; rewrite leq_addl.
    rewrite leq_eqVlt ltnS size_poly_leq0 (negPf nz_q2) orbF.
    case/size_poly1P_w=> c cn0 cqe; exists (c2, c); first by rewrite Hc2.
    by rewrite Hq2 -mul_polyC -cqe.
  Qed.

  Lemma Bezoutp_w [R : idomainType] (p q : {poly R}) : {u | u.1 * p + u.2 * q %= (gcdp p q)}.
  Proof.
    have [-> | pn0] := eqVneq p 0.
    - by rewrite gcd0p; exists (0, 1); rewrite mul0r mul1r add0r eqpxx.
    - have [-> | qn0] := eqVneq q 0.
      + by rewrite gcdp0; exists (1, 0); rewrite mul0r mul1r addr0 eqpxx.
      + pose e := egcdp p q; exists e; rewrite eqp_sym.
        by case: (egcdpP pn0 qn0).
  Qed.
  
  Lemma Bezout_coprimepP_w [R : idomainType] (p q : {poly R}) :
    coprimep p q ->
    {u | u.1 * p + u.2 * q %= 1}.
  Proof.
    rewrite -gcdp_eqp1.
    case: (Bezoutp_w p q) => [[u v] Puv].
    intros g1.
    by exists (u, v); apply: eqp_trans g1.
  Qed.

  Lemma Bezout_eq1_coprimepP_w [F : fieldType] (p q : {poly F}) :
    coprimep (R:=F) p q ->
    {u : poly_ringType F * poly_ringType F | u.1 * p + u.2 * q = 1}.
  Proof.
    move/ Bezout_coprimepP_w.
    case=> [[u v]] /=.
    case/eqpP_w=> [[c1 c2]] /andP /= [c1n0 c2n0] e.
    exists (c2^-1 *: (c1 *: u), c2^-1 *: (c1 *: v)); rewrite /= -!scalerAl.
    by rewrite -!scalerDr e scalerA mulVf // scale1r.
  Qed.

End construct.

  Section Chinese.

(*   The chinese remainder theorem for polynomials overa a field *)
Variables F : fieldType.


Definition chinesep (m1 m2 r1 r2 : {poly F}) (co_m12: coprimep (R:=F) m1 m2) :=
  let u := sval (Bezout_eq1_coprimepP_w m1 m2 co_m12) in
  r1 * m2 * u.1 + r2 * m1 * u.2.

 Lemma chinesep_prop (m1 m2 r1 r2 : {poly F}) :
    coprimep (R:=F) m1 m2 ->
    {e : poly_ringType F |
      e %% m1 = r1 %% m1 /\ e %% m2 = r2 %% m2}.
 Proof.
   intros co_m12.
   destruct (Bezout_eq1_coprimepP_w  m1 m2 co_m12).
   pose c := r2 * x.1 * m1 + r1 * x.2 * m2.
   exists c.
  split. 
  - rewrite modpD modp_mull add0r.
    apply (f_equal (fun z => z %% m1)) in e.
    rewrite modpD modp_mull add0r in e.
    by rewrite -mulrA -modp_mul e modp_mul mulr1.
  - rewrite modpD modp_mull addr0.
    apply (f_equal (fun z => z %% m2)) in e.
    rewrite modpD modp_mull addr0 in e.    
    by rewrite -mulrA -modp_mul e modp_mul mulr1.
Qed.

 Lemma all_coprimep_prod (a : {poly F}) (l : seq {poly F}) :
    all (coprimep a) l ->
    coprimep a (\prod_(i <- l) i).
  Proof.
    intros.
    rewrite big_seq.
    apply big_rec.
    - apply coprimep1.
    - intros.
      move/allP/(_ _ H0): H.
      by rewrite coprimepMr H1 => ->.
  Qed.

  Lemma mod_mul_mod_r (a p q : {poly F}) :
    (a %% (p * q))%%q = a%%q.
  Proof.
    generalize (divp_eq a (p * q)); intros.
    apply (f_equal (fun z => z %% q)) in H.
    rewrite H.
    by rewrite modpD mulrA modp_mull add0r.
  Qed.

  Lemma mod_mul_mod_l (a p q : {poly F}) :
    (a %% (p * q))%%p = a%%p.
  Proof.
    rewrite mulrC.
    apply mod_mul_mod_r.
  Qed.

  Lemma prod_mod (a b : {poly F}) (l : seq {poly F}) :
    a %% (\prod_(q <- l) q) = b %% (\prod_(q <- l) q) ->
    forall p,
      p \in l -> a %% p = b %% p.
  Proof.
    induction l.
    - intros.
      by rewrite in_nil in H0.
    - intros.
      rewrite in_cons in H0.
      move /orP in H0.
      rewrite !big_cons in H.
      destruct H0.
      + rewrite (eqP H0).
        simpl in H.
        apply (f_equal (fun z => z %% a0)) in H.
        by rewrite !mod_mul_mod_l in H.
      + apply (f_equal (fun z => z %% (\prod_(j <- l) j))) in H.
        rewrite !mod_mul_mod_r in H.
        specialize (IHl H).
        by apply IHl.
  Qed.

Lemma chinesep_list_prop (l : seq ({poly F} * {poly F})) :
  pairwise (coprimep (R := F)) (map snd l) ->
  { e : {poly F} |
    forall p,
      p \in l -> e %% p.2 = p.1 %% p.2}.
Proof.
  induction l.
  - simpl.
    intros.
    exists 0.
    intros.
    by rewrite in_nil in H0.
  - intros.
    rewrite map_cons pairwise_cons in H.
    move /andP in H.
    destruct H.
    specialize (IHl H0).
    destruct IHl.
    assert (coprimep a.2 (\prod_(q <- l) q.2)).
    {
      generalize (all_coprimep_prod a.2 [seq i.2 | i <- l] H); intros.
      by rewrite big_map in H1.
    }
    destruct (chinesep_prop a.2 (\prod_(q <- l) q.2) a.1 x H1) as [? [??]].
    exists x0.
    intros.
    rewrite in_cons in H4.
    move /orP in H4.
    destruct H4.
    + by rewrite (eqP H4).
    + specialize (e p H4).
      rewrite -e.
      assert (\prod_(q <- l) q.2 = \prod_(q <-  [seq i.2 | i <- l]) q).
      {
        by rewrite big_map.
      }
      rewrite H5 in H3.
      generalize (prod_mod x0 x [seq i.2 | i <- l] H3 p.2); intros.
      apply H6.
      by apply map_f.
 Qed.

End Chinese.


Definition odd_nth_roots (n : nat) :=
  \row_(j < 2^n) (nth_root (2 * j + 1) (2 ^ (S n))).

Definition even_nth_roots (n : nat) :=
  \row_(j < 2^n) (nth_root (2 * j) (2 ^ (S n))).

Definition nth_roots_half (n : nat) :=
  \row_(j < 2^n) (nth_root j (2 ^ (S n))).

Lemma unity_root_nth_root (j n : nat) :
  n.+1.-unity_root (nth_root j n.+1).
Proof.
  apply /unity_rootP.
  by rewrite nth_root_npow /RtoC /=.
Qed.

Lemma primitive_root_nth_root (n : nat) :
  n.+1.-primitive_root (nth_root 1 n.+1).
Proof.
  intros.
  rewrite /primitive_root_of_unity.
  apply/andP.
  split; try lia.
  apply /forallP; intros.
  apply /eqP.
  apply /unity_rootP.
  case: (eqVneq x.+1 n.+1); intros.
  - by rewrite e nth_root_npow /RtoC /=.
  - rewrite Cpow_nth_root muln1.
    apply nth_root_not_1.
    rewrite Nat.mod_small; try lia.
    destruct x; simpl in *.
    lia.
Qed.

Lemma primitive_root_nth_root_coprime (j n : nat) :
  coprime j n.+1 ->
  n.+1.-primitive_root ((nth_root 1 n.+1) ^+ j).
Proof.
  intros.
  rewrite prim_root_exp_coprime //.
  apply primitive_root_nth_root.
Qed.

Lemma primitive_root_nth_root_coprime_alt (j n : nat) :
  coprime j n.+1 ->
  n.+1.-primitive_root (nth_root j n.+1).
Proof.
  intros.
  generalize (primitive_root_nth_root_coprime j n H); intros.
  by rewrite Cpow_nth_root muln1 in H0.
Qed.

Lemma pow2_S (j:nat) :
  { k : nat | (2^j)%nat == S k}.
Proof.
  exists (2^j-1)%nat.
  induction j.
  - now simpl.
  - rewrite /= expnS (eqP IHj); lia.
Defined.

Lemma primitive_root_odd_nth_root (j n : nat) :
  (2^(n.+1)).-primitive_root ((nth_root 1 (2^n.+1)) ^+ (2 * j + 1)).
Proof.
  destruct (pow2_S (S n)).
  rewrite (eqP i).
  apply primitive_root_nth_root_coprime.
  rewrite -(eqP i); clear i.
  assert (forall j0, coprime (2 * j0 + 1) 2).
  {
    intros.
    rewrite coprimen2.
    induction j0.
    * by rewrite muln0 add0n /=.
    * replace (2 * j0.+1 + 1)%N with (2 + (2 * j0 + 1))%N by lia.
      by rewrite oddD IHj0 /=.
  }
  induction n.
  - by rewrite expn1 H.
  - by rewrite expnS coprimeMr IHn // H.
Qed.

Lemma primitive_root_odd_nth_root_alt (j n : nat) :
  (2^(n.+1)).-primitive_root (nth_root (2 * j + 1) (2^n.+1)).
Proof.
  generalize (primitive_root_odd_nth_root j n); intros.
  destruct (pow2_S (S n)).
  rewrite (eqP i).
  by rewrite (eqP i) Cpow_nth_root muln1 in H.
Qed.

Lemma mul_INR n m :
  INR(n * m) = INR n * INR m.
Proof.
  by rewrite mult_INR /mul /=.
Qed.

Lemma even_nth_root_half (j n : nat) :
  0 < n ->
  nth_root (2 * j) (2 * n) = nth_root j n.
Proof.
  intros.
  rewrite /nth_root.
  apply /eqP.
  rewrite eq_complex /=.
  apply /andP.
  assert (INR 2 != 0).
  {
    rewrite /zero/=.
    apply/eqP.
    coq_lra.
  } 
  assert (INR 2 \is a unit).
  {
    by rewrite unitfE.
  }
  assert (INR n \is a unit).
  {
    rewrite unitfE INR0eq; lia.
  } 
  assert (inv (INR 2) * (INR 2) = 1).
  {
    rewrite mulrC divff //.
  }
  split; apply /eqP; f_equal;
    rewrite -![2 * PI * _ * _]mulrA; f_equal;
    rewrite !mul_INR invrM // [INR 2 * _]mulrC -mulrA; f_equal; 
    by rewrite mulrC -mulrA H3 mulr1.
Qed.

Lemma even_nth_root_half_pow (j n : nat) :
  nth_root (2 * j) (2 ^ (S n)) = nth_root j (2^n).
Proof.
  destruct (pow2_S n).
  rewrite expnS (eqP i).
  apply even_nth_root_half; lia.
Qed.  
  
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

Definition RtoC (x : R):R[i] := Complex x 0%R.

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

Lemma pow_nth_root' j n e :
  n != 0%nat ->
  (nth_root j n) ^+ e = nth_root (e * j) n.
Proof.
  destruct n; [lia |]=>_.
  apply pow_nth_root.
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
    by rewrite add0r -addrA (addrC _ 1) addrN addr0 in H1.
Qed.

Lemma telescope_pow_0_nat (c : R[i]) (n : nat) :
  c <> 1 ->
  c ^+ (S n) = 1 ->
  \sum_(0 <= j < S n) (c ^+ j) = C0.
Proof.
  intros.
  rewrite telescope_div; trivial.
  by rewrite H0 addrN mul0r.
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

Lemma add_conj (c1 c2 : R[i]) :
  (conjc c1) + (conjc c2) = conjc (c1 + c2).
Proof.
  by rewrite rmorphD.
Qed.

Lemma mul_conj (c1 c2 : R[i]) :
  (conjc c1) * (conjc c2) = conjc (c1 * c2).
Proof.
  by rewrite rmorphM.
Qed.

Lemma exp_conj (c : R[i]) n :
  conjc (c ^+ n) = (conjc c)^+n.
Proof.
  by rewrite rmorphXn.
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
  rewrite modnMDl modn_small//.
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
  
Lemma vector_rev_conj_plus {n} (v1 v2 : 'rV[R[i]]_n) :
  vector_rev_conj v1 ->
  vector_rev_conj v2 ->
  vector_rev_conj (map2_mx (fun (c1 c2 : R[i]) => add c1 c2) v1 v2).
Proof.
  unfold vector_rev_conj; intros.
  do 2 rewrite mxE.
  rewrite H.
  rewrite H0.
  now rewrite -rmorphD.
Qed.

Lemma vector_rev_conj_mult {n} (v1 v2 : 'rV[R[i]]_n) :
  vector_rev_conj v1 ->
  vector_rev_conj v2 ->
  vector_rev_conj (map2_mx (fun (c1 c2 : R[i]) => mul c1 c2) v1 v2).
Proof.
  unfold vector_rev_conj; intros.
  do 2 rewrite mxE.
  rewrite H; rewrite H0.
  now rewrite -rmorphM.
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
  lra.
Qed.

Lemma vector_rev_conj_const_R n (r : R) :
  vector_rev_conj (ConstVector n (RtoC r)).
Proof.
  unfold vector_rev_conj, ConstVector, RtoC; intros.
  do 2 rewrite mxE.
  unfold conjc.
  apply f_equal.
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
  intros.
  destruct c.
  move /eqP in H.
  rewrite /conjc eq_complex /= in H.
  move /andP in H.
  destruct H.
  simpl.
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
  rewrite rmorphD /= conjcK addrC//.
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
    coq_lra.
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
    unfold zero; simpl; coq_lra.
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

From mathcomp Require Import order.

(* 0 <= rand < 1 *)
Definition ran_round (x rand : R) :=
  let hi := up x in
  if (Order.lt (Rminus (IZR hi) x) rand)%R then hi else (Zminus hi 1).

Definition nearest_round (x : R) := ran_round x (1/2).

Definition mx_round {n m} (mat : 'M[R]_(n,m)) : 'M[int]_(n,m) :=
  map_mx (fun r => ssrZ.int_of_Z (nearest_round r)) mat.

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

Definition peval_C (p : {poly R}) (x : C) : C :=
  (map_poly RtoC p).[x].

Lemma ev_C_is_rmorphism (x:C) :
  rmorphism (fun (p : {poly R}) => peval_C p x).
Proof.
  unfold peval_C.
  constructor.
  - intros ??.
    rewrite -horner_evalE !rmorphB //.
  - split.
    + intros ??.
      rewrite -horner_evalE !rmorphM //.
    + rewrite -horner_evalE !rmorph1 //.
Qed.

Canonical ev_C_rmorphism (x:R[i]) := RMorphism (ev_C_is_rmorphism x).

Lemma sum_conj (n : nat) (F : 'I_n -> R[i]) :
  conjc (\sum_(i < n) (F i)) = \sum_(i<n) conjc (F i).
Proof.
  induction n.
  - by rewrite !big_ord0 conjc0.
  - by rewrite !big_ord_recr rmorphD /= IHn.
Qed.

Lemma peval_C_conj (p : {poly R}) (c : C) :
  peval_C p (conjc c) = conjc (peval_C p c).
Proof.
  rewrite /peval_C /map_poly !horner_poly sum_conj.
  apply eq_bigr.
  intros.
  rewrite rmorphM rmorphXn /= /RtoC.
  f_equal; f_equal.
  lra.
Qed.

Definition ctrace (c : R[i]) := Re (c + conjc c).
Definition cnorm (c : R[i]) := Re (c * conjc c).

Lemma ctrace_correct (c : R[i]) :
  Im (c + conjc c) = 0.
Proof.
  destruct c.
  simpl.
  lra.
Qed.

Lemma cnorm_correct (c : R[i]) :
  Im (c * conjc c) = 0.
Proof.
  destruct c.
  simpl.
  lra.
Qed.

Lemma RtoC_Re_Im0 (c : R[i]) :
  Im c = 0 ->
  RtoC (Re c) = c.
Proof.  
  intros.
  rewrite /RtoC.
  destruct c; simpl.
  apply /eqP.
  rewrite eq_complex.
  rewrite /=.
  apply /andP.
  split; trivial.
  apply /eqP.
  simpl in H.
  by rewrite H.
Qed.

Lemma RtoC_cnorm (c : R[i]) :
  RtoC (cnorm c) = c * conjc c.
Proof.
  rewrite /cnorm.
  apply RtoC_Re_Im0.
  destruct c.
  simpl.
  lra.
Qed.

Lemma RtoC_ctrace (c : R[i]) :
  RtoC (ctrace c) = c + conjc c.
Proof.
  rewrite /ctrace.
  apply RtoC_Re_Im0.
  destruct c.
  simpl.
  lra.
Qed.

Lemma RtoC_opp (r : R) :
  RtoC (- r) = - RtoC r.
Proof.
  rewrite /RtoC /=.
  apply /eqP.
  rewrite eq_complex /=.
  apply /andP; split; apply /eqP.
  - by rewrite /opp /=.
  - lra.
Qed.

Definition characteristic_polynomial (c : R[i]) : {poly R} :=
  'X^2 + (- ctrace c) *: 'X + (cnorm c)%:P.

Lemma size_charpoly (c : R[i]) :
  size (characteristic_polynomial c) = 3%N.
Proof.
  rewrite /characteristic_polynomial.
  rewrite -addrA size_addl size_polyXn //.
  case : (eqVneq (ctrace c) 0); intros.
  - rewrite e oppr0 scale0r add0r.
    rewrite size_polyC.
    case : (eqVneq (cnorm c) 0); rewrite //.
  - rewrite size_addl.
    + rewrite size_scale.
      * rewrite size_polyX //.
      * by rewrite -eqr_opp opprK oppr0.
    + rewrite size_scale.
      * rewrite size_polyX size_polyC.
        case : (eqVneq (cnorm c) 0); rewrite //.
      * by rewrite -eqr_opp opprK oppr0.
Qed.

Lemma monic_charpoly (c : R[i]) :
  characteristic_polynomial c \is monic.
Proof.
  apply /monicP.
  rewrite /characteristic_polynomial.
  rewrite -addrA.
  rewrite lead_coefDl.
  - apply lead_coefXn.
  - rewrite size_polyXn.
    case : (eqVneq (ctrace c) 0); intros.
    + rewrite e oppr0 scale0r add0r.
      rewrite size_polyC.
      case : (eqVneq (cnorm c) 0); rewrite //.
    + rewrite size_addl.
      * rewrite size_scale.
        -- rewrite size_polyX //.
        -- by rewrite -eqr_opp opprK oppr0.
      * rewrite size_scale.
        -- rewrite size_polyX size_polyC.
           case : (eqVneq (cnorm c) 0); rewrite //.
        -- by rewrite -eqr_opp opprK oppr0.
Qed.

Lemma characteristic_polynomial_correct (c : R[i]) :
  (map_poly RtoC (characteristic_polynomial c)).[c] = 0.
Proof.
  rewrite /map_poly size_charpoly /characteristic_polynomial.
  rewrite horner_poly.
  rewrite big_ord_recl big_ord_recl big_ord1 /= expr0 mulr1 /bump addn0 expr1 /=.
  replace (addn (S 0) (S 0)) with 2%N by lia.
  rewrite !coefD !coefZ !coefX !coefC !coefXn /=.
  rewrite mulr0 mulr1 !addr0 !add0r.
  rewrite rmorph1 RtoC_cnorm RtoC_opp RtoC_ctrace mul1r expr2 opprD mulrDl.
  rewrite -addrA (addrC _ (c * c)) (addrA _ (c * c) _) -mulrDl (addrC _ c).
  by rewrite addrN mul0r add0r mulrC -mulrDl addrN mul0r.
Qed.

Lemma trace_conj (c : R[i]) :
  ctrace c = ctrace (conjc c).
Proof.
  by rewrite /ctrace conjcK addrC.
Qed.

Lemma norm_conj (c : R[i]) :
  cnorm c = cnorm (conjc c).
Proof.
  by rewrite /cnorm conjcK mulrC.
Qed.

Lemma cnorm_peval_C_conj (p : {poly R}) (c : C) :
  cnorm (peval_C p c) = cnorm (peval_C p (conjc c)).
Proof.
  by rewrite norm_conj peval_C_conj.
Qed.

Lemma char_poly_conj (c : R[i]) :
  characteristic_polynomial c = characteristic_polynomial (conjc c).
Proof.
  by rewrite /characteristic_polynomial trace_conj norm_conj.
Qed.

Lemma char_poly_conj_alt (c : R[i]) :
  (map_poly RtoC (characteristic_polynomial c)).[conjc c] = 0.
Proof.
  rewrite char_poly_conj.
  apply characteristic_polynomial_correct.
Qed.

Lemma ctrace_eq (c1 c2 : R[i]) :
  ctrace c1 = ctrace c2 <-> c1 + conjc c1 = c2 + conjc c2.
Proof.
  rewrite /ctrace.
  split; intros.
  - apply /eqP.
    rewrite eq_complex.
    apply /andP.
    split.
    + now apply /eqP.
    + by rewrite !ctrace_correct.
  - by rewrite H.
Qed.

Lemma cnorm_eq (c1 c2 : R[i]) :
  cnorm c1 = cnorm c2 <-> c1 * conjc c1 = c2 * conjc c2.
Proof.
  rewrite /cnorm.
  split; intros.
  - apply /eqP.
    rewrite eq_complex.
    apply /andP.
    split.
    + now apply /eqP.
    + by rewrite !cnorm_correct.
  - by rewrite H.
Qed.

Lemma norm_trace_eq (c1 c2 : R[i]) :
  ctrace c1 = ctrace c2 /\ cnorm c1 = cnorm c2 <->
    c1 = c2 \/ c1 = conjc c2.
Proof.
  split; intros.
  - destruct H.
    destruct c1; destruct c2.
    rewrite /ctrace /= in H.
    rewrite /cnorm /= in H0.
    assert (Re = Re0) by lra.
    rewrite H1 in H0.
    assert (Im *Im = Im0 * Im0) by lra.
    rewrite /conjc.
    rewrite H1.
    assert (Im = Im0 \/ Im = -Im0).
    {
      rewrite -!expr2 in H2.
      move /eqP in H2.
      rewrite eqf_sqr in H2.
      move /orP in H2.
      destruct H2.
      - by move /eqP in H2; left.
      - by move /eqP in H2; right.
    }
    destruct H3.
    + by rewrite H3; left.
    + by rewrite H3; right.
  - destruct H; rewrite H; try easy.
    by rewrite trace_conj norm_conj conjcK.
Qed.

Lemma charpoly_eq (c1 c2 : R[i]) :
  characteristic_polynomial c1 = characteristic_polynomial c2 <->
    c1 = c2 \/ c1 = conjc c2.
Proof.
  split; intros.
  - rewrite /characteristic_polynomial in H.
    apply polyP in H.
    generalize (H 0%N); intros.
    generalize (H 1%N); intros.
    rewrite !coefD !coefZ !coefC !coefX !coefXn /= in H0.
    rewrite !coefD !coefZ !coefC !coefX !coefXn /= in H1.
    rewrite !mulr0 addr0 !add0r in H0.
    rewrite !addr0 !add0r !mulr1 in H1.
    apply norm_trace_eq.
    split; trivial.
    lra.
  - destruct H.
    + by rewrite H.
    + by rewrite H char_poly_conj conjcK.
Qed.

Lemma poly2_expand {S:comRingType} (c1 c2 : S) :
  'X^2 - (c1 + c2)*: 'X + (c1*c2)%:P =
    ('X - c1%:P) * ('X - c2%:P).
Proof.
  rewrite mulrDr !mulrDl addrA.
  f_equal.
  - rewrite scalerDl -expr2 -addrA.
    f_equal.
    rewrite (mulrC 'X _) opprD -!scaleNr -!mul_polyC.
    by f_equal; rewrite polyCN.
  - by rewrite mulrNN -scale_polyC mul_polyC.
Qed.

Lemma RtoCR n : RtoC n%:R = n%:R.
Proof.
  unfold RtoC.
  induction n.
  - now rewrite mulr0n.
  - rewrite mulrSr /= mulrS -IHn.
    apply /eqP.
    rewrite eq_complex /= addrC addr0 /=.
    by apply /andP.
Qed.

Lemma charpoly_factor (c : R[i]) :
  map_poly RtoC (characteristic_polynomial c) =
    ('X - c%:P) * ('X - (conjc c)%:P).
Proof.
  move: (size_charpoly c).
  rewrite -poly2_expand /characteristic_polynomial /ctrace /cnorm.
  rewrite map_polyE=>sz.
  apply/polyP=>i.
  rewrite coef_Poly.
  case/orP: (leqVgt 3 i)=>ibd.
  - rewrite !(coefD, coefZ, coefC, coefN, coefX, coefXn).
    replace (i == 2%N) with false by lia.
    replace (i == 1%N) with false by lia.
    replace (i == 0%N) with false by lia.
    rewrite /= mulr0 mulr0n oppr0 !addr0.
    rewrite nth_default //.
    by rewrite size_map sz.
  - rewrite (nth_map 0); [| by rewrite sz].
    rewrite !(coefD, coefZ, coefC, coefN, coefX, coefXn).
    rewrite !(rmorphD, rmorphM, rmorphN) /=.
    rewrite !RtoCR RtoC_ctrace mulNr.
    f_equal.
    case : (eqVneq i 0%N).
    + by rewrite RtoC_cnorm.
    + by rewrite /RtoC.
 Qed.

Lemma charpoly_irreducible (c : R[i]) :
  c != conjc c ->
  irreducible_poly (characteristic_polynomial c).
Proof.
  intros.
  assert (1 < size (characteristic_polynomial c) <= 4).
  {
    rewrite size_charpoly //.
  }
  apply (cubic_irreducible H0).
  intros.
  apply /negP.
  unfold not; intros.
  assert (root (map_poly RtoC (characteristic_polynomial c)) (RtoC x)).
  {
    by apply rmorph_root.
  }
  rewrite charpoly_factor in H2.
  unfold root in H2.
  rewrite hornerM hornerD mulf_eq0 in H2.
  move /orP in H2.
  destruct H2.
  - move /eqP in H2.
    rewrite hornerX hornerN hornerC in H2.
    apply (f_equal (fun z => z+ c)) in H2.
    rewrite -addrA add0r (addrC _ c) addrN addr0 in H2.
    by rewrite -H2 /RtoC /= eq_complex /= oppr0 !eq_refl /= in H.
  - move /eqP in H2.
    rewrite hornerD hornerX hornerN hornerC in H2.
    apply (f_equal (fun z => z+ conjc c)) in H2.
    rewrite -addrA add0r (addrC _ (conjc c)) addrN addr0 in H2.
    apply (f_equal (fun z => conjc z)) in H2.
    rewrite conjcK /RtoC /= in H2.
    by rewrite -H2 /RtoC /= eq_complex /= opprK oppr0 !eq_refl /= in H.
 Qed.

Lemma charpoly_square (c : R[i]) :
  c == conjc c ->
  characteristic_polynomial c = ('X - (Re c)%:P)^+2.
Proof.
  intros.
  move /eqP in H.
  rewrite expr2 /characteristic_polynomial /ctrace /cnorm H conjcK /= -H -poly2_expand.
  f_equal.
  - f_equal.
    rewrite -scaleNr.
    f_equal.
    f_equal.
    destruct c.
    by simpl.
  - f_equal.
    destruct c.
    simpl.
    move /eqP in H.
    rewrite eq_complex /= in H.
    move /andP in H.
    destruct H.
    move /eqP in H0.
    assert (Im = 0) by lra.
    rewrite H1.
    lra.
Qed.

Lemma charpoly_coprime_case1 (c1 c2 : R[i]) :
  c1 != conjc c1 ->
  c2 != conjc c2 ->
  characteristic_polynomial c1 != characteristic_polynomial c2 ->
  coprimep (characteristic_polynomial c1) (characteristic_polynomial c2).
Proof.
  intros.
  apply /coprimepP.
  intros.
  apply charpoly_irreducible in H.
  apply charpoly_irreducible in H0.
  specialize (H d); intros.
  specialize (H0 d); intros.
  rewrite -size_poly_eq1.
  case : (eqVneq (size d) 1%N); trivial.
  intros.
  specialize (H4 i H2).
  specialize (H5 i H3).
  rewrite eqp_sym in H4.
  generalize (eqp_trans H4 H5); intros.
  rewrite eqp_monic in H6.
  - by rewrite H6 in H1.
  - apply monic_charpoly.
  - apply monic_charpoly.    
Qed.

Lemma charpoly_coprime_case2 (c1 c2 : R[i]) :
  c1 != conjc c1 ->
  c2 == conjc c2 ->
  characteristic_polynomial c1 != characteristic_polynomial c2 ->
  coprimep (characteristic_polynomial c1) (characteristic_polynomial c2).
Proof.
  intros.
  apply charpoly_square in H0.
  apply /coprimepP.
  intros.
  apply charpoly_irreducible in H.
  specialize (H d); intros.
  rewrite -size_poly_eq1.
  case : (eqVneq (size d) 1%N); trivial.
  intros.
  specialize (H4 i H2).
  assert (size d == size (characteristic_polynomial c2)).
  {
    generalize (eqp_size H4); intros.
    rewrite size_charpoly.
    rewrite size_charpoly in H5.
    by rewrite H5.
  }
  rewrite Pdiv.CommonIdomain.dvdp_size_eqp in H5; trivial.
  rewrite eqp_sym in H4.
  generalize (eqp_trans H4 H5); intros.
  rewrite eqp_monic in H6.
  - by rewrite H6 in H1.
  - apply monic_charpoly.
  - apply monic_charpoly.    
Qed.
  
Lemma charpoly_coprime_case3 (c1 c2 : R[i]) :
  c1 == conjc c1 ->
  c2 == conjc c2 ->
  characteristic_polynomial c1 != characteristic_polynomial c2 ->
  coprimep (characteristic_polynomial c1) (characteristic_polynomial c2).
Proof.
  intros.
  apply charpoly_square in H.
  apply charpoly_square in H0.
  rewrite H H0.
  rewrite H H0 in H1.
  apply coprimep_expl.
  apply coprimep_expr.
  apply coprimep_XsubC2.
  apply /negP.
  unfold not; intros.
  rewrite subr_eq0 in H2.
  move /eqP in H2.
  rewrite H2 in H1.
  move /negP in H1.
  by apply H1.
Qed.

Lemma charpoly_comprime (c1 c2 : R[i]) :
  characteristic_polynomial c1 != characteristic_polynomial c2 ->
  coprimep (characteristic_polynomial c1) (characteristic_polynomial c2).
Proof.
  case : (boolP (c1 == conjc c1)); intros.
  - case : (boolP (c2 == conjc c2)); intros.
    + by apply charpoly_coprime_case3.
    + rewrite coprimep_sym.
      rewrite eq_sym in H.
      by apply charpoly_coprime_case2.
  - case : (boolP (c2 == conjc c2)); intros.
    + by apply charpoly_coprime_case2.
    + by apply charpoly_coprime_case1.
Qed.

 Lemma ev_C_1 :
   forall (x : C), peval_C 1 x = 1.
  Proof.
    apply ev_C_is_rmorphism.
  Qed.

  Definition peval_C_ker_pred (x : C) : pred {poly R} :=
    fun p => peval_C p x == 0.

  Lemma peval_C_ker_proper (x : C) :
    proper_ideal (peval_C_ker_pred x).
  Proof.
    split.
    - by rewrite /peval_C_ker_pred /in_mem /mem /= ev_C_1 oner_neq0.
    - move => a b.
      rewrite /in_mem /=.
      rewrite /peval_C_ker_pred.
      case: (ev_C_is_rmorphism x) => _ -> /eqP->.
      by rewrite mulr0.
  Qed.

  Lemma peval_C_ker_zmod (x : C) :
    zmodPred (peval_C_ker_pred x).
  Proof.
    constructor.
    - constructor; [constructor|].
      constructor.
      + rewrite /in_mem //= /peval_C_ker_pred /peval_C.
        unfold map_poly.
        rewrite poly_size_0.
        rewrite (eq_poly (fun _ => 0)).
        * rewrite -{2}(horner0 x).
          apply /eqP.
          f_equal.
          apply /polyP => i /=.          
          rewrite coef_poly coefC /=.
          f_equal.
          by case: (i == 0)%nat.
        * move=> i ilt.
          rewrite coefC.
          by case: (i == 0)%nat.
      + rewrite /in_mem //= /prop_in2 /peval_C_ker_pred => a b.
        rewrite /in_mem /mem /= .
        generalize (raddfD (ev_C_rmorphism x)); intros.
        simpl in H; rewrite H.
        revert H0 H1.
        move => /eqP -> /eqP->.
        rewrite add0r //.
    - rewrite /Pred.Exports.oppr_closed /mem /= /peval_C_ker_pred => a.
      rewrite /in_mem /= => /eqP-eqq1.
      generalize (raddfN (ev_C_rmorphism x) a); intros.
      simpl in H.
      rewrite H eqq1 oppr0 //.
  Qed.

  Definition peval_C_ker_is_ideal (x:C) :
    idealr (peval_C_ker_pred x)
    := MkIdeal (peval_C_ker_zmod x) (peval_C_ker_proper x).

  Canonical peval_C_ker_ideal (x:C) := KeyedPred (peval_C_ker_is_ideal x).

  Definition peval_C_ker_quot_ring (x:C)
    := { ideal_quot (peval_C_ker_ideal x) }.

  Local Open Scope quotient_scope.

  Definition peval_C_quot (x:C) : peval_C_ker_quot_ring x -> C
    := lift_fun1 (peval_C_ker_quot_ring x) (fun p => peval_C p x).

  Lemma pi_peval_C_quot x : {mono (\pi_(peval_C_ker_quot_ring x)) : p / peval_C p x >-> peval_C_quot x p}.
  Proof.
    move=> p.
    rewrite /peval_C_quot -eq_lock.
    case: piP => a /EquivQuot.eqmodP.
    rewrite /Quotient.equiv_equiv /Quotient.equiv /in_mem /mem /= /peval_C_ker_pred.
    destruct (ev_C_is_rmorphism x).
    rewrite base => eqq.
    move=> /eqP in eqq.
    apply (f_equal (fun z => z + peval_C a x)) in eqq.
    by rewrite -addrA add0r (addrC _ (peval_C a x)) addrN addr0 in eqq.
  Qed.

  Lemma peval_C_quot1 x : peval_C_quot x 1 = 1.
  Proof.
    rewrite /one /= /Quotient.one /= /one /= /locked.
    destruct master_key.
    rewrite pi_peval_C_quot /peval_C.
    rewrite /map_poly size_poly1.
    rewrite horner_poly big_ord1 expr0 mulr1.
    by rewrite -horner_coef0 hornerC.
  Qed.

  Lemma peval_quot_C_is_rmorphism (c:C): rmorphism (peval_C_quot c).
  Proof.
    split => [x|].
    - apply quotP=> y <-.
      revert x.
      apply quotP => x <-.
      rewrite !reprK.
      rewrite !pi_peval_C_quot.
      rewrite /peval_C_quot -!eq_lock.
      rewrite -pi_is_additive.
      case: piP => y' /eqquotP.
      rewrite /peval_C_ker_pred /in_mem/mem/= => /eqP.
      generalize (raddfD (ev_C_rmorphism c)); intros peval_C_add.
      generalize (raddfN (ev_C_rmorphism c)); intros peval_C_opp.
      generalize (peval_C_add (x-y) (-y')); intros add1.
      simpl in add1; rewrite add1.
      specialize (peval_C_add x (-y)); simpl in peval_C_add.
      rewrite peval_C_add.
      generalize (peval_C_opp y); intro opp1.
      simpl in opp1; rewrite opp1.
      specialize (peval_C_opp y'); simpl in peval_C_opp.
      rewrite peval_C_opp.
      intro HH.
      apply (f_equal (fun z => z + peval_C y' c)) in HH.
      rewrite add0r -!addrA in HH.
      rewrite (addrC _ (peval_C y' c)) addrN addr0 in HH.
      by rewrite -HH.
    - constructor.
      + move => x.
        apply quotP=> y <-.
        revert x.
        apply quotP => x <-.
        rewrite !reprK.
        rewrite !pi_peval_C_quot.
        rewrite /peval_C_quot -!eq_lock.
        rewrite -pi_is_multiplicative.
        case: piP => y' /eqquotP.
        rewrite /peval_C_ker_pred /in_mem/mem/= => /eqP.
        destruct (ev_C_is_rmorphism c) as [? [??]].
        specialize (base (x * y) y'); simpl in base.
        rewrite base.
        specialize (m x y); simpl in m.
        rewrite m.
        intro HH.
        apply (f_equal (fun z => z + peval_C y' c)) in HH.
        rewrite add0r -!addrA in HH.
        rewrite (addrC _ (peval_C y' c)) addrN addr0 in HH.
        by rewrite -HH.
      + by apply peval_C_quot1.
  Qed.

  Lemma peval_C_quot_is_injective (c:C) :
    injective (peval_C_quot c).
  Proof.
    intros x y.
    rewrite /peval_C_quot -!eq_lock.
    rewrite -{2}[x]reprK -{2}[y]reprK.
    move: (repr x) (repr y) => {x} {y} x y eqq.
    apply/eqquotP.
    rewrite /Quotient.equiv/=.
    rewrite /peval_C_ker_pred /in_mem/mem/=.
    apply/eqP.
    destruct (ev_C_is_rmorphism c).
    specialize (base x y).
    simpl in base.
    by rewrite eqq addrN in base.
  Qed.

  Lemma cval_decomp (c1 c2 : C) :
    Im c1 != 0 ->
    {a : R * R | (a.1%:C * c1 + a.2%:C)%C = c2}.
  Proof.
    intros.
    exists ((Im c2/Im c1), (Re c2 - (Im c2 / Im c1)*Re c1)).
    apply /eqP.
    rewrite eq_complex.
    apply /andP.
    destruct c1.
    destruct c2.
    simpl.
    rewrite !mul0r !addr0 subr0.
    - split.
      + apply /eqP.
        rewrite addrC.
        generalize (subrKA (Im0 / Im * Re) Re0 0); intros.
        by rewrite !addr0 in H0.
      + rewrite -mulrA.
        rewrite (mulrC _ Im).
        rewrite divff //.
        by rewrite mulr1.
  Qed.

  Lemma peval_C_decomp (c1 c2 : C) :
    Im c1 != 0 ->
    {p : {poly R} | peval_C p c1 = c2}.
  Proof.
    intros.
    destruct (cval_decomp c1 c2 H).
    exists (x.1 *: 'X + x.2 %:P).
    rewrite /peval_C -e.
    case: (eqVneq x.1 0) => [-> |].
    - rewrite scale0r add0r /map_poly.
      rewrite horner_poly mul0r add0r.
      case: (eqVneq x.2 0) => [-> |].
      + by rewrite size_poly0 big_ord0.
      + intros.
        rewrite size_polyC.
        rewrite i // big_ord1 expr0 mulr1 coefC //.
    - intros.
      rewrite /map_poly size_addl size_scale //; rewrite size_polyX.
      + rewrite horner_poly.
        rewrite big_ord_recl big_ord1 /= expr0 mulr1 /bump /= addn0 expr1.
        rewrite !coefD !coefZ !coefX !coefC /=.
        rewrite mulr0 mulr1 addr0 add0r.
        by rewrite addrC mulrC.
      + rewrite size_polyC.
        by case: (eqVneq x.2 0).
  Qed.

  Lemma peval_C_quot_is_surjective (c c2 :C) :
    Im c != 0 ->
    {p: peval_C_ker_quot_ring c | peval_C_quot c p = c2}.
  Proof.
    intros.
    destruct (peval_C_decomp c c2); trivial.
    exists (\pi_(peval_C_ker_quot_ring c) x).
    rewrite -e.
    apply pi_peval_C_quot.
  Qed.


  Lemma peval_C_quot_is_bijective (c :C) :
    Im c != 0 ->
    bijective (peval_C_quot c).
  Proof.
    intros imn0.
    pose g : R[i] -> peval_C_ker_quot_ring c :=
      fun c2 => sval (peval_C_quot_is_surjective c c2 imn0).
    apply Bijective with (g := g).
    - intros ?.
      assert (peval_C_quot c (g (peval_C_quot c x)) = peval_C_quot c x).
      {
        rewrite /g.
        destruct (peval_C_quot_is_surjective c (peval_C_quot c x) imn0).
        by simpl.
      }
      by apply peval_C_quot_is_injective in H.
    - intros ?.
      rewrite /g.
      destruct (peval_C_quot_is_surjective c x imn0).
      by simpl.
   Qed.


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
    case: piP => a /EquivQuot.eqmodP.
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

  Lemma mx_eval_quot_is_injective :
    injective mx_eval_quot.
  Proof.
    intros x y.
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

  Lemma poly_eval_mod (a b p : {poly R}) (c : R[i]) :
    a %% p = b %% p ->
    (map_poly RtoC p).[c] = 0 ->
    (map_poly RtoC a).[c] = (map_poly RtoC b).[c].
  Proof.
    intros.
    rewrite (divp_eq a p).
    rewrite (divp_eq b p) H.
    by rewrite !rmorphD !rmorphM !hornerD !hornerM H0 !mulr0 !add0r.
  Qed.

  Lemma mx_eval_is_surjective :
    let charvals := [seq characteristic_polynomial (vals 0 j) | j  : 'I_n.+1] in
    pairwise (coprimep (R := R_fieldType)) charvals  ->
    (forall j, Im (vals 0 j) != 0) ->              
    forall (c : MR_comRingType 0 n),
    {x : {poly R} | mx_eval x = c}.
  Proof.
    intros charvals cop imn0 c.

    pose rvals := [seq sval (peval_C_decomp (vals 0 j) (c 0 j) (imn0 j)) | j : 'I_n.+1].
    have rvals_prop: forall (j:'I_n.+1), peval_C (rvals`_j) (vals 0 j) = (c 0 j).
    {
      subst rvals=>j.
      rewrite (nth_map 0)/=.
      - move: (svalP (peval_C_decomp (vals 0 (enum 'I_n.+1)`_j) (c 0 (enum 'I_n.+1)`_j) (imn0 (enum 'I_n.+1)`_j))).
        by rewrite !nth_ord_enum.        
      - rewrite size_enum_ord.
        by destruct j.
    }

    have eqsize: size rvals = size charvals.
    {
      subst rvals charvals.
      by rewrite !size_map -enumT size_enum_ord.
    }  
    
    generalize (chinesep_list_prop R_fieldType (zip rvals charvals)); intros.
    assert ([seq i.2 | i <- zip rvals charvals] = charvals).
    {
      apply (@eq_from_nth _ 0).
      - by rewrite size_map size_zip eqsize ?minnn.
      - intros.
        rewrite size_map in H.
        rewrite (nth_map 0) //.
        by rewrite nth_zip_cond H.
    }
    rewrite -H in cop.
    specialize (X cop).
    destruct X.
    exists x.
    apply /matrixP.
    intros ??.
    pose p := (zip rvals charvals)`_y.
    assert (p \in zip rvals charvals).
    {
      subst p.
      apply/(nthP 0).
      subst rvals charvals.
      exists y => //.
      by rewrite size_zip eqsize minnn size_map size_enum_ord ltn_ord.
    } 
    specialize (e p H0).
    rewrite ord1 -(rvals_prop y).
    rewrite /mx_eval /peval_C.
    rewrite !mxE.
    have eqq1: charvals`_y = p.2.
    {
      subst p.
      by rewrite nth_zip.
    }
    have eqq2: rvals`_y = p.1.
    {
      subst p.
      by rewrite nth_zip.
    }
    rewrite eqq2.
    apply (poly_eval_mod _ _ _ _ e).
    rewrite -eqq1.
    assert (charvals`_y = characteristic_polynomial (vals 0 y)).
    {
      unfold charvals.
      rewrite (nth_map 0)/=.
      - by rewrite nth_ord_enum. 
      - by rewrite size_enum_ord ltn_ord.
    }
    rewrite H1.
    apply characteristic_polynomial_correct.
  Qed.

  Lemma mx_eval_quot_is_surjective  :
    let charvals := [seq characteristic_polynomial (vals 0 j) | j  : 'I_n.+1] in
    pairwise (coprimep (R := R_fieldType)) charvals  ->
    (forall j, Im (vals 0 j) != 0) ->   
    forall (c : MR_comRingType 0 n),
    {x :  mx_eval_ker_quot_ring | mx_eval_quot x = c}.
  Proof.
    intros.
    destruct (mx_eval_is_surjective H H0 c).
    exists (\pi_mx_eval_ker_quot_ring x).
    by rewrite pi_mx_eval_quot.
  Qed.

  Lemma mx_eval_quot_is_bijective :
    let charvals := [seq characteristic_polynomial (vals 0 j) | j  : 'I_n.+1] in
    pairwise (coprimep (R := R_fieldType)) charvals  ->
    (forall j, Im (vals 0 j) != 0) ->   
    bijective mx_eval_quot.
  Proof.
    intros charvals cop imn0.
    pose g : MR_comRingType 0 n -> mx_eval_ker_quot_ring :=
      fun c => sval (mx_eval_quot_is_surjective cop imn0 c).
    apply Bijective with (g := g).
    - intros ?.
      assert (mx_eval_quot (g (mx_eval_quot x)) = mx_eval_quot x).
      {
        rewrite /g.
        destruct (mx_eval_quot_is_surjective cop imn0 (mx_eval_quot x)).
        by simpl.
      }
      by apply mx_eval_quot_is_injective in H.
    - intros ?.
      rewrite /g.
      destruct (mx_eval_quot_is_surjective cop imn0 x).
      by simpl.
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

Lemma odd_nth_roots_minpoly_complex n :
  forall (c : R[i]),
    root ('X^(2^(S n)) + 1%:P) c ->
    Im c <> 0.
Proof.
  intros.
  unfold root in H.
  rewrite hornerD hornerXn hornerC in H.
  move /eqP in H.
  unfold not; intros.
  destruct c.
  simpl in H0.
  rewrite H0 in H.
  assert (forall x:R, x^+2 + 1 <> 0).
  {
    intros.
    apply Rgt_not_eq.
    generalize (pow2_ge_0 x); intros.
    rewrite /one /add /zero /= -RpowE.
    coq_lra.
  }
  assert (forall x:R, x^+(2^(S n)) + 1 <> 0).
  {
    intros.
    by rewrite expnS mulnC exprM.
  }
  clear H0 H1.
  replace ((Re +i* 0)%C ^+ (2 ^ n.+1)) with (RtoC (Re ^+ (2 ^ n.+1))) in H.
  - unfold RtoC in H.
    move /eqP in H.
    rewrite eq_complex in H.
    move /andP in H.
    destruct H.
    simpl in H.
    move /eqP in H.
    by specialize (H2 Re).
  - assert (forall n,
               RtoC (Re ^+ n) = (Re +i* 0)%C ^+n).
    {
      induction n0.
      - by rewrite !expr0.
      - rewrite !exprS.
        assert (forall (x y : R),
                   RtoC (x * y) = RtoC x * RtoC y).
        {
          apply RtoC_is_rmorphism.
        }
        by rewrite H0 IHn0.
    }
    apply H0.
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

  Definition cvec_norm_inf {n} (v : 'cV[R[i]]_n):R := norm_inf(v^T).
  Definition cvec_norm1 {n} (v : 'cV[R[i]]_n):R := norm1(v^T).  

  Definition matrix_norm_inf {n m} (mat : 'M[R[i]]_(n,m)) :=
    \big[Order.max/0]_(j<n) (\sum_(k<m) normc (mat j k)).

  Definition matrix_norm1 {n m} (mat : 'M[R[i]]_(n,m)) :=
    matrix_norm_inf (mat ^T).

  Definition coef_norm1 (p : {poly R}):R := \sum_(j < seq.size p) Rabs (p`_ j).

  Definition coef_maxnorm (p : {poly R}):R := \big[Order.max/0]_(j < seq.size p) Rabs (p`_ j).

  Definition canon_norm1 n (p : {poly R}):R := norm1 (mx_eval (odd_nth_roots' n) p).
  Definition canon_norm_inf n (p : {poly R}):R := norm_inf (mx_eval (odd_nth_roots' n) p).

  Lemma norm_inf_diag {n} (v : 'rV[R[i]]_n) :
    norm_inf v = matrix_norm_inf (diag_mx v).
  Proof.  
    rewrite /norm_inf /matrix_norm_inf.
    apply eq_bigr => i _.
    rewrite (bigD1 i) // /= big1_idem ?addr0 //.
    - by rewrite /diag_mx mxE eq_refl /= mulr1n.
    - intros.
      rewrite mxE eq_sym.
      by rewrite (negbTE H) ComplexField.Normc.normc0.
 Qed.

  Lemma normc_nneg (x : R[i]) :
    (R0  <= normc x)%O.
  Proof.
    rewrite /normc.
    case: x => r i.
    apply ssrnum.Num.Theory.sqrtr_ge0.
  Qed.

  Lemma sum_normc_nneg {n} (v : 'rV[R[i]]_n) :
    ((@zero R_zmodType) <= \sum_(k < n) normc (R:=R_rcfType) (v ord0 k))%O.
  Proof.
    apply big_rec => // i x _ xnneg.
    by rewrite ssrnum.Num.Theory.addr_ge0 // normc_nneg.
  Qed.

  Lemma mat_vec_norm_inf {n} (v : 'rV[R[i]]_n) :
    norm_inf v = matrix_norm_inf (v^T).
  Proof.
    rewrite /norm_inf /matrix_norm_inf /=.
    apply eq_bigr => j _.
    by rewrite big_ord_recl big_ord0 addr0 mxE.
  Qed.

  Lemma mat_vec_norm1 {n} (v : 'rV[R[i]]_n) :
    norm1 v = matrix_norm1 (v^T).
  Proof.
    rewrite /norm1 /matrix_norm1 /matrix_norm_inf /=.
    rewrite big_ord_recl big_ord0 Order.POrderTheory.max_l ?sum_normc_nneg //.
    by apply eq_bigr => j _; rewrite !mxE.
    Qed.
 

  Lemma R00 : R0 = 0.
  Proof.
    by [].
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
    (repeat case: RltbP); [lra | | | lra]; intros.
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

  Lemma maxrM_l (c a b : R) : Rle 0 c -> Order.max (a * c) (b * c)  = (Order.max a b)*c.
  Proof.
    rewrite /Order.max /Order.lt /=.
    (repeat case: RltbP); [lra | | | lra]; intros.
    - destruct H.
      + apply Rmult_lt_reg_r in p => //.
      + subst.
        by rewrite !mulr0.
    - destruct H.
      + elim n.
        by apply Rmult_lt_compat_r.
      + subst.
        by rewrite !mulr0.
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

  Lemma normc_triang_sum {n} (a : 'I_n -> R[i]) :
    Rleb (normc (\sum_(j<n) (a j)))
      (\sum_(j<n) normc (a j)).
  Proof.
    induction n.
    - rewrite !big_ord0 ComplexField.Normc.normc0.
      apply /RlebP.
      apply Rle_refl.
    - rewrite !big_ord_recl.
      apply /RlebP.
      eapply Rle_trans.
      apply normc_triangR.
      apply Rplus_le_compat_l.
      apply /RlebP.
      apply IHn.
  Qed.

  Lemma sum_mult_distr {n} (a : 'I_n -> R) (c : R) :
    (\sum_(j<n) (a j))*c = \sum_(j<n) (a j) * c.
  Proof.
    induction n.
    - by rewrite !big_ord0 mul0r.
    - rewrite !big_ord_recl mulrDl.
      f_equal.
      by rewrite IHn.
  Qed.   

  Lemma sum_mult_distl {n} (a : 'I_n -> R) (c : R) :
    c * (\sum_(j<n) (a j)) = \sum_(j<n) c * (a j).
  Proof.
    induction n.
    - by rewrite !big_ord0 mulr0.
    - rewrite !big_ord_recl mulrDr.
      f_equal.
      by rewrite IHn.
  Qed.   

  Lemma max_mult_distr {n} (a : 'I_n -> R) (c : R) :
    Rle 0 c ->
    (\big[Order.max/0]_(j<n) (a j))*c =
      \big[Order.max/0]_(j<n) ((a j)*c).
  Proof.
    induction n.
    - by rewrite !big_ord0 mul0r.
    - intros.
      rewrite !big_ord_recl -maxrM_l //.
      rewrite IHn //.
  Qed.   

 Lemma max_mult_distl {n} (a : 'I_n -> R) (c : R) :
    Rle 0 c ->
    c * (\big[Order.max/0]_(j<n) (a j)) =
      \big[Order.max/0]_(j<n) (c * (a j)).
  Proof.
    induction n.
    - by rewrite !big_ord0 mulr0.
    - intros.
      rewrite !big_ord_recl !(mulrC c _) -maxrM_l //.
      rewrite !(mulrC _ c) IHn //.
  Qed.
  
  Lemma sum_le {n} (a b : 'I_n -> R) :
    (forall j, Rleb (a j) (b j)) ->
    Rleb (\sum_(j<n) (a j)) (\sum_(j<n) (b j)).
  Proof.
    induction n.
    - rewrite !big_ord0.
      intros.
      apply /RlebP.
      now right.
    - intros.
      rewrite !big_ord_recl.
      apply /RlebP.
      apply Rplus_le_compat.
      + apply /RlebP.
        apply H.
      + apply /RlebP.
        apply IHn.
        intros.
        apply H.
  Qed.   

  Lemma max_le_compat (a b c d : R) :
    Rleb a b ->
    Rleb c d ->
    Rleb (Order.max a c) (Order.max b d).
  Proof.
    rewrite -!RmaxE.
    intros.
    apply /RlebP.
    move /RlebP in H.
    move /RlebP in H0.
    apply Rmax_case; apply Rmax_Rle.
    - by left.
    - by right.
  Qed.

  Lemma bigmax_le2 {n} (a b : 'I_n -> R) :
    (forall j, Rleb (a j) (b j)) ->
    Rleb (\big[Order.max/0]_(j<n) (a j))
      (\big[Order.max/0]_(j<n) (b j)).
  Proof.
    induction n.
    - rewrite !big_ord0.
      intros.
      apply /RlebP.
      now right.
    - intros.
      rewrite !big_ord_recl.
      apply max_le_compat; rewrite //.
      apply IHn.
      intros.
      apply H.
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
  
  Lemma bigmaxr_le_alt {n} (v : 'I_n -> R) init i:
    Rleb (v i) (\big[Order.max/init]_(j < n) (v j)).
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

  Lemma mat_vec_norm_bound1 {n m}
    (mat : 'M[R[i]]_(n, m))
    (vec : 'rV[R[i]]_m) k:
    Rleb (normc (\sum_(j<m) (mat k j) * (vec 0 j)))
      ((\sum_(j<m) normc (mat k j)) *
         (\big[Order.max/0]_(j<m) normc (vec 0 j))).
  Proof.
    apply /RlebP.
    eapply Rle_trans.
    - apply /RlebP.
      apply normc_triang_sum.
    - generalize (@sum_mult_distr m); intros.
      rewrite /mul /= in H.
      rewrite H.
      apply /RlebP.
      apply sum_le => j.
      rewrite ComplexField.Normc.normcM.
      apply /RlebP.
      apply Rmult_le_compat_l.
      + apply normc_nnegR.
      + apply /RlebP.
        apply bigmaxr_le.
  Qed.


  Lemma bigmax_nneg {n} (v : 'I_n -> R) :
    (forall i, Rleb 0 (v i)) ->
    Rleb 0 (\big[Order.max/0]_(j < n) (v j)).
  Proof.
    intros.
    apply big_rec.
    - apply /RlebP.
      unfold zero; simpl.
      coq_lra.
    - intros.
      assert  ((zero R_ringType) <= Order.max (v i) x)%O.
      {
        rewrite Order.TotalTheory.le_maxr.      
        apply /orP.
        left.
        apply H.
      }
      by rewrite /Order.le /= in H1.
   Qed.

  Lemma bigmax_normc_nneg {n} (v : 'rV[R[i]]_n):
    Rleb 0 (\big[Order.max/0]_(j < n) normc (v 0 j)).
  Proof.
    apply bigmax_nneg => i.
    apply normc_nneg.
  Qed.

  Lemma sum_nneg {n} (v : 'I_n -> R) :
    (forall i, Rleb 0 (v i)) ->
    Rleb 0 (\sum_(j < n) (v j)).
  Proof.
    intros.
    apply big_rec.
    - apply /RlebP.
      unfold zero; simpl.
      coq_lra.
    - intros.
      apply /RlebP.
      rewrite /add /=.
      apply Rplus_le_le_0_compat; by apply /RlebP.
   Qed.

 Lemma matrix_vec_norm_inf_sub_mult {n m} 
    (mat : 'M[R[i]]_(n, m))
    (vec : 'rV[R[i]]_m) :
    Rleb (matrix_norm_inf (mat *m (vec^T)))
      ((matrix_norm_inf mat) * (norm_inf vec)).
  Proof.
    rewrite /matrix_norm_inf /norm_inf /mulmx /=.
    generalize (@max_mult_distr n); intros.
    rewrite /mul /= in H.
    rewrite H.
    - apply bigmax_le2.
      intros.
      rewrite big_ord_recl big_ord0 addr0 mxE /trmx /=.
      under eq_bigr do rewrite mxE.
                       by rewrite mat_vec_norm_bound1.
    - apply /RlebP.
      apply bigmax_normc_nneg.
  Qed.

  Lemma sum_plus {n} (a b : 'I_n -> R) :
    \sum_(i<n) (a i) + \sum_(i<n) (b i) = \sum_(i<n) ((a i) + (b i)).
  Proof.
    induction n.
    - by rewrite !big_ord0 addr0.
    - rewrite !big_ord_recl.
      rewrite -IHn.
      rewrite /add /=.
      coq_lra.
  Qed.

  Lemma exchange_sums {n m} (a : 'I_n -> 'I_m -> R) :
    \sum_(i<n) \sum_(j<m) (a i j) = \sum_(j<m) \sum_(i<n) (a i j).
  Proof.
    apply exchange_big.
  Qed.

 Lemma matrix_norm_inf_sub_mult {n m p} 
    (mat1 : 'M[R[i]]_(n, m))
    (mat2 : 'M[R[i]]_(m, p)) :
    Rleb (matrix_norm_inf (mat1 *m mat2))
      ((matrix_norm_inf mat1) * (matrix_norm_inf mat2)).
  Proof.
    rewrite /matrix_norm_inf /mulmx /=.
    generalize (@max_mult_distr n); intros.
    rewrite /mul /= in H.
    rewrite H.
    - apply bigmax_le2 => j.
      under eq_bigr do rewrite mxE.
      apply /RlebP.
      apply Rle_trans with
        (r2 := \sum_(i < p) (\sum_(j0 < m) normc (R:=R_rcfType) (mat1 j j0 * mat2 j0 i))).
      + apply /RlebP.
        apply sum_le => j0.
        apply normc_triang_sum.
      + rewrite exchange_sums.
        generalize (@sum_mult_distr); intros.
        rewrite /mul /= in H0.
        rewrite H0.
        apply /RlebP.
        apply sum_le => j0.
        replace  (\sum_(i < p) normc (R:=R_rcfType) (mat1 j j0 * mat2 j0 i)) with
          ((normc (R:=R_rcfType) (mat1 j j0)) * 
             (\sum_(i < p) normc (R:=R_rcfType) (mat2 j0 i))).
        * apply /RlebP.
          apply Rmult_le_compat_l.
          -- apply normc_nnegR.
          -- apply /RlebP.
             generalize (@bigmaxr_le_alt m
                           (fun j0 => (\sum_(i < p) normc (R:=R_rcfType) (mat2 j0 i))) 0 j0); intros.
             apply H1.
        * rewrite mulrC sum_mult_distr.
          apply eq_bigr => i _.
          by rewrite mulrC ComplexField.Normc.normcM.
    - apply /RlebP.
      apply bigmax_nneg => i.
      apply sum_nneg => k.
      apply normc_nneg.
  Qed.

  Lemma matrix_norm_inf_scale {n m} (mat : 'M[R[i]]_(n,m)) (c : R[i]) :
    matrix_norm_inf (scalemx c mat) = (normc c)*(matrix_norm_inf mat).
  Proof.
    rewrite /matrix_norm_inf /scalemx max_mult_distl.
    - apply eq_bigr => j _.
      rewrite sum_mult_distl.
      apply eq_bigr => k _.
      by rewrite mxE ComplexField.Normc.normcM.
    - apply normc_nnegR.
  Qed.
                              
  Lemma big_max_const (n:nat) (c : R) : n != 0%nat ->
    Rle 0 c ->
    \big[Order.max/0]_(j < n) c = c.
  Proof.
    case: n; [lia |intros n _].
    induction n.
    - rewrite big_ord_recl big_ord0 => H.
      rewrite Order.POrderTheory.max_l //.
      apply /RlebP.
      apply H.
    - rewrite big_ord_recl => H.
      rewrite IHn.
      rewrite Order.POrderTheory.max_l //.
      apply H.
  Qed.

  Lemma normc_conj (x : R[i]) :
    ComplexField.Normc.normc x = ComplexField.Normc.normc (conjc x).
  Proof.
    case: x => rx ix /=.
    by rewrite sqrrN.
  Qed.

  Lemma normc_nth_root j (n:nat) :
    n != 0%nat ->
    normc (nth_root j n) = 1.
  Proof.
    rewrite /normc /nth_root => nN0.
    rewrite -!RpowE -!Rsqr_pow2 addrC /add /=.
    by rewrite sin2_cos2 ssrnum.Num.Theory.sqrtr1.
  Qed.    

  Lemma big_max_const_fun (n : nat) (a : 'I_n -> R) (c : R) :  n != 0%nat ->
    Rle 0 c ->
    (forall i, a i = c) ->
    \big[Order.max/0]_(i < n) (a i) = c.
  Proof.
    intros.
    under eq_bigr do rewrite H1.
    by apply big_max_const.
  Qed.

  Lemma norm_inf_const_norm (n : nat) (vec : 'rV[R[i]]_n.+1) :
    (forall i , normc (R:=R_rcfType) (vec 0 i) = 1) ->
    norm_inf vec = 1.
  Proof.
    intros.
    rewrite /norm_inf.
    apply big_max_const_fun; trivial.
    rewrite /one /=; coq_lra.
  Qed.

  Lemma pow2n0 n : (2 ^ n)%N != 0%N.
  Proof.
    by rewrite expn_eq0.
  Qed.

  Hint Immediate pow2n0.
    
  Lemma norm_inf_conj_half_roots (n : nat) :
    norm_inf (map_mx conjc (nth_roots_half n.+1)) = 1.
  Proof.
    rewrite /norm_inf /nth_roots_half.
    apply big_max_const_fun.
    - apply pow2n0.
    - rewrite /one/=; coq_lra.
    - intros.
      by rewrite !mxE -normc_conj normc_nth_root // pow2n0.
  Qed.
  
  Lemma big_sum_const (n : nat) (c : R) :
    \sum_(j<n) c = c *+ n.
  Proof.
    induction n.
    - by rewrite big_ord0 mulr0n.
    - rewrite big_ord_recl IHn.
      by rewrite mulrSr addrC.
   Qed.

  Lemma norm_inf_peval_mat_conj_even_roots (n : nat) : 
    matrix_norm_inf (peval_mat (map_mx conjc (even_nth_roots n.+1))) = (2 ^ n.+1)%:R.
  Proof.
    rewrite /matrix_norm_inf /peval_mat.
    apply big_max_const_fun.
    - apply pow2n0.
    - rewrite -INRE.
      apply pos_INR.
    - intros.
      under eq_bigr => i0 _.
      rewrite /even_nth_roots !mxE -exp_conj -normc_conj pow_nth_root' ?normc_nth_root.
      over.
      apply pow2n0.
      apply pow2n0.
      by rewrite big_sum_const.
  Qed.
  
  Lemma encode_mat_norm_inf (n : nat) :
    let pmat := peval_mat (odd_nth_roots (S n)) in
    let encmat := (conj_mat (pmat^T)) in
    Rleb (matrix_norm_inf encmat) (2^S n)%:R.
  Proof.
    rewrite /= encode_mat_prod.
    apply /RlebP.
    eapply Rle_trans.
    - apply /RlebP.
      apply matrix_norm_inf_sub_mult.
    - rewrite -norm_inf_diag norm_inf_conj_half_roots Rmult_1_l.
      rewrite norm_inf_peval_mat_conj_even_roots.
      coq_lra.
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
      apply /RlebP; apply Rmult_le_pos; apply /RlebP; apply bigmax_normc_nneg.
    - intros i x _ xn.
      rewrite Order.TotalTheory.le_maxl mxE ComplexField.Normc.normcM.
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
    rewrite /zero /=.
    f_equal.
    now apply Rle_antisym.
  Qed.

  Lemma normc_Rabs (r : R) :
    normc (RtoC r) = Rabs r.
  Proof.
    rewrite /normc /RtoC (expr2 0) mulr0 addr0.
    by rewrite ssrnum.Num.Theory.sqrtr_sqr.
  Qed.

  Lemma mx_evalZ {n} (v : 'rV[R[i]]_n.+1) (r:R) p :
    mx_eval v (r *: p) = (RtoC r) *: (mx_eval v p).
  Proof.
    apply matrixP => a b.
    rewrite !mxE /scale /= scale_polyE.
    rewrite rmorphismMP /= (map_polyC RtoC_rmorphism) /=.
    by rewrite -hornerZ /= /scale /= scale_polyE.
  Qed.

  (* following 4 lemmas show canon_norm_inf is a norm on quotient by x^+(2^n) + 1 *)
  Lemma canon_norm_infZ n (r : R) (p : {poly R}) :
    canon_norm_inf n (r *: p) = Rabs r * canon_norm_inf n p.
  Proof.
    by rewrite /canon_norm_inf !mx_evalZ norm_infZ normc_Rabs.
  Qed.

  Lemma canon_norm_inf_nneg n (p : {poly R}) :
    (zero R_ringType <= canon_norm_inf n p)%O.
  Proof.
    apply norm_inf_nneg.
  Qed.

  Lemma canon_norm_inf_triang n (p q : {poly R}) :
    (canon_norm_inf n (p + q) <= canon_norm_inf n p + canon_norm_inf n q)%O.
  Proof.
    rewrite /canon_norm_inf.
    move: (raddfD (mx_eval_rmorphism (odd_nth_roots' n)) p q) => /= ->.
    apply norm_inf_triang.
  Qed.
      
  Lemma canon_norm_inf_semi_multiplicative n (p q : {poly R}) :
    (canon_norm_inf n (p * q) <= canon_norm_inf n p * canon_norm_inf n q)%O.
  Proof.
    rewrite /canon_norm_inf rmorphM.
    apply norm_inf_semi_multiplicative.
 Qed.

  Lemma mx_eval_pow {n} (v : 'rV_n.+1) e :
    mx_eval v 'X^e = map_mx (fun c => c ^ e) v.
  Proof.
    apply eq_map_mx.
    intros ?.
    by rewrite map_polyXn hornerXn /exprz.
  Qed.


  Lemma iter_max {disp : Datatypes.unit} {T : porderType disp} i (a b: T) :
    i != 0%nat ->
    ssrnat.iter i (Order.max a) b = Order.max a b.
  Proof.
    induction i => //=.
    destruct i => // _.
    rewrite IHi //=.
    by rewrite Order.POrderTheory.max_maxxK.
  Qed.

  Lemma canon_norm_inf_pow n e :
    canon_norm_inf n 'X^e = 1.
  Proof.
    rewrite /canon_norm_inf mx_eval_pow /odd_nth_roots'.
    unfold norm_inf.
    under eq_big_seq.
    {
      intros.
      rewrite !mxE.
      rewrite /exprz.
      rewrite pow_nth_root'; try lia.
      rewrite normc_nth_root; try lia.
      over.
    }
    simpl.
    rewrite big_const_ord iter_max //.
    rewrite /Order.max.
    case: RltP => //.
    rewrite /one/zero/=.
    move/lt_IZR.
    lia.
  Qed.
  
  Lemma canon_norm_inf_C_pow n e c :
    canon_norm_inf n (c *: 'X^e) = Rabs c.
  Proof.
    by rewrite canon_norm_infZ canon_norm_inf_pow mulr1.
  Qed.

  Lemma canon_norm_inf_C n (c : R) :
    canon_norm_inf n (polyC c) = Rabs c.
  Proof.
    rewrite -(canon_norm_inf_C_pow n 0 c).
    f_equal.
    by rewrite expr0 /scale /Lmodule.scale /= scale_polyE mulr1.
  Qed.

  Lemma coef_norm1_C (c : R) :
    coef_norm1 (polyC c) = Rabs c.
  Proof.
    rewrite /coef_norm1 size_polyC.
    case: eqVneq; simpl.
    - rewrite big_ord0 => ->.
      by rewrite Rabs_R0.
    - by rewrite big_ord1 coefC.
  Qed.

  Lemma size_poly_def (p : {poly R}) :
    size (\sum_(i < size p) p`_i *: 'X^i) = size p.
  Proof.
    case: (eqVneq p 0); intros.
    - by rewrite e poly_size_0 big_ord0 poly_size_0.
    - rewrite -poly_def size_poly_eq //.
      by rewrite -lead_coefE lead_coef_eq0.
  Qed.    
    
  Lemma coef_norm1_poly_def (p : {poly R}) :
    coef_norm1 (\sum_(i < (size p)) p`_i *: 'X^i) =
      \sum_(i < (size p)) Rabs p`_i.
  Proof.
    rewrite /coef_norm1 size_poly_def.
    apply eq_big => //= i _.
    f_equal.
    by rewrite -poly_def coef_poly ltn_ord.
  Qed.
                                              
  Lemma canon_norm_inf_poly_def n m (p : {poly R}) :
        (canon_norm_inf n (\sum_(i < m) p`_i *: 'X^i) <=
           \sum_(i < m) canon_norm_inf n (p`_i *: 'X^i))%O.
  Proof.
    induction m.
    - rewrite !big_ord0 canon_norm_inf_C Rabs_R0.
      apply Order.POrderTheory.le_refl.
    - 
      move: (@big_nat_recr {poly R} 0 (add_monoid _)
               m
               0
               (fun i =>  p`_i *: 'X^i)
               (leq0n _)
            ).
      rewrite !big_mkord => ->.
      move: (@big_nat_recr R 0 (@add_monoid _)
               m
               0
               (fun i => canon_norm_inf n (p`_i *: 'X^i))
               (leq0n _)
            ).
      rewrite !big_mkord => -> /=.
      eapply Order.POrderTheory.le_trans.
      + apply canon_norm_inf_triang.
      + by apply ssrnum.Num.Theory.lerD.
  Qed.

  Lemma canon_norm_inf_le_norm1 n (p : {poly R}) :
    (canon_norm_inf n p <= coef_norm1 p)%O.
  Proof.
    rewrite -(coefK p) poly_def coef_norm1_poly_def.
    eapply Order.POrderTheory.le_trans.
    apply canon_norm_inf_poly_def.
    rewrite /Order.le /Order.POrder.le /=.
    apply /RlebP.
    right.
    apply eq_big_seq => ??.
    by rewrite canon_norm_inf_C_pow.
  Qed.

  Lemma canon_norm_inf_val n (p : {poly R}) (i : 'I_(2^n-1).+1) :
    (normc ((map_poly RtoC p).[odd_nth_roots' n 0 i]) <= canon_norm_inf n p)%O.
  Proof.
    rewrite /canon_norm_inf /norm_inf /=.
    generalize (@bigmaxr_le (2^n-1).+1 (odd_nth_roots' n) 0 (fun c => normc (map_poly RtoC p).[c]) i) => HH.
    eapply Order.POrderTheory.le_trans.
    - rewrite /Order.le/=.
      apply HH.
    - rewrite /Order.le/=.
      apply /RlebP.
      right.
      apply eq_big_seq => ??.
      f_equal.
      by rewrite /mx_eval !mxE.
  Qed.

  Lemma peval_mx_eval {n} (v :'rV[R[i]]_n.+1) (p : {poly R}) :
    size p <= n.+1 ->
    let pmat := peval_mat v in
    let pC := map_poly RtoC p in
    mx_eval v p = (pmat *m (poly_rV pC)^T)^T.
  Proof.
    intros.
    rewrite /mx_eval /peval_mat /map_mx trmx_mul trmxK /poly_rV /= /mulmx.
    apply matrixP => j k.
    rewrite !mxE /= horner_coef -map_RtoC_size.
    unfold pmat, peval_mat, pC.
    under [RHS]eq_bigr do rewrite !mxE.
    case : (eqVneq (size p) n.+1); intros.
    - rewrite e /=.
      apply eq_big_seq => ??.
      by rewrite fintype.ord1.
    - transitivity (\sum_(i0 < (size p + (n.+1-size p))%nat)
                      (map_poly (aR:=R_ringType) (rR:=ComplexField.complex_ringType R_fieldType) RtoC p)`_i0 * v 0 k ^+ i0);
        [| by have ->: (size p + (n.+1 - size p) = n.+1)%nat by lia].
      rewrite big_split_ord /=.
      rewrite !fintype.ord1.
      suff ->: ( \sum_(i0 < n.+1 - size p)
                   (map_poly (aR:=R_ringType) (rR:=ComplexField.complex_ringType R_fieldType) RtoC p)`_
                   (size p + i0) * v 0 k ^+ (size p + i0) = 0).
      { by rewrite addr0. }

      under eq_bigr => si _.
      { rewrite nth_default ?mul0r.
        - over.
        - rewrite -map_RtoC_size.
          lia.
      }
      by rewrite big_const_seq iter_addr_0 mul0rn.
  Qed.

Lemma decode_encode_scalar_mx' (n : nat):
  let pmat := (peval_mat (odd_nth_roots' (S n))) in
  pmat *m (conj_mat (pmat^T)) = scalar_mx (2^S n)%:R.
Proof.
  Proof.
    apply/matrixP.
    move/matrixP: (decode_encode_scalar_mx n) => H i j.
    have eqq: (sval (pow2_S n.+1)).+1 = (2^n.+1)%nat by (simpl; lia).
    move: (H (cast_ord eqq i) (cast_ord eqq j)).
    rewrite !mxE /= => <-.
    rewrite (big_ord_widen_leq (2^n.+1)%N); try lia.
    apply eq_big.
    - move=> [??] /=.
      by lia.
    - intros.
      by rewrite !mxE inordK.
  Qed.

  Lemma encode_mat_norm_inf' (n : nat) :
    let pmat' := peval_mat (odd_nth_roots' (S n)) in
    let encmat' := (conj_mat (pmat'^T)) in
    Rleb (matrix_norm_inf encmat') (2^S n)%:R.
  Proof.
    generalize (encode_mat_norm_inf n); intros.
    unfold matrix_norm_inf in *; simpl in *.
    rewrite (big_ord_widen_leq (2^n.+1)%N); try lia.
    apply /RlebP.
    move /RlebP in H.
    eapply Rle_trans; cycle 1.
    apply H.
    right.
    apply eq_big.
    - intros ?.
      destruct x.
      simpl.
      lia.
    - intros.
      rewrite (big_ord_widen_leq (2^n.+1)%N); try lia.
      apply eq_big.
      + intros ?.
        destruct x.
        simpl.
        lia.
      + intros.
        rewrite /odd_nth_roots /odd_nth_roots' !mxE !inordK //.
  Qed.

  
  Lemma encmat_pmat (n : nat) :
    let pmat' := peval_mat (odd_nth_roots' (S n)) in
    let encmat := (conj_mat (pmat'^T)) in
    pmat' *m ((RtoC (inv (2^S n)%:R)) *: encmat) = scalar_mx 1.
  Proof.
    intros.
    rewrite -scalemxAr /encmat /pmat' decode_encode_scalar_mx'.
    apply /matrixP => i j.
    rewrite !mxE mulrnAr -RtoCR -rmorphM /= mulrC divrr // unitfE.
    by rewrite natmul0eq pow2n0.
  Qed.

  Lemma invmx_comm (n : nat) (A B : 'M[R[i]]_n) :
    A *m B = scalar_mx 1 ->
    B *m A = scalar_mx 1.
   Proof.
     intros.
     destruct (mulmx1_unit H).
     generalize (mulmxV H1); intros.
     generalize H2; intros.
     apply (f_equal (fun z => A *m z)) in H2.
     rewrite mulmxA H mul1mx mulmx1 in H2.
     by rewrite H2 in H3.
  Qed.

  Lemma encmat_pmat_alt (n : nat) :
    let pmat' := peval_mat (odd_nth_roots' (S n)) in
    let encmat := (conj_mat (pmat'^T)) in
    ((RtoC (inv (2^S n)%:R)) *: encmat) *m pmat' = scalar_mx 1.
  Proof.
    intros.
    apply invmx_comm.
    apply encmat_pmat.
  Qed.

Lemma decode_encode_off_diag_T (n : nat):
  let pmat := (peval_mat (odd_nth_roots' (S n))) in
  forall n1 n2,
    n1 <> n2 ->
    H_inner_prod (col n1 pmat)^T (col n2 pmat)^T = C0.
Proof.
  intros.
  rewrite !tr_col -H_inner_prod_mat trmxK.
  generalize (encmat_pmat_alt n); intros.
  simpl in H0.
  apply (f_equal (fun m => trmx ((RtoC (2 ^ n.+1)%:R) *: m))) in H0.
  rewrite scalemxAl scalerA in H0.
  replace ((RtoC (2 ^ n.+1)%:R * RtoC (2 ^ n.+1)%:R^-1)) with (RtoC 1) in H0.
  - rewrite trmx_mul scale1r conj_transpose trmxK scalemx1 in H0.
    rewrite /pmat H0 tr_scalar_mx mxE.
    case: (eqVneq n1 n2); intros.
    + by rewrite e in H.
    + by rewrite /= mulr0n.
  - rewrite -rmorphM /= divff // natmul0eq.
    lia.
Qed.

  Lemma encmat_pmat_pvec (n : nat) (p : {poly R}) :
    let pmat' := peval_mat (odd_nth_roots' (S n)) in
    let encmat := (conj_mat (pmat'^T)) in
    let pvec := (poly_rV (d := (sval (pow2_S n.+1)).+1)
                   (map_poly (aR:=R_ringType)
                      (rR:=ComplexField.complex_ringType
                               R_fieldType) RtoC p))^T in
    (((RtoC (inv (2^S n)%:R)) *: encmat) *m pmat') *m pvec = pvec.
  Proof.
    by rewrite /= encmat_pmat_alt mul1mx.
  Qed.

  Lemma big_max_split {k2 : nat} (k1 : nat) (F : 'I_k2 -> R) :
    \big[Order.max/0]_(j < k2)  F j =
      Order.max
        (\big[Order.max/0]_(j < k2 | true && (j < k1)%N) F j)
        (\big[Order.max/0]_(j < k2 | true && ~~(j < k1)) F j).
  Proof.
    rewrite -Order.TotalTheory.bigmaxID.
    by apply eq_bigr.
  Qed.

Lemma big_max_nneg_with_trailing_zeros {k1 k2} (le12: k1 <= k2) (F: 'I_k2 -> R) :
    (forall i, Rle 0 (F i)) ->
    (forall i: 'I_k2 , k1 <= i -> F i = 0%R) ->
    \big[Order.max/0]_(j < k2) F j = \big[Order.max/0]_(j < k1) F (widen_ord le12 j).
 Proof.
   intros Fnneg Ftrail0.
   rewrite (big_max_split k1).
   assert (\big[Order.max/0]_(j < k2 | true && ~~ (j < k1)) F j = 0).
   {
     under eq_bigr.
     intros.
     rewrite Ftrail0; try lia.
     over.
     rewrite big_const_seq iter_fix // -RmaxE /zero/= Rmax_left //; coq_lra.
   }
   rewrite H -RmaxE Rmax_left.
   destruct k1.
   - rewrite big_ord0.
     pose G : ('I_k2 -> R_orderType) :=  fun=> 0%R.
     assert (\big[Order.max/0]_(j < k2 | true && (j < 0)) F j =
               \big[Order.max/0]_(j < k2 | true && (j < 0)) G j).
     {
       apply congr_big; trivial.
       intros ??.
       lia.
     }
     rewrite H0 /G.
     rewrite big_const_seq iter_fix // -RmaxE /zero/= Rmax_left //; coq_lra.
   - rewrite [RHS](big_ord_widen_leq k2); trivial.
     apply eq_bigr.
     intros.
     f_equal.
     apply ord_inj => /=.
     by rewrite inordK.
   - pose G : ('I_k2 -> R_orderType) :=  fun=> 0%R.
     assert ((\big[Order.max/0]_(j < k2 | true && (j < k1)%N) (G j)) = 0)%R.
     {
       rewrite /G big_const_seq iter_fix // -RmaxE /zero/= Rmax_left //; coq_lra.
     }
     rewrite -{1}H0.
     apply /RleP.
     apply (@Order.TotalTheory.le_bigmax2 _ R_orderType).
     intros.
     rewrite /G.
     apply /RleP.
     apply Fnneg.
 Qed.



         

  Lemma coef_maxnorm_pvec n (p : {poly R}) :
    size p <= 2^n.+1 ->
    let pvec := (poly_rV (d := (sval (pow2_S n.+1)).+1)
                   (map_poly (aR:=R_ringType)
                      (rR:=ComplexField.complex_ringType
                               R_fieldType) RtoC p))^T in
    coef_maxnorm p = cvec_norm_inf pvec.
  Proof.
    intros.
    rewrite /coef_maxnorm /cvec_norm_inf /norm_inf.
    assert ((sval (pow2_S n.+1)).+1 = (2^n.+1)%N).
    {
      simpl.
      lia.
    }
    case : (eqVneq (size p) (sval (pow2_S n.+1)).+1); intros.
    - rewrite e /=.
      apply eq_big_seq => k HH.
      rewrite /pvec !mxE.
      rewrite /map_poly coef_poly /=.
      case: ltP; rewrite normc_Rabs // => kbig.
      rewrite nth_default //.
      lia.
    - have le1: (size p <= (sval (pow2_S n.+1)).+1) by lia.
      rewrite (big_max_nneg_with_trailing_zeros le1).
      + apply eq_bigr => j _.
        rewrite /pvec /poly_rV !mxE.
        rewrite /= /map_poly coef_poly.
        destruct j.
        simpl in i0.
        by rewrite /= i0 normc_Rabs.
      + intros.
        apply/RleP.
        apply normc_nneg.
      + intros.
        rewrite /pvec /= /poly_rV.
        rewrite !mxE /= map_polyE.
        rewrite nth_default.
        * by rewrite ComplexField.Normc.normc0.
        * eapply leq_trans.
          -- apply size_Poly.
          -- by rewrite size_map.
  Qed.

  Lemma canon_norm_inf_pvec n (p : {poly R}) :
    size p <= 2^n ->
    let pmat' := peval_mat (odd_nth_roots'  n) in
    let pvec := (poly_rV (d := (sval (pow2_S n)).+1)
                   (map_poly (aR:=R_ringType)
                      (rR:=ComplexField.complex_ringType
                             R_fieldType) RtoC p))^T in
    canon_norm_inf n p = cvec_norm_inf (pmat' *m pvec).
  Proof.
    intros.
    rewrite /canon_norm_inf /cvec_norm_inf /norm_inf.
    apply eq_big; trivial; intros.
    f_equal.
    rewrite /odd_nth_roots' /pmat' /pvec /peval_mat !mxE /map_poly horner_poly.
    rewrite /odd_nth_roots'.
    under [RHS]eq_bigr do rewrite !mxE mulrC coef_poly.
    simpl.
    case : (eqVneq (size p) (2^n-1).+1); intros.
    - rewrite e.
      apply eq_big_seq => k HH.
      f_equal.
      assert (k < (2 ^ n - 1).+1).
      {
        by destruct k; simpl.
      }
      by rewrite H1.
    - transitivity (\sum_(i1 < size p + ((2^n-1).+1-size p)%nat)
                       (if i1 < size p then RtoC p`_i1 else 0) *
                      nth_root (2 * i + 1) (2 ^ n.+1) ^+ i1);
                [| by have ->: (size p + ((2^n-1).+1 - size p) = (2^n-1).+1)%nat by lia].
      rewrite big_split_ord /=.
      assert (\sum_(i1 < (2 ^ n - 1).+1 - size p)
                (if size p + i1 < size p then RtoC p`_(size p + i1) else 0) *
                nth_root (2 * i + 1) (2 ^ n.+1) ^+ (size p + i1) = 0).
      {
         under eq_bigr => si _.
         {
           have ->: ((size p + si < size p) = false) by lia.
           rewrite mul0r.
           over.
         } 
         by rewrite big_const_seq iter_addr_0 mul0rn.
      }
      rewrite H1 addr0.
      by apply eq_big => // [[? /= ->]].
  Qed.

  Lemma matrix_norm_inf_pmat_inv n :
    let pmat' := peval_mat (odd_nth_roots' (S n)) in
    let encmat := (conj_mat (pmat'^T)) in
    Rle (matrix_norm_inf ((RtoC (inv (2^S n)%:R)) *: encmat)) 1.
  Proof.
    generalize (encode_mat_norm_inf' n); intros.
    simpl in H.
    move /RlebP in H.
    rewrite matrix_norm_inf_scale normc_Rabs.
    apply Rmult_le_compat_l with (r := Rabs (2 ^ n.+1)%:R^-1) in H.
    - eapply Rle_trans.
      apply H.
      right.
      assert (Rlt 0  (2 ^ n.+1)%:R).
      {
        rewrite -INRE.
        apply lt_0_INR.
        lia.
      }
      rewrite Rabs_right.
      + rewrite /inv/= RmultRinvx // unitrE divff //.
        rewrite /zero/=.
        apply/eqP.
        apply Rgt_not_eq.
        apply H0.
      + left.
        rewrite -RinvE.
        * apply Rinv_0_lt_compat; trivial.
        * rewrite /zero/=.
          apply/eqP.
          apply Rgt_not_eq.
          apply H0.
   - apply Rabs_pos.    
  Qed.

  Lemma Rmult_le_1 (r1 r2 : R) :
    Rle r1 1 ->
    Rle 0 r2 ->
    Rle (r1 * r2) r2.
  Proof.
    intros.
    apply Rmult_le_compat_r with (r := r2) in H; trivial.
    by rewrite Rmult_1_l in H.
  Qed.
  
  Lemma matrix_norm_inf_pos {n m} (A : 'M[R[i]]_(n,m)) :
    Rle 0 (matrix_norm_inf A).
  Proof.
    rewrite /matrix_norm_inf.
    apply /RlebP.
    apply bigmax_nneg.
    intros.
    apply sum_nneg.
    intros.
    apply /RlebP.
    apply normc_nnegR.
  Qed.

  Theorem coef_maxnorm_le_canon_norm_inf n (p : {poly R}) :
    size p <= 2^n.+1 ->
    Rle (coef_maxnorm p) (canon_norm_inf n.+1 p).
  Proof.
    intros.
    rewrite (coef_maxnorm_pvec n) //.
    rewrite canon_norm_inf_pvec //.
    rewrite -{1}encmat_pmat_pvec /cvec_norm_inf.
    rewrite !mat_vec_norm_inf !trmxK.
    eapply Rle_trans.
    - rewrite -mulmxA.
      apply /RlebP.
      apply matrix_norm_inf_sub_mult.
    - generalize (matrix_norm_inf_pmat_inv n); intros.
      simpl in H0.
      apply Rmult_le_1; trivial.
      apply matrix_norm_inf_pos.
  Qed.

  Theorem canon_norm_inf_bounds n (p : {poly R}) :
    size p <= 2^n.+1 ->
    (coef_maxnorm p <= canon_norm_inf n.+1 p <= coef_norm1 p)%O.
  Proof.
    intros.
    apply /andP.
    split.
    - apply /RleP.
      by apply coef_maxnorm_le_canon_norm_inf.
    - apply canon_norm_inf_le_norm1.
  Qed.

  Lemma canon_norm_zero_mod_qpoly n (p : {poly R}) :
    canon_norm_inf n p = 0 ->
    Pdiv.Ring.rmodp (R:=R_ringType) p ('X^(2 ^ n) + 1%:P) = 0.
  Proof.
    intros.
    apply odd_nth_roots_minpoly_mult_R.
    intros.
    unfold root.
    apply /eqP.
    generalize (canon_norm_inf_val n p); intros.
    destruct i.
    assert (m < (2^n-1).+1) by lia.
    specialize (H0 (Ordinal H1)).
    rewrite H in H0.
    apply ComplexField.Normc.eq0_normc.
    apply Order.POrderTheory.le_anti.
    apply /andP; split.
    - replace (odd_nth_roots n 0 (Ordinal (n:=2^n) i)) with
        (odd_nth_roots' n 0 (Ordinal (n:=(2^n-1).+1) H1)).
      + apply H0.
      + by rewrite /odd_nth_roots' /odd_nth_roots !mxE.
    - apply normc_nneg.
  Qed.

(* following only holds on quotient ring by x^+(2^n) + 1 
  Lemma canon_norm_inf_pos_def n p :
    canon_norm_inf n p = 0 -> p = 0.
*)


  Lemma normc_conj_mul (x y : R[i]) :
    normc (x * y) = normc (x * (conjc y)).
  Proof.
    by rewrite !ComplexField.Normc.normcM (normc_conj y).
  Qed.
    
  Lemma normc_conj_add (r : R) (x y : R[i]) :
    normc (x + y) = normc (conjc x + conjc y).
  Proof.
    by rewrite -rmorphD normc_conj.
  Qed.

  Lemma normc_conj_exp (x : R[i]) n :
    normc (x ^+ n) = normc ((conjc x) ^+ n).
  Proof.
    by rewrite -rmorphXn normc_conj.
  Qed.

  Lemma RtoC1 : RtoC 1 = 1.
  Proof.
    by [].
  Qed.

  Lemma RtoC0E (c:R) : (RtoC c == 0) = (c == 0).
  Proof.
    by rewrite /RtoC !eqE /= !eqE /= eqxx !andbT.
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
    pc.[x]^*%C = pc.[x^*%C].
  Proof.
    case: p => l llast.
    rewrite /horner /= !map_polyE /=.
    have/PolyK->: seq.last (RtoC 1) (seq.map RtoC l) != 0
      by rewrite seq.last_map RtoC0E.
    move => {llast}.
    elim: l => /=.
    - by rewrite oppr0.
    - move=> a l <-.
      by rewrite rmorphD rmorphM /RtoC /= oppr0.
  Qed.

  Lemma rpoly_eval_conj_R (p : {poly R}) (x : R[i]) :
    let pc := map_poly RtoC p in 
    pc.[x] = pc.[x]^*%C ->
    pc.[x] = pc.[x^* %C].
  Proof.
    move=> /= -> . by rewrite rpoly_eval_conj.
  Qed.

  Lemma normc_conj_poly (p : {poly R}) (x : R[i]) :
    let pc := map_poly RtoC p in 
    normc (pc.[x]) = normc (pc.[x^*%C]).
  Proof.
    by rewrite /= -rpoly_eval_conj normc_conj.
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

  Lemma mul_dvdn_l (x d1 d2:nat) :
    (d1 * d2 %| x)%N -> (d1 %| x)%N.
   Proof.
     eapply dvdn_trans.
     apply dvdn_mulr.
     by apply dvdnn.
   Qed.

  Lemma mul_dvdn_r (x d1 d2:nat) :
    (d1 * d2 %| x)%N -> (d2 %| x)%N.
  Proof.
    rewrite mulnC.
    by apply mul_dvdn_l.
  Qed.

  Lemma modn_muln (x y b1 b2:nat) :
    x == y %[mod b1 * b2] -> x == y %[mod b1].
  Proof.
    wlog le_yx : x y / y <= x; last by (rewrite !eqn_mod_dvd //; apply mul_dvdn_l).
    by have [?|/ltnW ?] := leqP y x; last rewrite !(eq_sym (x %% _)%N); apply.
  Qed.

  Section unity.
    Context {T : comRingType}
            (z : T).

  Lemma two_pow_prim_root_alt (n:nat) :
    z ^+ (2^n) <> 1 ->
    z ^+ (2^n.+1) = 1 ->
    primitive_root_of_unity (2^(n.+1)) z.
  Proof.
    intros zpow_n1 zpow1.
    assert (root_of_unity (2^(n.+1)) z).
    {
      by apply /unity_rootP.
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
        by rewrite HH exprM (prim_expr_order i) Theory.expr1n in zpow_n1.
      }
      by rewrite HH in i.
  Qed.

  Lemma two_pow_prim_root (n:nat) :
    -(one T) <> (one T) ->
    z ^+ (2^n) = -1 ->
    primitive_root_of_unity (2^(n.+1)) z.
  Proof.
    intros onem1 zpowm1.
    apply two_pow_prim_root_alt.
    - by rewrite -zpowm1 in onem1.
    - by rewrite expnSr exprM zpowm1 expr2 mulrNN mulr1.
  Qed.

  Lemma unity_gcd e1 e2 :
    z^+e1 = 1  ->
    z^+e2 = 1  ->
    z^+(gcdn e1 e2) = 1.
  Proof.
  intros.
  destruct e2.
  - by rewrite gcdn0.
  - assert (0 < e2.+1) by lia.
    destruct (egcdnP e1 H1).
    apply (f_equal (fun y => y^+kn)) in H.
    rewrite -exprM mulnC expr1n in H.
    apply (f_equal (fun z => z^+km)) in H0.
    by rewrite -exprM mulnC e exprD expr1n H mul1r gcdnC in H0.
 Qed.

Lemma modn_sub i j m :
  i >= j ->
  (i == j %[mod m]) = (i - j == 0 %[mod m]).
Proof.
  move/eqn_mod_dvd->.
  by rewrite mod0n.
Qed.

Lemma modn_sub_iff i j m :
  i >= j ->
  i = j %[mod m] <-> i - j = 0 %[mod m].
Proof.
  move/modn_sub=>eqq.
  split; move/eqP
  ; [rewrite eqq | rewrite -eqq]
  ; by move/eqP.
Qed.

Lemma prim_root_inv (k n : nat) :
  primitive_root_of_unity (n.+1) z ->
  k < n.+1 ->
  (z^+k) * (z ^+ (n.+1 - k)) = 1.
Proof.
  intros.
  rewrite -exprD.
  replace (k + (n.+1-k))%N with (n.+1)%N by lia.
  by apply prim_expr_order.
Qed.

Lemma prim_root_inv' (k n : nat) :
  n != 0%N ->
  primitive_root_of_unity n z ->
  k < n ->
  (z^+k) * (z ^+ (n - k)) = 1.
Proof.
  intros.
  rewrite -exprD.
  replace (k + (n-k))%N with (n)%N by lia.
  by apply prim_expr_order.
Qed.

Lemma prim_root_pow_unique (k1 k2 n : nat) :
  primitive_root_of_unity n z ->
  z ^+ k1 = z^+ k2 <-> k1 = k2 %[mod n].
Proof.
  intros.
  generalize (eq_prim_root_expr H k1 k2); intros.
  split; intros.
  - move /eqP in H1.
    rewrite H0 in H1.
    apply (eqP H1).
  - move /eqP in H1.
    rewrite -H0 in H1.  
    apply (eqP H1).
Qed.
  
Lemma two_pow_prim_root_inv (k n : nat) :
  primitive_root_of_unity (2^n.+1) z ->
  k < 2^n.+1 ->
  (z^+k) * (z ^+ (2^n.+1 - k)) = 1.
Proof.
  intros.
  apply prim_root_inv'; lia.
Qed.

Lemma prim_root_pow_sqr (k n : nat) :
  n != 0%N ->
  primitive_root_of_unity (2*n)%N z ->
  (z^+k)^+2 = 1 ->
  k = 0 %[mod n].
Proof.
  intros.
  rewrite -exprM mulnC in H1.
  generalize (prim_root_pow_unique (2*k) 0%N (2*n)%N H0); intros.
  rewrite expr0 in H2.
  assert (0 < 2*n) by lia.
  rewrite H2 -muln_modr (modn_small H3) in H1.
  assert (k %% n = 0)%N by lia.
  by rewrite H4 mod0n.
Qed.

Lemma zero_modn_mod2n (k n : nat) :
  0 < n ->
  k = 0 %[mod n] ->
  k = 0 %[mod 2*n] \/ k = n %[mod 2*n].
Proof.
  move=> npos /eqP.
  move: (dvdn_eq n k).
  rewrite (modn_small npos) /dvdn => -> eqq1.

  have ->: (k = k%/n * n)%N.
  {
    symmetry.
    by apply /eqP.
  }
  rewrite -muln_modl.
  have [-> | eqq]: (((k %/n) %% 2 = 0) \/ ((k %/n) %% 2 = 1))%N.
  {
    have:  ((k %/ n) %% 2)%N < 2 by by apply ltn_pmod.
    lia.
  }
  - left; by rewrite mod0n mul0n.
  - right.
    rewrite -{3}(mul1n n) eqq -muln_modl.
    lia.
Qed.

Lemma two_pow_prim_root_m1 (k n : nat) :
    primitive_root_of_unity (2^n.+1) z ->
    -(one T) <> (one T) ->
    z^+k = -1 ->
    k = 2^n %[mod 2^n.+1].
  Proof.
    intros.
    assert (2^n != 0)%N by lia.
    rewrite expnS in H.
    assert (z ^+ k ^+ 2 = 1).
    {
      by rewrite H1 expr2 mulrNN mulr1.
    }
    generalize (prim_root_pow_sqr k (2^n) H2 H H3); intros.
    assert (k <> 0 %[mod 2^n.+1]).
    {
      unfold not; intros.
      rewrite -expnS in H.
      generalize (prim_root_pow_unique k 0 (2^n.+1) H); intros.
      rewrite expr0 H1 in H6.
      by rewrite -H6 in H5.
    }
    clear H H0 H1 H3 z T.
    assert (0 < 2^n)%N by lia.
    generalize (zero_modn_mod2n k (2^n) H H4); intros.
    rewrite expnS.
    rewrite expnS in H5.
    by destruct H0.
 Qed.

Lemma two_pow_prim_root_m1_alt (n : nat) :
  primitive_root_of_unity (2^n.+1) z ->
  -(one T) <> (one T) ->
  z^+(2^n) <> -1 ->
  not (exists k, z^+k = -1).
Proof.
  intros.
  unfold not; intros.
  destruct H2.
  generalize (two_pow_prim_root_m1 x n H H0 H2); intros.
  generalize (prim_expr_mod H); intros.
  by rewrite -H4 H3 H4 in H2.
Qed.

  Lemma odd_pow_prim_root (n:nat) :
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

  Lemma pow2_odd_inv (j n :nat) :
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

  Lemma odd_pow_prim_root_inv (j n:nat) :
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

  Lemma odd_pow_prim_inv (n:nat) :
    z ^+ (2^n) = -1 ->
    forall j,
      ((z ^+ j) ^+ (2^(S n) -1)) * (z ^+ j) = 1.
  Proof.
    intros.
    rewrite -exprM -exprD /= -{2}(muln1 j) -mulnDr mulnC exprM.
    rewrite addBnCAC; try lia.
    by rewrite subnn add0n expnS mulnC exprM H expr2 mulrNN mulr1 expr1n.
  Qed.    

  Lemma odd_pow_prim_root_inj (j n:nat) (z2 : T) :
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

(*
  Lemma odd_pow_prim_roots_perm (j n : nat) :
    let l := mkseq (fun i => nth_root (2 * i + 1) (2 ^ (S n))) (2^n) in
    Permutation l (map (fun r => r^+(2*j+1)) l).
  Proof.
    apply NoDup_Permutation_bis.
    - assert (uniq (mkseq (fun i : nat => nth_root (2 * i + 1) (2 ^ n.+1)) (2 ^ n))).
      {
        apply /mkseq_uniqP.
        intros ?????.
        rewrite /in_mem /mem /= in H.
        rewrite /in_mem /mem /= in H0.
        destruct (pow2_S (S n)).
        rewrite (eqP i) -nth_root_eq -(eqP i) in H1.
        rewrite !Nat.mod_small in H1; try rewrite expnS; try lia.
      }
      admit.
    - apply Nat.eq_le_incl.
      apply map_length.
    - intros ??.
      assert (odd (2*j+1)) by lia.
      generalize (odd_pow_prim_root_inv (2*j+1) n H0); intros.
      
*)
  Lemma nth_root_eq' j k (n:nat) : n != 0%nat ->
    j mod n = k mod n <->
      nth_root j n = nth_root k n.
  Proof.
    destruct n; [lia |]=>_.
    apply nth_root_eq.
  Qed.

  Lemma expn_n0 (c:nat) n : c != 0%nat -> expn c n != 0%nat.
  Proof.
    lia.
  Qed.


  Lemma iff_eqb (a b:bool) : (a <-> b) <-> a = b.
  Proof.
    destruct a; destruct b; simpl in *; firstorder.
    elim H => //.
  Qed.

  Lemma odd_rep (n : nat) :
    odd n -> n = (2*(n%/2)+1)%N.
  Proof.
    intros.
    generalize (divn_eq n 2); intros.
    assert (n %% 2 = 1)%N.
    {
      by rewrite modn2 H.
    }
    by rewrite H1 in H0; lia.
  Qed.


  Lemma modn2_odd (x : nat) :
    odd x <-> (x %% 2 = 1)%N.
  Proof.
    rewrite modn2.
    by case: (odd _).
  Qed.

  Lemma pow2_odd_rem1_odd (x n : nat) :
    (x %% 2^(n.+1) = 1)%N -> odd x.
  Proof.
    intros.
    rewrite expnS in H.
    have: (x %% 2 = 1)%N.
    {
      assert (1 %% (2 * 2^n) = 1)%N.
      {
        rewrite modn_small; lia.
      }
      rewrite -{3}H0 in H.
      move /eqP in H.
      apply modn_muln in H.
      move /eqP in H.
      rewrite H.
      rewrite modn_small; trivial.
    }
    by rewrite modn2_odd.
  Qed.
  
  Lemma pow2_odd_inv_aux (j x n : nat) :
    ((x * (2*j+1)) %% 2^(n.+1) = 1)%N ->
    exists x0, x = (2*x0+1)%N.
  Proof.
    intros.
    exists (x%/2)%N.
    apply odd_rep.
    apply pow2_odd_rem1_odd in H.
    rewrite oddM in H.
    move /andP in H.
    tauto.
  Qed.

  Lemma odd_pow_prim_roots_perm_eq (j n : nat) :
    let l := mkseq (fun i => nth_root (2 * i + 1) (2 ^ (S n))) (2^n) in
    perm_eq l (map (fun r => r^+(2*j+1)) l).
  Proof.
    assert (uniq (mkseq (fun i : nat => nth_root (2 * i + 1) (2 ^ n.+1)) (2 ^ n))).
    {
      apply /mkseq_uniqP.
      intros ?????.
      rewrite /in_mem /mem /= in H.
      rewrite /in_mem /mem /= in H0.
      destruct (pow2_S (S n)).
      rewrite (eqP i) -nth_root_eq -(eqP i) in H1.
      rewrite !Nat.mod_small in H1; try rewrite expnS; try lia.
    }
    assert (odd (2*j+1)) by lia.
    destruct (pow2_odd_inv (2*j+1) n H0).
    rewrite mulnC modulo_modn in e.      
    apply uniq_perm; trivial.
    - rewrite map_inj_in_uniq // => a b.
      rewrite /mkseq => /mapP-[i inth ->] /mapP-[k knth ->].
      do 2 rewrite pow_nth_root' ?expn_n0 //.
      do 2 rewrite -nth_root_eq' ?expn_n0 //.
      rewrite !modulo_modn => HH.
      apply (f_equal (fun k => ((x %% 2^n.+1) * k) %% 2^n.+1)%N) in HH.
      do 2 rewrite modnMm mulnA -modnMm e mul1n in HH.
      by rewrite !modn_mod in HH.
    - move=> a.
      apply iff_eqb.
      split; rewrite /mkseq -map_comp /comp => /mapP-[i inth ->]; apply/mapP.
      + assert (exists x0, (2 * x0 +1)*(2 * j +1) mod 2^n.+1 = (2 * i +1)%N mod 2^n.+1).
        {
          destruct (pow2_odd_inv_aux _ _ _ e).
          rewrite H1 in e.
          exists ((2*(x0 * i)+x0+i)%N).
          rewrite !modulo_modn.
          replace (2 * (2 * (x0 * i) + x0 + i) + 1)%N with ((2 * x0 + 1)*(2 * i + 1))%N by lia.
          rewrite -mulnA (mulnC (2 * i + 1)%N _) mulnA.
          rewrite -modnMm e mul1n.
          by rewrite modn_mod.
        }
        destruct H1.
        exists (x0 mod 2^n).
        * rewrite mem_iota.
          apply /andP.
          split; try lia.
          rewrite add0n.
          generalize (Nat.mod_upper_bound x0 (2^n)); lia.
        * rewrite pow_nth_root'; try lia.
          rewrite -nth_root_eq'; try lia.
          rewrite -H1.
          rewrite (mulnC (2 * x0 + 1)%N).
          rewrite !modulo_modn -modnMm -(modnMm (2*j+1)%N).
          do 2 f_equal.
          rewrite muln_modr -expnS.
          assert (1 < 2^n.+1) by lia.
          generalize (modn_small H2); intros.
          by rewrite -{6}H3 modnDm.
      + exists ((2*(i*j)+i+j)%N mod 2^n).
        * rewrite mem_iota.
          apply /andP.
          split; try lia.
          rewrite add0n.
          generalize (Nat.mod_upper_bound  (2 * (i * j) + i + j)  (2^n)); lia.
        * rewrite pow_nth_root'; try lia.
          rewrite -nth_root_eq'; try lia.
          rewrite !modulo_modn muln_modr -expnS.
          assert (1 < 2^n.+1) by lia.
          generalize (modn_small H1); intros.
          rewrite -{9}H2 modnDm.
          f_equal; lia.
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
     
 
