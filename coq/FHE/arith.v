Require Import Reals Lra Lia List Permutation.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix Rstruct complex seq fingroup.
From mathcomp Require Import ssralg ssrfun.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv ssrint zmodp eqtype ssrbool div.

Import ssralg.GRing.
Require Import nth_root encode.

Ltac coq_lra := lra.
From mathcomp Require Import lra.

Set Bullet Behavior "Strict Subproofs".


Local Open Scope ring_scope.


Record ENCODE : Type :=
  mkENCODE
    { clear : {poly int} ;
      scale : nat
    }.

Record FHE : Type := 
  mkFHE
    { q : nat; 
      cypher : {poly {poly 'Z_q}} ;
      norm_bound : R ; 
      noise_bound : R
    }.




Definition FHE_add {q : nat}  (P Q : {poly {poly 'Z_q}} ) := P + Q.

Definition FHE_mult_base {q : nat} (P Q : {poly {poly 'Z_q}} ) := P * Q.

Definition pliftc {q : nat} (p : nat) (c : 'Z_q) : 'Z_(p*q) := inZp c.

Definition plift {q : nat} (p : nat) (s : {poly 'Z_q}) : {poly 'Z_(p*q)} :=
  map_poly (pliftc p) s.

Definition zliftc {q : nat} (c : 'Z_q) : int :=
  if (c <= q/2) then c%:Z else c%:Z - q%:Z.

Lemma modp_small (q : nat) (m : nat) :
  m < (Zp_trunc q).+2 ->
  nat_of_ord (intmul (one (Zp_ringType (Zp_trunc q))) (Posz m)) = m.
Proof.
  rewrite /intmul Zp_nat /=.
  by apply/modn_small.
Qed.

Lemma modpp (q : nat) :
  nat_of_ord (intmul (one (Zp_ringType (Zp_trunc q))) (Posz (Zp_trunc q).+2)) = 0%nat.
Proof.
  by rewrite /intmul Zp_nat /= modnn.
Qed.

Lemma zliftc_valid {q : nat} (c : 'Z_q) :
  c = (zliftc c) %:~R.
Proof.
  unfold zliftc.
  case: (c <= q/2).
  - destruct c.
    apply ord_inj => /=.
    by rewrite modp_small.
  - destruct c.
    rewrite intrD.
    assert (intmul (one (Zp_ringType (Zp_trunc q))) (opp (Posz q)) = 0).
    {
      admit.
    }
    rewrite H addr0.
    apply ord_inj => /=.
    by rewrite modp_small.
Admitted.

Definition zlift {q : nat} (a : {poly 'Z_q}) : {poly int} :=
  map_poly zliftc a.

Lemma zlift0 {q : nat} (a : {poly 'Z_q}) :
  a = 0 -> 
  zlift a = 0.
Proof.
  intros.
  rewrite /zlift /zliftc H.
  apply map_poly0.
Qed.  

Lemma zlift0_alt {q : nat} :
  zlift (zero (poly_zmodType (Zp_ringType (Zp_trunc q)))) = 0.
Proof.
  rewrite /zlift /zliftc.
  apply map_poly0.
Qed.  

(* 0 <= rand < 1 *)

From mathcomp Require Import order.

Definition upi (c:R) : int := ssrZ.int_of_Z (up c).

Definition ran_round (x rand : R) : int :=
  let hi := upi x in
  if (Order.lt (hi%:~R - x) rand)%R then hi else (hi - 1).

Definition nearest_round (x : R) : int := ran_round x (1/2)%R.

Definition nearest_round_int (n d : int) : int := nearest_round ((n %:~R)/(d %:~R))%R.

Lemma IZRE (n : Z) : IZR n = (ssrZ.int_of_Z n)%:~R.
Proof.
  destruct n.
  - by rewrite /intmul /= /IZR R00.
  - by rewrite /IZR -INR_IPR INRE /ssrZ.int_of_Z /intmul.
  - rewrite /IZR -INR_IPR INRE /ssrZ.int_of_Z /intmul /opp /=.
    f_equal; f_equal.
    lia.
Qed.    

Lemma IZREb (n : int) :  n%:~R = IZR (ssrZ.Z_of_int n).
Proof.
  by rewrite -{1}(ssrZ.Z_of_intK n) -IZRE.
Qed.

Lemma up_int_add (n : Z) (c : R) :
  up (Rplus (IZR n) c) = Zplus n (up c).
Proof.
  symmetry.
  destruct (archimed c).
  apply tech_up; rewrite plus_IZR; coq_lra.
Qed.

Lemma upi_intl (n : int) (c : R) :
  upi ((n%:~R) + c) = n + upi c.
Proof.
  rewrite /upi !IZREb up_int_add.
  lia.
Qed.

Lemma upi0 :
  upi 0 = 1.
Proof.
  rewrite /upi -(tech_up 0 1); try coq_lra.
  lia.
Qed.

Lemma nearest_round_int0 (d : int) :
  nearest_round_int 0 d = 0.
Proof.
  rewrite /nearest_round_int /nearest_round /ran_round.
  rewrite mul0r upi0 oppr0 addr0 addrN.
  rewrite /intmul /=.
  rewrite ssrnum.Num.Theory.ltr_pdivlMr // mul1r.
  by rewrite /natmul/= ssrnum.Num.Theory.gtrDl ssrnum.Num.Theory.ltr10.
Qed.

Lemma nearest_round_int_add (n1 : int) (c : R) :
  nearest_round (n1 %:~R + c)%R = n1 + nearest_round c.
Proof.
  rewrite /nearest_round /ran_round.
  have ->: (upi (n1%:~R + c))%:~R - (n1%:~R + c)%R = ((upi c)%:~R - c).
  {
    rewrite upi_intl; lra.
  }
  case: Order.TotalTheory.ltP => _ ; by rewrite upi_intl; lra.
Qed.

Lemma nearest_round_int_mul_add (n1 n2 d : int) :
  d <> 0 ->
  nearest_round_int (n1 * d + n2) d = n1 + nearest_round_int n2 d.
Proof.
  intros.
  rewrite /nearest_round_int -nearest_round_int_add.
  rewrite intrD intrM mulrDl.
  rewrite -mulrA divff.
  - f_equal; lra.
  - rewrite intr_eq0.
    by apply/eqP.
Qed.

Lemma nearest_round_int_mul_add_r (n1 n2 d : int) :
  d <> 0 ->
  nearest_round_int (n1 + d * n2) d = nearest_round_int n1 d + n2.
Proof.
  intros.
  rewrite mulrC addrC nearest_round_int_mul_add //.
  lia.
Qed.

Lemma nearest_round_int_add2 (n1 n2 d : int) :
  d <> 0 ->
  let sum := nearest_round_int n1 d + nearest_round_int n2 d in
  `|nearest_round_int (n1 + n2) d - sum| <= 1.
Proof.
  intros.
  rewrite /= /nearest_round_int /nearest_round /ran_round.
  Admitted.

Definition div_round (a : {poly int}) (d : int) : {poly int} :=
  map_poly (fun c => nearest_round_int c d) a.

Lemma div_round0 (den : int) :
  div_round (zero (poly_zmodType int_Ring)) den = 0.
Proof.
  rewrite /div_round.
  apply map_poly0.
Qed.

Lemma div_round_mul_add (a b : {poly int}) (d : int) :
  d <> 0 ->
  div_round (a + d *: b) d = div_round a d + b.
Proof.
  intros.
  rewrite /div_round /map_poly -polyP.
  intros ?.
  rewrite !coefD !coef_poly coefD coefZ.
  case: ltP.
  - rewrite nearest_round_int_mul_add_r //.
    case : ltP; intros.
    + by [].
    + rewrite nth_default /=.
      * by rewrite nearest_round_int0.
      * apply/leP.
        by apply Nat.nlt_ge.
  - intros.
    case : ltP; intros.
    + admit.
    + admit.
 Admitted.

Definition div_round_q {q : nat} (p : {poly 'Z_q}) (den : int) : {poly int} :=
  div_round (zlift p) den.

Definition q_reduce (q : nat) (p : {poly int}) : {poly 'Z_q} :=
  map_poly (fun c => c%:~R) p.

Lemma q_reduce_is_rmorphism (q : nat) :
  rmorphism (q_reduce q).
Proof.
  unfold q_reduce.
  apply map_poly_is_rmorphism.
Qed.        

Canonical q_reduce_rmorphism (q : nat) := RMorphism (q_reduce_is_rmorphism q).

From mathcomp Require Import order.
Definition zabs (c : int):int := (absz c)%:Z.

Definition int_coef_maxnorm (p : {poly int}):int := \big[Order.max/0]_(j < seq.size p)  zabs p`_ j.

Definition public_key {q : nat} (e s : {poly int}) (a : {poly 'Z_q})  : {poly {poly 'Z_q}} :=
  Poly [:: (- a * (q_reduce q s) + (q_reduce q e)); a].

Definition FHE_encrypt {q : nat} (p : {poly 'Z_q}) (v e0 e1 : {poly int}) (evkey : {poly {poly 'Z_q}}) :=
  Poly [:: (p + q_reduce q e0); q_reduce q e1] + (q_reduce q v) *: evkey.

Definition FHE_decrypt {q : nat} (s : {poly int}) (pp : {poly {poly 'Z_q}}) :=
  pp.[q_reduce q s].

Lemma decrypt_encrypt {q : nat} (e s v e0 e1 : {poly int}) (a p : {poly 'Z_q}) :
  FHE_decrypt s (FHE_encrypt p v e0 e1 (public_key e s a)) = 
    p + (q_reduce q e0) + q_reduce q e1 * q_reduce q s + q_reduce q v * q_reduce q e.
Proof.
  rewrite /FHE_decrypt /FHE_encrypt /public_key.
  rewrite hornerD hornerZ !horner_Poly /= mul0r !add0r.
  rewrite !mulrDr !addrA.
  f_equal.
  by rewrite -addrA -mulrDr -mulrDl subrr mul0r mulr0 addr0 -addrA addrC.
Qed.  

Lemma decrypt_add {q : nat} (P Q : {poly 'Z_q}) (PP QQ : {poly {poly 'Z_q}}) (s : {poly int}) :
  FHE_decrypt s PP = P ->
  FHE_decrypt s QQ = Q ->
  FHE_decrypt s (FHE_add PP QQ) = P + Q.
Proof.
  rewrite /FHE_decrypt /FHE_add.
  intros.
  by rewrite hornerD H H0.
Qed.

Lemma decrypt_mult_base {q : nat} (P Q : {poly 'Z_q}) (PP QQ : {poly {poly 'Z_q}}) (s : {poly int}) :
  FHE_decrypt s PP = P ->
  FHE_decrypt s QQ = Q ->
  FHE_decrypt s (FHE_mult_base PP QQ) = P * Q.
Proof.
  rewrite /FHE_decrypt /FHE_mult_base.
  intros.
  by rewrite hornerM H H0.
Qed.

Definition key_switch_key {q p : nat} (s s2 e : {poly int}) (a : {poly 'Z_(p*q)}) : {poly {poly 'Z_(p*q)}} := 
  Poly [:: (-a * (q_reduce (p * q) s) + (q_reduce (p * q) e) + (q_reduce (p * q) (s2 *+ p))); a].

Definition ev_key {q p : nat} (s e : {poly int}) (a : {poly 'Z_(p*q)}) :=
  key_switch_key s (exp s 2) e a.

Definition linearize {q p : nat} (c0 c1 c2 : {poly 'Z_q}) 
  (evkey : {poly {poly 'Z_(p*q)}}) :=
  Poly [:: c0; c1] +
    map_poly (fun P => q_reduce q (div_round_q ((plift p c2) * P) (p%:Z)))
                               evkey.


Lemma linearize_prop  {q p : nat} (c2 : {poly 'Z_q}) (s e : {poly int}) (a : {poly 'Z_(p*q)}) :
  (map_poly (fun P => q_reduce q (div_round_q ((plift p c2) * P) (p%:Z)))
     (ev_key s e a)).[q_reduce q s] = 
    c2 * (q_reduce q (exp s 2)) + q_reduce q (div_round_q ((plift p c2) * (q_reduce (p * q) e)) p). 
Proof.
  rewrite /ev_key /key_switch_key.
  rewrite map_Poly_id0.
  - rewrite horner_Poly /= mul0r add0r mulrDr.
Admitted.

Definition rescale {q1 q2 : nat} (p : {poly 'Z_(q1 * q2)}) : {poly 'Z_q2} :=
  q_reduce q2 (div_round_q p q1%:Z).

Definition FHE_mult  {q p : nat} (P Q : {poly {poly 'Z_q}}) 
  (evkey : {poly {poly 'Z_(p*q)}}) :=
  let PQ := FHE_mult_base P Q in
  linearize (PQ`_0) (PQ`_1) (PQ`_2) evkey.

Lemma decrypt_mult {p q : nat} (P Q : {poly 'Z_q}) (PP QQ : {poly {poly 'Z_q}}) 
  (s e : {poly int}) (a : {poly 'Z_(p*q)}) :
  FHE_decrypt s PP = P ->
  FHE_decrypt s QQ = Q ->
  size PP = 2%N ->
  size QQ = 2%N ->
  FHE_decrypt s (FHE_mult PP QQ (ev_key s e a)) = 
    P * Q + q_reduce q (div_round_q (plift p (PP * QQ)`_2 * q_reduce (p * q) e) p).
Proof.
  intros.
  rewrite -(decrypt_mult_base P Q PP QQ s) //.
  rewrite /FHE_mult /linearize /FHE_mult_base /FHE_decrypt hornerD.
  rewrite linearize_prop.
  assert (size (PP * QQ) <= 3%N).
  {
    generalize (size_mul_leq PP QQ); intros.
    by rewrite H1 H2 in H3.
  }
  replace (q_reduce q (s ^+ 2)) with
    ((q_reduce q s) ^+ 2).
  - assert (PP * QQ = Poly [:: (PP * QQ)`_0; (PP * QQ)`_1; (PP * QQ)`_2]).
    {
      replace (PP * QQ) with (take_poly 3 (PP * QQ)) at 1.
      - unfold take_poly.
        rewrite -polyP.
        intros ?.
        rewrite coef_poly coef_Poly.
        case: leqP => ineq.
        + by rewrite nth_default.
        + by rewrite -(nth_mkseq 0 (fun i => (PP * QQ)`_i) ineq).
      - rewrite take_poly_id //.
    }
    rewrite {5}H4 !horner_Poly /= mul0r !add0r mulrDl addrC -!addrA.
    f_equal.
    + by rewrite expr2 mulrA.
    + by rewrite addrC addrA.
  - by rewrite rmorphXn.
Qed.

Definition key_switch {q p : nat} (c0 c1 : {poly 'Z_q})
  (ks_key : {poly {poly 'Z_(p*q)}}) : {poly {poly 'Z_q}} :=
  c0%:P + map_poly (fun P => q_reduce q (div_round_q ((plift p c1) * P) (p%:Z)))
                   ks_key.
  
Definition FHE_automorphism  {q p : nat} (s e : {poly int}) 
                     (a : {poly 'Z_(p*q)}) (P : {poly {poly 'Z_q}}) (j : nat) :=
  key_switch (comp_poly 'X^(2*j+1) P`_0)
    (comp_poly 'X^(2*j+1) P`_1)
    (key_switch_key s (comp_poly 'X^(2*j+1) s) e a).

Lemma decrypt_FHE_automorphism_base  {q p : nat} (s : {poly int}) (P : {poly 'Z_q})
  (PP : {poly {poly 'Z_q}}) (j : nat) :
  FHE_decrypt s PP = P ->
  comp_poly 'X^(2*j+1) P = FHE_decrypt (comp_poly 'X^(2*j+1) s)
                                       (map_poly (comp_poly 'X^(2*j+1)) PP).
Proof.
  rewrite /FHE_decrypt.
  intros.
  replace (q_reduce q (s \Po 'X^(2 * j + 1))) with
    (comp_poly 'X^(2*j+1) (q_reduce q s)).
  - by rewrite horner_map /= H.
  - rewrite /q_reduce map_comp_poly /=.
    f_equal.
    by rewrite map_polyXn.
Qed.
    
