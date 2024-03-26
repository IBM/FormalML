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

Definition zlift {q : nat} (a : {poly 'Z_q}) : {poly int} :=
  map_poly (fun c => (nat_of_ord c)%:Z) a.

Definition rlift (a : {poly int}) : {poly R} :=
  map_poly (fun c => c%:~R) a.

Definition nearest_round_int (c : R) : int := ssrZ.int_of_Z (nearest_round c).

Definition polyR_divz (a : {poly R}) (d : int) : {poly int} :=
  map_poly (fun c => nearest_round_int (c / d%:~R)) a.

Definition div_round (p : {poly int}) (den : int) : {poly int} :=
  polyR_divz (rlift p) den.

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
  - rewrite horner_Poly /= mul0r add0r.
    admit.
  - rewrite mulr0.
    rewrite /div_round_q.
    admit.
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
    P * Q + q_reduce q (div_round_q ((plift p (PP * QQ)`_2) * (q_reduce (p * q) e)) p). 
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
    rewrite {4}H4.
    rewrite !horner_Poly /= mul0r !add0r.
(*
    rewrite mulrDl.
    rewrite addrC -!addrA.
    f_equal.
    by rewrite expr2 mulrA.
  - by rewrite rmorphXn.
*)
Admitted.

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
    
