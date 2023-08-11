Require Import Lia List.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix ring.
From mathcomp Require Import ssralg ssrfun ssrint.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv ssrint zmodp eqtype ssrbool.
Import ssralg.GRing.
Require Import encode.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope ring_scope.

Section encrypted_ops.

  Variable (q:nat).
  Hypothesis (qodd : (odd q)).
  
  Variable (err_poly secret_poly a_poly : {poly 'Z_q}).
  Variable (ρ : nat). (* bound for errs *)

  (* err_poly is small, a_poly is random over 'Z_q *)

  Definition public_key := (-a_poly * secret_poly + err_poly, a_poly).

  Definition encrypt (m : {poly 'Z_q}) : ({poly 'Z_q} * {poly 'Z_q}) :=
    (m + fst public_key, snd public_key).

  Definition encrypt_z (m : {poly int}) := encrypt (red_poly m q).

  Definition balanced_mod {qq:nat} (x : 'Z_qq) :=
    let xz := x %:Z in
    let qz := q %:Z in
    if intOrdered.lez xz (qz/2) then xz else qz-xz.

  Definition rounded_div (num : int) (den : nat) :=
    let denz := den %:Z in
    let q := num/denz in
    let rem := num - q * denz in
    if absz rem < (Nat.div den 2) then q else q+1.

  Definition coef_norm {qq:nat} (p : {poly 'Z_qq}) :=
    list_max (map absz (map balanced_mod p)).

  Hypothesis (err_poly_small : coef_norm err_poly <= ρ).

  Definition decrypt mpair := (fst mpair) + (snd mpair) * secret_poly.

  Lemma encrypt_decrypt (m : {poly 'Z_q}) :
    decrypt (encrypt m) = m + err_poly.
  Proof.
    unfold decrypt, encrypt, public_key, fst, snd.
    ring.
  Qed.
  
(*
  (* following already defined in ssralg *)
  Definition add_pair (p1 p2 : ({poly 'Z_q} * {poly 'Z_q})) :=
    (fst p1 + fst p2, snd p1 + snd p2).
*)

  Definition scale_pair (m : {poly 'Z_q}) (p : ({poly 'Z_q} * {poly 'Z_q})) :=
    (m * fst p, m * snd p).

  Definition mul_pair (p1 p2 : ({poly 'Z_q} * {poly 'Z_q})) :=
    (fst p1 * fst p2, (fst p1 * snd p2 + snd p1 * fst p2, snd p1 * snd p2)).

  Lemma CKKS_add (m1 m2 : {poly 'Z_q}) :
    decrypt (add_pair (encrypt m1) (encrypt m2)) =
      decrypt (encrypt m1) + decrypt(encrypt m2).
  Proof.
    rewrite !encrypt_decrypt.
    unfold add_pair, decrypt, encrypt, public_key, fst, snd.
    ring.
  Qed.

  Lemma CKKS_scale (m1 m2 : {poly 'Z_q}) :
    decrypt (scale_pair m1 (encrypt m2)) = 
      m1 * decrypt(encrypt m2).
  Proof.
    unfold scale_pair, encrypt, decrypt, public_key, fst, snd.
    ring.
  Qed.

  Definition decrypt_mul trip := fst trip + secret_poly * decrypt (snd trip).

  Lemma CKKS_mul_trip (m1 m2 : {poly 'Z_q}) :
    decrypt_mul (mul_pair (encrypt m1) (encrypt m2)) =
      decrypt (encrypt m1) * decrypt (encrypt m2).
  Proof.
    unfold mul_pair, encrypt, decrypt_mul, decrypt, public_key, fst, snd.
    ring.
  Qed.
    
  Variable (p:nat). (* relin_modulus *)
  Hypothesis pbig : p > q.
  
  Definition ired_q {qq:nat} (i : int) : 'Z_qq :=
    intmul Zp1 i.

  Definition pq_embed (c : 'Z_q) : 'Z_(p*q) := ired_q (balanced_mod c).

  Definition secret_p := map_poly pq_embed secret_poly.

  Variable (relin_err relin_a : {poly 'Z_(p*q)}).
  Hypothesis (relin_err__small : coef_norm relin_err <= ρ).

  Definition rescale (q1 q2 : nat) (c : 'Z_(q1*q2)) : 'Z_q2 :=
    ired_q (rounded_div (balanced_mod c) q1).

  Definition rescale_gen (q1 q2 : nat) (c : 'Z_q1) : 'Z_q2 :=
    ired_q (rounded_div (balanced_mod c) (Nat.div q1 q2)).

  Lemma rescale_gen_prop (q1 q2 : nat) (c : 'Z_(q1*q2)):
    q2 <> 0%N ->
    rescale q1 q2 c = rescale_gen (q1 * q2) q2 c.
  Proof.
    intros.
    unfold rescale, rescale_gen.
    do 2 f_equal.
    now rewrite PeanoNat.Nat.div_mul.
  Qed.
    
  Definition red_p_q (c : 'Z_(p*q)) : 'Z_q := rescale p q c.

  Definition relin_V2_aux (c2 : {poly 'Z_q}) :=
    let b := - relin_a * secret_p + (secret_p ^+ 2)*+p + relin_err in
    let cp := map_poly pq_embed c2 in
    (map_poly red_p_q (cp * b), map_poly red_p_q (cp * relin_a)).

  Definition relin_V2 trip :=
    add_pair (fst trip, fst (snd trip))
             (relin_V2_aux (snd (snd trip))).
             
  Definition CKKS_mul (p1 p2 : ({poly 'Z_q} * {poly 'Z_q})) : 
    ({poly 'Z_q} * {poly 'Z_q}) :=
    relin_V2 (mul_pair p1 p2).
  
End encrypted_ops.
