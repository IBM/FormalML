Require Import Lia List.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix ring.
From mathcomp Require Import ssralg ssrfun ssrint.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv ssrint zmodp eqtype ssrbool.
Import ssralg.GRing.
Require Import encode.

Set Bullet Behavior "Strict Subproofs".

Require Import LibUtilsListAdd.

Lemma Forall2_nth_error_iff {A B} (P:A->B->Prop) (l1 : list A) (l2: list B) :
  (forall (i : nat), match nth_error l1 i, nth_error l2 i with
             | Some a, Some b => P a b
              | None, None => Logic.True
              | _, _ => Logic.False
              end
  ) <->
  Forall2 P l1 l2.
Proof.
  split.
  - revert l2; induction l1; destruct l2; simpl in *; trivial; intros HH.
    + specialize (HH 0); simpl in HH; contradiction.
    + specialize (HH 0); simpl in HH; contradiction.
    + constructor.
      * now specialize (HH 0); simpl in HH.
      * apply IHl1; intros i.
        now specialize (HH (S i)).
  - induction 1; intros [| i]; simpl; trivial.
    apply IHForall2.
Qed.

Lemma nth_error_eqs {A} (l1 l2 : list A) :
  (forall (i : nat), nth_error l1 i = nth_error l2 i) ->
  l1 = l2.
Proof.
  intros HH.
  apply Forall2_eq.
  apply Forall2_nth_error_iff; intros i.
  rewrite HH.
  now destruct (nth_error l2 i).
Qed.

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
  
  Definition ired_q {qq:nat} (i : int) : 'Z_qq := intmul Zp1 i.

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

Section rotation.
  
  (* show  p x -> p (x^k) is a morphism *)
  Definition poly_shift [R:comRingType] (k : nat) (p : {poly R}) :=
    comp_poly 'X^k p.

  Lemma poly_shift_1 [R:comRingType] (k : nat):
    @poly_shift R k 1 = 1.
  Proof.
    by rewrite /poly_shift comp_polyC.
  Qed.

  Lemma poly_shift_is_rmorphism [R:comRingType] (k : nat) :
    rmorphism (poly_shift (R := R) k).
  Proof.
    unfold poly_shift.
    constructor.
    - intros ??.
      by rewrite comp_polyB.
    - split.
      + intros ??.
        by rewrite comp_poly_multiplicative.
      + by rewrite comp_polyC polyC1.
  Qed.

  Lemma coefp_eq_poly [R:ringType] (a b : {poly R}) :
    (forall i, a`_i = b`_i) -> a = b.
  Proof.
    intros.
    by apply polyP => i.
  Qed.
  
  Lemma poly_shift_injective [R:comRingType] (k:nat) : injective (poly_shift (R:=R) (S k)).
  Proof.
    move=> a b eqq.
    apply coefp_eq_poly => i.
    apply (f_equal (coefp (k.+1 * i))) in eqq.
    move: eqq.
    rewrite /poly_shift /=.
    rewrite !coef_comp_poly_Xn //=.
    rewrite !div.dvdn_mulr //.
    by rewrite !div.mulKn //.
  Qed.    

End rotation.  
      
      
