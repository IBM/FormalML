Require Import Lia List.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix ring.
From mathcomp Require Import ssralg ssrfun ssrint.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv zmodp eqtype ssrbool.
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
  Definition poly_shift [R:ringType] (k : nat) (p : {poly R}) : {poly R}
    := comp_poly 'X^k p.

  Definition poly_shift_alt [R:ringType] (k : nat) (p : {poly R}) : {poly R}
      := \poly_(i < (k * (seq.size p).-1).+1) (if div.dvdn k i then p`_(div.divn i k) else 0).

  Lemma poly_shift_altE [R:ringType] (k : nat) (p : {poly R}) :
    poly_shift k.+1 p = poly_shift_alt k.+1 p.
  Proof.
    case: (@eqP _ (seq.size p) 0%nat).
    - move/seq.size0nil.
      rewrite -polyseq0 => /poly_inj->.
      rewrite /poly_shift /poly_shift_alt comp_poly0.
      apply polyP => i.
      rewrite coef_poly !coef0.
      case: ltP => //.
      by case: div.dvdnP => //.
    - move=> pn0.
      apply polyP => i.
      rewrite /poly_shift /poly_shift_alt.
      rewrite !coef_comp_poly_Xn //= coef_poly /=.
      case: div.dvdnP.
      + move=>[m ->].
        rewrite div.mulnK //.
        case: ltP => // nlt.
        rewrite seq.nth_default //.
        move /ltP: nlt.
        rewrite mulnC ltnS leq_pmul2l //.
        rewrite leqNgt Bool.negb_involutive.
        by case: (seq.size p) pn0.
      + by case: ltP.
  Qed.

  Lemma poly_shift_altE' [R:ringType] (k : nat) (p : {poly R}) : k != 0%nat ->
    poly_shift k p = poly_shift_alt k p.
  Proof.
    destruct k => // _.
    apply poly_shift_altE.
  Qed.

  Lemma poly_shift_1 [R:ringType] (k : nat):
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
  
  Lemma poly_shift_injective [R:ringType] (k:nat) : injective (poly_shift (R:=R) (S k)).
  Proof.
    move=> a b eqq.
    apply polyP => i.
    apply (f_equal (coefp (k.+1 * i))) in eqq.
    move: eqq.
    rewrite /poly_shift /=.
    rewrite !coef_comp_poly_Xn //=.
    rewrite !div.dvdn_mulr //.
    by rewrite !div.mulKn //.
  Qed.    

  Lemma poly_shift1_id [R:ringType] (p : {poly R}):
    @poly_shift R 1 p = p.
  Proof.
    apply polyP => i.
    rewrite /poly_shift /=.
    rewrite !coef_comp_poly_Xn //=.
    by rewrite div.dvd1n div.divn1.
  Qed.    

  Lemma size_poly_shift [R:ringType] (k:nat) (p : {poly R}) (pn0:p!=0) :
    seq.size (poly_shift (k.+1) p) = (k.+1 * (seq.size p).-1).+1%nat.
  Proof.
    rewrite poly_shift_altE.
    rewrite size_poly_eq //=.
    rewrite div.dvdn_mulr ?div.dvdnn //.
    rewrite div.mulKn //.
    by rewrite -lead_coefE lead_coef_eq0.
  Qed.

  Lemma size_poly_shift' [R:ringType] (k:nat) (p : {poly R}) (pn0:p!=0) :
    k != 0%nat ->
    seq.size (poly_shift k p) = (k * (seq.size p).-1).+1%nat.
  Proof.
    elim: k => //.
    move=> k _ _.
    by apply size_poly_shift.
  Qed.

  Definition poly_unshift [R:ringType] (k : nat) (p : {poly R}) :=
    \poly_(i < (div.divn (seq.size p).-1 k).+1) (p`_(k*i)).

  Lemma poly_shiftK [R:comRingType] (k: nat) : cancel (@poly_shift R (S k)) (@poly_unshift R (S k)).
  Proof.
    move=> p.
    case: (@eqP _ p 0).
    - move=> -> /=.
      rewrite /poly_shift comp_poly0 /poly_unshift.
      apply polyP=> i.
      rewrite coef_poly !polyseq0 /= !seq.nth_nil.
      by case: ltP.
    - rewrite /poly_unshift => /eqP-pn0.
      rewrite size_poly_shift //.
      rewrite poly_shift_altE /poly_shift_alt.
      apply polyP=> i.
      rewrite coef_poly => /=.
      rewrite div.mulKn //.
      rewrite -polySpred //.
      case: ltP.
      + move=> ilt.
        rewrite coef_poly div.mulKn //.
        rewrite div.dvdn_mulr ?div.dvdnn //.
        rewrite ltnS leq_pmul2l //.
        rewrite polySpred // in ilt.
        rewrite -ltnS.
        by move/ltP: ilt => ->.
      + move=> inlt.
        rewrite seq.nth_default //.
        rewrite leqNgt.
        by apply/ltP.
  Qed.


  Lemma comp_poly_exp_polyX [R:ringType] j k :
    (polyX R) ^+ (j * k) = comp_poly ('X^ j) ('X^ k).
  Proof.
    by rewrite comp_Xn_poly /= -exprM.
  Qed.  
  
  Lemma poly_shiftM [R:comRingType] (j k: nat) (p: {poly R}) :
    poly_shift (j * k) p = poly_shift j (poly_shift k p).
  Proof.
    by rewrite /poly_shift -comp_polyA comp_poly_exp_polyX.
  Qed.
  
  Lemma lin_div_odd_power [R:ringType] k :
    odd k ->
    Pdiv.Ring.rdvdp (R := R) ('X + 1%:P) ('X^k + 1%:P).
  Proof.
    rewrite -{1}(opprK 1%:P).
    replace (- polyC (R:=R) 1) with (polyC (R:=R) (-1)).
    - intros.
      rewrite Pdiv.Ring.rdvdp_XsubCl /root hornerD hornerXn hornerC.
      by rewrite -signr_odd H /= expr1 addrC addrN.
    - by rewrite polyCN polyC1.
  Qed.

  (*
  Lemma comp_poly_monic [R:comRingType] (p q : {poly R}) :
    p \is monic ->
    q \is monic ->
    q \Po p \is monic.
  Proof.
    rewrite !monicE !lead_coefE coef_comp_poly.
  Admitted.
   *)
  
  Lemma rdvdp_comp_poly_monic [R:comRingType] (r p q : {poly R}) :
    p \is monic ->
    p \Po r \is monic -> 
    Pdiv.Ring.rdvdp p q ->
    Pdiv.Ring.rdvdp (p \Po r) (q \Po r).
  Proof.
    move=> monp monpr.
    have [-> | pn0] := eqVneq p 0.
    - by rewrite comp_poly0 !Pdiv.Ring.rdvd0p; move/eqP->; rewrite comp_poly0.
    - rewrite Pdiv.ComRing.rdvdp_eq.
      rewrite (monicP monp) expr1n /= scale1r.
      set s := Pdiv.Ring.rdivp (R:=R) _ _; move/eqP=> Hq.
      apply: (@mathcomp.algebra.polydiv.Pdiv.RingMonic.eq_rdvdp _ _ _ (s \Po r)).
      + trivial.
      + by rewrite -comp_polyM -{}Hq.
  Qed.
  
  Lemma pow2_div_odd_power [R:comRingType] k n :
    odd k ->
    n != 0%nat ->
    Pdiv.Ring.rdvdp (R := R) ('X^(2^n) + 1%:P) ('X^k ^+(2^n) + 1%:P).
  Proof.
    move=> oddk nn0.
    move: (rdvdp_comp_poly_monic (R:=R) ('X^(2 ^ n)) ('X + 1%:P) ('X^k + 1%:P)).
    rewrite lin_div_odd_power //.
    rewrite (Xn_add_c_monic 0).
    rewrite !comp_polyD !comp_polyX !comp_polyC.
    have-> : 'X^(2 ^ n) + 1%:P \is @monic R.
    {
      case: (@eqP _ (expn 2 n) 0%nat) =>eqq.
      - lia.
      - destruct (expn 2 n); [lia |].
        apply Xn_add_c_monic.
    }
    rewrite comp_Xn_poly -!exprM.
    rewrite [muln (2^n) k]mulnC.
    by apply.
  Qed.
  
End rotation.  
      
      
