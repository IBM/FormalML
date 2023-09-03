Require Import Lia List.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix ring.
From mathcomp Require Import ssralg ssrfun ssrint seq.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv zmodp eqtype ssrbool.
From mathcomp Require Import intdiv.

Import ssralg.GRing.
Require Import encode.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope ring_scope.

Lemma nat_of_ordK {p: nat} : cancel (@nat_of_ord (S (S p))) (natmul 1).
Proof.
  move=> x.
  by rewrite Zp_nat valZpK.
Qed.

Lemma int_of_ordK {p: nat} : cancel (fun x:'Z_p => Posz (nat_of_ord x)) (intmul 1).
Proof.
  move=> x.
  by rewrite -pmulrn nat_of_ordK.
Qed.

Section balance.

  Import ssrnum.Num.Syntax.
  
  (* range (-p/2, p/2] *)
  Definition balanced_mod {p:nat} (x : 'Z_p):int :=
    if (x <= p./2)%N then x%:Z else x%:Z-p%:Z.

  (* range [-p/2, p/2) *)
  Definition balanced_mod_lo {p:nat} (x : 'Z_p):int :=
    let xz := x %:Z in
    let xzm := xz - p%:Z in
    if -(p./2)%:Z <= xzm then xzm else xz.
  

  Lemma absz_bound (x : int) (b : nat) :
    - (b%:Z) <= x /\ x <= b%:Z <->
    (absz x <= b)%N.
  Proof.
    unfold absz.
    split; intros.
    - destruct H.
      case_eq x; intros; lia.
    - case_eq x; intros; rewrite H0 in H; lia.
  Qed.

  Lemma absz_bound_lt (x : int) (b : nat) :
    - (b%:Z) < x /\ x < b%:Z <->
    (absz x < b)%N.
  Proof.
    unfold absz.
    split; intros.
    - destruct H.
      case_eq x; intros; lia.
    - case_eq x; intros; rewrite H0 in H; lia.
  Qed.

  Context {p : nat} {pbig:(1 < p)%nat}.
  
  Lemma Zp_intmul_Np  (x : 'Z_p) :
    x = (x%:Z - p%:Z)%:~R.
  Proof.
    generalize (intmul1_is_rmorphism (Zp_ringType (Zp_trunc p))); intros.
    destruct H.
    by rewrite base int_of_ordK -pmulrn char_Zp // oppr0 addr0.
  Qed.

  Import order.Order.TotalTheory.
  Import ssrnum.Num.Theory. 
  
  Lemma balanced_mod_cong (x : 'Z_p) :
    x = (balanced_mod x)%:~R.
  Proof.
    unfold balanced_mod.
    case: (x <= p./2)%N.
    - by rewrite int_of_ordK.
    - by rewrite {1}(Zp_intmul_Np x).
  Qed.

  Lemma balanced_mod_lo_cong (x : 'Z_p) :
    x = (balanced_mod_lo x)%:~R.
  Proof.
    unfold balanced_mod_lo.
    case: leP => _.
    - by rewrite {1}(Zp_intmul_Np x).
    - by rewrite int_of_ordK.
  Qed.

  Lemma Zp_lt_p (x : 'Z_p):
    x%:Z < p.
  Proof.
    generalize (ltn_ord x); intros.
    by rewrite {2}Zp_cast in H.
  Qed.

  Lemma Zp_lt_p_N (x : 'Z_p):
    (x < p)%N.
  Proof.
    generalize (ltn_ord x); intros.
    by rewrite {2}Zp_cast in H.
  Qed.

  Lemma balanced_mod_range1 (x : 'Z_p):
    balanced_mod x <= p./2.
  Proof.
    unfold balanced_mod.
    generalize (Zp_lt_p_N x).
    intros.
    case leqP; lia.
  Qed.

  Lemma balanced_mod_lo_range1 (x : 'Z_p):
    balanced_mod_lo x <= p.-1./2.
  Proof.
    unfold balanced_mod_lo.
    generalize (Zp_lt_p x).
    case: (boolP (- (p./2)%:Z <= _)) => le1; lia.
  Qed.

  Lemma balanced_mod_range2 (x : 'Z_p):
    -((p.-1./2)%:Z) <= balanced_mod x.
  Proof.
    unfold balanced_mod.
    case: leqP => HH; try lia.
  Qed.

  Lemma balanced_mod_lo_range2 (x : 'Z_p):
    -((p./2)%:Z) <= balanced_mod_lo x.
  Proof.
    unfold balanced_mod_lo.
    case: (boolP (_ <= Posz x - p%:Z)) => le1; lia.
  Qed.

  Lemma balanced_mod_abs_range (x : 'Z_p):
    (absz (balanced_mod x) <= p./2)%N.
  Proof.
    apply absz_bound.
    split.
    - generalize (balanced_mod_range2 x); lia.
    - apply balanced_mod_range1.
  Qed.

  Lemma balanced_mod_lo_abs_range (x : 'Z_p):
    (absz (balanced_mod_lo x) <= p./2)%N.
  Proof.
    apply absz_bound.
    split.
    - apply balanced_mod_lo_range2.
    - generalize (balanced_mod_lo_range1 x); lia.
  Qed.

  Lemma balanced_mod_unique (c1 c2 : int) :
    c1 <= p./2 ->
    c2 <= p./2 ->
    -((p.-1./2)%:Z) <= c1 ->
    -((p.-1./2)%:Z) <= c2 ->
    ((c1 - c2) %% p)%Z = 0 ->
    c1 = c2.
   Proof.
     intros.
     case (leP (0%Z) (c1 - c2)%Z) => le0.
     - assert (le0_lep:0%Z <= c1 - c2 < p%:Z).
       {
         apply /andP; lia.
       }
       generalize (modz_small le0_lep); lia.
     - assert (le0_lep:0%Z <= c2 - c1 < p%:Z).
       {
         apply /andP; lia.
       }
       assert (((c2 - c1) %% p)%Z = 0).
       {
         replace (c2 - c1)%Z with (-1 *  (c1 - c2))%Z by lia.
         by rewrite -modzMmr H3 mulr0 mod0z.
       }
       generalize (modz_small le0_lep); lia.
  Qed.

End balance.

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
  
  Definition rounded_div (num : int) (den : nat) :=
    let denz := den %:Z in
    let q := (num %/ denz)%Z in
    let rem := num - q * denz in
    if absz rem <= den./2 then q else q+1.

  Lemma add_opp [R : comRingType] (x : R) :
    (-x) + x = 0.
  Proof.
    ring.
  Qed.

  Lemma rounded_div_rem_small (num : int) (den : nat) :
   (0 < den)%N ->
    absz (num - (rounded_div num den) * (den%:Z))%Z <= den ./2.
  Proof.
    intros.
    apply absz_bound.
    unfold rounded_div.
    case: (boolP ((`|(num - (num %/ den)%Z * den)%R|) <= _)) => HH.    
    - apply absz_bound in HH.
      destruct HH.
      split; lia.
    - split; try lia.
   Qed.

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
  
  Definition pq_embed (c : 'Z_q) : 'Z_(p*q) := (balanced_mod c)%:~R.

  Definition secret_p := map_poly pq_embed secret_poly.

  Variable (relin_err relin_a : {poly 'Z_(p*q)}).
  Hypothesis (relin_err__small : coef_norm relin_err <= ρ).

  Definition rescale (q1 q2 : nat) (c : 'Z_(q1*q2)) : 'Z_q2 :=
    (rounded_div (balanced_mod c) q1)%:~R.

  Definition rescale_gen (q1 q2 : nat) (c : 'Z_q1) : 'Z_q2 :=
    (rounded_div ((balanced_mod c) * q2) q1)%:~R.

  Definition scale_up (q1 q2 : nat) (c : 'Z_q1) : 'Z_(q1*q2) :=
    inZp (muln q2 c).

  Lemma scale_up_additive (q1 q2 : nat):
    additive (scale_up (Zp_trunc q1).+2 (Zp_trunc q2).+2).
  Proof.
    intros x y.
    rewrite /scale_up /add /opp /= /inZp.
    apply ord_inj => /=.
    set q1' := (Zp_trunc q1).+2.
    set q2' := (Zp_trunc q2).+2.
    rewrite {2 4}(@Zp_cast (q1' * q2')) //.
    rewrite !div.modnDmr !div.modnDml.
    rewrite div.muln_modr.
    unfold q1', q2'.
    replace ((Zp_trunc ((Zp_trunc q1).+2 * (Zp_trunc q2).+2)).+2 ) with
      ((Zp_trunc q2).+2 * (Zp_trunc q1).+2)%N at 1 by (unfold Zp_trunc; lia).
    rewrite div.modn_mod.
    f_equal; try lia.
    rewrite div.modn_small.
    - rewrite mulnDr mulnBr.
      f_equal.
      f_equal.
      rewrite mulnC.
      unfold Zp_trunc.
      lia.
    - rewrite mulnC.
      have: (ltn y (Zp_trunc q1).+2).
      + apply ltn_ord.
      + assert (0 < (Zp_trunc q2).+2).
        {
          unfold Zp_trunc; lia.
        }
        by rewrite ltn_mul2r.
  Qed.

  Definition rescale1 (q1 q2 : nat) (c : 'Z_(q1*q2)) : 'Z_q2 := inZp c.

  Lemma rescale1_is_rmorphism (q1 q2 : nat) :
    rmorphism (rescale1 (Zp_trunc q1).+2 (Zp_trunc q2).+2).
  Proof.
    unfold rescale1.
    generalize (intmul1_is_rmorphism (Zp_ringType (Zp_trunc q2))); intros.
    destruct H as [? [? ?]].
    constructor.
    - intros x y.
      rewrite /add/opp/=/Zp_add /= /inZp.
      apply ord_inj => /=.
      set q1' := (Zp_trunc q1).+2.
      set q2' := (Zp_trunc q2).+2.
      rewrite {2 4}(@Zp_cast (q1' * q2')) //.
      rewrite !div.modnDmr !div.modnDml div.modn_dvdm.
      + suff: Posz (div.modn (x + (q1' * q2' - y)) q2') = Posz (div.modn (x + (q2' - div.modn y q2')) q2')
          by inversion 1.
        rewrite -!modz_nat !PoszD -!ssrint.subzn.
        * rewrite -modzDmr -(modzDml (muln q1' q2')).
          rewrite PoszM modzMl add0r modzDmr -!modz_nat.
          rewrite -(modzDmr x (Posz q2' - _)).
          rewrite -(modzDml q2' _).
          rewrite modzz add0r modzNm.
          by rewrite modzDmr.
        * apply ltnW.
          by apply div.ltn_pmod.
        * apply ltnW.
          apply ltn_ord.
      + by rewrite div.dvdn_mull.
    - constructor.
      + intros x y.
        rewrite -!Zp_nat !pmulrn.
        rewrite -m -!pmulrn !Zp_nat /inZp.
        apply ord_inj => //=.
        rewrite div.modn_dvdm //.
        rewrite {1}Zp_cast //.
        rewrite (@Zp_cast ((Zp_trunc q1).+2 * (Zp_trunc q2).+2)) //.
        by rewrite div.dvdn_mull //.
      + by rewrite /= div.modn_small //.
  Qed.

  Canonical rescale1_rmorphism (q1 q2: nat) := RMorphism (rescale1_is_rmorphism q1 q2).

  Lemma cdivqq_int (q1 q2 : nat) (c : int):
    (0 < q2)%N ->
    (c %/ q1)%Z = ((c * q2) %/ (q1 * q2)%N)%Z.
  Proof.
    intros.
    rewrite -(@divzMpr q2%:Z); [| lia].
    do 2 f_equal.
  Qed.
  
  Lemma lt_muln_iff (n1 n2 n3 : nat) :
    (n1 < n2)%N <-> (n1 * (S n3) < n2 * (S n3))%N.
  Proof.
    induction n3; lia.
  Qed.

  Lemma le_half_odd (n1 n2 : nat) :
    odd n2 ->
    (n1 <= n2./2)%N <-> (n1.*2.+1 <= n2)%N.
  Proof.
    lia.
  Qed.

  Lemma le_half_mul_odd (n1 n2 n3 : nat) :
    odd n2 ->
    odd n3 ->
    (n1 <= n2./2)%N <-> (n1 * n3 <= (n2 * n3)./2)%N.
  Proof.
    intros.
    rewrite le_half_odd // le_half_odd; try lia.
    replace ((n1 * n3).*2) with ((n1.*2)*n3)%N by lia.
    replace n3 with (n3.-1.+1) by lia.
    apply lt_muln_iff.
  Qed.

  Lemma rounded_div_scale_div (q1 q2 : nat) (c : int):
    odd q1 ->
    odd q2 ->
    rounded_div c q1 = rounded_div (c * q2) (q1 * q2).
  Proof.
    intros.
    assert (0 < q2)%N by lia.
    rewrite /rounded_div -!cdivqq_int //.
    have: ((c * q2 - (c %/ q1)%Z * (q1 * q2)%N)%R =
             (c - (c %/ q1)%Z * q1)%R * q2) by lia.
    move ->.
    rewrite abszM absz_nat.
    generalize (le_half_mul_odd `|(c - (c %/ q1)%Z * q1)%R| q1 q2 H H0); intros.
    case: leP; case: leP; lia.
  Qed.

  Lemma rescale_gen_prop (q1 q2 : nat) (c : 'Z_(q1*q2)):
    odd q1 ->
    odd q2 ->
    rescale q1 q2 c = rescale_gen (q1 * q2) q2 c.
  Proof.
    intros.
    unfold rescale, rescale_gen, balanced_mod.
    by rewrite -rounded_div_scale_div.
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
    Pdiv.Ring.rdvdp (R := R) ('X^(2^n) + 1%:P) ('X^k ^+(2^n) + 1%:P).
  Proof.
    move=> oddk.
    case: (@eqVneq _ n 0%nat).
    - move=> ->.
      rewrite expn0 !expr1.
      by apply lin_div_odd_power.
    - move=> nn0.
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

  Require Import Reals nth_root encode.
  From mathcomp Require Import Rstruct complex.

  Lemma poly_shift_eval [S : comRingType] (p : {poly S}) (k : nat) (v : S) :
    p.[v^+k] = (poly_shift k p).[v].
  Proof.
    unfold poly_shift.
    by rewrite horner_comp hornerXn.
  Qed.

  Lemma poly_shift_C (p : {poly R}) (k : nat) :
    poly_shift k (map_poly RtoC p) = map_poly RtoC (poly_shift k p).
  Proof.
    by rewrite /poly_shift map_comp_poly map_polyXn.
  Qed.

  Lemma poly_shift_eval_C (p : {poly R}) (k:nat) (v : R[i]) :
    (map_poly RtoC p).[v^+k] = (map_poly RtoC (poly_shift k p)).[v].
  Proof.
    by rewrite poly_shift_eval poly_shift_C.
  Qed.
    
  Lemma conj_poly_eval_pow (p : {poly R}) (i j :nat) :
    let v := nth_root i (S j) in
    conjc ((map_poly RtoC p).[v]) = (map_poly RtoC (poly_shift j p)).[v].
  Proof.
    simpl.
    rewrite -poly_shift_eval_C.
    rewrite rpoly_eval_conj.
    f_equal.
    by rewrite -conj_pow_nth_root.
  Qed.
    
  From mathcomp Require Import ssrnat.
   Lemma poly_odd_pow_prim_roots_perm_eq (j n : nat) (p : {poly R[i]}):
     let l := mkseq (fun i => nth_root (2 * i + 1) (2 ^ (S n))) (2^n) in
     perm_eq (map (fun x => p.[x]) l)
       (map (fun x => (poly_shift (2*j+1) p).[x]) l).
   Proof.
     pose (l := mkseq (fun i => nth_root (2 * i + 1) (2 ^ (S n))) (2^n)).
     assert (map (fun x => (poly_shift (2*j+1) p).[x]) l =
               map (fun x => p.[x]) (map (fun x => x^+(2*j+1)) l)).
     {
       generalize (poly_shift_eval p (2*j+1)); intros.
       admit.
     }
     rewrite /= H /l /=.
     apply perm_map.
     apply odd_pow_prim_roots_perm_eq.
  Admitted.     






      
      
