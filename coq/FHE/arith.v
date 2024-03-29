Require Import Reals Lra Lia List Permutation.
From mathcomp Require Import common ssreflect fintype bigop ssrnat matrix Rstruct complex seq fingroup.
From mathcomp Require Import ssralg ssrfun.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import poly mxpoly polydiv ssrint zmodp eqtype ssrbool div order.
From mathcomp Require Import ring ssrZ.

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

Definition zliftc {q : nat} (c : 'Z_q) : int :=
  if (c <= q/2) then c%:Z else c%:Z - q%:Z.

Lemma modp_small (q : nat) (m : nat) :
  m < (Zp_trunc q).+2 ->
  nat_of_ord (intmul (1 : 'Z_q) (Posz m)) = m.
Proof.
  rewrite /intmul Zp_nat /=.
  by apply/modn_small.
Qed.

Lemma modpp (q : nat) :
  nat_of_ord (intmul (1 : 'Z_q) (Posz (Zp_trunc q).+2)) = 0%nat.
Proof.
  by rewrite /intmul Zp_nat /= modnn.
Qed.

Lemma modpp' (q : nat) :
  1 < q ->
  intmul (1 : 'Z_q) (Posz q) = 0.
Proof.
  intros.
  apply ord_inj. 
  by rewrite /intmul Zp_nat /= Zp_cast // modnn.
Qed.
  
Lemma zliftc_valid {q : nat} (c : 'Z_q) :
  1 < q ->
  c = (zliftc c) %:~R.
Proof.
  intros.
  rewrite /zliftc.
  case: (c <= q/2).
  - destruct c.
    apply ord_inj => /=.
    by rewrite modp_small.
  - destruct c.
    rewrite intrD mulrNz modpp' // oppr0 addr0.
    apply ord_inj => /=.
    by rewrite modp_small.
Qed.

Lemma zliftc_add2 {q : nat} (a b : 'Z_q) :
  1 < q ->
  let ab := a + b in 
  let sum := zliftc a + zliftc b in
  `|zliftc ab - sum | <= q.
Proof.
  have diveq: (Nat.divmod q 1 0 1).1 = (q / 2)%nat by [].

  move=> qbig.
  rewrite /zliftc /=.
  Ltac t1 C :=
    match goal with
    | [|- is_true (leq (absz ?x) _) ] =>
        have ->: x = C by lia
    end.

  Ltac t2 C := t1 C
    ; case: (boolP (((Zp_trunc q).+1 < _ + _))) => // _
                                                  ; (rewrite ?mul0n ?mul1n ?Zp_cast // ?distnn); lia.

  case: (boolP ( (a + b) %% (Zp_trunc q).+2 <= (Nat.divmod q 1 0 1).1)) => ltab
   ; case: (boolP (a <= (Nat.divmod q 1 0 1).1)) => lta
   ; case: (boolP (b <= (Nat.divmod q 1 0 1).1)) => ltb
                                                  ; rewrite modnD // [modn a _]modn_small ?[modn b _]modn_small; try apply ltn_ord.
  - t2 (opp (Posz (muln (leq (S (S (Zp_trunc q))) (addn a b)) (S (S (Zp_trunc q)))))).
  - t2 (add (V:=int_ZmodType) q (opp (Posz (muln (leq (S (S (Zp_trunc q))) (addn a b)) (S (S (Zp_trunc q))))))).
  - t2 (add (V:=int_ZmodType) (Posz q) (opp (Posz (muln (leq (S (S (Zp_trunc q))) (addn a b)) (S (S (Zp_trunc q))))))).
  - have eqq: ((Zp_trunc q).+1 < a + b).
    { move: (Nat.divmod_spec q 1 0 1) lta ltb.
      case: (Nat.divmod q 1 0 1) => /= x u.
      move/(_ (le_n _)) => [eqq1 eqq2] lta ltb.
      rewrite !Nat.add_0_r in eqq1.
      rewrite {1}Zp_cast //.
      destruct u; simpl in *; lia.
    }
    rewrite eqq mul1n.
    rewrite {1}Zp_cast // in eqq.
    rewrite {3}Zp_cast //.
    by t1 (Posz q).
  - case: (boolP ((Zp_trunc q).+1 < a + b)).
    + rewrite mul1n {1}Zp_cast // => ineq2.
      simpl in lta.
      rewrite diveq in lta ltb ltab.
      case: (eqVneq q (nat_of_ord a + nat_of_ord b))%nat =>eqq2.
      * case/negP: ltab.
        by rewrite {3}Zp_cast // {3}eqq2 modnn.
      * suff: 2 * (q / 2)%nat <= q by lia.
        apply/leP.
        apply Nat.Div0.mul_div_le.
    + rewrite mul0n => _.
      t1 (opp (Posz q)).
      by rewrite abszN.
  - t2 (opp (Posz (muln (leq (S (S (Zp_trunc q))) (addn a b)) (S (S (Zp_trunc q)))))).
  - t2 (opp (Posz (muln (leq (S (S (Zp_trunc q))) (addn a b)) (S (S (Zp_trunc q)))))).
  - have eqq: ((Zp_trunc q).+1 < a + b).
    { move: (Nat.divmod_spec q 1 0 1) lta ltb.
      case: (Nat.divmod q 1 0 1) => /= x u.
      move/(_ (le_n _)) => [eqq1 eqq2] lta ltb.
      rewrite !Nat.add_0_r in eqq1.
      rewrite {1}Zp_cast //.
      destruct u; simpl in *; lia.
    }
    rewrite eqq mul1n.
    rewrite {1}Zp_cast // in eqq.
    rewrite {3}Zp_cast //; lia.
Qed.


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
  zlift (0 : {poly 'Z_q}) = 0.
Proof.
  rewrite /zlift /zliftc.
  apply map_poly0.
Qed.  

Definition upi (c:R) : int := ssrZ.int_of_Z (up c).

(* 0 <= rand < 1 *)
Definition ran_round (x rand : R) : int :=
  let hi := upi x in
  if (Order.lt (hi%:~R - x) rand)%R then hi else (hi - 1).

Definition nearest_round (x : R) : int := ran_round x (1/2)%R.

Definition nearest_round_int (n d : int) : int := nearest_round ((n %:~R)/(d %:~R))%R.

Definition coef_maxnorm (p : {poly int}):nat := \max_(j < seq.size p) `|p`_ j|.

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
  rewrite ssrnum.Num.Theory.ltr_pdivlMr //; try lra.
  by rewrite mul1r /natmul/= ssrnum.Num.Theory.gtrDl ssrnum.Num.Theory.ltr10.    
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

Lemma up_add2' (r1 r2 : R) :
  (up(r1 + r2) = Z.add (up r1) (up r2) \/ up(r1 + r2) = Z.sub (Z.add (up r1) (up r2)) 1)%Z.
Proof.
  destruct (archimed r1).
  destruct (archimed r2).
  destruct (archimed (r1 + r2)).  
  case: (boolP (Rleb ((IZR (up r1) + IZR (up r2)) - (r1 + r2)) 1)).
  - intros.
    left.
    move /RlebP in p.
    by rewrite (tech_up (r1 + r2) (up r1 + up r2)) // plus_IZR; coq_lra.
  - intros.
    right.
    move /RlebP in i.
    by rewrite (tech_up (r1 + r2) (up r1 + up r2 - 1)) // !plus_IZR opp_IZR; coq_lra.
Qed.

Lemma up_add2 (r1 r2 : R) :
  Z.abs_nat (Z.sub (up (r1 + r2)) (Z.add (up r1) (up r2))) <= 1.
Proof.
  destruct (up_add2' r1 r2); rewrite H; lia.
Qed.


Lemma int_of_Z_abs x : `|int_of_Z x| = Z.abs_nat x.
Proof.
  rewrite /int_of_Z /absz /Z.abs_nat.
  destruct x; trivial.
  lia.
Qed.  

Lemma upi_add2' (n1 n2 : R) :
  (upi (n1 + n2) = (upi n1 + upi n2))%R \/
    (upi (n1 + n2) = (upi n1 + upi n2) -1)%R.
Proof.
  rewrite /upi.
  destruct (up_add2' n1 n2).
  - left.
    by rewrite H raddfD /=.
  - right.
    rewrite H.
    rewrite -Z.add_opp_r !raddfD /=.
    lra.
Qed.

Lemma upi_add2 (n1 n2 : R) :
   `|upi (n1 + n2) - (upi n1 + upi n2)%R| <= 1.
Proof.
  rewrite /upi.
  rewrite (_:
            ssrZ.int_of_Z (up (n1 + n2)) - (ssrZ.int_of_Z (up n1) + ssrZ.int_of_Z (up n2))%R =
              ssrZ.int_of_Z (Z.sub (up (n1 + n2)) (Z.add (up n1) (up n2)))%Z).
  - rewrite int_of_Z_abs.
    apply up_add2.
  - rewrite -Z.add_opp_r !raddfD /= raddfN /= raddfD /=.
    lra.
Qed.

Lemma ran_round_add2 (n1 n2 cutoff : R) :
  ((0 : R) < cutoff)%O -> 
  (cutoff < (1 : R))%O -> 
  let sum := ran_round n1 cutoff + ran_round n2 cutoff  in
  `|ran_round (n1 + n2)%R cutoff - sum| <= 1.
Proof.
  move=> cutoff_big cutoff_small.
  rewrite /ran_round.
  case: Order.TotalTheory.ltP=>lt1 ; case: Order.TotalTheory.ltP => lt2 ; case: Order.TotalTheory.ltP => lt3
                                                                                                      ; try (destruct (upi_add2' n1 n2); rewrite H; try lia; rewrite H raddfD /= in lt1; lra).
Qed.

Lemma nearest_round_add2 (n1 n2 : R) :
  let sum := nearest_round n1 + nearest_round n2 in
  `|nearest_round (n1 + n2) - sum| <= 1.
Proof.
  rewrite /nearest_round.
  apply ran_round_add2; lra.
Qed.

Lemma nearest_round_int_add2 (n1 n2 d : int) :
  d <> 0 ->
  let sum := nearest_round_int n1 d + nearest_round_int n2 d in
  `|nearest_round_int (n1 + n2) d - sum| <= 1.
Proof.
  move=> dn0.
  rewrite /= /nearest_round_int.
  rewrite (_:((n1 + n2)%:~R / d%:~R)%R = ((n1%:~R / d%:~R) + (n2%:~R / d%:~R))%R).
  - apply nearest_round_add2.
  - ring.
Qed.

Lemma nearest_round_int_add2' (n1 n2 d : int) : 
  d <> 0 ->
  let sum := nearest_round_int n1 d + nearest_round_int n2 d in
  { n3 : int |
    nearest_round_int (n1 + n2) d = sum + n3 /\
      `|n3| <= 1}.
Proof.
  intros.
  exists (nearest_round_int (n1 + n2) d - sum).
  split; try lia.
  by apply nearest_round_int_add2.
Qed.

Definition div_round (a : {poly int}) (d : int) : {poly int} :=
  map_poly (fun c => nearest_round_int c d) a.

Lemma div_round0 (den : int) :
  div_round (0 : {poly int}) den = 0.
Proof.
  rewrite /div_round.
  apply map_poly0.
Qed.

Lemma nth_map_default:
  forall [T1 : Type] (x1 : T1) [T2 : Type] (x2 : T2) (f : T1 -> T2) [n : nat] [s : seq T1],
    f x1 = x2 ->
    nth x2 [seq f i | i <- s] n = f (nth x1 s n).
Proof.
  intros.
  case/orP: (leqVgt (size s) n) => ineq.
  - by rewrite !nth_default // size_map.
  - by rewrite (nth_map x1).
Qed.
                                              
Lemma div_round_mul_add (a b : {poly int}) (d : int) :
  d <> 0 ->
  div_round (a + d *: b) d = div_round a d + b.
Proof.
  intros.
  rewrite /div_round !map_polyE -polyP => i.
  rewrite coefD !coef_Poly.
  rewrite !(nth_map_default 0 0); try by rewrite nearest_round_int0.
  rewrite coefD /=.
  by rewrite -nearest_round_int_mul_add_r // coefZ.
Qed.  


Lemma div_round_add2 (a b : {poly int}) (d : int) :
  d <> 0 ->
  { c : {poly int} |
    div_round (a + b) d = div_round a d + div_round b d + c /\
      coef_maxnorm c <= 1}.
Proof.
  exists (div_round (a + b) d - (div_round a d + div_round b d)).
  split.
  - ring.
  - rewrite /coef_maxnorm /div_round.
    apply /bigmax_leqP => i _.
    rewrite !(coefD,coefN).
    rewrite !coef_map_id0; try by rewrite nearest_round_int0.
    rewrite !coefD.
    by apply nearest_round_int_add2.
Qed.

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
  ring.
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
    map_poly (fun P => q_reduce q (div_round ((zlift c2) * (zlift P)) (p%:Z)))
                               evkey.

Lemma linearize_prop  {q p : nat} (c2 : {poly 'Z_q}) (s e : {poly int}) (a : {poly 'Z_(p*q)}) :
  { e2 : {poly int} |
    (map_poly (fun P => q_reduce q (div_round ((zlift c2) * (zlift P)) (p%:Z)))
     (ev_key s e a)).[q_reduce q s] = 
      c2 * (q_reduce q (exp s 2)) + q_reduce q (div_round ((zlift c2) * e) p + e2) /\
  coef_maxnorm e2 <= 1}. 
Proof.
  eexists; split.
  - rewrite /ev_key /key_switch_key.
    rewrite map_Poly_id0.
    + rewrite horner_Poly /= mul0r add0r.
(*
      assert (div_round
       (zlift c2 *
        zlift
          (- a * q_reduce (p * q) s + q_reduce (p * q) e +
             q_reduce (p * q) (s ^+ 2 *+ p))) p =
*)                
      admit.
    + by rewrite [zlift 0]zlift0 // mulr0 div_round0 rmorph0.

(*
    + rewrite horner_Poly /= mul0r add0r mulrDr.
    assert (div_round_q
              (plift p c2 * (- a * q_reduce (p * q) s + q_reduce (p * q) e) +
                 plift p c2 * q_reduce (p * q) (s ^+ 2 *+ p)) p) =
             div_round_q (plift p c2 * (- a * q_reduce (p * q) s + q_reduce (p * q) e)) p
                         + plift p c2 * q_reduce (p * q) (s ^+ 2 *+ p)) p) =
  *)              
Admitted.

Definition rescale {q1 q2 : nat} (p : {poly 'Z_(q1 * q2)}) : {poly 'Z_q2} :=
  q_reduce q2 (div_round (zlift p) q1%:Z).

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
  {R : {poly int} |
     FHE_decrypt s (FHE_mult PP QQ (ev_key s e a)) = 
       P * Q + q_reduce q (div_round (zlift (PP * QQ)`_2 * e) p + R) /\
       coef_maxnorm R <= 1 }.
Proof.
(*
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
 *)
  Admitted.

Definition key_switch {q p : nat} (c0 c1 : {poly 'Z_q})
  (ks_key : {poly {poly 'Z_(p*q)}}) : {poly {poly 'Z_q}} :=
  c0%:P + map_poly (fun P => q_reduce q (div_round ((zlift c1) * (zlift P)) (p%:Z)))
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
    
