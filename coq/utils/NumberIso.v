Require Import BinNums BinNat Nat List.
Require Import Lia.

Require Import LibUtils Isomorphism PairEncoding.
Import ListNotations.

Require Import QArith Qcanon.

Global Program Instance positive_N_iso : Isomorphism positive N
  := {iso_f n := Pos.pred_N n ;
      iso_b n := N.succ_pos n
     }.
Next Obligation.
  apply N.pos_pred_succ.
Qed.
Next Obligation.
  destruct a; simpl; trivial.
  apply Pos.succ_pred_double.
Qed.



Global Program Instance Z_N_iso : Isomorphism Z N
  := { iso_f n := (if Z_ge_lt_dec n 0 then (Z.to_N n)*2 else (Z.to_N (- n))*2-1)%N ;
       iso_b n := if (n mod 2)%N then Z.of_N (n / 2)%N else (- (Z.of_N ((n+1) / 2)%N))%Z
     }.
Next Obligation.
  case_eq ((b mod 2)%N); [intros modeq | intros ? modeq].
  - generalize (N.div_mod b 2); intros HH.
    destruct ( Z_ge_lt_dec (Z.of_N (b / 2)) 0); lia.
  - assert (modeq2:(b mod 2 = 1)%N).
    { generalize (N.mod_upper_bound b 2); lia. }
    clear modeq.
    generalize (N.div_mod b 2); intros HH.
    rewrite modeq2 in HH.
    cut_to HH; [| lia].
    destruct (  Z_ge_lt_dec (- Z.of_N ((b + 1) / 2)) 0).
    + generalize (N2Z.is_nonneg ((b+1) / 2)); intros HH2.
      assert ((Z.of_N ((b+1)  / 2)%N = 0%Z)) by lia.
      generalize (f_equal Z.to_N H); intros HH3.
      rewrite N2Z.id in HH3.
      rewrite Z2N.inj_0 in HH3.
      generalize (N.div_str_pos (b+1) 2); intros HH4.
      lia.
    + rewrite Z.opp_involutive.
      rewrite N2Z.id.
      assert (modeq3:((b+1) mod 2 = 0)%N).
      {
        rewrite <- N.add_mod_idemp_l by lia.
        rewrite modeq2.
        simpl.
        rewrite N.mod_same; lia.
      }
      generalize (N.div_mod (b+1) 2); intros HH5.
      lia.
Qed.
Next Obligation.
  destruct (Z_ge_lt_dec a 0).
  - rewrite N.mod_mul by lia.
    rewrite N.div_mul by lia.
    rewrite Z2N.id; lia.
  - match_case; intros.
    + apply N.mod_divide in H; [| lia].
      destruct H as [k HH].
      lia.
    + rewrite N.sub_add by lia.
      rewrite N.div_mul by lia.
      rewrite Z2N.id by lia.
      rewrite Z.opp_involutive; lia.
Qed.

Global Program Instance Q_Zpos_iso : Isomorphism Q (Z*positive)
  := { iso_f q := (Qnum q, Qden q) ;
       iso_b '(z,p) := Qmake z p
     }.
Next Obligation.
  now destruct a.
Qed.

Global Instance Q_N_iso : Isomorphism Q N
  := Isomorphism_trans
       Q_Zpos_iso
       (Isomorphism_trans
          (Isomorphism_prod
             Z_N_iso positive_N_iso) N_pair_encoder).

Global Instance Q_nat_iso : Isomorphism Q nat
  := Isomorphism_trans
       Q_N_iso
       (Isomorphism_symm nat_to_N_iso).

Require Import ZArith.



Program Instance Qc_Qpos_iso : Isomorphism Q (Qc*positive)
  := {
  iso_f q := (Q2Qc q, Z.to_pos (Z.gcd (Qnum q) (Zpos (Qden q))));
  iso_b '(qc,m) := ((this qc) * (Z.pos m # m))%Q
    }.
Next Obligation.
  f_equal.
  - apply Qc_is_canon.
    unfold Qeq; simpl.
    case_eq ( (Z.ggcd (Qnum q * Z.pos p) (Z.pos (Qden q * p)))); intros; simpl.
    generalize (Z.ggcd_correct_divisors (Qnum q * Z.pos p) (Z.pos (Qden q * p))); intros HH.
    rewrite H in HH.
    destruct p0.
    destruct HH as [eqq1 eqq2].
    simpl.
    destruct q.
    destruct this.
    simpl in *.
    rewrite Pos2Z.inj_mul in eqq2.
    assert (eqq12:(Z.pos Qden * (Qnum * Z.pos p)%Z = Z.pos Qden * (z * z0)%Z)%Z)
           by now rewrite eqq1.
    assert (eqq22:(Z.pos Qden * (Qnum * Z.pos p)%Z = Qnum * (z * z1)%Z)%Z)
      by (rewrite <- eqq2; lia).
    rewrite eqq12 in eqq22.
    assert (eqq3:( z * (Z.pos Qden * z0) = z * (Qnum * z1))%Z) by lia.
    rewrite Z2Pos.id.
    + apply Z.mul_cancel_l in eqq3; [ | lia].
      lia.
    + rewrite <- Pos2Z.inj_mul in eqq2.
      generalize (Pos2Z.pos_is_pos (Qden * p)); intros HH1.
      rewrite eqq2 in HH1.
      rewrite Z.mul_comm in HH1.
      generalize (Z.ggcd_gcd (Qnum * Z.pos p) (Z.pos (Qden * p))); intros HH2.
      rewrite H in HH2; simpl in HH2.
      
      generalize (Z.gcd_nonneg (Qnum * Z.pos p) (Z.pos (Qden * p))); intros HH3.
      rewrite <- HH2 in HH3.
      assert (HH4:(z = 0 \/ 0 < z)%Z) by lia.
      destruct HH4.
      * subst.
        lia.
      * eapply Zmult_gt_0_lt_0_reg_r.
        -- apply Z.lt_gt.
           apply H0.
        -- lia.
  - simpl.
    rewrite Pos2Z.inj_mul.
    rewrite Z.gcd_mul_mono_r.
    destruct q; simpl.
    apply Qred_iff in canon.
    rewrite canon.
    simpl.
    trivial.
Qed.
Next Obligation.
  generalize (Qred_correct a); intros HH.
  red in HH.
  rewrite <- Z.ggcd_gcd.
  unfold Qred.
  destruct a.
  generalize (Z.ggcd_correct_divisors Qnum (Z.pos Qden)).
  case_eq (Z.ggcd Qnum (Z.pos Qden)).
  intros z [p q] eqq [HH1 HH2].
  simpl.
  rewrite eqq, HH1; simpl.
  unfold Qmult; simpl.
  assert (zn:(z <> 0)%Z).
  {
    intro; subst.
    simpl in HH2.
    lia.
  }
  assert (zpos:(z > 0)%Z).
  {
    generalize (Z.gcd_nonneg Qnum (Z.pos Qden)); intros HH3.
    rewrite <- Z.ggcd_gcd in HH3.
    rewrite eqq in HH3; simpl in HH3.
    lia.
  }
  assert (qpos:(q>0)%Z).
  {
    generalize (Pos2Z.is_pos Qden); intros HH3.
    eapply Z.lt_gt.
    eapply Zmult_lt_0_reg_r.
    + eapply Z.gt_lt.
      eapply zpos.
    + lia.
  } 
  rewrite Z2Pos.id by lia.
  f_equal.
  + lia.
  + rewrite <- Z2Pos.inj_mul by lia.
    apply Pos2Z.inj_pos.
    rewrite HH2.
    rewrite Z2Pos.id by lia.
    lia.
Qed.
