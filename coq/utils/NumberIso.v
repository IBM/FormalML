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

Global Program Instance Q_Zpos_iso : Isomorphism (Q) (Z*positive)
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
