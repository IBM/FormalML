(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(** This modules defines conversions between numbers and strings. This
relies on an intermediate representation of numbers in base 'n'. The
main use for this is when defining fresh names. *)

Require Import Orders.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Equivalence.
Require Import EquivDec.
Require Import Compare_dec.
Require Import Lia.
Require Import Nat.
Require Import ZArith.
Require Import Eqdep_dec.
Require Import Peano_dec.

(** * Preliminaries *)

Section prelude.
  (** lifted from the faq: [https://coq.inria.fr/faq] *)

  Theorem K_nat :
    forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
  Proof.
    intros; apply K_dec_set with (p := p).
    apply eq_nat_dec.
    assumption.
  Qed.

  Theorem eq_rect_eq_nat :
    forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
  Proof.
    intros; apply K_nat with (p := h); reflexivity.
  Qed.
  
  Scheme le_ind' := Induction for le Sort Prop.

  Theorem le_uniqueness_proof : forall (n m : nat) (p q : n <= m), p = q.
  Proof.
    induction p using le_ind'; intro q.
    replace (le_n n) with
    (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (refl_equal n)).
    2:reflexivity.
    generalize (refl_equal n).
    pattern n at 2 4 6 10, q; case q; [intro | intros m l e].
    rewrite <- eq_rect_eq_nat; trivial.
    contradiction (le_Sn_n m); rewrite <- e; assumption.
    replace (le_S n m p) with
    (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).
    2:reflexivity.
    generalize (refl_equal (S m)).
    pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
    contradiction (le_Sn_n m); rewrite Heq; assumption.
    injection HeqS; intro Heq; generalize l HeqS.
    rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
    rewrite (IHp l0); reflexivity.
  Qed.

End prelude.

(** * Numbers as lists of digits *)

Section Digits.
  Definition maxbase := 36.

  Context (base:nat) (basenzero:1<base).
  Definition digit := {n:nat | n < base}.

  Definition digit_proj (d:digit) : nat := proj1_sig d.

  (** ** Conversions between [nat] and lists of digits *)
  
  Section natexplosion.

    Lemma digit_pf_irrel a (pf1 pf2:a<base) : pf1 = pf2.
    Proof.
      apply le_uniqueness_proof.
    Qed.

    Lemma digit_ext (a b:digit) : proj1_sig a = proj1_sig b -> a = b.
    Proof.
      destruct a; destruct b.
      simpl.
      intros; subst.
      f_equal.
      apply digit_pf_irrel.
    Qed.
  
    Fixpoint digits_to_nat_aux (l:list digit) (acc:nat) : nat
      := match l with
         | nil => acc
         | d::lx => digits_to_nat_aux lx (acc*base+(proj1_sig d))
         end.

    Lemma digits_to_nat_aux_app l1 l2 n :
      digits_to_nat_aux (l1 ++ l2) n = digits_to_nat_aux l2 (digits_to_nat_aux l1 n).
    Proof.
      revert n l2.
      induction l1; simpl; trivial.
    Qed.

    Definition digits_to_nat (l:list digit) : nat
      := digits_to_nat_aux l 0.
    
    Fixpoint trim_digits (l:list digit) : list digit
      := match l with
         | (exist _ 0 _)::lx => trim_digits lx
         | _ => l
         end.

    Program Fixpoint nat_to_digits_backwards (n:nat) {measure n lt} :
      {l:list digit | digits_to_nat (rev l) = n /\ (forall a, hd_error (rev l) = Some a -> proj1_sig a <> 0)}
      := if n == 0
         then nil
         else exist _ (cons (n mod base)
                            (nat_to_digits_backwards (n / base)%nat)
                      ) _.
    Next Obligation.
      split; trivial.
      discriminate.
    Defined.
    Next Obligation.
      generalize (Nat.divmod_spec n base 0 base).
      destruct (Nat.divmod n base 0 base); intros; simpl.
      apply Nat.mod_upper_bound.
      lia.
    Defined.
    Next Obligation.
      apply Nat.div_lt; trivial.
      lia.
    Defined.
    Next Obligation.
      unfold digits_to_nat.
      rewrite digits_to_nat_aux_app.
      simpl.
      destruct (nat_to_digits_backwards (n / base)
                                        (nat_to_digits_backwards_obligation_3 n H)).
      simpl.
      destruct a as [e1 e2].
      split. 
      - unfold digits_to_nat in e1.
        rewrite e1.
        rewrite mult_comm.
        rewrite <- Nat.div_mod; trivial.
        lia.
      - intros. destruct (rev x); simpl in * .
        + inversion H0; clear H0; subst.
          simpl.
          unfold digits_to_nat in e1.
          simpl in *.
          rewrite <- Nat.div_exact by lia.
          rewrite <- e1.
          rewrite mult_comm.
          simpl.
          lia.
        + auto.
    Defined.

    Program Definition nat_to_digits (n:nat) : list digit
      := rev (nat_to_digits_backwards n).

    Lemma trim_digits_to_nat l : digits_to_nat (trim_digits l) = digits_to_nat l.
    Proof.
      unfold digits_to_nat.
      induction l; simpl; trivial.
      destruct a.
      destruct x; simpl; trivial.
    Qed.

    Lemma digits_to_nat_aux_acc_le_preserve l acc acc':
      acc <= acc' ->
      digits_to_nat_aux l acc <= digits_to_nat_aux l acc'.
    Proof.
      revert acc acc'.
      induction l; simpl; trivial.
      intros.
      apply IHl.
      apply plus_le_compat_r.
      apply mult_le_compat_r.
      trivial.
    Qed.

    Lemma digits_to_nat_aux_le l acc : acc <= digits_to_nat_aux l acc.
    Proof.
      revert acc.
      induction l; simpl.
      - auto.
      - intros.
        transitivity (digits_to_nat_aux l acc).
        + auto.
        + apply digits_to_nat_aux_acc_le_preserve.
          transitivity (acc*base).
          * transitivity (acc * 1).
            { lia. }
            apply mult_le_compat_l.
            lia.
          * apply le_plus_l.
    Qed.

    Lemma digits_to_nat_aux_bound l c:
      c*(base^length l) <= digits_to_nat_aux l c <  (c+1)*(base^(length l)).
    Proof.
      revert c.
      induction l; simpl.
      - split.
        + lia.
        + destruct (mult_O_le c (base*1)).
          * lia.
          * rewrite mult_comm.
            lia.
      - intros.
        destruct (IHl (c * base + proj1_sig a)) as [le1 le2].
        clear IHl.
        split.
        + rewrite <- le1.
          rewrite mult_plus_distr_r.
          rewrite mult_assoc.
          apply le_plus_l.
        + eapply lt_le_trans; [apply le2 | ].
          repeat rewrite mult_plus_distr_r.
          repeat rewrite mult_assoc.
          repeat rewrite Nat.mul_1_l.
          rewrite plus_assoc_reverse.
          apply plus_le_compat_l.
          replace 
            (proj1_sig a * base ^ Datatypes.length l + base ^ Datatypes.length l)
            with
              ((proj1_sig a +1) * base ^ Datatypes.length l).
          * apply mult_le_compat_r.
            destruct a; simpl.
            rewrite plus_comm; simpl.
            apply lt_le_S.
            trivial.
          * rewrite mult_plus_distr_r, Nat.mul_1_l; trivial.
    Qed.

    Lemma digits_to_nat_aux_acc_inj_helper1 a b c n1 n2 :
      0 <> c ->
      a < base ->
      b < base ->
      (c * base + a) * base ^ n2 < (c * base + b + 1) * base ^ n1 ->
      ~ n1 < n2.
    Proof.  
      intros ? ? ? lt1 ltn.
      assert (le12:c * base * base ^ n2 + 0 <= c * base * base ^ n2 + a * base ^ n2).
      { apply plus_le_compat_l.
        apply Peano.le_0_n.
      }
      rewrite plus_0_r in le12.
      rewrite mult_plus_distr_r in lt1.
      eapply le_lt_trans in lt1; try eapply le12.
      assert (le13:(c * base + b + 1) * (base ^ n1)
                   <=
                   (c * base + base) * (base ^ n1 )).
      {
        apply mult_le_compat_r.
        rewrite plus_assoc_reverse.
        apply plus_le_compat_l.
        lia.
      }
      eapply lt_le_trans in le13; try eapply lt1.
      rewrite (le_plus_minus n1 n2) in le13 by lia.
      rewrite Nat.pow_add_r in le13.
      rewrite mult_assoc in le13.
      assert (le14:c*base+base <= c*base*base).
      {
        replace (c*base+base) with ((c+1)*base).
        - apply mult_le_compat_r.
          rewrite mult_comm.
          destruct base.
          + lia.
          + simpl.
            apply plus_le_compat_l.
            destruct n. lia.
            destruct c. lia.
            apply lt_le_S.
            replace 0 with (S n *0) by auto.
            apply mult_lt_compat_l; lia.
        - rewrite mult_plus_distr_r.
          rewrite mult_1_l.
          trivial.
      }
      assert (le15:(c * base + base) * base ^ n1 <= (c * base * base) * base ^ n1).
      {
        apply mult_le_compat_r.
        auto.
      }
      eapply lt_le_trans in le15; try eapply le13.
      assert (le16:c * base * base ^ n1 * base <= c * base * base ^ n1 * base ^ (n2 - n1)).
      {
        apply mult_le_compat_l.
        generalize (Nat.sub_gt _ _ ltn).
        destruct (n2-n1).
        - congruence.
        - simpl; intros _ .
          replace base with (base*base^0) at 1.
          + apply mult_le_compat_l.
            apply Nat.pow_le_mono_r; lia.
          + simpl.
            rewrite mult_1_r.
            trivial.
      }
      eapply le_lt_trans in le16; try eapply le15.
      replace (c * base * base ^ n1 * base) with
          (c * base * base * base ^ n1) in le16.
      - intuition.
      - repeat rewrite mult_assoc_reverse.
        f_equal. f_equal.
        rewrite mult_comm.
        trivial.
    Qed.

    Lemma digits_to_nat_aux_acc_inj_helper12 a b c n1 n2 :
      a <> 0 ->
      a < base ->
      b < base ->
      (c * base + a) * base ^ n2 < (c * base + b + 1) * base ^ n1 ->
      ~ n1 < n2.
    Proof.  
      intros ? ? ? lt1 ltn.
      destruct (c == 0)
      ; [ | eapply (digits_to_nat_aux_acc_inj_helper1 a b c n1 n2); eauto].
      red in e; subst.
      simpl in *.
      rewrite (le_plus_minus n1 n2) in lt1 by lia.
      rewrite Nat.pow_add_r in lt1.
      rewrite (mult_comm (base ^ n1)) in lt1.
      rewrite mult_assoc in lt1.
      assert (le2:base*base^n1 <= a*base^(n2 - n1) * base ^ n1).
      {
        apply mult_le_compat_r.
        replace base with (1*base) at 1 by lia.
        apply mult_le_compat.
        - replace 1 with (1*1) by lia.
          simpl. lia.
        - simpl.
          replace base with (base^1) at 1.
          + apply Nat.pow_le_mono_r; lia.
          + apply Nat.pow_1_r.
      } 
      eapply le_lt_trans in lt1; try eapply le2; clear le2.
      assert (le3:(b + 1) * base ^ n1 <= base * base^n1).
      {
        apply mult_le_compat_r.
        lia.
      }
      eapply le_lt_trans in lt1; try eapply le3; clear le3.
      lia.
    Qed.

    Lemma digits_to_nat_aux_acc_inj_helper2 a b c n :
      (c * base + a) * base ^ n < (c * base + b + 1) * base ^ n ->
      ~ b < a.
    Proof.
      intros lt1 l2.
      apply lt_not_le in lt1.
      apply lt1.
      apply mult_le_compat_r.
      rewrite plus_assoc_reverse.
      apply plus_le_compat_l.
      lia.
    Qed.

    Lemma digits_to_nat_aux_acc_inj_helper01 a b n1 n2 :
      a <> 0 ->
      a < base ->
      b < base ->
      a * base ^ n1 < (b + 1) * base ^ n2 ->
      ~ n2 < n1.
    Proof.
      intros ? ? ? lt1 l2.
      apply lt_not_le in lt1.
      apply lt1.
      rewrite (le_plus_minus n2 n1) by lia.
      rewrite Nat.pow_add_r.
      rewrite (mult_comm a).
      rewrite (mult_comm (b+1)).
      rewrite <- mult_assoc.
      apply mult_le_compat_l.
      transitivity base; try lia.
      transitivity (base^1*a).
      - rewrite Nat.pow_1_r.
        transitivity (base * 1); try lia.
        apply mult_le_compat_l.
        lia.
      - apply mult_le_compat_r.
        apply Nat.pow_le_mono_r; lia.
    Qed.
    
    Lemma digits_to_nat_aux_acc_inj l1 l2 c (a b:digit):
      0 <> c ->
      digits_to_nat_aux l1 (c*base+proj1_sig a) = digits_to_nat_aux l2 (c*base+proj1_sig b) ->
      (length l1 = length l2) /\ a = b.
    Proof.
      destruct a as [a alt]; destruct b as [b blt]; simpl.
      intros cne0 eqq1.
      destruct (digits_to_nat_aux_bound l1 (c*base+a)) as [lb1 ub1].
      destruct (digits_to_nat_aux_bound l2 (c*base+b)) as [lb2 ub2].
      rewrite eqq1 in lb1,ub1.
      eapply le_lt_trans in lb1; [ | eapply ub2].
      eapply le_lt_trans in lb2; [ | eapply ub1].
      clear eqq1 ub1 ub2.
      revert lb1 lb2.
      generalize (Datatypes.length l1).
      generalize (Datatypes.length l2).
      intros n1 n2 lt1 lt2.
      assert (n1 = n2).
      {
        generalize (digits_to_nat_aux_acc_inj_helper1 a b c n1 n2 cne0 alt blt lt1).
        generalize (digits_to_nat_aux_acc_inj_helper1 b a c n2 n1 cne0 blt alt lt2).
        intros.
        lia.
      }
      subst.
      split; trivial.
      apply digit_ext.
      simpl.
      generalize (digits_to_nat_aux_acc_inj_helper2 a b c n2 lt1).
      generalize (digits_to_nat_aux_acc_inj_helper2 b a c n2 lt2).
      lia.
    Qed.
    
    Lemma digits_to_nat_aux_acc_inj2 l1 l2 c (a b:digit):
      proj1_sig a <> 0 ->
      proj1_sig b <> 0 ->
      digits_to_nat_aux l1 (c*base+proj1_sig a) = digits_to_nat_aux l2 (c*base+proj1_sig b) ->
      (length l1 = length l2) /\ a = b.
    Proof.
      destruct a as [a alt]; destruct b as [b blt]; simpl.
      intros ane0 bne0 eqq1.
      destruct (digits_to_nat_aux_bound l1 (c*base+a)) as [lb1 ub1].
      destruct (digits_to_nat_aux_bound l2 (c*base+b)) as [lb2 ub2].
      rewrite eqq1 in lb1,ub1.
      eapply le_lt_trans in lb1; [ | eapply ub2].
      eapply le_lt_trans in lb2; [ | eapply ub1].
      clear eqq1 ub1 ub2.
      revert lb1 lb2.
      generalize (Datatypes.length l1).
      generalize (Datatypes.length l2).
      intros n1 n2 lt1 lt2.
      assert (n1 = n2).
      {
        generalize (digits_to_nat_aux_acc_inj_helper12 a b c n1 n2 ane0 alt blt lt1).
        generalize (digits_to_nat_aux_acc_inj_helper12 b a c n2 n1 bne0 blt alt lt2).
        intros.
        lia.
      }
      subst.
      split; trivial.
      apply digit_ext.
      simpl.
      generalize (digits_to_nat_aux_acc_inj_helper2 a b c n2 lt1).
      generalize (digits_to_nat_aux_acc_inj_helper2 b a c n2 lt2).
      lia.
    Qed.
  
    Lemma digits_to_nat_aux_digits_inj l1 l2 n :
      n <> 0 ->
      digits_to_nat_aux l1 n = digits_to_nat_aux l2 n ->
      l1 = l2.
    Proof.
      simpl.
      revert l2 n.
      induction l1; destruct l2; simpl; intros.
      - trivial. 
      - generalize (digits_to_nat_aux_le l2 (n * base + proj1_sig d)); intros eqq.
        rewrite <- H0 in eqq.
        assert (le1:n * base <= n*1) by lia.
        assert (le2:n * base <= n*1) by lia.
        destruct n; [congruence|].
        apply mult_S_le_reg_l in le2.
        lia.
      - generalize (digits_to_nat_aux_le l1 (n * base + proj1_sig a)); intros eqq.
        rewrite H0 in eqq.
        assert (le1:n * base <= n*1) by lia.
        assert (le2:n * base <= n*1) by lia.
        destruct n; [congruence|].
        apply mult_S_le_reg_l in le2.
        lia.
      - assert (lt0:0<n * base).
        { assert (equ1:0<n) by lia.
          assert (eqq1:n*0<n * base).
          { apply Nat.mul_lt_mono_pos_l; trivial. lia. }
          lia.
        } 
        assert (eql:a = d).
        + generalize (digits_to_nat_aux_acc_inj
                        l1
                        l2
                        n
                        a d); intros eqq1.
          apply eqq1.
          * lia.
          * trivial.
        + subst. f_equal.
          revert H0. eapply IHl1.
          lia.
    Qed.

    Lemma trim_digits_nz {y d l}: trim_digits y = d :: l -> proj1_sig d <> 0.
    Proof.
      induction y; simpl; try discriminate.
      destruct a.
      destruct x; trivial.
      destruct d; simpl in *.
      intros.
      inversion H; subst.
      lia.
    Qed.

    Lemma digits_to_nat_nzero l x :
      x <> 0 ->
      digits_to_nat_aux l x <> 0.
    Proof.
      revert x.
      induction l; simpl; trivial; intros.
      apply IHl.
      cut (0 < x*base + proj1_sig a); [lia | ].
      cut (0 < x * base); [lia | ].
      cut (0*base < x*base); [lia | ].
      apply mult_lt_compat_r; lia.
    Qed.

    Lemma trim_nat_to_digits x :
      trim_digits (nat_to_digits x) = nat_to_digits x.
    Proof.
      unfold nat_to_digits; simpl.
      destruct (nat_to_digits_backwards x); simpl.
      destruct a as [_ pf2].
      destruct (rev x0); simpl; trivial.
      destruct d; simpl in *.
      specialize (pf2 _ (eq_refl _)).
      simpl in pf2.
      destruct x1; simpl; trivial.
      congruence.
    Qed.

    Theorem digits_to_nat_inv x y :
      digits_to_nat x = digits_to_nat y ->
      trim_digits x = trim_digits y.
    Proof.
      rewrite <- (trim_digits_to_nat x).
      rewrite <- (trim_digits_to_nat y).
      unfold digits_to_nat.
      case_eq (trim_digits x);
        case_eq (trim_digits y);
        simpl; intros.
      - trivial.
      - generalize (trim_digits_nz H); intros neq1.
        generalize (digits_to_nat_nzero l _ neq1).
        congruence.
      - generalize (trim_digits_nz H0); intros neq1.
        generalize (digits_to_nat_nzero l _ neq1).
        congruence.
      - generalize (trim_digits_nz H); intros nz
        ; generalize (trim_digits_nz H0); intros nz0.
        clear H H0 x y.
        generalize (digits_to_nat_aux_acc_inj2 l0 l 0 d0 d nz0 nz).
        simpl.
        intros HH.
        specialize (HH H1).
        destruct HH as [leq deq].
        subst.
        f_equal.
        eapply digits_to_nat_aux_digits_inj; eauto.
    Qed.

    Theorem nat_to_digits_inv x y :
      nat_to_digits x = nat_to_digits y ->
      x = y.
    Proof.
      unfold nat_to_digits.
      destruct (nat_to_digits_backwards x);
        destruct (nat_to_digits_backwards y).
      simpl; intros eqq.
      intuition.
      congruence.
    Qed.

    Theorem nat_to_digits_to_nat (n:nat) :
      digits_to_nat (nat_to_digits n) = n.
    Proof.
      unfold digits_to_nat, nat_to_digits.
      destruct (nat_to_digits_backwards n).
      simpl.
      unfold digits_to_nat in * .
      destruct a as [pf1 _].
      rewrite pf1; trivial.
    Qed.

    
    Theorem digits_to_nat_to_digits (ld:list digit) :
      nat_to_digits (digits_to_nat ld) = trim_digits ld.
    Proof.
      simpl.
      rewrite <- trim_nat_to_digits.
      apply digits_to_nat_inv.
      rewrite nat_to_digits_to_nat.
      trivial.
    Qed.

  End natexplosion.

  (** ** Conversions between [nat] and strings *)
  
  Section Ntostring.

    Definition digit_to_char (n:digit) : ascii
      := match proj1_sig n with
         | 0 => "0"%char
         | 1 => "1"%char
         | 2 => "2"%char
         | 3 => "3"%char
         | 4 => "4"%char
         | 5 => "5"%char
         | 6 => "6"%char
         | 7 => "7"%char
         | 8 => "8"%char
         | 9 => "9"%char
         | 10 => "A"%char
         | 11 => "B"%char
         | 12 => "C"%char
         | 13 => "D"%char
         | 14 => "E"%char
         | 15 => "F"%char
         | 16 => "G"%char
         | 17 => "H"%char
         | 18 => "I"%char
         | 19 => "J"%char
         | 20 => "K"%char
         | 21 => "L"%char
         | 22 => "M"%char
         | 23 => "N"%char
         | 24 => "O"%char
         | 25 => "P"%char
         | 26 => "Q"%char
         | 27 => "R"%char
         | 28 => "S"%char
         | 29 => "T"%char
         | 30 => "U"%char
         | 31 => "V"%char
         | 32 => "W"%char
         | 33 => "X"%char
         | 34 => "Y"%char
         | 35 => "Z"%char
         | _ => "?"%char
         end.

    Definition char_to_digit_aux (a:ascii) : option nat
      := match a with
         | "0"%char => Some 0
         | "1"%char => Some 1
         | "2"%char => Some 2
         | "3"%char => Some 3
         | "4"%char => Some 4
         | "5"%char => Some 5
         | "6"%char => Some 6
         | "7"%char => Some 7
         | "8"%char => Some 8
         | "9"%char => Some 9
         | "A"%char => Some 10
         | "B"%char => Some 11
         | "C"%char => Some 12
         | "D"%char => Some 13
         | "E"%char => Some 14
         | "F"%char => Some 15
         | "G"%char => Some 16
         | "H"%char => Some 17
         | "I"%char => Some 18
         | "J"%char => Some 19
         | "K"%char => Some 20
         | "L"%char => Some 21
         | "M"%char => Some 22
         | "N"%char => Some 23
         | "O"%char => Some 24
         | "P"%char => Some 25
         | "Q"%char => Some 26
         | "R"%char => Some 27
         | "S"%char => Some 28
         | "T"%char => Some 29
         | "U"%char => Some 30
         | "V"%char => Some 31
         | "W"%char => Some 32
         | "X"%char => Some 33
         | "Y"%char => Some 34
         | "Z"%char => Some 35
         | _ => None
         end.

    Program Definition char_to_digit (a:ascii) : option digit
      := match char_to_digit_aux a with
         | Some n =>
           match lt_dec n base with
           | left pf => Some (exist _ n pf)
           | right _ => None
           end
         | None => None
         end.

    Lemma char_to_digit_to_char (a:ascii) (d:digit) :
      char_to_digit a = Some d -> digit_to_char d = a.
    Proof.
      unfold char_to_digit, digit_to_char.
      destruct a; simpl.
      destruct b; destruct b0
      ; destruct b1; destruct b2
      ; destruct b3; destruct b4
      ; destruct b5; destruct b6
      ; simpl; try discriminate
      ; match goal with
        | [|- context[match ?x with
                      | left _ => _
                      | right _ => _
                      end]] => destruct x
        end; intros eqq; inversion eqq; clear eqq
      ; subst; simpl; trivial.
    Qed.

    Lemma digit_to_char_to_digit (basesmall:base<=maxbase) (d:digit) :
      char_to_digit (digit_to_char d) = Some d.
    Proof.
      unfold char_to_digit, digit_to_char.
      destruct d; simpl.
      unfold maxbase in *.
      do 36 (destruct x; simpl;
             [match goal with
              | [|- context[match ?x with
                            | left _ => _
                            | right _ => _
                            end]] =>
                destruct x
                ; f_equal; trivial
                ;  [apply digit_ext; simpl; trivial
                   | congruence]
              end | ]).
      lia.
    Qed.

    Fixpoint string_to_digits (s:string) : option (list digit*string)
      := match s with
         | ""%string => None
         | String a s' =>
           match char_to_digit a with
           | Some dd =>
             match string_to_digits s' with
             | Some (ld,rest) => Some (dd::ld,rest)
             | None => Some (dd::nil,s')
             end
           | None => None
           end
         end.

    Fixpoint list_to_string (l:list ascii) : string
      := match l with
         | nil => EmptyString
         | cons x xs => String x (list_to_string xs)
         end.

    Definition digits_to_string_aux (ld:list digit) : string
      := list_to_string (map digit_to_char ld).

    Definition digits_to_string (ld:list digit) : string
      := match digits_to_string_aux ld with
         | ""%string => "0"
         | s => s
         end.

    Lemma string_to_digits_to_string_aux (s:string) (ld:list digit) (rest:string) :
      string_to_digits s = Some (ld,rest) ->
      (digits_to_string_aux ld ++ rest)%string = s.
    Proof.
      revert ld rest.
      induction s; simpl; try discriminate; intros.
      case_eq (char_to_digit a); [intros ? eqq | intros eqq]
      ; rewrite eqq in H; try discriminate.
      case_eq (string_to_digits s); [intros ? eqq2 | intros eqq2]
      ; rewrite eqq2 in H.
      - destruct p.
        inversion H; clear H; subst.
        simpl.
        unfold digits_to_string_aux in IHs.
        rewrite (IHs _ _ eqq2).
        f_equal.
        apply char_to_digit_to_char; auto.
      - inversion H; clear H; subst.
        simpl.
        f_equal.
        apply char_to_digit_to_char; auto.
    Qed.

    Lemma string_to_digits_to_string (s:string) (ld:list digit) (rest:string) :
      string_to_digits s = Some (ld,rest) ->
      (digits_to_string ld ++ rest)%string = s.
    Proof.
      unfold digits_to_string.
      case_eq (digits_to_string_aux ld).
      - simpl; intros.
        unfold digits_to_string_aux in H.
        destruct ld; simpl in H; try discriminate.
        destruct s; simpl in H0; try discriminate.
        destruct (char_to_digit a); try discriminate.
        destruct (string_to_digits s); try discriminate.
        destruct p.
        inversion H0.
      - intros.
        rewrite <- H.
        apply string_to_digits_to_string_aux; trivial.
    Qed.

    Lemma string_to_digits_empty : string_to_digits ""%string = None.
    Proof.
      reflexivity.
    Qed.

    Fixpoint iszeros (s:string)
      := match s with
         | ""%string => True
         | String a s' => "a"%char = "0"%char /\ iszeros s'
         end.

    Fixpoint trim_extra_stringdigits (s:string)
      :=  match s with
          | String "0" s => trim_extra_stringdigits s
          | _ => s
          end.
    
    Definition default_to_string0 (s:string)
      :=  match string_to_digits s with
          | Some _ => s
          | None => String "0" s
          end.


    Definition trim_stringdigits (s:string)
      :=  default_to_string0 (trim_extra_stringdigits s). 

    Lemma digit0pf : 0 < base.
    Proof.
      lia.
    Qed.

    Definition digit0 : digit := exist _ 0 digit0pf.

    Definition default_to_digits0 l
      :=  match l with
          | nil => digit0::nil
          | _ => l
          end.

    Lemma char_to_digit0 : (char_to_digit "0") = Some digit0.
    Proof.
      unfold char_to_digit.
      simpl.
      destruct (lt_dec 0 base).
      - f_equal.
        apply digit_ext.
        simpl; trivial.
      - lia.
    Qed.

    Lemma char_to_digit0_inv a pf :
      char_to_digit a = Some (exist _ 0 pf) -> a = "0"%char.
    Proof.
      intros eqq.
      apply char_to_digit_to_char in eqq.
      rewrite <- eqq.
      reflexivity.
    Qed.

    Lemma trim_stringdigits_some s l1 rest :
      string_to_digits s = Some (l1, rest) ->
      string_to_digits (trim_stringdigits (String "0" s)) =
      string_to_digits (trim_stringdigits s).
    Proof.
      unfold trim_stringdigits; simpl; intros eqq.
      trivial.
    Qed.

    Lemma trim_extra_stringdigits_None rest :
      string_to_digits rest = None ->
      trim_extra_stringdigits rest = rest.
    Proof.
      destruct rest; simpl; trivial.
      destruct a; simpl.
      destruct b; destruct b0
      ; destruct b1; destruct b2
      ; destruct b3; destruct b4
      ; destruct b5; destruct b6; trivial.
      rewrite char_to_digit0.
      case_eq (string_to_digits rest); intros.
      - destruct p; discriminate.
      - discriminate.
    Qed.

    Lemma trim_extra_stringdigits_nzero  a s :
      a<> "0"%char ->
      trim_extra_stringdigits (String a s) = String a s.
    Proof.
      intros neqq.
      destruct a; simpl.
      destruct b; destruct b0
      ; destruct b1; destruct b2
      ; destruct b3; destruct b4
      ; destruct b5; destruct b6; trivial.
      congruence.
    Qed.

    Lemma string_to_digits_trim s l rest:
      string_to_digits s = Some (l, rest) ->
      string_to_digits (trim_stringdigits s) = Some (default_to_digits0 (trim_digits l),rest).
    Proof.
      revert l rest.
      induction s; simpl; try discriminate; intros.
      case_eq (char_to_digit a)
      ; [intros ? eqq | intros eqq]
      ; rewrite eqq in H; try discriminate.
      destruct (ascii_dec a "0"%char).
      - subst.
        unfold char_to_digit in eqq; simpl in eqq.
        destruct (lt_dec 0 base); [ | lia].
        inversion eqq; clear eqq; subst.
        case_eq (string_to_digits s)
        ; [intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in H.
        + destruct p.
          inversion H; clear H; subst.
          simpl.
          apply IHs; trivial.
        + inversion H; clear H; subst.
          simpl.
          unfold trim_stringdigits; simpl.
          rewrite trim_extra_stringdigits_None by trivial.
          unfold default_to_string0.
          rewrite eqq2.
          simpl.
          rewrite char_to_digit0.
          rewrite eqq2.
          trivial.
      - unfold trim_stringdigits.
        rewrite trim_extra_stringdigits_nzero by trivial.
        unfold default_to_string0; simpl.
        rewrite eqq.
        case_eq (string_to_digits s)
        ; [intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in H.
        + destruct p.
          inversion H; clear H; subst.
          simpl. rewrite eqq.
          rewrite eqq2.
          destruct d; simpl.
          destruct x; trivial.
          apply char_to_digit0_inv in eqq.
          congruence.
        + inversion H; clear H; subst.    
          simpl.
          rewrite eqq, eqq2.
          destruct d; simpl.
          destruct x; trivial.
          apply char_to_digit0_inv in eqq.
          congruence.
    Qed.

    (* nat_to_digits *)

    Lemma digits_to_string_aux_to_digits_None
          (basesmall:base<=maxbase) (ld:list digit) (rest:string) :
      string_to_digits rest = None ->
      ld <> nil ->
      string_to_digits (digits_to_string_aux ld ++ rest) = Some (ld,rest).
    Proof.
      unfold maxbase in *.
      intros eqq1.
      induction ld; simpl.
      - congruence.
      - intros.
        rewrite digit_to_char_to_digit by trivial.
        destruct ld; simpl.
        + rewrite eqq1; trivial.
        + rewrite digit_to_char_to_digit by trivial.
          unfold digits_to_string_aux in IHld.
          simpl in IHld.
          assert (neq: d::ld <> nil) by congruence.
          specialize (IHld neq); clear neq.
          rewrite digit_to_char_to_digit in IHld by trivial.
          case_eq (string_to_digits (list_to_string (map digit_to_char ld) ++ rest))
          ; [intros ? eqq2 | intros eqq2]; rewrite eqq2 in IHld.
          * destruct p.
            inversion IHld; congruence.
          * inversion IHld; congruence.
    Qed.

    Definition nat_to_string (n:nat) : string
      := digits_to_string (nat_to_digits n).

    Definition string_to_nat (s:string) :  option (nat*string)
      := match string_to_digits s with
         | Some (dl,rest) => Some (digits_to_nat dl, rest)
         | None => None
         end.

    Lemma digits_to_string_default l :
      digits_to_string (default_to_digits0 l) = digits_to_string l.
    Proof.
      unfold default_to_digits0, digits_to_string.
      destruct l; simpl; trivial.
    Qed.
  
    Theorem string_to_nat_to_string (s:string) (n:nat) (rest:string) :
      string_to_nat s = Some (n,rest) ->
      (nat_to_string n ++ rest)%string = trim_stringdigits s.
    Proof.
      unfold string_to_nat, nat_to_string.
      case_eq (string_to_digits s); try discriminate.
      destruct p; intros eqq1 eqq2.
      inversion eqq2; clear eqq2; subst.
      rewrite digits_to_nat_to_digits.
      rewrite <- digits_to_string_default.
      apply string_to_digits_to_string.
      rewrite (string_to_digits_trim _ _ _ eqq1).
      trivial.
    Qed.

    Lemma digits_to_string_aux_empty n:
      digits_to_string_aux (nat_to_digits n) = ""%string -> n = 0.
    Proof.
      unfold nat_to_digits.
      destruct (nat_to_digits_backwards n); simpl.
      destruct a as [pf1 pf2].
      unfold digits_to_string_aux.
      unfold digits_to_nat in *.
      intros eqq2.
      destruct (rev x).
      - simpl in pf1; congruence.
      - simpl in eqq2. discriminate.
    Qed.

    Lemma append_nil_r s : (s ++ "")%string = s.
    Proof.
      induction s; simpl; congruence.
    Qed.
      
    Theorem nat_to_string_to_nat (basesmall:base<=maxbase) n (rest:string) :
      string_to_digits rest = None ->
      string_to_nat (nat_to_string n ++ rest) = Some (n, rest).
    Proof.
      unfold maxbase in *.
      unfold string_to_nat, nat_to_string; intros eqq.
      unfold digits_to_string.
      case_eq (digits_to_string_aux (nat_to_digits n)); simpl; intros.
      - rewrite char_to_digit0, eqq.
        apply digits_to_string_aux_empty in H.
        unfold digits_to_nat.
        simpl.
        congruence.
      -  assert (nn:nat_to_digits n <> nil).
         {
           destruct (nat_to_digits n); trivial; [ | congruence ].
           unfold digits_to_string_aux in H.
           simpl in H.
           congruence.
         } 
         generalize (digits_to_string_aux_to_digits_None basesmall (nat_to_digits n) rest); intros eqq2.
         specialize (eqq2 eqq nn).
         rewrite H in eqq2.
         simpl in eqq2.
         case_eq (char_to_digit a )
         ; [intros ? eqq3 | intros eqq3]; rewrite eqq3 in eqq2
         ; try discriminate.
         case_eq (string_to_digits (s ++ rest) )
         ; [intros ? eqq4 | intros eqq4]; rewrite eqq4 in eqq2.
         + destruct p.
           inversion eqq2; clear eqq2; subst.
           rewrite H1.
           rewrite nat_to_digits_to_nat.
           trivial.
         + inversion eqq2; clear eqq2.
           repeat rewrite H2.
           rewrite H1.
           rewrite nat_to_digits_to_nat.
           trivial.
    Qed.

    Theorem nat_to_string_inj_full (basesmall:base<=maxbase) n1 n2 rest1 rest2 :
      string_to_digits rest1 = None ->
      string_to_digits rest2 = None ->
      (nat_to_string n1 ++ rest1 = nat_to_string n2 ++ rest2)%string ->
      n1 = n2 /\ rest1 = rest2.
    Proof.
      intros neq1 neq2 eqq1.
      generalize (nat_to_string_to_nat basesmall n1 rest1 neq1); intros eqq11.
      generalize (nat_to_string_to_nat basesmall n2 rest2 neq2); intros eqq12.
      rewrite eqq1 in eqq11.
      rewrite eqq11 in eqq12.
      inversion eqq12.
      tauto.
    Qed.
    
    Theorem nat_to_string_inj (basesmall:base<=maxbase) n1 n2 :
      nat_to_string n1 = nat_to_string n2 -> n1 = n2.
    Proof.
      intros eqq.
      generalize ((nat_to_string_inj_full basesmall n1 n2 "" "")%string).
      simpl.
      repeat rewrite append_nil_r.
      intuition.
    Qed.

  End Ntostring.

  (** ** Conversions between [Z] and strings *)
  
  Section Ztostring.

    Local Open Scope Z.

    Definition Z_to_string (z:Z) :=
      match z with
      | Z0 => "0"%string
      | Zpos n => nat_to_string (Pos.to_nat n)
      | Zneg n => String ("-"%char) (nat_to_string (Pos.to_nat n))
      end.

    Definition string_to_Z (s:string) : option (Z* string)
      := match s with
         | ""%string => None
         | String ("+"%char) l' =>
           match string_to_nat l' with
           | Some (n,rest) => Some (Z.of_nat n, rest)
           | None => None
           end
         | String ("-"%char) l' =>
           match string_to_nat l' with
           | Some (n,rest) =>
             match n with
             | 0%nat => None 
             | _ => Some (Zneg (Pos.of_nat n), rest)
             end
           | None => None
           end
         | l' =>
           match string_to_nat l' with
           | Some (n,rest) => Some (Z.of_nat n, rest)
           | None => None
           end
         end.

    Definition trim_stringZdigits (s:string)
      := match s with
         | String "+" l => trim_stringdigits l
         | String "-" l => String "-" (trim_stringdigits l)
         | l => trim_stringdigits l
         end.

    Lemma nat_to_string_nempty n : nat_to_string n <> ""%string.
    Proof.
      unfold nat_to_string, digits_to_string.
      destruct (digits_to_string_aux (nat_to_digits n)); simpl; congruence.
    Qed.

    Lemma append_empty_both l1 l2
      : (l1 ++ l2)%string = ""%string ->
        l1 = ""%string /\ l2 = ""%string.
    Proof.
      destruct l1; simpl.
      - tauto.
      - inversion 1.
    Qed.
    
    Theorem string_to_Z_to_string (s:string) (n:Z) (rest:string) :
      string_to_Z s = Some (n,rest) ->
      (Z_to_string n ++ rest)%string = trim_stringZdigits s.
    Proof.
      unfold string_to_Z, Z_to_string.
      destruct s; simpl; try discriminate.
      destruct a.
      intros eqq.
      destruct b; destruct b0
      ; destruct b1; destruct b2
      ; destruct b3; destruct b4
      ; destruct b5; destruct b6
      ; simpl in *; try solve[inversion eqq]
      ; (match type of eqq with
         | context[match ?x with
                   | Some _ => _
                   | None => _
                   end] => case_eq x; [intros ? eqq2 | intros eqq2];rewrite eqq2 in eqq
         end; [|discriminate]
         ; destruct p; inversion eqq; clear eqq; subst)
      ; try solve [rewrite <- (string_to_nat_to_string _ _ _ eqq2)
                   ; destruct n0; simpl; trivial
                   ; rewrite SuccNat2Pos.id_succ; trivial].
      destruct n0; try discriminate.
      inversion H0; clear H0; subst.
      rewrite <- (string_to_nat_to_string _ _ _ eqq2).
      simpl; f_equal.
      f_equal.
      f_equal.
      destruct n0; try reflexivity.
      rewrite Pos.succ_of_nat by congruence.
      rewrite SuccNat2Pos.id_succ.
      trivial.
    Qed.
    
    Theorem Z_to_string_to_Z (basesmall:(base<=maxbase)%nat) n (rest:string) :
      string_to_digits rest = None ->
      string_to_Z (Z_to_string n ++ rest) = Some (n, rest).
    Proof.
      unfold string_to_Z, Z_to_string.
      intros neq.
      destruct n; simpl.
      - unfold string_to_nat.
        simpl.
        rewrite char_to_digit0, neq.
        simpl; trivial.
      - rewrite nat_to_string_to_nat by trivial.
        case_eq ((nat_to_string (Pos.to_nat p) ++ rest))%string.
        + intros eqq1; apply append_empty_both in eqq1.
          destruct eqq1; subst.
          apply nat_to_string_nempty in H.
          intuition.
        + intros.
          rewrite positive_nat_Z.
          destruct a; trivial.
          destruct b; destruct b0
          ; destruct b1; destruct b2
          ; destruct b3; destruct b4
          ; destruct b5; destruct b6; trivial.
          * generalize (nat_to_string_to_nat basesmall (Pos.to_nat p) _ neq).
            rewrite H; inversion 1.
          * generalize (nat_to_string_to_nat basesmall (Pos.to_nat p) _ neq).
            rewrite H; inversion 1.
      - rewrite nat_to_string_to_nat by trivial.
        rewrite Pos2Nat.id.
        case_eq (Pos.to_nat p); trivial.
        generalize (Pos2Nat.is_pos p).
        lia.
    Qed.

    Theorem Z_to_string_inj_full
            (basesmall:(base<=maxbase)%nat) n1 n2 rest1 rest2 :
      string_to_digits rest1 = None ->
      string_to_digits rest2 = None ->
      (Z_to_string n1 ++ rest1 = Z_to_string n2 ++ rest2)%string ->
      n1 = n2 /\ rest1 = rest2.
    Proof.
      intros neq1 neq2 eqq1.
      generalize (Z_to_string_to_Z basesmall n1 rest1 neq1); intros eqq11.
      generalize (Z_to_string_to_Z basesmall n2 rest2 neq2); intros eqq12.
      rewrite eqq1 in eqq11.
      rewrite eqq11 in eqq12.
      inversion eqq12.
      tauto.
    Qed.

    Theorem Z_to_string_inj (basesmall:(base<=maxbase)%nat) n1 n2 :
      Z_to_string n1 = Z_to_string n2 -> n1 = n2.
    Proof.
      intros eqq.
      generalize ((Z_to_string_inj_full basesmall n1 n2 "" "")%string).
      simpl.
      repeat rewrite append_nil_r.
      intuition.
    Qed.

  End Ztostring.

End Digits.

(** * Integers in base 'n' *)

Section Bases.
 
  Definition lt_decider (a b:nat) :
    match lt_dec a b with
    | left pf => lt a b
    | right _ => True
    end.
  Proof.
    destruct (lt_dec); trivial.
  Defined.

  Definition le_decider (a b:nat) :
    match le_dec a b with
    | left pf => le a b
    | right _ => True
    end.
  Proof.
    destruct (le_dec); trivial.
  Defined.

  (** ** Base 2 *)
  
  Section base2.
    Definition base2valid : 1 < 2 := lt_decider 1 2.
    Definition base2small : 2 <= maxbase := le_decider 2 maxbase.

    Section nat.
      Definition nat_to_string2 := nat_to_string 2 base2valid.
      Definition string2_to_nat := string_to_nat 2.

      Definition nat_to_string2_to_nat 
        := nat_to_string_to_nat 2 base2valid base2small.
      
      Definition string2_to_nat_to_string2
        := string_to_nat_to_string 2 base2valid.
      
      Definition nat_to_string2_inj
        : forall x y : nat, nat_to_string2 x = nat_to_string2 y -> x = y
        := nat_to_string_inj 2 base2valid base2small.
      
    End nat.
    
    Section Z.
      Definition Z_to_string2 := Z_to_string 2 base2valid.
      Definition string2_to_Z := string_to_Z 2.

      Definition Z_to_string2_to_Z 
        := Z_to_string_to_Z 2 base2valid base2small.
      
      Definition string2_to_Z_to_string2
        := string_to_Z_to_string 2 base2valid.
      
      Definition Z_to_string2_inj
        : forall x y : Z, Z_to_string2 x = Z_to_string2 y -> x = y
        := Z_to_string_inj 2 base2valid base2small.
      
    End Z.
  End base2.

  (** ** Base 8 *)
  
  Section base8.
    Definition base8valid : 1 < 8 := lt_decider 1 8.
    Definition base8small : 8 <= maxbase := le_decider 8 maxbase.

    Section nat.
      Definition nat_to_string8 := nat_to_string 8 base8valid.
      Definition string8_to_nat := string_to_nat 8.

      Definition nat_to_string8_to_nat 
        := nat_to_string_to_nat 8 base8valid base8small.
      
      Definition string8_to_nat_to_string8
        := string_to_nat_to_string 8 base8valid.
      
      Definition nat_to_string8_inj
        : forall x y : nat, nat_to_string8 x = nat_to_string8 y -> x = y
        := nat_to_string_inj 8 base8valid base8small.

    End nat.
    
    Section Z.
      Definition Z_to_string8 := Z_to_string 8 base8valid.
      Definition string8_to_Z := string_to_Z 8.

      Definition Z_to_string8_to_Z 
        := Z_to_string_to_Z 8 base8valid base8small.
      
      Definition string8_to_Z_to_string8
        := string_to_Z_to_string 8 base8valid.
      
      Definition Z_to_string8_inj
        : forall x y : Z, Z_to_string8 x = Z_to_string8 y -> x = y
        := Z_to_string_inj 8 base8valid base8small.
      
    End Z.
    
  End base8.
  
  (** ** Base 10 *)
  
  Section base10.
    Definition base10valid : 1 < 10 := lt_decider 1 10.
    Definition base10small : 10 <= maxbase := le_decider 10 maxbase.

    Section nat.
      Definition nat_to_string10 := nat_to_string 10 base10valid.
      Definition string10_to_nat := string_to_nat 10.
      
      Definition nat_to_string10_to_nat 
        := nat_to_string_to_nat 10 base10valid base10small.
      
      Definition string10_to_nat_to_string10
        := string_to_nat_to_string 10 base10valid.
      
      Definition nat_to_string10_inj
        : forall x y : nat, nat_to_string10 x = nat_to_string10 y -> x = y
        := nat_to_string_inj 10 base10valid base10small.

    End nat.
    
    Section Z.
      Definition Z_to_string10 := Z_to_string 10 base10valid.
      Definition string10_to_Z := string_to_Z 10.
            
      Definition Z_to_string10_to_Z 
        := Z_to_string_to_Z 10 base10valid base10small.
      
      Definition string10_to_Z_to_string10
        := string_to_Z_to_string 10 base10valid.
      
      Definition Z_to_string10_inj
        : forall x y : Z, Z_to_string10 x = Z_to_string10 y -> x = y
        := Z_to_string_inj 10 base10valid base10small.
      
    End Z.
  End base10.
  
  (** ** Base 16 *)
  
  Section base16.
    Definition base16valid : 1 < 16 := lt_decider 1 16.
    Definition base16small : 16 <= maxbase := le_decider 16 maxbase.

    Section nat.
      Definition nat_to_string16 := nat_to_string 16 base16valid.
      Definition string16_to_nat := string_to_nat 16.


      Definition nat_to_string16_to_nat 
        := nat_to_string_to_nat 16 base16valid base16small.
      
      Definition string16_to_nat_to_string16
        := string_to_nat_to_string 16 base16valid.
      
      Definition nat_to_string16_inj
        : forall x y : nat, nat_to_string16 x = nat_to_string16 y -> x = y
        := nat_to_string_inj 16 base16valid base16small.

    End nat.
    
    Section Z.
      Definition Z_to_string16 := Z_to_string 16 base16valid.
      Definition string16_to_Z := string_to_Z 16.

      Definition Z_to_string16_to_Z 
        := Z_to_string_to_Z 16 base16valid base16small.
      
      Definition string16_to_Z_to_string16
        := string_to_Z_to_string 16 base16valid.
      
      Definition Z_to_string16_inj
        : forall x y : Z, Z_to_string16 x = Z_to_string16 y -> x = y
        := Z_to_string_inj 16 base16valid base16small.
      
    End Z.
  End base16.

End Bases.

