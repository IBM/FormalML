From mathcomp Require Import all_ssreflect zmodp poly ssralg cyclic fingroup finalg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* next 3 lemmas are copied from mathcomp_extra rsa *)

(* This should be part of the standard library *)

Lemma prime_modn_expSn p n : prime p -> n.+1 ^ p = (n ^ p).+1 %[mod p].
Proof.
case: p => // p pP.
rewrite -[(_ ^ _).+1]addn0 (expnDn 1) big_ord_recr big_ord_recl /=.
rewrite subnn binn exp1n !mul1n addnAC -modnDmr; congr ((_ + _) %% _).
apply/eqP/dvdn_sum => -[i ?] _; exact/dvdn_mulr/prime_dvd_bin. 
Qed. 

(* This should be part of the standard library *)

Lemma fermat_little a p : prime p -> a ^ p = a %[mod p].
Proof.
move=> pP.
elim: a => [|a IH]; first by rewrite exp0n // prime_gt0.
by rewrite prime_modn_expSn // -addn1 -modnDml IH modnDml addn1.
Qed.

(* This should be part of the standard library *)

Lemma fermat_little_pred a p : prime p -> ~(p %| a) -> a ^ p.-1 = 1 %[mod p].
Proof.
move=> Pp pNDa.
have a_gt0 : 0 < a by case: a pNDa.
have aCp : coprime a p by rewrite coprime_sym prime_coprime //; apply/negP.
have aE : (egcdn a p).1 * a = 1 %[mod p].
  by case: egcdnP => //= km kn -> _; rewrite (eqP aCp) modnMDl.
rewrite -[_^ _]muln1 -modnMmr -[in LHS]aE // modnMmr.
rewrite mulnC -mulnA -expnS prednK ?prime_gt0 //.
by rewrite -modnMmr fermat_little // modnMmr aE.
Qed.

Import ssralg.GRing.

Section cyclic.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Variable p : nat.
Definition Fp := if p > 1 then [set: 'F_p] else 1%g.
Definition units_Fp := [set: {unit 'F_p}].
Canonical units_Fp_group := [group of units_Fp].

  Lemma zp_prime_units_cyclic :
    prime p ->
    cyclic (units_Fp_group).
  Proof.
    generalize (field_unit_group_cyclic units_Fp_group ); intros.
    apply H.
  Qed.

  Lemma card_units_Fp : prime p -> #|units_Fp| = totient p.
  Proof.
    move=> p_prime.
    assert (p_gt0 : p > 0) by (by apply prime_gt0).
    transitivity (totient p.-2.+2); last by case: p p_gt0 => [|[|p']].
    rewrite cardsT card_sub -sum1_card big_mkcond /=.
    rewrite totient_count_coprime.
    rewrite big_mkord.
    unfold Zp_trunc.
    replace (pdiv p) with p; try easy.
    unfold pdiv.
    by rewrite primes_prime.
  Qed.

  Lemma zp_prim_root_max :
    prime p ->
    { w : 'F_p | (p-1).-primitive_root w}.
  Proof.
    intros p_prime.
    generalize (zp_prime_units_cyclic p_prime); intros.
    generalize (card_units_Fp p_prime); intros.    
    rewrite totient_prime in H0; trivial.
    move => /cyclicP in H.
    Admitted.

Local Open Scope group_scope.

Lemma prime_pbig2 (q : nat) :
  prime q ->
   0 < (q.-1)%N.
Proof.
    intros p_prime.
    assert (q > 0)%N by (by apply prime_gt0).
    destruct q; [| destruct q].
      - by rewrite ltnn in H.
      - by inversion p_prime.
      - by apply ltn0Sn.
Qed.    
  

  Lemma zp_prim_root_max_alt :
    prime p ->
    exists ( w : 'Z_p), (p-1).-primitive_root w.
  Proof.
    intros p_prime.
    generalize (prime_pbig2 p_prime); intros pbig.
    exists (inZp (find ((p.-1).-primitive_root) [seq x <- ord_enum (Zp_trunc (pdiv p)).+2 | (x != 0)])).
    have/(nth_find 0)-HH: has (p.-1).-primitive_root [seq x <- ord_enum (Zp_trunc (pdiv p)).+2 | (x != 0)].
    {
      apply (@has_prim_root _ _ [seq x <- ord_enum (Zp_trunc (pdiv p)).+2 | x != 0]) => //.
      - rewrite all_filter.
        apply/allP => /= x xin.
        apply/implyP=> xn0.
        rewrite unity_rootE.
        assert (not (is_true (dvdn p x))).
        {
          assert (x < p).
          {
            admit.
          }
          admit.
        }
        generalize (fermat_little_pred p_prime H); intros.
        admit.
      - apply filter_uniq.
        by apply ord_enum_uniq.
      - rewrite size_filter /=.
        admit.        
    }
  Admitted.

  Lemma zp_prim_root (n : nat) :
    n > 0 ->
    prime p ->
    n %| p-1 ->
    { w : 'F_p | n.-primitive_root w}.
  Proof.
    intros npos prim div.
    destruct (zp_prim_root_max prim).
    generalize (dvdn_prim_root i div); intros.
    exists (x ^+ ((p - 1) %/ n)).
    
  Admitted.

