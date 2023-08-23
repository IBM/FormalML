From mathcomp Require Import all_ssreflect zmodp poly ssralg cyclic fingroup.

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

Local Open Scope ring_scope.
Import ssralg.GRing.
Local Open Scope group_scope.
Lemma zp_prime_units_cyclic (p : nat) :
  prime p ->
  cyclic (units_Zp_group p).
Proof.
  move=> p_prime.
  move: (field_unit_group_cyclic ).
  Admitted.

  Lemma zp_prim_root_max (p n : nat) :
    prime p ->
    { w : 'Z_p | (p-1).-primitive_root w}.
  Proof.
    intros p_prime.
    generalize (zp_prime_units_cyclic p_prime); intros.
    assert (p > 0)%N by (by apply prime_gt0).
    generalize (card_units_Zp H0); intros.
    rewrite totient_prime in H1; trivial.
    move => /cyclicP in H.
    assert (pbig: 0 < (p.-1)%N).
    {
      destruct p; [| destruct p].
      - by rewrite ltnn in H0.
      - by inversion p_prime.
      - by apply ltn0Sn.
    }

    exists (inZp (find ((p.-1).-primitive_root) [seq x <- ord_enum (Zp_trunc (pdiv p)).+2 | (x != 0)])).
    
    have/(nth_find 0)-HH: has (p.-1).-primitive_root [seq x <- ord_enum (Zp_trunc (pdiv p)).+2 | (x != 0)].
    {
      apply (@has_prim_root _ _ [seq x <- ord_enum (Zp_trunc (pdiv p)).+2 | x != 0]) => //.
      - rewrite all_filter.
        apply/allP => /= x xin.
        apply/implyP=> xn0.
        admit.
      - apply filter_uniq.
        by apply ord_enum_uniq.
      - rewrite size_filter /=.
        admit.        
    }
    
    
  Admitted.

  Lemma zp_prim_root (p n : nat) :
    n > 0 ->
    prime p ->
    n %| p-1 ->
    { w : 'Z_p | n.-primitive_root w}.
  Proof.
    intros npos prim div.
    destruct (zp_prim_root_max p prim) as [wp ?].
    generalize (dvdn_prim_root i div); intros.
    by exists (wp ^+ (div.divn (p - 1)%N n)).
  Qed.

