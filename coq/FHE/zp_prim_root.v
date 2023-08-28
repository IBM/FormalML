Require Import Lia.
From mathcomp Require Import all_ssreflect zmodp poly ssralg cyclic fingroup finalg ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

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

Variable p : nat.

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

   Lemma Fp_exp_expn (x : 'F_p) (n : nat):
     prime p ->
     nat_of_ord (x ^+ n)%R = x ^ n %% p.
   Proof.
     intros p_prime.
     generalize (Fp_cast p_prime); intros.
     induction n.
     - by rewrite /= {1}H expn0.
     - rewrite expnS exprS /mul /= IHn -modnMm.
       rewrite {2}H {3}H {3}H.
       by rewrite -(modnMm x _) modn_mod.
   Qed.

  Lemma zp_prim_root_max :
    prime p ->
    { w : 'F_p | (p.-1).-primitive_root w}.
  Proof.
    intros p_prime.
    generalize (prime_pbig2 p_prime); intros pbig.
    have/(nth_find 0)-HH: has (p.-1).-primitive_root [seq x <- enum 'F_p | x != Zp0].
    {
      apply (@has_prim_root _ _ [seq x <- enum 'F_p | x != Zp0]) => //.
      - rewrite all_filter.
        apply/allP => /= x xin.
        apply/implyP=> xn0.
        rewrite unity_rootE.
        assert (not (is_true (dvdn p x))).
        {
          assert (x < p).
          {
            generalize (ltn_ord x); intros.
            by rewrite {2}(Fp_cast p_prime) in H.
          }
          assert (0 < x) by by rewrite lt0n.
          unfold not; intros.
          generalize (dvdn_leq H0 H1); lia.
        }
        generalize (fermat_little_pred p_prime H); intros.
        apply /eqP.
        apply val_inj => /=.
        by rewrite {2}(Fp_cast p_prime) -H0 Fp_exp_expn.
      - simpl.
        apply filter_uniq.
        apply enum_uniq.
      - rewrite -rem_filter; [| apply enum_uniq].
        rewrite size_rem.
        + by rewrite -cardE (card_Fp p_prime).
        + by rewrite enumT Finite.EnumDef.enumDef /=  mem_ord_enum.
    } 
    by exists ([seq x <- enum 'F_p | x != 0]`_(find (p.-1).-primitive_root [seq x <- enum 'F_p | x != 0])).
  Qed.  

  Lemma zp_prim_root (n : nat) :
    n > 0 ->
    prime p ->
    n %| p.-1 ->
    { w : 'F_p | n.-primitive_root w}.
  Proof.
    intros npos prim div.
    destruct (zp_prim_root_max prim).
    generalize (dvdn_prim_root i div); intros.
    by exists (exp x (p.-1 %/ n)).
  Qed.

End cyclic.

Require Import List.
From mathcomp Require Import seq.
Require Import Permutation.

Section chinese.

  (* pairs represent (residue, modulus) *)
  Fixpoint chinese_list (l : seq (nat * nat)) : nat :=
    match l with
    | nil => 0
    | a :: nil => a.1
    | a :: l' =>
        chinese (a.2) (fold_left muln (map snd l') 1)
          (a.1) (chinese_list l')
    end.

  Lemma all_coprime (a a0 : nat) (l : seq nat) :
    coprime a a0 ->
    all (coprime a) l ->
    coprime a (fold_left muln l a0).
  Proof.
    revert a0.
    induction l; simpl; intros; trivial.
    move => /andP in H0.
    destruct H0.
    apply IHl; trivial.
    rewrite coprimeMr.
    by apply /andP.
  Qed.

  Lemma pairwise_coprime_list (l : seq nat) :
    pairwise coprime l ->
    match l with
    | nil => true
    | a :: l' => coprime a (fold_left muln l' 1)
    end.
  Proof.
    induction l; simpl; trivial.
    intros.
    move => /andP in H.
    destruct H.
    apply all_coprime; trivial.
    apply coprimen1.
 Qed.

  Lemma chinese_remainder_list_l (l : list (nat * nat)) :
    pairwise coprime (map snd l) ->
    match l with
    | nil => true
    | a :: _ => chinese_list l == a.1 %[mod a.2]
    end.
  Proof.
     induction l; simpl; trivial; intros.
     destruct l; trivial.
     rewrite chinese_modl //.
     move => /andP in H; destruct H.
     apply all_coprime; trivial.
     apply coprimen1.
  Qed.

  Lemma chinese_reminder_list_cons1 (a : nat * nat) (l : list (nat * nat)) :
        pairwise coprime (map snd (a::l)) ->
        chinese_list (a::l) == a.1 %[mod a.2].
  Proof.
    intros.
    by apply (chinese_remainder_list_l H).
  Qed.

  Lemma chinese_reminder_list_cons2 (a : nat * nat) (l : list (nat * nat)) :
        pairwise coprime (map snd (a::l)) ->
        let m := fold_left muln (map snd l) 1 in 
        chinese_list (a::l) == chinese_list l %[mod m].
  Proof.
    intros.
    simpl.
    destruct l; trivial.
    - apply /eqP.
      by rewrite modn1.
    - rewrite chinese_modr //.
      apply all_coprime.
      + apply coprimen1.
      + move => /andP in H.
        by destruct H.
 Qed.

(*
  Lemma Gauss_dvd_l m n p :
    m * n %| p -> (m %| p).
  Proof.
    Search dvdn.
    unfold dvdn.
    Search modn.
    generalize
  Admitted.
  
  Lemma modn_muln x y b1 b2 :
    x == y %[mod b1 * b2] ->
    (x == y %[mod b1]).
  Proof.
    wlog le_yx : x y / y <= x; last rewrite !eqn_mod_dvd //.
    - intros.
      apply H; trivial.
      have [?|/ltnW ?] := leqP y x.
      generalize eq_sym; intros.
      trivial.
      admit.
    - apply Gauss_dvd_l.
  Admitted.

  Lemma chinese_remainder m1 m2 x y :
    coprime m1 m2 ->
    (x == y %[mod m1 * m2]) = (x == y %[mod m1]) && (x == y %[mod m2]).
  Proof.
    intros.
    wlog le_yx : x y / y <= x; last by rewrite !eqn_mod_dvd // Gauss_dvd.
    by have [?|/ltnW ?] := leqP y x; last rewrite !(eq_sym (x %% _)); apply.
  Qed.
*)
  Lemma chinese_remainder_list_2 :
    forall (l1 l2 l : list (nat * nat)) (p : nat * nat),
      pairwise coprime (map snd l) ->
      l = l1 ++ (p::nil) ++ l2 ->
      chinese_list l == p.1 %[mod p.2].
  Proof.
    induction l1; intros.
    - simpl in H0.
      rewrite H0.
      rewrite H0 in H.
      by apply (chinese_remainder_list_l H).
    - pose (l3 := l1 ++ [:: p] ++ l2).
      assert (l = a :: l3).
      {
        admit.
      }
      rewrite H1.
      simpl.
      unfold l3.
      simpl.
      case_eq (l1 ++ p :: l2); intros.
      + generalize (app_cons_not_nil l2 l2 p); intros.
        admit.
      + rewrite -H2.
        assert (coprime a.2 (fold_left muln [seq i.2 | i <- p0 :: l0] 1)).
        {
          admit.
        }
        rewrite -H2 in H3.
        generalize (chinese_modr H3 a.1 (chinese_list (p0 :: l0))); intros.
        rewrite -H2 in H4.
        assert (pairwise coprime (map snd (p0 :: l0))).
        {
          admit.
        }
        generalize (chinese_remainder_list_l H5); intros.
        rewrite -H2 in H6.
        
        
(*      
      
    pose (m := fold_left muln (map snd l) 1).
    assert (pairwise coprime (map snd (p :: (l1 ++ l2)))).
    {
      admit.
    }
    assert (chinese_list (p :: (l1 ++ l2)) = chinese_list l %[mod m]).
    {
      admit.
    }
    generalize (chinese_remainder_list_l H1); intros.
    move => /eqP in H3.
    rewrite -H3.
    apply /eqP.
    symmetry.
    assert (m = p.2 * (fold_left muln (map snd (l1 ++ l2)) 1)).
    {
      admit.
    }
    rewrite H4 in H2.
    move => /eqP in H2.
    rewrite chinese_remainder in H2.
    apply /eqP.
    now move => /andP in H2.
*)    
    Admitted.
    
  Lemma chinese_remainder_list_permutation (l l2: list (nat * nat)) :
    pairwise coprime (map snd l) ->
    Permutation l l2 ->
    let m := fold_left muln (map snd l) 1 in
    chinese_list l == chinese_list l2 %[mod m].
  Proof.
    intros.
    assert (pairwise coprime (map snd l2)).
    {
      Search pairwise.
      admit.
    }
    simpl.
    Admitted.

  Lemma chinese_remainder_list  (l : list (nat * nat)) :
    pairwise coprime (map snd l) ->
    forall p,
      In p l ->
      chinese_list l == p.1 %[mod p.2].
  Proof.
    intros.
    assert (exists l1 l2,
               l = l1 ++ (p::nil) ++ l2).
    {
      admit.
    }
    destruct H1 as [l1 [l2 ?]].
    rewrite H1.
    generalize (chinese_remainder_list_2 H H1); intros.
    Admitted.

End chinese.
     
  

    
        