Require Import LibUtilsListAdd ListAdd Permutation.
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

  Lemma symmetricE {A} (f:A->A->bool) :  (ssrbool.symmetric f) <-> (RelationClasses.Symmetric f).
  Proof.
    rewrite /symmetric /RelationClasses.Symmetric.
    split; intros.
    - by rewrite H.
    - case_eq (f x y)=> eqq.
      + by rewrite H.
      + case_eq (f y x)=> eqq2//.
        by rewrite (H _ _ eqq2) in eqq.
  Qed.

  Lemma allE {A} (P:pred A) (l:list A) : all P l <->  Forall (fun x : A => P x) l.
  Proof.
    elim: l => /=.
    - split=>// _.
    - move=> a l IHl.
      split.
      + move/andP=> [ap pairP].
        constructor; tauto.
      + inversion 1; subst.
        by rewrite H2 IHl.
  Qed.    

  Lemma pairwiseE {A} (P:rel A) (l:list A) : pairwise P l <-> ForallOrdPairs P l.
  Proof.
    elim: l => /=.
    - split=>// _.
      constructor.
    - move=> a l IHl.
      split.
      + move/andP=> [ap pairP].
        constructor;[| tauto].
        by apply allE.
      + inversion 1; subst.
        apply/andP; split.
        * by apply allE.
        * by apply IHl.
  Qed.
    
  Lemma pairwise_perm_symm {A} f (l1 l2: list A) :
    symmetric f ->
    Permutation l1 l2 ->
    pairwise f l1 = pairwise f l2.
  Proof.
    intros.
    apply symmetricE in H.
    apply Bool.eq_true_iff_eq.
    split; intros HH; apply pairwiseE; apply pairwiseE in HH.
    - by rewrite ForallOrdPairs_perm; [| apply Permutation_sym; apply H0].
    - by rewrite ForallOrdPairs_perm; [| apply H0].
  Qed.

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
      have ->/=: l = a :: l3 by by rewrite H0.
      case_eq l3.
      + subst l3; destruct l1; simpl; congruence.
      + move=> _ _ <-.
        have pc': pairwise coprime [seq i.2 | i <- l3].
        {
          rewrite H0/= in H.
          by move/andP: H => [_ ->].
        }
        specialize (IHl1 l2 l3 p pc' (Logic.eq_refl _)).
        rewrite <- (eqP IHl1).
        have cp: coprime (a.2) (fold_left muln [seq i.2 | i <- l3] 1).
        {
          admit.
        } 
        move/eqP: (chinese_modr cp (a.1) (chinese_list l3)).
        have ->: fold_left muln [seq i.2 | i <- l3] 1 = fold_right muln 1 [seq i.2 | i <- (p::(l1++l2))].
        {
          rewrite fold_symmetric.
          - apply fold_right_perm.
            + apply mulnA.
            + apply mulnC.
            + apply Permutation_map.
              by rewrite Permutation_middle.
          - apply mulnA.
          - apply mulnC.
        }

        simpl.
        rewrite chinese_remainder.
        * by move/andP => [-> _].
        * subst l3.
          rewrite (pairwise_perm_symm (l2:=[seq i.2 | i <- p :: (l1 ++ l2)]))/= in pc'.
          -- move/andP: pc' => [allcp _].
             admit.
          -- move=> x y.
             by rewrite coprime_sym.
          -- by rewrite <- Permutation_middle.
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
      p \in l ->
      chinese_list l == p.1 %[mod p.2].
  Proof.
    intros.
    case/splitPr: H0 H=>l1 l2 HH.
    by eapply chinese_remainder_list_2 => //=.
  Qed.    

End chinese.
