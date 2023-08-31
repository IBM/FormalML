Require Import Lia.
From mathcomp Require Import all_ssreflect zmodp poly ssralg cyclic fingroup finalg ring seq.

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

Require Import ssrbool.

Section chinese.

  (* pairs represent (residue, modulus) *)
  Fixpoint chinese_list (l : seq (nat * nat)) : nat :=
    match l with
    | nil => 0
    | a :: nil => a.1
    | a :: l' =>
        chinese (a.2) (\prod_(i <- (map snd l')) i)
          (a.1) (chinese_list l')
    end.

  Lemma all_coprime_prod (a : nat) (l : seq nat) :
    all (coprime a) l ->
    coprime a (\prod_(i <- l) i).
  Proof.
    intros.
    rewrite big_seq.
    apply big_rec.
    - apply coprimen1.
    - intros.
      move/allP/(_ _ H0): H.
      by rewrite coprimeMr H1 => ->.
  Qed.

  Lemma chinese_remainder_list_cons_l (a : nat * nat) (l : list (nat * nat)) :
    all (coprime a.2) (map snd l) ->
    chinese_list (a::l) == a.1 %[mod a.2].
  Proof.
    induction l=> //= HH.
    rewrite big_cons.
    destruct l; trivial.
    - rewrite chinese_modl //.
      rewrite big_nil muln1.
      by move/andP: HH => [-> _].
    - rewrite chinese_modl //.
      move/andP: HH => [HH1 HH2/=].
      by rewrite coprimeMr HH1 /= all_coprime_prod.
  Qed.

  Lemma pairwise_coprime_cons a l :
    pairwise coprime (a :: l) ->
    all (coprime a) l.
  Proof.
    simpl.
    move /andP.
    tauto.
  Qed.

  Lemma chinese_reminder_list_cons_r (a : nat * nat) (l : list (nat * nat)) :
    pairwise coprime (map snd (a::l)) ->
    let m := \prod_(i <- map snd l) i in 
    chinese_list (a::l) == chinese_list l %[mod m].
  Proof.
    intros.
    simpl.
    destruct l; trivial.
    - rewrite big_nil /= modn1 //.
    - rewrite chinese_modr //.
      apply all_coprime_prod.
      by apply pairwise_coprime_cons.
 Qed.

  Lemma mul_dvdn_l x d1 d2:
    d1 * d2 %| x -> d1 %| x.
   Proof.
     eapply dvdn_trans.
     apply dvdn_mulr.
     by apply dvdnn.
   Qed.

  Lemma mul_dvdn_r x d1 d2:
    d1 * d2 %| x -> d2 %| x.
  Proof.
    rewrite mulnC.
    by apply mul_dvdn_l.
  Qed.

  Lemma modn_muln x y b1 b2 :
    x == y %[mod b1 * b2] -> x == y %[mod b1].
  Proof.
    wlog le_yx : x y / y <= x; last by (rewrite !eqn_mod_dvd //; apply mul_dvdn_l).
    by have [?|/ltnW ?] := leqP y x; last rewrite !(eq_sym (x %% _)); apply.
  Qed.

(*
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
*)

  Lemma chinese_remainder_list_split :
    forall (l1 l2 l : list (nat * nat)) (p : nat * nat),
      pairwise coprime (map snd l) ->
      l = l1 ++ (p::nil) ++ l2 ->
      chinese_list l == p.1 %[mod p.2].
  Proof.
    induction l1; intros.
    - simpl in H0.
      rewrite H0.
      rewrite H0 in H.
      rewrite chinese_remainder_list_cons_l //.
      simpl in H.
      by move/andP: H => [-> _].
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
        have cp: coprime (a.2) (\prod_(i <- (map snd l3)) i).

        {
          rewrite all_coprime_prod //.
          subst l3.
          simpl in H.
          rewrite H0/= in H.
          by move/andP: H => [-> _].
        } 
        move/eqP: (chinese_modr cp (a.1) (chinese_list l3)).
        have ->: \prod_(i <- [seq i.2 | i <- l3]) i = \prod_(i <- [seq i.2 | i <- p::(l1++l2)]) i.
        {
          apply perm_big_AC.
          - apply mulnA.
          - apply mulnC.
          - subst l3.
            apply perm_map.
            by rewrite perm_catCA perm_refl.
        }
        simpl.
        rewrite big_cons.
        by apply modn_muln.
(*        
        rewrite chinese_remainder.
        * by move/andP => [-> _].
        * subst l3.
          rewrite (pairwise_perm_symm (l2:=[seq i.2 | i <- p :: (l1 ++ l2)]))/= in pc'.
          -- move/andP: pc' => [allcp _].
             by apply all_coprime_prod.
          -- move=> x y.
             by rewrite coprime_sym.
          -- by rewrite <- Permutation_middle.
*)
  Qed.

  Lemma chinese_remainder_list  (l : list (nat * nat)) :
    pairwise coprime (map snd l) ->
    forall p,
      p \in l ->
      chinese_list l == p.1 %[mod p.2].
  Proof.
    intros.
    case/splitPr: H0 H=>l1 l2 HH.
    by eapply chinese_remainder_list_split => //=.
  Qed.    

  Lemma chinese_remainder_list_unique (a b : nat) (l : list nat) :
    pairwise coprime l ->
    (forall p,
        p \in l -> a == b %[mod p]) ->
    a == b %[mod \prod_(i <- l) i].
  Proof.
    induction l; simpl; intros.
    - by rewrite big_nil !modn1.
    - move /andP in H.
      destruct H.
      rewrite big_cons chinese_remainder.
      + apply /andP.
        split.
        * apply H0.
          rewrite in_cons.
          apply /orP.
          by left.
        * apply IHl; trivial.
          intros.
          apply H0.
          rewrite in_cons.
          apply /orP.
          by right.
     + by apply all_coprime_prod.
  Qed.

  Lemma allrel_sym {A:eqType} f (l1 l2: seq A) :
    symmetric f ->
    allrel f l1 l2 = allrel f l2 l1.
  Proof.
    rewrite allrelC=>sym.
    apply eq_allrel => x y.
    by rewrite sym.
  Qed.

  Lemma pairwise_perm_sym {A:eqType} f (l1 l2: seq A) :
    symmetric f ->
    perm_eq l1 l2 ->
    pairwise f l1 = pairwise f l2.
  Proof.
    move=> symf.
    move: l1 l2.
    wlog pimp: / forall l1 l2, perm_eq l1 l2 -> pairwise f l1 -> pairwise f l2.
    - apply.
      apply catCA_perm_ind=> l1 l2 l3.
      rewrite !pairwise_cat !allrel_catr.
      move/andP=>[/andP-[rel12 rel13] /andP-[p1 /andP-[rel23 /andP-[p2 p3]]]].
      repeat (try (apply/andP; split)) => //.
      by rewrite allrel_sym.
    - move=> l1 l2 pm.
      apply Bool.eq_bool_prop_intro.
      split =>/Bool.Is_true_eq_true=> HH
         ; apply Bool.Is_true_eq_left
         ; eapply pimp; try apply HH.
      + by [].
      + by rewrite perm_sym.
  Qed.

  Lemma pairwise_coprime_perm l l2:
    perm_eq l l2 ->
    pairwise coprime l = pairwise coprime l2.
  Proof.
    intros.
    apply pairwise_perm_sym => // x y.
    apply coprime_sym.
  Qed.

  Lemma chinese_remainder_list_permutation (l l2: list (nat * nat)) :
    pairwise coprime (map snd l) ->
    perm_eq l l2 ->
    let m := \prod_(i <- map snd l) i in
    chinese_list l == chinese_list l2 %[mod m].
  Proof.
    intros co_l perm.
    apply chinese_remainder_list_unique; trivial.
    intros.
    assert (co_l2: pairwise coprime (map snd l2)).
    {
      rewrite (pairwise_coprime_perm (l2:=[seq i.2 | i <- l]))//.
      apply perm_map.
      by rewrite perm_sym.
    }
    move/mapP: H => [px ] in1 ->.
    rewrite (eqP (chinese_remainder_list co_l in1)).
    move: in1.
    rewrite (perm_mem perm)=> in2.
    by rewrite (eqP (chinese_remainder_list co_l2 in2)).
  Qed.

End chinese.
