Require Import Lia.
From mathcomp Require Import all_ssreflect zmodp poly ssralg cyclic fingroup finalg ring seq.
Require Import encode.

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

(* order of 3 mod 2^(n+2) = 2^n *)
(* show 3^(2^n) <> 1 mod 2^(n+3) *)

From mathcomp Require Import ssrnat.

Lemma n_n1_even j :
  exists k,
    j * (j + 1) = k.*2.
Proof.
  assert (~~ odd(j * (j + 1))).
  {
    replace (j+1) with (S j) by lia.
    rewrite oddM oddS.
    by case: (odd j).
  }
  apply even_halfK in H.
  exists ((j * (j + 1)) ./2).
  by rewrite H.
Qed.

Lemma modn_sub i j m :
  i >= j ->
  (i == j %[mod m]) = (i - j == 0 %[mod m]).
Proof.
  move/eqn_mod_dvd->.
  by rewrite mod0n.
Qed.

Lemma modn_sub_iff i j m :
  i >= j ->
  i = j %[mod m] <-> i - j = 0 %[mod m].
Proof.
  move/modn_sub=>eqq.
  split; move/eqP
  ; [rewrite eqq | rewrite -eqq]
  ; by move/eqP.
Qed.


Lemma subn_sqr_1 (x : nat) :
  x^2-1 = (x + 1) * (x - 1).
Proof.
  replace (x^2-1) with (x^2-1^2) by lia.
  by rewrite mulnC -subn_sqr.
Qed.

Lemma ord_odd_pow_2 j n :
  (2*j+1)^(2^n.+1) = 1 %[mod 2^(n.+3)].
Proof.
  induction n.
  - rewrite expn1 expnS expn1.
    replace ((2 * j + 1) * (2 * j + 1)) with (4*(j*(j+1)) + 1) by lia.
    destruct (n_n1_even j).
    rewrite H /=.
    replace (2^3) with 8 by lia.
    replace (4 * (x.*2)) with (8 * x) by lia.
    by rewrite -modnDm modnMr modnDmr.
  - rewrite expnS (mulnC _ (2^n.+1)) expnM (expnS _ n.+3).
    rewrite modn_sub_iff; [|lia].
    rewrite subn_sqr_1.
    rewrite modn_sub_iff in IHn; [|lia].
    assert (exists k,
               2 * k = ((2 * j + 1) ^ 2 ^ n.+1 + 1)).
    {
      assert (~~ odd  ((2 * j + 1) ^ 2 ^ n.+1 + 1)).
      {
        rewrite oddD oddX oddD.
        replace (2 *j) with (j.*2) by lia.
        rewrite odd_double /=.
        lia.
      }
      apply even_halfK in H.
      exists (((2 * j + 1) ^ 2 ^ n.+1 + 1)./2).
      rewrite -H.
      lia.
    }
    destruct H.
    rewrite -H -mulnA -muln_modr.
    replace 0 with (2*0) at 7 by lia.
    rewrite -muln_modr.
    f_equal.
    by rewrite -modnMm IHn modnMm muln0.
 Qed.

Lemma iotaSn0 m n : n != 0 ->
  iota m n = m :: iota m.+1 n.-1.
Proof.
  case: n => //=.
Qed.

Lemma index_iotaSn0 m n : m < n ->
  index_iota m n = m :: index_iota m.+1 n.
Proof.
  rewrite /index_iota=> mltn.
  rewrite iotaSn0; try lia.
  do 2 f_equal.
  lia.
Qed.


(*
Lemma add4_pow2_mod j n :
  (j + 4)^(2 ^n) = j^(2^n) + (2^n.+2)*j^(2^n-1) %[mod 2^n.+3].
Proof.
  rewrite (Pascal j 4 (2^n)) /=.
  move: (@big_mkord _ 0 addn (2 ^ n).+1 predT (fun i => 'C(2 ^ n, i) * (j ^ (2 ^ n - i) * 4 ^ i)))=> /= <-.
  rewrite index_iotaSn0 // big_cons.
  rewrite index_iotaSn0 ?big_cons; [| lia].
  rewrite expn0 expn1 muln1 subn0 bin0 bin1 mul1n addnA.
  rewrite (mulnC _ 4) mulnA.
  replace (2^n*4) with (2^n.+2) by (rewrite !expnS; lia).
  assert (\sum_(2 <= j0 < (2 ^ n).+1) 'C(2 ^ n, j0) * (j ^ (2 ^ n - j0) * 4 ^ j0) = 0 %[mod 2^n.+3]).
  {
    rewrite -modn_summ.
    rewrite (eqP (_ : \sum_( _ <= _ < _ ) _ == 0)) //.
    rewrite (big_nat_widenl _ 0) //.
    move: (@big_mkord _ 0 addn  (2 ^ n).+1 (fun i => (andb true (leq (S (S O)) i))) (fun i => ('C(2 ^ n, i) * (j ^ (2 ^ n - i) * 4 ^ i))
                                                               %% 2 ^ n.+3)) => /= ->.
    rewrite sum_nat_eq0.
    apply/forallP => x.
    apply/implyP => xbig.
    assert (('C(2 ^ n, x) * 4 ^ x) %% 2 ^ n.+3 == 0)%N.
    {
      admit.
    }
    by rewrite (mulnC _ (4 ^ x)) mulnA -modnMm (eqP H) mul0n mod0n.
  }
  by rewrite -modnDmr -modnDmr H !mod0n addn0.
  
Admitted.

Lemma ord_pow_2_odd j n :
  odd j ->
  j ^ (2^n) = 1 %[mod 2^n.+3] ->
  (j + 4)^(2^n) <> 1 %[mod 2^n.+3].
Proof.
  intros.
  rewrite add4_pow2_mod -modnDm H0 modnDm addnC modn_sub_iff; [|lia].
  replace (2 ^ n.+2 * j ^ (2 ^ n - 1) + 1 - 1) with
    (2 ^ n.+2 * j ^ (2 ^ n - 1)) by lia.
  rewrite (expnS _ n.+2) (mulnC 2 _).
  replace 0 with (2^n.+2 * 0) at 6 by lia.
  rewrite -!muln_modr mod0n muln0.
  apply /eqP.
  rewrite muln_eq0.
  apply /norP.
  split; [lia |].
  by rewrite modn2 oddX H orbT.
Qed.
*)

(* https://math.stackexchange.com/questions/459815/the-structure-of-the-group-mathbbz-2n-mathbbz *)


Lemma mod_mul_mul_0 a b m1 m2 :
  a == 0 %[mod m1] && (b == 0 %[mod m2]) ->
  a * b == 0 %[mod m1 * m2].
Proof.
  do 3 (rewrite eqn_mod_dvd; [|lia]).
  rewrite !subn0.
  move /andP=>[diva divb].
  by rewrite dvdn_mul.
Qed.

Lemma mod_mul_mul_0_alt a b m1 m2 :
  a = 0 %[mod m1] /\ (b = 0 %[mod m2]) ->
  a * b = 0 %[mod m1 * m2].
Proof.
  move=>[/eqP? /eqP?].
  by apply/eqP/mod_mul_mul_0/andP.
Qed.
 
Lemma mod_pow2_sqr_aux a b n :
  b <= a ->
  a = b %[mod 2^n.+1] ->
  a^2 = b^2 %[mod 2^n.+2].
Proof.
  intros.
  rewrite modn_sub_iff // in H0.
  rewrite modn_sub_iff.
  - rewrite subn_sqr.
    rewrite expnS mulnC.
    apply mod_mul_mul_0_alt.
    split; trivial.
    rewrite -modn_sub_iff // expnS in H0.
    lia.
  - by rewrite leq_sqr.
 Qed.

Lemma mod_pow2_sqr a b n :
  a = b %[mod 2^n.+1] ->
  a^2 = b^2 %[mod 2^n.+2].
Proof.
  case (boolP (b <= a)); intros.
  - by apply mod_pow2_sqr_aux.
  - symmetry.
    symmetry in H.
    apply mod_pow2_sqr_aux; lia.
 Qed.

  Lemma modn_muln (x y b1 b2:nat) :
    x == y %[mod b1 * b2] -> x == y %[mod b1].
  Proof.
    wlog le_yx : x y / y <= x; last by (rewrite !eqn_mod_dvd //; apply mul_dvdn_l).
    by have [?|/ltnW ?] := leqP y x; last rewrite !(eq_sym (x %% _)%N); apply.
  Qed.


Lemma ord_5_pow_2 n :
  5 ^ (2 ^ n) = 1 + 2^n.+2 %[mod 2^n.+3].
Proof.
  induction n.
  - lia.
  - rewrite expnS mulnC expnM.
    apply mod_pow2_sqr in IHn.
    rewrite IHn.
    generalize (expnD (1 + 2^n.+2) 1 1); intros.
    rewrite H !expn1.
    replace  ((1 + 2 ^ n.+2) * (1 + 2 ^ n.+2)) with
      (1 + 2 * (2^n.+2) + (2^n.+2)*(2^n.+2)) by lia.
    rewrite -expnD.
    assert (2^(n.+2 + n.+2) = 0 %[mod 2^n.+4]).
    {
      replace (n.+2 + n.+2) with ((2 * n).+4) by lia.
      rewrite !expnS -!muln_modr.
      replace (2^(2*n) %% 2^n) with 0.
      - rewrite muln0 mod0n //.
      - rewrite mulnC expnM.
        generalize (expnD (2 ^ n) 1 1); intros.
        by rewrite H0 !expn1 -modnMm modnn muln0 mod0n.
    }
    by rewrite -modnDm H0 mod0n addn0 modn_mod (expnS _ (n.+2)).
 Qed.

Lemma ord_5_pow_2_neq n :
  5^(2^n) <> 1 %[mod 2^n.+3].
Proof.
  rewrite ord_5_pow_2.
  rewrite modn_sub_iff; try lia.
  replace (1 + 2 ^ n.+2 - 1) with (2^n.+2) by lia.
  rewrite !modn_small; try lia.
  rewrite (expnS _ (n.+2)).
  lia.
Qed.

Lemma ord_pow_gcd b e1 e2 n :
  b^e1 = 1 %[mod n] ->
  b^e2 = 1 %[mod n] ->
  b^(gcdn e1 e2) = 1 %[mod n].
Proof.
  Search gcdn.
  Admitted.

Lemma ord_5_pow_2_neq_m1 n :
  not (exists k,
        5^k = 2^n.+3-1 %[mod 2^n.+3]).
Proof.
  unfold not; intros.
  destruct H.
  assert ((5 ^ x)^2 = 1 %[mod 2^n.+3]).
  {
    rewrite modn_sub_iff.
    - rewrite subn_sqr_1.
      rewrite -modnMm -(modnDm (5^x) _) H modnDm.
      replace (2^n.+3-1+1) with (2^n.+3) by lia.
      by rewrite modnn mul0n mod0n.
    - rewrite sqrn_gt0.
      rewrite expn_gt0.
      lia.
  }
  generalize (ord_5_pow_2 n); intros.
  generalize (ord_odd_pow_2 2 n); intros.
  replace (2 * 2 + 1) with 5 in H2 by lia.
  rewrite -expnM in H0.
  generalize (ord_pow_gcd H2 H0); intros.
  assert (x = 2^n).
  {
    admit.
  }
  rewrite H4 in H.
  rewrite H1 in H.
  clear H1 H2 H0 H3 H4.
  rewrite modn_small in H; [|rewrite !expnS; lia].
  rewrite modn_small in H; [|rewrite !expnS; lia].
  rewrite !expnS in H; lia.
 Admitted.           

  Lemma pow_3_5_pow_2 n :
    3^(2^n.+1) = 5^(2^n.+1) %[mod 2^n.+4].
  Proof.
  induction n.
  - lia.
  - symmetry.
    rewrite modn_sub_iff; [|rewrite leq_exp2r; lia].
    rewrite expnS !(mulnC 2 _) !expnM subn_sqr.
    symmetry in IHn.
    rewrite modn_sub_iff in IHn; [|rewrite leq_exp2r; lia].
    rewrite (expnS _ n.+4) (mulnC 2 _).
    rewrite mod_mul_mul_0_alt; trivial.
    split; trivial.
    rewrite modn2 mod0n oddD !oddX.
    lia.
  Qed.

  Lemma ord_3_pow_2_neq n :
    3^(2^n) <> 1 %[mod 2^n.+3].
  Proof.
    destruct n.
    - lia.
    - rewrite pow_3_5_pow_2.
      apply ord_5_pow_2_neq.
  Qed.

