Require Import Lia.
From mathcomp Require Import all_ssreflect zmodp poly ssralg cyclic fingroup finalg ring seq bigop.
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
  move=> p_prime.
  move: (p_prime) => /(prime_gt0).
  destruct q; [| destruct q].
  - by rewrite ltnn.
  - by inversion p_prime.
  - by rewrite ltn0Sn.
Qed.

   Lemma Fp_exp_expn (x : 'F_p) (n : nat):
     prime p ->
     nat_of_ord (x ^+ n)%R = x ^ n %% p.
   Proof.
     move=> p_prime.
     have peqq := (Fp_cast p_prime).
     induction n.
     - by rewrite /= {1}peqq expn0.
     - rewrite expnS exprS /mul /= IHn -modnMm.
       rewrite {2 4 5}peqq.
       by rewrite -(modnMm x _) modn_mod.
   Qed.

  Lemma zp_prim_root_max :
    prime p ->
    { w : 'F_p | (p.-1).-primitive_root w}.
  Proof.
    move=> p_prime.
    have pbig := (prime_pbig2 p_prime).
    have/(nth_find 0)-HH: has (p.-1).-primitive_root [seq x <- enum 'F_p | x != Zp0].
    {
      apply (@has_prim_root _ _ [seq x <- enum 'F_p | x != Zp0]) => //=.
      - rewrite all_filter.
        apply/allP => /= x xin.
        apply/implyP=> xn0.
        rewrite unity_rootE.
        have/(fermat_little_pred p_prime)-eqq: ~ p %| x.
        {
          have xltp: x < p.
          {
            move: (ltn_ord x).
            by rewrite {2}(Fp_cast p_prime).
          }
          have xpos: (0 < x) by by rewrite lt0n.
          move/(dvdn_leq xpos); lia.
        }
        apply /eqP.
        apply val_inj => /=.
        by rewrite {2}(Fp_cast p_prime) -eqq Fp_exp_expn.
      - apply filter_uniq.
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

Lemma inZp_add j k n :
  inZp (j + k) = inZp j + inZp k :> 'Z_n.
Proof.
  apply: val_inj => /=.
  by rewrite modnDm.
Qed.

Lemma inZp_mul j k n :
  inZp (j * k) = inZp j * inZp k :> 'Z_n.
Proof.
  apply: val_inj => /=.
  by rewrite modnMm.
Qed.

Lemma inZp_exp j k n :
  inZp (j ^ k) = inZp j ^+ k :> 'Z_n.
Proof.
  induction k.
  - rewrite expn0 expr0.
    by apply: val_inj => /=.
  - rewrite exprS expnS -IHk.
    apply inZp_mul.
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
+    rewrite big_seq.
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

  Lemma allE {A} (P:pred A) (l:list A) : all P l <->  List.Forall (fun x : A => P x) l.
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

  Lemma pairwiseE {A} (P:rel A) (l:list A) : pairwise P l <-> List.ForallOrdPairs P l.
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

  Definition balanced_chinese_list (l : seq (nat * nat)) :=
    \sum_(p <- l)
      (\prod_(q <- l | q != p) q.2) *
      ((p.1 * (egcdn (\prod_(q <- l | q!= p) q.2) p.2).1) %% p.2).

  Lemma egcd_coprime (a b : nat) :
    0 < a ->
    coprime a b ->
    (egcdn a b).1 * a = 1 %[mod b].
  Proof.
    intros.
    case: egcdnP => //= km kn ->.
    by rewrite (eqP H0) -modnDm modnMl add0n modn_mod.
  Qed.

  Lemma egcd_coprime_mult (a b c : nat) :
    0 < a ->
    0 < b ->
    coprime a b ->
    c * (egcdn a b).1 * a = c %[mod b].
  Proof.
    intros.
    rewrite -mulnA -modnMmr egcd_coprime //.
    rewrite modnS mod0n dvdn1.
    case: eqVneq => [-> |].
    - by rewrite muln0 !modn1.
    - by rewrite muln1.
  Qed.

  Lemma sym_pairwiseP {T : Type} (r : T -> T -> bool) (sym:symmetric r) (x0 : T) (xs : seq T) :
    reflect {in gtn (size xs) &, {homo nth x0 xs : i j / i <> j >-> r i j}} (pairwise r xs).
  Proof.
    induction xs; simpl; first by apply (iffP idP).
    apply: (iffP andP).
    - intros [??]?????.
      destruct x; destruct y; simpl.
      + lia.
      + move/(all_nthP x0): H.
        apply.
        rewrite/in_mem/mem/= in H2.
        lia.
      + rewrite sym.
        move/(all_nthP x0): H.
        apply.
        rewrite/in_mem/mem/= in H1.
        lia.
      + rewrite H0 in IHxs.
        inversion IHxs.
        apply H4; trivial.
        lia.
    - intros ?.
      split.
      + apply/(all_nthP x0)=> i ilt.
        move: (H 0 i.+1) => /=.
        apply; rewrite /in_mem/mem/=; lia.
      + inversion IHxs => //.
        elim H1 => x y xlt ylt xny.
        move: (H x.+1 y.+1).
        unfold in_mem, mem in *; simpl in *.
        apply; lia.
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

  Lemma prodn_filter1 [I : Type] (r : seq I) (F : I -> nat) :
    \prod_(i <- r | F i != 1) F i = \prod_(i <- r) F i.
  Proof.
    induction r.
    - by rewrite !big_nil.
    - rewrite !big_cons -IHr.
      case: eqVneq => /= [->|//].
      lia.
  Qed.
      
  Lemma balanced_chinese_list_mod_1 (l : seq (nat * nat)) :
    (forall p, p \in l -> 0 < p.2) ->
    pairwise coprime (map snd l) ->
    forall p,
      p \in l ->
            \prod_(q <- l | q != p) q.2 * ((p.1 * (egcdn (\prod_(q <- l | q != p) q.2) p.2).1) %% p.2) == p.1 %[mod p.2].
  Proof.
    intros.
    apply /eqP.
    rewrite modnMmr mulnC.
    apply egcd_coprime_mult; trivial.
    - rewrite big_seq_cond.
      apply prodn_cond_gt0 => i.
      move/andP => [iinl _].
      by apply H.
    - by apply H.
    - rewrite (perm_big_AC _ _ _ (r2:=p :: rem p l)).
      + case: (eqVneq p.2 1) => [->|neq].
        {
          by rewrite coprimen1.
        }
        rewrite -big_filter /= eqxx /=.
        rewrite (_ : (\prod_(i <- [seq i <- rem p l | i != p]) i.2) = (\prod_(i <- (map snd [seq x <- rem p l | x.2 != 1]) | (i != p.2)) i)).
        * rewrite coprime_sym -big_filter.
          apply all_coprime_prod.
          apply pairwise_coprime_cons.
          rewrite (pairwise_perm_sym coprime_sym (perm_map snd (perm_to_rem H1))) in H0.
          revert H0.
          apply subseq_pairwise.
          rewrite /= eqxx.
          rewrite filter_map.
          apply map_subseq.
          eapply subseq_trans.
          -- apply filter_subseq.
          -- apply filter_subseq.
        * rewrite big_map.
          transitivity (\prod_(i <- [seq i <- rem p l | i != p] | i.2 != 1) i.2)
          ; [by rewrite prodn_filter1 |].
          rewrite -big_filter.
          symmetry; rewrite -big_filter.
          rewrite -!filter_predI /predI.
          f_equal.
          apply eq_in_filter => x xin /=.
          case: (eqVneq x.2 1) => /=; [by rewrite Bool.andb_false_r |intros ne1].
          case: (eqVneq x p).
          { move => ->.
            by rewrite eqxx.
          }
          case: (eqVneq x.2 p.2) => //= eqq2.
          rewrite /eq_op/= eqq2 eqxx Bool.andb_true_r => eqq1.
          move: H0.
          rewrite (pairwise_perm_sym coprime_sym (perm_map snd (perm_to_rem H1))) /=.
          move/andP=> [].
          have x2in:  x.2 \in [seq i.2 | i <- rem p l] by apply map_f.
          move/allP/(_ x.2 x2in).
          rewrite eqq2 /coprime gcdnn -eqq2 => eqq3.
          by rewrite eqq3/= in ne1.
      + by apply mulnA.
      + by apply mulnC.
      + by apply perm_to_rem.
  Qed.

  Lemma prod_split1 (l : seq (nat * nat)) (p : nat*nat) :
    uniq l ->
    p \in l -> 
    \prod_(q<-l) q.2 = p.2 * \prod_(q <- l | q != p) q.2.
  Proof.  
    intros.
    rewrite (big_rem_AC mulnA mulnC _ (z := p)) //.
    f_equal.
    rewrite -big_filter.
    symmetry; rewrite -big_filter.
    replace  [seq _ <- rem p l | true] with [seq i <- l | i != p]; trivial.
    rewrite rem_filter // filter_predT.
    apply eq_filter.
    intros ?.
    by rewrite /predC1 /=.
  Qed.

  Lemma muln_lt (a b c : nat) :
    0 < c ->
    a < b ->
    a * c < b * c.
  Proof.
    intros.
    by rewrite ltn_pmul2r.
  Qed.

  Lemma balanced_chinese_list_mod_1_lt (l : seq (nat * nat)) :
    uniq l ->
    (forall p, p \in l -> 0 < p.2) ->
    forall p,
      p \in l ->
            \prod_(q <- l | q != p) q.2 * ((p.1 * (egcdn (\prod_(q <- l | q != p) q.2) p.2).1) %% p.2) < \prod_(q <- l) q.2.
  Proof.
    intros.
    rewrite (prod_split1 H H1) mulnC.
    apply muln_lt.
    - rewrite big_seq_cond.
      apply prodn_cond_gt0 => i.
      intros.
      apply H0.
      move /andP in H2.
      tauto.
    - apply ltn_pmod.
      by apply H0.
  Qed.

  Lemma modn_add0 (m a b : nat) :
    b == 0 %[mod m] ->
    a %% m + b == a %[mod m].
  Proof.
    intros.
    move /eqP in H.
    rewrite modnDml -modnDm H mod0n addn0 modn_mod //.
  Qed.

  Lemma modn_mull0 (m a b : nat) :
    a %% m = 0 ->
    (a * b) %% m = 0.
  Proof.
    intros.
    rewrite -(mod0n m) -modnMml H mul0n //.
  Qed.

  Lemma balanced_chinese_list_mod (l : seq (nat * nat)) :
    (forall p, p \in l -> 1 < p.2) ->
    pairwise coprime (map snd l) ->
    forall p,
      p \in l ->
      balanced_chinese_list l == p.1 %[mod p.2].
  Proof.
    intros.
    rewrite -modn_summ (bigD1_seq p) /= //.
    - have posl: (forall p, p \in l -> 0 < p.2).
      {
        intros ??.
        apply H in H2.
        lia.
      }
      rewrite (eqP (balanced_chinese_list_mod_1 posl H0 H1)).
      apply modn_add0.
      rewrite big1_idem //.
      intros.
      apply modn_mull0.
      rewrite -big_filter.
      rewrite (perm_big_AC _ _ _ (r2:=p :: rem p [seq i0 <- l | i0 != i])).
      + by rewrite big_cons modnMr.
      + by apply mulnA.
      + by apply mulnC.
      + apply perm_to_rem.
        by rewrite mem_filter H1 eq_sym H2.
    - rewrite uniq_pairwise.
      have: (pairwise (fun x y => coprime x.2 y.2 && (1<x.2)) l).
      {
        rewrite pairwise_relI.
        apply /andP.
        split.
        - rewrite pairwise_map in H0.
          apply H0.
        - apply/(pairwiseP (0,0)) => x y xlt ylt xlty.
          apply H.
          by apply mem_nth.
      }
      apply sub_pairwise.
      intros ???.
      simpl.
      assert (x = y -> false).
      {
        intros.
        destruct x; destruct y.
        simpl in H2.
        inversion H3.
        rewrite H6 in H2.
        move /andP in H2; destruct H2.
        rewrite /coprime gcdnn in H2.
        move /eqP in H2.
        lia.
      }
      by apply (contra_not_neq H3).
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

  Definition Zp_reduce_r (p q : nat) (a : 'Z_(p*q)) : 'Z_q := inZp a.
  Definition Zp_reduce_l (p q : nat) (a : 'Z_(p*q)) : 'Z_p := inZp a.  
  Definition Zp_reduce_pair (p q : nat) (a : 'Z_(p*q)) := (Zp_reduce_l a,
                                                            Zp_reduce_r a).

  Lemma modn_plus_const x a b m :
    a = b %[mod m] ->
    x + a = x + b %[mod m].
  Proof.
    intros.
    by rewrite -modnDm H modnDm.
  Qed.

  Lemma Zp_reduce_r_is_morphism (p q : nat) :
    1 < p ->
    1 < q ->    
    rmorphism (@Zp_reduce_r p q).
  Proof.
    intros.
    assert (1 < p*q) by lia.
    assert ((Zp_trunc q).+2 %| (Zp_trunc (p * q)).+2).
    {
      rewrite !Zp_cast //.
      apply dvdn_mull.
      apply dvdnn.
    }
    constructor.
    - intros ??.
      apply val_inj; simpl.
      rewrite modnDm modn_dvdm //.
      apply (@modn_plus_const x (((Zp_trunc (p * q)).+2 - y) %% (Zp_trunc (p * q)).+2)
               ((Zp_trunc q).+2 - y %% (Zp_trunc q).+2) (Zp_trunc q).+2).
      rewrite modn_dvdm //.
      destruct y.
      simpl.
      rewrite !Zp_cast //.
      rewrite Zp_cast // in i.
      clear H2 x.
      rewrite modnB; try lia.
      rewrite modnMl.
      case (boolP (0 < m %% q)); intros; simpl.
      + rewrite mul1n addn0.
        assert (q - m%%q < q) by lia.
        rewrite (modn_small H2) //.
      + rewrite mul0n addn0.
        assert (m%%q = 0) by lia.
        rewrite H2 !subn0 modnn //.
    - constructor.
      + intros ??.
        apply val_inj; simpl.
        rewrite modnMm modn_dvdm // !Zp_cast //.
      + apply val_inj; simpl.
        rewrite modn_dvdm // !Zp_cast //.
  Qed.

  Lemma Zp_reduce_l_is_morphism (p q : nat) :
    1 < p ->
    1 < q ->    
    rmorphism (@Zp_reduce_l p q).
  Proof.
    intros.
    rewrite /Zp_reduce_l mulnC.
    by apply Zp_reduce_r_is_morphism.
  Qed.

  Lemma Zp_reduce_pair_is_morphism (p q : nat) :
    1 < p ->
    1 < q ->    
    rmorphism (@Zp_reduce_pair p q).
  Proof.
    intros.
    destruct (@Zp_reduce_l_is_morphism p q H H0) as [? [? ?]].
    destruct (@Zp_reduce_r_is_morphism p q H H0) as [? [? ?]].
    constructor.
    - intros ??.
      rewrite /Zp_reduce_pair base base0 //.
    - constructor.
      + intros ??.
        rewrite /Zp_reduce_pair m m0 //.
      + rewrite /Zp_reduce_pair e e0 //.
  Qed.      

  Definition Zp_lift_pair (p q : nat) (r : 'Z_p * 'Z_q) : 'Z_(p*q) :=
    inZp (chinese p q r.1 r.2).

  Lemma modn_muln_l x p q :
    (x %% (p * q)) %% p = x %% p.
  Proof.
    symmetry.
    apply /eqP.
    have HH: (x %% (p * q) <= x) by apply leq_mod.
    rewrite eqn_mod_dvd //.
    apply mul_dvdn_l with (d2 := q).
    by rewrite -(eqn_mod_dvd (p * q)) // modn_mod.
  Qed.

  Lemma modn_muln_r x p q :
    (x %% (p * q)) %% q = x %% q.
  Proof.
    by rewrite mulnC modn_muln_l.
  Qed.

  Lemma Zp_lift_pair_is_morphism (p q : nat) :
    1 < p ->
    1 < q ->
    coprime p q ->
    rmorphism (@Zp_lift_pair p q).
  Proof.
    intros.
    assert (1 < p*q) by lia.
    generalize (chinese_remainder H1); intros.
    generalize (chinese_modl H1); intros.
    generalize (chinese_modr H1); intros.    
    constructor.
    - intros ??.
      unfold Zp_lift_pair.
      rewrite -inZp_add.
      apply val_inj.
      destruct x, y.
      destruct s, s0, s1, s2.
      rewrite /= !Zp_cast //.
      apply /eqP.
      rewrite H3.
      apply /andP.
      split; apply /eqP.
      + rewrite H4.
        symmetry.
        rewrite -modnDm H4 modnB; [|lia|lia].
        rewrite modn_muln_l modnMr addn0.
        case (boolP (0 < (chinese p q m1 m2 %% p))); simpl; intros.
        * rewrite mul1n H4.
          symmetry.
          rewrite -modnDm !modn_mod.
          apply modn_plus_const.
          rewrite Zp_cast in i1; [|lia].
          rewrite modnB; [|lia|lia].
          rewrite modnn (modn_small i1) addn0.
          case (boolP (0 < m1)); simpl; intros.
          -- by rewrite mul1n.
          -- assert (m1 = 0) by lia.
             by rewrite H6 mul0n !subn0 modnn mod0n.
        * assert (chinese p q m1 m2 %% p = 0) by lia.
          rewrite mul0n H4.
          symmetry.
          rewrite -modnDm !modn_mod.
          apply modn_plus_const.
          rewrite Zp_cast in i1; [|lia].
          rewrite modnB; [|lia|lia].
          rewrite modnn (modn_small i1) addn0.
          case (boolP (0 < m1)); simpl; intros.
          -- rewrite mul1n.
             rewrite H4 (modn_small i1) in H6.
             lia.
          -- by rewrite mul0n.
      + rewrite H5.
        symmetry.
        rewrite -modnDm H5 modnB; [|lia|lia].
        rewrite modn_muln_r modnMl addn0.
        case (boolP (0 < (chinese p q m1 m2 %% q))); simpl; intros.
        * rewrite mul1n H5.
          symmetry.
          rewrite -modnDm !modn_mod.
          apply modn_plus_const.
          rewrite Zp_cast in i2; [|lia].
          rewrite modnB; [|lia|lia].
          rewrite modnn (modn_small i2) addn0.
          case (boolP (0 < m2)); simpl; intros.
          -- by rewrite mul1n.
          -- assert (m2 = 0) by lia.
             by rewrite H6 mul0n !subn0 modnn mod0n.
        * assert (chinese p q m1 m2 %% q = 0) by lia.
          rewrite mul0n H5.
          symmetry.
          rewrite -modnDm !modn_mod.
          apply modn_plus_const.
          rewrite Zp_cast in i2; [|lia].
          rewrite modnB; [|lia|lia].
          rewrite modnn (modn_small i2) addn0.
          case (boolP (0 < m2)); simpl; intros.
          -- rewrite mul1n.
             rewrite H5 (modn_small i2) in H6.
             lia.
          -- by rewrite mul0n.
    - constructor.
      + intros ??.
        unfold Zp_lift_pair.
        rewrite -inZp_mul.
        apply val_inj.
        destruct x, y.
        destruct s, s0, s1, s2.
        rewrite /= !Zp_cast //.
        apply /eqP.
        rewrite H3.
        apply /andP.
        split; apply /eqP; symmetry.
        * by rewrite -modnMm !H4 /= modnMm modn_mod.
        * by rewrite -modnMm !H5 /= modnMm modn_mod.
      + unfold Zp_lift_pair.
        apply val_inj.
        rewrite /= !Zp_cast //.
        apply /eqP.
        rewrite H3.
        apply /andP.
        split; apply /eqP.
        * rewrite H4 !modn_small //.
        * rewrite H5 !modn_small //.          
 Qed.

  Lemma right_inv_chinese (p q : nat) :
    1 < p ->
    1 < q ->
    coprime p q ->
    cancel (@Zp_lift_pair p q) (@Zp_reduce_pair p q).
  Proof.
    intros.
    unfold cancel.
    intros.
    unfold Zp_reduce_pair, Zp_lift_pair.
    destruct x.
    simpl.
    unfold Zp_reduce_l, Zp_reduce_r.
    generalize (chinese_remainder H1); intros.
    generalize (chinese_modl H1); intros.
    generalize (chinese_modr H1); intros.
    assert (1 < p * q) by lia.
    destruct o, o0.
    f_equal.
    - apply val_inj.
      rewrite /= !Zp_cast //.
      rewrite Zp_cast // in i.
      rewrite modn_muln_l H3.
      by rewrite (modn_small i).
    - apply val_inj.
      rewrite /= !Zp_cast //.
      rewrite Zp_cast // in i0.
      rewrite modn_muln_r H4.
      by rewrite (modn_small i0).
  Qed.

  Lemma left_inv_chinese (p q : nat) :
    1 < p ->
    1 < q ->
    coprime p q ->
    cancel (@Zp_reduce_pair p q) (@Zp_lift_pair p q).
  Proof.
    intros.
    unfold cancel.
    intros.
    unfold Zp_reduce_pair, Zp_lift_pair.
    destruct x.
    unfold Zp_reduce_l, Zp_reduce_r.
    generalize (chinese_remainder H1); intros.
    generalize (chinese_modl H1); intros.
    generalize (chinese_modr H1); intros.
    assert (1 < p * q) by lia.
    apply val_inj.
    simpl.
    rewrite !Zp_cast //.
    rewrite Zp_cast // in i.
    replace m with (m %% (p * q)) at 3.
    - apply /eqP.
      rewrite H2.
      apply /andP.
      split.
      + apply /eqP.
        by rewrite H3 modn_mod.
      + apply /eqP.
        by rewrite H4 modn_mod.
    - by rewrite (modn_small i).
  Qed.

  Lemma bijective_reduce_pair (p q : nat) 
              (pbig: 1 < p)
              (qbig: 1 < q)
              (cop: coprime p q) :
    bijective (@Zp_reduce_pair p q).
  Proof.
    eapply Bijective.
    - by apply left_inv_chinese.
    - by apply right_inv_chinese.
  Qed.
    
  Lemma bijective_lift_pair (p q : nat) 
              (pbig: 1 < p)
              (qbig: 1 < q)
              (cop: coprime p q) :
    bijective (@Zp_lift_pair p q).
  Proof.
    eapply Bijective.
    - by apply right_inv_chinese.
    - by apply left_inv_chinese.
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

Lemma ord_odd_pow_2' j n :
  odd j ->
  j^(2^n.+1) = 1 %[mod 2^(n.+3)].
Proof.
  intros.
  generalize (ord_odd_pow_2 (j./2) n); intros.
  generalize (odd_double_half j); intros.
  replace (2 * j./2) with (j./2.*2) in H0 by lia.
  rewrite H /= addnC in H1.
  by rewrite -H1.
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
    assert (forall k, k < n -> ('C(2 ^ n, 2^k.+1) * 4 ^ 2^k.+1) %% 2 ^ n.+3 == 0)%N.    
    {
      intros.
      assert (exists q, 'C(2^n, 2^k.+1) = q * 2^(n-k.+1)).
      {
        admit.
      }
      destruct H0.
      rewrite H0.
      replace 4 with (2^2) by lia.
      rewrite -expnM -expnS.
      replace (x0 * 2 ^ (n - k.+1) * 2 ^ 2 ^ k.+2) with
        (x0 * 2^ (n - k.+1 + (2^k.+2))).
      - assert (2^k.+2 >= k.+4).
        {
          clear H H0.
          induction k; trivial.
          assert (k.+4 < 2*2^k.+2) by lia.
          by rewrite expnS.
        }
        rewrite -modnMm.
        assert (exists q,  (2 ^ (n - k.+1 + 2 ^ k.+2) = q * 2^n.+3)).
        {
          admit.
        }
        destruct H2.
        by rewrite H2 modnMl muln0 mod0n.
      - by rewrite -mulnA expnD.
    }
    assert (('C(2 ^ n, x) * 4 ^ x) %% 2 ^ n.+3 == 0)%N.
    {
      (* 2^(n-1) | 'C(2^n, 2), ok for x = 2 *)
      (* 2^n | 'C(2^n,3), ok for x = 3 *)
      (* 2^(n-2) | 'C(2^n, 4), ok for x = 4 *)
      (* enough to prove for x = 2^k, since sucessive values are better *)
      admit.
    }
    by rewrite (mulnC _ (4 ^ x)) mulnA -modnMm (eqP H0) mul0n mod0n.
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

Lemma add_exp_mod_p a b p :
  prime p ->
  (a + b)^p = a^p + b^p %[mod p].
Proof.
  move=> pprime.
  rewrite expnDn.
  move: (prime_gt0 pprime).
  case: p pprime; [lia |]=> p pprime _.
  rewrite big_ord_recr big_ord_recl /=.
  rewrite bin0 binn subn0 subnn !expn0 !mul1n muln1.
  rewrite addnC addnA.
  rewrite -modnDmr -modn_summ.
  suff/eqP->:  \sum_(i < p) (('C(p.+1, bump 0 i) * (a ^ (p.+1 - bump 0 i) * b ^ bump 0 i)) %% p.+1) == 0
    by rewrite mod0n addn0 addnC.
  rewrite sum_nat_eq0.
  apply/forallP=> k.
  apply/implyP=> _.
  rewrite -modnMml (eqP (_ : 'C(p.+1, bump 0 k) == 0 %[mod p.+1])).
  - by rewrite mod0n. 
  - rewrite (eqn_mod_dvd p.+1) // subn0 prime_dvd_bin //.
    rewrite /bump.
    destruct k; simpl; lia.
Qed.

Lemma iffbP {x y : bool}: reflect (x <-> y) (x == y).
Proof.
  case: x y; case
  ; rewrite eqE /= /eqb /=
  ; constructor
  ; firstorder.
Qed.

Lemma iffEq {x y : bool}: (x <-> y) <-> (x = y).
Proof.
  case: x y; case; firstorder.
  symmetry; firstorder.
Qed.

Lemma prime_pow_dvd_aux k p n:
  k <= p^n ->
  forall j,
    j <= n ->
    (p ^ j %| k) = (p^j %| (p^n - k)).
Proof.
  intros kle j jlt.
  assert (p^j %| p^n).
  {
    by apply dvdn_exp2l.
  }
  apply iffEq.
  split; intros.
  - rewrite dvdn_sub //.
  - by rewrite -(dvdn_subr (m := p^n)).
Qed.

Lemma prime_pow_dvd j k p n  :
  prime p ->
  ~~ (p %| j) ->
  p^n.+1 %| j * k ->
  p^n.+1 %| k.
Proof.
  move=> pprime pndivj.
  induction n.
  - rewrite !expn1 Euclid_dvdM //.
    case/orP => // eqq1.
    by rewrite eqq1 in pndivj.
  - intros.
    assert (p^n.+1 %| j * k).
    {
      rewrite expnS in H.
      by apply mul_dvdn_r in H.
    }
    generalize (divnK (IHn H0)); intros.
    clear IHn H0.
    rewrite -H1 expnS dvdn_pmul2r.
    + rewrite -H1 mulnA expnS dvdn_pmul2r in H.
      * rewrite Euclid_dvdM // in H.
        move /orP in H.
        destruct H; trivial.
        by move /negP in pndivj.
      * apply prime_gt1 in pprime; lia.
    + apply prime_gt1 in pprime; lia.
 Qed.
  

Lemma expn_boundr a b c :
  1 < a ->
  a ^ b <= c ->
  b <= c.
Proof.
  move=> abig able.
  rewrite -(@leq_exp2l a) // (leq_trans able) //.
  by rewrite ltnW // ltn_expl.
Qed.

Lemma max_prime_pow_dvd j p :
  1 < p ->
  0 < j ->
  {k | (p^k %| j) && ~~ (p^k.+1 %| j)}.
Proof.
  move=> pbig jnneg.
  have exP: exists i : nat, [pred k | p ^ k %| j] i.
  {
    exists 0.
    by rewrite /= expn0 dvd1n.
  }

  have bounded: forall i : nat, [pred k | p ^ k %| j] i -> i <= j.
  {
    move=> i /=.
    move/(dvdn_leq jnneg).
    by apply expn_boundr.
  } 
  
  exists (ex_maxn exP bounded).
  case: ex_maxnP=> i /= divi ub.
  rewrite divi /=.
  apply/negP.
  move/ub.
  by rewrite ltnn.
Qed.

(*
Lemma prime_dvd_pow_m1_bin k p n : prime p -> k < p^n.+1 ->
                                   ~~ (p %| 'C(p^n.+1-1, k)).
Proof.
  intros.
  apply /negP.
  revert H0.
  induction k.
  - rewrite bin0.
    intros ??.
    apply prime_gt1 in H.
    apply dvdn_leq in H1; lia.
  - intros.
    assert (k < p^n.+1) by lia.
    specialize (IHk H1).
    generalize (mul_bin_left (p^k-1) k); intros.
    intros ?.
    generalize (prime_gt1 H); intros.
    replace (p^k-1-k) with (p^k-k.+1) in H2.
    + assert (0 < k.+1) by lia.
      destruct (max_prime_pow_dvd H4 H5).
      assert (0< p^k -k.+1).
      {
        admit.
      }
      destruct (max_prime_pow_dvd H4 H6).      
      assert (x = x0).
      {
        admit.
      }
      move /andP in i.
      move /andP in i0.
      destruct i; destruct i0.
      admit.
    + clear IHk H2 H3; lia.
Admitted.
*)

Lemma prime_power_dvd_mul_helper p k a b :
  prime p ->
  p ^ k %| a * b ->
  exists j, (j<=k) && (p^j %| a) && (p^(k-j) %| b).
Proof.
  intros.
  induction k.
  - exists 0.
    by rewrite subn0 !expn0 !dvd1n.
  - assert (p^k %| a*b).
    {
      rewrite expnS in H0.
      by apply mul_dvdn_r in H0.
    }
    specialize (IHk H1).
    destruct IHk.
    move /andP in H2.
    destruct H2.
    move /andP in H2.
    destruct H2.
    generalize (divnK H3); intros.
    generalize (divnK H4); intros.
    rewrite -H5 -H6 expnS in H0.
    assert (forall k, 0 < p^k).
    {
      intros.
      rewrite expn_gt0.
      apply prime_gt0 in H.
      apply /orP.
      tauto.
    }
    replace (a %/ p ^ x * p ^ x * (b %/ p ^ (k - x) * p ^ (k - x))) with
      (a %/ p ^ x * (b %/ p ^ (k - x) * p ^ k)) in H0.
    + rewrite mulnA in H0.
      rewrite dvdn_pmul2r // in H0.
      rewrite (Euclid_dvdM _ _ H) in H0.
      move /orP in H0.
      destruct H0.
      * exists (x.+1).
        apply /andP; split.
        -- apply /andP; split; trivial.
           rewrite -H6 expnS dvdn_pmul2r //.
        -- replace (k.+1-x.+1) with (k-x); trivial.
      * exists x.
        apply /andP; split; trivial.
        -- apply /andP; split; trivial.
           lia.
        -- rewrite -H5.
           replace (k.+1-x) with (1 + (k - x)).
           ++ rewrite expnD expn1 dvdn_pmul2r //.
           ++ clear H1 H3 H4 H5 H0.
              lia.
   + clear H1 H3 H4 H5 H6 H0.
     replace (p^k) with (p^x * p^(k-x)); try lia.
     rewrite -expnD.
     f_equal.
     lia.
 Qed.

Lemma prime_pow_dvd_gen' j k p e n  :
  prime p ->
  e <= n ->
  (p^e %| j) ->
  ~~ (p^e.+1 %| j) ->
  p^n.+1 %| j * k ->
  p^(n.+1-e) %| k.
Proof.
  intros p_prim ele divj notdivj divjk.
  generalize (divnK divj); intros.
  rewrite -H in divjk.
  rewrite mulnC mulnA in divjk.
  replace (p^n.+1) with (p^(n.+1-e) * p^e) in divjk.
  - rewrite dvdn_pmul2r in divjk.
    assert (~~ (p %| (j %/ p ^ e))).
    {
      apply /negP.
      intros ?.
      apply prime_gt0 in p_prim.
      assert (0 < p^e).
      {
        rewrite expn_gt0.
        apply /orP.
        tauto.
      }
      rewrite -(dvdn_pmul2r H1) in H0.
      rewrite divnK // in H0.
      rewrite expnS in notdivj.
      move /negP in notdivj.
      tauto.
    }
    + replace (n.+1-e) with ((n-e).+1) in divjk.
      * rewrite mulnC in divjk.
        generalize (prime_pow_dvd p_prim H0 divjk); intros.
        replace (n.+1-e) with ((n-e).+1); trivial.
        clear divj notdivj H H0 divjk H1; lia.
      * clear divj notdivj H H0 divjk; lia.
    + rewrite expn_gt0.
      apply prime_gt0 in p_prim.
      apply /orP.
      tauto.
  - rewrite -expnD.
    f_equal.
    clear divj notdivj H divjk; lia.
 Qed.

Lemma prime_pow_dvd_gen j k p e n  :
  prime p ->
  e <= n.+1 ->
  (p^e %| j) ->
  ~~ (p^e.+1 %| j) ->
  p^n.+1 %| j * k ->
  p^(n.+1-e) %| k.
Proof.
  intros p_prim ele divj notdivj divjk.
  case (boolP (e <= n)).
  - intros.
    by apply prime_pow_dvd_gen' with (j := j).
  - intros.
    assert (e = n.+1) by lia.
    by rewrite H subnn expn0 dvd1n.
 Qed.

(*
Lemma prime_power_dvd_mul p k a b :
  prime p ->
  p ^ k %| a * b = [exists j:(ordinal (k.-1.+1)), (p^j %| a) && (p^(k-j) %| b)].
Proof.
(*  move=> pprime.
  case: (eqVneq a 0)=> [-> | neqq].
  - admit.
  - case: (@max_prime_pow_dvd a p).
    + by apply prime_gt1.
    + lia.
    + move => x /andP-[pdiva pndiva].
      have: p^(k-x) %| b = (p ^ k %| a * b).
      {
        repeat case: dvdnP => //.
        - move=> HH1 [j eqq1]; subst.
          elim HH1.
          move: pdiva.
          move/dvdnP=> [jj eqq2]; subst.
          exists (jj * j).
          rewrite -!mulnA.
          f_equal.
          rewrite mulnC -!mulnA.
          f_equal.
          rewrite -expnD.
          f_equal.
          rewrite subnK //.
          
        - 
      } 
        
      case: dvdnP.
      apply/iffEq.
      split=> HH.
      * have pdvib: p^(x-k) %| b.
        {
          Search (_ * _ %| _ * _).
        
      move/andP.
  
  case: dvdnP=> HH; symmetry.
  - destruct HH as [j eqq].
    


  
  induction k => /=.
  - rewrite expn0 dvd1n.
    symmetry.
    apply/existsP.
    simpl.
    exists ord0.
    by rewrite /= expn0 !dvd1n.
  - rewrite expnS.
    apply/iffEq.
    split=> HH.
    + have: p ^ k %| a * b by apply mul_dvdn_r in HH.
      rewrite IHk.
      move/existsP=>[j ]/andP-[diva divb].
      apply/existsP.
      case_eq (dvdn (p^j.+1) a) => eqq1.
      * have ordpf: j.+1 < k.+1.
        {
          admit.
        } 
        exists (Ordinal ordpf).
        by rewrite /= eqq1 /= subSS.
      * have ordpf: j < k.+1.
        {
          admit.
        } 
        exists (Ordinal ordpf).
        rewrite /= diva /=.
        
        
        dvdn_pmul2r: forall [p d m : nat], 0 < p -> (d * p %| m * p) = (d %| m)
        dvdn_pmul2l: forall [p d m : nat], 0 < p -> (p * d %| p * m) = (d %| m)
    *)
    
Admitted.
*)

Lemma prime_pow_dvd_bin_full j k p n :
  prime p -> 0 < k < p^n -> 0 < n ->
  p^j %| k ->
  ~~ (p^j.+1 %| k) ->
  p^(n-j) %| 'C(p^n, k).
Proof.
  intros.
  have HH: (p^n %| k * 'C(p^n,k)).
  {
    destruct k; trivial.
    by rewrite -mul_bin_diag dvdn_mulr.    
  }
  assert (j < n).
  {
    assert (0 < k) by lia.
    generalize (dvdn_leq H4 H2); intros.
    clear H2 H3 HH.
    apply ltn_pexp2l with (m := p); try lia.
    by apply prime_gt0.
  }
  destruct n; trivial.
  apply prime_pow_dvd_gen with (j := k); trivial.
  lia.
Qed.

Lemma prime_dvd_pow_bin k p n :
  prime p ->
  0 < k < p ->
  p^n.+1 %| 'C(p^n.+1, k).
Proof.
  intros.
  generalize (mul_bin_down (p^n.+1) k); intros.  
  have HH: (~~ (p %| p^n.+1-k)).
  {
    rewrite dvdn_subr.
    - apply/negP.
      move/dvdn_leq.
      lia.
    - apply (@leq_trans (k ^ n.+1)).
      + rewrite -[k]expn1 leq_pexp2l //.
        lia.
      + rewrite leq_exp2r //.
        lia.
    - by rewrite dvdn_exp.
  }
  assert (p^n.+1 %| (p^n.+1-k) * 'C(p^n.+1,k)).
  {
    rewrite -H1.
    apply dvdn_mulr.
    apply dvdnn.
  }
  rewrite Gauss_dvdr // in H2.
  rewrite coprimeXl //.
  by rewrite prime_coprime.
Qed.
  
(*
Lemma add_exp_mod_exp_p p k :
  prime p ->
  odd p ->
  (1 + p)^(p^k) = 1 %[mod p^k.+1].
Proof.
  intros.
  rewrite expnDn.
  rewrite big_ord_recl /= bin0 exp1n !mul1n expn0.
  rewrite -modnDmr -modn_summ.
  suff/eqP-> : \sum_(i < p ^ k) 'C(p ^ k, bump 0 i) * (1 ^ (p ^ k - bump 0 i) * p ^ bump 0 i) %% (p ^ k.+1) == 0
    by rewrite mod0n addn0.

  rewrite sum_nat_eq0.
  apply/forallP=> i.
  apply/implyP=> _.
  rewrite exp1n mul1n.
  rewrite /bump /=.

        
  
 (*
  rewrite bin_ffactd.
  *)

Admitted.



Lemma ord_p1_pow_p p n :
  prime p ->
  odd p ->
  (1 + p)^(p^n) = 1 + p^n.+1 %[mod p^n.+2].
Proof.
  intros.
  induction n.
  - by rewrite expn0 !expn1.
  - rewrite expnS expnS.
    apply (f_equal (fun z => z^p)) in IHn.
    Admitted.

 *)

Lemma ord_5_pow_2_neq n :
  5^(2^n) <> 1 %[mod 2^n.+3].
Proof.
  rewrite ord_5_pow_2 !expnS !modn_small; lia.
Qed.

Lemma ord_5_pow_2_neq_m1 n :
  5^(2^n) <> 2^n.+3-1 %[mod 2^n.+3].
Proof.
  rewrite ord_5_pow_2 !expnS; lia.
Qed.

Lemma ord_pow_gcd b e1 e2 n :
  b^e1 = 1 %[mod n] ->
  b^e2 = 1 %[mod n] ->
  b^(gcdn e1 e2) = 1 %[mod n].
Proof.
  intros.
  destruct e2.
  - by rewrite gcdn0.
  - assert (0 < e2.+1) by lia.
    destruct (egcdnP e1 H1).
    apply (f_equal (fun z => z^kn %% n)) in H.
    rewrite !modnXm -expnM mulnC exp1n in H.
    apply (f_equal (fun z => z^km %% n)) in H0.
    by rewrite !modnXm -expnM mulnC e expnD exp1n -modnMm H modnMm mul1n gcdnC in H0.
 Qed.

From mathcomp Require Import poly zmodp.
Local Open Scope ring_scope.

Lemma ord_pow2' (n : nat) (b : 'Z_(2^n.+3)):
  b^+(2^n.+1) = 1 :> 'Z_(2^n.+3) ->
  b^+(2^n) <> 1 :> 'Z_(2^n.+3) ->
  (2^(S n)).-primitive_root b.
Proof.
  intros.
  by apply @two_pow_prim_root_alt.
Qed.

Lemma zp_m1_neq1 (n : nat) :
  n > 2 ->
  -1 <> 1 :> 'Z_n.
Proof.
  intros.
  injection; unfold Zp_trunc; simpl.
  replace (n.-2.+2) with n by lia.
  have /modn_small->: (1 < n)%N by lia.
  have /modn_small->: (n-1 < n)%N by lia.
  lia.
Qed.      

Lemma unit_pow_2_Zp (n : nat) (b : 'Z_(2^n.+1)) :
  b \is a unit <->
  odd b.
Proof.
  have/(unitZpE b): (2^n.+1 > 1).
  {
    rewrite !expnS; lia.
  }
  rewrite (_ : (b%:R) = b) ?natr_Zp // => ->.
  rewrite -coprimen2 coprime_sym coprime_pexpr; lia.
Qed.

Lemma unit_pow_2_Zp' (n : nat) (b : {unit 'Z_(2^n.+1)}) :
  odd (val b).
Proof.
  by rewrite -unit_pow_2_Zp ?(valP b).
Qed.


Lemma ord_5_pow_2_Zp' n :
  inZp (5 ^ (2^n)) = inZp (1 + 2^n.+2) :> 'Z_(2^n.+3).
Proof.
  generalize (ord_5_pow_2 n); intros.
  rewrite /inZp.
  apply /eqP.
  rewrite /eq_op /=.
  rewrite Zp_cast; [| rewrite !expnS; lia].
  by apply /eqP.
Qed.  

Lemma ord_5_pow_2_Zp n :
  inZp 5 ^+ (2^n) = inZp (1 + 2^n.+2) :> 'Z_(2^n.+3).
Proof.
  rewrite -ord_5_pow_2_Zp'.
  by rewrite inZp_exp.
Qed.

Lemma ord_5_pow_2_Zp_1 n :
  inZp 5 ^+ (2^n.+1) = 1 :> 'Z_(2^n.+3).
Proof.
  assert (odd5:odd 5) by by [].
  move: (ord_odd_pow_2' n odd5)=> b2n1_1.
  rewrite -inZp_exp.
  apply: val_inj => /=.
  rewrite Zp_cast; try lia.
  rewrite !expnS; lia.
Qed.

Lemma ord_3_pow_2_Zp_1 n :
  inZp 3 ^+ (2^n.+1) = 1 :> 'Z_(2^n.+3).
Proof.
  assert (odd3:odd 3) by by [].
  move: (ord_odd_pow_2' n odd3)=> b2n1_1.
  rewrite -inZp_exp.
  apply: val_inj => /=.
  rewrite Zp_cast; try lia.
  rewrite !expnS; lia.
Qed.

Lemma primitive_5_pow2 n :
  let b5 : 'Z_(2^n.+3) := inZp 5 in
  (2^n.+1).-primitive_root b5.
Proof.
  apply ord_pow2'.
  - apply ord_5_pow_2_Zp_1.
  - rewrite ord_5_pow_2_Zp.
    intros ?.
    apply (f_equal val) in H.
    simpl in H.
    rewrite Zp_cast in H; [|rewrite !expnS; lia].
    rewrite modn_small in H; [|rewrite !expnS; lia].
    rewrite modn_small in H; [|rewrite !expnS; lia].    
    lia.
Qed.

Lemma m1_neq_pow5_mod2n (n : nat) :
  let b5 : 'Z_(2^n.+3) := inZp 5 in
  not (exists k, b5^+k = -1).
Proof.
  generalize (primitive_5_pow2 n); intros.
  simpl in H.
  generalize (two_pow_prim_root_m1_alt b5 n H); intros.
  apply H0.
  - apply zp_m1_neq1.
    rewrite !expnS; lia.
  - rewrite ord_5_pow_2_Zp.
    unfold opp; simpl.
    unfold Zp_opp.
    intros ?.
    apply (f_equal val) in H1.
    simpl in H1.
    rewrite Zp_cast in H1; [|rewrite !expnS; lia].
    rewrite modn_small in H1; [|rewrite !expnS; lia].
    rewrite modn_small in H1; [|rewrite !expnS; lia].
    rewrite modn_small in H1; [|rewrite !expnS; lia].        
    rewrite !expnS in H1; lia.
Qed.

  Lemma pow_3_5_pow_2 n :
    3^(2^n.+1) = 5^(2^n.+1) %[mod 2^n.+4].
  Proof.
  induction n.
  - lia.
  - symmetry.
    rewrite modn_sub_iff; [|rewrite leq_exp2r; lia].
    rewrite expnS !(mulnC 2%N _) !expnM subn_sqr.
    symmetry in IHn.
    rewrite modn_sub_iff in IHn; [|rewrite leq_exp2r; lia].
    rewrite (expnS _ n.+4) (mulnC 2%N _).
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

  Lemma ord_3_pow_2_neq_m1 n :
    3^(2^n) <> 2^n.+3-1 %[mod 2^n.+3].
  Proof.
    destruct n.
    - lia.
    - rewrite pow_3_5_pow_2.
      apply ord_5_pow_2_neq_m1.     
  Qed.

  Lemma primitive_3_pow2 n :
    let b3 : 'Z_(2^n.+3) := inZp 3 in
    (2^n.+1).-primitive_root b3.
  Proof.
    apply ord_pow2'.
    - apply ord_3_pow_2_Zp_1.
    - generalize (@ord_3_pow_2_neq n); intros.
      unfold one; simpl.
      unfold Zp1.
      intros ?.
      rewrite -inZp_exp in H0.
      apply (f_equal val) in H0.
      simpl in H0.
      rewrite Zp_cast in H0; [|rewrite !expnS; lia].
      tauto.
  Qed.

  Lemma m1_neq_pow3_mod2n (n : nat) :
  let b3 : 'Z_(2^n.+3) := inZp 3 in
  not (exists k, b3^+k = -1).
Proof.
  generalize (primitive_3_pow2 n); intros.
  simpl in H.
  generalize (two_pow_prim_root_m1_alt b3 n H); intros.
  apply H0.
  - apply zp_m1_neq1.
    rewrite !expnS; lia.
  - generalize (@ord_3_pow_2_neq_m1 n); intros.
    unfold opp; simpl.
    unfold Zp_opp.
    intros ?.
    unfold b3 in H2.
    rewrite -inZp_exp in H2.
    apply (f_equal val) in H2.
    simpl in H2.
    rewrite Zp_cast in H2; [|rewrite !expnS; lia].
    rewrite H2 in H1.
    clear H0 H2.
    rewrite modn_small in H1.
    + rewrite modn_small in H1; [|rewrite !expnS; lia].
      rewrite modn_small in H1; [|rewrite !expnS; lia].
      tauto.
    + rewrite modn_small; [|rewrite !expnS; lia].        
      lia.
Qed.

From mathcomp Require Import finset eqtype finalg.
From mathcomp Require Import fingroup.quotient.
Section two_pow_units.
  
  Import GroupScope.
Lemma ord_unit_pow_2_Zp (n : nat) (b : {unit 'Z_(2^n.+3)}) :
  b ^+ (2^n.+1) = 1.
Proof.
  move: (unit_pow_2_Zp' b)=> bodd.
  move: (ord_odd_pow_2' n bodd)=> b2n1_1.
  move: (unit_Zp_expg b (2^n.+1)).
  rewrite /inZp.
  move/(f_equal val)=> /=.
  rewrite {3}Zp_cast; [| rewrite !expnS; lia].
  rewrite b2n1_1 => eqq.
  apply/eqP.
  rewrite /eq_op /= /eq_op /= eqq.
  rewrite Zp_cast; [| rewrite !expnS; lia].
  rewrite modn_small // !expnS; lia.
Qed.

Lemma ord_unit_pow_2_Zp' (n : nat) (b : {unit 'Z_(2^n.+3)}) :
  #[b] %| (2^n.+1)%N.
Proof.
  rewrite order_dvdn.
  apply /eqP.
  apply ord_unit_pow_2_Zp.
Qed.

Lemma dvdn_prime_power x p n :
  prime p ->
  x %| p^n.+1 ->
  ~ x %| p^n ->
  (x = p^n.+1)%N.
Proof.
  intros p_prime x_n1 x_n.
  generalize (prime_gt1 p_prime); intros pgt.
  move /dvdn_pfactor in x_n1.
  destruct (x_n1 p_prime).
  rewrite H0 (dvdn_Pexp2l x0 n pgt) in x_n.
  assert (x0 = n.+1) by lia.
  by rewrite H1 in H0.
Qed.

Lemma ord_unit_pow_2_Zp_max (n : nat) (b : {unit 'Z_(2^n.+3)}) :
  b ^+ (2^n) <> 1 ->
  #[b] = (2^n.+1)%N.
Proof.
  intros.
  generalize (ord_unit_pow_2_Zp' b); intros.
  assert (~ #[b] %| 2^n).
  {
    intros ?.
    rewrite order_dvdn in H1.
    by move /eqP in H1.
  }
  by apply dvdn_prime_power.
Qed.

Lemma card_units_pow_2_Zp (n : nat) :
  #|units_Zp (2^n.+2)| = (2^n.+1)%N.
Proof.
  rewrite card_units_Zp; try lia.
  rewrite totient_pfactor; trivial; try lia.
  rewrite !expnS; lia.
Qed.

Lemma unit_Zp_gens_ord (n : nat) (a b : {unit 'Z_n}) :
  #|<[a]>%G :&: <[b]>%G| = 1%N ->
  #|<[a]> * <[b]>|  = (#[a] * #[b])%N.
Proof.
  intros.
  by rewrite mul_cardG H muln1.
Qed.

Lemma unit_pow_2_Zp_gens_ord (n : nat) (a b : {unit 'Z_(2^n.+2)}) :
  #[a] = 2%N ->
  #[b] = (2^n)%N ->
  #|<[a]>%G :&: <[b]>%G| = 1%N ->
  #|<[a]> * <[b]>|  = (2^n.+1)%N.
Proof.
  intros.
  rewrite (unit_Zp_gens_ord H1) H H0; trivial.
  by rewrite expnS.
Qed.

Lemma ord2_setI (n : nat) (a b : {unit 'Z_(2^n)}) :
  #[a] = 2%N ->
  (a \notin <[b]>) ->
  #|<[a]>%G :&: <[b]>%G| = 1%N.
Proof.
  intros.
  have ->: (<[a]> :&: <[b]> = [set 1]).
  {
    rewrite (cycle2g H) setIUl.
    have /eqP->: ([set a] :&: <[b]> == set0).
    {
      by rewrite setI_eq0 disjoints1.
    } 
    by rewrite setU0 -set1gE setI1g.
  }
  by rewrite cards1.
Qed.

Lemma unit_pow_2_Zp_gens (n : nat) (a b : {unit 'Z_(2^n.+2)}) :
  #[a] = 2%N ->
  #[b] = (2^n)%N ->
  a \notin <[b]> ->
  <[a]> <*> <[b]> = [group of (units_Zp (2^n.+2)%N)].
Proof.
  intros.
  generalize (subsetT (<[a]> * <[b]>)%G); intros.
  apply index1g; trivial.
  rewrite -(divgS H2) (card_units_pow_2_Zp n) joinGE /= norm_joinEr /=.
  - rewrite unit_pow_2_Zp_gens_ord //.
    + rewrite divnn !expnS; lia.
    + by apply ord2_setI.
  - apply cents_norm.
    eapply subset_trans.
    apply subsetT.
    apply sub_abelian_cent.
    + apply units_Zp_abelian.
    + apply subsetT.
Qed.

Lemma unit_3_pow_2_Zp (n : nat) :
  (3 : 'Z_(2^n.+1)) \is a unit.
Proof.
  rewrite unitZpE.
  - rewrite coprimeXl //.
  - rewrite !expnS; lia.
Qed.

Lemma unit_5_pow_2_Zp (n : nat) :
  (5 : 'Z_(2^n.+1)) \is a unit.
Proof.
  rewrite unitZpE.
  - rewrite coprimeXl //.
  - rewrite !expnS; lia.
Qed.

Lemma unit_odd_pow_2_Zp (j n : nat):
  odd j ->
  (inZp j : 'Z_(2^n.+1)) \is a unit.
Proof.
  intros.
  rewrite unit_pow_2_Zp /= expnS Zp_cast; [|lia].
  rewrite odd_mod //.
  replace (2 * 2^n)%N with ((2^n).*2) by lia.
  by rewrite odd_double.
Qed.

Lemma unit_3_pow_2_Zp' (n : nat) :
  (3 : 'Z_(2^n.+1)) \is a unit.
Proof.
  apply unit_odd_pow_2_Zp.
  rewrite /= expnS Zp_cast; lia.
Qed.

Lemma unit_pow_2_Zp_gens_m1_3 (n : nat) :
  let um1 := FinRing.unit 'Z_(2^n.+3) (unitrN1 _) in
  let u3 := FinRing.unit 'Z_(2^n.+3) (unit_3_pow_2_Zp n.+2) in
  <[um1]> <*> <[u3]> = [group of (units_Zp (2^n.+3)%N)].
Proof.
  have small1: 1 < 2 ^ n.+3 by (rewrite !expnS; lia).
  have small2: 2 < 2 ^ n.+3 by (rewrite !expnS; lia).
  have small3: 3 < 2 ^ n.+3 by (rewrite !expnS; lia).
  apply unit_pow_2_Zp_gens.
  - apply nt_prime_order; trivial.
    + apply val_inj.
      by rewrite /= mulrNN mulr1.
    + apply /eqP.
      move/(f_equal FinRing.uval).
      simpl.
      by apply (zp_m1_neq1 small2).
  - apply ord_unit_pow_2_Zp_max.
    generalize (@ord_3_pow_2_neq n); intros.
    move/(f_equal (fun (z : {unit 'Z_(2^n.+3)}) => val z)).
    rewrite unit_Zp_expg /= {2 3 4 5 6}Zp_cast // !modn_small // /inZp.
    move/(f_equal val) => /=.
    rewrite !Zp_cast //.
  - have nexist := @m1_neq_pow3_mod2n n.
    apply/negP.
    move/cyclePmin => [x xlt].
    move/(f_equal (fun (z : {unit 'Z_(2^n.+3)}) => val z)).
    rewrite /= unit_Zp_expg /= {2 3 4 5 6}Zp_cast // !modn_small // /inZp.
    move/(f_equal val) => /=.
    rewrite !Zp_cast // modn_small; [| rewrite !expnS; lia].
    rewrite modn_small // => pow3m1.
    apply nexist.
    exists x.
    rewrite /opp /= /Zp_opp {2}Zp_cast // -inZp_exp.
    apply val_inj.
    by rewrite /= !Zp_cast // -pow3m1 !modn_small //; rewrite !expnS; lia.
Qed.

Lemma unit_Z4_gens_m1 :
  let um1 := FinRing.unit 'Z_4 (unitrN1 _) in  
  <[um1]> = [group of (units_Zp 4)].
Proof.
  intros.
  generalize (subsetT (<[um1]>)); intros.
  apply index1g; trivial.
  rewrite -(divgS H) (card_units_pow_2_Zp 0).
  assert (#[um1] = 2%N).
  {
    apply nt_prime_order; trivial.
    apply val_inj.
    by rewrite /= mulrNN mulr1.
  }
  unfold order in H0.
  rewrite H0.
  lia.
Qed.

Lemma unit_pow_2_Zp_gens_m1_5 (n : nat) :
  let um1 := FinRing.unit 'Z_(2^n.+3) (unitrN1 _) in
  let u5 := FinRing.unit 'Z_(2^n.+3) (unit_5_pow_2_Zp n.+2) in
  <[um1]> <*> <[u5]> = [group of (units_Zp (2^n.+3)%N)].
Proof.
  have small1: 1 < 2 ^ n.+3 by (rewrite !expnS; lia).
  have small2: 2 < 2 ^ n.+3 by (rewrite !expnS; lia).
  have small3: 3 < 2 ^ n.+3 by (rewrite !expnS; lia).
  have small4: 4 < 2 ^ n.+3 by (rewrite !expnS; lia).
  have small5: 5 < 2 ^ n.+3 by (rewrite !expnS; lia).    
  apply unit_pow_2_Zp_gens.
  - apply nt_prime_order; trivial.
    + apply val_inj.
      by rewrite /= mulrNN mulr1.
    + apply /eqP.
      move/(f_equal FinRing.uval).
      simpl.
      by apply (zp_m1_neq1 small2).
  - apply ord_unit_pow_2_Zp_max.
    generalize (@ord_5_pow_2_neq n); intros.
    move/(f_equal (fun (z : {unit 'Z_(2^n.+3)}) => val z)).
    rewrite unit_Zp_expg /= {2 3 4 5 6 7 8 9 10}Zp_cast // !modn_small // /inZp.
    move/(f_equal val) => /=.
    rewrite !Zp_cast //.
  - generalize (@m1_neq_pow5_mod2n n); intros.
    apply/negP.
    move/cyclePmin => [x xlt].
    move/(f_equal (fun (z : {unit 'Z_(2^n.+3)}) => val z)).
    rewrite /= unit_Zp_expg /= {2 3 4 5 6 7 8 9 10}Zp_cast // !modn_small // /inZp.
    move/(f_equal val) => /=.
    rewrite !Zp_cast // modn_small; [| rewrite !expnS; lia].
    rewrite modn_small // => HH.
    apply H.
    exists x.
    rewrite /opp /= /Zp_opp {2}Zp_cast // -inZp_exp.
    apply val_inj.
    by rewrite /= !Zp_cast // -HH !modn_small //; rewrite !expnS; lia.
Qed.

Lemma unit_pow_2_Zp_gens_m1_3_quo (n : nat) :
  let um1 := FinRing.unit 'Z_(2^n.+3) (unitrN1 _) in
  let u3 := FinRing.unit 'Z_(2^n.+3) (unit_3_pow_2_Zp n.+2) in
  <[u3]>/<[um1]> = [group of (units_Zp (2^n.+3)%N)]/<[um1]>.
Proof.
  intros.
  rewrite -quotientYidl.
  - f_equal.
    by rewrite unit_pow_2_Zp_gens_m1_3.
  - apply cents_norm.
    eapply subset_trans.
    apply subsetT.
    apply sub_abelian_cent.
    + apply units_Zp_abelian.
    + apply subsetT.
 Qed.

End two_pow_units.

From mathcomp Require Import matrix perm.
Section add_self.

  Context {G:ringType}.
  Context {n:nat} (npos:0 < n).
  
  Definition modn_ord (m:nat) : 'I_n := Ordinal (@ltn_pmod m n npos).
  
  Definition rotate_index_right_ord (idx:'I_n) (e:nat) 
    := modn_ord (idx + e).
  
  Lemma rotate_ind_right_ord_cancel (e:nat) :
    cancel (fun (idx : 'I_n) => rotate_index_right_ord idx e)
      (fun (idx : 'I_n) => rotate_index_right_ord idx (n - e %% n)).
  Proof.
    rewrite /rotate_index_right_ord /cancel /modn_ord /=.
    intros.
    apply ord_inj=> /=.
    rewrite -(modnDm x e n) modnDml -addnA.
    generalize (ltn_pmod e npos); intros.
    replace (e %% n + (n - e %% n))%N with n by lia.
    rewrite -modnDmr modnn addn0 modn_mod modn_small //.
  Qed.

  Definition rot_perm e := perm (can_inj (rotate_ind_right_ord_cancel e)).

  Lemma rot_mul e1 e2 :
    perm_mul (rot_perm e1) (rot_perm e2) = rot_perm (e1 + e2).
  Proof.
    rewrite /perm_mul /rot_perm -permP.
    move => x.
    rewrite permE /= !permE /rotate_index_right_ord /modn_ord.
    apply ord_inj=> /=.
    by rewrite modnDml addnA.
  Qed.

  Definition rotate_row_right (v:'rV[G]_n) (e:nat)
    := \row_(i < n) v 0 (rotate_index_right_ord i e).

  Definition row_sum_naive_rot_row (v:'rV[G]_n)
    := \sum_(i < n) rotate_row_right v i.

  Definition row_sum_naive_rot (v:'rV[G]_n)
    := row_sum_naive_rot_row v 0 (Ordinal npos).

  Lemma row_sum_naive_rot_correct (v:'rV[G]_n)
    : row_sum_naive_rot v == \sum_(j < n) v 0 j.
  Proof.
    rewrite/row_sum_naive_rot/row_sum_naive_rot_row.
    rewrite /rotate_row_right/rotate_index_right_ord summxE /=.
    apply/eqP.
    apply eq_bigr=> k _.
    rewrite !mxE.
    f_equal.
    apply ord_inj => /=.
    by rewrite add0n modn_small.
  Qed.

End add_self.
