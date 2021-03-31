Require Import Reals Lra List Permutation.

Require Import LibUtils utils.Utils.
Require Import ProbSpace DiscreteProbSpace SigmaAlgebras.
Require Import pmf_monad mdp.
Require Import RealRandomVariable SimpleExpectation.
Require Import cond_expt.
Require Import Lia.
Require Import Equivalence EquivDec.
Require Import Morphisms.

Set Bullet Behavior "Strict Subproofs".

Require Import ClassicalDescription.

Lemma list_fst_sum_eq {A : Type} (l : list (nonnegreal*A)) :
  list_fst_sum l =
  list_sum (map (fun x => nonneg (fst x)) l).
Proof.
  induction l; simpl; trivial.
  rewrite IHl.
  now destruct a.
Qed.

Lemma seqmap_map {A B:Type} (f:A->B) (l:list A) : seq.map f l = List.map f l.
Proof.
  induction l; auto.
Qed.

Section Pmf_PMF.

  Definition pmf_PMF_fun {A:Type} {countableA:Countable A} {dec:EqDec A eq} (pmf:Pmf A): A -> R
    := fun a => list_sum
               (map
                  (fun x => nonneg (fst x))
                  (filter
                     (fun x => if a == snd x then true else false)
                     (pmf.(outcomes)))).

  Lemma list_sum_nsubl0 l1 l2 :
    (forall x, In x l2 /\ ~ In x l1 -> x = 0) ->
    sublist l1 l2 ->
    NoDup l2 ->
    list_sum l1 = list_sum l2.
  Proof.
    intros.
    destruct (sublist_perm_head H0) as [l3 perm].
    rewrite <- perm.
    rewrite list_sum_cat.
    assert (forall x, In x l3 -> x = 0).
    {
      intros ? inn.
      apply H.
      split.
      - rewrite <- perm.
        rewrite in_app_iff; eauto.
      - intros inn2.
        rewrite <- perm in H1.
        apply NoDup_app_disj in H1.
        eelim H1; eauto.
    } 
    cut (list_sum l3 = 0); [lra |].
    clear perm.
    induction l3; simpl in *; trivial.
    rewrite IHl3 by eauto.
    rewrite (H2 a) by eauto.
    lra.
  Qed.

  Lemma list_sum_nincl0 l1 l2 :
    NoDup l1 ->
    NoDup l2 ->
    (forall x, In x l2 /\ ~ In x l1 -> x = 0) ->
    incl l1 l2 ->
    list_sum l1 = list_sum l2.
  Proof.
    intros.
    destruct (incl_NoDup_sublist_perm H H2)
      as [l3 [perm subl]].
    rewrite perm.
    apply list_sum_nsubl0; trivial.
    intros ? [??].
    apply (H1 x).
    split; trivial.
    now rewrite perm.
  Qed.

  Lemma list_sum_filter0 l : list_sum l = list_sum (filter (fun x => nequiv_decb x 0) l).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl; simpl.
    unfold nequiv_decb, negb, equiv_decb.
    destruct (equiv_dec a 0); simpl; trivial.
    rewrite e; lra.
  Qed.
  
  Lemma infinite_sum'_finite (coll:nat->R) (l:list nat):
    (forall n, ~ In n l -> coll n = 0) ->
    NoDup l ->
    infinite_sum' coll (list_sum (map coll l)).
  Proof.
    intros nin nd.
    apply (infinite_sum'_split (list_max l + 1)).
    rewrite (infinite_sum'_ext _ (fun _ => 0)).
    - replace (sum_f_R0' coll (list_max l + 1))
        with (list_sum (map coll l)).
      + rewrite Rminus_eq_0.
        apply infinite_sum'0.
      + rewrite sum_f_R0'_list_sum.
        rewrite (list_sum_filter0 (map coll l)).
        rewrite (list_sum_filter0 (map coll (seq 0 (list_max l + 1)))).
        repeat rewrite filter_map_swap.
        apply list_sum_perm_eq.
        apply Permutation_map.
        apply NoDup_Permutation'.
        * now apply NoDup_filter.
        * apply NoDup_filter.
          apply seq_NoDup.
        * intros a.
          repeat rewrite filter_In.
          split; intros [inn non0]; split; trivial.
          -- apply in_seq.
             split; [lia |].
             generalize (list_max_upper l).
             rewrite Forall_forall; intros lmu.
             specialize (lmu _ inn).
             lia.
          -- destruct (in_dec eq_nat_dec a l); trivial.
             specialize (nin _ n).
             unfold nequiv_decb, negb, equiv_decb in non0.
             destruct (equiv_dec (coll a) 0); congruence.
    - intros.
      apply nin.
      intros inn.
      generalize (list_max_upper l).
      rewrite Forall_forall; intros lmu.
      specialize (lmu _ inn).
      lia.
  Qed.

  Lemma list_sum0_0 l: Forall (fun x => x = 0) l -> list_sum l = 0.
  Proof.
    induction l; simpl; trivial.
    intros FF; invcs FF.
    rewrite IHl; trivial.
    lra.
  Qed.


  Lemma map_filter_nodup_perm_aux {A B:Type} {dec:EqDec B eq} (f:A->B) l (b:B) :
   Permutation
    (concat
       (map
          (fun x : B =>
           filter (fun x0 : A => if dec x (f x0) then true else false)
                  l) (nodup dec (map f l)))) l.
  Proof.
    rewrite <- (nodup_hd_quotient _ b).
    rewrite map_map.
    rewrite quotient_map.
    rewrite map_map.
    etransitivity
    ; [| eapply (unquotient_quotient (fun x y => eq (f x) (f y)) (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) l)].

    apply perm2_concat_perm.

    transitivity
    (map
       (fun x : list A =>
        filter (fun x0 : A => if dec (hd b (map f x)) (f x0) then true else false) (concat (quotient (fun x y : A => f x = f y) (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) l)))
       (quotient (fun x y : A => f x = f y) (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) l)).
    -
      assert (HH:forall ll, Forall2 (Permutation (A:=A))
    (map
       (fun x : list A =>
        filter (fun x0 : A => if dec (hd b (map f x)) (f x0) then true else false) l)
       ll)
    (map
       (fun x : list A =>
        filter (fun x0 : A => if dec (hd b (map f x)) (f x0) then true else false)
          (concat (quotient (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) (fun x0 y : A => f x0 = f y) l)))
       ll)).
      {
        induction ll; simpl; trivial.
        constructor; trivial.
        apply Permutation_filter.
        symmetry.
        apply unquotient_quotient.
      }
      apply HH.
    -
      generalize (quotient_all_equivs (fun x y : A => f x = f y) (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) l).
      generalize (quotient_all_different  (fun x y : A => f x = f y) (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) l).
      generalize (quotient_nnil  (fun x y : A => f x = f y) (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) l).
      generalize (quotient (fun x y : A => f x = f y) (equiv:=Equivalence_pullback _ _ _) (dec:=EqDec_pullback _ _) l)
      ; intros ll ll_nnil ll_diff ll_equivs.
      induction ll; simpl; trivial.
      invcs ll_nnil.
      invcs ll_diff.
      invcs ll_equivs.
      constructor.
      + rewrite filter_app.
        replace (filter (fun x0 : A => if dec (hd b (map f a)) (f x0) then true else false) a) with a.
        * replace (filter (fun x0 : A => if dec (hd b (map f a)) (f x0) then true else false) (concat ll)) with (@nil A).
          -- rewrite app_nil_r; trivial.
          -- symmetry.
             apply false_filter_nil; intros.
             match_destr.
             red in e.
             unfold not_nil in H1.
             destruct a; [congruence |].
             simpl in e.
             apply in_concat in H.
             destruct H as [?[inn1 inn2]].
             rewrite Forall_forall in H3.
             specialize (H3 _ inn1).
             elim (H3 a x); simpl; eauto.
        * symmetry.
          apply true_filter; intros.
          match_destr.
          unfold not_nil in H1.
          destruct a; [congruence |].
          simpl in c.
          elim c.
          apply (H5 a x); simpl; eauto.
      + etransitivity; [| eapply IHll]; trivial.
        erewrite map_ext_in; [reflexivity |]; intros ? inn1.
        rewrite filter_app.
        replace (filter (fun x0 : A => if dec (hd b (map f a0)) (f x0) then true else false) a) with (@nil A); simpl; trivial.
        symmetry.
        apply false_filter_nil; intros ? inn2.
        rewrite Forall_forall in *.
        match_destr.
        specialize (H2 _ inn1).
        unfold not_nil in H2.
        destruct a0; [congruence |].
        simpl in e.
        specialize (H3 _ inn1).
        elim (H3 x a0); simpl; eauto.
  Qed.

  Lemma map_filter_nodup_perm {A B:Type} {dec:EqDec B eq} (f:A->B) l :
    Permutation
      (concat
         (map
            (fun x : B =>
               filter (fun x0 : A => if dec x (f x0) then true else false)
                      l) (nodup dec (map f l)))) l.
  Proof.
    destruct l; [reflexivity |].
    apply map_filter_nodup_perm_aux.
    exact (f a).
  Qed.
  
  Program Definition pmf_PMF {A:Type} {countableA:Countable A} {dec:EqDec A eq} (pmf:Pmf A) : prob_mass_fun A
    := {|
    pmf_pmf := pmf_PMF_fun pmf
      |}. 
  Next Obligation.
    unfold pmf_PMF_fun.
    apply list_sum_pos_pos'.
    apply Forall_map.
    rewrite Forall_forall; intros [[??]?]; intros; simpl.
    apply cond_nonneg.
  Qed.
  Next Obligation.
    unfold pmf_PMF_fun, countable_sum.
    replace 1 with R1 by lra.
    destruct pmf; simpl.
    rewrite <- sum1; clear sum1.
    rewrite list_fst_sum_eq.
    replace (list_sum (map (fun x : nonnegreal * A => nonneg (fst x)) outcomes))
      with (list_sum (map (fun n : nat =>
     match countable_inv n with
     | Some a =>
         list_sum
           (map (fun x : nonnegreal * A => nonneg (fst x))
              (filter (fun x : nonnegreal * A => if equiv_dec a (snd x) then true else false) outcomes))
     | None => 0
     end) (nodup eq_nat_dec (map countable_index (map snd outcomes))))).
    - apply infinite_sum'_finite
      ; intros.
      + match_case; intros.
        apply countable_inv_sound in H0.
        apply list_sum0_0.
        rewrite Forall_forall; intros ? inn.
        apply in_map_iff in inn.
        destruct inn as [[??][? inn]]; simpl in *; subst.
        apply filter_In in inn.
        destruct inn as [inn an0].
        simpl in *.
        match_destr_in an0.
        red in e; subst.
        elim H.
        apply nodup_In.
        apply in_map.
        apply in_map_iff.
        exists (n0, a0); simpl; eauto.
      + apply NoDup_nodup.
    - rewrite nodup_map_inj with (decA:=dec)
      ; [| intros; now apply countable_index_inj].
      rewrite map_map.
      erewrite map_ext
      ; [| intros; rewrite countable_inv_index; reflexivity].
      rewrite <- map_map.
      rewrite <- list_sum_map_concat.
      transitivity (list_sum
                      (concat
                         (map (map (fun x0 : nonnegreal * A => nonneg (fst x0)))
                              (map (fun x => (filter (fun x0 : nonnegreal * A => if equiv_dec x (snd x0) then true else false)
                                                  outcomes)) (nodup dec (map snd outcomes)))))).
      {
        now rewrite map_map.
      }
      rewrite concat_map_map.
      apply list_sum_perm_eq.
      apply Permutation_map.
      apply map_filter_nodup_perm.
  Qed.

End Pmf_PMF.

Section pmf_prob.
  Context {A:Type}.
  Context {countableA:Countable A}.
  Context {decA:EqDec A eq}.
  Context (pmf:Pmf A).


  Instance ps_pmf : ProbSpace (discrete_sa A) := discrete_ps (pmf_PMF pmf).

 Lemma pmf_SimpleExpectation_value_const (c:R) :
     SimpleExpectation (Prts:=ps_pmf) (const c) = expt_value pmf (const c).
 Proof.
   rewrite SimpleExpectation_const.
   unfold const.
   now rewrite expt_value_const.
 Qed.

 Lemma pmf_SimpleExpectation_value_point_preimage_indicator (rv_X : A -> R) (c:R)
       {rv:RandomVariable (discrete_sa A) borel_sa rv_X} :
   SimpleExpectation (Prts:=ps_pmf) (point_preimage_indicator rv_X c) =
   expt_value pmf (point_preimage_indicator rv_X c).
 Proof.
   unfold point_preimage_indicator.
   generalize (SimpleExpectation_EventIndicator (Prts:=ps_pmf) (P:=(preimage_singleton rv_X c))
                                                (fun x => Req_EM_T (rv_X x) c))
   ; intros.
   simpl in H.
   unfold pre_event_preimage, pre_event_singleton in H.
   erewrite SimpleExpectation_pf_irrel in H.
   rewrite H; clear H.
   
   unfold EventIndicator.
   unfold ps_P; simpl.
   unfold ps_p_pmf.
   unfold expt_value.
   apply list_sum_Proper.
   destruct pmf; simpl.
   apply refl_refl.
   unfold map.
   unfold seq.map.
   f_equal.
   intros.
   clear sum1.
   induction outcomes.
   + easy.
   + cut_to IHoutcomes; trivial.
     rewrite IHoutcomes.
     f_equal.
     match_destr.
     unfold fst, snd.
     match_destr.
     * rewrite e.
       match_destr; lra.
     * match_destr; lra.
 Qed.

Lemma SimpleExpectation_preimage_indicator
      (rv_X : A -> R)
      {rv: RandomVariable sa_pmf borel_sa rv_X}
      {srv : SimpleRandomVariable rv_X} :
     SimpleExpectation (Prts := ps_pmf) rv_X = 
     list_sum (map (fun v => v *
                             (SimpleExpectation (Prts:=ps_pmf) (point_preimage_indicator rv_X v)))
                   (nodup Req_EM_T srv_vals)).
  Proof.
    unfold SimpleExpectation at 1.
    apply list_sum_Proper.
    apply refl_refl.
    apply map_ext.
    intros.
    unfold point_preimage_indicator.
    generalize (SimpleExpectation_EventIndicator (Prts:=ps_pmf) (P:=(preimage_singleton rv_X a))
                                                (fun x => Req_EM_T (rv_X x) a))
   ; intros.
   simpl in H.
   unfold pre_event_preimage, pre_event_singleton in H.
   erewrite SimpleExpectation_pf_irrel in H.
   rewrite H; clear H.
   reflexivity.
  Qed.


  Lemma expt_value_preimage_indicator
       (rv_X : A -> R)
       {srv : SimpleRandomVariable rv_X} :
     expt_value pmf rv_X = 
     list_sum (map (fun v => v *
                             (expt_value pmf (point_preimage_indicator rv_X v)))
                   (nodup Req_EM_T srv_vals)).
  Proof.
    transitivity (expt_value pmf (fun a => list_sum 
                 (map 
                    (fun c => c * (point_preimage_indicator rv_X c a))
                    (nodup Req_EM_T srv_vals)))).
    - apply expt_value_Proper; trivial.
      apply srv_preimage_indicator'.
    - rewrite expt_value_sum_comm.
      f_equal.
      apply map_ext; intros.
      apply expt_value_const_mul.
  Qed.

  Theorem pmf_SimpleExpectation_value (rv_X : A -> R)
          {rv: RandomVariable sa_pmf borel_sa rv_X}
          {srv:SimpleRandomVariable rv_X} 
   : SimpleExpectation (Prts:=ps_pmf) rv_X = expt_value pmf rv_X.
 Proof.
    rewrite SimpleExpectation_preimage_indicator.   
    rewrite expt_value_preimage_indicator with (srv := srv).
    apply list_sum_Proper.
    apply refl_refl.
    apply map_ext.
    intros.
    apply Rmult_eq_compat_l.
    apply pmf_SimpleExpectation_value_point_preimage_indicator.
 Qed.

 Definition rv_restricted_range {B} {decB:EqDec B eq} (default:B) (l:list B) (rv_X: A -> B) : A -> B
   := fun a => if in_dec decB (rv_X a) l
            then rv_X a
            else default.
   
 Program Global Instance srv_restricted_range
        {B} {decB:EqDec B eq} (default:B) (l:list B) (rv_X: A -> B)
   : SimpleRandomVariable (rv_restricted_range default l rv_X)
   := {|
   srv_vals := default::l
     |}.
 Next Obligation.
   unfold rv_restricted_range.
   match_destr; eauto.
 Qed.

Definition pmf_image rv_X : list R := (map rv_X (map snd pmf.(outcomes))).
 
Lemma expt_value_on_restricted_range rv_X :
  expt_value pmf rv_X = expt_value pmf (rv_restricted_range 0 (pmf_image rv_X) rv_X).
Proof.
  unfold expt_value.
  assert (forall x, In x pmf -> In (rv_X (snd x)) (pmf_image rv_X)).
  {
    unfold pmf_image; intros.
    now repeat apply in_map.
  }
  destruct pmf; simpl in *.
  clear sum1.
  induction outcomes; simpl; trivial.
  rewrite <- IHoutcomes.
  - f_equal.
    unfold rv_restricted_range.
    match_destr.
    specialize (H a); simpl in *.
    elim n.
    apply H.
    eauto.
  - simpl in *.
    firstorder.
Qed.

(* TODO: clean the proof up a bit *)
 Global Instance rv_restricted_range_image_borel
        (default:R) (rv_X: A -> R) {rv: RandomVariable sa_pmf borel_sa rv_X}
   : RandomVariable sa_pmf borel_sa (rv_restricted_range default (pmf_image rv_X) rv_X).
Proof.
  red; intros.
  destruct B.
  unfold event_preimage, rv_restricted_range, pmf_image.
  simpl proj1_sig.
  
  assert (
      pre_event_equiv
        (fun omega : A =>
           x (if in_dec EqDecR (rv_X omega) (map rv_X (map snd pmf)) then rv_X omega else default))
        (pre_event_union
           (fun omega =>
              In (rv_X omega)
                 (map rv_X (map snd pmf))
              /\ x (rv_X omega))
           (fun omega =>
              ~ In (rv_X omega)
                 (map rv_X (map snd pmf))
              /\ x default))).
  {
    unfold pre_event_union.
    intros ?; simpl.
    match_destr; intuition.
  } 
  rewrite H.
  apply sa_union.
  - apply sa_inter.
    +
      generalize (sa_pre_list_union (s:=sa_pmf)
                    (map (fun c => fun omega : A => rv_X omega = rv_X c) (map snd pmf)))
      ; intros HH.
      eapply sa_proper; try eapply HH; clear HH.
      * unfold pre_list_union.
        red; intros.
        split; intros.
        -- apply in_map_iff in H0.
           destruct H0 as [?[??]].
           eexists.
           split.
           ++ apply in_map; eauto.
           ++ simpl; congruence.
        -- destruct H0 as [? [??]].
           apply in_map_iff in H0.
           destruct H0 as [?[??]]; subst.
           rewrite H1.
           now apply in_map.
      * intros ? inn.
        apply in_map_iff in inn.
        destruct inn as [? [??]]; subst.
        now apply sa_preimage_singleton .
    + apply (rv (exist _ _ s)).
  - apply sa_inter.
    +
      apply sa_complement.
      generalize (sa_pre_list_union (s:=sa_pmf)
                    (map (fun c => fun omega : A => rv_X omega = rv_X c) (map snd pmf)))
      ; intros HH.
      eapply sa_proper; try eapply HH; clear HH.
      * unfold pre_list_union.
        red; intros.
        split; intros.
        -- apply in_map_iff in H0.
           destruct H0 as [?[??]].
           eexists.
           split.
           ++ apply in_map; eauto.
           ++ simpl; congruence.
        -- destruct H0 as [? [??]].
           apply in_map_iff in H0.
           destruct H0 as [?[??]]; subst.
           rewrite H1.
           now apply in_map.
      * intros ? inn.
        apply in_map_iff in inn.
        destruct inn as [? [??]]; subst.
        now apply sa_preimage_singleton .
    + apply sa_sigma_const_classic.
Qed.


Theorem pmf_value_SimpleExpectation (rv_X : A -> R)
   {rv: RandomVariable sa_pmf borel_sa rv_X} :
  expt_value pmf rv_X =
  SimpleExpectation (Prts:=ps_pmf)
                    (rv_restricted_range 0 (pmf_image rv_X) rv_X).
Proof.
  rewrite pmf_SimpleExpectation_value.
  apply expt_value_on_restricted_range.
Qed.

