Require Import Reals Lra List Permutation.

Require Import LibUtils utils.Utils.
Require Import ProbSpace DiscreteProbSpace SigmaAlgebras.
Require Import pmf_monad mdp.
Require Import RealRandomVariable SimpleExpectation Expectation RandomVariableFinite.
Require Import Almost.

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
    generalize (nodup_hd_quotient _ b (map f l)); intros HH0.
    eapply Permutation_map in HH0.
    eapply Permutation_concat in HH0.
    rewrite <- HH0.
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


  Lemma pmf_infinite_sum_finite {A : Type}
        {countableA : Countable A}
        {dec : EqDec A eq}
        (pmf : Pmf A) :
   infinite_sum'
    (fun n : nat =>
     match countable_inv n with
     | Some a =>
         list_sum
           (map (fun x : nonnegreal * A => nonneg (fst x))
              (filter (fun x : nonnegreal * A => if equiv_dec a (snd x) then true else false)
                 pmf))
     | None => 0
     end) (list_sum (map (fun x : nonnegreal * A => nonneg (fst x)) pmf)).
  Proof.
    destruct pmf; simpl.
    clear sum1.
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
    replace 1 with R1 by lra.
    rewrite <- pmf.(sum1).
    unfold countable_sum.
    rewrite list_fst_sum_eq.
    apply pmf_infinite_sum_finite.
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

 Lemma pmf_SimpleExpectation_value_point_preimage_indicator (rv_X : A -> R) (c:R) :
   SimpleExpectation (Prts:=ps_pmf) (point_preimage_indicator rv_X c) =
   expt_value pmf (point_preimage_indicator rv_X c).
 Proof.
   unfold point_preimage_indicator.
   generalize (SimpleExpectation_EventIndicator (Prts:=ps_pmf) (P:=(preimage_singleton rv_X c))
                                                (fun x => Req_EM_T (rv_X x) c))
   ; intros.
   unfold preimage_singleton, event_pre in H.
   unfold pre_event_preimage in H.
   simpl in H.
   erewrite SimpleExpectation_pf_irrel in H.
   rewrite H; clear H.
   
   unfold EventIndicator.
   unfold ps_of_pmf.
   unfold proj1_sig.
   match_destr.
   unfold expt_value.
   simpl in i.
   unfold pmf_PMF_fun in i.
   
   generalize (infinite_sum'_finite
                 (pmf_parts (pmf_PMF pmf)
                            (exist (fun _ : pre_event A => True)
                                   (fun omega : A => pre_event_singleton c (rv_X omega))
                                   (sa_preimage_singleton rv_X c)))
                 (nodup eq_nat_dec (map countable_index (map snd pmf.(outcomes)))))
   ; intros HH.
   cut_to HH.
   - rewrite (infinite_sum'_unique i HH).
     clear i HH.
     unfold pmf_parts; simpl.
     rewrite (nodup_map_inj decA)
      ; [| intros; now apply countable_index_inj].
      rewrite map_map.
      erewrite map_ext
      ; [| intros; rewrite countable_inv_index; reflexivity].
      destruct pmf.
      unfold pmf_PMF_fun; simpl.
      clear sum1.
      generalize (map_filter_nodup_perm snd outcomes); intros HH0.
      rewrite seqmap_map at 1.
      eapply Permutation_map in HH0.
      eapply list_sum_perm_eq in HH0.
      rewrite <- HH0.
      rewrite concat_map.
      rewrite list_sum_map_concat.
      repeat rewrite map_map.
      f_equal.
      apply map_ext_in; intros a inn1.
      match_destr.
     + f_equal.
       apply map_ext_in; intros [??] inn2; simpl.
       match_destr.
       * subst; lra.
       * field_simplify.
         apply filter_In in inn2.
         destruct inn2 as [inn2 eqq2].
         simpl in *.
         match_destr_in eqq2.
         red in e.
         subst.
         red in p.
         congruence.
     + unfold pre_event_singleton in n.
       symmetry.
       apply list_sum0_0.
       apply Forall_map.
       rewrite Forall_forall; intros [??] inn2.
       apply filter_In in inn2.
       destruct inn2 as [inn2 eqq2].
       simpl in *.
       match_destr_in eqq2.
       red in e.
       subst.
       match_destr; [congruence | lra].
   - intros n nin.
     unfold pmf_parts.
     match_case; intros a eqq1.
     apply countable_inv_sound in eqq1; subst.
     match_destr.
     simpl in e.
     unfold pmf_PMF; simpl.
     unfold pmf_PMF_fun.
     apply list_sum0_0.
     rewrite Forall_map.
     rewrite Forall_forall; intros [??] inn1; simpl.
     apply filter_In in inn1.
     destruct inn1 as [inn1 eqq2].
     simpl in eqq2.
     match_destr_in eqq2.
     red in e0; subst.
     elim nin.
     apply nodup_In.
     apply in_map.
     apply in_map_iff.
     exists (n, a0); simpl; eauto.
   - apply NoDup_nodup.
 Qed.     

Lemma SimpleExpectation_preimage_indicator
      (rv_X : A -> R)
      {frf : FiniteRangeFunction rv_X} :
     SimpleExpectation (Prts := ps_pmf) rv_X = 
     list_sum (map (fun v => v *
                             (SimpleExpectation (Prts:=ps_pmf) (point_preimage_indicator rv_X v)))
                   (nodup Req_EM_T frf_vals)).
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
       {frf : FiniteRangeFunction rv_X} :
     expt_value pmf rv_X = 
     list_sum (map (fun v => v *
                             (expt_value pmf (point_preimage_indicator rv_X v)))
                   (nodup Req_EM_T frf_vals)).
  Proof.
    transitivity (expt_value pmf (fun a => list_sum 
                 (map 
                    (fun c => c * (point_preimage_indicator rv_X c a))
                    (nodup Req_EM_T frf_vals)))).
    - apply expt_value_Proper; trivial.
      apply frf_preimage_indicator'.
    - rewrite expt_value_sum_comm.
      f_equal.
      apply map_ext; intros.
      apply expt_value_const_mul.
  Qed.

  Theorem pmf_SimpleExpectation_value (rv_X : A -> R)
          {frf:FiniteRangeFunction rv_X} 
   : SimpleExpectation (Prts:=ps_pmf) rv_X = expt_value pmf rv_X.
 Proof.
    rewrite SimpleExpectation_preimage_indicator.   
    rewrite expt_value_preimage_indicator with (frf := frf).
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
   
 Program Global Instance frf_restricted_range
        {B} {decB:EqDec B eq} (default:B) (l:list B) (rv_X: A -> B)
   : FiniteRangeFunction (rv_restricted_range default l rv_X)
   := {|
   frf_vals := default::l
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

Lemma pmf_restricted_range_almostR2_eq rv_X :
  almostR2 ps_pmf eq rv_X  (rv_restricted_range 0 (pmf_image rv_X) rv_X).
Proof.
  simpl.
  repeat red;  simpl.
  unfold ps_of_pmf, proj1_sig, rv_restricted_range.
  exists (exist _ _ (sa_discrete (fun (a:A) => In a (map snd (outcomes pmf))))).
  split.
  - simpl.

    assert (HH:infinite_sum (pmf_parts (pmf_PMF pmf)
             (exist (fun _ : pre_event A => True) (fun a : A => In a (map snd pmf))
                    (sa_discrete (fun a : A => In a (map snd pmf))))) 1).
    {
      apply infinite_sum_infinite_sum'.
      unfold pmf_parts; simpl.
      generalize (pmf_infinite_sum_finite pmf); intros HH.
      unfold pmf_pmf, pmf_PMF; simpl.
      unfold pmf_PMF_fun.
      assert (adds1: (list_sum (map (fun x : nonnegreal * A => nonneg (fst x)) pmf)) = 1).
      {
        destruct pmf.
        rewrite <- list_fst_sum_eq.
        apply sum1.
      }
      rewrite <- adds1.
      eapply infinite_sum'_ext; try apply HH.
      intros.
      simpl.
      match_destr; trivial.
      match_destr.
      rewrite false_filter_nil; simpl; trivial.
      intros ? inn; simpl.
      match_destr.
      red in e; subst; simpl in *.
      elim n.
      now apply in_map.
    } 
    apply infinite_sum_is_lim_seq in HH.
    apply Lim_seq.is_lim_seq_unique in HH.
    now rewrite (f_equal _ HH); simpl.
  - intros.
    simpl in H.
    unfold pmf_image.
    match_destr.
    now apply (in_map rv_X) in H.
Qed.
      
Local Instance pmf_restricted_range_finite (rv_X : A -> R) :
  IsFiniteExpectation ps_pmf (rv_restricted_range 0 (pmf_image rv_X) rv_X).
Proof.
  red.
  now rewrite (Expectation_simple (rv_restricted_range 0 (pmf_image rv_X) rv_X)).
Qed.

Global Instance pmf_value_IsFinite (rv_X : A -> R) :
  IsFiniteExpectation ps_pmf rv_X.
Proof.
  apply IsFiniteExpectation_proper_almostR2 with 
      (rv_X1 := (rv_restricted_range 0 (pmf_image rv_X) rv_X)); try typeclasses eauto.
  apply symmetry.
  apply pmf_restricted_range_almostR2_eq.
Qed.

Lemma pmf_expectation_on_restricted_range rv_X :
  Expectation (Prts:=ps_pmf) rv_X = Expectation (Prts:=ps_pmf) (rv_restricted_range 0 (pmf_image rv_X) rv_X).
Proof.
  generalize (FiniteExpectation_proper_almostR2 ps_pmf _ _ (pmf_restricted_range_almostR2_eq rv_X)).
  unfold FiniteExpectation, proj1_sig.
  repeat match_destr.
  congruence.
Qed.

Theorem pmf_value_SimpleExpectation (rv_X : A -> R) :
  expt_value pmf rv_X =
  SimpleExpectation (Prts:=ps_pmf)
                    (rv_restricted_range 0 (pmf_image rv_X) rv_X).
Proof.
  rewrite pmf_SimpleExpectation_value.
  apply expt_value_on_restricted_range.
Qed.

Theorem pmf_value_Expectation (rv_X : A -> R) :
  Expectation (Prts:=ps_pmf) rv_X =
  Some (Rbar.Finite (expt_value pmf rv_X)).
Proof.
  rewrite pmf_expectation_on_restricted_range.
  erewrite Expectation_simple.
  now rewrite pmf_value_SimpleExpectation.
Qed.

Corollary pmf_value_FiniteExpectation (rv_X : A -> R) :
  FiniteExpectation ps_pmf rv_X = expt_value pmf rv_X.
Proof.
  generalize (pmf_value_Expectation rv_X).
  erewrite FiniteExpectation_Expectation; congruence.
Qed.

End pmf_prob.
