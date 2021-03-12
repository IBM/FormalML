Require Import Reals Lra List.

Require Import LibUtils utils.Utils.
Require Import ProbSpace SigmaAlgebras.
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

Section pmf_prob.
  Context {A:Type}.
  Context (pmf:Pmf A).

  Definition sa_pmf : SigmaAlgebra A
      := generated_sa (fun e => In e (map pre_event_singleton (map snd pmf.(outcomes)))).

  Program Definition ps_p_pmf (e:pre_event A) : R
    := list_sum
         (map (fun '(r, v) =>
                 if excluded_middle_informative (e v)
                 then nonneg r
                 else 0%R)
              pmf.(outcomes)).

  Global Instance ps_p_pmf_proper : Proper (pre_event_equiv ==> eq) ps_p_pmf.
  Proof.
    intros ?? eqq.
    unfold ps_p_pmf.
    f_equal.
    apply map_ext; intros [??].
   red in eqq.
   repeat match_destr.
   - apply eqq in x0; tauto.
   - apply eqq in y0; tauto.
  Qed.

 Program Instance ps_pmf : ProbSpace sa_pmf
   := {|
   ps_P e := ps_p_pmf e
     |}.
 Next Obligation.
   intros ?? eqq1.
   now apply ps_p_pmf_proper.
 Qed.
 Next Obligation.
   unfold sum_of_probs_equals.
   rewrite (infinite_sum'_ext _ (fun n : nat => ps_p_pmf (collection_pre collection n)))
     by reflexivity.
   apply -> (collection_is_pairwise_disjoint_pre collection) in H.
   rewrite (ps_p_pmf_proper _ (fun t : A => exists n : nat, (collection_pre collection n) t)) by reflexivity.
   revert H.
   generalize (collection_pre collection); clear collection; intros collection.
   intros.
   unfold ps_p_pmf; simpl in *.
   (* there should be a more constructive proof, but my spirit is broken *)
   destruct pmf.
   simpl in *.
   clear sum1.
   induction outcomes.
   - red; simpl.
     apply infinite_sum'0.
   - simpl.
     destruct a; simpl in *.
     match_destr.
     + destruct e as [nn Hn].
       apply infinite_sum'_plus; trivial.
       apply (infinite_sum'_one
                     _
                     nn n).
       * intros.
         match_destr.
         eelim H; eauto.
       * match_destr.
         congruence.
     + rewrite Rplus_0_l.
       red.
       eapply infinite_sum'_ext; try eapply IHoutcomes
       ; intros; simpl.
       match_destr; simpl.
       * elim n0.
         eexists; eauto.
       * lra.
Qed.
 Next Obligation.
   unfold ps_p_pmf.
   rewrite <- pmf.(sum1).
   rewrite list_fst_sum_eq.
   f_equal.
   apply map_ext; intros [??].
   match_destr.
   elim n0; now red.
 Qed.
 Next Obligation.
   unfold ps_p_pmf.
   apply list_sum_pos_pos'.
   rewrite Forall_forall; intros ? inn.
   apply in_map_iff in inn.
   destruct inn as [[??][??]].
   match_destr_in H; subst.
   - apply cond_nonneg.
   - now right.
 Qed.

 Lemma pmf_SimpleExpectation_value_const (c:R) :
     SimpleExpectation (Prts:=ps_pmf) (const c) = expt_value pmf (const c).
 Proof.
   rewrite SimpleExpectation_const.
   unfold const.
   now rewrite expt_value_const.
 Qed.

 Lemma pmf_SimpleExpectation_value_point_preimage_indicator (rv_X : A -> R) (c:R)
       {rv:RandomVariable sa_pmf borel_sa rv_X} :
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

