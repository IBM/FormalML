Require Import Reals Lra List.

Require Import LibUtils utils.Utils.
Require Import ProbSpace SigmaAlgebras.
Require Import pmf_monad mdp.
Require Import SimpleExpectation.
Require Import cond_expt.
Require Import Lia.
Require Import Equivalence.

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
      := generated_sa (fun e => In e (map event_singleton (map snd pmf.(outcomes)))).

  Program Definition ps_p_pmf (e:event A) : R
    := list_sum
         (map (fun '(r, v) =>
                 if excluded_middle_informative (e v)
                 then nonneg r
                 else 0%R)
              pmf.(outcomes)).
    
 Program Instance ps_pmf : ProbSpace sa_pmf
   := {|
   ps_P e := ps_p_pmf e
     |}.
 Next Obligation.
   unfold ps_p_pmf.
   intros ?? eqq1.
   f_equal.
   apply map_ext; intros [??].
   red in eqq1.
   repeat match_destr.
   - apply eqq1 in x0; tauto.
   - apply eqq1 in y0; tauto.
 Qed.
 Next Obligation.
   unfold ps_p_pmf; simpl in *.
   clear H.
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
     + destruct u as [nn Hn].
       apply infinite_sum'_plus; trivial.
       apply (infinite_sum'_one
                     _
                     nn n).
       * intros.
         match_destr.
         eelim H0; eauto.
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
   match_destr_in H0; subst.
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

 (* TODOL Move to utils/BasicUtils *)
 Lemma refl_refl {T} {R:T->T->Prop} {refl:Reflexive R} x y : x = y -> R x y.
 Proof.
   intros; subst.
   apply refl.
 Qed.
 
 Lemma pmf_SimpleExpectation_value_point_preimage_indicator (rv_X : A -> R) (c:R) :
   SimpleExpectation (Prts:=ps_pmf) (point_preimage_indicator rv_X c) =
   expt_value pmf (point_preimage_indicator rv_X c).
 Proof.
   unfold point_preimage_indicator.
   rewrite SimpleExpectation_EventIndicator.
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
    rewrite SimpleExpectation_EventIndicator.
    reflexivity.
  Qed.

  Lemma preimage_indicator_notin (rv_X : A -> R) l :
    forall a:A,
      ~ In (rv_X a) l ->
                       list_sum 
                         (map 
                            (fun c => c * (point_preimage_indicator rv_X c a))
                            (nodup Req_EM_T l)) = 0.
  Proof.
    intros.
    erewrite map_ext_in.
    - apply list_sum_map_zero.
    - intros.
      apply nodup_In in H0.
      unfold point_preimage_indicator, EventIndicator.
      match_destr.
      + congruence.
      + lra.
  Qed.


 Lemma srv_preimage_indicator (rv_X : A -> R) {srv:SimpleRandomVariable rv_X} :
   forall a:A, rv_X a =
               list_sum 
                 (map 
                    (fun c => c * (point_preimage_indicator rv_X c a))
                    (nodup Req_EM_T srv_vals)).
  Proof.
    intros.
    destruct srv; simpl.
    specialize (srv_vals_complete a).
    induction srv_vals; simpl in srv_vals_complete; [tauto |].
    simpl.
    match_destr.
    - apply IHsrv_vals.
      intuition congruence.
    - simpl.
      destruct srv_vals_complete.
      + subst.
        rewrite preimage_indicator_notin; trivial.
        unfold point_preimage_indicator, EventIndicator.
        match_destr; lra.
      + rewrite IHsrv_vals; trivial.
        unfold point_preimage_indicator, EventIndicator.
        match_destr.
        * subst.
          tauto.
        * lra.
  Qed.

(*

 Theorem pmf_SimpleExpectation_value (rv_X : A -> R) {srv:SimpleRandomVariable rv_X} 
   : SimpleExpectation (Prts:=ps_pmf) rv_X = expt_value pmf rv_X.
 Proof.
   unfold SimpleExpectation.
   f_equal.
   unfold group_by_image.
*)
   
