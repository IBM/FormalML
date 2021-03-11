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

 Theorem pmf_SimpleExpectation_value (rv_X : A -> R) {srv:SimpleRandomVariable rv_X} 
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

Theorem pmf_value_SimpleExpectation (rv_X : A -> R) :
  expt_value pmf rv_X = SimpleExpectation (Prts:=ps_pmf) (rv_restricted_range 0 (pmf_image rv_X) rv_X).
Proof.
  rewrite pmf_SimpleExpectation_value.
  apply expt_value_on_restricted_range.
Qed.

