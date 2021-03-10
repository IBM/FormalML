Require Import Reals Lra List.

Require Import LibUtils utils.Utils.
Require Import ProbSpace SigmaAlgebras.
Require Import pmf_monad mdp.
Require Import SimpleExpectation.
Require Import cond_expt.
Require Import Lia.

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
   assert  ((map
       (fun pat : nonnegreal * A =>
        (let
         '(r, v) as anonymous' := pat return (anonymous' = pat -> R) in
          fun _ : (r, v) = pat =>
          if excluded_middle_informative (rv_X v = c) then r else 0) eq_refl)
       outcomes) = 
   (seq.map
        (fun x : nonnegreal * A =>
        (if Req_EM_T (rv_X (snd x)) c then 1 else 0) * fst x) outcomes)).
   - unfold map.
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
   - rewrite H.
     apply Permutation.Permutation_refl.
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
    assert ( (@map R R
       (fun v : R =>
        Rmult v
          (@ps_P A sa_pmf ps_pmf
             (@event_preimage A R rv_X (@event_singleton R v))))
       (@nodup R Req_EM_T (@srv_vals A R rv_X srv))) = 
    (@map R R
       (fun v : R =>
        Rmult v
          (@SimpleExpectation A sa_pmf ps_pmf
             (@point_preimage_indicator A rv_X v)
             (@EventIndicator_srv A (fun x : A => @eq R (rv_X x) v)
                (fun x : A => Req_EM_T (rv_X x) v))))
       (@nodup R Req_EM_T (@srv_vals A R rv_X srv)))).
    - apply map_ext.
      intros.
      unfold point_preimage_indicator.
      rewrite SimpleExpectation_EventIndicator.
      reflexivity.
    - rewrite H.
      apply Permutation.Permutation_refl.    
  Qed.

 Lemma srv_preimage_indicator (rv_X : A -> R) {srv:SimpleRandomVariable rv_X} :
   forall a:A, rv_X a =
               list_sum 
                 (map 
                    (fun c => c * (point_preimage_indicator rv_X c a))
                    (nodup Req_EM_T srv_vals)).
  Proof.
    intros.
    destruct srv.
    unfold RandomVariable.srv_vals.
    specialize (srv_vals_complete a).
    
    induction srv_vals.
    
  Admitted.


(*

 Theorem pmf_SimpleExpectation_value (rv_X : A -> R) {srv:SimpleRandomVariable rv_X} 
   : SimpleExpectation (Prts:=ps_pmf) rv_X = expt_value pmf rv_X.
 Proof.
   unfold SimpleExpectation.
   f_equal.
   unfold group_by_image.
*)
   
