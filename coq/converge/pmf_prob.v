Require Import Reals Lra List.

Require Import LibUtils utils.Utils.
Require Import ProbSpace SigmaAlgebras.
Require Import pmf_monad.
Require Import SimpleExpectation.
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

