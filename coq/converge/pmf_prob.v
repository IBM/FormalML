Require Import Reals Lra List.

Require Import LibUtils utils.Utils.
Require Import ProbSpace SigmaAlgebras.
Require Import pmf_monad.
Require Import SimpleExpectation.


Set Bullet Behavior "Strict Subproofs".

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
  
  Definition pmf_space := {x : A | In x (map snd pmf.(outcomes))}.

  Definition sa_pmf_space : SigmaAlgebra pmf_space
    := discrete_sa _.

   Axiom (A_event_dec:forall (e:event pmf_space), dec_event e).

   Program Definition ps_p_pmf_space (e:event pmf_space) : R
   := list_sum (map_dep pmf.(outcomes) (fun '(p,a) pf =>
                            if A_event_dec e (exist _ a _)
                            then nonneg p else 0%R)).
   Next Obligation.
     apply in_map_iff.
     eexists.
     split; eauto; simpl; trivial.
   Qed.


   

   
 Definition Pmf_sa {A} (pmf:Pmf A) : SigmaAlgebra A
   := generated_sa (fun e => In e (map event_singleton (map snd pmf.(outcomes)))).
 
 Definition Pmf_ps_p (pmf:Pmf A) (e:event A) : R
   := list_sum (map (fun '(p,a) =>
                            if A_event_dec e a
                            then nonneg p else 0%R) pmf.(outcomes)).

 Definition finitesubset_sa {A} (l:list A) : SigmaAlgebra {x : A | In x l}
   := discrete_sa {x : A | In x l}.

 
 Program Instance Pmf_ps (pmf:Pmf A) : ProbSpace (Pmf_sa pmf)
   := {|
   ps_P e := Pmf_ps_p pmf e
     |}.
 Next Obligation.
   unfold Pmf_ps_p.
   intros ?? eqq1.
   f_equal.
   apply map_ext; intros [??].
   red in eqq1.
   repeat match_destr.
   - apply eqq1 in x0; tauto.
   - apply eqq1 in y0; tauto.
 Qed.
 Next Obligation.
 Admitted.
 Next Obligation.
   unfold Pmf_ps_p.
   rewrite <- pmf.(sum1).
   rewrite list_fst_sum_eq.
   f_equal.
   apply map_ext; intros [??].
   match_destr.
   elim n0; now red.
 Qed.
 Next Obligation.
   unfold Pmf_ps_p.
   apply list_sum_pos_pos'.
   rewrite Forall_forall; intros ? inn.
   apply in_map_iff in inn.
   destruct inn as [[??][??]].
   match_destr_in H0; subst.
   - apply cond_nonneg.
   - now right.
 Qed.

 
 Lemma pmf_SimpleExpectation (rv_X:A->R)

