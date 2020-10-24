Require Import Reals EquivDec List LibUtils Permutation Morphisms Utils.
Require Import pmf_monad cond_expt.
Require Import micromega.Lra.
From mathcomp Require Import ssreflect ssrfun seq.

Set Bullet Behavior "Strict Subproofs".

(*

****************************************************************************************
Useless auxilary results. 
****************************************************************************************
*)
Local Open Scope list_scope.

Open Scope R_scope.

Section range.
  
Global Instance EqDecR : EqDec R eq := Req_EM_T. 

Arguments outcomes {_}.

(* Range of a random variable together with the atomic probabilities.*)
Definition range {A : Type} (l : list(nonnegreal*A)) (f : A -> R) : list (nonnegreal*R) :=
  map (fun x => (x.1, f x.2)) l.

(* All p.(outcomes) which are preimages of a fixed r in R under the random variable g. *)
(*Definition preim_outcomes_of {A : Type} (p : Pmf A) (g : A -> R) (r : R) :=
  filter (fun x => (g x.2 ==b r)) p.(outcomes).*)

Definition preim_outcomes_of_And {A : Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2 ==b r1) (g x.2 ==b r2)) (p).(outcomes).


Lemma expt_value_range_sum {A : Type} (p : Pmf A) (f : A -> R) :
  expt_value p f = list_sum (map (fun p => nonneg(p.1)*p.2) (range p.(outcomes) f)).
Proof.
  unfold comp, expt_value,range. 
  rewrite <-map_comp. unfold comp. simpl. f_equal.
  apply List.map_ext. intro a. apply Rmult_comm. 
Qed.


(* p(f = r) *)
Definition prob_of_event {A : Type} (p : Pmf A) (f : A -> R) (r : R) :=
  𝕡[[seq s <- range p f | s.2 ==b r]].

(* p(f = r1 /\ g = r2) *)
Definition and_prob {A : Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :=
  𝕡[[seq s <- range (preim_outcomes_of p g r2) f | s.2 ==b r1]].


(* The function f doesn't matter here as we're only summing over the probabilities (first indices)*)
Lemma list_sum_outcomes_And {A : Type} (f : A -> R) (l : list (nonnegreal*A)) :
   𝕡[l] = list_fst_sum (range l f).
Proof.
unfold prob ; simpl.
rewrite list_fst_sum_compat. unfold list_fst_sum'.
rewrite list_fst_sum_compat. unfold list_fst_sum'.
simpl in *.  induction l.
- simpl ; lra.
- simpl. rewrite IHl. reflexivity.
Qed.

Lemma preim_outcomes_of_range {A:Type}(p : Pmf A) (f : A -> R) (r : R) :
  𝕡[preim_outcomes_of p f r] = 𝕡[[seq s <- (range p f) | (s.2 ==b r)]].
Proof.
  unfold prob, preim_outcomes_of. simpl.
  repeat (rewrite list_fst_sum_compat ; unfold list_fst_sum').
  f_equal. unfold range.  
  induction p.(outcomes).
  - simpl. reflexivity.          
  - simpl.
    unfold equiv_decb; destruct (equiv_dec (f a.2) r).
    simpl. rewrite IHl. f_equal.
    rewrite IHl. reflexivity.
Qed.


Lemma preim_outcomes_of_range_And {A : Type} (p : Pmf A) (f g: A -> R) (r1 r2 : R) :
 𝕡[preim_outcomes_of_And p f g r1 r2] = 𝕡[[seq s <- range (preim_outcomes_of p g r2) f | s.2 ==b r1]].
Proof.
  unfold prob, preim_outcomes_of,range,preim_outcomes_of_And. simpl.
  repeat (rewrite list_fst_sum_compat ; unfold list_fst_sum').
  f_equal. rewrite map_comp.  rewrite map_comp. f_equal.
  induction p.(outcomes).
  simpl ; reflexivity.
  simpl. unfold equiv_decb. destruct (equiv_dec (g a.2) r2) ; [simpl| simpl].
  unfold equiv_decb ; destruct (equiv_dec (f a.2) r1) ; [simpl | rewrite IHl].
  rewrite IHl.  reflexivity.
  simpl.  reflexivity.
  destruct (equiv_dec (f a.2) r1) ; [simpl; now rewrite IHl | simpl; now rewrite IHl].
Qed.

Definition cond_prob {A : Type}(p : Pmf A) (f g : A -> R)(r1 r2 : R) := 𝕡[preim_outcomes_of_And p f g r1 r2]/ 𝕡[preim_outcomes_of p g r2].
  
           
Definition cond_expt_value {A : Type}(p : Pmf A)(f g : A -> R) (r : R) : R := 
  list_sum (map (fun x => (cond_prob p f g x.2 r)*(x.2)) (range p.(outcomes) f)).


Definition independent {A : Type}(p : Pmf A) (f g : A -> R) :=
  forall r1 r2,  𝕡[preim_outcomes_of_And p f g r1 r2] = 𝕡[preim_outcomes_of p f r1]*𝕡[preim_outcomes_of p g r2].

Lemma cond_prob_eq_prob_independent {A : Type}(p : Pmf A) {f g : A -> R} (hi : independent p f g) :
  forall r1 r2, 𝕡[preim_outcomes_of p g r2] <> 0 -> cond_prob p f g r1 r2 = 𝕡[preim_outcomes_of p f r1].
Proof.
  intros r1 r2 H. 
  unfold cond_prob. specialize (hi r1 r2).
  rewrite hi. field_simplify. reflexivity.
  assumption.
Qed.


Lemma cond_expt_value_expt_value_aux {A : Type}{p : Pmf A}{f g : A -> R} (l : list(nonnegreal*R))(hi : independent p f g) :
 forall r, 𝕡[preim_outcomes_of p g r] <> 0 -> map (fun x => (cond_prob p f g x.2 r)*(x.2)) l = map (fun x => (𝕡[preim_outcomes_of p f x.2])*(x.2)) l.
Proof.
  intros r Hr.   
  apply List.map_ext.
  intro a. f_equal.
  apply (cond_prob_eq_prob_independent p hi).
  assumption.
Qed.





(*Lemma cond_expt_value_range {A : Type}{r : R} {g : A -> R}{p : Pmf A} (hne : 0 <> 𝕡[preim_outcomes_of p g r])(f : A -> R):
  cond_expt_value p f g r =
  list_sum ([seq nonneg(x.1) * x.2 | x <- range (preim_outcomes_of p g r) f])/𝕡[preim_outcomes_of p g r].
Proof.
  unfold cond_expt_value. unfold cond_prob.
  unfold range.  
  rewrite <-map_comp. unfold comp.  simpl. unfold cond_prob. f_equal.
  apply List.map_ext. intro a. apply Rmult_comm.
Qed.*)


  
(*Lemma cond_expt_value_expt_value_aux {A : Type}{r2 : R} {g : A -> R}{p : Pmf A} (hne : 0 <> 𝕡[preim_outcomes_of p g r2])(f : A -> R) (r1:R): list_sum ([seq nonneg(x.1) * x.2 | x <- range (preim_outcomes_of p g r2) f]) = _.*)
  
End range.



(*Section product_measure.
Open Scope monad_scope.

(* Not able to use the cool do notation. :-(  *)
Definition product_measure {A:Type} (p q : Pmf A) : Pmf(A*A) :=
 Pmf_bind p (fun (x:A) => Pmf_bind q (fun (y:A) => Pmf_pure (pair x y))).

End product_measure.

Notation "p ⊗ q" := (product_measure p q) (at level 80, right associativity).

Section junk.

Arguments outcomes {_}. 
Definition preim_outcomes_of_And {A : Type} (p : Pmf A) (f g: A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2 ==b r1) (g x.2 ==b r2)) p.(outcomes).

Lemma preim_outcomes_of_And_split {A : Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :
  preim_outcomes_of_And p f g r1 r2 = filter (fun x => f x.2 ==b r1) (preim_outcomes_of p g r2).
Proof.
  unfold preim_outcomes_of, preim_outcomes_of_And.
  induction p.(outcomes).
  - simpl ; reflexivity. 
  - simpl.  unfold equiv_decb. destruct (equiv_dec (g a.2) r2).
    unfold equiv_decb. destruct (equiv_dec (f a.2) r1). simpl. rewrite e0.
    unfold equiv_decb. destruct (equiv_dec r1 r1) ; [| congruence]. 
    rewrite IHl. reflexivity.
    simpl. rewrite IHl. unfold equiv_decb.
    destruct (equiv_dec (f a.2) r1) ; [contradiction|congruence].
    unfold equiv_decb.
    destruct (equiv_dec (f a.2) r1). simpl. rewrite IHl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed. 

Definition independent_aux_prop {A : Type} (p : Pmf A) (f g : A -> R):=
  forall r : R,
    list_sum [seq f x.2 * nonneg(x.1) | x <- p & g x.2 ==b r] =
    list_sum [seq f x.2 * nonneg(x.1) | x <- p.(outcomes)]*list_sum [seq nonneg(x.1) | x<-p.(outcomes) & g x.2 ==b r].


Lemma independent_aux_prop_const_fun {A : Type} (p : Pmf A) (g : A -> R) (c : R) : 
  independent_aux_prop p (fun _ => c) g.
Proof.
  unfold independent.
  intros r. 
  enough (H :  list_sum [seq c * nonneg(x.1) | x <- p.(outcomes) & g x.2 ==b r] = c* list_sum [seq nonneg(x.1) | x <- p.(outcomes) & g x.2 ==b r]).
  rewrite H.
  enough (H1 : forall p:Pmf A, list_sum [seq c * nonneg(x.1) | x <- p] = c*list_sum [seq nonneg(x.1) | x <- p]).
  rewrite (H1 p). f_equal. destruct p as [p0 sum1]. simpl in *.
  revert sum1. rewrite list_fst_sum_compat. unfold list_fst_sum'. intro H2. rewrite H2 ;lra.
  intro p0.
  induction p0.(outcomes). 
  simpl ; lra.
  simpl. simpl in H. rewrite IHl. lra.
  induction p.(outcomes).
  simpl ; lra.
  simpl. unfold equiv_decb ; destruct (equiv_dec (g a.2) r);[ | rewrite IHl;reflexivity].
  simpl. rewrite IHl. rewrite Rmult_plus_distr_l. reflexivity.
Qed.

End junk.



Section events.

Arguments outcomes {_}.
    
(* All (p⊗p).(outcomes) which are preimages of a fixed r in R under the random variable g. *)
Definition preim_outcomes_of_fst {A : Type} (p : Pmf A) (f : A -> R) (r : R) :=
  filter (fun x => (f x.2.1 ==b r)) (p ⊗ p).(outcomes).

Definition preim_outcomes_of_snd {A : Type} (p : Pmf A) (g : A -> R) (r : R) :=
  filter (fun x => (g x.2.2 ==b r)) (p ⊗ p).(outcomes).


Definition preim_outcomes_of_pair_And {A:Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2.1 ==b r1) (g x.2.2 ==b r2)) (p ⊗ p).(outcomes).


Theorem independent {A:Type} (p:Pmf A) (f g : A -> R) :
  forall r1 r2, 𝕡[ preim_outcomes_of_pair_And p f g r1 r2] = 𝕡[preim_outcomes_of_fst p f r1]*𝕡[preim_outcomes_of_snd p g r2].
  
End events.

Section cond_prob.

Arguments outcomes {_}.


(* Conditional expectation of f given that g(a) = r. *)
Definition cond_expt_value{A : Type}{r : R} {g : A -> R}{p : Pmf A} (hne : 0 <> 𝕡[preim_outcomes_of_snd p g r])(f : A -> R)  : R :=
  let q:= preim_outcomes_of_snd p g r in
  list_sum [seq f x.2.1 * nonneg (x.1) | x <- q]/𝕡[preim_outcomes_of_snd p g r].

Lemma cond_expt_value_indep
{A : Type} {r : R} {f g : A -> R} {p : Pmf A}(hne : 0 <> 𝕡[preim_outcomes_of_snd p g r]) (Hi : independent p f g) :
  cond_expt_value hne f = expt_value p f.
Proof.
  unfold cond_expt_value. unfold prob,preim_outcomes_of_snd.
  simpl. rewrite list_fst_sum_compat. unfold list_fst_sum'.
  field_simplify.
  induction p.(outcomes).
  - simpl. admit.
  - simpl. destruct a. simpl. 
    rewrite filter_cat. rewrite filter_comp. rewrite IHl. 
      reflexivity.
  intro H. unfold prob in hne. simpl in hne.
  rewrite list_fst_sum_compat in hne. unfold list_fst_sum' in hne. firstorder.
Qed.   
 *)

